using Mba.Ast;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Synthesis
{
    public record Component(SynthOpc Opcode, CompontentData Data = null);
    public record CompontentData(int Index);

    public enum SynthOpc
    {
        // Boolean
        And,
        Or,
        Xor,

        Not,

        // Arithmetic
        Add,
        Sub,
        Mul,

        Lshr,

        // Special
        TruthTable,

        Constant,
    }

    public abstract record Line();
    public record VarLine(int Index, Expr Symbol) : Line();
    public record ExprLine(BitVecExpr Opcode, BitVecExpr Op0, BitVecExpr Op1, Expr TruthTable, BitVecExpr ConstantData) : Line();

    public class BrahmaSynthesis
    {
        private readonly AstCtx ctx;
        private readonly AstIdx idx;
        private readonly List<AstIdx> inputs;

        private readonly Context solver;
        private readonly Z3Translator translator;

        // Config:
        //
        private readonly int numInstructions = 7;


        private bool usesTruthOperator = false;
        private const int TRUTHVARS = 2;
        private const uint TRUTHSIZE = 1u << TRUTHVARS;

        private int maxConstants = 2;


        /*
        private readonly Dictionary<SynthOpc, int> components = new()
        {
            // Constants
            // Not present on booleans
            { SynthOpc.Constant, 2},

            
            //{ SynthOpc.Not, 2},
            //{ SynthOpc.And, 2},
            //{ SynthOpc.Or, 2},
            //{ SynthOpc.Xor, 2},
            

        
            
           // { SynthOpc.Add, 2},
            { SynthOpc.Not, 2},
            //{ SynthOpc.And, 2},
            { SynthOpc.Or, 2},
            //{ SynthOpc.Xor, 2},
            

            //{ SynthOpc.TruthTable, 2}
        };
        */

        List<Component> components = new List<Component>()
        {
            new(SynthOpc.Constant),

            //new(SynthOpc.Not),
            //new(SynthOpc.And),
            //new(SynthOpc.Or),
            //new(SynthOpc.TruthTable)

            new(SynthOpc.Xor),

            new(SynthOpc.Add),
            new(SynthOpc.Sub),
            new(SynthOpc.Mul),

            //new(SynthOpc.Lshr),
        };

        public BrahmaSynthesis(AstCtx ctx, AstIdx idx)
        {
            var config = new Dictionary<string, string>()
            {
                { "html_mode", "false"}
            };

            components = components.OrderBy(x => x.Opcode).ToList();

            // The `SynthOpc` enum has the simplest components at top.
            // Because of how we encode our MUX tree, we want the most complex components to be at the top.
            // Short version: Components are described as an N-bit bit-vector. Sometimes the number of components is not a power of 2 and there are padding values. 3-bit vector with 6 possible values leaves 2 padding choices. We default padding choices to the simplest component.
            // Reverse does make things way faster
            components.Reverse();

            for (int i = 0; i < components.Count; i++)
            {
                components[i] = new(components[i].Opcode, new(i));
            }

            usesTruthOperator = components.Any(x => x.Opcode == SynthOpc.TruthTable);




            this.ctx = ctx;
            this.idx = idx;
            inputs = ctx.CollectVariables(idx);

            solver = new();
            solver.PrintMode = Z3_ast_print_mode.Z3_PRINT_LOW_LEVEL;
            translator = new Z3Translator(ctx, solver);
        }

        // Ideas:
        //      - Tree synthesis
        //      - Heuristic for finding good quality counterexamples. Small functions or partial inputs cover large parts of the truth table. 
        //      -   Feasible for boolean circuits. Needs to be generalized for word level expressions. 
        //  
        public void Run()
        {

            var before = translator.Translate(idx);

            var (lines, shiftVariables, constantVariables) = GetLines();

            int li = 0;
            foreach (var line in lines)
            {
                if (line is not ExprLine exprLine)
                {
                    li++;
                    continue;
                }
                Console.WriteLine($"{exprLine.Opcode.SortSize}({exprLine.Op0.SortSize}, {exprLine.Op1.SortSize}) with {li} operands to choose from");
                li++;
            }


            var after = GetExpression(lines);

            //after = after.Simplify();

            var symbols = lines.Where(x => x is VarLine).Select(x => (x as VarLine).Symbol).ToArray();


            //      var tactics = solver.AndThen(
            //solver.MkTactic("simplify"),
            //solver.MkTactic("propagate-values"),
            //solver.MkTactic("simplify"),
            //solver.MkTactic("elim-uncnstr"),
            //solver.MkTactic("qe-light"),
            //solver.MkTactic("simplify"),
            //solver.MkTactic("elim-uncnstr"),
            //solver.MkTactic("reduce-args"),
            //solver.MkTactic("qe-light"),
            //solver.MkTactic("smt")
            //);


            var s = solver.MkSolver();
            var constraints = GetProgramConstraints(lines, shiftVariables);

            // Optionally hardcode constants
            /*
            var c0 = constantVariables[0];
            var c1 = constantVariables[1];
            s.Add(solver.MkEq(c0, solver.MkBV(60, 8)));
            s.Add(solver.MkEq(c1, solver.MkBV(82, 8)));
            */

            s.Add(constraints);


            CEGIS(s, symbols, before, after, lines);

            Debugger.Break();
        }

        private (IReadOnlyList<Line>, List<BitVecExpr> shiftVariables, List<BitVecExpr> constantVariables) GetLines()
        {
            var lines = new List<Line>();
            var shiftVariables = new List<BitVecExpr>();
            var constantVariables = new List<BitVecExpr>();

            // Each variable gets assigned its own line
            for (int i = 0; i < inputs.Count; i++)
                lines.Add(new VarLine(i, translator.cache[inputs[i]]));

            // Each instruction gets assigned its own line.
            var opcodeBitsize = BvWidth(components.Count - 1);
            //var opcodeBitsize = GetBitsNeeded(32);

            int allocatedConstants = 0;
            for (int i = lines.Count; i < numInstructions; i++)
            {
                // Choose the opcode
                var opcode = solver.MkBVConst($"code{i}", (uint)opcodeBitsize);

                // Choose the operands
                var operandBitsize = BvWidth(i - 1);
                //Console.WriteLine($"Got {other} bits needed for operands of line {i} with lz {BitOperations.LeadingZeroCount((ulong)i)}");
                var op0 = solver.MkBVConst($"{i}_op0", (uint)operandBitsize);
                var op1 = solver.MkBVConst($"{i}_op1", (uint)operandBitsize);

                Expr truthTable = null;
                if (usesTruthOperator)
                    truthTable = solver.MkBVConst($"{i}_tt", TRUTHSIZE);

                BitVecExpr constant = solver.MkBV(0, ctx.GetWidth(idx));
                if (HasComponent(SynthOpc.Lshr))
                {
                    // Compute the minimum number of bits necessary to fit the shift
                    var shiftByWidth = BvWidth(ctx.GetWidth(idx));

                    var shiftBy = solver.MkBVConst($"{i}_shift", (uint)shiftByWidth);
                    shiftVariables.Add(shiftBy);
                    if (shiftBy.SortSize < constant.SortSize)
                        shiftBy = solver.MkZeroExt(constant.SortSize - shiftBy.SortSize, shiftBy);


                    var lshrComponent = GetComponent(SynthOpc.Lshr);
                    var isLshr = solver.MkEq(opcode, solver.MkBV(lshrComponent.Data.Index, opcode.SortSize));

                    constant = (BitVecExpr)solver.MkITE(isLshr, shiftBy, constant);
                }

                if (allocatedConstants < maxConstants)
                {
                    constant = solver.MkBVConst($"{i}_const", ctx.GetWidth(idx));

                    constantVariables.Add(constant);

                    allocatedConstants++;
                }


                lines.Add(new ExprLine(opcode, op0, op1, truthTable, constant));
            }
            return (lines, shiftVariables, constantVariables);
        }

        public static int BvWidth(int maxValue)
        {
            if (maxValue == 0)
                return 1;

            return BitOperations.Log2((uint)maxValue) + 1;
        }

        private Expr GetExpression(IReadOnlyList<Line> lines)
        {
            var exprs = new List<Expr>();
            for (int lineIndex = 0; lineIndex < lines.Count; lineIndex++)
            {
                var line = lines[lineIndex];
                if (line is VarLine varLine)
                {
                    exprs.Add(varLine.Symbol);
                    continue;
                }

                // Convert the operands to 
                var exprLine = (ExprLine)line;
                var op0 = (BitVecExpr)SelectOperand(exprLine.Op0, exprs);
                var op1 = (BitVecExpr)SelectOperand(exprLine.Op1, exprs);

                // Compute expressions for each opcode
                var candidates = new List<Expr>(exprs.Count);
                foreach (var opc in components)
                {
                    var expr = opc.Opcode switch
                    {
                        SynthOpc.Not => solver.MkBVNot(op0),
                        SynthOpc.And => solver.MkBVAND(op0, op1),
                        SynthOpc.Or => solver.MkBVOR(op0, op1),
                        SynthOpc.Xor => solver.MkBVXOR(op0, op1),
                        SynthOpc.Add => solver.MkBVAdd(op0, op1),
                        SynthOpc.Sub => solver.MkBVSub(op0, op1),
                        SynthOpc.Mul => solver.MkBVMul(op0, op1),
                        SynthOpc.TruthTable => TruthTableToExpr((BitVecExpr)exprLine.TruthTable, op0, op1),
                        SynthOpc.Constant => exprLine.ConstantData,
                        SynthOpc.Lshr => solver.MkBVLSHR(op0, exprLine.ConstantData), // TODO: Assert that op1 is a constant

                        _ => throw new InvalidOperationException()
                    };
                    candidates.Add(expr);
                }

                Expr select = null;
                bool select3 = false;
                if (select3 && candidates.Count == 3)
                    select = Select3(exprLine.Opcode, candidates);
                else
                    select = LinearSelect((BitVecExpr)exprLine.Opcode, candidates);

                //var selectS = select.Simplify();

                exprs.Add(select);
            }

            //Debugger.Break();
            return exprs.Last();
        }

        private Expr TruthTableToExpr(BitVecExpr table, BitVecExpr x, BitVecExpr y)
        {
            var width = x.SortSize;

            var t = Enumerable.Range(0, 4).Select(x => GetMask(width, (uint)x, table)).ToList();
            var low = BitwiseMux(y, t[1], t[0]);
            var high = BitwiseMux(y, t[3], t[2]);
            return BitwiseMux(x, high, low);
        }

        private BitVecExpr BitwiseMux(BitVecExpr cond, BitVecExpr onTrue, BitVecExpr onFalse)
            => solver.MkBVOR(solver.MkBVAND(cond, onTrue), solver.MkBVAND(solver.MkBVNot(cond), onFalse));

        private BitVecExpr GetMask(uint width, uint index, BitVecExpr tableBv)
        {
            var bit = solver.MkExtract(index, index, tableBv);
            return (BitVecExpr)solver.MkITE(solver.MkEq(bit, solver.MkBV(1, 1)), solver.MkBV(ulong.MaxValue, width), solver.MkBV(0, width));
        }

        private Expr SelectOperand(Expr selector, List<Expr> exprs)
        {
            return LinearSelect((BitVecExpr)selector, exprs);
        }

        private Expr Select3(BitVecExpr index, List<Expr> elements)
        {
            Debug.Assert(elements.Count == 3);

            var b0 = solver.MkExtract(0, 0, index);
            var b1 = solver.MkExtract(1, 1, index);

            var lowerHalf = solver.MkITE(solver.MkEq(b0, solver.MkBV(1, 1)), elements[1], elements[0]);
            return solver.MkITE(solver.MkEq(b1, solver.MkBV(1, 1)), elements[2], lowerHalf);
        }

        // Given a symbolic index and a list of N values, pick the ith value
        private Expr LinearSelect(BitVecExpr index, List<Expr> options)
        {
            int n = options.Count;
            if (n == 0)
                throw new InvalidOperationException();
            if (n == 1)
                return options[0];

            var casted = options.Select(x => (BitVecExpr)x).ToList();

            if (n > 12)
                return PrunedSelect(index, casted);


            BitVecExpr result = (BitVecExpr)options[n - 1];

            for (int i = n - 2; i >= 0; i--)
            {
                BoolExpr condition = solver.MkEq(index, solver.MkBV(i, index.SortSize));
                result = (BitVecExpr)solver.MkITE(condition, (Expr)options[i], result);
            }

            return result;
        }

        public BitVecExpr PrunedSelect(BitVecExpr index, List<BitVecExpr> options)
        {
            return BuildPrunedTree(solver, index, options, 0, options.Count);
        }

        private static BitVecExpr BuildPrunedTree(Context ctx, BitVecExpr index, List<BitVecExpr> options, int offset, int count)
        {
            if (count == 1) return options[offset];

            int requiredBits = (int)Math.Ceiling(Math.Log2(count));
            int msbIndex = requiredBits - 1;
            int splitSize = 1 << msbIndex;
            int rightCount = count - splitSize;

            BitVecExpr condBit = ctx.MkExtract((uint)msbIndex, (uint)msbIndex, index);
            BoolExpr condition = ctx.MkEq(condBit, ctx.MkBV(1, 1));

            // Visit next branch of the tree
            BitVecExpr lowResult = BuildPrunedTree(ctx, index, options, offset, splitSize);
            BitVecExpr highResult = BuildPrunedTree(ctx, index, options, offset + splitSize, rightCount);

            return (BitVecExpr)ctx.MkITE(condition, highResult, lowResult);
        }


        private bool HasComponent(SynthOpc opc)
            => components.Any(x => x.Opcode == opc);

        private Component GetComponent(SynthOpc opc)
            => components.SingleOrDefault(x => x.Opcode == opc);


        private BoolExpr GetProgramConstraints(IReadOnlyList<Line> lines, List<BitVecExpr> shiftVariables)
        {
            int allocatedConstants = 0;

            var constraints = new List<BoolExpr>();
            for (int i = 0; i < lines.Count; i++)
            {
                if (lines[i] is VarLine)
                    continue;

                var line = (ExprLine)lines[i];

                // Enforce that operands are defined before they are used
                var op0 = line.Op0;
                var op1 = line.Op1;
                var w0 = BvWidth(i);
                var w1 = op0.SortSize;
                if (w0 > w1)
                {
                    op0 = solver.MkZeroExt((uint)w0 - w1, op0);
                    op1 = solver.MkZeroExt((uint)w0 - w1, op1);

                    //Debugger.Break();
                }
                var lineNumber = solver.MkBV((uint)i, (uint)w0);
                constraints.Add(solver.MkBVULT(op0, lineNumber));
                constraints.Add(solver.MkBVULT(op1, lineNumber));

                var opcodeBitsize = BvWidth(components.Count);
                var opc = line.Opcode;
                if (opc.SortSize < opcodeBitsize)
                    opc = solver.MkZeroExt((uint)opcodeBitsize - opc.SortSize, opc);

                // Eliminate padding bits
                constraints.Add(solver.MkBVULT(opc, solver.MkBV((uint)components.Count, (uint)opcodeBitsize)));

                // If the instruction has one operand, set the 2nd operand to zero.
                bool pruneUnaryOperands = true;
                if (pruneUnaryOperands)
                {
                    if (HasComponent(SynthOpc.Not))
                    {
                        var notComponent = GetComponent(SynthOpc.Not);
                        var isUnary = solver.MkEq(line.Opcode, solver.MkBV(notComponent.Data.Index, line.Opcode.SortSize));

                        var zeroOp = solver.MkEq(op1, solver.MkBV(0, op1.SortSize));

                        constraints.Add(solver.MkImplies(isUnary, zeroOp));
                    }
                }


                bool pruneLshrConstants = true;
                if (pruneLshrConstants)
                {
                    if (HasComponent(SynthOpc.Lshr))
                    {
                        var lshrComponent = GetComponent(SynthOpc.Lshr);
                        var isLshr = solver.MkEq(line.Opcode, solver.MkBV(lshrComponent.Data.Index, line.Opcode.SortSize));

                        var cdata = line.ConstantData;
                        var boundedConstant = solver.MkBVULT(cdata, solver.MkBV(cdata.SortSize, cdata.SortSize));

                        constraints.Add(solver.MkImplies(isLshr, boundedConstant));


                        var shiftVar = shiftVariables[i - lines.Count(x => x is VarLine)];
                        var zeroOp = solver.MkEq(shiftVar, solver.MkBV(0, shiftVar.SortSize));
                        constraints.Add(solver.MkImplies(solver.MkNot(isLshr), zeroOp));

                        //Debugger.Break();


                        // TODO: If this is not a constant or a shift, constraint the constant to be zero.
                       // var zeroOp = solver.MkEq(cdata, solver.MkBV(0, op1.SortSize));
                    }
                }


                // If the instruction is a constant, assert that both operands are equal to zero.
                bool pruneConstantOperands = true;
                if (pruneConstantOperands)
                {
                    if (HasComponent(SynthOpc.Constant) && allocatedConstants < maxConstants)
                    {
                        var constComponent = GetComponent(SynthOpc.Constant);
                        var isConstant = solver.MkEq(line.Opcode, solver.MkBV(constComponent.Data.Index, line.Opcode.SortSize));

                        var zeroOp = solver.MkAnd(solver.MkEq(op0, solver.MkBV(0, op0.SortSize)), solver.MkEq(op1, solver.MkBV(0, op1.SortSize)));

                        constraints.Add(solver.MkImplies(isConstant, zeroOp));
                    }
                }
                // Sort operands of commutative operators
                // Rewrite add(b, a) as add(a, b)
                // NOT has a overlapping constraint, basically asserting that op1 >= op0
                bool sortAssociativeOps = false;
                if (sortAssociativeOps)
                {
                    var associativeOps = components.Where(x => x.Opcode.IsAssociative());
                    foreach (var component in associativeOps)
                    {
                        var isAssociative = solver.MkEq(line.Opcode, solver.MkBV(component.Data.Index, line.Opcode.SortSize));
                        //var sorted = solver.MkBVULE(op0, op1);

                        var sorted = solver.MkBVUGE(op0, op1);

                        constraints.Add(solver.MkImplies(isAssociative, sorted));

                    }
                }

                // Idempotency elimination: Do not allow (a&a), (a|a), (a^a)
                // TODO: ~(~a))
                bool pruneIdempotentOps = true;
                if (pruneIdempotentOps)
                {
                    var idempotentOps = components.Where(x => x.Opcode.IsIdempotent());
                    foreach (var component in idempotentOps)
                    {
                        var isIdempotent = solver.MkEq(line.Opcode, solver.MkBV(component.Data.Index, line.Opcode.SortSize));

                        var zeroOp = solver.MkNot(solver.MkEq(line.Op0, line.Op1));

                        constraints.Add(solver.MkImplies(isIdempotent, zeroOp));
                    }
                }

                // 1 + 2 => 3
                // Assert that at least one operand of a boolean must not be constant
                // For each 2 variable operator, get both operands
                bool constFold = true;
                if (constFold && maxConstants > 0 && HasComponent(SynthOpc.Constant))
                {
                    var constComponent = GetComponent(SynthOpc.Constant);
                    var operands = new List<BitVecExpr>() { line.Op0, line.Op1 };

                    // Get the indices of all possible previous constants
                    var constIndices = Enumerable.Range(lines.Count(x => x is VarLine), maxConstants).TakeWhile(x => x < i).ToList();
                    // Skip if there are no constants before this instruction
                    if (constIndices.Count == 0)
                        goto skip;

                    // Otherwise there are some constants, and one of the children could possibly be a constant.
                    var operandConstraints = new List<BoolExpr>();
                    //for(int i = 0; i < operands.Count; i++)
                    for(int operandIdx = 0; operandIdx < operands.Count; operandIdx++)
                    {
                        // Cases:
                        //  - 0 variables(Constant)
                        //  - 1 variable(Not, Neg, Lshr)
                        //  - 2 variable(And, Add, Or, Xor)

                        var operand = operands[operandIdx];

                        // Create a boolean constraint that checks whether the operand is a  constant
                        var constConstraints = new List<BoolExpr>();
                        foreach(var constIndex in constIndices)
                        {
                            // Check whether the line could be a constant (is it within the range of instructions where we allow constants)
                            var isOperandInConstantRange = solver.MkEq(operand, solver.MkBV(constIndex, operand.SortSize));

                            var constOpc = (lines[constIndex] as ExprLine).Opcode;
                            var isConstantOpcode = solver.MkEq(constOpc, solver.MkBV(constComponent.Data.Index, constOpc.SortSize));

                            constConstraints.Add(solver.MkAnd(isOperandInConstantRange, isConstantOpcode));
                        }

                        // Compute whether the operand is equal to one of the constants
                        var isConstantOperand = solver.MkOr(constConstraints);

                        if (operandIdx == 1 && HasComponent(SynthOpc.Not))
                        {
                            var notComponent = GetComponent(SynthOpc.Not);
                            var isUnary = solver.MkEq(line.Opcode, solver.MkBV(notComponent.Data.Index, line.Opcode.SortSize));
                            isConstantOperand = (BoolExpr)solver.MkITE(isUnary, solver.MkTrue(), isConstantOperand);
                        }

                        operandConstraints.Add(isConstantOperand);
                    }

                    // Implies: If this expression is not a constant, it must have at least one non constant operand
                    var allConstantOperands = solver.MkAnd(operandConstraints);
                    var isConstant = solver.MkEq(line.Opcode, solver.MkBV(constComponent.Data.Index, line.Opcode.SortSize));
                    constraints.Add(solver.MkImplies(solver.MkNot(isConstant), solver.MkNot(allConstantOperands)));

                }

            skip:

                // CSE (common subexpression elimination)
                // Assert that no two lines are identical
                bool pruneCommonSubexp = false;
                if (pruneCommonSubexp)
                {
                    for (int j = i + 1; j < lines.Count; j++)
                    {
                        var l0 = lines[i] as ExprLine;
                        var l1 = lines[j] as ExprLine;
                        var lw0 = l1.Op0.SortSize - l0.Op0.SortSize;
                        if (lw0 > 0)
                        {
                            var ext0 = solver.MkZeroExt(lw0, l0.Op0);
                            var ext1 = solver.MkZeroExt(lw0, l0.Op1);
                            l0 = new ExprLine(l0.Opcode, ext0, ext1, l0.TruthTable, l0.ConstantData);
                        }



                        var sameOpcode = solver.MkEq(l0.Opcode, l1.Opcode);


                        var sameOp0 = solver.MkEq(l0.Op0, l1.Op0);
                        var sameOp1 = solver.MkEq(l0.Op1, l1.Op1);

                        var sameOperands = solver.MkAnd(sameOp0, sameOp1);

                        // TODO: Commutative matching
                        // (a+b) == (b+a)

                        var identical = solver.MkAnd(sameOpcode, sameOperands);
                        constraints.Add(solver.MkNot(identical));
                    }
                }

                // Assert that every instructions is used at least once
                bool useAllSteps = false;
                if (useAllSteps && i != lines.Count - 1)
                {
                    var usageConditions = new List<BoolExpr>();
                    for (int k = i + 1; k < lines.Count; k++)
                    {
                        var k0 = (lines[k] as ExprLine).Op0;
                        var k1 = (lines[k] as ExprLine).Op1;
                        var used0 = solver.MkEq(k0, solver.MkBV(i, k0.SortSize));
                        usageConditions.Add(used0);

                        // We should
                        var used1 = solver.MkEq(k1, solver.MkBV(i, k1.SortSize));
                        usageConditions.Add(used1);
                    }

                    constraints.Add(solver.MkOr(usageConditions));
                }

                if (allocatedConstants < maxConstants)
                {
                    allocatedConstants++;
                }

                else
                {
                    if (HasComponent(SynthOpc.Constant))
                    {
                        var constComponent = GetComponent(SynthOpc.Constant);
                        var notConstant = solver.MkNot(solver.MkEq(line.Opcode, solver.MkBV(constComponent.Data.Index, line.Opcode.SortSize)));
                        constraints.Add(notConstant);
                    }
                }

                /*

                // If the current line number is a power of two, the operands will always be used below it.
                if (BitOperations.PopCount((uint)i) == 1)
                    continue;

                // Assert that each operand is defined before it's used
                var lineNumber = solver.MkBV(i, line.Op0.SortSize);
                constraints.Add(solver.MkBVULT(line.Op0, lineNumber));
                constraints.Add(solver.MkBVULT(line.Op1, lineNumber));
                */
            }

            return solver.MkAnd(constraints);
        }


        private void CEGIS(Solver s, Expr[] symbols, Expr before, Expr after, IReadOnlyList<Line> lines)
        {
            Console.WriteLine("Beginning cegis");

            // Define 'after' as a function to avoid AST explosion during substitution
            var funcName = "synth_func";
            var domain = symbols.Select(x => x.Sort).ToArray();
            //var synthFunc = solver.MkRecFuncDecl(solver.MkSymbol(funcName), domain, after.Sort);
            var synthFunc = solver.MkRecFuncDecl(funcName, domain, after.Sort);
            solver.AddRecDef(synthFunc, symbols, after);


            var sw = Stopwatch.StartNew();

            uint costWidth = 5;
            var componentCosts = components.Select(x => (Expr)solver.MkBV(x.Opcode.GetCost(), costWidth)).ToList();
            //var lineOpcodes = lines.Where(x => x is ExprLine).Select(x => (x as ExprLine).Opcode).ToArray();

            var costSum = (BitVecExpr)solver.MkBV(0, costWidth);
            foreach(var line in lines)
            {
                if (line is not ExprLine exprLine)
                    continue;

                var cost = (BitVecExpr)LinearSelect(exprLine.Opcode, componentCosts);
                costSum = solver.MkBVAdd(costSum, cost);
            }

            // best known cost is 8
            //s.Add(solver.MkBVULT(costSum, solver.MkBV(14, costWidth)));

            s.Add(solver.MkEq(costSum, solver.MkBV(7, costWidth)));


            // Optionally force the last opcode to be something
            bool constrainLastOpcode = false;
            if (constrainLastOpcode)
            {
                var last = lines.Last() as ExprLine;
                var lastopc = (BitVecExpr)last.Opcode;

                // var tgt = solver.MkBV(components.OrderBy(x => x).ToList().IndexOf(SynthOpc.And), lastopc.SortSize);
                // s.Add(solver.MkEq(lastopc, tgt));
            }

            var rng = new SeededRandom();
            var constraints = new List<BoolExpr>();
            var points = new HashSet<ResultVectorKey>();

            var getEquivOnPointsConstraint = (BitVecNum[] bvPoints) =>
            {
                Debug.Assert(bvPoints.All(x => (x.UInt64 % 2) == 1));

                var subBefore = before.Substitute(symbols, bvPoints).Simplify();
                //var subAfter = solver.MkApp(synthFunc, bvPoints);
                var subAfter = after.Substitute(symbols, bvPoints);
                return solver.MkEq(subBefore, subAfter);
            };

            bool boolean = false;
            if (boolean)
            {
                s.Add(GetBooleanEquivalenceConstraint(before, after, symbols));
            }

            else
            {

                var inputCombinations = new ulong[7, 2]
                {
                    //{ 5555555555555555, ~0x5555555555555555ul },
                    /*
                    {  0x5555555555555555, 0xAAAAAAAAAAAAAAA },
                    { 0x5555555555555555, 0xCCCCCCCCCCCCCCC },
                    { 0xAAAAAAAAAAAAAAA, 0xCCCCCCCCCCCCCCC },
                    { 0x1555555555555554, 0xAAAAAAAAAAAAAAA},
                    { 0x9E3779B97F4A7C15, 0xBF58476D1CE4E5B9},
                    { 0x1555555555555554, 0xAAAAAAAAAAAAAAA},
                    { rng.GetRandUlong(), rng.GetRandUlong()},
                    */

                    // 8-bit
                    /*
                    { 40, 64 }, // Maximize ones in output
                     {  160, 89}, // Maximize zeroes in output
                     { 128, 232}, // Max match of 0x55 pattern
                     { 8, 244},  // Max match of 0xAA pattern
                     { 95, 31}, // Max input hamming distance
                    */

                    // 16-bit
                    /*
                    { 65535, 0},
                    { 64435, 1100},
                    { 256, 59555 },
                    { 256, 22511},
                    { 61687, 48984},
                    */

                    //{ 12128012135207198639, 6318731938502352976   },
                    //{ 2117123840593055747, 16329620233116495869  },

                    // 8-bit modular inverse
                    /*
                    { 253, 0 },
                    { 3, 0 },
                    { 131, 0 },
                    */


                    // 8-bit modular inverse (considering even inputs too)
                    // This hand picked input combination allows us to find a solution instantly
                    /*
                     { 188, 0 },
                     { 255, 0 },
                     { 2, 0 },
                     { 131, 0 },
                     { 128, 0 },
                    */

                      { 255, 0 },
                      { 131, 0 },
                      { 119, 0 },
                      { 3, 171 },

                      { 253, 0},
                      { 131, 0},
                      { 249, 0}
                      //{ 0, 0 },
                    //  { 0, 0 },
                };



                // Evaluate the expression on 8 random IO points
                for (var _ = 0; _ < inputCombinations.GetLength(0); _++)
                {


                    var keys = Enumerable.Range(0, symbols.Length)
                        .Select(x => rng.GetRandUlong())
                        .ToArray();

                    //keys = new ulong[] { inputCombinations[_, 0], inputCombinations[_, 1] };
                    keys = new ulong[] { inputCombinations[_, 0] };

                    points.Add(new ResultVectorKey(keys));

                    var bvPoints = keys
                        .Select(x => solver.MkBV(x, (before as BitVecExpr).SortSize))
                        .ToArray();


                    //var subBefore = before.Substitute(symbols, bvPoints).Simplify();
                    //var subAfter = solver.MkApp(synthFunc, bvPoints);
                    //constraints.Add(solver.MkEq(subBefore, subAfter));

                    var constraint = getEquivOnPointsConstraint(bvPoints);
                    constraints.Add(constraint);

                }

                var and = solver.MkAnd(constraints.ToArray());
                s.Add(and);

            }


            while (true)
            {
                bool export = true;
                if (export)
                {

                    Console.WriteLine("Exporting");
                    ExportSmtToFile(solver, s, @"C:\Users\colton\Downloads\Bitwuzla\your_problem.smt2");

                    //Console.WriteLine("Exported");
                    //Console.ReadLine();
                    //Debugger.Break();
                }


                var check = s.Check();
                if (check == Status.UNSATISFIABLE)
                {
                    Debugger.Break();
                }

                sw.Stop();
                Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms");

                var model = s.Model;
                var from = new List<Expr>();
                var to = new List<Expr>();
                foreach (var decl in model.Decls)
                {
                    if (decl.Arity == 0)
                    {
                        from.Add(solver.MkConst(decl));
                        to.Add(model.ConstInterp(decl));
                    }
                }

                var result = after.Substitute(from.ToArray(), to.ToArray()).Simplify();
                Console.WriteLine("\n\nExpr: \n" + result.Simplify());
                Console.WriteLine("");

                var w = ctx.GetWidth(idx);
                var programAst = new List<AstIdx>();
                foreach(var line in lines)
                {
                    // Variables get added immediately.
                    if (line is VarLine varLine)
                    {
                        programAst.Add(inputs[varLine.Index]);
                        continue;
                    }

                    var exprLine = (ExprLine)line;
                    var opcode = (BitVecNum)model.Eval(exprLine.Opcode);
                    var op0 = programAst[((BitVecNum)model.Eval(exprLine.Op0)).Int];
                    var op1 = programAst[((BitVecNum)model.Eval(exprLine.Op1)).Int];
                    var constData = model.Eval(exprLine.ConstantData);
                    //var truthTable = (BitVecNum)model.Eval(exprLine.TruthTable);

                    //SynthOpc opc = components[opcode.Int].Opcode;
                    SynthOpc opc = opcode.Int >= components.Count ? components.Last().Opcode : components[opcode.Int].Opcode;
                    AstIdx node = opc switch
                    {
                        SynthOpc.Constant => ctx.Constant((constData as BitVecNum).UInt64, w),
                        SynthOpc.Not => ctx.Neg(op0), // Neg() is actually bvnot in my IR
                        SynthOpc.And => ctx.And(op0, op1),
                        SynthOpc.Or => ctx.Or(op0, op1),
                        SynthOpc.Xor => ctx.Xor(op0, op1),
                        SynthOpc.Add => ctx.Add(op0, op1),
                        SynthOpc.Sub => ctx.Sub(op0, op1),
                        SynthOpc.Mul => ctx.Mul(op0, op1),
                        SynthOpc.Lshr => ctx.Lshr(op0, ctx.Constant((constData as BitVecNum).UInt64, w)),
                        SynthOpc.TruthTable => throw new NotImplementedException(),
                    };

                    programAst.Add(node);

                }

                Console.WriteLine($"MBA Expr: \n{ctx.GetAstString(programAst.Last())}\n\n");

                Console.WriteLine($"MBA DAG: \n{DagFormatter.Format(ctx, programAst.Last())}\n\n");

                Console.WriteLine($"With cost: {model.Eval(costSum)}\n");

                var equivSolver = solver.MkSolver();

                equivSolver.Add(solver.MkEq(solver.MkExtract(0, 0, symbols[0] as BitVecExpr), solver.MkBV(1, 1)));

                var equiv = ProveEquivalence(equivSolver, before, result) == Status.UNSATISFIABLE;
                Console.WriteLine($"Equivalent: {equiv}");

                foreach (var decl in model.Decls)
                {
                    if (decl.Arity == 0)
                        Console.WriteLine($"{decl.Name} = {model.ConstInterp(decl)}");
                }

                if (equiv)
                {

                    Console.WriteLine("done");
                    Console.ReadLine();
                    Debugger.Break();
                }

                else
                {
                    var bvPoints = symbols.Select(x => (BitVecNum)equivSolver.Model.Eval(x)).ToArray();
                    var constraint = getEquivOnPointsConstraint(bvPoints);
                    s.Add(constraint);
                    Console.WriteLine("");
                }
            }

        }

       

        public static void ExportSmtToFile(Context ctx, Solver solver, string filePath)
        {

            // Ensure the solver is in a state that reflects all constraints
            // (Z3 Solver.ToString() produces SMT-LIB v2 formatted output)
            string smtString = solver.ToString();

            // Standard SMT files should end with (check-sat) and (get-model) 
            // if you want the external solver to perform those actions.
            if (!smtString.Contains("(check-sat)"))
            {
                smtString += "\n(check-sat)\n(get-model)\n";
            }

            System.IO.File.WriteAllText(filePath, smtString);
            Console.WriteLine($"SMT problem exported to: {filePath}");
        }

        private BoolExpr GetEquivalenceConstraint(Expr[] symbols, Expr before, Expr after)
        {
            var forall = solver.MkForall(symbols, solver.MkEq(before, after));
            return forall;
        }

        private Status ProveEquivalence(Solver s, Expr a, Expr b)
        {
            s.Add(solver.MkNot(solver.MkEq(a, b)));
            var check = s.Check();
            return check;
        }

        private BoolExpr GetBooleanEquivalenceConstraint(Expr before, Expr after, Expr[] symbols)
        {
            var rand = new Random();

            var constraints = new List<BoolExpr>();
            long combinationCount = 1L << symbols.Length;

            for (long i = 0; i < combinationCount; i++)
            {
                var values = new Expr[symbols.Length];
                for (int j = 0; j < symbols.Length; j++)
                {
                    var zero = (ulong)rand.NextInt64();
                    var one = (ulong)rand.NextInt64();

                    bool isSet = ((i >> j) & 1) == 1;
                    var sort = ((BitVecExpr)symbols[j]).SortSize;
                    values[j] = isSet ? solver.MkBV(one, sort) : solver.MkBV(zero, sort);
                }

                var subBefore = before.Substitute(symbols, values);
                var subAfter = after.Substitute(symbols, values);

                constraints.Add(solver.MkEq(subBefore, subAfter));
            }

            return solver.MkAnd(constraints.ToArray());
        }

    }
}
