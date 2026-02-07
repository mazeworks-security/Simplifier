using Mba.Ast;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Synthesis;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Globalization;
using System.Linq;
using System.Linq.Expressions;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;
using static System.Net.Mime.MediaTypeNames;

namespace Mba.Simplifier.Synth
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
        Shl,

        // Special
        TruthTable,

        Constant,
    }

    public abstract record Line();
    public record VarLine(int Index, Expr Symbol) : Line();
    public record ExprLine(BitVecExpr Opcode, BitVecExpr Op0, BitVecExpr Op1, Expr TruthTable, BitVecExpr ConstantData) : Line();

    public class BrahmaSynthesis
    {
        private readonly AstCtx mbaCtx;
        private readonly AstIdx mbaIdx;
        private readonly List<AstIdx> mbaInputs;

        private readonly Context ctx;
        private readonly Z3Translator translator;

        // Config:
        // 7 is optimal for 8-bit modular inverse
        private readonly int numInstructions = 13;


        private bool usesTruthOperator = false;
        private const int TRUTHVARS = 2;
        private const uint TRUTHSIZE = 1u << TRUTHVARS;

        private int maxConstants = 3;

        private uint opcodeBitsize = uint.MaxValue;


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
            new(SynthOpc.Or),
            //new(SynthOpc.TruthTable)

            new(SynthOpc.Xor),

            new(SynthOpc.Add),
            //new(SynthOpc.Sub),
            //new(SynthOpc.Mul),

            //new(SynthOpc.Lshr),
        };

        public BrahmaSynthesis(AstCtx mbaCtx, AstIdx mbaIdx)
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




            this.mbaCtx = mbaCtx;
            this.mbaIdx = mbaIdx;
            mbaInputs = mbaCtx.CollectVariables(mbaIdx);

            this.ctx = new();
            this.ctx.PrintMode = Z3_ast_print_mode.Z3_PRINT_LOW_LEVEL;
            translator = new Z3Translator(mbaCtx, this.ctx);
        }

        // Ideas:
        //      - Tree synthesis
        //      - Heuristic for finding good quality counterexamples. Small functions or partial inputs cover large parts of the truth table. 
        //      -   Feasible for boolean circuits. Needs to be generalized for word level expressions. 
        //  
        public void Run()
        {

            var before = translator.Translate(mbaIdx);

            var (lines, shiftVariables, constantVariables) = GetLines();

            int li = 0;
            foreach (var line in lines)
            {
                if (line is not ExprLine exprLine)
                {
                    li++;
                    continue;
                }
                Console.WriteLine($"{exprLine.Opcode.SortSize}({exprLine.Op0.SortSize}, {exprLine.Op1.SortSize}) with {li} operands to choose from ");
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


            var s = ctx.MkSolver();
            var constraints = GetProgramConstraints(lines, shiftVariables);

            // Print `constraints` to dimacs file in CNF


            // Optionally hardcode constants
            /*
            var c0 = constantVariables[0];
            var c1 = constantVariables[1];
            s.Add(solver.MkEq(c0, solver.MkBV(60, 8)));
            s.Add(solver.MkEq(c1, solver.MkBV(82, 8)));
            */

            s.Add(constraints);


            ExportSmtToFile(ctx, s, "C:\\Users\\colton\\Downloads\\Bitwuzla\\your_problem.smt2");

            CEGIS(s, symbols, before, after, lines);

            Debugger.Break();
        }

        private (IReadOnlyList<Line>, List<BitVecExpr> shiftVariables, List<BitVecExpr> constantVariables) GetLines()
        {
            var lines = new List<Line>();
            var shiftVariables = new List<BitVecExpr>();
            var constantVariables = new List<BitVecExpr>();

            // Each variable gets assigned its own line
            for (int i = 0; i < mbaInputs.Count; i++)
                lines.Add(new VarLine(i, translator.cache[mbaInputs[i]]));

            // Each instruction gets assigned its own line.
            opcodeBitsize = (uint)BvWidth(components.Count - 1);
            //var opcodeBitsize = GetBitsNeeded(32);

            int allocatedConstants = 0;
            for (int i = lines.Count; i < numInstructions; i++)
            {
                // Choose the opcode
                var opcode = ctx.MkBVConst($"code{i}", opcodeBitsize);

                // Choose the operands
                var operandBitsize = BvWidth(i - 1);
                //Console.WriteLine($"Got {other} bits needed for operands of line {i} with lz {BitOperations.LeadingZeroCount((ulong)i)}");
                var op0 = ctx.MkBVConst($"{i}_op0", (uint)operandBitsize);
                var op1 = ctx.MkBVConst($"{i}_op1", (uint)operandBitsize);

                Expr truthTable = null;
                if (usesTruthOperator)
                    truthTable = ctx.MkBVConst($"{i}_tt", TRUTHSIZE);

                BitVecExpr constant = ctx.MkBV(0, mbaCtx.GetWidth(mbaIdx));
                if (HasComponent(SynthOpc.Lshr))
                {
                    // Compute the minimum number of bits necessary to fit the shift
                    var shiftByWidth = BvWidth(mbaCtx.GetWidth(mbaIdx));

                    var shiftBy = ctx.MkBVConst($"{i}_shift", (uint)shiftByWidth);
                    shiftVariables.Add(shiftBy);
                    if (shiftBy.SortSize < constant.SortSize)
                        shiftBy = ctx.MkZeroExt(constant.SortSize - shiftBy.SortSize, shiftBy);


                    var lshrComponent = GetComponent(SynthOpc.Lshr);
                    var isLshr = ctx.MkEq(opcode, ctx.MkBV(lshrComponent.Data.Index, opcode.SortSize));

                    constant = (BitVecExpr)ctx.MkITE(isLshr, shiftBy, constant);
                }

                if (allocatedConstants < maxConstants)
                {
                    constant = ctx.MkBVConst($"{i}_const", mbaCtx.GetWidth(mbaIdx));

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
                        SynthOpc.Not => ctx.MkBVNot(op0),
                        SynthOpc.And => ctx.MkBVAND(op0, op1),
                        SynthOpc.Or => ctx.MkBVOR(op0, op1),
                        SynthOpc.Xor => ctx.MkBVXOR(op0, op1),
                        SynthOpc.Add => ctx.MkBVAdd(op0, op1),
                        SynthOpc.Sub => ctx.MkBVSub(op0, op1),
                        SynthOpc.Mul => ctx.MkBVMul(op0, op1),
                        SynthOpc.TruthTable => TruthTableToExpr((BitVecExpr)exprLine.TruthTable, op0, op1),
                        SynthOpc.Constant => exprLine.ConstantData,
                        SynthOpc.Lshr => ctx.MkBVLSHR(op0, exprLine.ConstantData), // TODO: Assert that op1 is a constant

                        _ => throw new InvalidOperationException()
                    };
                    candidates.Add(expr);
                }

                Expr select = null;
                bool select3 = false;
                if (select3 && candidates.Count == 3)
                    select = Select3(exprLine.Opcode, candidates);
                else
                    select = LinearSelect(exprLine.Opcode, candidates);

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
            => ctx.MkBVOR(ctx.MkBVAND(cond, onTrue), ctx.MkBVAND(ctx.MkBVNot(cond), onFalse));

        private BitVecExpr GetMask(uint width, uint index, BitVecExpr tableBv)
        {
            var bit = ctx.MkExtract(index, index, tableBv);
            return (BitVecExpr)ctx.MkITE(ctx.MkEq(bit, ctx.MkBV(1, 1)), ctx.MkBV(ulong.MaxValue, width), ctx.MkBV(0, width));
        }

        private Expr SelectOperand(Expr selector, List<Expr> exprs)
        {
            return LinearSelect((BitVecExpr)selector, exprs);
        }

        private Expr Select3(BitVecExpr index, List<Expr> elements)
        {
            Debug.Assert(elements.Count == 3);

            var b0 = ctx.MkExtract(0, 0, index);
            var b1 = ctx.MkExtract(1, 1, index);

            var lowerHalf = ctx.MkITE(ctx.MkEq(b0, ctx.MkBV(1, 1)), elements[1], elements[0]);
            return ctx.MkITE(ctx.MkEq(b1, ctx.MkBV(1, 1)), elements[2], lowerHalf);
        }

        // Given a symbolic index and a list of N values, pick the ith value
        private Expr LinearSelect(BitVecExpr index, List<Expr> options)
        {
            int n = options.Count;
            if (n == 0)
                throw new InvalidOperationException();
            if (n == 1)
                return options[0];

            var casted = options.Select(x => x).ToList();

            if (n > 12)
                return PrunedSelect(index, casted);


            var result = options[n - 1];

            for (int i = n - 2; i >= 0; i--)
            {
                BoolExpr condition = ctx.MkEq(index, ctx.MkBV(i, index.SortSize));
                result = ctx.MkITE(condition, options[i], result);
            }

            return result;
        }

        public Expr PrunedSelect(BitVecExpr index, List<Expr> options)
        {
            return BuildPrunedTree(ctx, index, options, 0, options.Count);
        }

        private static Expr BuildPrunedTree(Context ctx, BitVecExpr index, List<Expr> options, int offset, int count)
        {
            if (count == 1) return options[offset];

            int requiredBits = (int)Math.Ceiling(Math.Log2(count));
            int msbIndex = requiredBits - 1;
            int splitSize = 1 << msbIndex;
            int rightCount = count - splitSize;

            BitVecExpr condBit = ctx.MkExtract((uint)msbIndex, (uint)msbIndex, index);
            BoolExpr condition = ctx.MkEq(condBit, ctx.MkBV(1, 1));

            // Visit next branch of the tree
            var lowResult = BuildPrunedTree(ctx, index, options, offset, splitSize);
            var highResult = BuildPrunedTree(ctx, index, options, offset + splitSize, rightCount);

            return ctx.MkITE(condition, highResult, lowResult);
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

                // Assert that every instructions is used at least once
                bool useAllSteps = true;
                if (useAllSteps && i != lines.Count - 1)
                {
                    var usageConditions = new List<BoolExpr>();
                    for (int k = i + 1; k < lines.Count; k++)
                    {
                        // Skip if this line is not an instruction
                        if (lines[k] is not ExprLine casted)
                            continue;

                        var k0 = (lines[k] as ExprLine).Op0;
                        var k1 = (lines[k] as ExprLine).Op1;

                        // Add constraint: If the instruction has one or more operands, operands[0] == curr
                        var used0 = ctx.MkEq(k0, ctx.MkBV(i, k0.SortSize));
                        var oneOperand = AtleastNOperands(lines[k] as ExprLine, 1);
                        usageConditions.Add(And(oneOperand, used0));

                        // Repeat for the two input case
                        var used1 = ctx.MkEq(k1, ctx.MkBV(i, k1.SortSize));
                        var twoOperand = AtleastNOperands(lines[k] as ExprLine, 2);
                        usageConditions.Add(And(twoOperand, used1));
                    }

                    // Constraint: This instruction has at least one use.
                    constraints.Add(ctx.MkOr(usageConditions));
                }

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
                    op0 = ctx.MkZeroExt((uint)w0 - w1, op0);
                    op1 = ctx.MkZeroExt((uint)w0 - w1, op1);

                    //Debugger.Break();
                }
                var lineNumber = ctx.MkBV((uint)i, (uint)w0);
                constraints.Add(ctx.MkBVULT(op0, lineNumber));
                constraints.Add(ctx.MkBVULT(op1, lineNumber));

                var opcodeBitsize = BvWidth(components.Count);
                var opc = line.Opcode;
                if (opc.SortSize < opcodeBitsize)
                    opc = ctx.MkZeroExt((uint)opcodeBitsize - opc.SortSize, opc);

                // Eliminate padding bits
                constraints.Add(ctx.MkBVULT(opc, ctx.MkBV((uint)components.Count, (uint)opcodeBitsize)));

                // If the instruction has one operand, set the 2nd operand to zero.
                bool pruneUnaryOperands = true;
                if (pruneUnaryOperands)
                {
                    if (HasComponent(SynthOpc.Not))
                    {
                        var notComponent = GetComponent(SynthOpc.Not);
                        var isUnary = ctx.MkEq(line.Opcode, ctx.MkBV(notComponent.Data.Index, line.Opcode.SortSize));

                        var zeroOp = ctx.MkEq(op1, ctx.MkBV(0, op1.SortSize));

                        constraints.Add(ctx.MkImplies(isUnary, zeroOp));
                    }
                }


                bool pruneLshrConstants = true;
                if (pruneLshrConstants)
                {
                    if (HasComponent(SynthOpc.Lshr))
                    {
                        var lshrComponent = GetComponent(SynthOpc.Lshr);
                        var isLshr = ctx.MkEq(line.Opcode, ctx.MkBV(lshrComponent.Data.Index, line.Opcode.SortSize));

                        var cdata = line.ConstantData;
                        var boundedConstant = ctx.MkBVULT(cdata, ctx.MkBV(cdata.SortSize, cdata.SortSize));

                        constraints.Add(ctx.MkImplies(isLshr, boundedConstant));


                        var shiftVar = shiftVariables[i - lines.Count(x => x is VarLine)];
                        var zeroOp = ctx.MkEq(shiftVar, ctx.MkBV(0, shiftVar.SortSize));
                        constraints.Add(ctx.MkImplies(ctx.MkNot(isLshr), zeroOp));

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
                        var isConstant = ctx.MkEq(line.Opcode, ctx.MkBV(constComponent.Data.Index, line.Opcode.SortSize));

                        var zeroOp = And(ctx.MkEq(op0, ctx.MkBV(0, op0.SortSize)), ctx.MkEq(op1, ctx.MkBV(0, op1.SortSize)));

                        constraints.Add(ctx.MkImplies(isConstant, zeroOp));
                    }
                }
                // Sort operands of commutative operators
                // Rewrite add(b, a) as add(a, b)
                // NOT has a overlapping constraint, basically asserting that op1 >= op0
                // TODO: I think this needs to take other synthesis constraints into account?
                // TODO: Need to implement associative sorting too. Would prune the search space further
                bool sortCommutativeOps = true;
                if (sortCommutativeOps)
                {

                    /*
                    var isAssociative = new List<BoolExpr>();
                    var ac = components.Where(x => x.Opcode.IsCommutative()).ToList();
                    foreach (var component in ac)
                    {
                        isAssociative.Add(IsComponent(line, component.Opcode));
                    }

                    var sorted = solver.MkBVULE(op0, op1);
                    constraints.Add(solver.MkImplies(solver.MkOr(isAssociative), sorted));
                    */

                    // Alternative encoding that is for some reason not faster
                    /*
                    var decisions = components.Select(x => (Expr)solver.MkBool(x.Opcode.IsAssociative())).ToList();
                    var isAssociative = (BoolExpr)LinearSelect(line.Opcode, decisions);

                    //var sorted = solver.MkBVULE(op0, op1);
                    var sorted = solver.MkBVUGE(op0, op1);
                    constraints.Add(solver.MkImplies(isAssociative, sorted));
                    */


                    // This encoding is actually better than all of the other encodings..
                    // Many imply statements are better than one big implies statement I guess
                    var associativeOps = components.Where(x => x.Opcode.IsCommutative());
                    foreach (var component in associativeOps)
                    {
                        var isAssociative = ctx.MkEq(line.Opcode, ctx.MkBV(component.Data.Index, line.Opcode.SortSize));
                        // Ascending order is apparently faster despite the unary operand optimization thing
                        var sorted = ctx.MkBVULE(op0, op1);

                        //var sorted = solver.MkBVUGE(op0, op1);

                        constraints.Add(ctx.MkImplies(isAssociative, sorted));
                    }






                }

                // TODO: Constant position elimination. Constants cannot be allocated after the first instruction.
                // Actually.. sorting solves this

                // Idempotency elimination: Do not allow (a&a), (a|a), (a^a)
                // TODO: ~(~a))
                bool pruneIdempotentOps = true;
                if (pruneIdempotentOps)
                {
                    var idempotentOps = components.Where(x => x.Opcode.IsIdempotent());
                    foreach (var component in idempotentOps)
                    {
                        var isIdempotent = ctx.MkEq(line.Opcode, ctx.MkBV(component.Data.Index, line.Opcode.SortSize));

                        var zeroOp = ctx.MkNot(ctx.MkEq(line.Op0, line.Op1));

                        constraints.Add(ctx.MkImplies(isIdempotent, zeroOp));
                    }
                }

                // Theres a bug with the current const folding encoding
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
                    for (int operandIdx = 0; operandIdx < operands.Count; operandIdx++)
                    {
                        // Cases:
                        //  - 0 variables(Constant)
                        //  - 1 variable(Not, Neg, Lshr)
                        //  - 2 variable(And, Add, Or, Xor)

                        var operand = operands[operandIdx];

                        // Create a boolean constraint that checks whether the operand is a  constant
                        var constConstraints = new List<BoolExpr>();
                        foreach (var constIndex in constIndices)
                        {
                            // Check whether the line could be a constant (is it within the range of instructions where we allow constants)
                            var isOperandInConstantRange = ctx.MkEq(operand, ctx.MkBV(constIndex, operand.SortSize));

                            var constOpc = (lines[constIndex] as ExprLine).Opcode;
                            var isConstantOpcode = ctx.MkEq(constOpc, ctx.MkBV(constComponent.Data.Index, constOpc.SortSize));

                            constConstraints.Add(And(isOperandInConstantRange, isConstantOpcode));
                        }

                        // Compute whether the operand is equal to one of the constants
                        var isConstantOperand = constConstraints.Count == 1 ? constConstraints.Single() : ctx.MkOr(constConstraints);

                        if (operandIdx == 1 && HasComponent(SynthOpc.Not))
                        {
                            var notComponent = GetComponent(SynthOpc.Not);
                            var isUnary = ctx.MkEq(line.Opcode, ctx.MkBV(notComponent.Data.Index, line.Opcode.SortSize));
                            isConstantOperand = (BoolExpr)ctx.MkITE(isUnary, ctx.MkTrue(), isConstantOperand);
                        }

                        operandConstraints.Add(isConstantOperand);
                    }

                    // Implies: If this expression is not a constant, it must have at least one non constant operand
                    var allConstantOperands = And(operandConstraints);
                    var isConstant = ctx.MkEq(line.Opcode, ctx.MkBV(constComponent.Data.Index, line.Opcode.SortSize));
                    constraints.Add(ctx.MkImplies(ctx.MkNot(isConstant), ctx.MkNot(allConstantOperands)));

                }

            skip:

                // Only allow multiplication if one operand is a constant
                bool forceConstMultiply = true;
                if (HasComponent(SynthOpc.Mul) && forceConstMultiply)
                {
                    var constComponent = GetComponent(SynthOpc.Constant);
                    var operands = new List<BitVecExpr>() { line.Op0, line.Op1 };

                    // Get the indices of all possible previous constants
                    var constIndices = Enumerable.Range(lines.Count(x => x is VarLine), maxConstants).TakeWhile(x => x < i).ToList();
                    // Skip if there are no constants before this instruction
                    if (constIndices.Count == 0)
                        goto skip2;

                    // Otherwise there are some constants, and one of the children could possibly be a constant.
                    var operandConstraints = new List<BoolExpr>();
                    //for(int i = 0; i < operands.Count; i++)
                    for (int operandIdx = 0; operandIdx < operands.Count; operandIdx++)
                    {
                        // Cases:
                        //  - 0 variables(Constant)
                        //  - 1 variable(Not, Neg, Lshr)
                        //  - 2 variable(And, Add, Or, Xor)

                        var operand = operands[operandIdx];

                        // Create a boolean constraint that checks whether the operand is a  constant
                        var constConstraints = new List<BoolExpr>();
                        foreach (var constIndex in constIndices)
                        {
                            // Check whether the line could be a constant (is it within the range of instructions where we allow constants)
                            var isOperandInConstantRange = ctx.MkEq(operand, ctx.MkBV(constIndex, operand.SortSize));

                            var constOpc = (lines[constIndex] as ExprLine).Opcode;
                            var isConstantOpcode = ctx.MkEq(constOpc, ctx.MkBV(constComponent.Data.Index, constOpc.SortSize));

                            constConstraints.Add(And(isOperandInConstantRange, isConstantOpcode));
                        }

                        // Compute whether the operand is equal to one of the constants
                        var isConstantOperand = constConstraints.Count == 1 ? constConstraints.Single() : ctx.MkOr(constConstraints);
                        operandConstraints.Add(isConstantOperand);
                    }

                    // Enforce that multiplication is only allowed if one operand is a constant
                    var anyConstOperand = ctx.MkOr(operandConstraints);
                    constraints.Add(ctx.MkImplies(IsComponent(line, SynthOpc.Mul), anyConstOperand));

                    /*
                    // If either operand is a constant, treat them as dependent. We'll handle with special logic
                    var const0 = IsComponent(line.Op0, SynthOpc.Constant);
                    var const1 = IsComponent(next, SynthOpc.Constant);
                    var anyConstants = solver.MkOr(const0, const1);
                    dependencyConstraints.Add(anyConstants);
                    */
                }

            skip2:


                // If you have two instructions that do not depend on each other:
                // %0 = c+d
                // %1 = a&b
                // sort them by their operands:
                // %0 = a&b
                // %1 = c+d
                bool pruneAdjacentSymmetry = true;
                if (pruneAdjacentSymmetry && i + 1 < lines.Count)
                {
                    var next = lines[i + 1] as ExprLine;

                    // TODO: If we have more 12 or more components, we probably want to use a different encoding.
                    List<BoolExpr> dependencyConstraints = new List<BoolExpr>();
                    foreach (var component in components)
                    {
                        var count = component.Opcode.GetOperandCount();
                        if (count == 0)
                            continue;

                        var isOpcode = IsComponent(next, component);
                        var diff0 = Different(next.Op0, ctx.MkBV(i, next.Op0.SortSize));
                        if (count == 1)
                        {
                            // Assert that the this instruction does not use the other.
                            dependencyConstraints.Add(ctx.MkImplies(isOpcode, diff0));
                            continue;
                        }

                        Debug.Assert(count == 2);
                        var diff1 = Different(next.Op1, ctx.MkBV(i, next.Op0.SortSize));
                        dependencyConstraints.Add(ctx.MkImplies(isOpcode, And(diff0, diff1)));
                    }

                    // If this instruction could be a constant, disable the opcode based sorting logic and instead apply a special canonicalization:
                    if (HasComponent(SynthOpc.Constant) && allocatedConstants < maxConstants)
                    {
                        // If either operand is a constant, treat them as dependent. We'll handle with special logic
                        var const0 = IsComponent(line, SynthOpc.Constant);
                        var const1 = IsComponent(next, SynthOpc.Constant);
                        var anyConstants = ctx.MkOr(const0, const1);
                        dependencyConstraints.Add(anyConstants);

                        // Rewrite:
                        // %0 = a+b
                        // %1 = 1111
                        // 
                        // to:
                        // %0 = 1111
                        // %1 = a+b
                        var sortConstant = And(const1, ctx.MkNot(const0));
                        constraints.Add(ctx.MkNot(sortConstant));


                        var bothConst = And(const0, const1);
                        constraints.Add(ctx.MkImplies(bothConst, ctx.MkBVULT(line.ConstantData, next.ConstantData)));
                    }


                    // Most expensive instructions are at the top of the list.. e.g. 0==div, because of the encoding we chose.
                    // So we want to sort opcodes in descending order. AND, XOR, etc are assigned the largest opcodes.
                    var depends = ctx.MkOr(dependencyConstraints);
                    var sortOpcode = ctx.MkBVUGE(line.Opcode, next.Opcode);
                    constraints.Add(ctx.MkImplies(ctx.MkNot(depends), sortOpcode));

                    // Tie breaker: Operands
                    var tie = And(ctx.MkNot(depends), ctx.MkEq(line.Opcode, next.Opcode));

                    // TODO: You have a very global encoding when you should instead be doing a local encoding. This encoding is bad for unit propagation.
                    // Prefer many implies over one big imply
                    var zextBy = next.Op0.SortSize - line.Op0.SortSize;
                    var args0 = new BitVecExpr[] { line.Op0, line.Op1 }.Select(x => zextBy == 0 ? x : ctx.MkZeroExt(zextBy, x)).ToArray();
                    var args1 = new BitVecExpr[] { next.Op0, next.Op1 };

                    var (j, k) = (args0[0], args0[1]);
                    var (jNext, kNext) = (args1[0], args1[1]);
                    var smaller = ctx.MkOr(ctx.MkBVULT(j, jNext), And(ctx.MkEq(j, jNext), ctx.MkBVULT(k, kNext)));
                    constraints.Add(ctx.MkImplies(tie, smaller));

                    //solver.MkImplies(sortConstant,);
                }

                // CSE (common subexpression elimination)
                // Assert that no two lines are identical
                bool pruneCommonSubexp = true;
                if (pruneCommonSubexp)
                {
                    for (int j = i + 1; j < lines.Count; j++)
                    {
                        var l0 = lines[i] as ExprLine;
                        var l1 = lines[j] as ExprLine;
                        var lw0 = l1.Op0.SortSize - l0.Op0.SortSize;
                        if (lw0 > 0)
                        {
                            var ext0 = ctx.MkZeroExt(lw0, l0.Op0);
                            var ext1 = ctx.MkZeroExt(lw0, l0.Op1);
                            l0 = new ExprLine(l0.Opcode, ext0, ext1, l0.TruthTable, l0.ConstantData);
                        }


                        // Having the same opcode implies that at least one operand is different
                        // Though we need to imply conditionally check the number of operands.


                        foreach (var component in components)
                        {
                            var count = component.Opcode.GetOperandCount();
                            if (count == 0)
                                continue;

                            var sameOpcode = ctx.MkEq(l0.Opcode, l1.Opcode);

                            // Change the implication to "we have the same opcode and the opcode == this"
                            sameOpcode = And(sameOpcode, IsComponent(line, component));

                            // For a unary operation, assert that the operands are different if they have the same opcode.
                            if (count == 1)
                            {

                                constraints.Add(ctx.MkImplies(sameOpcode, Different(l0.Op0, l1.Op0)));
                                continue;
                            }


                            // Otherwise there are 2 operands.
                            Debug.Assert(count == 2);
                            var diff0 = Different(l0.Op0, l1.Op0);
                            var diff1 = Different(l0.Op1, l1.Op1);
                            constraints.Add(ctx.MkImplies(sameOpcode, ctx.MkOr(diff0, diff1)));
                        }

                        /*
                        var sameOp0 = solver.MkEq(l0.Op0, l1.Op0);
                        var sameOp1 = solver.MkEq(l0.Op1, l1.Op1);

                        var sameOperands = solver.MkAnd(sameOp0, sameOp1);

                        // TODO: Commutative matching
                        // (a+b) == (b+a)

                        var identical = solver.MkAnd(sameOpcode, sameOperands);
                        constraints.Add(solver.MkNot(identical));
                        */

                    }
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
                        var notConstant = ctx.MkNot(ctx.MkEq(line.Opcode, ctx.MkBV(constComponent.Data.Index, line.Opcode.SortSize)));
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

            return And(constraints);
        }

        private BoolExpr Different(Expr a, Expr b)
            => ctx.MkNot(ctx.MkEq(a, b));

        // Return a constraint that the line has atleast one operand
        private BoolExpr AtleastNOperands(ExprLine line, int n)
        {
            List<BoolExpr> constraints = new();

            var zeroComponents = components.Select(x => x.Opcode).Where(x => x.GetOperandCount() < n).ToList();
            if (zeroComponents.Count == 0)
                return ctx.MkTrue();

            foreach (var c in zeroComponents)
                constraints.Add(ctx.MkNot(IsComponent(line, c)));
            if (constraints.Count == 1)
                return constraints.Single();
            return And(constraints);
        }

        private BoolExpr ExactlyNOperands(ExprLine line, int n)
        {
            List<BoolExpr> constraints = new();

            var zeroComponents = components.Select(x => x.Opcode).Where(x => x.GetOperandCount() == n).ToList();
            if (zeroComponents.Count == 0)
                return ctx.MkTrue();

            foreach (var c in zeroComponents)
                constraints.Add(IsComponent(line, c));
            if (constraints.Count == 1)
                return constraints.Single();
            return And(constraints);
        }

        private BoolExpr IsComponent(ExprLine line, SynthOpc component)
        {
            return ctx.MkEq(line.Opcode, GetComponentIndexBv(component));
        }

        private BoolExpr IsComponent(ExprLine line, Component component)
            => IsComponent(line, component.Opcode);

        private BitVecExpr GetComponentIndexBv(SynthOpc opc)
        {
            return ctx.MkBV(GetComponent(opc).Data.Index, opcodeBitsize);
        }


        private void CEGIS(Solver s, Expr[] symbols, Expr before, Expr after, IReadOnlyList<Line> lines)
        {
            bool minv = false;
            Console.WriteLine("Beginning cegis");

            // Define 'after' as a function to avoid AST explosion during substitution
            var funcName = "synth_func";
            var domain = symbols.Select(x => x.Sort).ToArray();
            //var synthFunc = solver.MkRecFuncDecl(solver.MkSymbol(funcName), domain, after.Sort);
            var synthFunc = ctx.MkRecFuncDecl(funcName, domain, after.Sort);
            ctx.AddRecDef(synthFunc, symbols, after);


       
            uint costWidth = 6;
            var componentCosts = components.Select(x => (Expr)ctx.MkBV(x.Opcode.GetCost(), costWidth)).ToList();
            //var lineOpcodes = lines.Where(x => x is ExprLine).Select(x => (x as ExprLine).Opcode).ToArray();

            var costSum = (BitVecExpr)ctx.MkBV(0, costWidth);
            foreach (var line in lines)
            {
                if (line is not ExprLine exprLine)
                    continue;

                var cost = (BitVecExpr)LinearSelect(exprLine.Opcode, componentCosts);
                costSum = ctx.MkBVAdd(costSum, cost);
            }

            // best known cost is 8
            //s.Add(solver.MkBVULT(costSum, solver.MkBV(14, costWidth)));
            //s.Add(solver.MkBVULT(costSum, solver.MkBV(32, costWidth)));

            //s.Add(solver.MkEq(costSum, solver.MkBV(8, costWidth)));

            //s.Add(solver.MkEq(costSum, solver.MkBV(0, costWidth)));


            // Optionally force the last opcode to be something
            bool constrainLastOpcode = false;
            if (constrainLastOpcode)
            {
                var last = lines.Last() as ExprLine;
                var lastopc = last.Opcode;

                // var tgt = solver.MkBV(components.OrderBy(x => x).ToList().IndexOf(SynthOpc.And), lastopc.SortSize);
                // s.Add(solver.MkEq(lastopc, tgt));
            }

            var rng = new SeededRandom();
            var constraints = new List<BoolExpr>();
            var points = new HashSet<ResultVectorKey>();

            var getEquivOnPointsConstraint = (BitVecNum[] bvPoints) =>
            {
                if (minv)
                    Debug.Assert(bvPoints.All(x => x.UInt64 % 2 == 1));

                var subBefore = before.Substitute(symbols, bvPoints).Simplify();
                //var subAfter = solver.MkApp(synthFunc, bvPoints);
                var subAfter = after.Substitute(symbols, bvPoints);
                return ctx.MkEq(subBefore, subAfter);
            };

            bool boolean = false;
            if (boolean)
            {
                s.Add(GetBooleanEquivalenceConstraint(before, after, symbols));
            }

            else
            {

                var inputCombinations = new ulong[3, 2]
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
                        
                    // 8-bit optimal synthesis:
                    /*
                      { 255, 0 },
                      { 131, 0 },
                      { 119, 0 },
                      { 3, 171 },

                      { 253, 0},
                      { 131, 0},
                      { 249, 0}
                    */
                        
                        /*
                      { 65535, 0 },

                      { 27785, 0},
                      //{ 64765, 0},
                      //{ 64003, 0},
                      //{ 27785, 0},
                       { 3, 0},
                       { 46661, 0 }
                        */

                    /*
                    { 65535, 0 },
                    { 64509, 1026  },
                    { 64384, 12437 },
                    { 64256, 61119 },
                    */

                    /*
                    { 4, 248 },
                    { 168, 21 },
                    { 224, 18 },
                    { 52, 211 },
                    //{ 105, 80 },

                    //{ 20521, 43908 },
                      { 70, 178 },
                    */

                    { 404801, 16372414   },
                    { 9989854, 6787361    },
                     { 5631938, 5391020    },
                    //{ 12162971954278319982, 6283772119431231633  },
                    //{ 2939599917423341567, 0  },
                    //{ 12162971954278319982, 6283772119431231633 },
                    //{ 12162971962868015873, 0 },

                    //  { 0, 0 },
                };



                // Evaluate the expression on 8 random IO points
                // for (var _ = 0; _ < 1; _++)
                //for (var _ = 0; _ < inputCombinations.GetLength(0); _++)
                for (var _ = 0; _ < 1; _++)
                {


                    var keys = Enumerable.Range(0, symbols.Length)
                        .Select(x => rng.GetRandUlong())
                        .ToArray();

                    //keys = new ulong[] { inputCombinations[_, 0], inputCombinations[_, 1] };

                    points.Add(new ResultVectorKey(keys));

                    var bvPoints = keys
                        .Select(x => ctx.MkBV(x, (before as BitVecExpr).SortSize))
                        .ToArray();


                    //var subBefore = before.Substitute(symbols, bvPoints).Simplify();
                    //var subAfter = solver.MkApp(synthFunc, bvPoints);
                    //constraints.Add(solver.MkEq(subBefore, subAfter));

                    var constraint = getEquivOnPointsConstraint(bvPoints);
                    constraints.Add(constraint);

                }

                var and = And(constraints.ToArray());
                s.Add(and);

            }


            var skeletons = new List<Expr>();

            var iii = 0;
            var total = Stopwatch.StartNew();
            var sw = Stopwatch.StartNew();

            while (true)
            {
                bool export = true;
                if (export)
                {

                    Console.WriteLine("Exporting");
                    ExportSmtToFile(ctx, s, @"C:\Users\colton\Downloads\Bitwuzla\your_problem.smt2");

                    //Console.WriteLine("Exported");
                    //Console.ReadLine();
                    //Debugger.Break();
                }


                var check = s.Check();
                if (check == Status.UNSATISFIABLE)
                {
                    Console.WriteLine($"No solution. Took {total.ElapsedMilliseconds}");
                    Debugger.Break();
                }

                sw.Stop();
                Console.WriteLine($"Took {sw.ElapsedMilliseconds}ms");
                sw = Stopwatch.StartNew();

                var model = s.Model;
                var from = new List<Expr>();
                var to = new List<Expr>();
                foreach (var decl in model.Decls)
                {
                    if (decl.Arity == 0)
                    {
                        from.Add(ctx.MkConst(decl));
                        to.Add(model.ConstInterp(decl));
                    }
                }

                var result = after.Substitute(from.ToArray(), to.ToArray()).Simplify();
                //Console.WriteLine("\n\nExpr: \n" + result.Simplify());
                //Console.WriteLine("");

                var w = mbaCtx.GetWidth(mbaIdx);
                var programAst = new List<AstIdx>();
                List<BitVecExpr> z3ProgramAst = new List<BitVecExpr>();

                Dictionary<Expr, Expr> bannedModel = new();
                for (int li = 0; li < lines.Count; li++)
                {
                    var line = lines[li];
                    // Variables get added immediately.
                    if (line is VarLine varLine)
                    {
                        programAst.Add(mbaInputs[varLine.Index]);
                        z3ProgramAst.Add((BitVecExpr)symbols[varLine.Index]);
                        continue;
                    }

                    var exprLine = (ExprLine)line;
                    var opcode = (BitVecNum)model.Eval(exprLine.Opcode);

                    var op0Value = model.Eval(exprLine.Op0);
                    var op1Value = model.Eval(exprLine.Op1);
                    if (op0Value is not BitVecNum && opcode.Int != GetComponent(SynthOpc.Constant).Data.Index)
                    {
                        throw new InvalidOperationException();
                        programAst.Add(mbaCtx.Symbol($"ILLEGAL{li}", w));
                        continue;
                    }

                    if (op1Value is not BitVecNum && opcode.Int != GetComponent(SynthOpc.Constant).Data.Index && opcode.Int != GetComponent(SynthOpc.Not).Data.Index)
                    {
                        throw new InvalidOperationException();
                        programAst.Add(mbaCtx.Symbol($"ILLEGAL{li}", w));
                        continue;
                    }

                    var op0 = programAst[((BitVecNum)op0Value).Int];
                    var op1 = programAst[((BitVecNum)op1Value).Int];
                    var op0Z3 = z3ProgramAst[((BitVecNum)op0Value).Int];
                    var op1Z3 = z3ProgramAst[((BitVecNum)op1Value).Int];
                    var constData = model.Eval(exprLine.ConstantData);
                    //var truthTable = (BitVecNum)model.Eval(exprLine.TruthTable);


                    //SynthOpc opc = components[opcode.Int].Opcode;
                    SynthOpc opc = opcode.Int >= components.Count ? components.Last().Opcode : components[opcode.Int].Opcode;

                    // We ban this opcode assignment
                    bannedModel[exprLine.Opcode] = opcode;

                    switch (opc)
                    {
                        case SynthOpc.Constant:
                            // For constants we don't actually care about their assignments... 
                            break;
                        case SynthOpc.Not:
                            bannedModel[exprLine.Op0] = op0Value;
                            break;
                        case SynthOpc.And:
                        case SynthOpc.Or:
                        case SynthOpc.Xor:
                        case SynthOpc.Add:
                        case SynthOpc.Sub:
                        case SynthOpc.Mul:
                            bannedModel[exprLine.Op0] = op0Value;
                            bannedModel[exprLine.Op1] = op0Value;
                            break;
                        default:
                            throw new InvalidOperationException("Fail");
                    }


                    Console.WriteLine($"v{li} = {opc}");
                    AstIdx node = opc switch
                    {
                        SynthOpc.Constant => mbaCtx.Constant((constData as BitVecNum).UInt64, w),
                        SynthOpc.Not => mbaCtx.Neg(op0), // Neg() is actually bvnot in my IR
                        SynthOpc.And => mbaCtx.And(op0, op1),
                        SynthOpc.Or => mbaCtx.Or(op0, op1),
                        SynthOpc.Xor => mbaCtx.Xor(op0, op1),
                        SynthOpc.Add => mbaCtx.Add(op0, op1),
                        // Note: My IR does not have a subtract operator. `a-b` becomes `a + -1*b`. This may cause weird printed output but is fine otherwise.
                        SynthOpc.Sub => mbaCtx.Sub(op0, op1),
                        SynthOpc.Mul => mbaCtx.Mul(op0, op1),
                        SynthOpc.Lshr => mbaCtx.Lshr(op0, mbaCtx.Constant((constData as BitVecNum).UInt64, w)),
                        SynthOpc.TruthTable => throw new NotImplementedException(),
                    };



                    BitVecExpr z3Node = opc switch
                    {
                        SynthOpc.Constant => ctx.MkBV((constData as BitVecNum).UInt64, w),
                        SynthOpc.Not => ctx.MkBVNot(op0Z3), // Neg() is actually bvnot in my IR
                        SynthOpc.And => ctx.MkBVAND(op0Z3, op1Z3),
                        SynthOpc.Or => ctx.MkBVOR(op0Z3, op1Z3),
                        SynthOpc.Xor => ctx.MkBVXOR(op0Z3, op1Z3),
                        SynthOpc.Add => ctx.MkBVAdd(op0Z3, op1Z3),
                        // Note: My IR does not have a subtract operator. `a-b` becomes `a + -1*b`. This may cause weird printed output but is fine otherwise.
                        SynthOpc.Sub => ctx.MkBVSub(op0Z3, op1Z3),
                        SynthOpc.Mul => ctx.MkBVMul(op0Z3, op1Z3),
                        //SynthOpc.Lshr => solver.MkBVLSHR(op0Z3, ctx.Constant((constData as BitVecNum).UInt64, w)),
                        SynthOpc.TruthTable => throw new NotImplementedException(),
                    };


                    programAst.Add(node);
                    z3ProgramAst.Add(z3Node);

                }

                result = z3ProgramAst.Last();

                Console.WriteLine($"MBA Expr: \n{mbaCtx.GetAstString(programAst.Last())}\n\n");

                Console.WriteLine($"MBA DAG: \n{DagFormatter.Format(mbaCtx, programAst.Last())}\n\n");

                Console.WriteLine($"With cost: {model.Eval(costSum)}\n");

                var equivSolver = ctx.MkSolver();

                ///// ??????????????????? aint no way
                //equivSolver.Add(solver.MkEq(solver.MkExtract(0, 0, symbols[0] as BitVecExpr), solver.MkBV(1, 1)));

                var equiv = ProveEquivalence(equivSolver, before, result) == Status.UNSATISFIABLE;
                Console.WriteLine($"Equivalent: {equiv}");

                foreach (var decl in model.Decls)
                {
                    if (decl.Arity == 0)
                        Console.WriteLine($"{decl.Name} = {model.ConstInterp(decl)}");
                }


                if (equiv)
                {

                    Console.WriteLine($"Done. Solved in {total.ElapsedMilliseconds}ms");
                    Console.ReadLine();
                    Debugger.Break();
                }

               

                else
                {


                    skeletons.Add(result);




                    var generalized = Generalize(symbols, before, result);
                    if (generalized == false)
                    {
                        var generalizedStructureBan = And(bannedModel.Select(x => ctx.MkEq(x.Key, x.Value)));
                        s.Add(ctx.MkNot(generalizedStructureBan));
                        //Debugger.Break();
                    }

                    // Synthesize an input combination that makes all previous skeletons not equal to `before`.
                    if (false)
                    {



                        var cands = new List<BitVecNum[]>();

                        int best = 0;
                        Model bestModel = null;
                        while (true)
                        {
                            BitVecExpr sum = ctx.MkBV(0, 16);
                            var skeletonSolver = ctx.MkSolver();
                            foreach (var skel in skeletons)
                            {
                                var notEq = ctx.MkNot(ctx.MkEq(skel, before));
                                // skeletonSolver.Add(notEq);

                                sum = ctx.MkBVAdd(sum, (BitVecExpr)ctx.MkITE(notEq, ctx.MkBV(1, 16), ctx.MkBV(0, 16)));
                            }

                            skeletonSolver.Add(ctx.MkBVUGT(sum, ctx.MkBV(best, 16)));

                            skeletonSolver.Add(ctx.MkNot(ctx.MkEq(result, before)));


                            var status = skeletonSolver.Check();
                            if (status == Status.UNSATISFIABLE)
                                break;

                            bestModel = skeletonSolver.Model;
                            best = (skeletonSolver.Model.Eval(sum) as BitVecNum).Int;
                            var bi = symbols.Select(x => bestModel.Eval(x) as BitVecNum).ToArray();
                            cands.Add(bi);
                        }

                        Console.WriteLine($"Num not equivalent: {best} with skeleton count {skeletons.Count} and cand list {cands.Count}");
                        //Console.WriteLine();

                        /*
                        var bestInputs = (iii % 3) switch
                        {
                            0 => cands.First(),
                            1 => cands[cands.Count / 2],
                            2 => cands[cands.Count],
                        };
                        */

                        if (cands.Count > 3)
                        {
                            cands = new()
                            {
                                cands.First(),
                                cands[cands.Count / 2],
                                cands[cands.Count],
                            };
                        }

                        iii++;

                        //var bestInputs = symbols.Select(x => (bestModel.Eval(x) as BitVecNum)).ToArray();
                       

                        /*
                        var optimizer = solver.MkOptimize();

                        

                        foreach (var skel in skeletons)
                        {
                            var notEq = solver.MkNot(solver.MkEq(skel, before));
                            optimizer.AssertSoft(notEq, 1, "grp");
                        }

                        if (optimizer.Check() == Status.SATISFIABLE)
                        {
                            var skelModel = optimizer.Model;
                            var skelInputs = symbols.Select(x => skelModel.Eval(x) as BitVecNum).Select(x => x.UInt64).ToArray();
                            Console.WriteLine($"Found input distinguishing loop skeletons: {string.Join(", ", skelInputs)}");

                            var bvInputs = skelInputs.Select(x => solver.MkBV(x, (before as BitVecExpr).SortSize)).ToArray();
                            var cs = getEquivOnPointsConstraint(bvInputs);
                            s.Add(cs);
                        }

                        else
                        {
                            var bvPoints = symbols.Select(x => (BitVecNum)equivSolver.Model.Eval(x)).ToArray();
                            var constraint = getEquivOnPointsConstraint(bvPoints);
                            s.Add(constraint);
                        }
                        */

                        /*
                        foreach (var bestInputs in cands)
                        {
                            var modelToUse = (best > 0 && bestModel != null) ? bestModel : equivSolver.Model;
                            var bvPoints = symbols.Select(x => (BitVecNum)modelToUse.Eval(x)).ToArray();
                            var constraint = getEquivOnPointsConstraint(bestInputs);
                            s.Add(constraint);
                        }
                        */
                    }

                    var bvPoints = symbols.Select(x => (BitVecNum)equivSolver.Model.Eval(x)).ToArray();
                    var constraint = getEquivOnPointsConstraint(bvPoints);
                    s.Add(constraint);


                    Console.WriteLine("");
                }
            }

            // TODO Idea: Sort constants by their value? Maybe
            // Ban ~(~x))
        }

        // Implements generalization of cegis(T)
        // (1). 
        private bool Generalize(Expr[] symbols, Expr before, Expr candidateExpression)
        {
            // Collect all constants in the candidate expression
            var constants = new HashSet<Expr>();
            var newConstants = new List<Expr>();

            // Recursive function to traverse the AST and find constants
            void CollectConstants(Expr e)
            {
                /*
                if (e is BitVecNum && e.Args.Length == 0 && e.Sort.SortKind == Z3_sort_kind.Z3_BV_SORT)
                {
                    // It's a bitvector constant
                    constants.Add(e);
                    newConstants.Add(solver.MkConst($"c{newConstants.Count}", e.Sort)); // Create symbolic variable
                }
                else
                {
                    foreach (var arg in e.Args)
                        CollectConstants(arg);
                }
                */

                if (e.ASTKind == Z3_ast_kind.Z3_NUMERAL_AST)
                {
                    if (constants.Add((BitVecNum)e))
                        newConstants.Add(ctx.MkBVConst($"HOLE{newConstants.Count}", (e as BitVecNum).SortSize));
                    return;
                }

                if (e.ASTKind != Z3_ast_kind.Z3_APP_AST)
                    throw new InvalidOperationException();

                foreach (var child in e.Args)
                {
                    CollectConstants(child);
                }

            }
            CollectConstants(candidateExpression);

            if (constants.Count == 0)
                return false;



            // Substitute original constants with symbolic variables
            var generalizedExpression = candidateExpression.Substitute(constants.ToArray(), newConstants.ToArray());

            // forall inputs, exists constants, generalizedExpression(inputs, constants) == before(inputs)
            // But here we want: exists constants . forall inputs . generalizedExpression == before

            // We want to find IF there exist constants such that for all inputs, they are equal.
            // If so, we found a solution!

            // However, this is expensive.
            // Generalization typically used to prune search space.
            // If NO constants exist such that they are equal, we can block this *structure*.

            // exists C . forall X . P(X, C) == S(X)
            // C = newConstants
            // X = symbols

            var equality = ctx.MkEq(generalizedExpression, before);
            var forallX = ctx.MkForall(symbols, equality);

            var genSolver = ctx.MkSolver();
            genSolver.Add(forallX);

            var res = genSolver.Check();
            //if (res == Status.SATISFIABLE)
            if (false)
            {
                Console.WriteLine("Generlization found a solution!");

                Debugger.Break();
                Console.WriteLine("IGNORING GOOD SOLUTION FORNOW");
                return true;

                //Debugger.Break();
                //return true;
            }
            else
            {
                return false;
                Debugger.Break();
            }

            //  Debugger.Break();
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

            File.WriteAllText(filePath, smtString);
            Console.WriteLine($"SMT problem exported to: {filePath}");
        }

        private BoolExpr GetEquivalenceConstraint(Expr[] symbols, Expr before, Expr after)
        {
            var forall = ctx.MkForall(symbols, ctx.MkEq(before, after));
            return forall;
        }

        private Status ProveEquivalence(Solver s, Expr a, Expr b)
        {
            s.Add(ctx.MkNot(ctx.MkEq(a, b)));
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

                    bool isSet = (i >> j & 1) == 1;
                    var sort = ((BitVecExpr)symbols[j]).SortSize;
                    values[j] = isSet ? ctx.MkBV(one, sort) : ctx.MkBV(zero, sort);
                }

                var subBefore = before.Substitute(symbols, values);
                var subAfter = after.Substitute(symbols, values);

                constraints.Add(ctx.MkEq(subBefore, subAfter));
            }

            return And(constraints.ToArray());
        }

        private BoolExpr And(params BoolExpr[] t)
            => And(t.AsEnumerable());

        // Solver wrappers
        private BoolExpr And(IEnumerable<BoolExpr> t)
        {
            if (t.Count() == 1)
                return t.Single();
            return ctx.MkAnd(t);
        }

        private BoolExpr Or(params BoolExpr[] t)
       => Or(t.AsEnumerable());

        // Solver wrappers
        private BoolExpr Or(IEnumerable<BoolExpr> t)
        {
            if (t.Count() == 1)
                return t.Single();
            return ctx.MkOr(t);
        }
    }
}
