using Mba.Simplifier.Bindings;
using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Synthesis
{
    enum SynthOpc
    {
        // Leafs
        Constant,

        // Boolean
        Not,
        And,
        Or,
        Xor,

        // Arithmetic
        Add,
        Mul,

        // Special
        TruthTable,
    }

    public abstract record Line();
    public record VarLine(int Index, Expr Symbol) : Line();
    public record ExprLine(BitVecExpr Opcode, BitVecExpr Op0, BitVecExpr Op1, Expr TruthTable) : Line();

    public class BrahmaSynthesis
    {
        private readonly AstCtx ctx;
        private readonly AstIdx idx;
        private readonly List<AstIdx> inputs;

        private readonly Context solver;
        private readonly Z3Translator translator;

        // Config:
        private readonly int numInstructions = 14;


        private bool usesTruthOperator = false;
        private const int TRUTHVARS = 2;
        private const uint TRUTHSIZE = 1u << TRUTHVARS;

        private readonly Dictionary<SynthOpc, int> components = new()
        {
            // Constants
            // Not present on booleans
            { SynthOpc.Constant, 2},

            /*
            { SynthOpc.Not, 2},
            { SynthOpc.And, 2},
            { SynthOpc.Or, 2},
            { SynthOpc.Xor, 2},
            */

        
            
           // { SynthOpc.Add, 2},
            { SynthOpc.Not, 2},
            //{ SynthOpc.And, 2},
            { SynthOpc.Or, 2},
            //{ SynthOpc.Xor, 2},
            

            //{ SynthOpc.TruthTable, 2}

        };

        public BrahmaSynthesis(AstCtx ctx, AstIdx idx)
        {
            var config = new Dictionary<string, string>()
            {
                { "html_mode", "false"}
            };

            usesTruthOperator = components.ContainsKey(SynthOpc.TruthTable);

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

            var lines = GetLines();

            var after = GetExpression(lines);

            after = after.Simplify();

            var symbols = lines.Where(x => x is VarLine).Select(x => (x as VarLine).Symbol).ToArray();

            var s = solver.MkSolver();
            var constraints = GetProgramConstraints(lines);
            //s.Add(constraints);
     

            CEGIS(s, symbols, before, after, lines);

            Debugger.Break();
        }

        private IReadOnlyList<Line> GetLines()
        {
            // For each instruction, we need a variable representing the opcode, and a variable representing the operands.
            var opcodeCount = components.Count + 1;

            var lines = new List<Line>();

            // Each variable gets assigned its own line
            for (int i = 0; i < inputs.Count; i++)
                lines.Add(new VarLine(i, translator.cache[inputs[i]]));

            // Each instruction gets assigned its own line.
            var opcodeBitsize = BvWidth(components.Count - 1);
            //var opcodeBitsize = GetBitsNeeded(32);
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


                lines.Add(new ExprLine(opcode, op0, op1, truthTable));
            }
            return lines;
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
                foreach (var opc in components.Keys.OrderBy(x => x))
                {
                    var expr = opc switch
                    {
                        SynthOpc.Constant => solver.MkBV(0, ctx.GetWidth(idx)),
                        SynthOpc.Not => solver.MkBVNot(op0),
                        SynthOpc.And => solver.MkBVAND(op0, op1),
                        SynthOpc.Or => solver.MkBVOR(op0, op1),
                        SynthOpc.Xor => solver.MkBVXOR(op0, op1),
                        SynthOpc.Add => solver.MkBVAdd(op0, op1),
                        SynthOpc.TruthTable => TruthTableToExpr((BitVecExpr)exprLine.TruthTable, op0, op1),
                        _ => throw new InvalidOperationException()
                    };
                    candidates.Add(expr);
                }

                
                var select = ConditionalSelect((BitVecExpr)exprLine.Opcode, candidates, 0);

                var selectS = select.Simplify();

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
            return ConditionalSelect((BitVecExpr)selector, exprs, 0);
        }

        // Given a symbolic index and a list of N values, pick the ith value
        private Expr ConditionalSelect(BitVecExpr inputNode, List<Expr> phiValues, int index)
        {
            if (phiValues.Count == 0)
                return phiValues[0];

            Expr op0 = null;
            Expr op1 = null;

            var icmp = solver.MkEq(inputNode, solver.MkBV(index, inputNode.SortSize));
            if (index + 1 == phiValues.Count)
            {
                (op0, op1) = (phiValues[index], phiValues[index]);
            }

            else
            {
                var otherIte = ConditionalSelect(inputNode, phiValues, index + 1);
                (op0, op1) = (phiValues[index], otherIte);
            }

            var w0 = (op0 as BitVecExpr).SortSize;
            var w1 = (op1 as BitVecExpr).SortSize;
            if (w0 < w1)
            {
                op0 = solver.MkZeroExt(w1 - w0, (BitVecExpr)op0);
            }

            return solver.MkITE(icmp, op0, op1);
        }

        private BoolExpr GetProgramConstraints(IReadOnlyList<Line> lines)
        {
            var constraints = new List<BoolExpr>();
            for(int i = 0; i < lines.Count; i++)
            {
                if (lines[i] is VarLine)
                    continue;

                var line = (ExprLine)lines[i];

                // Enforce that a < b
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
            var sw = Stopwatch.StartNew();

            // Optionally force the last opcode to be something
            bool constrainLastOpcode = false;
            if (constrainLastOpcode)
            {
                var last = lines.Last() as ExprLine;
                var lastopc = (BitVecExpr)last.Opcode;

                var tgt = solver.MkBV(components.Keys.OrderBy(x => x).ToList().IndexOf(SynthOpc.And), lastopc.SortSize);
                s.Add(solver.MkEq(lastopc, tgt));
            }

            var rng = new SeededRandom();
            var constraints = new List<BoolExpr>();
            var points = new HashSet<ResultVectorKey>();
            while (true)
            {
                bool boolean = false;
                if (boolean)
                {
                    s.Add(GetBooleanEquivalenceConstraint(before, after, symbols));
                }

                else
                {
                    // Evaluate the expression on 8 random IO points
                    for (var _ = 0; _ < 1000; _++)
                    {
                        var keys = Enumerable.Range(0, symbols.Length)
                            .Select(x => rng.GetRandUlong())
                            .ToArray();

                        points.Add(new ResultVectorKey(keys));

                        var bvPoints = keys
                            .Select(x => solver.MkBV(rng.GetRandUlong(), (before as BitVecExpr).SortSize))
                            .ToArray();


                        var subBefore = before.Substitute(symbols, bvPoints);
                        var subAfter = after.Substitute(symbols, bvPoints);
                        constraints.Add(solver.MkEq(subBefore, subAfter));
                    }

                    var and = solver.MkAnd(constraints.ToArray());
                    s.Add(and);

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
                Console.WriteLine("\n\n" + result.Simplify());
                Console.WriteLine("");

                var equiv = ProveEquivalence(before, result) == Status.UNSATISFIABLE;
                Console.WriteLine($"Equivalent: {equiv}");

                foreach (var decl in model.Decls)
                {
                    if (decl.Arity == 0)
                        Console.WriteLine($"{decl.Name} = {model.ConstInterp(decl)}");
                }

                Debugger.Break();
            }
        }

        private BoolExpr GetEquivalenceConstraint(Expr[] symbols, Expr before, Expr after)
        {
            var forall = solver.MkForall(symbols, solver.MkEq(before, after));
            return forall;
        }

        private Status ProveEquivalence(Expr a, Expr b)
        {
            var s = solver.MkSolver();
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
