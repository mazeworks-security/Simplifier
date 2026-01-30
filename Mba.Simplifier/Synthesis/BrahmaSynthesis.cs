using Mba.Simplifier.Bindings;
using Mba.Simplifier.Utility;
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
    public abstract record Line();
    public record VarLine(int Index, Expr Symbol) : Line();
    public record ExprLine(Expr Opcode, Expr Op0, Expr Op1) : Line();

    public class BrahmaSynthesis
    {
        private readonly AstCtx ctx;
        private readonly AstIdx idx;
        private readonly List<AstIdx> inputs;

        private readonly Context solver = new();
        private readonly Z3Translator translator;

        // Config:
        private readonly int numInstructions = 3;

        private readonly Dictionary<Z3_decl_kind, int> components = new()
        {
            // Constants
            // Not present on booleans
            //{ Z3_decl_kind.Z3_OP_UNINTERPRETED, 2},

            { Z3_decl_kind.Z3_OP_BNOT, 2},
            { Z3_decl_kind.Z3_OP_BAND, 2},
            { Z3_decl_kind.Z3_OP_BOR, 2},
            { Z3_decl_kind.Z3_OP_BXOR, 2},
        };

        public BrahmaSynthesis(AstCtx ctx, AstIdx idx)
        {
            this.ctx = ctx;
            this.idx = idx;
            inputs = ctx.CollectVariables(idx);
            translator = new Z3Translator(ctx, solver);
        }

        public void Run()
        {
            var before = translator.Translate(idx);

            var lines = GetLines();

            var after = GetExpression(lines);

            after = after.Simplify();

            var symbols = lines.Where(x => x is VarLine).Select(x => (x as VarLine).Symbol).ToArray();
            var forall = solver.MkForall(symbols, solver.MkEq(before, after));

            var s = solver.MkSolver();
            s.Add(forall);
            var check = s.Check();
            Console.WriteLine(check);
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
            var opcodeBitsize = GetBitsNeeded(components.Count);
            for (int i = lines.Count; i < numInstructions; i++)
            {
                // Choose the opcode
                var opcode = solver.MkBVConst($"code{i}", (uint)opcodeBitsize);

                // Choose the operands
                var operandBitsize = GetBitsNeeded(components.Count);
                var op0 = solver.MkBVConst($"{i}_op0", (uint)operandBitsize);
                var op1 = solver.MkBVConst($"{i}_op1", (uint)operandBitsize);

                lines.Add(new ExprLine(opcode, op0, op1));
            }
            return lines;
        }

        private int GetBitsNeeded(int maxValue)
        {
            return 63 - BitOperations.LeadingZeroCount((ulong)maxValue);
        }

        private Expr GetExpression(IReadOnlyList<Line> lines)
        {
            var exprs = new List<Expr>();
            for(int lineIndex = 0; lineIndex < lines.Count; lineIndex++)
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
                foreach(var opc in components.Keys.OrderBy(x => x))
                {
                    var expr = opc switch
                    {
                        Z3_decl_kind.Z3_OP_BNOT => solver.MkBVNot(op0),
                        Z3_decl_kind.Z3_OP_BAND => solver.MkBVAND(op0, op1),
                        Z3_decl_kind.Z3_OP_BOR => solver.MkBVOR(op0, op1),
                        Z3_decl_kind.Z3_OP_BXOR => solver.MkBVXOR(op0, op1),
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
    }
}
