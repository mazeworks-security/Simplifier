using Mba.Ast;
using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using Mba.Testing;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    public static class BooleanMinimizer
    {
        private const bool useLegacyMinimizer = false;

        private static int substCount = 0;

        public static AstIdx GetBitwise(AstCtx ctx, IReadOnlyList<AstIdx> variables, TruthTable truthTable, bool negate = false)
        {
            // If requested, negate the result vector to find a negated expression.
            if (negate)
            {
                truthTable.Negate();
            }

            // Exit early if the boolean function is a constant.
            var asConstant = AsConstant(ctx, truthTable, ctx.GetWidth(variables[0]));
            if (asConstant != null)
                return asConstant.Value;

            if (variables.Count == 1)
            {
                return truthTable.GetBit(0) == false ? variables[0] : ctx.Neg(variables[0]);
            }

            if (variables.Count <= 5)
            {
                var bar = MinimizeAnf(ctx, variables, truthTable.Clone()); 
                //var bar = FromTruthTable(ctx, variables, truthTable);
                var tableUint = (uint)truthTable.arr[0];
                var result = GetOptimalNpnCircuit(ctx, variables, AppendVariables(tableUint, (uint)variables.Count, 5 - (uint)variables.Count));
                return result;
            }

            // If there are four or less variables, we can pull the optimal representation from the truth table.
            // TODO: One could possibly construct a 5 variable truth table for all 5 variable NPN classes.
            if (variables.Count <= 4)
            {
                return FromTruthTable(ctx, variables, truthTable);
            }

            // For debugging purposes we still want to keep the legacy boolean minimization logic around.
            if (useLegacyMinimizer)
            {
                // Otherwise use Espresso to compute a semi optimal version of the boolean function.
                var xnf = AnfMinimizer.SimplifyBoolean(ctx, variables, truthTable);
                var dnf = EspressoMinimizer.SimplifyBoolean(ctx, truthTable.AsList(), variables).ast;

                var c1 = LinearSimplifier.GetCost(ctx, xnf, false, 1);
                var c2 = LinearSimplifier.GetCost(ctx, dnf, false, 1);
                if (c1 < c2)
                    return xnf;
                return dnf;
            }

            return MinimizeAnf(ctx, variables, truthTable);
        }

        private static AstIdx? AsConstant(AstCtx ctx, TruthTable table, uint width)
        {
            var first = table.GetBit(0);
            for (int i = 1; i < table.NumBits; i++)
            {
                if (table.GetBit(i) != first)
                    return null;
            }

            ulong constant = first ? (ulong)ModuloReducer.GetMask(width) : 0;
            return ctx.Constant(constant, width);
        }

        public static uint AppendVariables(uint truthTable, uint numExistingVars, uint numVarsToAdd)
        {
            uint currentRows = 1u << (int)numExistingVars; 
            uint duplicationFactor = 1u << (int)numVarsToAdd;
            uint expandedTruthTable = 0;
            for (uint i = 0; i < duplicationFactor; i++)
                expandedTruthTable |= truthTable << (int)(i * (1u << (int)numExistingVars));
            return expandedTruthTable;
        }

        // Extend the truth table to include new variables
        public static uint AddTruthTableVariables(uint truthTable, uint numVarsToAdd)
        {
            uint currentRows = 1u << BitOperations.PopCount(truthTable); 
            uint newRows = currentRows << (int)numVarsToAdd; 
            uint expandedTruthTable = 0;
            for (uint i = 0; i < currentRows; i++)
            {
                for (uint j = 0; j < (1u << (int)numVarsToAdd); j++)
                    expandedTruthTable |= (truthTable & (1u << (int)i)) << (int)(i + j);
            }

            return expandedTruthTable;
        }

        public static UInt32 ReverseBytes(UInt32 value)
        {
            return (value & 0x000000FFU) << 24 | (value & 0x0000FF00U) << 8 |
                (value & 0x00FF0000U) >> 8 | (value & 0xFF000000U) >> 24;
        }

        public static unsafe AstIdx GetOptimalNpnCircuit(AstCtx ctx, IReadOnlyList<AstIdx> variables, uint truthTable)
        {
            // Lookup the optimal circuit representation
            var neg = ReverseBits(truthTable);
            //var neg = ReverseBytes(truthTable);
            var gv = Optimal5.Instance.Lookup(neg);

            Optimal5.Instance.PrintGatevec(gv);

            // Emplace variables onto node vector

            var reversed = variables.Reverse().ToArray();
            var nodeVec = new AstIdx[5 + gv.NumGates];
            for (int i = 0; i < 5; i++)
                nodeVec[i] = reversed[Math.Min(i, variables.Count - 1)];

            // Compute the circuit
            for (int idx = 0; idx < gv.NumGates; idx++)
            {
                // Fetch operands
                uint a = gv.Gates[idx];
                var i1 = ((a >> 4) & 31);
                var idx1 = nodeVec[i1 - 1];
                var i2 = ((a >> 10) & 31);
                var idx2 = nodeVec[i2 - 1];

                // Build the expression
                var expr = (a & 7) switch
                {
                    3 => ctx.Xor(idx1, idx2),
                    4 => ctx.And(idx1, idx2),
                    5 => ctx.And(idx1, ctx.Neg(idx2)),
                    6 => ctx.And(idx2, ctx.Neg(idx1)),
                    7 => ctx.Or(idx1, idx2),
                    _ => throw new InvalidOperationException()
                };

                nodeVec[idx + 5] = expr;
            }

            // Negate the circuit if necessary
            var resultIdx = (gv.Output >> 1) - 1;
            var result = nodeVec[resultIdx];
            if ((gv.Output & 1) != 0)
                result = ctx.Neg(result);

            return result;
        }

        public static uint ReverseBits(uint n)
        {
            n = (n >> 1) & 0x55555555 | (n << 1) & 0xaaaaaaaa;
            n = (n >> 2) & 0x33333333 | (n << 2) & 0xcccccccc;
            n = (n >> 4) & 0x0f0f0f0f | (n << 4) & 0xf0f0f0f0;
            n = (n >> 8) & 0x00ff00ff | (n << 8) & 0xff00ff00;
            n = (n >> 16) & 0x0000ffff | (n << 16) & 0xffff0000;
            return n;
        }


        public static AstIdx FromTruthTable(AstCtx ctx, IReadOnlyList<AstIdx> variables, TruthTable truthTable)
        {
            // Fetch the truth table entry corresponding to this node.
            var ast = TableDatabase.Instance.GetTableEntry(ctx, (List<AstIdx>)variables, (int)(uint)truthTable.arr[0]);
            return ast;
        }


        private static AstIdx MinimizeAnf(AstCtx ctx, IReadOnlyList<AstIdx> variables, TruthTable truthTable)
        {
            // Minimize normally if zext/trunc nodes aren't present
            bool containsExt = variables.Any(x => ctx.GetOpcode(x) == AstOp.Zext || ctx.GetOpcode(x) == AstOp.Trunc);
            if (!containsExt)
                return ctx.MinimizeAnf(TableDatabase.Instance.db, truthTable, (List<AstIdx>)variables, MultibitSiMBA.JitPage.Value);

            // Otherwise we need to apply substitution.
            var invSubstMapping = new Dictionary<AstIdx, AstIdx>();
            var tempVars = new List<AstIdx>();
            foreach (var v in variables)
            {
                bool isExt = ctx.GetOpcode(v) == AstOp.Zext || ctx.GetOpcode(v) == AstOp.Trunc;
                if (!isExt)
                {
                    tempVars.Add(v);
                    continue;
                }

                var toSubst = v;
                var subst = ctx.Symbol($"extSubstVar{substCount}", ctx.GetWidth(toSubst));
                substCount++;
                invSubstMapping.Add(subst, toSubst);
                tempVars.Add(subst);
            }

            var r = ctx.MinimizeAnf(TableDatabase.Instance.db, truthTable, tempVars, MultibitSiMBA.JitPage.Value);
            var backSubst = GeneralSimplifier.ApplyBackSubstitution(ctx, r, invSubstMapping);
            return backSubst;
        }
    }
}
