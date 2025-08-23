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
