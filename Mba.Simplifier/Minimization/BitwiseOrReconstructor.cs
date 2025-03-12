using Mba.Simplifier.Bindings;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    /// <summary>
    /// Given a truth table for `a` and a truth table for `a|b`, this class recovers a truth table for `b`.
    /// Note that `a` and `b` are both arbitrary boolean truth tables, making this nontrivial.
    /// We implemented an algorithm to compare the truth tables, eliminating undemanded variables from all positive DNF terms in `a|b` 
    /// until we find a minimal result.
    /// </summary>
    public class BitwiseOrReconstructor
    {
        private readonly AstCtx ctx;

        private readonly IReadOnlyList<AstIdx> variables;

        private readonly TruthTable aTable;

        private readonly ushort[] aDemandedVars;
        
        private readonly TruthTable oredTable;

        private readonly ushort[] oredDemandedVars;

        public BitwiseOrReconstructor(AstCtx ctx, IReadOnlyList<AstIdx> variables, TruthTable aTable, TruthTable oredTable)
        {
            this.ctx = ctx;
            this.variables = variables;
            this.aTable = aTable.Clone();
            this.aDemandedVars = new ushort[this.aTable.NumBits];
            this.oredTable = oredTable.Clone();
            this.oredDemandedVars = new ushort[this.oredTable.NumBits];
        }

        public AstIdx Match()
        {
            // Take the combined tables and eliminate all positive rows that overlap with `a`
            oredTable.Xor(aTable);

            // Enumerate through all truth table rows and make all variables demanded 
            SetDemandedVars(aTable, aDemandedVars);
            SetDemandedVars(oredTable, oredDemandedVars);

            for (int i = 0; i < oredTable.NumBits; i++)
            {
                // Skip zeroed out rows
                if (!oredTable.GetBit(i))
                    continue;

                for(ushort varIdx = 0; varIdx < oredTable.NumVars; varIdx++)
                {
                    var vMask = 1 << varIdx;
                    bool set = (i & vMask) != 0;
                    var otherIdx = set ? i & ~vMask : i | vMask;
                    // If changing the value of this variable would result in a different outcome, we cannot eliminate it.
                    if (!aTable.GetBit(otherIdx))
                        continue;

                    // Otherwise we can eliminate this variable.
                    oredDemandedVars[i] &= (ushort)~vMask;
                }
            }

            // Then finally convert the truth table to DNF.
            var terms = new List<AstIdx>();
            for (int i = 0; i < oredTable.NumBits; i++)
            {
                var bitwise = new List<AstIdx>();
                if (!oredTable.GetBit(i))
                    continue;
                if (oredDemandedVars[i] == 0)
                    continue;

                for (ushort varIdx = 0; varIdx < oredTable.NumVars; varIdx++)
                {
                    var vMask = 1 << varIdx;
                    // Skip undemanded variables.
                    if ((oredDemandedVars[i] & vMask) == 0)
                        continue;

                    var negated = (i & vMask) == 0;
                    bitwise.Add(negated ? ctx.Neg(variables[varIdx]) : variables[varIdx]);
                }

                terms.Add(ctx.And(bitwise));
                
            }

            var expr = ctx.Or(terms);
            return expr;
        }

        private static void SetDemandedVars(TruthTable table, ushort[] demandedVars)
        {
            var mask = (ushort)ModuloReducer.GetMask((uint)table.NumVars);
            for(int i = 0; i < table.NumBits; i++)
            {
                if (table.GetBit(i))
                    demandedVars[i] = mask;
            }
        }
    }
}
