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
    public class DnfMinimizer
    {
        private readonly AstCtx ctx;

        private readonly int numVars;

        private readonly TruthTable table;

        public static void Minimize(AstCtx ctx, TruthTable table) => new DnfMinimizer(ctx, table).Minimize();

        private DnfMinimizer(AstCtx ctx, TruthTable table)
        {
            this.ctx = ctx;
            this.numVars = table.NumVars;
            this.table = table;
        }

        private void Minimize()
        {
            // If the 0th bit is set, we have a negated boolean function.
            bool negated = false;
            if (table.GetBit(0))
            {
                table.Negate();
                negated = true;
            }

            var demandedMask = GetDemandedVars();
            Debugger.Break();
        }

        private ushort[] GetDemandedVars()
        {
            // For each positive truth table entry, assume all variables are demanded.
            var demandedVars = new ushort[table.NumBits];
            var mask = (ushort)ModuloReducer.GetMask((uint)numVars);
            for(int i = 0; i < table.NumBits; i++)
            {
                // Skip zero entries.
                if (table.GetBit(i))
                    demandedVars[i] = mask;
            }

            // Walk the truth table, eliminating undemanded variables.
            for (int i = 0; i < table.NumBits; i++)
            {
                if (!table.GetBit(i))
                    continue;

                for (ushort varIdx = 0; varIdx < numVars; varIdx++)
                {
                    var vMask = (1 << varIdx);
                    bool set = (i & vMask) != 0;
                    var otherIdx = set ? i & ~vMask : i | vMask;
                    // Skip if this entry is already dead.
                    if (!table.GetBit(otherIdx))
                        continue;

                    // Delete the other entry if it is covered by the current entry.
                    demandedVars[i] &= (ushort)~vMask;
                    if (demandedVars[i] == demandedVars[otherIdx])
                    {
                        demandedVars[otherIdx] = 0;
                        table.SetBit(otherIdx, false);
                    }
                }
            }

            return demandedVars;
        }
    }
}
