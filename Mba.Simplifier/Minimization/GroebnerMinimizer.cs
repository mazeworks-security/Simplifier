using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    // Boolean minimization algorithm heavily based on "Gröbner Bases for Boolean Function Minimization" (https://ceur-ws.org/Vol-3455/short4.pdf)
    public class GroebnerMinimizer
    {
        private readonly AstCtx ctx;

        private readonly IReadOnlyList<AstIdx> variables;

        private readonly TruthTable truthTable;

        private readonly Dictionary<AstIdx, uint> demandedVarsMap = new();

        public static AstIdx Run(AstCtx ctx, IReadOnlyList<AstIdx> variables, TruthTable truthTable)
            => new GroebnerMinimizer(ctx, variables, truthTable).Run();

        private GroebnerMinimizer(AstCtx ctx, IReadOnlyList<AstIdx> variables, TruthTable truthTable)
        {
            this.ctx = ctx;
            this.variables = variables;
            this.truthTable = truthTable;
        }

        private AstIdx Run()
        {
            // Compute a groebner basis for this truth table
            var (gb, negated) = GroebnerBasis.Compute(truthTable);

            // Set the initial demanded variable masks.
            for (int i = 0; i < variables.Count; i++)
            {
                var mask = 1u << i;
                var var = variables[i];
                demandedVarsMap.Add(var, mask);
            }

            // Factor each member of the groebner basis
            var terms = new List<AstIdx>();
            foreach(var conjs in gb)
            {
                terms.Add(AnfMinimizer.Factor(ctx, variables, conjs, demandedVarsMap).Value);
            }

            // Combine them into a single boolean
            var result = ctx.Or(terms);

            return negated ? ctx.Neg(result) : result;
        }
        
    }
}
