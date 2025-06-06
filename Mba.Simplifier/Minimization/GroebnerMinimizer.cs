using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using System;
using System.Collections.Generic;
using System.Diagnostics;
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

        public static AstIdx RunWithPermutation(AstCtx ctx, IReadOnlyList<AstIdx> variables, TruthTable truthTable)
        {
            var perms = Permute(variables.ToArray());
            var src = AnfMinimizer.SimplifyBoolean(ctx, variables, truthTable);

            var seen = new HashSet<TruthTable>();


            AstIdx? best = null;
            foreach (var perm in perms)
            {
                var map = new Dictionary<AstIdx, AstIdx>();
                for(int i = 0; i < variables.Count; i++)
                {
                    map[variables[i]] = perm[i];
                }



                var withOrder = MapVars(ctx, src, map);


                // Build a result vector for the millionth time..
                var w = ctx.GetWidth(withOrder);
                var rv = LinearSimplifier.JitResultVector(ctx, 1, 1, variables, withOrder, false, (ulong)Math.Pow(2, variables.Count));

                var table = new TruthTable(variables.Count);
                for (int i = 0; i < rv.Length; i++)
                    table.SetBit(i, rv[i] != 0);

                if(seen.Contains(table))
                    Console.WriteLine("Seen!");
                seen.Add(table);

                var minimized = GroebnerMinimizer.Run(ctx, variables, table.Clone());
                if(best == null || ctx.GetCost(minimized) < ctx.GetCost(best.Value))
                {
                    Console.WriteLine($"Found best: {minimized}\n\n");
                    best = minimized;
                }
            }

            Debugger.Break();
            return 0;
        }

        private static AstIdx MapVars(AstCtx ctx, AstIdx idx, Dictionary<AstIdx, AstIdx> replacementMap)
        {
            var opc = ctx.GetOpcode(idx);
            return opc switch
            {
                AstOp.Constant => idx,
                AstOp.And or AstOp.Or or AstOp.Xor => ctx.Binop(opc, MapVars(ctx, ctx.GetOp0(idx), replacementMap), MapVars(ctx, ctx.GetOp1(idx), replacementMap)),
                AstOp.Neg => ctx.Neg(MapVars(ctx, ctx.GetOp0(idx), replacementMap)),
                AstOp.Symbol => replacementMap[idx],
                _ => throw new InvalidOperationException("Unsupported opcodes")
            };
        }

        private AstIdx Run()
        {
            // Compute a groebner basis for this truth table
            var (gb, negated) = GroebnerBasis.Compute(truthTable);


            var sorted = gb.OrderBy(x => x.Count).ToList();

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

            //var minimized = 

            return negated ? ctx.Neg(result) : result;
        }

        static IList<IList<AstIdx>> Permute(AstIdx[] nums)
        {
            var list = new List<IList<AstIdx>>();
            return DoPermute(nums, 0, nums.Length - 1, list);
        }

        static IList<IList<AstIdx>> DoPermute(AstIdx[] nums, int start, int end, IList<IList<AstIdx>> list)
        {
            if (start == end)
            {
                // We have one of our possible n! solutions,
                // add it to the list.
                list.Add(new List<AstIdx>(nums));
            }
            else
            {
                for (var i = start; i <= end; i++)
                {
                    Swap(ref nums[start], ref nums[i]);
                    DoPermute(nums, start + 1, end, list);
                    Swap(ref nums[start], ref nums[i]);
                }
            }

            return list;
        }

        static void Swap(ref AstIdx a, ref AstIdx b)
        {
            var temp = a;
            a = b;
            b = temp;
        }

        static void PrintResult(IList<IList<AstIdx>> lists)
        {
            Console.WriteLine("[");
            foreach (var list in lists)
            {
                Console.WriteLine($"    [{string.Join(',', list)}]");
            }
            Console.WriteLine("]");
        }

    }
}
