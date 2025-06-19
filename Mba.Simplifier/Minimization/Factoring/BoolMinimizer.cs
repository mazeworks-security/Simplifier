using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization.Factoring
{
    public class BoolMinimizer
    {
        private readonly BoolCtx ctx;

        public BoolMinimizer(BoolCtx ctx)
        {
            this.ctx = ctx;
        }

        public void Minimize(ExprId id)
        {
            var bar = TryFactorByLiteral(id);
            Debugger.Break();
        }

        private ExprId TryFactorByLiteral(ExprId id)
        {
            var node = ctx.Get(id);
            if (node.Kind != ExprKind.Add)
                return id;

            // Calculate the frequency of each literal
            var literalCounts = new int[(int)ctx.VarCount];
            GetLiteralCounts(node.Children, literalCounts);

            // If there is no literal that occurs more than once, there is no factoring to be done.
            var bestIdx = GetMostCommonIdx(literalCounts);
            if (bestIdx == -1 || literalCounts[bestIdx] <= 1)
                return id;

            // Otherwise we have a common literal.
            // E.g. if we have ab + ac + c, we want to factor it into a(b+c) + c
            var literal = ctx.Var((uint)bestIdx);
            var factors = new List<ExprId>();
            var others = new List<ExprId>();
            foreach(var childId in node.Children)
            {
                var child = ctx.Get(childId);
                // If we have a literal, factor it out.
                if (child.Kind == ExprKind.Var)
                {
                    if (childId == literal)
                        factors.Add(ctx.Constant1Id);
                    else
                        others.Add(childId);

                    continue;
                }

                if (child.Kind == ExprKind.Const)
                {
                    others.Add(childId);
                    continue;
                }

                if (child.Kind != ExprKind.Mul)
                    throw new InvalidOperationException($"Failed to hoist terms!");
                var products = child.Children;
                // If we have a multiplication, and the literal is not one of the factors, skip it.
                bool containsLiteral = products.Contains(literal);
                if (!containsLiteral)
                {
                    others.Add(childId);
                    continue;
                }

                Debug.Assert(products.Count(x => x == literal) == 1);
                var withoutLiteral = products.Where(x => x != literal).ToList();
                var mul = ctx.Mul(withoutLiteral);
                factors.Add(mul);
            }


            var lhs = ctx.Add(factors);
            var part1 = ctx.Mul(literal, TryFactorByLiteral(lhs));

            var part2 = ctx.Add(others);
            part2 = TryFactorByLiteral(part2);

            var result = ctx.Add(part1, part2);
            return result;
        }

        private void GetLiteralCounts(IReadOnlyList<ExprId> ids, int[] literalCounts)
        {
            foreach(var id in ids)
            {
                var node = ctx.Get(id);
                if (node.Kind == ExprKind.Var)
                {
                    var varIdx = ctx.GetVarIndex(node);
                    literalCounts[varIdx] += 1;
                }
                if (node.Kind == ExprKind.Mul)
                    GetLiteralCounts(node.Children, literalCounts);
            }
        }

        private int GetMostCommonIdx(int[] literalCounts)
        {
            int bestIdx = -1;
            for(int i = 0; i < literalCounts.Length; i++)
            {
                if (bestIdx == -1)
                {
                    bestIdx = i;
                    continue;
                }

                bestIdx = literalCounts[i] > literalCounts[bestIdx] ? i : bestIdx;
            }
            return bestIdx;
        }

    }
}
