using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Synthesis
{
    public enum NodeDecision
    {
        Undecided = 0,
        Cut = 1,
        Expand = 2,
    }

    public class NodeState
    {
        public Dictionary<AstIdx, NodeDecision> Decisions { get; set; } = new();

        public Dictionary<AstIdx, AstIdx> Holes { get; set; } = new();

        public NodeState Clone()
            => new NodeState() { Decisions = Decisions.ToDictionary(x => x.Key, x => x.Value), Holes = Holes.ToDictionary(x => x.Key, x => x.Value) };

        public NodeDecision Get(AstIdx idx)
        {
            var existing = NodeDecision.Undecided;
            Decisions.TryGetValue(idx, out existing);
            return existing;
        }

        public void Set(AstIdx idx, NodeDecision newState) 
            => Decisions[idx] = newState;
    }

    public record Pattern(AstIdx Idx, int Cost, NodeState State);

    public class DagRuleSynthesis
    {
        private readonly AstCtx ctx;

        public DagRuleSynthesis(AstCtx ctx)
        {
            this.ctx = ctx;
        }

        public void Run(AstIdx idx)
        {
            var seen = new HashSet<AstIdx>();
            Collect(idx, seen);

            HashSet<AstIdx> simplSeen = new();

            foreach (var subtree in seen)
            {
                var state = new NodeState();

                var range = Enumerable.Range(3, 10);

                //var all = EnumeratePatterns(subtree, 13, state);
                var all = range.SelectMany(x => EnumeratePatterns(subtree, x, new NodeState()));

                foreach (var p in all)
                {
                    var before = p.Idx;
                    if (simplSeen.Contains(before))
                        continue;
                    simplSeen.Add(before);

                    var after = LinearSimplifier.Run(ctx.GetWidth(before), ctx, before, false, false);
                 

                    var c0 = ctx.GetCost(after);
                    var c1 = ctx.GetCost(before);
                    if (c0 < c1)
                    {
                        Console.WriteLine($"{before}\n=>\n{after}\n{c0} => {c1}\n\n");
                    }
                }
            }
            Debugger.Break();
        }

        private void Collect(AstIdx idx, HashSet<AstIdx> seen)
        {
            if (seen.Contains(idx))
                return;

            seen.Add(idx);
            var opc = ctx.GetOpcode(idx);
            if (opc == AstOp.Constant || opc == AstOp.Symbol)
                return;

            switch(opc)
            {
                case AstOp.Neg:
                    Collect(ctx.GetOp0(idx), seen);
                    break;

                case AstOp.And:
                case AstOp.Or:
                case AstOp.Xor:
                    Collect(ctx.GetOp0(idx), seen);
                    Collect(ctx.GetOp1(idx), seen);
                    break;
                default:
                    throw new InvalidOperationException();

            }
        }

        private List<Pattern> EnumeratePatterns(AstIdx idx, int budget, NodeState state)
        {
            var results = new List<Pattern>();


            // Substitute the node with a variable if we have not committed to using it in the tree.
            bool isSymbol = ctx.IsSymbol(idx);
            var decision = state.Get(idx);


            bool COND0 = decision != NodeDecision.Expand;
            bool COND1 = decision != NodeDecision.Cut && budget > 1;
            if (decision != NodeDecision.Expand || isSymbol)
            {
       
                var newState = state.Clone();
                newState.Set(idx, NodeDecision.Cut);
                var holeSymbol = ctx.Symbol($"subst{state.Holes.Count}", ctx.GetWidth(idx));
                newState.Holes.TryAdd(idx, holeSymbol);
                results.Add(new Pattern(newState.Holes[idx], 1, newState));

                // Variables automatically become holes!
                if (isSymbol)
                    return results;
            }

            // TODO: Handle constant case
            if (decision != NodeDecision.Cut && budget > 1)
            {
                var currentState = state.Clone();
                currentState.Set(idx, NodeDecision.Expand);

                var remainingBudget = budget - 1;

                if (ctx.IsSymbol(idx))
                {
                    var sPattern = new Pattern(idx, 1, currentState);
                    results.Add(sPattern);
                    return results;
                }


                var op0 = ctx.GetOp0(idx);
                var lefts = EnumeratePatterns(op0, remainingBudget, currentState);
                var opc = ctx.GetOpcode(idx);
                if (opc == AstOp.Neg)
                {
                    // For unary operations there is no rhs.
                    foreach(var pattern in lefts)
                    {
                        var newIdx = ctx.Neg(pattern.Idx);
                        var newPattern = new Pattern(newIdx, pattern.Cost + 1, pattern.State);
                        results.Add(newPattern);
                    }

                    return results;
                }

                foreach (var leftPattern in lefts)
                {
                    var op1 = ctx.GetOp1(idx);
                    var rightBudget = remainingBudget - leftPattern.Cost;
                    var rights = EnumeratePatterns(op1, rightBudget, leftPattern.State);
                    foreach(var rightPattern in rights)
                    {
                        var totalCost = 1 + leftPattern.Cost + rightPattern.Cost;
                        var patternIdx = ctx.Binop(opc, leftPattern.Idx, rightPattern.Idx);
                        var newPattern = new Pattern(patternIdx, totalCost, rightPattern.State);
                        results.Add(newPattern);
                    }
                }

                //Debugger.Break();
            }

            // In this case we should also return a hole.
            // Or if its a constant then we can return it.
            // Also literals should always be holes
            //if (budget <= 1)
            //    Debugger.Break();


            return results;
        }
    }
}
