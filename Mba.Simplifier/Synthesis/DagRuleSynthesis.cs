using Mba.Simplifier.Bindings;
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
        Expand = 1,
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
            var state = new NodeState();
            EnumeratePatterns(idx, 5, state);
            Debugger.Break();
        }

        private List<Pattern> EnumeratePatterns(AstIdx idx, int budget, NodeState state)
        {
            var results = new List<Pattern>();


            // Substitute the node with a variable if we have not committed to using it in the tree.
            bool isSymbol = ctx.IsSymbol(idx);
            var decision = state.Get(idx);
            if (decision != NodeDecision.Expand || isSymbol)
            {
                var newState = state.Clone();
                newState.Set(idx, NodeDecision.Cut);
                var holeSymbol = ctx.Symbol($"subst{state.Holes.Count}", ctx.GetWidth(idx));
                newState.Holes.Add(idx, holeSymbol);
                results.Add(new Pattern(holeSymbol, 1, newState));

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
                
                var left = EnumeratePatterns(ctx.GetOp0(idx), remainingBudget, currentState);
                var opc = ctx.GetOpcode(idx);
                if (opc == AstOp.Neg)
                {

                }

                Debugger.Break();
            }

            // In this case we should also return a hole.
            // Or if its a constant then we can return it.
            // Also literals should always be holes
            if (budget <= 1)
                Debugger.Break();


            return results;
        }
    }
}
