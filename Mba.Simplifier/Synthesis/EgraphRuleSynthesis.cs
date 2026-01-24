using Mba.Simplifier.Bindings;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Synthesis
{
    public class EClass
    {
        private readonly AstCtx parent;

        public AstIdx Id;

        public IReadOnlyList<AstIdx> Enodes;

        public EClass(AstCtx parent, AstIdx id, IReadOnlyList<AstIdx> enodes)
        {
            this.parent = parent;
            Id = id;
            Enodes = enodes;
        }
    }

    public class SharpGraph
    {
        // This is used exclusively to hold enodes from the egraph.
        public readonly AstCtx ctx;
        // Egraph
        private readonly EGraph egraph;

        //public List<EClass> eclasses = new();

        public Dictionary<AstIdx, EClass> eclasses = new();

        public static SharpGraph Create(EGraph egraph)
        {
            var graph = new SharpGraph(new AstCtx(), egraph);
            graph.eclasses = graph.GetEclasses().ToDictionary(x => x.Id, x => x);
            return graph;
        }

        public SharpGraph(AstCtx ctx, EGraph graph)
        {
            this.ctx = ctx;
            this.egraph = graph;
        }

        private List<EClass> GetEclasses()
        {
            var classIds = egraph.GetClasses();

            var output = new List<EClass>();
            foreach(var eclassId in classIds)
            {
                var enodeIds = egraph.GetClassNodes(ctx, eclassId);
                output.Add(new(ctx, eclassId, enodeIds));
            }

            return output;
        }
    }

    public class EgraphRuleSynthesis
    {
        private const byte width = 1;
        private const int maxDepth = 5;

        // ctx for constructing temporary nodes
        private readonly AstCtx constructionCtx;
        private readonly SharpGraph egraph;

        public EgraphRuleSynthesis(AstCtx ctx, EGraph egraph)
        {
            this.constructionCtx = ctx;
            this.egraph = SharpGraph.Create(egraph);
        }

        public void Run()
        {
            Debugger.Break();
            HashSet<AstIdx> uniqueOutputs = new();
            List<AstIdx> outputs = new();
            foreach(var eclass in egraph.eclasses.Values)
            {
                var o = VisitEclass(eclass, new(), new(), 0);
                outputs.AddRange(o);
                uniqueOutputs.AddRange(o);
            }

            Debugger.Break();
        }

        // Use destructive rewriting to prune the search space
        // You are starting at the top and have three choices
        private List<AstIdx> VisitEclass(EClass eclass, Dictionary<AstIdx, AstIdx> eclassToSubst, Stack<AstIdx> substStack, int depth)
        {
            // Skip if we've already substituted away this variable.
            if (eclassToSubst.TryGetValue(eclass.Id, out var existing))
                return new List<AstIdx>() { existing };

            // Substitute away if we are at the max depth
            if (depth >= maxDepth)
            {
                return new List<AstIdx>() { GetSubstitution(eclass.Id, eclassToSubst, substStack) };    
            }

            var output = new List<AstIdx>();
            for (int i = 0; i < eclass.Enodes.Count; i++)
            {
                // If it's a constant, jut emit it
                var enode = eclass.Enodes[i];
                var opc = egraph.ctx.GetOpcode(enode);

                if (opc == AstOp.Constant)
                {
                    output.Add(constructionCtx.Constant(egraph.ctx.GetConstantValue(enode), width));
                    continue;
                }


                // If it's a symbol, just emit it. TODO: We need to make name fetching actually work
                if (opc == AstOp.Symbol)
                {
                    output.Add(constructionCtx.Symbol($"v{enode.Idx}", width));
                    continue;
                }

                var prevCount = substStack.Count;

                // We can substitute the right, left, or both nodes.
                // Though if we are interested in seeing all depths.. we also need to explore the case where the full node is substituted.
                // Deal with it later..
                var opcount = AstCtx.GetOpcount(opc);

                // Process negation substitutions
                if (opcount == 1)
                {
                    // Base case: We don't substitute this node.
                    Debug.Assert(opc == AstOp.Neg);
                    var negClass0 = egraph.eclasses[egraph.ctx.GetOp0(enode)];
                    var op0Neg = VisitEclass(negClass0, eclassToSubst, substStack, depth + 1);
                    var negations = op0Neg.Select(x => constructionCtx.Neg(x));
                    output.AddRange(negations);
                    UndoSubstitutions(eclassToSubst, substStack, prevCount);

                    // Other case: We substitute it.
                    var subst = GetSubstitution(negClass0.Id, eclassToSubst, substStack);
                    output.Add(subst);
                    UndoSubstitutions(eclassToSubst, substStack, prevCount);
                    continue;
                }

                // We have three choices: Substitute zero inputs, substitute one input, substitute two inputs.
                var class0 = egraph.eclasses[egraph.ctx.GetOp0(enode)];
                var class1 = egraph.eclasses[egraph.ctx.GetOp1(enode)];

                // Base case: Substitute all
                var subst0 = GetSubstitution(class0.Id, eclassToSubst, substStack);
                var subst1 = GetSubstitution(class1.Id, eclassToSubst, substStack);
                output.Add(constructionCtx.Binop(opc, subst0, subst1));
                UndoSubstitutions(eclassToSubst, substStack, prevCount);

                // Other case: Substitute the first operand
                subst0 = GetSubstitution(class0.Id, eclassToSubst, substStack);
                var op1 = VisitEclass(class1, eclassToSubst, substStack, depth + 1);
                output.AddRange(op1.Select(x => constructionCtx.Binop(opc, subst0, x)));
                UndoSubstitutions(eclassToSubst, substStack, prevCount);

                var op0 = VisitEclass(class0, eclassToSubst, substStack, depth + 1);
                subst1 = GetSubstitution(class1.Id, eclassToSubst, substStack);
                output.AddRange(op0.Select(x => constructionCtx.Binop(opc, x, subst1)));
                UndoSubstitutions(eclassToSubst, substStack, prevCount);
            }

            return output;
        }

        private AstIdx GetSubstitution(AstIdx eclassId, Dictionary<AstIdx, AstIdx> eclassToSubst, Stack<AstIdx> substStack)
        {
            bool isConstant = egraph.eclasses[eclassId].Enodes.Any(x => egraph.ctx.IsConstant(x));
            if(isConstant)
            {
                var constId = egraph.eclasses[eclassId].Enodes.First(x => egraph.ctx.IsConstant(x));
                return constructionCtx.Constant(egraph.ctx.GetConstantValue(constId), width);
            }

            // Skip if we've already substituted away this variable.
            if (eclassToSubst.TryGetValue(eclassId, out var existing))
                return existing;

            var subst = constructionCtx.Symbol($"subst{eclassToSubst.Count}", 1);
            substStack.Push(eclassId);
            eclassToSubst[eclassId] = subst;
            return subst;
        }

        private void UndoSubstitutions(Dictionary<AstIdx, AstIdx> eclassToSubst, Stack<AstIdx> substStack, int prevCount)
        {
            while (substStack.Count != prevCount)
            {
                var key = substStack.Pop();
                eclassToSubst.Remove(key);
            }
        }
    }
}
