using Mba.Ast;
using Mba.Common.Ast;
using Mba.Common.MSiMBA;
using Mba.Common.Parsing;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.DSL
{
    public class DslPreprocessor
    {
        IReadOnlyList<DslFunction> dslFunctions;

        IReadOnlyList<DslRule> dslRules;

        private IReadOnlyDictionary<string, DslFunction> nameToFunc;

        public static void Run(IReadOnlyList<DslFunction> dslFunctions, IReadOnlyList<DslRule> dslRules)
            => new DslPreprocessor(dslFunctions, dslRules).Run();

        private DslPreprocessor(IReadOnlyList<DslFunction> dslFunctions, IReadOnlyList<DslRule> dslRules)
        {
            this.dslFunctions = dslFunctions;
            this.dslRules = dslRules;
            nameToFunc = dslFunctions.ToDictionary(x => x.Name, x => x);
        }

        public void Run()
        {
            // Inline all function calls.
            InlineDslFunctionCalls();

            // Make the rhs, lhs, and precondition of a rule use the same leaf nodes 
            // This is required so that we can do hashmap lookups on the variable and constant nodes.
            HashConseRuleLeafs();

            // Replace all constants in the lhs with temporary variables (mconst0, mconst1, mconst..),
            // and update the precondition to assert that the constant value matches modulo 2**w.
            AddConstantModularMatchingPreconditions(DslRuntime.GetIsConstantFunction(dslFunctions), DslRuntime.GetConstantEqFunction(dslFunctions), dslRules);
        }

        private void InlineDslFunctionCalls()
        {
            // Recursively inline all functions called by other DSL functions
            foreach (var dslFunction in dslFunctions)
            {
                // Skip bodyless functions.
                if (dslFunction.IsBuiltin)
                    continue;

                // Recursively inline until a fixed point is reached.
                var inlined = InlineCalls(dslFunction.Body, nameToFunc);
                bool changed = inlined.ToString() != dslFunction.Body.ToString();
                while(changed)
                {
                    dslFunction.Body = inlined;
                    inlined = InlineCalls(dslFunction.Body, nameToFunc);
                    changed = dslFunction.Body.ToString() != inlined.ToString();
                }

                dslFunction.Body = inlined;
            }

            // Recursively inline all function calls in the rule preconditions.
            // Calls should not appear in the lhs or rhs of a rule.
            foreach (var rule in dslRules)
            {
                if (rule.Precondition == null)
                    continue;

                rule.Precondition = InlineCalls(rule.Precondition, nameToFunc);
            }
        }

        private static AstNode InlineCalls(AstNode body, IReadOnlyDictionary<string, DslFunction> nameToFunc)
        {
            return AstCloner.Clone(body, (AstNode src) => { return CloneIntrinsic(src, nameToFunc); });
        }

        private static AstNode CloneIntrinsic(AstNode node, IReadOnlyDictionary<string, DslFunction> nameToFunc)
        {
            // Skip if this is not an intrinsic call.
            if (node is not IntrinsicCallNode intrinsicCall)
                return null;

            // Skip if the call cannot be inlined
            var clonedChildren = intrinsicCall.Children.Select(x => AstCloner.Clone(x, (AstNode src) => { return CloneIntrinsic(src, nameToFunc); })).ToList();
            var callTarget = nameToFunc[intrinsicCall.Name];
            if (callTarget.IsBuiltin)
            {
                return new IntrinsicCallNode(intrinsicCall.Name, callTarget.ReturnType.Width, clonedChildren.ToList());
            }

            // Otherwise the call can be inlined.
            Dictionary<string, AstNode> varToReplacement = new();
            for (int i = 0; i < callTarget.Arguments.Count; i++)
            {
                var arg = callTarget.Arguments[i];
                varToReplacement[arg.Name] = clonedChildren[i];
            }

            var inlined = AstCloner.ReplaceVars(callTarget.Body, varToReplacement);

            return inlined;
        }

        private void HashConseRuleLeafs()
        {
            foreach (var rule in dslRules)
            {
                Dictionary<string, VarNode> varMap = new();
                Dictionary<ulong, ConstNode> constMap = new();
                var before = HashConsLeaf(rule.Before, varMap, constMap);
                var after = HashConsLeaf(rule.After, varMap, constMap);
                var precondition = HashConsLeaf(rule.Precondition, varMap, constMap);

                rule.Before = before;
                rule.After = after;
                rule.Precondition = precondition;
            }
        }

        private static AstNode HashConsLeaf(AstNode node, Dictionary<string, VarNode> varMap, Dictionary<ulong, ConstNode> constMap)
        {
            if (node == null)
                return null;
            return AstCloner.Clone(node, (AstNode src) => { return HashConseCallback(src, varMap, constMap); });
        }

        private static AstNode HashConseCallback(AstNode node, Dictionary<string, VarNode> varMap, Dictionary<ulong, ConstNode> constMap)
        {
            if (node is VarNode varNode)
            {
                if (varMap.TryGetValue(varNode.Name, out var existing))
                    return existing;

                var newVar = new VarNode(varNode.Name, varNode.BitSize);
                varMap[varNode.Name] = newVar;
                return varNode;
            }

            if (node is ConstNode constNode)
            {
                if (constMap.TryGetValue(constNode.UValue, out var existing))
                    return existing;

                var newConst = new ConstNode(constNode.UValue, constNode.BitSize);
                constMap[constNode.UValue] = newConst;
                return newConst;
            }

            return null;
        }

        // Update the rule to match constants modulo 2**w
        public static void AddConstantModularMatchingPreconditions(DslFunction isConstIntrinsic, DslFunction eqIntrinsic, IReadOnlyList<DslRule> rules)
        {
            foreach (var rule in rules)
            {
                // Get all unique constant nodes in the lhs of the rule
                var nodes = new List<AstNode>();
                GetNodes(rule.Before, nodes);
                var uniqueConstants = nodes
                    .Where(x => x is ConstNode)
                    .Select(x => (ConstNode)x).Distinct().ToList();

                // Skip if there are no constants to match.
                if (!uniqueConstants.Any())
                    continue;

                // Get all variables used in the rule.
                Dictionary<string, VarNode> uniqueVariables = GetUniqueVariables(new List<AstNode> { rule.Before, rule.After, rule.Precondition }).ToDictionary(x => x.Name, x => x);

                Dictionary<ulong, AstNode> replacements = new();
                foreach (var constant in uniqueConstants)
                {
                    var name = $"mconst{replacements.Count}";
                    if (uniqueVariables.ContainsKey(name))
                        throw new InvalidOperationException($"Rule {rule.Name} is using reserved name {name}");

                    var mconstVar = new VarNode(name, constant.BitSize);
                    uniqueVariables.Add(name, mconstVar);
                    replacements.Add(constant.UValue, mconstVar);

                    // Create a precondition requiring that (a) `mconst` is a constant
                    AstNode precondition = new IntrinsicCallNode(isConstIntrinsic.Name, isConstIntrinsic.ReturnType.Width, new List<AstNode>() { mconstVar });
                    // , and (b) mconst == constant % (2**width(mconst))
                    var eqCond = new IntrinsicCallNode(eqIntrinsic.Name, eqIntrinsic.ReturnType.Width, new List<AstNode>() { mconstVar, constant, });
                    precondition = new ConditionalAndNode(precondition, eqCond);

                    rule.Precondition = rule.Precondition == null ? precondition : new ConditionalAndNode(precondition, rule.Precondition);
                }

                rule.Before = AstCloner.ReplaceConstants(rule.Before, replacements);

            }
        }

        public static List<VarNode> GetUniqueVariables(IReadOnlyList<AstNode> nodes)
            => nodes.SelectMany(x => GetUniqueVariables(x)).Distinct().ToList();

        public static List<VarNode> GetUniqueVariables(AstNode node)
            => GetNodes(node).Where(x => x is VarNode).Select(x => (VarNode)x).Distinct().OrderBy(x => x.Name).ToList();

        public static List<AstNode> GetNodes(AstNode root)
        {
            var nodes = new List<AstNode>();
            GetNodes(root, nodes);
            return nodes;
        }

        public static void GetNodes(AstNode root, List<AstNode> children)
        {
            if (root == null)
                return;
            foreach (var child in root.Children)
                GetNodes(child, children);
            children.Add(root);
            return;
        }
    }
}
