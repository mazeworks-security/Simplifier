using Antlr4.Runtime.Misc;
using Mba.Ast;
using Mba.Common.Ast;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using static Antlr4.Runtime.Atn.SemanticContext;

namespace Mba.Simplifier.DSL
{
    public static class EggBackend
    {
        public static string GenerateEggDsl(IReadOnlyList<DslRule> rules)
        {
            var rewriteSb = new StringBuilder();
            var applierSb = new StringBuilder();
            foreach(var rewrite in rules)
            {
                // In the case of a rewrite rule like `x-x` => 0, we need to some way of telling ISLE what bit width to create `0` as.
                // To solve this we keep track of variable and width occurrences during transpilation, then pick one of the occurrences to steal the width field from.
                // Special care needs to be taken for zext/trunc instructions though.
                Dictionary<AstNode, string> boundedNames = new();
                Dictionary<ulong, string> modularConstants = new();

                var sanitizedName = "rule_" + rewrite.Name.Replace("-", "_");

                rewriteSb.Append($"// {rewrite.Name}: {rewrite.Before.ToString()} => {rewrite.After.ToString()}\n");
                rewriteSb.Append($@"        rewrite!(""{rewrite.Name}""; ");

                rewriteSb.Append(@"""");
                TranspileLhs(rewrite.Before, rewriteSb, boundedNames, modularConstants);
                rewriteSb.AppendLine(@""" => ");
                rewriteSb.Append("\n\n\n");

                // First we need to do the precondition.
                var precondition = GetPreconditionMethod(sanitizedName, boundedNames.Where(x => (x is ConstNode || x is WildCardConstantNode)).ToList());
                Console.WriteLine(precondition + "\n\n\n");
                continue;

                var boundingNode = GetWidthBoundingNode(rewrite.After, boundedNames);
                var boundingName = boundedNames[boundingNode];
                applierSb.AppendLine($"let bounded_width = &egraph[subst[self.{boundingName}]].data.width;");
                TranspileRhs(rewrite.After, applierSb, boundedNames, new(), boundingName);
                applierSb.AppendLine("\n\n\n");
            }

            Console.WriteLine(applierSb.ToString());

            return null;
        }

        private static void TranspileLhs(AstNode ast, StringBuilder sb, Dictionary<AstNode, string> boundedNames, Dictionary<ulong, string> modularConstants)
        {
            if (ast is VarNode varNode)
            {
                sb.Append($"?{varNode.Name}");
                boundedNames[ast] = (varNode.Name);
                return;
            }

            // Handle a literal constant, e.g. "-1)
            if (ast is ConstNode constNode)
            {
                var constName = (modularConstants.ContainsKey((ulong)constNode.Value) ? modularConstants[(ulong)constNode.Value] : $"mconst{modularConstants.Count}");
                sb.Append($"?{constName}");
                boundedNames[ast] = (constName);
                return;
            }

            // Handle a wildcard constant(i.e. a variable that must be a constant)
            if(ast is WildCardConstantNode wc)
            {
                sb.Append($"?{wc.Name}");
                boundedNames[ast] = (wc.Name);
                return;
            }

            // Otherwise this is some kind of operation with one or more children.
            Debug.Assert(ast.Children.Any());
            sb.Append($"({GetOperatorName(ast)} ");

            for (int i = 0; i < ast.Children.Count; i++)
            {
                var child = ast.Children[i];
                TranspileLhs(child, sb, boundedNames, modularConstants);
                if (i != ast.Children.Count - 1)
                    sb.Append(" ");
                
            }

            sb.Append(")");
        }

        private static void TranspileRhs(AstNode ast, StringBuilder sb, Dictionary<AstNode, string> boundedNames, Dictionary<AstNode, string> cache, string widthFieldName)
        {
            // Assign the symbol id to a local variable
            if (ast is VarNode || ast is WildCardConstantNode)
            {
                var name = boundedNames[ast];
                var idName = $"{name}_id";
                sb.AppendLine($"let {idName} = subst[self.{name}];");
                cache[ast] = idName;
                return;
            }

            // Handle a literal constant, e.g. "-1)
            if (ast is ConstNode constNode)
            {
                var literalName = $"literal_{((ulong)constNode.Value)}_id";
                sb.AppendLine($"let {literalName} = egraph.add(SimpleAst::Constant {{c: {constNode.Value}, width: {widthFieldName} }});");
                cache[ast] = literalName;
                return;
            }

            // Assign each of the children to temporary variables.
            foreach (var child in ast.Children)
            {
                if (cache.ContainsKey(child))
                    continue;
                TranspileRhs(child, sb, boundedNames, cache, widthFieldName);
            }

            var destName = $"t{cache.Count}";
            var childNames = String.Join(", ", ast.Children.Select(x => cache[x]));
            switch (ast.Kind)
            {
                case AstKind.Add:
                case AstKind.Mul:
                case AstKind.Pow:
                case AstKind.And:
                case AstKind.Or:
                case AstKind.Xor:
                case AstKind.Neg:
                case AstKind.Lshr:
                case AstKind.Select:
                    sb.AppendLine($"let {destName} = egraph.add(SimpleAst::{ast.Kind.ToString()}([{childNames}]));");
                    break;
                case AstKind.Zext:
                case AstKind.Trunc:
                    sb.AppendLine($"let {destName} = egraph.add(SimpleAst::{ast.Kind.ToString()} {{a: {childNames.Single()}, to: {ast.BitSize} }});");
                    break;
                case AstKind.ICmp:
                    var predicate = (ast as ICmpNode).Pred;
                    sb.AppendLine($"let {destName} = egraph.add(SimpleAst::ICmp {{predicate: Predicate::{predicate}, children: [{childNames}]}});");
                    break;
                default:
                    throw new InvalidOperationException($"Cannot lower node kind {ast.Kind}");

            }

            cache[ast] = destName;
        }

        private static AstNode GetWidthBoundingNode(AstNode rhs, Dictionary<AstNode, string> boundedNames)
        {
            // Get all nodes in the rhs of the pattern
            var children = new List<AstNode>();
            GetNodes(rhs, children);

            // Ideally we want to find a variable that is used in both the lhs and rhs.
            // This way our egg applier function does not depend on a spurious variable to fetch the width.
            foreach(var node in children)
            {
                // Skip if this node was not bounded to a named variable.
                if (!boundedNames.ContainsKey(node))
                    continue;

                if (node is VarNode || node is WildCardConstantNode)
                {
                    return node;
                }
            }

            // Otherwise return the first variable.
            return boundedNames.Keys.Where(x => x is VarNode).OrderBy(x => x.ToString()).First();
        }


        private static void GetNodes(AstNode root, List<AstNode> children)
        {
            foreach(var child in root.Children)
                GetNodes(child, children);
            children.Add(root);
            return;
        }

        private static string GetPreconditionMethod(string ruleName, List<KeyValuePair<AstNode, string>> names)
        {
            var constantNodes = names.OrderBy(x => x.Value).ToList();

            var sb = new CodeBuilder();
            var args = String.Join(", ", constantNodes.Select(x => $"{x.Value}:  &str"));
            sb.AppendLine($"pub fn {ruleName}_precondition({args}) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {{");
            sb.Indent();

            foreach(var arg in constantNodes)
                sb.AppendLine($"let {arg.Value} = {arg.Value}.parse().unwrap();");

            sb.AppendLine($"move |egraph, _, subst| {{");
            sb.Indent();

            // Assert that every constant is actually a constant.
            foreach(var arg in constantNodes)
                sb.AppendLine($"let {arg.Value}_value = as_constant(&egraph[subst[{arg.Value}]].data);");
            var all_constants_cond = String.Join("|| ", constantNodes.Select(x => $"{x.Value}_value.is_none()"));
            sb.AppendLine($"if {all_constants_cond} {{ return false; }}");

            var modularConstants = constantNodes.Where(x => x.Key is ConstNode).ToList();
            if(modularConstants.Any())
            {
                var eqmodCond = String.Join("|| ", modularConstants.Select(x => $"!eqmod({x.Value}_value, {(x.Key as ConstNode).UValue}, egraph[subst[{x.Value}]].data.width)"));
                sb.AppendLine($"if {eqmodCond} {{ return false; }}");
            }

            sb.AppendLine("return true;");
            for (int i = 0; i < 2; i++)
            {
                sb.Outdent();
                sb.AppendLine("}");
            }

            return sb.ToString();
        }

        private static string GetOperatorName(AstNode node)
        {
            return node.Kind switch
            {
                AstKind.Pow => "**",
                AstKind.Add => "**",
                AstKind.Mul => "**",
                AstKind.And => "&",
                AstKind.Or => "|",
                AstKind.Xor => "^",
                AstKind.Neg => "~",
                AstKind.Lshr => ">>",
                AstKind.Zext => $"\"zx i{node.BitSize}\"",
                AstKind.Trunc => $"\"tr i{node.BitSize}\"",
                AstKind.ICmp => $"\"icmp {AstFormatter.GetPredicateOperator((node as ICmpNode).Pred)}\"",
                AstKind.Select => "select",
                _ => throw new InvalidOperationException($"Cannot get operator for {node.Kind}"),
            };
        }
    }
}
