using Antlr4.Runtime.Misc;
using Mba.Ast;
using Mba.Common.Ast;
using Mba.Simplifier.Bindings;
using Mba.Testing;
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
    /// <summary>
    /// Generated rust applier struct and function
    /// </summary>
    /// <param name="StructName">The name of the applier struct</param>
    /// <param name="ArgNames">An ordered list of the function argument names</param>
    /// <param name="Body">The code containing both the struct and Applier trait implementation.</param>
    public record Applier(string StructName, IReadOnlyList<string> ArgNames, string Body);

    public record PreconditionMethod(string MethodName, IReadOnlyList<string> ArgNames, string Body);

    public static class EggBackend
    {
        public static string GenerateEggDsl(IReadOnlyList<DslRuleOld> rules)
        {
            var ruleSb = new StringBuilder();
            var codeBuilder = new CodeBuilder(ruleSb);
            var applierSb = new StringBuilder();

            codeBuilder.AppendLine("pub fn get_generated_rules() -> Vec<Rewrite> {");
            codeBuilder.Indent();
            codeBuilder.AppendLine("vec![");
            codeBuilder.Indent();

            foreach(var rewrite in rules)
            {
                // In the case of a rewrite rule like `x-x` => 0, we need to some way of telling ISLE what bit width to create `0` as.
                // To solve this we keep track of variable and width occurrences during transpilation, then pick one of the occurrences to steal the width field from.
                // Special care needs to be taken for zext/trunc instructions though.
                Dictionary<AstNode, string> boundedNames = new();
                Dictionary<ulong, string> modularConstants = new();

                // Append the start of the rewrite rule.
                var sanitizedName = "rule_" + rewrite.Name.Replace("-", "_");
                //codeBuilder.Append($"// {rewrite.Name}: {rewrite.Before.ToString()} => {rewrite.After.ToString()}\n");
                codeBuilder.AppendLine($"// {rewrite.Name}:");
                codeBuilder.AppendLine($"// {rewrite.Before.ToString()} => {rewrite.After.ToString()}");
                codeBuilder.Append($@"rewrite!(""{rewrite.Name}""; ");

                // Emit a string representation of the LHS ast
                ruleSb.Append(@"""");
                TranspileLhs(rewrite.Before, ruleSb, boundedNames, modularConstants);
                ruleSb.AppendLine(@""" => {");

                // Generate an applier for the RHS
                var outArgs = new OrderedSet<AstNode>();
                var boundingNode = GetWidthBoundingNode(rewrite.After, boundedNames);
                var boundingName = boundedNames[boundingNode];
                var cache = new Dictionary<AstNode, string>();
                // Lower the AST to a series of egg AST constructor calls.
                var rhsDagStr = TranspileRhs(rewrite.After, boundedNames, cache, boundingNode, outArgs);
                var applier = GetRhsApplier(sanitizedName, outArgs, boundedNames, rhsDagStr, cache[rewrite.After]);


                // Actually emit the rhs of the rule now
                codeBuilder.Indent();
                codeBuilder.AppendLine($"{applier.StructName} {{");
                codeBuilder.Indent();
                foreach (var argName in applier.ArgNames)
                    codeBuilder.AppendLine(@$"{argName} : ""?{argName}"".parse().unwrap(),");
                codeBuilder.Outdent();
                codeBuilder.AppendLine("}");
                codeBuilder.Outdent();

    

                // Compile the precondition to a method.
                var preconditionMethodName = $"{sanitizedName}_precondition";
                var preconditionArgs = boundedNames.Where(x => x.Key is ConstNode || x.Key is WildCardConstantNode).OrderBy(x => x.Value).ToList();
                var preconditionMethod = GetPreconditionMethod(preconditionMethodName, preconditionArgs, rewrite.ManualPrecondition);


                // Emit the precondition if one exists.
                if (preconditionMethod == null)
                {
                    codeBuilder.AppendLine("}),");
                }

                else
                {
                    var precondArgStr = String.Join(", ", preconditionArgs.Select(x => $@"""?{x.Value}"""));
                    codeBuilder.AppendLine($@"}} if ({preconditionMethodName}({precondArgStr}))),");
                }

                codeBuilder.AppendLine("");

                // Append the precondition method
                if(preconditionMethod != null)
                    applierSb.AppendLine(preconditionMethod + "\n");

                applierSb.AppendLine(applier.Body);

            }

            codeBuilder.Outdent();
            codeBuilder.AppendLine("]");
            codeBuilder.Outdent();
            codeBuilder.AppendLine("}");


            var text = codeBuilder.ToString() + Environment.NewLine + applierSb.ToString();
            //File.WriteAllText("rules.rs", text);

            Console.WriteLine(codeBuilder.ToString());

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
                modularConstants.TryAdd((ulong)constNode.Value, constName);
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

        private static string TranspileRhs(AstNode ast, Dictionary<AstNode, string> boundedNames, Dictionary<AstNode, string> cache, AstNode widthField, OrderedSet<AstNode> outArgs)
        {
            var sb = new StringBuilder();

            TranspileRhsInternal(ast, sb, boundedNames, cache, widthField, outArgs);
            return sb.ToString();
        }

        private static void TranspileRhsInternal(AstNode ast, StringBuilder sb, Dictionary<AstNode, string> boundedNames, Dictionary<AstNode, string> cache, AstNode widthField, OrderedSet<AstNode> outArgs)
        {
            // Assign the symbol id to a local variable
            if (ast is VarNode || ast is WildCardConstantNode)
            {
                var name = boundedNames[ast];
                var idName = $"{name}_id";
                sb.AppendLine($"let {idName} = subst[self.{name}];");
                outArgs.Add(ast);
                cache[ast] = idName;

                // Compute the bounded width variable if we need it.
                if (ast == widthField)
                    sb.AppendLine($"let bounded_width = egraph[{idName}].data.width;");
                return;
            }

            // Handle a literal constant, e.g. "-1)
            if (ast is ConstNode constNode)
            {
                // Fetch the id of the field.
                if(!cache.ContainsKey(widthField))
                    TranspileRhsInternal(widthField, sb, boundedNames, cache, widthField, outArgs);
                



                //var widthFieldName = boundedNames[widthField];
                var literalName = $"literal_{constNode.UValue}_id";
                sb.AppendLine($"let {literalName} = egraph.add(SimpleAst::Constant {{c: {constNode.UValue}, width: bounded_width }});");
                //outArgs.Add(ast);
                outArgs.Add(widthField);
                cache[ast] = literalName;
                return;
            }

            // Assign each of the children to temporary variables.
            foreach (var child in ast.Children)
            {
                if (cache.ContainsKey(child))
                    continue;
                TranspileRhsInternal(child, sb, boundedNames, cache, widthField, outArgs);
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
                    sb.AppendLine($"let {destName} = egraph.add(SimpleAst::{ast.Kind.ToString()} {{a: {childNames}, to: {ast.BitSize} }});");
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

        private static string GetPreconditionMethod(string methodName, IReadOnlyList<KeyValuePair<AstNode, string>> constantNodes, bool manualPrecondition)
        {
            if (!constantNodes.Any())
                return null;

            var sb = new CodeBuilder();
            var args = String.Join(", ", constantNodes.Select(x => $"{x.Value}:  &str"));
            sb.AppendLine($"pub fn {methodName}({args}) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {{");
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
                var eqmodCond = String.Join("|| ", modularConstants.Select(x => $"!eqmod({x.Value}_value.unwrap(), {(x.Key as ConstNode).UValue}, egraph[subst[{x.Value}]].data.width)"));
                sb.AppendLine($"if {eqmodCond} {{ return false; }}");
            }

            if(manualPrecondition)
            {
                var manualCond = $"manual_{methodName}(egraph, subst, {String.Join(", ", constantNodes.Select(x => x.Value))})";
                sb.AppendLine($"if !{manualCond} {{ return false; }}");
            }

            sb.AppendLine("return true;");
            for (int i = 0; i < 2; i++)
            {
                sb.Outdent();
                sb.AppendLine("}");
            }

            return sb.ToString();
        }



        private static Applier GetRhsApplier(string ruleName, OrderedSet<AstNode> args, Dictionary<AstNode, string> boundedNames, string rhsStr, string rhsRootVariableName)
        {
            var sb = new CodeBuilder();

            var structName = $"applier_{ruleName}";
            sb.AppendLine(@$"pub struct {structName} {{");
            sb.Indent();

            var argNames = args.Select(x => boundedNames[x]).ToList();
            foreach (var argName in argNames)
                sb.AppendLine($"pub {argName}: Var,");
            sb.Outdent();
            sb.AppendLine("}\n");


            rhsStr = String.Join("\n", rhsStr.Split(new[] { '\r', '\n' }, StringSplitOptions.RemoveEmptyEntries).Select(x => "        " + x));


            string body = @$"impl Applier<SimpleAst, MbaAnalysis> for {structName} {{
    fn apply_one(
        &self,
        egraph: &mut EEGraph,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<SimpleAst>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {{
{rhsStr}

        if egraph.union(eclass, {rhsRootVariableName}) {{
            vec![{rhsRootVariableName}]
        }} else {{
            vec![]
        }}
    }}
}}
";
            sb.Append(body);
            return new Applier(structName, argNames, sb.ToString());
            
        }

        private static string GetOperatorName(AstNode node)
        {
            return node.Kind switch
            {
                AstKind.Pow => "**",
                AstKind.Add => "+",
                AstKind.Mul => "*",
                AstKind.And => "&",
                AstKind.Or => "|",
                AstKind.Xor => "^",
                AstKind.Neg => "~",
                AstKind.Lshr => ">>",
                //AstKind.Zext => $"\\\"zx i{node.BitSize}\\\"",
                //AstKind.Trunc => $"\\\"tr i{node.BitSize}\\\"",
                AstKind.Zext => "zx",
                AstKind.Trunc => "tr",
                AstKind.ICmp => $"\\\"icmp {AstFormatter.GetPredicateOperator((node as ICmpNode).Pred)}\\\"",
                AstKind.Select => "select",
                _ => throw new InvalidOperationException($"Cannot get operator for {node.Kind}"),
            };
        }
    }
}
