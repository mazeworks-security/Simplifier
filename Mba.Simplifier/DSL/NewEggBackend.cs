using Mba.Ast;
using Mba.Common.Ast;
using Mba.Common.MSiMBA;
using Mba.Common.Parsing;
using Mba.Testing;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.DSL
{
    public static class DslRuntime
    {
        public static DslFunction GetIsConstantFunction(IReadOnlyList<DslFunction> functions)
            => functions.Single(x => x.Name == "is_const");

        // Gets a function that checks whether some node is a equivalent to a constant c1, where c1 is reduced modulo 2**get_width(node).
        public static DslFunction GetConstantEqFunction(IReadOnlyList<DslFunction> functions)
            => functions.Single(x => x.Name == "const_eq");
    }

    public class NewEggBackend
    {
        IReadOnlyList<DslFunction> dslFunctions;

        IReadOnlyList<DslRule> dslRules;

        private IReadOnlyDictionary<string, DslFunction> nameToFunc;

        public NewEggBackend(Dsl dsl)
        {
            dslFunctions = dsl.FunctionGroups.Single().Functions;
            dslRules = dsl.RuleGroups.Single().Rules;
            nameToFunc = dslFunctions.ToDictionary(x => x.Name, x => x);
        }

        public void Generate()
        {
            // Preprocess the DSL.
            DslPreprocessor.Run(dslFunctions, dslRules);

            GenerateEggDsl(dslRules);
        }

        public static string GenerateEggDsl(IReadOnlyList<DslRule> rules)
        {
            var ruleSb = new StringBuilder();
            var codeBuilder = new CodeBuilder(ruleSb);
            var applierSb = new StringBuilder();

            codeBuilder.AppendLine("pub fn get_generated_rules() -> Vec<Rewrite> {");
            codeBuilder.Indent();
            codeBuilder.AppendLine("vec![");
            codeBuilder.Indent();

            foreach (var rewrite in rules)
            {
                // In the case of a rewrite rule like `x-x` => 0, we need to some way of telling ISLE what bit width to create `0` as.
                // To solve this we keep track of variable and width occurrences during transpilation, then pick one of the occurrences to steal the width field from.
                // Special care needs to be taken for zext/trunc instructions though.
                Dictionary<AstNode, string> boundedNames = new();

                // Emit the rule header
                codeBuilder.AppendLine($"// {rewrite.Before.ToString()} => {rewrite.After.ToString()}");
                codeBuilder.Append($@"rewrite!(""{rewrite.Name}""; ");

                // Emit the LHS of the rule as an egg s-expr.
                ruleSb.Append(@"""");
                TranspileLhs(rewrite.Before, ruleSb);
                ruleSb.AppendLine(@""" => {");


                // Generate an applier for the RHS
                var sanitizedName = "rule_" + rewrite.Name.Replace("-", "_");
                var applier = GetRhsApplier(sanitizedName, rewrite);


                // Actually emit the rhs of the rule now
                codeBuilder.Indent();
                codeBuilder.AppendLine($"{applier.StructName} {{");
                codeBuilder.Indent();
                foreach (var argName in applier.ArgNames)
                    codeBuilder.AppendLine(@$"{argName} : ""?{argName}"".parse().unwrap(),");
                codeBuilder.Outdent();
                codeBuilder.AppendLine("}");
                codeBuilder.Outdent();

                // Finish the rule if there is no preconditoin
                if(rewrite.Precondition == null)
                {
                    codeBuilder.AppendLine("}),");
                    codeBuilder.AppendLine("");
                    applierSb.AppendLine(applier.Body);
                    continue;
                }


                //var preconditionMethodName = $"{sanitizedName}_precondition";
                //GetPreconditionMethod2(preconditionMethodName, rewrite.Precondition);

                //var preconditionArgs = boundedNames.Where(x => x.Key is ConstNode || x.Key is WildCardConstantNode).OrderBy(x => x.Value).ToList();
                //var preconditionMethod = GetPreconditionMethod(preconditionMethodName, preconditionArgs, rewrite.Precondition != null);
                var preconditionMethod = GetPreconditionMethod2(sanitizedName, rewrite.Precondition);

                var precondArgStr = String.Join(", ", preconditionMethod.ArgNames.Select(x => $@"""?{x}"""));
                codeBuilder.AppendLine($@"}} if ({preconditionMethod.MethodName}({precondArgStr}))),");
                

                codeBuilder.AppendLine("");
                applierSb.AppendLine(preconditionMethod.Body + "\n");
                applierSb.AppendLine(applier.Body);

            }

            codeBuilder.Outdent();
            codeBuilder.AppendLine("]");
            codeBuilder.Outdent();
            codeBuilder.AppendLine("}");


            var text = codeBuilder.ToString() + Environment.NewLine + applierSb.ToString();
            Console.WriteLine(codeBuilder.ToString());

            Console.WriteLine(applierSb.ToString());

            return null;
        }

        private static void TranspileLhs(AstNode ast, StringBuilder sb)
        {
            if (ast is VarNode varNode)
            {
                sb.Append($"?{varNode.Name}");
                return;
            }

            // Literal constants (e.g. -1) should not appear in the LHS of a rule.
            // They must be substituted for temporary variables, with a precondition checking the constant modulo 2**w.
            if (ast is ConstNode constNode)
                throw new InvalidOperationException();
            // TODO: Delete WildCardConstantNode
            if (ast is WildCardConstantNode wc)
                throw new InvalidOperationException();

            // Otherwise this is some kind of operation with one or more children.
            Debug.Assert(ast.Children.Any());
            sb.Append($"({GetOperatorName(ast)} ");

            for (int i = 0; i < ast.Children.Count; i++)
            {
                var child = ast.Children[i];
                TranspileLhs(child, sb);
                if (i != ast.Children.Count - 1)
                    sb.Append(" ");

            }

            sb.Append(")");
        }


        private static void TranspileRhs(AstNode ast, StringBuilder sb, Dictionary<AstNode, string> cache, VarNode widthField, OrderedSet<VarNode> outArgs)
        {
            // Assign the symbol id to a local variable
            if (ast is VarNode varNode)
            {
                var name = varNode.Name;
                var idName = $"{name}_id";
                sb.AppendLine($"let {idName} = subst[self.{name}];");
                outArgs.Add(varNode);
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
                if (!cache.ContainsKey(widthField))
                    TranspileRhs(widthField, sb, cache, widthField, outArgs);

                var literalName = $"literal_{constNode.UValue}_id";
                sb.AppendLine($"let {literalName} = egraph.add(SimpleAst::Constant {{c: {constNode.UValue}, width: bounded_width }});");
                outArgs.Add(widthField);
                cache[ast] = literalName;
                return;
            }

            // Assign each of the children to temporary variables.
            foreach (var child in ast.Children)
            {
                if (cache.ContainsKey(child))
                    continue;
                TranspileRhs(child, sb, cache, widthField, outArgs);
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
                case AstKind.Zext:
                case AstKind.Trunc:
                    sb.AppendLine($"let {destName} = egraph.add(SimpleAst::{ast.Kind.ToString()}([{childNames}]));");
                    break;
                /*
                case AstKind.Zext:
                case AstKind.Trunc:
                    sb.AppendLine($"let {destName} = egraph.add(SimpleAst::{ast.Kind.ToString()} {{a: {childNames}, to: {ast.BitSize} }});");
                    break;
                */
                case AstKind.Select:
                    sb.AppendLine($"let {destName} = egraph.add(SimpleAst::Select {{children: [{childNames}]}});");
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

        private static PreconditionMethod GetPreconditionMethod2(string ruleName, AstNode precondition)
        {

            var constantNodes = DslPreprocessor.GetUniqueVariables(precondition);

            var stringBuilder = new StringBuilder();
            var codeBuilder = new CodeBuilder(stringBuilder);
            var args = String.Join(", ", constantNodes.Select(x => $"{x.Name}:  &'a str"));
            var methodName = $"{ruleName}_precondition";
            codeBuilder.AppendLine($"pub fn {methodName}<'a>({args}) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool + 'a {{");
            codeBuilder.Indent();

            codeBuilder.AppendLine($"move |egraph, _, subst| {{");
            codeBuilder.Indent();

            foreach (var arg in constantNodes)
            {
                codeBuilder.AppendLine($"let {arg.Name}_id = subst[{arg.Name}.parse().unwrap()];");
                codeBuilder.AppendLine($"let {arg.Name} = &egraph[{arg.Name}_id];");
            }

            codeBuilder.Append($"let precondition = ");
            LowerPreconditionNode(stringBuilder, precondition);
            stringBuilder.Append(";\n");

            codeBuilder.AppendLine($"if !precondition {{ return false; }}");

            codeBuilder.AppendLine("return true;");
            for (int i = 0; i < 2; i++)
            {
                codeBuilder.Outdent();
                codeBuilder.AppendLine("}");
            }

            return new PreconditionMethod(methodName, constantNodes.Select(x => x.Name).ToList(), codeBuilder.ToString());
        }

        private static void LowerPreconditionNode(StringBuilder sb, AstNode precondition)
        {
            if (precondition is VarNode varNode)
            {
                sb.Append(varNode.Name);
                return;
            }

            if (precondition is ConstNode constNode)
            {
                sb.Append(constNode.UValue);
                return;
            }

            if(precondition is IntrinsicCallNode intrinsicCall)
            {
                sb.Append($"{intrinsicCall.Name}(egraph, ");
                for (int i = 0; i < intrinsicCall.Children.Count; i++)
                {
                    LowerPreconditionNode(sb, intrinsicCall.Children[i]);
                    if (i != intrinsicCall.Children.Count - 1)
                        sb.Append(", ");
                }
                sb.Append(")");
                return;
            }

            switch(precondition.Kind)
            {
                case AstKind.Add:
                case AstKind.Mul:
                case AstKind.And:
                case AstKind.Or:
                case AstKind.Xor:
                case AstKind.Lshr:
                case AstKind.ICmp:
                case AstKind.ConditionalAnd:
                case AstKind.ConditionalOr:
                    Debug.Assert(precondition.Children.Count == 2);
                    var binop = AstFormatter.GetOperatorName(precondition);
                    sb.Append("(");
                    LowerPreconditionNode(sb, precondition.Children[0]);
                    sb.Append($" {binop} ");
                    LowerPreconditionNode(sb, precondition.Children[1]);
                    sb.Append(")");
                    break;
                case AstKind.Neg:   
                    sb.Append("(!");
                    LowerPreconditionNode(sb, precondition.Children[0]);
                    sb.Append(")");
                    break;

                default:
                    throw new InvalidOperationException();
            }

        }

        private static string GetPreconditionMethod(string methodName, IReadOnlyList<KeyValuePair<AstNode, string>> constantNodes, bool manualPrecondition)
        {
            if (!constantNodes.Any())
                return null;

            var sb = new CodeBuilder();
            var args = String.Join(", ", constantNodes.Select(x => $"{x.Value}:  &str"));
            sb.AppendLine($"pub fn {methodName}({args}) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {{");
            sb.Indent();

            foreach (var arg in constantNodes)
                sb.AppendLine($"let {arg.Value} = {arg.Value}.parse().unwrap();");

            sb.AppendLine($"move |egraph, _, subst| {{");
            sb.Indent();

            // Assert that every constant is actually a constant.
            foreach (var arg in constantNodes)
                sb.AppendLine($"let {arg.Value}_value = as_constant(&egraph[subst[{arg.Value}]].data);");
            var all_constants_cond = String.Join("|| ", constantNodes.Select(x => $"{x.Value}_value.is_none()"));
            sb.AppendLine($"if {all_constants_cond} {{ return false; }}");

            var modularConstants = constantNodes.Where(x => x.Key is ConstNode).ToList();
            if (modularConstants.Any())
            {
                var eqmodCond = String.Join("|| ", modularConstants.Select(x => $"!eqmod({x.Value}_value.unwrap(), {(x.Key as ConstNode).UValue}, egraph[subst[{x.Value}]].data.width)"));
                sb.AppendLine($"if {eqmodCond} {{ return false; }}");
            }

            if (manualPrecondition)
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

        private static Applier GetRhsApplier(string sanitizedName, DslRule rewrite)
        {
            // If the RHS contains constants, we need to pull the width from somewhere.
            // The node we pull the width from is referred to as the bounding node.
            var boundingNode = GetWidthBoundingNode(rewrite.After, DslPreprocessor.GetUniqueVariables(rewrite.Before).ToHashSet());

            // Lower the RHS to a series of egg constructor calls.
            var outArgs = new OrderedSet<VarNode>();
            var cache = new Dictionary<AstNode, string>();
            var sb = new StringBuilder();
            TranspileRhs(rewrite.After, sb, cache, boundingNode, outArgs);
            var rhsDagStr = sb.ToString();

            // Create an egg applier struct and method body.
            var applier = BuildRhsApplier(sanitizedName, outArgs, rhsDagStr, cache[rewrite.After]);
            return applier;
        }

        private static VarNode GetWidthBoundingNode(AstNode rhs, HashSet<VarNode> boundedNames)
        {
            // Get all nodes in the rhs of the pattern
            var children = DslPreprocessor.GetNodes(rhs);

            // Ideally we want to find a variable that is used in both the lhs and rhs.
            // This way our egg applier function does not depend on a spurious variable to fetch the width.
            foreach (var node in children)
            {
                // Skip if this node was not bounded to a named variable.
                if (!boundedNames.Contains(node))
                    continue;

                if (node is VarNode vn)
                {
                    return vn;
                }
            }

            // Otherwise return the first variable.
            return boundedNames.OrderBy(x => x.ToString()).First();
        }

        private static Applier BuildRhsApplier(string ruleName, OrderedSet<VarNode> args, string rhsStr, string rhsRootVariableName)
        {
            var sb = new CodeBuilder();

            var structName = $"applier_{ruleName}";
            sb.AppendLine(@$"pub struct {structName} {{");
            sb.Indent();

            var argNames = args.Select(x => x.Name).ToList();
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

