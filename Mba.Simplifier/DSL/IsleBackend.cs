using Mba.Ast;
using Mba.Common.MSiMBA;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.DSL
{
    public static class IsleBackend
    {
        const int HARDCODED_WIDTH = 64;

        const string WIDTH_NAME = "width";

        public static string GenerateIsleDsl(IReadOnlyList<DslRule> rules)
        {
            var sb = new StringBuilder();

            int rc = 0;
            foreach (var rewrite in rules)
            {
                // In the case of a rewrite rule like `x-x` => 0, we need to some way of telling what bit width to create `0` as.
                // To solve this we keep track of variable and width occurrences during transpilation, then pick one of the occurrences to steal the width field from.
                // Special care needs to be taken for zext/trunc instructions though.
                HashSet<string> boundedIndices = new();
                HashSet<string> boundedWidths = new();

                sb.Append($";; {rewrite.Name}\n");
                sb.Append($"(rule {rc}");
                rc++;

                TranspileLhs(rewrite.Before, sb, boundedIndices, boundedWidths);
                sb.Append("\n");
                sb.Append("    ");

                TranspileRhs(rewrite.After, sb, boundedIndices, boundedWidths);
                sb.Append("\n)\n\n");
            }

            return sb.ToString();
        }

        private static void TranspileLhs(AstNode ast, StringBuilder sb, HashSet<string> boundedIndices, HashSet<string> boundedWidths)
        {
            int dataCount = 0;
            sb.Append("(lower ");
            TranspileLhsInternal(ast, sb, boundedIndices, boundedWidths);
            sb.Append(")");
        }


        private static void TranspileLhsInternal(AstNode ast, StringBuilder sb, HashSet<string> boundedIndices, HashSet<string> boundedWidths)
        {
            bool parens = false;
            if (ast is VarNode varNode)
            {
                sb.Append($"{varNode.Name}");
                boundedIndices.Add(varNode.Name);
            }

            else
            {
                parens = true;
                sb.Append($"(SimpleAst.{GetOperatorName(ast.Kind)} ");
            }
            for (int i = 0; i < ast.Children.Count; i++)
            {
                var child = ast.Children[i];
                TranspileLhsInternal(child, sb, boundedIndices, boundedWidths);
                if (i != ast.Children.Count - 1)
                {
                    sb.Append(" ");
                }
            }

            if (ast is ConstNode constNode)
            {
                var name = $"width{boundedWidths.Count}";
                boundedWidths.Add(name);

                sb.Append($"{(ulong)constNode.Value} {name}");
            }

            if (ast is WildCardConstantNode wc)
            {
                var name = $"width{boundedWidths.Count}";
                boundedWidths.Add(name);

                sb.Append($"{wc.Name} {name}"); // TODO: Maybe we need to specify the width here?
            }

            if (parens)
                sb.Append(")");

        }

        private static void TranspileRhs(AstNode ast, StringBuilder sb, HashSet<string> boundedIndices, HashSet<string> boundedWidths)
        {
            TranspileRhsInternal(ast, sb, boundedIndices, boundedWidths);
        }

        private static void TranspileRhsInternal(AstNode ast, StringBuilder sb, HashSet<string> boundedIndices, HashSet<string> boundedWidths)
        {
            bool parens = true;
            sb.Append($"({GetOperatorName(ast.Kind)} ");

            for (int i = 0; i < ast.Children.Count; i++)
            {
                var child = ast.Children[i];
                TranspileRhsInternal(child, sb, boundedIndices, boundedWidths);
                if (i != ast.Children.Count - 1)
                {
                    sb.Append(" ");
                }
            }
            if (ast is ConstNode constNode)
            {
                var width_field = boundedWidths.Any() ? boundedWidths.First() : $"(GetWidth {boundedIndices.First()})";
                sb.Append($"{(ulong)constNode.Value} {width_field}");
            }

            if (ast is WildCardConstantNode wc)
            {
                sb.Append($"{wc.Name} {boundedWidths.First()}");
            }

            else if (ast is VarNode varNode)
            {
                sb.Append($"{varNode.Name}");
            }

            if (parens)
                sb.Append(")");
        }



        private static string GetOperatorName(AstKind kind)
        {
            return kind switch
            {
                AstKind.Power => "Pow",
                AstKind.Add => "Add",
                AstKind.Mul => "Mul",
                AstKind.And => "And",
                AstKind.Or => "Or",
                AstKind.Xor => "Xor",
                AstKind.Neg => "Neg",
                AstKind.Const => "Constant",
                AstKind.WildCardConstant => "Constant",
                AstKind.Var => "Any",
                _ => throw new InvalidOperationException($"Unrecognized operator: {kind.ToString()}")
            };
        }
    }
}
