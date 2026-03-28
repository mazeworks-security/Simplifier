using Mba.Ast;
using Mba.Common.Ast;
using Mba.Common.MSiMBA;
using Mba.Common.Parsing;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using System.Xml.Linq;

namespace Mba.Simplifier.DSL
{
    // Class for lowering our term rewriting DSL down to ISLE definitions
    public class IsleBackend
    {
        IReadOnlyList<DslFunction> dslFunctions;

        IReadOnlyList<DslRule> dslRules;

        public IsleBackend(Dsl dsl)
        {
            dslFunctions = dsl.FunctionGroups.First().Functions;
            dslRules = dsl.RuleGroups.First().Rules;
        }

        public void Generate()
        {
            DslPreprocessor.Run(dslFunctions, dslRules);

            GenerateIsleDsl(dslRules);
        }

        public void GenerateIsleDsl(IReadOnlyList<DslRule> rules)
        {
            var rulesSb = new StringBuilder();
            var precondDefSb = new StringBuilder();
            var precondMethods = new List<PreconditionMethod>();

            int rc = 0;
            foreach (var rewrite in rules)
            {
                var boundedIndices = new HashSet<string>();
                var boundedWidths = new HashSet<string>();
                var predicates = new Dictionary<string, Predicate>();

                rulesSb.Append($";; {rewrite.Name}:\n;; {rewrite.Before.ToString()} => {rewrite.After.ToString()}\n");
                rulesSb.Append($"(rule {rc} ");
                rc++;

                TranspileLhs(rewrite.Before, rulesSb, boundedIndices, boundedWidths, predicates);
                rulesSb.Append("\n");

                foreach (var (name, predicate) in predicates)
                    rulesSb.AppendLine($"(if-let _ (is_icmp_{predicate.ToString().ToLower()} {name}))");

                AppendPrecondition(rewrite, rulesSb, precondDefSb, precondMethods);

                rulesSb.Append("    ");
                TranspileRhs(rewrite.After, rulesSb, boundedIndices, boundedWidths);
                rulesSb.Append("\n)\n\n");
            }

            var precondMethodText = BuildPreconditionMethodText(precondMethods);
            var finalIsle = BuildFinalIsleText(precondDefSb, rulesSb);
            var repoRoot = GetSrcDir();

            UpdateRulesIsle(repoRoot, finalIsle);
            UpdateMacros(repoRoot, precondMethodText);
            RegenerateIsleRust(repoRoot);
        }

        private static void TranspileLhs(AstNode ast, StringBuilder sb, HashSet<string> boundedIndices, HashSet<string> boundedWidths, Dictionary<string, Predicate> predicates)
        {
            sb.Append("(lower ");
            TranspileLhsInternal(ast, sb, boundedIndices, boundedWidths, predicates);
            sb.Append(")");
        }

        private static void TranspileLhsInternal(AstNode ast, StringBuilder sb, HashSet<string> boundedIndices, HashSet<string> boundedWidths, Dictionary<string, Predicate> predicates)
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

            // ICmps have a special first argument
            if (ast is ICmpNode icmp)
            {
                var pred = icmp.Pred;
                var name = $"pred{predicates.Count}";
                sb.Append($"{name} ");
                predicates[name] = pred;
            }

            for (int i = 0; i < ast.Children.Count; i++)
            {
                var child = ast.Children[i];
                TranspileLhsInternal(child, sb, boundedIndices, boundedWidths, predicates);
                if (i != ast.Children.Count - 1)
                {
                    sb.Append(" ");
                }
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
            sb.Append($"({GetOperatorName(ast.Kind)} ");

            // ICmps have a special first argument
            if (ast is ICmpNode icmp)
            {
                var pred = icmp.Pred;
                sb.Append($"(Pred{pred.ToString()}) ");
            }

            for (int i = 0; i < ast.Children.Count; i++)
            {
                var child = ast.Children[i];
                TranspileRhsInternal(child, sb, boundedIndices, boundedWidths);
                if (i != ast.Children.Count - 1)
                    sb.Append(" ");
            }

            if (ast is ConstNode constNode)
            {
                var width_field = boundedWidths.Any() ? boundedWidths.First() : $"(GetWidth {boundedIndices.First()})";
                sb.Append($"{(ulong)constNode.Value} {width_field}");
            }

            else if (ast is VarNode varNode)
            {
                sb.Append($"{varNode.Name}");
            }

            sb.Append(")");
        }

        private PreconditionMethod LowerPreconditionMethod(string ruleName, AstNode precondition)
        {
            var constantNodes = DslPreprocessor.GetUniqueVariables(precondition);
            var args = String.Join(", ", constantNodes.Select(x => $"{x.Name}: AstIdx"));
            var methodName = $"{ruleName}_precondition";

            var sb = new StringBuilder();
            var codeBuilder = new CodeBuilder(sb);
            codeBuilder.AppendLine($"fn ${methodName}(&mut self, {args}) -> Option<Empty> {{");
            codeBuilder.Indent(2);

            codeBuilder.Append($"let precondition = ");

            LowerPreconditionNode(sb, precondition);
            codeBuilder.AppendNoIndent(";");
            codeBuilder.AppendLine("");

            codeBuilder.AppendLine($"if !precondition {{ return None; }}");
            codeBuilder.AppendLine("return Some(Empty());");
            codeBuilder.Outdent();
            codeBuilder.AppendLine("}");

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
                sb.Append("0x" + ((ulong)constNode.Value).ToString("X"));
                return;
            }

            if (precondition is IntrinsicCallNode intrinsicCall)
            {
                // Terrible hack: Prefix intrinsic call names with `isle_`, to avoid conflicts with the auto-generated egg code.
                sb.Append($"isle_{intrinsicCall.Name}(self, ");
                for (int i = 0; i < intrinsicCall.Children.Count; i++)
                {
                    LowerPreconditionNode(sb, intrinsicCall.Children[i]);
                    if (i != intrinsicCall.Children.Count - 1)
                        sb.Append(", ");
                }
                sb.Append(")");
                return;
            }

            switch (precondition.Kind)
            {
                case AstKind.Add:
                case AstKind.Mul:
                case AstKind.And:
                case AstKind.Or:
                case AstKind.Xor:
                case AstKind.Lshr:
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

        private static string GetSrcDir()
        {
            var cands = new[]
            {
                Directory.GetCurrentDirectory(),
                AppContext.BaseDirectory,
                Path.GetDirectoryName(typeof(IsleBackend).Assembly.Location),
            }
            .Where(path => !string.IsNullOrWhiteSpace(path))
            .Select(Path.GetFullPath)
            .Distinct(StringComparer.OrdinalIgnoreCase);

            foreach (var path in cands)
            {
                var srcDir = GetSrcDir(path);
                if (srcDir != null)
                    return srcDir;
            }

            throw new DirectoryNotFoundException("Could not locate the repository root containing EqSat/src/dsl and Mba.Simplifier/DSL.");
        }

        private static string? GetSrcDir(string path)
        {
            for (var current = new DirectoryInfo(path); current != null; current = current.Parent)
            {
                var repoRoot = current.FullName;
                if (!Directory.Exists(Path.Combine(repoRoot, "EqSat", "src", "dsl")))
                    continue;

                if (!Directory.Exists(Path.Combine(repoRoot, "Mba.Simplifier", "DSL")))
                    continue;

                return repoRoot;
            }

            return null;
        }

        private void AppendPrecondition(DslRule rewrite, StringBuilder rulesSb, StringBuilder precondDefSb, List<PreconditionMethod> precondMethods)
        {
            if (rewrite.Precondition == null)
                return;

            var name = EggBackend.GetSanitizedRewriteName(rewrite);
            var precond = LowerPreconditionMethod(name, rewrite.Precondition);

            rulesSb.AppendLine($"(if-let _ ({precond.MethodName} {String.Join(" ", precond.ArgNames)}))");
            precondDefSb.AppendLine($"(decl pure partial {precond.MethodName} ({String.Join(" ", precond.ArgNames.Select(x => "index"))}) empty)");
            precondDefSb.AppendLine($"(extern constructor {precond.MethodName} {precond.MethodName})");
            precondMethods.Add(precond);
        }

        private static string BuildPreconditionMethodText(IReadOnlyList<PreconditionMethod> precondMethods)
        {
            var precondMethodSb = new CodeBuilder();
            precondMethodSb.AppendLine("// Code generated by \"IsleBackend.cs\"; DO NOT EDIT.");
            precondMethodSb.AppendLine("#[macro_export]");
            precondMethodSb.AppendLine("macro_rules! isle_methods {");
            precondMethodSb.Indent();

            var identifiers = String.Join(", ", precondMethods.Select(x => $"${x.MethodName}:ident"));
            precondMethodSb.AppendLine($"({identifiers}) => {{");
            precondMethodSb.Indent();

            foreach (var method in precondMethods)
                precondMethodSb.AppendLines(method.Body);

            precondMethodSb.Outdent();
            precondMethodSb.AppendLine("};");
            precondMethodSb.Outdent();
            precondMethodSb.AppendLine("}");

            var macroCall = $"isle_methods!({String.Join(", ", precondMethods.Select(x => x.MethodName))})";
            var fmt = $"#[macro_export]\r\nmacro_rules! isle_defaults {{\r\n    () => {{\r\n            {macroCall};\r\n    }};\r\n}}\r\n\r\n";
            precondMethodSb.AppendLine(fmt);

            return precondMethodSb.ToString();
        }

        private static string BuildFinalIsleText(StringBuilder precondDefSb, StringBuilder rulesSb)
        {
            var finalIsle = new StringBuilder();
            finalIsle.AppendLine(precondDefSb.ToString());
            finalIsle.AppendLine(rulesSb.ToString());
            return finalIsle.ToString();
        }

        private static void UpdateRulesIsle(string repoRoot, string finalIsle)
        {
            var rulesIslePath = Path.Combine(repoRoot, "EqSat", "src", "dsl", "rules.isle");
            if (!File.Exists(rulesIslePath))
                return;

            var isleContent = File.ReadAllText(rulesIslePath);
            var beginIndex = isleContent.IndexOf(";;BEGIN", StringComparison.Ordinal);
            if (beginIndex == -1)
                return;

            var lineEnd = isleContent.IndexOf(Environment.NewLine, beginIndex, StringComparison.Ordinal);
            if (lineEnd == -1)
                return;

            var prefix = isleContent.Substring(0, lineEnd + Environment.NewLine.Length);
            var newIsleContent = prefix + Environment.NewLine + finalIsle;
            File.WriteAllText(rulesIslePath, newIsleContent);
        }

        private static void UpdateMacros(string repoRoot, string precondMethodText)
        {
            var macrosPath = Path.Combine(repoRoot, "EqSat", "src", "dsl", "isle_macros.rs");
            File.WriteAllText(macrosPath, precondMethodText);
        }

        private static void RegenerateIsleRust(string repoRoot)
        {
            var rulesIslePath = Path.Combine(repoRoot, "EqSat", "src", "dsl", "rules.isle");
            var isleRulesPath = Path.Combine(repoRoot, "EqSat", "src", "dsl", "isle_rules.rs");
            GenerateIsleRust("islec.exe", rulesIslePath, isleRulesPath);
        }

        public static void GenerateIsleRust(string islecPath, string inputPath, string outputPath)
        {
            var fullInputPath = Path.GetFullPath(inputPath);
            var fullOutputPath = Path.GetFullPath(outputPath);

            var startInfo = new ProcessStartInfo
            {
                FileName = islecPath,
                UseShellExecute = false,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                CreateNoWindow = true,
            };

            startInfo.ArgumentList.Add(fullInputPath);
            startInfo.ArgumentList.Add("-o");
            startInfo.ArgumentList.Add(fullOutputPath);

            using var process = Process.Start(startInfo) ?? throw new InvalidOperationException($"Failed to start {islecPath}.");
            var stdout = process.StandardOutput.ReadToEnd();
            var stderr = process.StandardError.ReadToEnd();
            process.WaitForExit();

            if (process.ExitCode != 0)
                throw new InvalidOperationException($"islec failed with exit code {process.ExitCode}.{Environment.NewLine}{stdout}{stderr}");

            var content = File.ReadAllText(fullOutputPath);
            content = NormalizeGeneratedIsleRust(content);
            File.WriteAllText(fullOutputPath, content);
        }

        // ISLE does not support generating matching code for array-style enums
        // We have to rewrite the matching code with a post processing step
        private static string NormalizeGeneratedIsleRust(string content)
        {
            var variants = new Dictionary<int, string[]>
            {
                [1] = new[] { "Neg" },
                [2] = new[] { "Add", "Mul", "Pow", "And", "Or", "Xor", "Lshr", "Zext", "Trunc", "Concat" },
                [3] = new[] { "Extract", "Carry" },
            };

            var fields = new[] { "a", "b", "c", "t" };

            foreach (var (arity, names) in variants)
            {
                var fieldPattern = string.Join(@"\s*,\s*", Enumerable.Range(0, arity).Select(index => $@"{fields[index]}:\s*(\w+)"));
                foreach (var name in names)
                {
                    var pattern = $@"SimpleAst::{name}\s*\{{\s*{fieldPattern},?\s*\}}";
                    var replacement = $"SimpleAst::{name}([{string.Join(", ", Enumerable.Range(1, arity).Select(index => $"${index}"))}])";
                    content = Regex.Replace(content, pattern, replacement, RegexOptions.Singleline);
                }
            }

            content = Regex.Replace(
                content,
                @"SimpleAst::ICmp\s*\{\s*a:\s*(ref\s+)?(\w+),\s*b:\s*(\w+),\s*c:\s*(\w+),?\s*\}",
                "SimpleAst::ICmp { predicate: $1$2, children: [$3, $4] }",
                RegexOptions.Singleline);

            content = Regex.Replace(
                content,
                @"SimpleAst::Select\s*\{\s*a:\s*(\w+),\s*b:\s*(\w+),\s*c:\s*(\w+),?\s*\}",
                "SimpleAst::Select { children: [$1, $2, $3] }",
                RegexOptions.Singleline);

            return content;
        }

        private static string GetOperatorName(AstKind kind)
        {
            return kind switch
            {
                AstKind.Pow => "Pow",
                AstKind.Add => "Add",
                AstKind.Mul => "Mul",
                AstKind.And => "And",
                AstKind.Or => "Or",
                AstKind.Xor => "Xor",
                AstKind.Neg => "Neg",
                AstKind.Lshr => "Lshr",
                AstKind.Const => "Constant",
                AstKind.ICmp => "ICmp",
                AstKind.Select => "Select",
                AstKind.Zext => "Zext",
                AstKind.Trunc => "Trunc",
                AstKind.WildCardConstant => "Constant",
                AstKind.Var => "Any",
                _ => throw new InvalidOperationException($"Unrecognized operator: {kind.ToString()}")
            };
        }
    }
}
