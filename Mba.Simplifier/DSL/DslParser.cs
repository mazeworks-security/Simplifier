using Mba.Ast;
using Mba.Parsing;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.DSL
{
    public enum DslType
    {
        Bool,
        U8,
        U64,
        Node,
    }

    public record DslFunctionArgument(string Name, DslType Type);

    public record DslFunction(bool IsBuiltin, string Name, IReadOnlyList<DslFunctionArgument> Arguments, DslType ReturnType, AstNode Body);

    public record DslRule(string Name, AstNode Before, AstNode After, bool ManualPrecondition);

    public static class DslParser
    {
        public static IReadOnlyList<DslRule> Parse(string fileContents)
        {
            var lines = fileContents.Split(Environment.NewLine);
            foreach(var line in lines)
            {
                var idx = line.IndexOf(":");
                if (idx == -1)
                {
                    Console.WriteLine(line);
                    continue;
                }

                var name = line.Substring(0, idx).Replace("-", "_");
                var other = line.Substring(idx);
                Console.WriteLine(name + other);
            }

            var rules = new List<DslRule>();
            foreach(var curr in lines)
            {
                var line = WithoutComments(curr);

                // Skip empty lines
                if (line.Length == 0 || line == Environment.NewLine)
                    continue;

                bool precond = line.Contains("::");
                var split = line.Split(new string[] { ";", "=>", "::" }, StringSplitOptions.RemoveEmptyEntries);
                var name = split[0];

                Dictionary<string, VarNode> varNodes = new();
                var constNodes = new Dictionary<(ulong, uint), ConstNode>();
                Dictionary<string, WildCardConstantNode> wildCardConstantNodes = new();
                var before = AstParser.Parse(split[1], 64, varNodes, constNodes, wildCardConstantNodes);
                var after = AstParser.Parse(split[2], 64, varNodes, constNodes, wildCardConstantNodes);

                var rule = new DslRule(name, before, after, precond);
                rules.Add(rule);
            }

            return rules;
        }

        private static string WithoutComments(string input)
        {
            var index = input.IndexOf("//");
            return index == -1 ? input : input.Substring(0, index);
        }
    }
}
