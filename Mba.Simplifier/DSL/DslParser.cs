using Mba.Ast;
using Mba.Common.Parsing;
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

    public record DslRuleOld(string Name, AstNode Before, AstNode After, bool ManualPrecondition);

    public static class DslParser
    {
        public static Dsl ParseDsl(string fileContents)
            => (Dsl)AstParser.ParseDsl(fileContents, 64, new (), new (), new ());


        public static IReadOnlyList<DslRuleOld> Parse(string fileContents)
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

            var rules = new List<DslRuleOld>();
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
                var before = AstParser.ParseDsl(split[1], 64, varNodes, constNodes, wildCardConstantNodes);
                var after = AstParser.ParseDsl(split[2], 64, varNodes, constNodes, wildCardConstantNodes);

                var rule = new DslRuleOld(name, before, after, precond);
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
