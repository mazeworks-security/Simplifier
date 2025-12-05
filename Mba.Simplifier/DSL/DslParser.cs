using Mba.Ast;
using Mba.Parsing;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.DSL
{
    public record DslRule(string Name, AstNode Before, AstNode After);

    public static class DslParser
    {
        public static IReadOnlyList<DslRule> Parse(string fileContents)
        {
            var lines = fileContents.Split(Environment.NewLine);

            var rules = new List<DslRule>();
            foreach(var line in lines)
            {
                // Skip empty lines
                if (line.Length == 0 || line == Environment.NewLine)
                    continue;

                var split = line.Replace(" ", "").Split(new string[] { ":", "=>" }, StringSplitOptions.RemoveEmptyEntries);
                var name = split[0];

                Dictionary<string, VarNode> varNodes = new();
                var constNodes = new Dictionary<(ulong, uint), ConstNode>();
                Dictionary<string, WildCardConstantNode> wildCardConstantNodes = new();
                var before = AstParser.Parse(split[1], 64, varNodes, constNodes, wildCardConstantNodes);
                var after = AstParser.Parse(split[2], 64, varNodes, constNodes, wildCardConstantNodes);

                var rule = new DslRule(name, before, after);
                rules.Add(rule);
            }

            return rules;
        }
    }
}
