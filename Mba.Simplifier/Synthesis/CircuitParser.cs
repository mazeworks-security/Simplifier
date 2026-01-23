using Antlr4.Runtime;
using Mba.Common.Parsing;
using Mba.Parsing;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Synthesis
{
    // Verilog parser
    public static class CircuitParser
    {
        public static void Parse(AstCtx ctx, string text)
        {
            // Parse the expression AST.
            var charStream = new AntlrInputStream(text);
            var lexer = new VerilogLexer(charStream);
            var tokenStream = new CommonTokenStream(lexer);
            var parser = new VerilogParser(tokenStream);
            parser.BuildParseTree = true;
            var expr = parser.sourceText();

            // Throw if ANTLR has any errors.
            var errCount = parser.NumberOfSyntaxErrors;
            if (errCount > 0)
                throw new InvalidOperationException($"Parsing ast failed. Encountered {errCount} errors.");

            // Process the parse tree into a usable AST node.
            var visitor = new VerilogTranslationVisitor(ctx);
            var result = visitor.Visit(expr);

            var outBits = visitor.outputs.Values.Single().Select(x => x.Value).ToList();
            for (int i = 0; i < outBits.Count; i++) 
            {
                if (i != 2)
                    continue;
                var output = outBits[i];
                var w = ctx.GetWidth(output);

                var shiftBy = (ulong)Math.Pow(2, i);
                output = ctx.Mul(ctx.Constant(shiftBy, w), output);

                Console.WriteLine(ctx.GetAstString(output));

                /*
                var simpl = LinearSimplifier.Run(w, ctx, output, multiBit: true);

                var symbols = ctx.CollectVariables(output);
                var valueMap = new Dictionary<AstIdx, ulong>();

                valueMap[symbols[0]] = 2;
                valueMap[symbols[1]] = 2;

                var before = SimpleAstEvaluator.Evaluate(ctx, output, valueMap);
                var after = SimpleAstEvaluator.Evaluate(ctx, simpl, valueMap);
                Console.WriteLine($"{before} => {after}");

                Console.WriteLine(ctx.GetAstString(simpl));
                */
            }

 

            Debugger.Break();
        }
    }
}
