using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Interpreter;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Transactions;

namespace Mba.Simplifier.Fuzzing
{
    public class MSiMBAFuzzer
    {
        private readonly SeededRandom rand = new();

        private readonly AstCtx ctx = new();

        public static void Run()
        {
            var sharpPtr = JitUtils.AllocateExecutablePage(1000);
            var fuzzer = new MSiMBAFuzzer();
            var ctx = fuzzer.ctx;
            AstIdx.ctx = fuzzer.ctx;
            for (int i = 0; i < 1000000; i++)
            {
                // Simplify the expression using MSiMBA
                var fCase = fuzzer.GetFuzzCase();
                var result = LinearSimplifier.Run(ctx.GetWidth(fCase), fuzzer.ctx, fCase, false, true);
                Console.WriteLine($"{fuzzer.ctx.GetAstString(fCase)}\n=>\n{fuzzer.ctx.GetAstString(result)}\n    \n");

                // Skip if the expression simplifies to a constant
                var variables = ctx.CollectVariables(fCase);

                if (variables.Count == 0)
                    continue;

                // Verify that both expressions are equivalent. Fuzz both JITs by using the old/new jit for the input and result.
                bool multiBit = true;
                var numCombinations = (ulong)Math.Pow(2, variables.Count);
                var w = ctx.GetWidth(fCase);
                var vec1 = LinearSimplifier.JitResultVector(ctx, w, (ulong)ModuloReducer.GetMask(w), variables, fCase, multiBit, numCombinations);
                var vec2 = LinearSimplifier.JitResultVectorOld(ctx, w, (ulong)ModuloReducer.GetMask(w), variables, result, multiBit, numCombinations);
                if(!vec1.SequenceEqual(vec2))
                    throw new InvalidOperationException("Mismatch");
            }
        }

        // Expression can either be purely linear(with zext/trunc which is technically semi-linear), or classically semi-linear
        // Pick output expression size(e.g. 8, 16, 32, 64)
        // Pick N variables of random size
        // TODO: Truncation.. for now, assert that the variable sizes must be less than or equal to the size of the output expression
        private AstIdx GetFuzzCase()
        {
            // Clear the ast context
            ctx.Clear();

            // Pick the width of the output expression...
            int outputWidth = rand.Next(0, 4) switch
            {
                0 => 8,
                1 => 16,
                2 => 32,
                3 => 64,
            };

            // Pick between 2 and 5 variables of random sizes
            var numVars = rand.Next(2, 5);
            var variables = new List<AstIdx>();
            for (int i = 0; i < numVars; i++)
            {
                variables.Add(ctx.Symbol($"v{i}", (byte)ChooseVarWidth(outputWidth)));
            }

            // Chose between 2 and 5 terms
            //var termCount = rand.Next(2, 6);
            var termCount = 1;
            List<AstIdx> terms = new();
            for(int i = 0; i < termCount; i++)
            {
                var term = GetTerm(outputWidth, variables);
                terms.Add(term);
            }

            var result = ctx.Add(terms);
            return result;
        }

        // Choose an aligned width that is less than or equal to the size of the output register
        private int ChooseVarWidth(int outputWidth)
        {
            var choices = new int[] { 8, 16, 32, 64 };
            return choices[rand.Next(0, choices.Length)];
        }

        // Compute a random semi-linear bitwise term
        // We output booleans in algebraic form because it's more convenient to generate 
        private AstIdx GetTerm(int outputWidth, List<AstIdx> variables)
        {
            // Compute a list of variable conjunctions, e.g. [(a&b&c), (b&c), (a)]
            var conjCount = rand.GetRandUshort(1, 4);
            HashSet<ulong> conjMasks = new();
            for (int i = 0; i < conjCount; i++)
            {
                // Get a unique conjunction.
                while (true)
                {
                    var conj = GetRandConjMask(variables.Count);
                    if (conj == 0)
                        continue;
                    // Skip if we've already used this conjunction.
                    if (conjMasks.Contains(conj))
                        continue;

                    conjMasks.Add(conj);
                    break;
                }
            }

            // Build an AST for the variable conjunction, inserting zero extensions where necessary.
            List<AstIdx> conjs = new();
            foreach(var conjMask in conjMasks)
            {
                var minWidth = GetConjMinWidth(conjMask, variables);
                var extendedVars = variables.Select(x => ChangeWidth(x, ctx.GetWidth(x), minWidth)).ToList();
                var conj = LinearSimplifier.ConjunctionFromVarMask(ctx, extendedVars, 1, conjMask);
                conjs.Add(ChangeWidth(conj, ctx.GetWidth(conj), (uint)outputWidth));
            }

            // XOR all of the conjunctions together
            return ctx.Mul(ctx.Constant(rand.GetRandUlong(), (byte)outputWidth), ctx.Xor(conjs));
        }

        private AstIdx ChangeWidth(AstIdx idx, uint from, uint to)
        {
            if (from == to)
                return idx;
            if (from < to)
                return ctx.Zext(idx, (byte)to);
            else
                return ctx.Trunc(idx, (byte)to);
        }

        private ulong GetRandConjMask(int varCount)
        {
            return rand.GetRandUlong(0, (1ul << varCount));
        }

        private byte GetConjMinWidth(ulong conj, List<AstIdx> variables)
        {
            // Compute a minimal width that all variables must be extended to.
            byte minWidth = 0;
            for (ushort i = 0; i < variables.Count; i++)
            {
                // Skip if this variable is not demanded.
                if (((1ul << i) & conj) == 0)
                    continue;

                var w = ctx.GetWidth(variables[i]);
                if (w > minWidth)
                    minWidth = w;
            }

            return minWidth;
        }
    }
}
