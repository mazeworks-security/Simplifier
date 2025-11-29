using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Interpreter;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Pipeline
{
    public class ProbableEquivalenceChecker
    {
        private readonly AstCtx ctx;

        private readonly List<AstIdx> variables;

        private readonly AstIdx before;

        private readonly AstIdx after;

        private readonly uint width;

        private readonly nint pagePtr1;

        private readonly nint pagePtr2;

        private ulong seed = ulong.MaxValue;

        private unsafe delegate* unmanaged[SuppressGCTransition]<ulong*, ulong> func1;

        private unsafe delegate* unmanaged[SuppressGCTransition]<ulong*, ulong> func2;

        public static bool ProbablyEquivalent(AstCtx ctx, AstIdx before, AstIdx after, bool slowHeuristics = true)
        {
            var pagePtr1 = JitUtils.AllocateExecutablePage(4096);
            var pagePtr2 = JitUtils.AllocateExecutablePage(4096);

            var allVars = ctx.CollectVariables(before).Concat(ctx.CollectVariables(after)).Distinct().OrderBy(x => ctx.GetSymbolName(x)).ToList();
            bool probablyEquivalent = new ProbableEquivalenceChecker(ctx, allVars, before, after, pagePtr1, pagePtr2).ProbablyEquivalent(false);

            JitUtils.FreeExecutablePage(pagePtr1);
            JitUtils.FreeExecutablePage(pagePtr2);
            return probablyEquivalent;
        }

        public ProbableEquivalenceChecker(AstCtx ctx, List<AstIdx> variables, AstIdx before, AstIdx after, nint pagePtr1, nint pagePtr2)
        {
            this.ctx = ctx;
            // this.variables = variables;
            this.variables = ctx.CollectVariables(before).Concat(ctx.CollectVariables(after)).Distinct().OrderBy(x => ctx.GetSymbolName(x)).ToList();
            this.before = before;
            this.after = after;
            this.pagePtr1 = pagePtr1;
            this.pagePtr2 = pagePtr2;
        }

        public unsafe bool ProbablyEquivalent(bool slowHeuristics = false)
        {
            //var jit1 = new Amd64OptimizingJit(ctx);
            //jit1.Compile(before, variables, pagePtr1, false);
            var w = ctx.GetWidth(before);
            ctx.Compile(before, ModuloReducer.GetMask(w), variables.ToArray(), pagePtr1);
            func1 = (delegate* unmanaged[SuppressGCTransition]<ulong*, ulong>)pagePtr1;

            //var jit2 = new Amd64OptimizingJit(ctx);
            //jit2.Compile(after, variables, pagePtr2, false);
            ctx.Compile(after, ModuloReducer.GetMask(w), variables.ToArray(), pagePtr2);
            func2 = (delegate* unmanaged[SuppressGCTransition]<ulong*, ulong>)pagePtr2;

            var vArray = stackalloc ulong[variables.Count];
            if (!RandomlyEquivalent(vArray, 1000))
                return false;

            ulong half1 = 0x5555555555555555;

            ulong m1 = 0xAAAAAAAAAAAAAAA;
            ulong m1Neg = 0xCCCCCCCCCCCCCCC;

            ulong m2 = 0xAAAAAAAAAAAAAAA;
            ulong m2Neg = 0xCCCCCCCCCCCCCCC;

            if (!SignatureVectorEquivalent(vArray, 0, ulong.MaxValue))
                return false;

            //return true;

            // Too slow
            if (slowHeuristics)
            {
                bool allBits = variables.Count <= 6;

                if (!AllCombs(vArray, 0x5555555555555555ul, ~0x5555555555555555ul, allBits))
                    return false;
                if (!AllCombs(vArray, 0x5555555555555555, 0xAAAAAAAAAAAAAAA, allBits))
                    return false;
                if (!AllCombs(vArray, 0x5555555555555555, 0xCCCCCCCCCCCCCCC, allBits))
                    return false;
                if (!AllCombs(vArray, 0xAAAAAAAAAAAAAAA, 0xCCCCCCCCCCCCCCC, allBits))
                    return false;
            }

            if (!RandomlyEquivalent(vArray, 1000))
                return false;
            return true;
        }

        private unsafe bool RandomlyEquivalent(ulong* vArray, int numGuesses)
        {
            int varCount = variables.Count;
            for(int _ = 0; _ < numGuesses; _++)
            {
                for (int i = 0; i < varCount; i++)
                {
                    var next = Next();
                    vArray[i] = next;
                }

                var op1 = func1(vArray);
                var op2 = func2(vArray);

                if (op1 != op2)
                    return false;
            }

            return true;
        }

        private unsafe bool AllCombs(ulong* vArray, ulong a, ulong b, bool allBits)
        {
            if (!SignatureVectorEquivalent(vArray, 0, a, allBits))
                return false;
            if (!SignatureVectorEquivalent(vArray, 0, b, allBits))
                return false;
            if (!SignatureVectorEquivalent(vArray, a, b, allBits))
                return false;
            if (!SignatureVectorEquivalent(vArray, b, a, allBits))
                return false;

            return true;
        }

        private unsafe bool SignatureVectorEquivalent(ulong* vArray, ulong zeroes, ulong ones, bool allBits = true)
        {
            var numCombinations = (ulong)Math.Pow(2, variables.Count);
            ushort numBitIterations = allBits ? (ushort)1 : (ushort)64;
            for (ushort bitIndex = 0; bitIndex < numBitIterations; bitIndex++)
            {
                for(ulong i = 0; i < numCombinations; i++)
                {
                    // Set the value to zeroes or ones
                    for(int vIdx = 0; vIdx < variables.Count; vIdx++)
                    {
                        var value = ((i >> (ushort)vIdx) & 1) == 0 ? 0 : ones;
                        value >>= bitIndex;
                        vArray[vIdx] = value;
                    }

                    var op1 = func1(vArray);
                    var op2 = func2(vArray);
                    if (op1 != op2)
                        return false;
                }
            }

            return true;
        }

        private ulong Next()
        {
            ulong z = (seed += (ulong)(0x9E3779B97F4A7C15));
            z = (z ^ (z >> 30)) * (ulong)(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)) * (ulong)(0x94D049BB133111EB);
            return z ^ (z >> 31);
        }

        public static void ProbablyEquivalentZ3(AstCtx ctx, AstIdx before, AstIdx after)
        {
            using (var z3Ctx = new Context())
            {
                var translator = new Z3Translator(ctx, z3Ctx);
                var beforeZ3 = translator.Translate(before);
                var afterZ3 = translator.Translate(after);
                var solver = z3Ctx.MkSolver("QF_BV");

                // Set the maximum timeout to 10 seconds.
                var p = z3Ctx.MkParams();
                uint solverLimit = 5000;
                p.Add("timeout", solverLimit);
                solver.Parameters = p;

                Console.WriteLine("Proving equivalence...\n");
                solver.Add(z3Ctx.MkNot(z3Ctx.MkEq(beforeZ3, afterZ3)));
                var check = solver.Check();

                var printModel = (Model model) =>
                {
                    var values = model.Consts.Select(x => $"{x.Key.Name} = {(long)ulong.Parse(model.Eval(x.Value).ToString())}");
                    return $"[{String.Join(", ", values)}]";
                };

                if (check == Status.UNSATISFIABLE)
                    Console.WriteLine("Expressions are equivalent.");
                else if (check == Status.SATISFIABLE)
                    Console.WriteLine($"Expressions are not equivalent. Counterexample:\n{printModel(solver.Model)}");
                else
                    Console.WriteLine($"Solver timed out - expressions are probably equivalent. Could not find counterexample within {solverLimit}ms");
                
            }
        }

    }
}
