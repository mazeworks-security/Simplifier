using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Testing;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;
using ApInt = System.UInt64;

namespace Mba.Simplifier.Pipeline
{
    /// <summary>
    /// Class for simplifying polynomial MBA expressions. 
    /// This works for arbitrary variable counts, up to degree 2.
    /// </summary>
    /// TODO: Extend to higher degrees.
    public class MixedPolynomialSimplifier
    {
        private readonly AstCtx ctx;

        private readonly uint bitSize;

        private readonly IReadOnlyList<AstIdx> polynomials;

        private ApInt numCombinations;

        private readonly ApInt moduloMask;

        private readonly List<int> groupSizes;

        IReadOnlyList<AstIdx> allVars;

        public static AstIdx Simplify(AstCtx ctx, uint bitSize, IReadOnlyList<AstIdx> polyTerms)
            => new MixedPolynomialSimplifier(ctx, bitSize, polyTerms).Simplify();

        private MixedPolynomialSimplifier(AstCtx ctx, uint bitSize, IReadOnlyList<AstIdx> polyTerms)
        {
            this.ctx = ctx;
            this.bitSize = bitSize;
            polynomials = polyTerms;
            moduloMask = (ulong)ModuloReducer.GetMask(bitSize);

            // Union all of the variables.
            allVars = polynomials.SelectMany(x => ctx.CollectVariables(x)).ToHashSet().OrderBy(x => ctx.GetSymbolName(x)).ToList().AsReadOnly();
            numCombinations = (ApInt)Math.Pow(2, allVars.Count);
            groupSizes = LinearSimplifier.GetGroupSizes(allVars.Count);
        }

        private AstIdx Simplify()
        {
            // Get all possible conjunctions of variables.
            var variableCombinations = LinearSimplifier.GetVariableCombinations(allVars.Count);

            // Keep track of which variables are demanded by which combination,
            // as well as which result vector idx corresponds to which combination.
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var myMask = variableCombinations[i];
                var myIndex = LinearSimplifier.GetGroupSizeIndex(groupSizes, myMask);
                combToMaskAndIdx.Add((myMask, (int)myIndex));
            }

            // Combine all of the polynomials into a single result vector.
            var polynomialResultVector = new ulong[numCombinations * numCombinations];
            foreach (var poly in polynomials)
                AddPolyToResultVector(poly, variableCombinations, combToMaskAndIdx, polynomialResultVector);

            // Convert the vector back into a (possibly simpler) polynomial.
            return GetPolynomialFromVector(polynomialResultVector);
        }

        private void AddPolyToResultVector(AstIdx poly, ApInt[] variableCombinations, List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx, ulong[] combinedResultVector)
        {
            // Given a polynomial, collect all terms being multiplied together.
            List<AstIdx> terms = new();
            SplitIntoTermsByOpcode(AstOp.Mul, ctx, poly, terms);
            if (terms.Count != 2)
                throw new InvalidOperationException();

            // Given a polynomial in the form of (a*b), construct a result vector for both a and b individually.
            var resultVectors = terms.Select(x => LinearSimplifier.JitResultVector(ctx, bitSize, moduloMask, allVars, x, false, numCombinations)).ToList();

            // Take the result vectors for a and b, and convert them into a result vector using the basis of all possible conjunctions(see SiMBA paper).
            var anfVector = new List<ulong[]>();
            for (int i = 0; i < resultVectors.Count; i++)
            {
                var outAnfVector = new ulong[(int)numCombinations];
                GetAnfVector(bitSize, allVars, variableCombinations, combToMaskAndIdx, resultVectors[i], outAnfVector);
                anfVector.Add(outAnfVector);
            }

            // Multiply the two result vectors together to get the combined result vector.
            // Sum the combined vector with the existing vector.
            int combinedIndex = 0;
            for (int a = 0; a < (int)numCombinations; a++)
            {
                for (int b = 0; b < (int)numCombinations; b++)
                {
                    var aVal = anfVector[0][a];
                    var bVal = anfVector[1][b];
                    var combined = moduloMask & aVal * bVal;
                    combinedResultVector[combinedIndex] = moduloMask & combinedResultVector[combinedIndex] + combined;
                    combinedIndex++;
                }
            }
        }

        public static void SplitIntoTermsByOpcode(AstOp op, AstCtx ctx, AstIdx expr, List<AstIdx> terms)
        {
            var opcode = ctx.GetOpcode(expr);
            if (opcode == op)
            {
                var op1 = ctx.GetOp0(expr);
                var op2 = ctx.GetOp1(expr);
                if (ctx.GetOpcode(op1) == op)
                {
                    SplitIntoTerms(ctx, op1, terms);
                }

                else
                {
                    terms.Add(op1);
                }

                if (ctx.GetOpcode(op2) == op)
                {
                    SplitIntoTerms(ctx, op2, terms);
                }

                else
                {
                    terms.Add(op2);
                }
            }

            else
            {
                terms.Add(expr);
            }
        }


        private static void SplitIntoTerms(AstCtx ctx, AstIdx expr, List<AstIdx> terms)
        {
            SplitIntoTermsByOpcode(AstOp.Add, ctx, expr, terms);
        }

        public static void GetAnfVector(uint bitSize, IReadOnlyList<AstIdx> allVars, ApInt[] variableCombinations, List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx, ApInt[] resultVector, ulong[] outAnfVector)
        {
            var moduloMask = (ulong)ModuloReducer.GetMask(bitSize);
            var constantOffset = resultVector[0];
            for (int i = 1; i < resultVector.Length; i++)
                resultVector[i] = moduloMask & resultVector[i] - constantOffset;

            bool allZeroes = true;
            var varCount = allVars.Count;
            bool onlyOneVar = varCount == 1;
            int width = (int)(varCount == 1 ? 1 : 2u << (ushort)(varCount - 1));
            bool multiBit = false;

            outAnfVector[0] = constantOffset;

            unsafe
            {
                fixed (ApInt* ptr = &resultVector[0])
                {
                    for (ushort bitIndex = 0; bitIndex < LinearSimplifier.GetNumBitIterations(multiBit, bitSize); bitIndex++)
                    {
                        // If multi-bit simba is enabled, we need to take our base expression
                        // and isolate only the bit at the current bit index.
                        var maskForIndex = multiBit ? (ApInt)1 << bitIndex : moduloMask;
                        // Offset the result vector index such that we are fetching entries for the current bit index.
                        //var offset = bitIndex * numCombinations;
                        var offset = bitIndex * variableCombinations.Length;
                        for (int i = 0; i < variableCombinations.Length; i++)
                        {
                            // Fetch the result vector index for this conjunction.
                            // If the coefficient is zero, we can skip it.
                            var comb = variableCombinations[i];
                            var (trueMask, index) = combToMaskAndIdx[i];
                            var coeff = ptr[(int)offset + index];
                            if (coeff == 0)
                                continue;

                            // Subtract the coefficient from the result vector.
                            allZeroes = false;
                            MultibitSiMBA.SubtractCoeff(moduloMask, ptr, bitIndex, coeff, index, width, varCount, onlyOneVar, trueMask);

                            // Add an entry to the linear combination list.
                            outAnfVector[i + 1] = coeff;
                        }
                    }
                }
            }
        }

        // Convert the polynomial result vector back into a polynomial
        private AstIdx GetPolynomialFromVector(ulong[] polynomialResultVector)
        {
            var constantOffset = polynomialResultVector[0];
            polynomialResultVector[0] = 0;

            // Isolate and simplify the linear part of the polynomial.
            AstIdx? polynomial = GetLinearPart(polynomialResultVector);
            if (polynomial != null)
                polynomial = LinearSimplifier.Run(bitSize, ctx, polynomial.Value, false, false, false, allVars);

            // Now we need to perform factoring in hopes of finding a simpler result.
            while (true)
            {
                // Calculate the number of instances for each basis.
                var basisCounts = GetBasisCounts(polynomialResultVector, out var anyNonZero);
                if (!anyNonZero)
                    break;

                // Walk through the vector, pick out the most common term.
                var (commonBasis, commonCount) = GetMostCommonBasis(basisCounts);
                var conj = LinearSimplifier.ConjunctionFromVarMask(ctx, allVars, 1, commonBasis);

                AstIdx? sum = null;
                int combinedIdx = 0;
                for (int a = 0; a < (int)numCombinations; a++)
                {
                    for (int b = 0; b < (int)numCombinations; b++)
                    {
                        var coeff = polynomialResultVector[combinedIdx];
                        if (coeff == 0)
                        {
                            combinedIdx++;
                            continue;
                        }

                        // If we found the basis:
                        if ((ApInt)a == commonBasis)
                        {
                            var otherBasis = LinearSimplifier.ConjunctionFromVarMask(ctx, allVars, coeff, (ApInt)b);
                            if (sum == null)
                                sum = otherBasis;
                            else
                                sum = ctx.Add(sum.Value, otherBasis);

                            polynomialResultVector[combinedIdx] = 0;
                        }

                        else if ((ApInt)b == commonBasis)
                        {
                            var otherBasis = LinearSimplifier.ConjunctionFromVarMask(ctx, allVars, coeff, (ApInt)a);
                            if (sum == null)
                                sum = otherBasis;
                            else
                                sum = ctx.Add(sum.Value, otherBasis);

                            polynomialResultVector[combinedIdx] = 0;
                        }

                        combinedIdx++;
                    }
                }

                // Process the linear part with SiMBA.
                sum = LinearSimplifier.Run(bitSize, ctx, sum.Value);

                // Multiply the linear part by the basis.
                sum = ctx.Mul(conj, sum.Value);

                if (polynomial == null)
                    polynomial = sum;
                else
                    polynomial = ctx.Add(polynomial.Value, sum.Value);
            }

            if (constantOffset != 0)
                polynomial = ctx.Add(ctx.Constant(constantOffset, bitSize), polynomial.Value);

            // If the polynomial was null then this is just a zero MBA.
            if (polynomial == null)
                polynomial = ctx.Constant(0, bitSize);

            return polynomial.Value;
        }

        private AstIdx? GetLinearPart(ulong[] polynomialResultVector)
        {
            int combinedIdx = 0;

            AstIdx? sum = null;

            combinedIdx = 0;
            for (int a = 0; a < (int)numCombinations; a++)
            {
                for (int b = 0; b < (int)numCombinations; b++)
                {
                    var coeff = polynomialResultVector[combinedIdx];
                    if (coeff == 0)
                    {
                        combinedIdx++;
                        continue;
                    }

                    if (BitOperations.PopCount((uint)a) == 0)
                    {
                        var term = LinearSimplifier.ConjunctionFromVarMask(ctx, allVars, coeff, (ApInt)b);
                        if (sum == null)
                            sum = term;
                        else
                            sum = ctx.Add(sum.Value, term);

                        polynomialResultVector[combinedIdx] = 0;
                    }

                    else if (BitOperations.PopCount((uint)b) == 0)
                    {
                        var term = LinearSimplifier.ConjunctionFromVarMask(ctx, allVars, coeff, (ApInt)a);
                        if (sum == null)
                            sum = term;
                        else
                            sum = ctx.Add(sum.Value, term);

                        polynomialResultVector[combinedIdx] = 0;
                    }

                    combinedIdx++;
                }
            }

            return sum;
        }

        private ApInt[] GetBasisCounts(ulong[] polynomialResultVector, out bool anyNonZero)
        {
            // First identify the most common basis expression.
            var basisCounts = new ulong[numCombinations];
            int combinedIdx = 0;
            anyNonZero = false;
            for (int a = 0; a < (int)numCombinations; a++)
            {
                for (int b = 0; b < (int)numCombinations; b++)
                {
                    var coeff = polynomialResultVector[combinedIdx];
                    if (coeff == 0)
                    {
                        combinedIdx++;
                        continue;
                    }

                    // At this point we know that each vector entry has two basis expression.
                    anyNonZero = true;
                    basisCounts[a]++;
                    basisCounts[b]++;
                    combinedIdx++;
                }
            }

            return basisCounts;
        }

        private (ApInt basis, ApInt count) GetMostCommonBasis(ApInt[] basisCounts)
        {
            ApInt mostCommonBasis = 0;
            ApInt mostCommonCount = 0;

            for (int i = 0; i < basisCounts.Length; i++)
            {
                var basis = (ApInt)i;
                var count = basisCounts[i];
                if (count > mostCommonCount)
                {
                    mostCommonBasis = basis;
                    mostCommonCount = count;
                }
            }

            return (mostCommonBasis, mostCommonCount);
        }
    }
}
