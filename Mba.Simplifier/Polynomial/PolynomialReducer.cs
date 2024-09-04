using Iced.Intel;
using Mba.Simplifier.Polynomial;
using Mba.Utility;
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;
using Wintellect.PowerCollections;

namespace Mba.Testing.PolyTesting
{
    public struct MonomialWithCoeff
    {
        public readonly Monomial monomial;

        public readonly ulong coeff;

        public MonomialWithCoeff(Monomial m, ulong c)
        {
            monomial = m;
            coeff = c;
        }
    }

    /// <summary>
    /// This class implements the multivariate polynomial reduction algorithm from the NDSS2024 paper
    /// "Efficient Normalized Reduction and Generation of Equivalent Multivariate Binary Polynomials".
    /// </summary>
    public static class PolynomialReducer
    {
        // Map each monomial to it's expanded factorial basis representation.
        public static ConcurrentDictionary<Monomial, IReadOnlyList<MonomialWithCoeff>> factorialMap = new();

        public static SparsePolynomial Reduce(SparsePolynomial input)
        {
            var fac = GetFactorialForm(input);
            ReduceFacBasisPolynomial(fac);
            return GetCanonicalForm(fac);
        }

        // Given a polynomial, compute a version of the polynomial with a factorial basis.
        // Note that this mutates the input polynomial and returns a separate object.
        // This is a naive implementation, and could be significantly optimized.
        public static SparsePolynomial GetFactorialForm(SparsePolynomial input)
        {
            // Note that `OrderedBag` is used to ensure that monomials are stored in sorted(graded reverse lexicographic) order,
            // and that ordering is preserved when removing or inserting elements.
            var worklist = new OrderedBag<Monomial>(input.GetOrderedMonomials());
            var outPoly = new SparsePolynomial(input.numVars, input.width);
            while (worklist.Any())
            {
                // Get the last monomial
                var monom = worklist.RemoveLast();

                // Skip zero terms
                var coeff = input.GetCoeff(monom);
                if (coeff == 0)
                    continue;
                var degrees = monom.Degrees;
                if (degrees.Count == 0)
                    continue;

                // Get the factorial basis for this monomial
                if(!factorialMap.TryGetValue(monom, out var expandedForm))
                {
                    expandedForm = GetSortedTerms(GetFactorialBasis(monom, 64));
                    factorialMap[monom] = expandedForm;
                }
                
                // Move the highest(current) degree term over to the new polynomial,
                // then subtract the input polynomial by the lower degree parts.
                var terms = expandedForm;
                for (int i = 0; i < terms.Count - 1; i++)
                {
                    // Negate and reduce(modulo the current bit width) the coefficient
                    var withCoeff = terms[i];
                    var termMonomial = withCoeff.monomial;
                    var termCoefficient = withCoeff.coeff;
                    termCoefficient &= input.moduloMask;
                    termCoefficient *= coeff;

                    // Subtract the monomial's coefficient from the input polynomial.
                    var negatedCoeff = (input.moduloMask * termCoefficient);
                    var contains = input.Sum(termMonomial, negatedCoeff);

                    // If this monomial was not contained in the input polynomial, we need to add it to the worklist.
                    if(!contains)
                    {
                        if (!worklist.Contains(termMonomial))
                            worklist.Add(termMonomial);
                    }
                }

                // Remove this term from the input polynomial
                input.SetCoeff(monom, 0);

                // Update the new polynomial
                ulong originalCoeff = 0;
                outPoly.TryGetCoeff(monom, out originalCoeff);
                originalCoeff += coeff;
                outPoly.SetCoeff(monom, originalCoeff);
            }

            Debug.Assert(input.coeffs.All(x => x.Value == 0));
            return outPoly;
        }

        public static IReadOnlyList<MonomialWithCoeff> GetSortedTerms(SparsePolynomial s)
        {
            return s.GetOrderedMonomials().Select(x => new MonomialWithCoeff(x, s.GetCoeff(x))).ToList(); ;
        }

        private static SparsePolynomial GetFactorialBasis(Monomial monomial, byte width)
        {
            // For each variable(of some degree) in the monomial, compute the expanded factorial basis,
            // then multiply with all other factorial bases.
            DensePolynomial mergedFactorial = null;
            foreach (var deg in monomial.Degrees)
            {
                DensePolynomial currFactorial = null;
                // For the degree zero case, construct a monomial with the constant value `1`.
                if (deg == 0)
                {
                    currFactorial = new DensePolynomial(width, new int[] { 1 });
                    currFactorial.SetCoeff(0, 1);
                }

                else
                {
                    currFactorial = PolynomialReducer.GetDenseExpandedFactorial(deg, width, true);
                }

                // Then multiply the factorial basis with the other factorial bases.
                if (mergedFactorial == null)
                    mergedFactorial = currFactorial;
                else
                    mergedFactorial = PolynomialReducer.Multiply(mergedFactorial, currFactorial);
            }

            // Convert the dense representation to a sparse representation.
            var result = new SparsePolynomial(mergedFactorial.NumVars, width);
            for(int i = 0; i < mergedFactorial.coeffs.Length; i++)
            {
                var monom = mergedFactorial.GetMonomial(i);
                var coeff = mergedFactorial.coeffs[i];
                if (coeff == 0)
                    continue;

                result.SetCoeff(monom, coeff);
            }

            return result;
        }

        public static DensePolynomial GetDenseExpandedFactorial(byte degree, byte width, bool falling)
        {
            var densePoly = new DensePolynomial(width, new int[] { degree });
            GetExpandedFactorial(densePoly.coeffs, degree, width, falling);
            return densePoly;
        }

        public static ulong[] GetExpandedFactorial(byte degree, byte width, bool falling)
        {
            var terms = new ulong[degree + 1];
            return GetExpandedFactorial(terms, degree, width, falling);
        }

        public static ulong[] GetExpandedFactorial(ulong[] terms, byte degree, byte width, bool falling)
        {
            var moduloMask = (ulong)ModuloReducer.GetMask(width);
            var clone = new ulong[degree + 1];
            Debug.Assert(terms.Length == clone.Length);

            terms[0] = 1;
            terms[1] = 1;
            for (byte degIdx = 1; degIdx < degree + 1; degIdx++)
            {
                ulong coeff = ((ulong)degIdx - 1ul);
                if (falling)
                    coeff *= moduloMask;
                coeff &= moduloMask;

                for (byte i = 0; i < degIdx; i++)
                {
                    clone[i] = terms[i];
                    terms[i] = 0;
                }

                // Move the leading X over
                for (byte i = 0; i < Math.Min(terms.Length - 1, degIdx + 1); i++)
                    terms[i + 1] = clone[i];
                // Move the coefficient over
                for (byte i = 0; i < degIdx; i++)
                    terms[i] += (coeff * clone[i]);
            }

            for (byte i = 0; i < terms.Length; i++)
                terms[i] &= moduloMask;

            return terms;
        }

        // Multiply two dense polynomials, yielding a new polynomial.
        // Note that this assumes disjoint variable sets.
        public static DensePolynomial Multiply(DensePolynomial a, DensePolynomial b)
        {
            var newDimensions = a.dimensions.Concat(new int[] { b.dimensions.Single() }).ToArray();
            var newPoly = new DensePolynomial(a.width, newDimensions);
            for(int aIdx = 0; aIdx < a.coeffs.Length; aIdx++)
            {
                var monomA = a.GetMonomial(aIdx);
                var coeffA = a.GetCoeff(monomA);
                if (coeffA == 0)
                    continue;

                for(int bIdx = 0; bIdx < b.coeffs.Length; bIdx++)
                {
                    var monomB = b.GetMonomial(bIdx);
                    var coeffB = b.GetCoeff(monomB);
                    if (coeffB == 0)
                        continue;

                    var newCoeff = coeffA * coeffB;
                    newCoeff &= a.moduloMask;

                    var degrees = new byte[newPoly.NumVars];
                    for(int i = 0; i < a.NumVars; i++)
                        degrees[i] = monomA.GetVarDeg(i);
                    degrees[a.NumVars] = monomB.GetVarDeg(0);

                    var newMonom = new Monomial(degrees);
                    newPoly.Sum(newMonom, newCoeff);
                }
            }

            return newPoly;
        }

        // Reduce a factorial basis polynomial
        public static void ReduceFacBasisPolynomial(SparsePolynomial poly)
        {
            foreach(var (monom, coeff) in poly.coeffs.ToList())
            {
                if (coeff == 0)
                    continue;

                var mask = GetReductionMask(poly.width, monom);
                var newCoeff = coeff & mask;
                if (newCoeff == coeff)
                    continue;

                poly.SetCoeff(monom, newCoeff);
            }
        }

        public static ulong GetReductionMask(byte bitWidth, Monomial monom)
        {
            var moduloMask = (ulong)ModuloReducer.GetMask(bitWidth);

            var getFac = (ulong i) =>
            {
                // Get the factorial of this number.
                var fact = Factorial(i);

                // Get the greatest power of two that divides this number.
                var highest = HighestPowerOfTwo(fact);

                // Count the number of trailing zeroes to 
                var idx = BitOperations.TrailingZeroCount(highest);
                return (highest, idx);
            };

            uint diff = 0;
            var degrees = monom.Degrees;
            for(int i = 0; i < degrees.Count; i++)
            {
                var deg = degrees[i];
                var (h1, idx1) = getFac((ulong)deg);
                diff += (uint)idx1;
            }
            
            var width = (diff == 0) ? bitWidth : bitWidth - diff;
            if (diff > bitWidth)
                width = 0;
            var modulus = (ulong)ModuloReducer.GetMask((uint)width);
            return modulus;
        }

        public static ulong Factorial(ulong a)
        {
            ulong fact = 1;
            for (ulong x = 1; x <= a; x++)
                fact *= x;
            return fact;
        }

        public static ulong HighestPowerOfTwo(ulong n)
        {
            return (n & (~(n - 1)));
        }

        // Convert a factorial basis polynomial to canonical basis.
        public static SparsePolynomial GetCanonicalForm(SparsePolynomial input)
        {
            var output = new SparsePolynomial(input.numVars, input.width);
            foreach (var (monom, coeff) in input.coeffs)
            {
                if (coeff == 0)
                    continue;

                var degrees = monom.Degrees;
                if (degrees.Count == 0)
                    throw new InvalidOperationException("TODO: Handle constant terms");

                var expanded = GetFactorialBasis(monom, input.width);
                expanded.Multiply(coeff);
                foreach (var (m, c) in expanded.coeffs)
                {
                    if (c == 0)
                        continue;

                    output.Sum(m, c);
                }
            }

            return output;
        }
    }
}
