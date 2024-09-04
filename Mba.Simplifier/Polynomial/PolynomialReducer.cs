using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;
using Wintellect.PowerCollections;

namespace Mba.Testing.PolyTesting
{
    /// <summary>
    /// This class implements the multivariate polynomial reduction algorithm from the NDSS2024 paper
    /// "Efficient Normalized Reduction and Generation of Equivalent Multivariate Binary Polynomials".
    /// </summary>
    public static class PolynomialReducer
    {
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
            var bag = new OrderedBag<Monomial>(input.GetOrderedMonomials());

            var outPoly = new SparsePolynomial(input.numVars, input.width);
            while (bag.Any())
            {
                // Get the last monomial
                var monom = bag.RemoveLast();

                // Skip zero terms
                var coeff = input.GetCoeff(monom);
                if (coeff == 0)
                    continue;
                var degrees = monom.Degrees;
                if (degrees.Count == 0)
                    continue;

                // Get the factorial basis for this monomial
                var expandedForm = GetMonomomialFacBasis(monom, input.width);

                // Then distribute our current coefficients, and subtract out the lower degree bits from the rest of the polynomial.
                // Subtract out the basis, skipping the leading coefficient.
                expandedForm.Multiply(coeff);
                var terms = expandedForm.GetOrderedMonomials();
                Debug.Assert(terms.Last().Equals(monom));
                for (int i = 0; i < terms.Count - 1; i++)
                {
                    // If this term was contained, we can just subtract it out.
                    var m = terms[i];
                    var contains = input.ContainsMonomial(m);

                    // If the sparse polynomial contains this polynomial:
                    if (contains)
                    {
                        // Update the coefficient
                        input.Sum(m, (expandedForm.moduloMask * expandedForm.GetCoeff(m)));
                    }

                    // Otherwise we need to add it to the bag.
                    else
                    {
                        if (!bag.Contains(m))
                            bag.Add(m);

                        var newCoeff = expandedForm.GetCoeff(m);
                        input.SetCoeff(m, expandedForm.moduloMask * newCoeff);
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

        private static SparsePolynomial GetMonomomialFacBasis(Monomial monomial, byte width)
        {
            // Compute the factorial basis for this monomial.
            SparsePolynomial mergedFactorial = null;
            foreach (var deg in monomial.Degrees)
            {
                SparsePolynomial expanded = null;
                // For this variable, get the factorial basis for it's degrees,
                if (deg == 0)
                {
                    expanded = new SparsePolynomial(1, width);
                    expanded.SetCoeff(new Monomial(0), 1);
                }

                else
                {
                    expanded = PolynomialReducer.GetExpandedUnivariateFacForm(deg, width, true);
                }

                // Then multiply the factorial basis with the other factorial bases.
                if (mergedFactorial == null)
                    mergedFactorial = expanded;
                else
                    mergedFactorial = PolynomialReducer.Multiply(mergedFactorial, expanded);
            }

            return mergedFactorial;
        }


        // Given a degree(for univariate monomials only), compute the expanded factorial form.
        public static SparsePolynomial GetExpandedUnivariateFacForm(int degree, byte width, bool falling)
        {
            var moduloMask = (ulong)ModuloReducer.GetMask(width);
            var terms = new ulong[degree + 1];
            terms[0] = 1;
            terms[1] = 1;
            for (int degIdx = 1; degIdx < degree + 1; degIdx++)
            {
                ulong coeff = ((ulong)degIdx - 1ul);
                if (falling)
                    coeff *= moduloMask;
                coeff &= moduloMask;

                var clone = terms.ToArray();
                for (int i = 0; i < terms.Length; i++)
                    terms[i] = 0;

                // Move the leading X over
                for (int i = 0; i < terms.Length - 1; i++)
                {
                    terms[i + 1] = clone[i];
                }

                // Move the coefficient over
                for (int i = 0; i < degIdx; i++)
                {
                    terms[i] += (coeff * clone[i]);
                    terms[i] &= moduloMask;
                }
            }

            var poly = new SparsePolynomial(1, width);
            for (int i = 1; i < terms.Length; i++)
            {
                var monom = new Monomial((byte)i);
                var coeff = (ulong)terms[i];
                poly.SetCoeff(monom, coeff);
            }

            return poly;
        }

        public static SparsePolynomial Multiply(SparsePolynomial a, SparsePolynomial b)
        {
            // This is not really a "generic" polynomial multiply, this will only work the case that no variables are shared.
            var newPoly = new SparsePolynomial(a.numVars + b.numVars, a.width);
            Debug.Assert(b.numVars == 1);

            foreach (var (monomA, coeffA) in a.coeffs)
            {
                if (coeffA == 0)
                    continue;

                foreach (var (monomB, coeffB) in b.coeffs)
                {
                    if (coeffB == 0)
                        continue;

                    // If no variables are shared then we can just merge the monomial.
                    var newCoeff = coeffA * coeffB;
                    newCoeff &= a.moduloMask;

                    var degrees = new byte[newPoly.numVars];
                    for (int i = 0; i < a.numVars; i++)
                        degrees[i] = monomA.GetVarDeg(i);
                    degrees[a.numVars] = monomB.GetVarDeg(0);

                    var newMonom = new Monomial(degrees);
                    ulong oldCoeff = 0;
                    newPoly.TryGetCoeff(newMonom, out oldCoeff);
                    oldCoeff += newCoeff;
                    newPoly.SetCoeff(newMonom, oldCoeff);
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

            var getFact = (ulong i) =>
            {
                // Get the factorial of this number.
                var fact = Factorial(i);

                // Get the greatest power of two that divides this number.
                // https://www.geeksforgeeks.org/highest-power-of-two-that-divides-a-given-number/
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
                var (h1, idx1) = getFact((ulong)deg);
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

                var expanded = GetMonomomialFacBasis(monom, input.width);
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
