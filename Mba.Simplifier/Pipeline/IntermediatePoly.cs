using Mba.Simplifier.Bindings;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Pipeline
{
    // This is an intermediate stage between our SparsePolynomial representation, and the 
    // representation that's necessary for arbitrary polynomial reduction.
    // In the future these should be abstracted into a single data structure.
    public class IntermediatePoly
    {
        public readonly uint bitWidth;

        public readonly ulong moduloMask;

        public readonly Dictionary<IntermediateMonomial, ulong> coeffs = new();

        public IntermediatePoly(uint bitWidth)
        {
            this.bitWidth = bitWidth;
            moduloMask = ModuloReducer.GetMask(bitWidth);
        }

        public void Sum(IntermediateMonomial monomial, ulong value)
        {
            bool contained = coeffs.TryGetValue(monomial, out var old);
            old += value;
            old &= moduloMask;
            if (old == 0)
            {
                if (contained)
                    coeffs.Remove(monomial);
                return;
            }
            coeffs[monomial] = old;
        }

        public override string ToString()
        {
            var terms = new List<string>();
            foreach (var (monom, coeff) in coeffs)
                terms.Add($"{coeff}*({monom})");

            return string.Join(" + ", terms);
        }

        public static IntermediatePoly Add(IReadOnlyList<IntermediatePoly> polys)
        {
            var width = polys.First().bitWidth;
            ulong constSum = 0;
            var outPoly = new IntermediatePoly(width);
            foreach (var poly in polys)
            {
                foreach (var (monom, coeff) in poly.coeffs)
                {
                    outPoly.Sum(monom, coeff);
                }
            }

            return outPoly;
        }

        public static IntermediatePoly Mul(AstCtx ctx, IReadOnlyList<IntermediatePoly> polys)
        {
            var width = polys.First().bitWidth;
            ulong coeffSum = 1;
            var outPoly = new IntermediatePoly(width);
            // Set the initial polynomial to `1`.
            outPoly.coeffs[IntermediateMonomial.Constant(ctx, width)] = 1;
            foreach (var poly in polys)
            {
                outPoly = Mul(ctx, outPoly, poly);
            }

            return outPoly;
        }

        public static IntermediatePoly Mul(AstCtx ctx, IntermediatePoly a, IntermediatePoly b)
        {
            var outPoly = new IntermediatePoly(a.bitWidth);
            foreach (var (monomA, coeffA) in a.coeffs)
            {
                var isAConstant = IsConstant(ctx, monomA);
                foreach (var (monomB, coeffB) in b.coeffs)
                {
                    var newCoeff = coeffA * coeffB;
                    newCoeff &= a.moduloMask;

                    // Then we need to construct a new monomial.
                    var newMonom = Mul(ctx, monomA, monomB);
                    outPoly.Sum(newMonom, newCoeff);
                }
            }

            return outPoly;
        }

        public static IntermediateMonomial Mul(AstCtx ctx, IntermediateMonomial a, IntermediateMonomial b)
        {
            // If both are a constant, return the first monomial.
            var isAConstant = IsConstant(ctx, a);
            var isBConstant = IsConstant(ctx, b);
            if (isAConstant && isBConstant)
                return a;
            // If one is a constant, return the other.
            if (isAConstant)
                return b;
            if (isBConstant)
                return a;
            // Otherwise we need to multiply.
            var outputDict = new Dictionary<AstIdx, ulong>();
            foreach (var (basis, deg) in a.varDegrees)
            {
                outputDict.TryAdd(basis, 0);
                outputDict[basis] += deg;
            }
            foreach (var (basis, deg) in b.varDegrees)
            {
                outputDict.TryAdd(basis, 0);
                outputDict[basis] += deg;
            }

            return new IntermediateMonomial(outputDict);
        }

        public static bool IsConstant(AstCtx ctx, IntermediateMonomial monom)
        {
            if (monom.varDegrees.Count != 1)
                return false;
            var asConstant = ctx.TryGetConstantValue(monom.varDegrees.First().Key);
            if (asConstant == null)
                return false;
            Debug.Assert(asConstant.Value == 1);
            Debug.Assert(monom.varDegrees.First().Value <= 1);
            return true;
        }
    }

    public class IntermediateMonomial : IEquatable<IntermediateMonomial>
    {
        public IReadOnlyDictionary<AstIdx, ulong> varDegrees;

        private readonly int hash;

        public IntermediateMonomial(IReadOnlyDictionary<AstIdx, ulong> varDegrees)
        {
            this.varDegrees = varDegrees;
            hash = ComputeHash(varDegrees);
        }

        public override int GetHashCode()
        {
            return hash;
        }

        public override string ToString()
        {
            List<string> terms = new();
            bool unroll = true;
            foreach (var (var, deg) in varDegrees)
            {
                if (!unroll)
                    terms.Add($"{var}**{deg}");
                else
                    terms.Add(string.Join("*", Enumerable.Repeat(var.ToString(), (int)deg)));
            }

            return string.Join("*", terms);
        }

        private static int ComputeHash(IReadOnlyDictionary<AstIdx, ulong> varDegrees)
        {
            int hash = 17;
            foreach (var (var, deg) in varDegrees)
            {
                // The hashes must not be dependent on one another, since the order of the dictionary is not guaranteed.
                var tempHash = var.GetHashCode() * 31 + deg.GetHashCode() * 17;
                hash += tempHash;
            }

            return hash;
        }

        public static IntermediateMonomial Constant(AstCtx ctx, uint width)
        {
            var constant = ctx.Constant(1, (byte)width);
            // Represent a constant as a constant monomial of `1`, with the constant being contained in the coefficient.
            var constMonom = new IntermediateMonomial(new Dictionary<AstIdx, ulong>() { { constant, 1 } });
            return constMonom;
        }

        public bool Equals(IntermediateMonomial? other)
        {
            if (hash != other.GetHashCode())
                return false;
            if (varDegrees.Count != other.varDegrees.Count)
                return false;
            foreach (var (var, deg) in varDegrees)
            {
                if (!other.varDegrees.TryGetValue(var, out var otherDeg))
                    return false;
                if (deg != otherDeg)
                    return false;
            }

            return true;
        }
    }
}
