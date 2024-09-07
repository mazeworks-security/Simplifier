using Mba.Simplifier.Bindings;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Pipeline.Intermediate
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
            moduloMask = (ulong)ModuloReducer.GetMask(bitWidth);
        }

        public void Sum(IntermediateMonomial monomial, ulong value)
        {
            bool contained =coeffs.TryGetValue(monomial, out var old);
            old += value;
            old &= moduloMask;
            if (old == 0)
            {
                if(contained)
                    coeffs.Remove(monomial);
                return;
            }
            coeffs[monomial] = old;
        }

        public override string ToString()
        {
            var terms = new List<string>();
            foreach(var (monom, coeff) in coeffs)
            {
                terms.Add($"{coeff}*({monom})");
            }

            return String.Join(" + ", terms);
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
            foreach(var (var, deg) in varDegrees)
            {
                if (!unroll)
                    terms.Add($"{var}**{deg}");
                else
                    terms.Add(String.Join("*", Enumerable.Repeat(var.ToString(), (int)deg)));
            }

            return String.Join("*", terms);
        }

        private static int ComputeHash(IReadOnlyDictionary<AstIdx, ulong> varDegrees)
        {
            int hash = 17;
            foreach (var (var, deg) in varDegrees)
            {
                hash = hash * 31 + var.GetHashCode();
                hash = hash * 31 + deg.GetHashCode();
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
            foreach(var (var, deg) in varDegrees)
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
