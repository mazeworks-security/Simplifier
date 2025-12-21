using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Polynomial
{
    // Represents a multivariate monomial, with up to 8 variables.
    public struct Monomial : IEquatable<Monomial>, IComparable<Monomial>
    {
        // Each byte represents the degree of a variable.
        // Note that 255 is a special value representing the end of the degree list.
        private readonly ulong value = ulong.MaxValue;

        public IReadOnlyList<byte> Degrees => BitConverter.GetBytes(value).TakeWhile(x => x != 255).ToList();

        public byte[] DegArray => Degrees.ToArray();

        public Monomial(params byte[] varDegrees)
        {
            Debug.Assert(varDegrees.Length <= 8);
            for (int i = 0; i < varDegrees.Length; i++)
            {
                var degree = (ulong)varDegrees[i];
                var shiftBy = (ushort)(i * 8);
                var mask = 255ul << shiftBy;
                value &= ~mask;
                value |= (degree << shiftBy);
            }
        }

        public Monomial(int varDeg) : this((byte)varDeg)
        {

        }

        public byte GetVarDeg(int varIdx)
        {
            var shiftBy = 8 * varIdx;
            return (byte)(value >> (ushort)shiftBy);
        }

        public uint GetNumVars()
        {
            uint total = 0;
            for (int i = 0; i < 8; i++)
            {
                var degree = GetVarDeg(i);
                if (degree == byte.MaxValue)
                    break;
                total += 1;
            }

            return total;
        }

        public uint GetTotalDeg()
        {
            uint total = 0;
            for (int i = 0; i < 8; i++)
            {
                var degree = GetVarDeg(i);
                if (degree == byte.MaxValue)
                    break;

                total += degree;
            }

            return total;
        }

        public bool Equals(Monomial other)
        {
            return value == other.value;
        }

        // Compare the two monomials.
        // If they are equal, return 0.
        // If a is greater than b, return 1.
        // If a is less than b, return -1.
        public int CompareTo(Monomial b)
        {
            var a = this;

            if (a.Equals(b))
                return 0;
            var totalA = a.GetTotalDeg();
            var totalB = b.GetTotalDeg();
            if (totalA > totalB)
                return 1;
            else if (totalB > totalA)
                return -1;


            // Pick the one with the most variables..
            var one = -1;
            var neg = 1;
            var numA = a.Degrees.Count(x => x != 0);
            var numB = b.Degrees.Count(x => x != 0);
            if (numA > numB)
                return one;
            if (numB > numA)
                return neg;

            // Number of variables..
            // Lowest deg
            for (int i = 0; i < 8; i++)
            {
                var degA = a.GetVarDeg(i);
                var degB = b.GetVarDeg(i);
                // Invalid cases
                if (degA == byte.MaxValue)
                    return degB;
                if (degB == byte.MaxValue)
                    return degA;


                if (degA == degB)
                    continue;
                if (degA > degB)
                    return one;
                else
                    return neg;
            }
            return 0;
        }

        public override string ToString()
        {
            return ToString(true);
        }

        public string ToString(bool canonicalBasis = false)
        {
            var varDegrees = Degrees;
            List<string> powers = new();
            for (int i = 0; i < varDegrees.Count; i++)
            {
                var degree = varDegrees[i];
                if (degree == byte.MaxValue)
                    break;

                if (degree == 0)
                {
                    continue;
                }

                var varName = $"x{i}";
                if (degree == 1)
                {
                    powers.Add(varName);
                    continue;
                }

                bool unroll = true;
                string pow = null;
                if (canonicalBasis)
                    pow = GetCanonicalBasisStr(varName, degree, unroll);
                else
                    pow = GetFactorialBasisStr(varName, degree);
                powers.Add(pow);
            }

            var txt = String.Join("*", powers);
            return txt;
        }

        private string GetCanonicalBasisStr(string varName, int degree, bool unroll)
        {
            var pow = unroll ? String.Join("*", Enumerable.Repeat(varName, degree)) : $"{varName}**{degree}";
            return pow;
        }

        private string GetFactorialBasisStr(string varName, int degree)
        {
            List<string> factors = new();
            for(int i = 1; i <= degree; i++)
            {
                if (i == 1)
                    factors.Add($"{varName}");
                else
                    factors.Add($"({varName}-{i - 1})");
            }

            return String.Join("*", factors);
        }
    }
}
