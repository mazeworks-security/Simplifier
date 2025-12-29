using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Polynomial
{
    public class SparsePolynomial
    {
        public readonly Dictionary<Monomial, ulong> coeffs = new();

        public readonly ulong moduloMask;

        public readonly int numVars;

        public readonly byte width;

        public ulong this[Monomial key]
        {
            get => GetCoeff(key);
            set => SetCoeff(key, value);
        }

        public SparsePolynomial(int numVars, byte width)
        {
            moduloMask = (ulong)ModuloReducer.GetMask(width);
            this.numVars = numVars;
            this.width = width;
        }

        public ulong GetCoeff(Monomial index)
        {
            return coeffs[index];
        }

        public ulong GetCoeffOrZero(Monomial index)
        {
            ulong coeff = 0;
            coeffs.TryGetValue(index, out coeff);
            return coeff;
        }

        public bool TryGetCoeff(Monomial index, out ulong coeff)
            => coeffs.TryGetValue(index, out coeff);

        public bool ContainsMonomial(Monomial index)
            => coeffs.ContainsKey(index);

        public void SetCoeff(Monomial index, ulong value)
        {
            value &= moduloMask;
            coeffs[index] = value;
        }

        public bool Sum(Monomial index, ulong value)
        {
            value &= moduloMask;
            ulong sum = 0;
            bool contains = TryGetCoeff(index, out sum);
            sum += value;
            SetCoeff(index, sum);
            return contains;
        }

        public void Multiply(ulong coeff)
        {
            coeff &= moduloMask;

            foreach (var (monom, oldCoeff) in coeffs.ToList())
            {
                var newCoeff = (moduloMask & oldCoeff) * coeff;
                SetCoeff(monom, newCoeff);
            }
        }

        public IReadOnlyList<Monomial> GetOrderedMonomials()
        {
            var bar = coeffs.Keys.OrderBy(x => x).ToList();
            return bar;
        }

        private int CompareTo(Monomial a, Monomial b)
        {
            // Compare the two monomials.
            // If they are equal, return 0.
            // If a is greater than b, return 1.
            // If a is less than b, return -1.
            if (a.Equals(b))
                return 0;
            var totalA = a.GetTotalDeg();
            var totalB = b.GetTotalDeg();
            if (totalA > totalB)
                return 1;
            else if (totalB > totalA)
                return -1;

            for (int i = 0; i < numVars; i++)
            {
                var degA = a.GetVarDeg(i);
                var degB = b.GetVarDeg(i);
                if (degA == degB)
                    continue;
                if (degA > degB)
                    return 1;
                else
                    return -1;
            }
            return 0;
        }

        public override string ToString()
        {
            return ToString(true);
        }

        public string ToString(bool canonicalBasis = true)
        {
            var keys = GetOrderedMonomials();
            List<string> terms = new();
            foreach (var key in keys)
            {
                var coeff = GetCoeff(key);
                if (coeff == 0)
                    continue;
                /*
                if (key.GetTotalDeg() == 0)
                    terms.Add(coeff.ToString());
                else
                    terms.Add($"{coeff}*{key.ToString(canonicalBasis)}");
                */
                terms.Add($"{coeff}*{key.ToString(canonicalBasis)}");
            }

            var txt = String.Join(" + ", terms.ToArray());
            return txt;
        }

        public SparsePolynomial Clone()
        {
            var clone = new SparsePolynomial(numVars, width);
            foreach (var (monom, coeff) in coeffs)
                clone.SetCoeff(monom, coeff);

            return clone;
        }

        public void Clear()
            => coeffs.Clear();

        public static SparsePolynomial GetUnivariate(byte width, params ulong[] coeffs)
        {
            var poly = new SparsePolynomial(1, width);
            for (int i = 0; i < coeffs.Length; i++)
            {
                var key = new Monomial((byte)i);
                poly[key] = coeffs[i];
            }
            return poly;
        }

        public static SparsePolynomial ParsePoly(string astStr, int numVars, byte width)
        {
            astStr = astStr.Replace("(", "");
            astStr = astStr.Replace(")", "");

            var strTerms = astStr.Split("+", StringSplitOptions.RemoveEmptyEntries);

            strTerms = strTerms.Select(x => x.Replace(" ", "")).ToArray();

            var terms = new List<(Int128 coeff, IReadOnlyList<(string, int)> varDegs)>();
            foreach (var term in strTerms)
            {
                var muls = term.Split("*", StringSplitOptions.RemoveEmptyEntries);

                Int128 coeff = 1;
                Dictionary<string, int> varCounts = new();
                foreach (var m in muls)
                {
                    if (Int128.TryParse(m, out var val))
                    {
                        coeff *= val;
                    }

                    else
                    {
                        varCounts.TryAdd(m, 0);
                        varCounts[m] += 1;
                    }
                }

                var bar = (coeff, varCounts.OrderBy(x => x.Key).Select(x => (x.Key, x.Value)).ToList().AsReadOnly());
                terms.Add(bar);
            }


            var poly = new SparsePolynomial(numVars, width);
            var allVars = terms.SelectMany(x => x.varDegs.Select(x => x.Item1)).ToHashSet().OrderBy(x => x).ToList();
            foreach (var term in terms)
            {
                var coeff = (ulong)(UInt128)term.coeff;
                var varDegs = term.varDegs.Select(x => (allVars.IndexOf(x.Item1), x.Item2));

                List<byte> degs = new();
                foreach (var (varIdx, degree) in varDegs.OrderBy(x => x.Item1))
                {
                    while (degs.Count != varIdx)
                        degs.Add(0);

                    degs.Add((byte)(uint)degree);
                }

                while (degs.Count != allVars.Count)
                    degs.Add(0);

                var monom = new Monomial(degs.ToArray());
                ulong existing = 0;
                poly.TryGetCoeff(monom, out existing);
                existing += coeff;
                poly.SetCoeff(monom, existing);
            }

            return poly;
        }
    }
}
