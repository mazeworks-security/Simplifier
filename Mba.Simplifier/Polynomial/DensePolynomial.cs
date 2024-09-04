using Mba.Testing.PolyTesting;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Polynomial
{
    /// <summary>
    /// Dense representation of a multivariate polynomial.
    /// </summary>
    public unsafe class DensePolynomial
    {
        public readonly byte width;

        public readonly ulong moduloMask;

        public readonly int[] dimensions;

        public readonly ulong[] coeffs;

        public int NumVars => dimensions.Length;

        public DensePolynomial(byte width, int[] maxVarDegrees)
        {
            this.width = width;
            moduloMask = (ulong)ModuloReducer.GetMask(width);
            dimensions = maxVarDegrees.Select(x => x + 1).ToArray();
            int arrSize = 1;
            foreach (var deg in maxVarDegrees)
            {
                arrSize *= (deg + 1);
            }

            coeffs = new ulong[arrSize];
        }

        public Monomial GetMonomial(int index)
        {
            var degrees = GetDegrees(index);
            var mDegs = new byte[degrees.Length];
            for(int i = 0; i < degrees.Length; i++)
                mDegs[i] = (byte)degrees[i];
            var m = new Monomial(mDegs);
            return m;
        }

        public ulong GetCoeff(Monomial monom)
        {
            return coeffs[GetMonomIdx(monom)];
        }

        public int GetMonomIdx(Monomial monom)
        {
            var degrees = new int[monom.GetNumVars()];
            for(int i = 0; i < degrees.Length; i++)
                degrees[i] = monom.GetVarDeg(i);

            var idx = GetIndex(degrees);
            return idx;
        }

        public ulong GetCoeff(params int[] degrees)
        {
            var idx = GetIndex(degrees);
            return coeffs[idx];
        }

        public void SetCoeff(Monomial monomial, ulong value)
        {
            SetCoeff(GetMonomIdx(monomial), value);
        }

        public void SetCoeff(int index, ulong value)
        {
            value &= moduloMask;
            coeffs[index] = value;
        }

        public void Sum(Monomial monomial, ulong value)
        {
            Sum(GetMonomIdx(monomial), value);
        }

        public void Sum(int index, ulong value)
        {
            coeffs[index] += value;
            coeffs[index] &= moduloMask;
        }

        public int GetIndex(params int[] degrees)
        {
            if (dimensions.Length != degrees.Length)
                throw new ArgumentException("Dimensions and indices must have the same length.");

            int index = 0;
            for (int i = 0; i < dimensions.Length; i++)
            {
                index *= dimensions[i];
                index += degrees[i];
            }
            return index;
        }

        public int[] GetDegrees(int index)
        {
            int[] indices = new int[dimensions.Length];

            for (int i = dimensions.Length - 1; i >= 0; i--)
            {
                indices[i] = (int)((uint)index % (uint)dimensions[i]);
                index = (int)((uint)index / (uint)dimensions[i]);
            }

            return indices;
        }
    }
}
