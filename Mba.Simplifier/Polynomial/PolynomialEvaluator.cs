using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Polynomial
{
    public static class PolynomialEvaluator
    {
        public static ulong Eval(SparsePolynomial poly, ulong[] inputs, bool canonicalBasis = true)
        {
            ulong sum = 0;
            var varCount = poly.numVars;
            foreach(var (monom, coeff) in poly.coeffs)
            {
                ulong result = 1;
                for(int i = 0; i < varCount; i++)
                {
                    var deg = monom.GetVarDeg(i);
                    if (deg == 0)
                        continue;
                    if (canonicalBasis)
                        result *= Pow(inputs[i], deg);
                    else
                        result *= FactorialPow(inputs[i], deg);
                }

                result *= coeff;
                sum += result;
            }

            return sum;
        }

        // TODO: Use repeated squaring algorithm for high degrees.
        public static ulong Pow(ulong x, byte power)
        {
            if (power == 0)
                return 1;
            if (power == 1)
                return x;

            var original = x;
            var originalBv = x;
            for(byte i = 1; i < power; i++)
            {
                x *= originalBv;
            }

            return x;
        }

        public static ulong FactorialPow(ulong x, byte power) 
        {
            if (power == 0)
                return 1;
            if (power == 1)
                return x;

            var original = x;
            var originalBv = x;
            for (byte i = 1; i < power; i++)
            {
                x *= (originalBv - (ulong)i);
            }

            return x;
        }
    }
}
