using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.LinEq
{
    public class LinearEquation
    {
        public ulong[] coeffs;

        public ulong result = 0;

        public int NumVars => coeffs.Length;

        public LinearEquation(int numElements)
        {
            coeffs = new ulong[numElements];
        }

        public override string ToString()
        {
            // Note that the highest degree terms come first.
            var terms = new List<string>();
            for (int i = 0; i < coeffs.Length; i++)
            {
                var str = $"{coeffs[i]}*m{coeffs.Length - 1 - i}";
                terms.Add(str);
            }

            var sum = string.Join(" + ", terms);

            sum = $"({sum}) == {result}";

            return sum;
        }

        public int FirstNonZeroIdx()
        {
            for (int i = 0; i < coeffs.Length; i++)
            {
                if (coeffs[i] != 0)
                    return i;
            }

            return int.MaxValue;
        }

        public int GetLeadingZeroCount()
        {
            int count = 0;
            for (int i = 0; i < coeffs.Length; i++)
            {
                var coeff = coeffs[i];
                if (coeff == 0)
                    count++;
                else
                    return count;
            }

            return count;
        }
    }
}
