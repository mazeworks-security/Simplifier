using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.LinEq
{
    public class LinearSystem
    {
        public ulong ModuloMask { get; }

        public int NumVars { get; }

        public List<LinearEquation> Equations { get; set; }

        public LinearSystem(uint bitSize, int numVars, List<LinearEquation> equations)
        {
            ModuloMask = (ulong)ModuloReducer.GetMask(bitSize);
            NumVars = numVars;
            Equations = equations;
        }

        // Sort the equations by their number of leading zeroes.
        // In the case of a tie, we pick the one with the smallest coefficient.
        public void Sort()
        {
            Equations.Sort((x, y) => Compare(x, y));
        }

        // Convert the system of equations to a set of z3 constraints, for debugging purposes.
        public string ToZ3String()
        {
            var sb = new StringBuilder();
            foreach (var linEq in Equations)
                sb.AppendLine($"s.add({linEq})");
            return sb.ToString();
        }

        public string ToPyString()
        {


            var sb = new StringBuilder();
            sb.AppendLine($"system = [");
            foreach(var linEq in Equations)
            {
               
                var inputs = String.Join($", ", linEq.coeffs);
                sb.AppendLine($"    ([{inputs}], {linEq.result}),");
            }

            sb.AppendLine("]");
            return sb.ToString();
        }

        private static int Compare(LinearEquation a, LinearEquation b)
        {
            var r = CompareInternal(a, b);

            return r;
        }

        private static int CompareInternal(LinearEquation a, LinearEquation b)
        {
            if (a.ToString() == b.ToString())
                return 0;

            var firstA = a.FirstNonZeroIdx();
            var firstB = b.FirstNonZeroIdx();
            if (firstA == firstB)
            {
                if (a.ToString() == b.ToString())
                    return 0;

                return 0;

                //return a.coeffs[firstA].CompareTo(b.coeffs[firstB]);
            }

            /*
            if (firstA < firstB)
                return -1;
            */
            return firstA.CompareTo(firstB);


            return 1;
        }
    }
}
