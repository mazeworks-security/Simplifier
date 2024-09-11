using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Pipeline
{
    public record Lc(UInt128 d, UInt128 x0, UInt128 n);

    public class LinearCongruenceSolver
    {
        private readonly UInt128 moduloMask;

        public LinearCongruenceSolver(UInt128 moduloMask)
        {
            this.moduloMask = moduloMask;
        }

        // Function to give the distinct
        // solutions of ax = b (mod n)
        public Lc? LinearCongruence(UInt128 A, UInt128 B, UInt128 N)
        {
            A = R(A % N);
            B = R(B % N);

            UInt128 u = 0, v = 0;

            // Function Call to find
            // the value of d and u
            UInt128[] person = ExtendedEuclidean(A, N);
            UInt128 d = person[0];
            u = person[1];
            v = person[2];

            // No solution exists
            if (R(B % d) != 0)
            {
                return null;
            }

            // Else, initialize the value of x0
            UInt128 x0 = R((u * R((B / d)))) % N;
            x0 = R(x0);
            if (x0 < 0)
                x0 += N;

            x0 = R(x0);
            return new Lc(d, x0, N);
        }

        // Function to stores the values of x and y
        // and find the value of gcd(a, b)
        public UInt128[] ExtendedEuclidean(UInt128 a, UInt128 b)
        {
            // Base Case
            if (a == 0)
            {
                return new UInt128[] { b, 0, 1 };
            }
            else
            {
                // Store the result of recursive call
                UInt128 x1 = 1, y1 = 1;
                UInt128[] gcdy = ExtendedEuclidean(b % a, a);
                UInt128 gcd = gcdy[0];
                x1 = gcdy[1];
                y1 = gcdy[2];

                // Update x and y using results of
                // recursive call
                UInt128 y = x1;
                UInt128 x = y1 - (UInt128)(R(b / a)) * x1;

                return new UInt128[] { gcd, x, y };
            }
        }

        public UInt128 GetSolution(UInt128 i, Lc solutions)
        {
            UInt128 an = R(solutions.x0 + i * R(solutions.n / solutions.d)) % solutions.n;
            an = R(an);
            return an;
        }

        private UInt128 R(UInt128 a)
            => moduloMask & a;
    }
}
