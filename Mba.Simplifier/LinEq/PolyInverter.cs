using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Polynomial;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Channels;
using System.Threading.Tasks;

namespace Mba.Simplifier.LinEq
{
    /// <summary>
    /// Class for inverting binary permutation polynomials.
    /// </summary>
    public static class PolyInverter
    {
        // Tries to find an inverse for the given polynomial.
        public static SparsePolynomial? TryInvert(SparsePolynomial poly)
        {
            // Construct a system of linear equations
            var linearSystem = GetInverseLinearSystem(poly);

            // Solve the linear system.
            var inverseCoeffs = LinearEquationSolver.Solve(linearSystem);
            if (inverseCoeffs == null)
                return null;

            // Construct the inverse polynomial.
            // Note that we invert the coefficients such that the lower degree terms come first.
            var invPoly = new SparsePolynomial(poly.numVars, poly.width);
            var coeffs = inverseCoeffs.Reverse().ToArray();
            for(int i = 0; i < coeffs.Length; i++)
            {
                var monom = new Monomial((byte)i);
                invPoly.SetCoeff(monom, coeffs[i]);
            }

            return invPoly;
        }

        // Construct a linear system where the solution is the inverse of the polynomial.
        private static LinearSystem GetInverseLinearSystem(SparsePolynomial poly)
        {
            var numVars = poly.coeffs.Count * 2;
            int numEquations = numVars * 2;
            var equations = new List<LinearEquation>();
            for (int i = 0; i < numEquations; i++)
                equations.Add(new LinearEquation(numVars));

            var linearSystem = new LinearSystem(poly.width, numVars, equations);
            // Evaluate the polynomial on one point for each degree.
            var points = new List<ulong>();
            for (int i = 0; i < numEquations; i++)
            {
                var eval = PolynomialEvaluator.Eval(poly, new ulong[] { (ulong)i });
                points.Add(poly.moduloMask & eval);
            }

            // Fill in the linear system
            for (int pointIdx = 0; pointIdx < points.Count; pointIdx++)
            {
                // For the lhs, we plug in the result of the polynomial evaluation
                linearSystem.Equations[pointIdx].coeffs[0] = 1;
                for (int i = 1; i < numVars; i++)
                {
                    var c = points[pointIdx];
                    var coeff = poly.moduloMask & PolynomialEvaluator.Pow(c, (byte)i);
                    linearSystem.Equations[pointIdx].coeffs[i] = coeff;
                }

                linearSystem.Equations[pointIdx].result = (ulong)pointIdx;
            }

            // Place the highest degree terms first, such that we solve for the constant offset first.
            foreach (var linEq in linearSystem.Equations)
                linEq.coeffs = linEq.coeffs.Reverse().ToArray();

            return linearSystem;
        }

        public static SparsePolynomial Get8BitPermPoly()
        {
            var poly = new SparsePolynomial(1, (byte)8);
            poly.SetCoeff(new Monomial(0), 132);
            poly.SetCoeff(new Monomial(1), 185);
            poly.SetCoeff(new Monomial(2), 42);
            return poly;
        }

        public static SparsePolynomial Get64BitPermPoly()
        {
            var poly = new SparsePolynomial(1, (byte)64);
            poly.SetCoeff(new Monomial(0), 9193501499183852111);
            poly.SetCoeff(new Monomial(1), 5260339532280414813);
            poly.SetCoeff(new Monomial(2), 14929154534604275712);
            poly.SetCoeff(new Monomial(3), 3178634119571570688);
            return poly;
        }
    }
}
