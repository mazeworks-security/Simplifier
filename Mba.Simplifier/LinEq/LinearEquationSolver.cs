using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Polynomial;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.LinEq
{
    public class LinearEquationSolver
    {
        private readonly ulong moduloMask;

        private readonly LinearCongruenceSolver congruenceSolver;

        private readonly LinearSystem linearSystem;

        public static ulong[]? Solve(LinearSystem linearSystem)
            => new LinearEquationSolver(linearSystem).Solve();

        private LinearEquationSolver(LinearSystem linearSystem)
        {
            this.moduloMask = linearSystem.ModuloMask;
            this.congruenceSolver = new LinearCongruenceSolver((UInt128)moduloMask);
            this.linearSystem = linearSystem;
        }

        private ulong[]? Solve()
        {
            // Try to convert the linear system to row echelon form.
            EnterRowEchelonForm();
            linearSystem.Equations.RemoveAll(x => x.GetLeadingZeroCount() == x.NumVars);
            linearSystem.Sort();

            Console.WriteLine(linearSystem.ToZ3String() + "\n\n");
            Console.WriteLine(linearSystem.ToPyString());

            // TODO: We still may be able to find a solution in both of these cases.
            if (linearSystem.Equations.Count != linearSystem.NumVars)
                return null;
            for (int i = 0; i < linearSystem.Equations.Count; i++)
            {
                var eq = linearSystem.Equations[i];
                if (eq.GetLeadingZeroCount() != i)
                    return null;
            }

            // Enumerate the possible solutions until we find a fit.
            var solutionMap = new ulong[linearSystem.NumVars];
            bool success = EnumerateSolutions(linearSystem, congruenceSolver, solutionMap, linearSystem.NumVars - 1, upperTriangular: true);
            if (!success)
                return null;

            return solutionMap;
        }

        private void EnterRowEchelonForm()
        {
            var varCount = linearSystem.NumVars;
            for (int varIdx = 0; varIdx < varCount; varIdx++)
            {
                // First we sort(ascending order) by the number of leading zero coefficients.
                linearSystem.Sort();

                // Identify the first coefficient that can be used to eliminate all other coefficients for this variable.
                var pivotIdx = SelectPivot(varIdx);
                // If we cannot find a coefficient to eliminate all others by, we still may be able to eliminate others
                // after solving a linear congruence.
                if (pivotIdx == -1)
                {
                    EliminateViaSubtraction(varIdx);

                    linearSystem.Sort();


                    continue;
                }

                // Eliminate all other coefficients for this variable.
                var ourCoeff = linearSystem.Equations[pivotIdx].coeffs[varIdx];
                for (int i = pivotIdx + 1; i < linearSystem.Equations.Count; i++)
                {
                    var otherEq = linearSystem.Equations[i];
                    var otherCoeff = otherEq.coeffs[varIdx];
                    if (otherCoeff == 0)
                        continue;

                    // Find the coefficient that would allow us to reduce the other coefficients to zero.
                    var reducer = GetCoeffReducer(ourCoeff, otherCoeff);
                    if (reducer == null)
                        continue;

                    AddMultipleTo(varIdx, pivotIdx, i, reducer.Value);
                }
            }
        }

        // Select a linear equation to be used as a pivot.
        private int SelectPivot(int varIdx)
        {
            int firstIdx = -1;
            var best = (-1, -1);
            for (int i = 0; i < linearSystem.Equations.Count; i++)
            {
                var lineq = linearSystem.Equations[i];
                var coeff = lineq.coeffs[varIdx];

                if (coeff == 0)
                    continue;
                var trailingZeroes = lineq.GetLeadingZeroCount();
                if (trailingZeroes != varIdx)
                    continue;

                if (firstIdx == -1)
                    firstIdx = i;

                // Skip if a modular inverse does not exist.
                // TODO: Use fast modular inverse, skip if coefficient is not odd
                var inv = GetModularInverse(coeff);
                if (coeff != 1 && inv == null)
                    continue;

                var leadingZeroes = lineq.coeffs.TakeWhile(x => x == 0).Count();
                if (leadingZeroes > best.Item2)
                {
                    best = (i, leadingZeroes);
                }
            }

            // If this has less trailing zeroes than the best candidate, we bail out.
            // This would increase the number of non zero entries across the whole linear system if used.
            if (best.Item2 != varIdx)
                return -1;
            // If the first non zero idx is the best candidate, we keep it.
            if (firstIdx == best.Item1)
                return firstIdx;

            var firstNonZeroIdx = firstIdx;
            var old = linearSystem.Equations[firstIdx];
            var firstInvertibleIdx = best.Item1;
            var nnew = linearSystem.Equations[firstInvertibleIdx];
            linearSystem.Equations[firstNonZeroIdx] = nnew;
            linearSystem.Equations[firstInvertibleIdx] = old;
            return firstNonZeroIdx;
        }

        private ulong? GetModularInverse(ulong coeff)
        {
            var lc = congruenceSolver.LinearCongruence((UInt128)coeff, 1, (UInt128)moduloMask + 1);
            if (lc == null)
                return null;
            if (lc.d == 0)
                return null;

            return (ulong)congruenceSolver.GetSolution(0, lc);
        }

        private ulong? GetCoeffReducer(ulong ourCoeff, ulong otherCoeff)
        {
            var inv = moduloMask & (moduloMask * otherCoeff);

            var lc = congruenceSolver.LinearCongruence(ourCoeff, inv, (UInt128)moduloMask + 1);
            if (lc == null)
                return null;
            if (lc.d == 0)
                return null;

            var sol = (ulong)congruenceSolver.GetSolution(0, lc);
            return sol;
        }

        private bool EliminateViaSubtraction(int varIdx)
        {
            /*
            var firstIdx = linearSystem.Equations.FindIndex(x => x.GetLeadingZeroCount() == varIdx);
            if (firstIdx == -1)
                return false;
            */

            var firstIdx = 0;


            bool changed = false;
            for (int a = firstIdx; a < linearSystem.Equations.Count; a++)
            {
                for (int b = a + 1; b < linearSystem.Equations.Count; b++)
                {
                    bool eliminated = TryEliminateBy(a, b, varIdx);
                    if (!eliminated)
                        eliminated = TryEliminateBy(b, a, varIdx);

                    changed |= eliminated;
                }
            }

            return changed;
        }

        private bool TryEliminateBy(int from, int to, int varIdx)
        {
            //if(varIdx == 2 && from == 2 && to == 1)
            //    Debugger.Break();

            if (linearSystem.Equations[from].GetLeadingZeroCount() < linearSystem.Equations[to].GetLeadingZeroCount())
            {
                //Debugger.Break();
                return false;
            }    

            var aCoeff = linearSystem.Equations[from].coeffs[varIdx];
            if (aCoeff == 0)
                return false;
            var bCoeff = linearSystem.Equations[to].coeffs[varIdx];
            if (bCoeff == 0)
                return false;

            var oldCoeff = bCoeff;
            bCoeff = moduloMask & moduloMask * bCoeff;
            var lc = congruenceSolver.LinearCongruence(aCoeff, bCoeff, (UInt128)moduloMask + 1);
            if (lc == null)
                return false;

            var reducer = (ulong)congruenceSolver.GetSolution(0, lc);

            AddMultipleTo(varIdx, from, to, reducer);
            return true;
        }

        private void AddMultipleTo(int varIdx, int fromIdx, int toIdx, ulong multiple)
        {
            if (linearSystem.Equations[fromIdx].GetLeadingZeroCount() < linearSystem.Equations[toIdx].GetLeadingZeroCount())
            {
                //Debugger.Break();
                Debugger.Break();
            }
            var ourEq = linearSystem.Equations[fromIdx];
            var ourCoeff = ourEq.coeffs[varIdx];
            var ourResult = ourEq.result;

            var otherEq = linearSystem.Equations[toIdx];
            var otherCoeff = otherEq.coeffs[varIdx];

            var mul = Mul(ourEq, multiple);
            var add = Add(otherEq, mul);
            var newResult = moduloMask & (moduloMask & multiple * ourResult) + otherEq.result;
            add.result = newResult;
            linearSystem.Equations[toIdx] = add;
        }

        private LinearEquation Mul(LinearEquation a, ulong coeff)
        {
            var clone = new LinearEquation(a.coeffs.Length);
            clone.coeffs = a.coeffs.ToArray();
            for (int i = 0; i < clone.coeffs.Length; i++)
            {
                clone.coeffs[i] = moduloMask & clone.coeffs[i] * coeff;
            }

            return clone;
        }

        private LinearEquation Add(LinearEquation a, LinearEquation b)
        {
            var clone = new LinearEquation(a.coeffs.Length);
            for (int i = 0; i < clone.coeffs.Length; i++)
            {
                clone.coeffs[i] = moduloMask & a.coeffs[i] + b.coeffs[i];
            }
            return clone;
        }

        public static HashSet<int> Solutions = new();

        public static bool EnumerateSolutions(LinearSystem linearSystem, LinearCongruenceSolver congruenceSolver,  ulong[] solutionMap, int varIdx, bool upperTriangular)
        {
            var moduloMask = linearSystem.ModuloMask;

            // Adjust the rhs of the equation to account for the solutions of the other variables.
            var lineq = linearSystem.Equations[varIdx];
            var result = lineq.result;

            var sum = (int i) =>
            {
                var coeff = lineq.coeffs[i];
                var mul = coeff * solutionMap[i];
                result -= mul;
                result &= moduloMask;
            };

            if (upperTriangular)
            {
                for (int i = varIdx + 1; i < linearSystem.NumVars; i++)
                    sum(i);
            }

            else
            {
                for (int i = 0; i < varIdx; i++)
                    sum(i);
            }


                var ourCoeff = lineq.coeffs[varIdx];
            var lc = congruenceSolver.LinearCongruence(ourCoeff, result, (UInt128)moduloMask + 1);
            if (lc == null)
                return false;
            int limit = lc.d > 255 ? 255 : (int)lc.d;

            //var reduceMask = PolynomialReducer.GetReductionMask((byte)BitOperations.PopCount(linearSystem.ModuloMask), new Monomial(varIdx));

            bool anySuccess = false;
            for (int solutionIdx = 0; solutionIdx < limit; solutionIdx++)
            {
                var solution = (ulong)congruenceSolver.GetSolution((UInt128)solutionIdx, lc);
                //solution &= reduceMask
                solutionMap[varIdx] = solution;

                var end = upperTriangular ? 0 : solutionMap.Length - 1;
                if (varIdx == end)
                {
                    var c = solutionMap.Count(x => x == 0);
                    if (Solutions.Add(c))
                    {

                        //Console.WriteLine(c);
                    }
                    //Solutions.Add(solutionMap.ToArray());
                    return true;
                }

                else
                {
                    var nextIdx = upperTriangular ? varIdx - 1 : varIdx + 1;
                    bool success = EnumerateSolutions(linearSystem, congruenceSolver, solutionMap, nextIdx, upperTriangular);
                    if (success)
                    {
                        anySuccess |= true;
                        return true;
                    }
                }
            }

            return anySuccess;
        }
    }
}
