using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Jit;
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
using System.Xml.Linq;

namespace Mba.Simplifier.LinEq
{
    using Num = ulong;

    public struct Point
    {
        public Num X { get; }
        public Num Y { get; }

        public Point(Num x, Num y)
        {
            X = x;
            Y = y;
        }

        public Point(double x, double y)
        {
            X = (Num)x;
            Y = (Num)y;
        }


        public override string ToString()
        {
            return $"{X}, {Y}";
        }
    }

    public static class NewtonInterpolation
    {
        static string[] nameTable = new string[] { "x", "y", "z", "d"};

        //public record Equation(List<(ulong coeff, Monomial monomial)> Terms, ulong Result);
        public class Equation
        {
            public Equation(List<(ulong coeff, Monomial monomial)> terms, ulong result)
            {
                Terms = terms;
                Result = result;
            }

            public List<(ulong coeff, Monomial monomial)> Terms { get; }
            public ulong Result { get; }

            public override string ToString()
            {
                var sum = String.Join(" + ", Terms.Select(x => $"{x.coeff}*{x.monomial}"));
                return $"[{sum}] == {Result}";
            }
        }

        private static string GetNewtonMonomialStr(Monomial m, string[] names, int[] offsets)
        {
            if (m.Degrees.All(x => x == 0))
                return "1";

            bool prev = false;
            var sb = new StringBuilder();
            for(int varIdx = 0; varIdx < m.Degrees.Count; varIdx++)
            {
                var deg = m.Degrees[varIdx];
                if (deg == 0)
                    continue;

                if (prev)
                    sb.Append("*");

                var name = names[varIdx];
                var offset = offsets[varIdx];
                for (int d = 0; d < deg; d++)
                {
                    sb.Append($"({name} - {d})");
                    if (d != deg - 1)
                        sb.Append("*");
                }

                prev = true;
            }

            return sb.ToString();
        }

        private static bool CheckEquiv(SparsePolynomial a, bool aCanonical, SparsePolynomial b, bool bCanonical)
        {
            var rand = new SeededRandom();
            var numVars = Math.Max(a.numVars, b.numVars);

            for(int _ = 0; _ < 2048; _++)
            {
                var inputs = new ulong[numVars];
                for(int i = 0; i < numVars; i++)
                {
                    inputs[i] = rand.GetRandUlong();
                }

                var before = a.moduloMask & PolynomialEvaluator.Eval(a, inputs, aCanonical);
                var after = b.moduloMask & PolynomialEvaluator.Eval(b, inputs, bCanonical);
                if(before != after)
                    return false;
            }

            return true;

        }


        public static ulong MonomialFactorial(Monomial m, int numVars, ulong[] inputs, ulong[,] variableFactorials, HashSet<(int, int)> seen)
        {
            ulong product = 1;
            for(int varIdx = 0; varIdx < numVars; varIdx++)
            {
                var deg = (ulong)m.GetVarDeg(varIdx);
                if (deg == 0)
                    continue;
                

                var prev = variableFactorials[varIdx, deg - 1];

                if (deg != 1 && !seen.Contains((varIdx, (int)deg - 1)))
                    Debugger.Break();

                var curr = prev * (inputs[varIdx] - ((ulong)deg - 1));
                variableFactorials[varIdx, deg] = curr;
                product *= curr;

                seen.Add((varIdx, (int)deg));
            }

            return product;
        }


        

        private static SparsePolynomial Interpolate(SparsePolynomial poly)
        {
            //var bar = PolyInverter.Enumerate(new byte[] { 1, 1});

            var mmask = poly.moduloMask;
            var maxDeg = (int)GetMaxDegree(poly);
            var maxDegOld = (int)GetMaxDegree(poly);

            var w = BitOperations.PopCount(poly.moduloMask);
            maxDeg = Math.Min(maxDeg, w + 2);


            var varDegrees = Enumerable.Repeat(maxDeg, poly.numVars).ToArray();
            var numPoints = (int)GetNumPoints(poly.numVars, maxDeg);
            var monomials = Enumerable.Range(0, (int)GetNumPoints(varDegrees)).Select(midx => new Monomial(DensePolynomial.GetDegreesWithZeroes(midx, varDegrees).Select(x => (byte)x).ToArray())).Where(x => x.GetTotalDeg() <= maxDeg).OrderBy(x => x).ToArray();


            ulong mTotalDeg = 0;
            var maxDegs = new byte[poly.numVars];
            foreach(var m in poly.coeffs.Keys)
            {
                mTotalDeg = Math.Max(mTotalDeg, m.GetTotalDeg());
                for(int i = 0; i < poly.numVars; i++)
                {
                    // We need d+1 points
                    var max = (byte)(m.GetVarDeg(i) + 1);

                    maxDegs[i] = Math.Max(maxDegs[i], max);
                    maxDegs[i] = (byte)Math.Min(maxDegs[i], w + 2);
                }
            }

            var mSet = monomials.ToHashSet();
            bool diffMonomialAlgorith = false;
            if (diffMonomialAlgorith)
            {
                var allMs = PolyInverter.Enumerate(maxDegs, (byte)Math.Min(maxDegOld + 1, w + 2)).ToList();
                allMs.Sort();

                /*
                for(int i = 0; i < allMs.Count; i++)
                {
                    var a = allMs[i];
                    var b = monomials[i];
                    Console.WriteLine($"{a}, {b}, {a.value == b.value}, shared: {mSet.Contains(b)}");
                }
                */

                monomials = allMs.ToArray();
                numPoints = monomials.Length;

 
            }


            //var allMs = PolyInverter.Enumerate(varDegrees.Select(x => (byte)x).ToArray());

            //var me = Enumerable.Range(0, (int)GetNumPoints(varDegrees)).Select(midx => new Monomial(DensePolynomial.GetDegreesWithZeroes(midx, varDegrees).Select(x => (byte)x).ToArray())).ToList();

            // TODO: We should still be able to do divided differences
            // Don't delete the linear system code though, it's still useful
            var monomialValues = new ulong[monomials.Length];
            // The 0th monomial always evaluates to 1
            monomialValues[0] = 1;

            var debugSys = new List<Equation>();
            int numVars = poly.numVars;
            var stepBy = monomials[1].Degrees.ToArray();

            var xs = new ulong[numPoints];
            var ys = new ulong[numPoints];

            var variableFactorials = new ulong[numVars, maxDeg + 2];
            for (int i = 0; i < numVars; i++)
                variableFactorials[i, 0] = 1;

            for (int equationIdx = 0; equationIdx < numPoints; equationIdx++)
            {
                HashSet<(int, int)> seen = new();

                var inputs = monomials[equationIdx].Degrees.Select(x => (ulong)x).ToArray();
                var y = mmask & PolynomialEvaluator.Eval(poly, inputs);

                xs[equationIdx] = (inputs[0]);
                ys[equationIdx] = y;

                List<(ulong coeff, Monomial monomial)> terms = new();
                for (int midx = 0; midx < equationIdx + 1; midx++)
                {
                    var m = monomials[midx];
                    //var coeff = mmask & PolynomialEvaluator.EvalMonomial(m, inputs, false);
                    //var otherCoeff = mmask & MonomialFactorial(m, numVars, inputs, variableFactorials);
                    var coeff = mmask & MonomialFactorial(m, numVars, inputs, variableFactorials, seen); 

                    terms.Add((coeff, m));
                }

                var eq = new Equation(terms, y);
                debugSys.Add(eq);
            }


            var newEqs = new List<LinearEquation>();
            foreach (var eq in debugSys)
            {
                var newEq = new LinearEquation(numPoints);
                for (int i = 0; i < eq.Terms.Count; i++)
                    newEq.coeffs[i] = eq.Terms[i].coeff;
                newEq.result = eq.Result;
                newEqs.Add(newEq);
            }




            var system = new LinearSystem(poly.width, poly.width, newEqs);

            var solver = new LinearCongruenceSolver(poly.moduloMask);
            var (solvable, solutions) = LinearEquationSolver.EnumerateSolutionsIterative(system, solver, upperTriangular: false);

            bool divDiff = true;
            if (divDiff)
            {
                ulong[] divDiffCoeffs = null;

                bool mv = true;
                if (mv)
                {
                    divDiffCoeffs = DivDiffMv(mmask, solver, monomials.ToList(), ys);
                }

                else
                {
                    DivDiff(mmask, solver, xs, ys);
                }

                //if (!divDiffCoeffs.SequenceEqual(divDiffMv))
                //    Debugger.Break();

                var divDiffFactorial = new SparsePolynomial(numVars, poly.width);
                for (int i = 0; i < monomials.Length; i++)
                    divDiffFactorial.SetCoeff(monomials[i], divDiffCoeffs[i]);
                PolynomialReducer.ReduceFacBasisPolynomial(divDiffFactorial);
                return divDiffFactorial;
            }

            var newFactorialOutput = new SparsePolynomial(poly.numVars, poly.width);
            for (int i = 0; i < (int)numPoints; i++)
            {
                var coeff = solutions[i];
                if (coeff == 0)
                    continue;
                // coeff &= PolynomialReducer.GetReductionMask(poly.width, monomials[i])
                newFactorialOutput.SetCoeff(monomials[i], coeff);
            }

            PolynomialReducer.ReduceFacBasisPolynomial(newFactorialOutput);
            return newFactorialOutput;
            // Temporary perf optimization
            //return newFactorialOutput;

            return PolynomialReducer.GetCanonicalForm(newFactorialOutput);
        }



        // it makes perfect sense that you cant interpolate a divided difference polynomial of degree greater than width+1
        // because you can only have w+1 roots 
        public static void Test()
        {
            SparsePolynomial poly;

            /*
            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z", 3, 8);

            poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y", 2, 8);

            poly = SparsePolynomial.ParsePoly("0*x + 1*x + 3*x*x + 4*x*x*x + 5*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x", 1, 8);

            poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x", 1, 8);

            poly = SparsePolynomial.ParsePoly("0*x + 1*x + 3*x*x + 4*x*x*x + 5*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x", 1, 8);
            */

            poly = SparsePolynomial.ParsePoly("29346*x1*x1 + 31366*x0*x1*x1 + 19332*x0*x1*x1*x1*x1*x1 + 39528*x0*x1*x1*x1*x1*x1*x1*x1 + 21700*x0*x0*x0*x0*x0*x0*x0*x0*x1 + 22720*x0*x0*x1*x1*x1*x1*x1*x1*x1 + 13194*x0*x1*x1*x1*x1*x1*x1*x1*x1 + 8660*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1 + 31033*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1 + 55928*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0 + 7073*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1 + 15721*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0 + 60029*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1 + 6560*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1", 2, 16);

            poly = SparsePolynomial.ParsePoly("102298892079951287*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1 + 3932933059212809607*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1 + 3694306803266850138*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1 + 7407423151917946980*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 10782197172688550999*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 305408652823506908*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1 + 4705948077018839815*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1 + 15160716662651366749*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 15791129022230709057*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 3382657411119324047*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 18018818757867235811*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 1637081871908459885*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 14454731397411804089*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 5753820305880432739*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0 + 7847557181586505224*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1 + 13636649095598319947*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 4996223195234889934*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1 + 3314888205962197045*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1 + 12199316756886761094*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 10870935002739846246*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1 + 2843183390828820462*x0*x0*x0*x0*x0*x0*x0*x0*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1*x1", 2, 64);

            //var before = PolynomialReducer.Reduce(poly.Clone());
            //var after = Interpolate(poly.Clone());

            //poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z", 3, 8);


            poly = SparsePolynomial.ParsePoly("x + y", 2, 8);

            //poly = SparsePolynomial.ParsePoly("x*y", 2, 8);

            //poly = SparsePolynomial.ParsePoly("1 + 3*x + 17*x*x + 33*x*x*x", 1, 8);

            var before = PolynomialReducer.GetFactorialForm(poly.Clone());
            PolynomialReducer.ReduceFacBasisPolynomial(before);

            var after = Interpolate(poly.Clone());

            var mset1 = before.coeffs.Keys.ToHashSet();
            var mset2 = after.coeffs.Keys.ToHashSet();

            var diff1 = mset2.Except(mset1).ToList();
            var diff2 = mset1.Except(mset2).ToList();

            //var after = PolynomialReducer.Reduce(after.Clone());
            Console.WriteLine($"Equiv: {before.Equivalent(after)}");


            Console.WriteLine($"Before: {before}");
            Console.WriteLine($"After: {after}");

            //poly = SparsePolynomial
            

            Fuzz();

            Debugger.Break();
        }

        public static void Fuzz()
        {
            var rand = new SeededRandom();
            
            var p = GetRandomPoly(rand);


            p = new SparsePolynomial(4, 8);
            p.SetCoeff(new Monomial(8, 8, 8, 8), 1);

            p = new SparsePolynomial(2, 64);
            p.SetCoeff(new Monomial(32, 32), 1);

            while (false)
            {
                var sw = Stopwatch.StartNew();
                var after = Interpolate(p.Clone());
                sw.Stop();
                Console.WriteLine($"Took {sw.ElapsedMilliseconds} to interpolate poly");
            }
            

         
            for(int i = 0; i < 1000000; i++)
            {
                var poly = GetRandomPoly(rand);

                var sw = Stopwatch.StartNew();
                var before = PolynomialReducer.GetFactorialForm(poly.Clone());
                PolynomialReducer.ReduceFacBasisPolynomial(before);
                Console.WriteLine($"Took {sw.ElapsedMilliseconds} to reduce poly");
                sw.Restart();
                var after = Interpolate(poly.Clone());

                Console.WriteLine($"Took {sw.ElapsedMilliseconds} to interpolate poly");
                var equiv = before.Equivalent(after);
                Console.WriteLine($"Equiv: {equiv}");

                if (!equiv)
                {

                    var b4Str = poly.ToString();
                    var a4Str = SparsePolynomial.ParsePoly(b4Str, poly.numVars, poly.width);

                    var parseEquiv = poly.Equivalent(a4Str);
                    Console.WriteLine($"parseEquiv: {parseEquiv}");

                    Console.WriteLine($"\n{b4Str}\n\n!=\n\n{a4Str}");

                    Debugger.Break();
                }
            }

            Debugger.Break();
        }

        public static SparsePolynomial GetRandomPoly(SeededRandom rand)
        {
            var numVars = rand.Next(1, 3);

            numVars = 1;

            var numTerms = rand.Next(10, 30);
            // Pick the width of the output expression...
            int width = rand.Next(0, 4) switch
            {
                0 => 8,
                1 => 16,
                2 => 32,
                3 => 64,
            };

            var poly = new SparsePolynomial(numVars, (byte)width);

            var maxDeg = width + 2;
            for(int _ = 0; _ < numTerms; _++)
            {
                // Pick a coefficient
                var coeff = rand.GetRandUlong();

                // Pick a monomial
                var leftOver = maxDeg;
                var degrees = new byte[numVars];
                for (int i = 0; i < numVars; i++)
                {
                    degrees[i] = (byte)rand.Next(0, leftOver);
                    leftOver -= degrees[i];
                }
                var m = new Monomial(degrees);
                poly.Sum(m, coeff);
            }

            return poly;
        }


        public static ulong[] DivDiffMv(ulong mmask, LinearCongruenceSolver solver, List<Monomial> x, ulong[] y)
        {

        }

        public static ulong[] DivDiffMvOld(ulong mmask, LinearCongruenceSolver solver, List<Monomial> x, ulong[] y)
        {
            


            var coeffs = y.ToArray();
            var n = x.Count;
            for (int j = 1; j < n; j++)
            {
                Console.WriteLine();
                for (int i = n - 1; i >= j; i--)
                {
                    //coeffs[i] = (coeffs[i] - coeffs[i - 1]) / (x[i] - x[i - j]);

                    // (coeffs[n] - coeffs[n - 1]
                    //  / 
                    // x[i] - x[i - j]

                    //var oldMonomial = x[i - j];
                    var oldMonomial = x[j];
                    var m = x[i];

                    bool isMultiple = true;
                    for (int varIdx = 0; varIdx < m.Degrees.Count; varIdx++)
                    {
                        var prevDeg = oldMonomial.Degrees[varIdx];
                        var currDeg = m.Degrees[varIdx];
                        // Skip if they're both zero
                        if (prevDeg == 0 && currDeg == 0)
                        {
                            isMultiple = false;
                            break;
                        }

                        
                        // If the previous degree was zero, its not a multiple..
                        if (prevDeg == 0)
                        {
                            isMultiple = false;
                            break;
                        }


                        // If the previous degree was zero, its not a multiple..
                        if (currDeg == 0)
                        {
                            isMultiple = false;
                            break;
                        }
                    }

                    if ((i - j) == 0)
                        isMultiple = true;

                    Console.WriteLine($"({i}, {j}), {oldMonomial}, {m}");
                    if (!isMultiple)
                        continue;

                    ulong product = 1;
                    for(int varIdx = 0; varIdx < m.Degrees.Count; varIdx++)
                    {
                        // x[i]
                        var deg = m.Degrees[varIdx];
                        if (deg == 0)
                            continue;

                        // x[i-j
                        var oldDeg = oldMonomial.Degrees[varIdx];

                        var diff = (ulong)deg - oldDeg;

                        product *= diff;
      
                    }


                    product &= mmask;

                    //coeffs[i] = mmask & Mdiv(mmask, solver, (coeffs[i] - coeffs[i - 1]), (x[i] - x[i - j])).Item1;
                    coeffs[i] = mmask & Mdiv(mmask, solver, (coeffs[i] - coeffs[i - 1]), product).Item1;
                }
            }

            return coeffs;
        }

        public static ulong[] DivDiff(ulong mmask, LinearCongruenceSolver solver, ulong[] x, ulong[] y)
        {
            var coeffs = y.ToArray();
            var n = x.Length;
            for (int j = 1; j < n; j++)
            {
                for (int i = n - 1; i >= j; i--)
                {
                    //coeffs[i] = (coeffs[i] - coeffs[i - 1]) / (x[i] - x[i - j]);

                    // (coeffs[n] - coeffs[n - 1]
                    //  / 
                    // x[i] - x[i - j]

                    coeffs[i] = mmask & Mdiv(mmask, solver, (coeffs[i] - coeffs[i - 1]), (x[i] - x[i - j])).Item1;
                }
            }

            return coeffs;
        }

        private static ulong GCD(ulong a, ulong b)
        {
            while (a != 0 && b != 0)
            {
                if (a > b)
                    a %= b;
                else
                    b %= a;
            }

            return a | b;
        }

        // 12/29/2025: If you have (even/even), e.g. (2/96), divide by gc of modulus and gets 1/48?
        private static (ulong, bool) Mdiv(ulong mmask, LinearCongruenceSolver solver, ulong a, ulong b)
        {
            a &= mmask;
            b &= mmask;

            if (b % 2 != 0)
            {
                var inv = GetModularInverse(solver, mmask, b).Value;
                return (mmask & (a * inv), false);
            }


            if (a == 0 || b == 0)
                return (0, false);

            var possibleLc = solver.LinearCongruence(b, a, (UInt128)mmask + 1);
            if (possibleLc != null)
            {
                var cand = (ulong)solver.GetSolution(0, possibleLc);
                return (cand, false);
                Debugger.Break();
            }


            var tzcnt = (ushort)BitOperations.TrailingZeroCount(b);
            var shiftedB = b >> tzcnt;

            //var coeff = GetModularInverse(solver, mmask, shiftedB).Value;




            //var gcd = GCD(b, mmask + 1);


            //Debugger.Break();




            if ((a % 2) == 0 && (b % 2) == 0)
            {
                if (b > a)
                {
                    var gcd1 = GCD(a, mmask + 1);
                    var gcd2 = GCD(b, mmask + 1);
                    var gcd = Math.Min(gcd1, gcd2);

                    var aShift = a >> BitOperations.TrailingZeroCount(gcd);
                    var bShift = b >> BitOperations.TrailingZeroCount(gcd);

                    Debug.Assert((bShift % 2) != 0);

                    var inv = GetModularInverse(solver, mmask, bShift);

                    var sol = mmask & (gcd * inv);

                    return (sol.Value, false);
                }

                else
                {
                    var gcd = GCD(a, b);
                    if (gcd != b)
                    {
                        var gcd1 = GCD(a, mmask + 1);
                        var gcd2 = GCD(b, mmask + 1);
                        gcd = Math.Min(gcd1, gcd2);

                        // 25 / 2
                        // => (2 / 164)
                        // => 1/82
                        // =?
                        var aShift = a >> BitOperations.TrailingZeroCount(gcd);
                        var bShift = b >> BitOperations.TrailingZeroCount(gcd);

                        var lcfinal = solver.LinearCongruence(aShift, bShift, mmask + 1);

                        if ((bShift % 2) == 0)
                        {
                            goto igiveup;
                            var bestSol = solver.GetSolution(0, lcfinal);

                            Debugger.Break();
                        }

                        Debug.Assert((bShift % 2) != 0);


                        var inv = GetModularInverse(solver, mmask, bShift);

                        var sol = mmask & (gcd * inv);

                        //Debugger.Break();

                        return (sol.Value, false);
                    }

                    // Otherwise a is a multiple of b
                    return (a / b, false);
                }

                //Debugger.Break();
            }


        igiveup:


            // if (a > 255 || b > 255)
            //    Debugger.Break();

            // var div = mmask & (a / b);
            ulong div = 0;
            if (a == 0 && b == 0)
            {
                // Probably illegal?
                div = 0;

            }

            else
            {
                div = mmask & (a / b);
            }

            var undo = mmask & (div * b);

            bool valid = undo == a;
            var s = valid ? "GOOD" : "BAD";
            //Console.WriteLine($"{s}: {a} / {b}");

            // if (!valid && (b % 2) == 0)
            //     Debugger.Break();


            /*
             *  var lc = solver.LinearCongruence(a, div, (UInt128)mmask + 1);
            if (lc == null || lc.d == 0)
            {
                Debugger.Break();
            }
  

            // If the
            if(lc != null)
            {
                //return div;
                var solution = (ulong)solver.GetSolution(0, lc);
                Debug.Assert((mmask & (solution * a)) == div);
                return solution;
                //Debugger.Break();
            }

            else
            {
                //Debugger.Break();
            }
                      */


            if (undo != a)
            //if (false)
            {
                // If the divisor has a modular inverse, rewrite as division.
                var inverse = GetModularInverse(solver, mmask, b);
                if (inverse != null)
                {
                    div = mmask & (inverse.Value * a);
                    return (div, false);
                }

                // If the divisor is even, can we rewrite this as a linear congruence?
                // e.g. if coeff == (58/6),
                // reformulate it as 6*coeff == 58
                //var lc = solver.LinearCongruence(a, b, (UInt128)mmask + 1); // originally worked
                var lc = solver.LinearCongruence(b, a, (UInt128)mmask + 1);
                if (lc == null || lc.d == 0)
                {


                    //var other = solver.LinearCongruence(b, a, (UInt128)mmask + 1);

                    // Still if we have e.g. c = 81/12, there may be no solution
                    // Shifting terms around yields c*12 = 81, which is unsatisfiable.
                    // But because 81 is odd, we can arbitrarily change the coeff...


                    // Solve for c1*a == b
                    var target = b;
                    lc = solver.LinearCongruence(a, b, (UInt128)mmask + 1);

                    // All of this is extremely dubious at best..
                    if (lc == null || lc.d == 0)
                    {
                        Debugger.Break();
                        throw new InvalidOperationException();
                    }

                    var sol = (ulong)solver.GetSolution(0, lc);


                    // now we have c1*x == 1
                    var lhs = mmask & (sol * b);
                    var rhs = mmask & (sol * a);

                    // Absolutely completely incorrect for some cases
                    inverse = GetModularInverse(solver, mmask, rhs);
                    div = mmask & (inverse.Value * lhs);
                    return (div, false);


                    return (sol, false);
                }

                var solution = (ulong)solver.GetSolution(0, lc);
                return (solution, false);

            }

        done:
            return (div, false);
        }

        private static ulong? GetModularInverse(LinearCongruenceSolver congruenceSolver, ulong moduloMask, ulong coeff)
        {
            var lc = congruenceSolver.LinearCongruence((UInt128)coeff, 1, (UInt128)moduloMask + 1);
            if (lc == null)
                return null;
            if (lc.d == 0)
                return null;

            return (ulong)congruenceSolver.GetSolution(0, lc);
        }


        private static void NewtonToMonomial(SparsePolynomial poly, List<Monomial> monomials)
        {
            var n = monomials.Count;
            var r = new ulong[n];
            for (int i = 0; i < monomials.Count; i++)
                r[i] = poly.GetCoeff(monomials[i]);

            for (int i = n - 2; i >= 0; i--)
            {
                for (int j = i; j < n - 1; j++)
                {
                    r[j] -= r[j + 1] * GetDegreeProduct(monomials[i]);
                    r[j] &= poly.moduloMask;
                }
            }

            poly.Clear();
            for (int i = 0; i < monomials.Count; i++)
                poly[monomials[i]] = r[i];

        }

        private static void MonomialToNewton(SparsePolynomial poly, List<Monomial> monomials)
        {
            var n = monomials.Count;
            var r = new ulong[n];
            for (int i = 0; i < monomials.Count; i++)
                r[i] = poly.GetCoeffOrZero(monomials[i]);

            for(int i = 0; i < n - 1; i++)
            {
                for (int j = n - 2; j >= i; j--)
                {
                    r[j] += r[j + 1] * GetDegreeProduct(monomials[i]);
                    r[j] &= poly.moduloMask;
                }
            }

            poly.Clear();
            for (int i = 0; i < monomials.Count; i++)
                poly[monomials[i]] = r[i];

        }

        private static ulong GetDegreeProduct(Monomial monomial)
        {
            ulong product = 1;
            foreach (var root in monomial.Degrees)
                product *= root;
            return product;
        }


        private static uint GetMaxDegree(SparsePolynomial poly)
        {
            return poly.coeffs.Keys.MaxBy(x => x.GetTotalDeg()).GetTotalDeg();
        }

        private static ulong GetNumPoints(int n, int d)
        {
            var a = PolynomialReducer.Factorial(n + d);
            var b = (PolynomialReducer.Factorial(d) * PolynomialReducer.Factorial(n));

            var r = a / b;
            return (ulong)r;
        }

        // Compute the number of points uniquely determining a multivariate polynomial
        private static ulong GetNumPoints(int[] varDegs)
        {
            ulong product = 1;
            foreach (var d in varDegs)
            {
                product *= ((ulong)d + 1);
            }

            return product;
        }
    }
}
