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


        public static ulong MonomialFactorial(Monomial m, int numVars, ulong[] inputs, ulong[,] variableFactorials)
        {
            ulong product = 1;
            for(int varIdx = 0; varIdx < numVars; varIdx++)
            {
                var deg = (ulong)m.GetVarDeg(varIdx);
                if (deg == 0)
                    continue;
                

                var prev = variableFactorials[varIdx, deg - 1];

                var curr = prev * (inputs[varIdx] - ((ulong)deg - 1));
                variableFactorials[varIdx, deg] = curr;
                product *= curr;
            }

            return product;
        }

        private static SparsePolynomial Interpolate(SparsePolynomial poly)
        {
            var mmask = poly.moduloMask;
            var maxDeg = (int)GetMaxDegree(poly);


            var w = BitOperations.PopCount(poly.moduloMask);
            maxDeg = Math.Min(maxDeg, w + 2);


            var varDegrees = Enumerable.Repeat(maxDeg, poly.numVars).ToArray();
            var numPoints = (int)GetNumPoints(poly.numVars, maxDeg);
            var monomials = Enumerable.Range(0, (int)GetNumPoints(varDegrees)).Select(midx => new Monomial(DensePolynomial.GetDegreesWithZeroes(midx, varDegrees).Select(x => (byte)x).ToArray())).Where(x => x.GetTotalDeg() <= maxDeg).OrderBy(x => x).ToArray();

            var me = Enumerable.Range(0, (int)GetNumPoints(varDegrees)).Select(midx => new Monomial(DensePolynomial.GetDegreesWithZeroes(midx, varDegrees).Select(x => (byte)x).ToArray())).ToList();

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

            var variableFactorials = new ulong[numVars, maxDeg + 1];
            for (int i = 0; i < numVars; i++)
                variableFactorials[i, 0] = 1;

            for (int equationIdx = 0; equationIdx < numPoints; equationIdx++)
            {
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
                    var coeff = mmask & MonomialFactorial(m, numVars, inputs, variableFactorials); 

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

            // Temporary perf optimization
            return newFactorialOutput;

            return PolynomialReducer.GetCanonicalForm(newFactorialOutput);
        }



        // it makes perfect sense that you cant interpolate a divided difference polynomial of degree greater than width+1
        // because you can only have w+1 roots 
        public static void Test()
        {
            SparsePolynomial poly;
            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z", 3, 8);

            poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y", 2, 8);

            poly = SparsePolynomial.ParsePoly("0*x + 1*x + 3*x*x + 4*x*x*x + 5*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x", 1, 8);

            poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x", 1, 8);

            poly = SparsePolynomial.ParsePoly("0*x + 1*x + 3*x*x + 4*x*x*x + 5*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x", 1, 8);

            /*
            var before = PolynomialReducer.Reduce(poly.Clone());
            var after = Interpolate(poly.Clone());
            Console.WriteLine($"Equiv: {before.Equivalent(after)}");
            */
            Fuzz();

            Debugger.Break();
        }

        public static void Fuzz()
        {
            var rand = new SeededRandom();
            var p = GetRandomPoly(rand);


            p = new SparsePolynomial(4, 8);
            p.SetCoeff(new Monomial(8, 8, 8, 8), 1);
            while(true)
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
                var before = PolynomialReducer.Reduce(poly.Clone());
                Console.WriteLine($"Took {sw.ElapsedMilliseconds} to reduce poly");
                sw.Restart();
                var after = Interpolate(poly.Clone());

                Console.WriteLine($"Took {sw.ElapsedMilliseconds} to interpolate poly");
                Console.WriteLine($"Equiv: {before.Equivalent(after)}");
            }

            Debugger.Break();
        }

        public static SparsePolynomial GetRandomPoly(SeededRandom rand)
        {
            var numVars = rand.Next(1, 3);
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
