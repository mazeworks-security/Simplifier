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

        public static void Test()
        {
            //GetNewtonMonomialStr()
            var poly = SparsePolynomial.ParsePoly("x + y + x*y  ", 2, 8);

            poly = SparsePolynomial.ParsePoly("x*y", 2, 8);

            poly = SparsePolynomial.ParsePoly("x + y + x*y", 2, 8);

            //poly = SparsePolynomial.ParsePoly("x + y + x*y + x*x*x*x*y", 2, 8);

            poly = SparsePolynomial.ParsePoly("x*x*y", 2, 8);

            poly = SparsePolynomial.ParsePoly("y + x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x", 2, 8);

            poly = SparsePolynomial.ParsePoly("x*y", 2, 8);

            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y", 2, 8);


            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z", 3, 8);

            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + z", 3, 8);

            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z + 33*x*x*x*x*x + 3443*x*x*x*z*z*y", 3, 8);

            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z + 33*x*x*x*x*x + 3443*x*x*x*z*z*y", 3, 8);


            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y", 2, 8);

            // Broiken
            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z", 3, 8);
            poly = SparsePolynomial.ParsePoly("2 + 4*x + 8*y + 16*x*y", 2, 8);
            poly = SparsePolynomial.ParsePoly("x + y + z", 3, 8);

            poly = SparsePolynomial.ParsePoly("x*y*z", 3, 8);
            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y", 2, 8); // works

            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z", 3, 8);
            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z + 33*x*x*x*x*x + 3443*x*x*x*z*z*y", 3, 8);


            poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y", 2, 8);
            poly = SparsePolynomial.ParsePoly("x*y*z", 3, 8);
            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z + 33*x*x*x*x*x + 3443*x*x*x*z*z*y", 3, 8);
            poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x", 1, 8);

            poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y", 2, 8);

            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z + 33*x*x*x*x*x + 3443*x*x*x*z*z*y", 3, 8);

            poly = SparsePolynomial.ParsePoly("1143416480 + 1792289334*x0 + 1400439363*x1 + 1549354901*x2 + 750794788*x0*x1 + 227753240*x0*x2 + 1915127299*x1*x2 + 1672049526*x0*x0 + 1827198538*x1*x1 + 1408829269*x2*x2 + 1710567261*x0*x1*x2 + 21157709*x0*x0*x1 + 1113710701*x0*x0*x2 + 40185026*x0*x1*x1 + 159464183*x0*x2*x2 + 1297690672*x1*x1*x2 + 829342554*x1*x2*x2 + 1748266395*x0*x0*x0 + 474011095*x1*x1*x1 + 2076924414*x2*x2*x2 + 69212338*x0*x0*x1*x2 + 530993515*x0*x1*x1*x2 + 1420726564*x0*x1*x2*x2 + 2077245454*x0*x0*x0*x1 + 1887748253*x0*x0*x0*x2 + 1668604664*x0*x0*x1*x1 + 1375091916*x0*x0*x2*x2 + 193565932*x0*x1*x1*x1 + 1440319644*x0*x2*x2*x2 + 166847441*x1*x1*x1*x2 + 661804695*x1*x1*x2*x2 + 361173395*x1*x2*x2*x2 + 999045089*x0*x0*x0*x0 + 255405560*x1*x1*x1*x1 + 1878554461*x2*x2*x2*x2 + 514981880*x0*x0*x0*x1*x2 + 1304883535*x0*x0*x1*x1*x2 + 897376920*x0*x0*x1*x2*x2 + 625678132*x0*x1*x1*x1*x2 + 1586249817*x0*x1*x1*x2*x2 + 1292251793*x0*x1*x2*x2*x2 + 1106046332*x0*x0*x0*x0*x1 + 797630856*x0*x0*x0*x0*x2 + 968433722*x0*x0*x0*x1*x1 + 2033723153*x0*x0*x0*x2*x2 + 293095893*x0*x0*x1*x1*x1 + 91305014*x0*x0*x2*x2*x2 + 912758096*x0*x1*x1*x1*x1 + 33195109*x0*x2*x2*x2*x2 + 612494358*x1*x1*x1*x1*x2 + 70839255*x1*x1*x1*x2*x2 + 1178724485*x1*x1*x2*x2*x2 + 310065099*x1*x2*x2*x2*x2 + 618485120*x0*x0*x0*x0*x0 + 1691004408*x1*x1*x1*x1*x1 + 1031255725*x2*x2*x2*x2*x2 + 882046461*x0*x0*x0*x0*x1*x2 + 1448601662*x0*x0*x0*x1*x1*x2 + 1639255646*x0*x0*x0*x1*x2*x2 + 1862053245*x0*x0*x1*x1*x1*x2 + 1599996559*x0*x0*x1*x1*x2*x2 + 1384284621*x0*x0*x1*x2*x2*x2 + 917494271*x0*x1*x1*x1*x1*x2 + 2119693603*x0*x1*x1*x1*x2*x2 + 975152729*x0*x1*x1*x2*x2*x2 + 1983089818*x0*x1*x2*x2*x2*x2 + 777238427*x0*x0*x0*x0*x0*x1 + 973774198*x0*x0*x0*x0*x0*x2 + 850590070*x0*x0*x0*x0*x1*x1 + 1511250365*x0*x0*x0*x0*x2*x2 + 981390553*x0*x0*x0*x1*x1*x1 + 590764770*x0*x0*x0*x2*x2*x2 + 313160869*x0*x0*x1*x1*x1*x1 + 223991418*x0*x0*x2*x2*x2*x2 + 1941890719*x0*x1*x1*x1*x1*x1 + 1487330771*x0*x2*x2*x2*x2*x2 + 973899586*x1*x1*x1*x1*x1*x2 + 342071561*x1*x1*x1*x1*x2*x2 + 228372049*x1*x1*x1*x2*x2*x2 + 954124928*x1*x1*x2*x2*x2*x2 + 231947527*x1*x2*x2*x2*x2*x2 + 446364404*x0*x0*x0*x0*x0*x0 + 36485981*x1*x1*x1*x1*x1*x1 + 307062429*x2*x2*x2*x2*x2*x2", 3, 8);

            poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y", 2, 8);

            poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y", 2, 8);
            poly = SparsePolynomial.ParsePoly("2*x + 2*y", 2, 8);
            // Causes stackoverflow!
            poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y", 2, 8);

            //poly = SparsePolynomial.ParsePoly("x + y + x*y", 2, 8);
            poly = SparsePolynomial.ParsePoly("x*x*x", 1, 8);

            poly = SparsePolynomial.ParsePoly("3*x + 4*x*x + 7*x*x*x + 25*x*x*x*x + 34234*x*x*x*x*x*x", 1, 8);

            poly = SparsePolynomial.ParsePoly("x*y", 2, 8);

            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z", 3, 8);

            poly = SparsePolynomial.ParsePoly("x*x*x", 1, 8);

            poly = SparsePolynomial.ParsePoly("17 + 233*x + 323*y + 34*x*y + 343434*x*y*z", 3, 8);

            Console.WriteLine($"Input: {poly}");

      
            var mmask = poly.moduloMask;

            var maxDeg = (int)GetMaxDegree(poly);
            var varDegrees = Enumerable.Repeat(maxDeg, poly.numVars).ToArray();
            var numPoints = GetNumPoints(poly.numVars, maxDeg);
            var monomials = Enumerable.Range(0, (int)GetNumPoints(varDegrees)).Select(midx => new Monomial(DensePolynomial.GetDegreesWithZeroes(midx, varDegrees).Select(x => (byte)x).ToArray())).Where(x => x.GetTotalDeg() <= maxDeg).OrderBy(x => x).ToArray();

            var rand = new Random();
            foreach(var monomial in monomials)
            {
              //  Console.Write($"{(ulong)rand.Next()}*{monomial.ToString(canonicalBasis: true)} + ");
            }

            bool log = false;


            //var sortedMonomials = new (byte, byte)[] { (0, 0), (0, 1), (1, 0), (1,1), (2, 0), (0, 2) };
            //monomials = sortedMonomials.Select(x => new Monomial(x.Item1, x.Item2)).ToArray();

            // There will be times where we cannot plug in zero
            var equations = new List<LinearEquation>();


            var realInputs = new List<ulong[]>()
            {
                new ulong[] { 1, 2},
                new ulong[] { 2, 2},
                new ulong[] { 1, 3},
                //new ulong[] { 1, 2},
            };

            realInputs = new List<ulong[]>()
            {
                new ulong[] { 1, 2},
                new ulong[] { 2, 2},
                new ulong[] { 1, 3},
                new ulong[] { 2, 3},
                new ulong[] { 3, 2},
                new ulong[] { 2, 4},
               // new ulong[] { 0, 0},
               // new ulong[] { 0, 0},
                //new ulong[] { 1, 2},
            };


            // Values of e.g. x0, x1, x2, x3, ...
            var variableAssignments = new ulong[poly.numVars, numPoints];

            // Initially assign each variable to an increasing value.
            for (int i = 0; i < poly.numVars; i++)
                variableAssignments[i, 0] = 1 + (ulong)i;

           // variableAssignments[0, 0] = 0;
            //variableAssignments[1, 0] = 1;

            // What index a variable is currently assigned to.
            //  Aka the value of `xk`.
            //var variableIterations = new ulong[poly.numVars];
            var variableIterations = Enumerable.Repeat(0ul, poly.numVars).ToArray();


            var eqs = new List<Equation>();

            var initialValues = new ulong[poly.numVars];
            var vValues = new ulong[poly.numVars];
            // Initially assign each variable to an increasing value.
            for (int i = 0; i < poly.numVars; i++)
            {
                //vValues[i] = 1 + (ulong)i;
                vValues[i] = 0;
                initialValues[i] = vValues[i];
            }

            var roots = new List<ulong[]>();
            int limit = (int)numPoints;
            // Alternatively just try generating the system.
            for (int equationIdx = 0; equationIdx < (int)limit; equationIdx++)
            {
                var addedMonomial = monomials[equationIdx];
                for(int varIdx = 0; varIdx < addedMonomial.Degrees.Count; varIdx++)
                {
                    if (addedMonomial.Degrees[varIdx] == 0)
                        continue;

                    // Increment a variables value when we actually need it?
                    vValues[varIdx] += 1;
                }

                //if (equationIdx == limit - 1)
                //    Debugger.Break();

                //if (equationIdx == 2)
                //    Debugger.Break();

                var inputs = new ulong[vValues.Length];
                for (int varIdx = 0; varIdx < addedMonomial.Degrees.Count; varIdx++)
                {
                    // If this monomial is undemanded, cancel it out.
                    if (addedMonomial.Degrees[varIdx] == 0)
                    {
                        var prevMax = (long)initialValues[varIdx];
                        foreach (var m in monomials.Take(equationIdx))
                        {
                            if (m.Degrees[varIdx] == 0)
                                continue;
                            prevMax = Math.Max(prevMax, (long)m.Degrees[varIdx] - 1);
                        }


                        //inputs[varIdx] = (ulong)prevMax;

                        inputs[varIdx] = 0;
                        continue;
                    }

                    inputs[varIdx] = initialValues[varIdx] + addedMonomial.Degrees[varIdx];
                }


                //vValues = realInputs[equationIdx].ToArray();


                // Compute the result of evaluating this poly.
                // c0*1 + c1*(x - 1) + c2*(y-2) =
                // When evaluating c2, we need to give it a value that cancels out c1..
                // The highest last x that was seen..
                roots.Add(inputs);
                var y = mmask & PolynomialEvaluator.Eval(poly, inputs);

                List<(ulong coeff, Monomial monomial)> terms = new();

                var sb = new StringBuilder();
                for (int midx = 0; midx < equationIdx + 1; midx++)
                {
                    var monomial = monomials[midx];
                    ulong product = 1;
                    for(int vIdx = 0; vIdx < monomial.Degrees.Count; vIdx++)
                    {
                        var deg = monomial.Degrees[vIdx];
                        if (deg == 0)
                            continue;
                        var name = nameTable[vIdx];

                        for(int i = 0; i < deg; i++)
                        {
                            var x = inputs[vIdx];
                            var x0 = initialValues[vIdx];

                            var sum = (x - (x0 + (Num)i));
                            product *= sum;

                            if(log)
                                sb.Append($"({x} - {x0} + {i})*");
                        }
                    }

                    if (log)
                        sb.Append(", ");

                    product &= mmask;
                    terms.Add((product, monomial));
                }

                if (log)
                    Console.WriteLine(sb);

                var eq = new Equation(terms, y);
                eqs.Add(eq);

                if (log)
                {
                    var strI = String.Join(", ", inputs);
                    Console.WriteLine($"{eq} on inputs {strI}");
                }
            }



            var newEqs = new List<LinearEquation>();
            foreach(var eq in eqs)
            {
                var newEq = new LinearEquation(limit);
                for (int i = 0; i < eq.Terms.Count; i++)
                    newEq.coeffs[i] = eq.Terms[i].coeff;
                newEq.result = eq.Result;

                newEqs.Add(newEq);
            }

            var newSystem = new LinearSystem(poly.width, poly.numVars, newEqs);
            var newSolver = new LinearCongruenceSolver(poly.moduloMask);

 
            var (newFoundSolution, newSolutionMap) = LinearEquationSolver.EnumerateSolutionsIterative(newSystem, newSolver, upperTriangular: false);

            //var newSolutionMap = new ulong[limit];
            //var newFoundSolution = LinearEquationSolver.EnumerateSolutions(newSystem, newSolver, newSolutionMap, 0, upperTriangular: false);
            if (!newFoundSolution)
                throw new InvalidOperationException("Unsolvable system!");

            var newFactorialOutput = new SparsePolynomial(poly.numVars, poly.width);
            for (int i = 0; i < (int)numPoints; i++)
            {
                var coeff = newSolutionMap[i];
                //var rcoeff = PolynomialReducer.GetReductionMask(poly.width, monomials[i]) & coeff;
                var rcoeff = coeff;
                newFactorialOutput.SetCoeff(monomials[i], rcoeff);
            }

            PolynomialReducer.ReduceFacBasisPolynomial(newFactorialOutput);


            var probEquiv = CheckEquiv(poly, true, newFactorialOutput, false);
            Console.WriteLine($"Equivalent: {probEquiv}");

            Console.WriteLine($"Expected result: {PolynomialReducer.Reduce(poly.Clone())}");

            NewtonToMonomial(newFactorialOutput, monomials.ToList());


            var clone = poly.Clone();
            MonomialToNewton(clone, monomials.ToList());
            NewtonToMonomial(clone, monomials.ToList());
            Debugger.Break();
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
