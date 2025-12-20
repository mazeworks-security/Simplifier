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
        public static void Test()
        {
            var data = new List<Point>() { new(1, 3), new(4,5), new(5,6), new(6,8), new Point(7,8) };

            data = new List<Point>() { new(1, 1), new(2, 5) };

            data = new List<Point>() { new(1, 1), new(2, 5), new(3, 2) };

            data = new List<Point>() { new(1, 1), new(2, 5), new(3, 2), new(3.2, 7), new(3.9, 4) };

            var table = new List<Num>();
            for(int i = 0; i< data.Count; i++)
            {
                BuildTable2(i, data, table);
            }

            Debugger.Break();

        }

        public static uint MAXDEG = 65;

        static string[] nameTable = new string[] { "x", "y", "c", "d"};

        public static void NewClassic()
        {
            var ms = new List<Monomial>() { new(1, 0), new(0,1) };
            ms.Sort();

            var poly = new SparsePolynomial(1, (byte)8);
            poly.SetCoeff(new Monomial(2, 3), 1);

            poly = new SparsePolynomial(1, (byte)8);
            //poly.SetCoeff(new Monomial(2), 1); // works
            poly.SetCoeff(new Monomial(10), 1); // works

            // works
            poly = new SparsePolynomial(2, (byte)8);
            poly.SetCoeff(new Monomial(1, 0), 1);
            poly.SetCoeff(new Monomial(0, 1), 1);

            poly = new SparsePolynomial(2, (byte)8);
            poly.SetCoeff(new Monomial(1, 1), 1);

            //poly = SparsePolynomial.ParsePoly("x + y*y", 1, 8);

            //poly = SparsePolynomial.ParsePoly("64 + 224*x + 64*x*x + 212*x*x*x*x*x + 205*x*x*x*x*x*x*x", 1, 8);
            //poly = SparsePolynomial.ParsePoly("x*x*x", 1, 8);

            //poly = SparsePolynomial.ParsePoly("64 + 224*x", 1, 8);
            //var reduced = PolynomialReducer.Reduce(poly);

            var mmask = poly.moduloMask;

            // Compute the max degree of each variable
            var maxDeg = (int)GetMaxDegree(poly);
            var varDegrees = Enumerable.Repeat(maxDeg, poly.numVars).ToArray();
            //var varDegrees = GetVarDegrees(poly);

            // Compute the number of points uniquely defining the polynomial
            //var numPoints = GetNumPoints(varDegrees);
            var numPoints = GetNumPoints(poly.numVars, maxDeg);

            // Enumerate through each point.
            ulong count = 0;

            /*
            var coeffMatrix = new ulong[numPoints, numPoints];
            var resultVector = new ulong[numPoints];
            */
            var equations = new List<LinearEquation>();





            //var allDegs = Enumerable.Range(0, (int)numPoints).Select(midx => (DensePolynomial.GetDegreesWithZeroes(midx, varDegrees).Select(x => (byte)x).ToArray())).ToArray();
            //var monomials = Enumerable.Range(0, (int)numPoints).Select(midx => new Monomial(DensePolynomial.GetDegreesWithZeroes(midx, varDegrees).Select(x => (byte)x).ToArray())).OrderBy(x => x).ToArray();
            var monomials = Enumerable.Range(0, (int)GetNumPoints(varDegrees)).Select(midx => new Monomial(DensePolynomial.GetDegreesWithZeroes(midx, varDegrees).Select(x => (byte)x).ToArray())).Where(x => x.GetTotalDeg() <= maxDeg).OrderBy(x => x).ToArray();

            // x3-x0, (x3-x0)*(x3-x1), (x3-x0)*(x3-x1)*(x3-x2
            // )


            // Bivariate case:
            // 1, x1-x0
            // 1  y1-y0
            // 1  (x2-x0)


            var x = new List<ulong>();

            var varSeen = Enumerable.Repeat(0, poly.numVars).ToArray();
            bool[] hasSeen = Enumerable.Repeat(false, poly.numVars).ToArray();
           
            for (int i = 0; i < (int)numPoints; i++)
            {
                var cDeg = monomials[i].Degrees;

                for (int degIdx = 0; degIdx < cDeg.Count; degIdx++)
                {
                    if (cDeg[degIdx] != 0 && !hasSeen[degIdx])
                        varSeen[degIdx] += 1;
                }

                x.Add(count);
                var eq = new LinearEquation((int)numPoints);

                // Compute unique inputs for these variables.
                /*
                var inputs = new ulong[poly.numVars];
                for(int vi = 0;  vi < poly.numVars; vi++)
                    inputs[vi] = mmask & count;
                */

                var inputs = varSeen.Select(x => (ulong)x).ToArray();

                // Note that we reuse the same input for [x0, x1, ...]
                // This makes our basis technically both a newton and falling factorial basis.. which is useful.

                count++;

                var sb = new StringBuilder();


                // See Multivariate Newton Generalization.txt
                var inputStr = String.Join(", ", inputs);
                for (int midx = 0; midx < i + 1; midx++)
                {
                    ulong coeff = 1;                   
                    var baseFunction = monomials[midx];

                    if (midx == 0)
                    {
                        sb.Append($"1, ");
                    }

                    else
                    {

                        var degrees = baseFunction.Degrees;
                        for (int degIdx = 0; degIdx < degrees.Count; degIdx++)
                        {
                            var deg = degrees[degIdx];
                            // Skip degree zero
                            if (deg == 0)
                                continue;

                            var seenI = varSeen[degIdx];
                            hasSeen[degIdx] = true;
                            //varSeen[degIdx] += 1;
                            // var seenI = i;


                            var name = nameTable[degIdx];
                            for (int vIdx = 0; vIdx < deg; vIdx++)
                            {
                                sb.Append($"({name}{seenI}-{name}{vIdx})");
                                if (vIdx != midx - 1)
                                    sb.Append("*");

                                coeff *= (x[seenI] - x[vIdx]);
                            }

                        }

                        sb.Append(", ");
                    }


                    /*
                    ulong coeff = 1;
                    var iArray = new List<ulong>();
                    if(midx == 0)
                    {
                        iArray.Add(1);
                        sb.Append($"1, ");
                    }

                    else
                    {
                        for(int vIdx = 0; vIdx < midx; vIdx++)
                        {
                            sb.Append($"(x{i}-x{vIdx})");
                            if (vIdx != midx - 1)
                                sb.Append("*");

                            coeff *= (x[i] - x[vIdx]); 
                        }

                        sb.Append(", ");
                    }
                    */

                    // Compute the monomial at index mi
                    //var mDegs = DensePolynomial.GetDegreesWithZeroes(midx, varDegrees).Select(x => (byte)x).ToArray();
                    //var monomial = new Monomial(mDegs);
                    var monomial = monomials[midx];
                    // Evaluate that monomial on the pair of inputs
                    // Though we're using the newton basis instead of standard basis
                    var meval = mmask & PolynomialEvaluator.EvalMonomial(monomial, inputs, canonicalBasis: false);
                   // var meval = coeff;

        
                    //Console.WriteLine($"{monomial.ToString(false)} on f({inputStr}) == {meval}");

                    //sb.Append($"{monomial.ToString(false)} + ");
                    eq.coeffs[midx] = meval;
                    //coeffMatrix[i, midx] = meval;
                }

                Console.WriteLine($"{sb.ToString()}: {inputStr}");

                //resultVector[i] = mmask & PolynomialEvaluator.Eval(poly, inputs, canonicalBasis: true);
                eq.result = mmask & PolynomialEvaluator.Eval(poly, inputs, canonicalBasis: true);
                equations.Add(eq);

                
                for(int degIdx = 0; degIdx < cDeg.Count; degIdx++)
                {
                    //if (cDeg[degIdx] == 0)
                    //    continue;
                    if (hasSeen[degIdx])
                        varSeen[degIdx] += 1;
                }

            }

            var system = new LinearSystem(poly.width, poly.numVars, equations);

            Console.WriteLine(system.ToZ3String());

            var solver = new LinearCongruenceSolver(poly.moduloMask);
            var solutionMap = new ulong[numPoints];
                
            var foundSolution = LinearEquationSolver.EnumerateSolutions(system, solver, solutionMap, 0, upperTriangular: false);
            if (!foundSolution)
                throw new InvalidOperationException("Unsolvable system!");

            var factorialOutput = new SparsePolynomial(poly.numVars, poly.width);
            for(int i = 0; i < (int)numPoints; i++)
            {
                var coeff = solutionMap[i];
                var rcoeff = PolynomialReducer.GetReductionMask(poly.width, monomials[i]) & coeff;

                factorialOutput.SetCoeff(monomials[i], rcoeff);
            }

            var standardOutput = PolynomialReducer.GetCanonicalForm(factorialOutput);


            Debugger.Break();
        }

        private static int[] GetVarDegrees(SparsePolynomial poly)
        {
            var degrees = new int[poly.numVars];
            foreach(var (m, coeff) in poly.coeffs)
            {
                if (coeff == 0)
                    continue;

                var mDegs = m.Degrees;
                for(int i = 0; i < mDegs.Count; i++)
                {
                    var d = mDegs[i];
                    if (d > degrees[i])
                        degrees[i] = d;
                }
            }

            return degrees;
        }

        private static uint GetMaxDegree(SparsePolynomial poly)
        {
            return poly.coeffs.Keys.MaxBy(x => x.GetTotalDeg()).GetTotalDeg();
        }

        private static ulong GetNumPoints(int n, int d)
        {
            var r = PolynomialReducer.Factorial(n + d) / (PolynomialReducer.Factorial(d) * PolynomialReducer.Factorial(n));
            return (ulong)r;
        }

        // Compute the number of points uniquely determining a multivariate polynomial
        private static ulong GetNumPoints(int[] varDegs)
        {
            ulong product = 1;
            foreach(var d in varDegs)
            {
                product *= ((ulong)d + 1);
            }

            return product;
        }


        // https://www.researchgate.net/publication/261421283_On_the_Newton_multivariate_polynomial_interpolation_with_applications
        public static void MvNewtonNew()
        {
            // 4 WORKS, 5 DOES NOT
            var poly = new SparsePolynomial(2, (byte)64);
            // poly.SetCoeff(new Monomial(3, 0), 127); // works with recent change
            //poly.SetCoeff(new Monomial(5, 0), 1); // works with recent change
            //poly.SetCoeff(new Monomial(6, 0), 127);
            //poly.SetCoeff(new Monomial(16, 0), 1231233);
            //poly.SetCoeff(new Monomial(14, 0), 65756);
            //poly.SetCoeff(new Monomial(13, 0), 2312132);
            //poly.SetCoeff(new Monomial(12, 0), 776546756767);
            poly.SetCoeff(new Monomial(32, 0), 1);


            //poly = SparsePolynomial.ParsePoly("12018333260144101810*y + 12670490878911611211*x + 80108105768519824*y*y + 13695898159358288600*x*y + 13363685499442732160*y*y*y + 12748260730795629248*x*y*y + 12465110187454997504*y*y*y*y + 10090656974170945024*x*y*y*y + 1378452286374879232*y*y*y*y*y + 10542703918158753792*x*y*y*y*y + 2889395752399339520*y*y*y*y*y*y + 9149001014639951872*x*y*y*y*y*y + 14816716637566664704*y*y*y*y*y*y*y + 7875404780207341568*x*y*y*y*y*y*y + 16411499749129060352*y*y*y*y*y*y*y*y + 18405398350772830208*x*y*y*y*y*y*y*y + 5006628381907746816*y*y*y*y*y*y*y*y*y + 7617777668603248640*x*y*y*y*y*y*y*y*y + 5811724210040471552*y*y*y*y*y*y*y*y*y*y + 8450204560567304192*x*y*y*y*y*y*y*y*y*y + 15940534159315828736*y*y*y*y*y*y*y*y*y*y*y + 12266303154647203840*x*y*y*y*y*y*y*y*y*y*y + 6796250300937142272*y*y*y*y*y*y*y*y*y*y*y*y + 9785671036442771456*x*y*y*y*y*y*y*y*y*y*y*y + 2197865607246905344*y*y*y*y*y*y*y*y*y*y*y*y*y + 17658263051113070592*x*y*y*y*y*y*y*y*y*y*y*y*y + 11578412693853306880*y*y*y*y*y*y*y*y*y*y*y*y*y*y + 14171013283393306624*x*y*y*y*y*y*y*y*y*y*y*y*y*y + 12372452503642439680*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y + 7979441755793653760*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y + 9994120891832729600*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y + 2960940833135656960*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y + 1039487088992452608*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y", 64);

            //poly = SparsePolynomial.ParsePoly("x*x*x*x*x*x*x*x*x*x", 1, 8);

            // poly = SparsePolynomial.ParsePoly(" 12018333260144101810*y + 12670490878911611211*x + 80108105768519824*y*y + 13695898159358288600*x*y + 13363685499442732160*y*y*y + 12748260730795629248*x*y*y + 12465110187454997504*y*y*y*y + 10090656974170945024*x*y*y*y + 1378452286374879232*y*y*y*y*y + 10542703918158753792*x*y*y*y*y + 2889395752399339520*y*y*y*y*y*y + 9149001014639951872*x*y*y*y*y*y + 14816716637566664704*y*y*y*y*y*y*y + 7875404780207341568*x*y*y*y*y*y*y + 16411499749129060352*y*y*y*y*y*y*y*y + 18405398350772830208*x*y*y*y*y*y*y*y + 5006628381907746816*y*y*y*y*y*y*y*y*y + 7617777668603248640*x*y*y*y*y*y*y*y*y + 5811724210040471552*y*y*y*y*y*y*y*y*y*y + 8450204560567304192*x*y*y*y*y*y*y*y*y*y + 15940534159315828736*y*y*y*y*y*y*y*y*y*y*y + 12266303154647203840*x*y*y*y*y*y*y*y*y*y*y + 6796250300937142272*y*y*y*y*y*y*y*y*y*y*y*y + 9785671036442771456*x*y*y*y*y*y*y*y*y*y*y*y + 2197865607246905344*y*y*y*y*y*y*y*y*y*y*y*y*y + 17658263051113070592*x*y*y*y*y*y*y*y*y*y*y*y*y + 11578412693853306880*y*y*y*y*y*y*y*y*y*y*y*y*y*y + 14171013283393306624*x*y*y*y*y*y*y*y*y*y*y*y*y*y + 12372452503642439680*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y + 7979441755793653760*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y + 9994120891832729600*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y + 2960940833135656960*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y + 1039487088992452608*x*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y*y", 2, 8);

            //poly = SparsePolynomial.ParsePoly("4243234*x + 42313443*y + 3432234*x*x + 23432432324*y*y + 234324*x*y + 23423443*x*y + 2453234342*x*x*y*y", 2, 64);

            /*
            poly.SetCoeff(new Monomial(0, 0), unchecked(0ul - 2));
            poly.SetCoeff(new Monomial(1, 0), unchecked(0ul - 2));
            poly.SetCoeff(new Monomial(1, 1), unchecked(0ul - 3));
            poly.SetCoeff(new Monomial(2, 1), 15);
            */

            //poly.SetCoeff(new Monomial(30,30), 15);

            // 4 works
            // 5 does not work



            //poly.SetCoeff(new Monomial(1, 1), 17);

            var mmask = ModuloReducer.GetMask(poly.width);
            var solver = new LinearCongruenceSolver(mmask);
            Console.WriteLine(poly);

            // (1) Construct zero order table of initial values
            var max = MAXDEG;
            var zeroOrderTable = new Num[max, max];
            for(int i = 0; i < max; i++)
            {
                for(int j = 0;  j < max; j++)
                {
                    var inputs = new ulong[] { (ulong)i, (ulong)j};
                    var y = mmask & PolynomialEvaluator.Eval(poly, new Num[] { (ulong)i, (ulong)j });
                    zeroOrderTable[i, j] = y;
                }
            }

            var byteZeroOrderTable = new sbyte[max, max];
            for(int r = 0; r < max; r++)
            {
                for(int c = 0; c < max; c++)
                {
                    byteZeroOrderTable[r, c] = (sbyte)(byte)zeroOrderTable[r, c];
                }
            }

            

            //P(0, 0, 0, null);
            /*
            Dictionary<(int, int, int), ulong> table = new();
            for (int i = 0; i < max; i++)
            {
                for (int j = 0; j < max; j++)
                {
                    P(3, i, j, table, zeroOrderTable);
                }
            }
            */

            // (2) Compute the kth ordewr table of divided differences


            //P(0, 1, 1, table, zeroOrderTable);

            var n = MAXDEG;
            for(int tableI = (int)n - 1; tableI < n; tableI++)
            {
                Dictionary<(int, int, int), (ulong, bool)> table = new();

                // Compute the nth order divided difference table
                for (int i = 0; i < n; i++)
                {
                    for (int j = 0; j < n - i; j++)
                    {
                        var d = Math.Max(i, j);
                        //d = Math.Min(d, i);
                        d = Math.Min(d, tableI);

                        //Console.WriteLine($"p{d}: {i},{j}");
                       // if (d == 2 && i == 2 && j == 1)
                       //     Debugger.Break();
                        P(mmask, solver, d, i, j, table, zeroOrderTable);
                    }
                }

                foreach(var elem in table)
                {
                    //if (elem.Value > 255)
                    //    Debugger.Break();
                }

                bool log = false;
                if(log)
                    Console.WriteLine($"\n\n\nDeg {tableI} table:");
                var coeffs = new ulong[n, n];
                foreach (var ((k, i, j), coeff) in table)
                {
                    coeffs[i, j] = coeff.Item1;
                }

                if (log)
                {
                    var padding = String.Join(" ", Enumerable.Repeat<string>(" ", 32));
                    // var padding = "                                ";
                    for (int r = 0; r < coeffs.GetLength(0); r++)
                    {
                        for (int c = 0; c < coeffs.GetLength(1); c++)
                        {
                            var coeff = coeffs[r, c];
                            //var (a, b) = divTable[r, c];
                            var str = ((sbyte)(byte)coeff).ToString();
                            //var str = $"({a}*{b})";
                            Console.Write($"{str}" + padding.Substring(0, padding.Length - str.Length));
                        }

                        Console.WriteLine("\n\n");
                    }
                }


                if (tableI == n - 1)
                {
                    var before = DivDiffToPoly(tableI, coeffs);

                    Console.WriteLine($"Interpolation found polynomial:\n    {before}\n\n for input:\n    {poly}");

                    Debugger.Break();
                }

                

            }


            //var hello = P(2, 1, 1, table, zeroOrderTable);


            Debugger.Break();
        }

        private static string DivDiffToPoly(int degree, Num[,] coeffs)
        {
            var sb = new StringBuilder();
            // monomial order: 0, x, y, x*y
            //

            for(int j = 0; j < coeffs.GetLength(1); j++)
            {
                for(int i = 0;  i < coeffs.GetLength(0); i++)
                {
                    var coeff = coeffs[i, j];
                    if (coeff == 0)
                        continue;

                    var s = GetMonomialStr(new Monomial((byte)i, (byte)j));
                    sb.Append($"{coeff}*{s} + ");
                }
            }

            return sb.ToString();
        }

        private static string GetMonomialStr(Monomial m)
        {
            return m.ToString(false);

            var sb = new StringBuilder();
            if (m.GetTotalDeg() == 0)
                return "1";

            for(int i = 0; i < m.GetNumVars(); i++)
            {

            }
        }

        // If we have (a/b), we want to find a coefficient
        private static (ulong, bool) Mdiv(ulong mmask, LinearCongruenceSolver solver, ulong a, ulong b)
        {
           // if (a > 255 || b > 255)
            //    Debugger.Break();
            var div = mmask & (a / b);
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
                /*
                // Debugger.Break();
                // var lc = solver.LinearCongruence(a, div, (UInt128)mmask + 1);
                var lc = solver.LinearCongruence(div, a, (UInt128)mmask + 1); // not correct. ensure that that after doing (a/b), there is some coeff you can multiply (a/b) by to undo the division.
                //var lc = solver.LinearCongruence(a, div, (UInt128)mmask + 1); // ensure that 
                if (lc == null || lc.d == 0)
                {
                   // Console.WriteLine("mismatch");
                    //throw new InvalidOperationException("Non invertible multiplication!");
                }

                else
                {



                    var solution = (ulong)solver.GetSolution(0, lc);
                    undo = mmask & (a * solution);
                    //Debug.Assert(undo == div);

                    // Rewrite the division as multiplication
                    //return solution;

                    // We probably should not do this
                    //return b;
                }
                */
            }

        done:
            return (div, false);
        }



        private static (ulong, bool) P(ulong mmask, LinearCongruenceSolver solver, int k, int i, int j, Dictionary<(int, int, int), (ulong, bool)> table, Num[,] zeroOrderTable)
        {

            var reduce = (ulong x) => mmask & x;
            var div = (ulong a, ulong b) => Mdiv(mmask, solver, a, b);


            bool dbg = false;
            var tup = (k, i, j);
            //if (tup == (6, 6, 0))
            //    Debugger.Break();
            if (table.ContainsKey(tup))
            {
                var r = table[tup];
                if (dbg && r.Item2)
                    Debugger.Break();
                return r;
            }

            //if (i == 1 && j == 1)
            //    Debugger.Break();

           // if (k == 0 && (i == 0 || j == 0))
           if(k == 0)
            {
                var v = zeroOrderTable[i, j];
                table[tup] = (v, false);
                goto done;
            }

            if (j <= k - 1 && i > k-1)
            {
                var (p0, p0Bad) = P(mmask, solver, k - 1, i, j, table, zeroOrderTable);
                var (p1, p1Bad) = P(mmask, solver, k - 1, i - 1, j, table, zeroOrderTable);

                var xi = (ulong)i;
                var xik = (ulong)xi - (ulong)k;

                // coeff = (y1-y0)/(x0-x1)
                // 6*coeff
                var (diff, isBad) = div((reduce(p0 - p1)), (reduce(xi - xik)));
                table[tup] = (diff, isBad | p0Bad | p1Bad);
                goto done;
            }

            if (i <= k - 1 && j > k - 1)
            {
                var (p0, p0Bad) = P(mmask, solver, k - 1, i, j, table, zeroOrderTable);
                var (p1, p1Bad) = P(mmask, solver, k - 1, i, j - 1, table, zeroOrderTable);

                var yi = (ulong)j;
                var yik = (ulong)yi - (ulong)k;

                var (diff, isBad) = div(reduce(p0 - p1), reduce(yi - yik));
                table[tup] = (diff, isBad | p0Bad | p1Bad);
                goto done;
            }


     

            var n = MAXDEG;
            if (i > k - 1 && j > k-1 && i+j <= n)
            {
                //if (k - 1 == 0 || k == 0)
                //    Debugger.Break();
                var (p0, p0Bad) = P(mmask, solver, k - 1, i, j, table, zeroOrderTable);
                var (p1, p1Bad) = P(mmask, solver, k - 1, i - 1, j - 1, table, zeroOrderTable);
                var (p2, p2Bad) = P(mmask, solver, k - 1, i, j - 1, table, zeroOrderTable);
                var (p3, p3Bad) = P(mmask, solver, k - 1, i - 1, j, table, zeroOrderTable);


                var xi = (ulong)i;
                var xik = (ulong)xi - (ulong)k;
                var yj = (ulong)j;
                var yjk = (ulong)yj - (ulong)k;

                // Paper seems to add p0 instead of subtracting.. typo?
                var (dif, isBad) = div(reduce(p0 + p1 - p2 - p3), reduce(((xi - xik))*(yj - yjk)));
                table[tup] = (dif, isBad | p0Bad | p1Bad | p2Bad | p3Bad);
                goto done;
            }




            Debugger.Break();
            return (0, false);


        done:
            var rr = table[tup];
            if (dbg && rr.Item2)
                Debugger.Break();
            return rr;
        }

        public static void MvNewtonOld()
        {
            var poly = new SparsePolynomial(2, (byte)8);
            //poly.SetCoeff(new Monomial(0, 0), 0);
            //poly.SetCoeff(new Monomial(1, 0), 17);
            //poly.SetCoeff(new Monomial(0, 1), 33);
            poly.SetCoeff(new Monomial(1, 1), 1);
            //poly.SetCoeff(new Monomial(2), 42);
            Console.WriteLine(poly);
            var mmask = ModuloReducer.GetMask(poly.width);
            var solver = new LinearCongruenceSolver(mmask);

            var monomials = new List<Monomial> { new(0, 0), new(1,0), new(0, 1), new(1, 1)};
            monomials.Sort();

            // Compute list of inputs
            //var xs = new List<Point> { new(0, 0), new(1, 0), new(0, 1), new(1, 1) };

            //var xs = new List<Point> { new(0, 0), new(1, 2), new(3, 4), new(5, 6) };

            var xs = new List<Point> { new(0, 0), new(1, 3), new(5, 7), new(9, 11) };

            // Compute list of outputs
            var y = xs.Select(x => PolynomialEvaluator.Eval(poly, new Num[] { x.X, x.Y })).ToList();

            // Fill the first column with y
            var n = xs.Count;
            var coeffs = new Num[n, n];
            for (int i = 0; i < n; i++)
                coeffs[i, 0] = y[i];

            //for(int i = 0;  i < n; i++)
            for (int j = 1; j < n; j++)
            {
                //for(int j = 1; i < n - j; i++)
                for (int i = 0; i < n - j; i++)
                {
                    var y1 = coeffs[i, j - 1];
                    var y2 = coeffs[i + 1, j - 1];
                    var a = mmask & (y2 - y1);

                    var ONE = xs[i];
                    var TWO = xs[i + j];

                    var x1 = xs[i].X;
                    var x2 = xs[i + j].X;

                    // Experimental
                    x1 += xs[i].Y;
                    x2 += xs[i + j].Y;
                    //x1 -= xs[i].Y;
                    //x2 -= xs[i + j].Y;

                    var b = mmask & (x2 - x1);

                    if (b == 0)
                        Debugger.Break();

                    var div = b == 0 ? 0 : mmask & (a / b);

                    // Undo the division.
                    var undo = mmask & (div * b);
                    if (undo != a)
                    {
                        var lc = solver.LinearCongruence(div, a, (UInt128)mmask + 1);
                        if (lc == null || lc.d == 0)
                        {
                            Console.WriteLine();
                            //Debugger.Break();
                        }

                        else
                        {

                            b = (ulong)solver.GetSolution(0, lc);
                            undo = mmask & (div * b);
                            Debug.Assert(undo == a);
                        }

                    }

                    coeffs[i, j] = div;
                }
            }

            // 0,x0,x1,x0*x1

            // We now have f (x0,x1,x2,x3) = y
            // There are many Xs but only one y obviouslyu
            // I think newton should

            Console.WriteLine("\n\n");
            var padding = String.Join(" ", Enumerable.Repeat<string>(" ", 32));
            // var padding = "                                ";
            for (int r = 0; r < coeffs.GetLength(0); r++)
            {
                for (int c = 0; c < coeffs.GetLength(1); c++)
                {
                    var coeff = coeffs[r, c];
                    //var (a, b) = divTable[r, c];
                    var str = coeff.ToString();
                    //var str = $"({a}*{b})";
                    Console.Write($"{str}" + padding.Substring(0, padding.Length - str.Length));
                }

                Console.WriteLine();
            }


            Debugger.Break();
        }


        public static void ActualWorkingNewton()
        {

            // 1 + 17*x + 33*x*x
            //// Solution(2nd row): op2 = 51 + 116*(x-1) + 33*(x-1)*(x-2)
            //var poly = new SparsePolynomial(1, (byte)8);
            //poly.SetCoeff(new Monomial(0), 1);
            //poly.SetCoeff(new Monomial(1), 17);
            //poly.SetCoeff(new Monomial(2), 33);
            //poly.SetCoeff(new Monomial(3), 72);
            //poly.SetCoeff(new Monomial(2), 3);



            /*
            var poly = new SparsePolynomial(1, (byte)64);
            poly.SetCoeff(new Monomial(0), 0x8000000000000000);
            poly.SetCoeff(new Monomial(1), 5260339532280414813);
            poly.SetCoeff(new Monomial(2), 14929154534604275712);
            poly.SetCoeff(new Monomial(3), 0x8000000000000000);
            */

            //var poly = new SparsePolynomial(1, (byte)64);
            //poly.SetCoeff(new Monomial(0), 9193501499183852111);
            //poly.SetCoeff(new Monomial(1), 5260339532280414813);
            //poly.SetCoeff(new Monomial(2), 14929154534604275712);
            //poly.SetCoeff(new Monomial(3), 3178634119571570688);

            // Solution(2nd row):  103 + 55*(x-1) + 42*(x-1)*(x-2)
            var poly = new SparsePolynomial(1, (byte)8);
            poly.SetCoeff(new Monomial(0), 132);
            poly.SetCoeff(new Monomial(1), 185);
            poly.SetCoeff(new Monomial(2), 42);

            poly = new SparsePolynomial(1, (byte)8);
            poly.SetCoeff(new Monomial(0), 0);
            poly.SetCoeff(new Monomial(1), 1);


            Console.WriteLine(poly);

      
            var mmask = ModuloReducer.GetMask(poly.width);
            var solver = new LinearCongruenceSolver(mmask);

            var inputs = new List<ulong>() { 0, 1, 2, 3 };
            var outputs = inputs.Select(x => mmask & PolynomialEvaluator.Eval(poly, new ulong[] { x })).ToList();


            var me = DivDiff2(solver, mmask, inputs.Select(x => (Num)x).ToArray(), outputs.Select(x => (Num)x).ToArray());
            //Debugger.Break();
            var (coeffs, divTable) = DividedDiff(solver, mmask, inputs.Select(x => (Num)x).ToArray(), outputs.Select(x => (Num)x).ToArray());

            int rows = me.GetLength(0);
            int cols = me.GetLength(1);
            for(int i = 0; i < rows; i++)
            {
                for(int j = 0;  j < cols; j++)
                {
                    var a = me[i, j];
                    var b = coeffs[i, j];
                    if (a != b)
                        throw new InvalidOperationException();
                }
            }
            //var data = new List<Point>() { new(1, 1), new(2, 5), new(3, 2), new(3.2, 7), new(3.9, 4) };
            //(coeffs, divTable) = DividedDiff(solver, mmask, data.Select(x => x.X).ToArray(), data.Select(y => y.Y).ToArray());

            Debugger.Break();
            Console.WriteLine("\n\n");
            var padding = String.Join(" ", Enumerable.Repeat<string>(" ", 32));
           // var padding = "                                ";
            for (int r = 0; r < divTable.GetLength(0); r++)
            {
                for(int c = 0; c < divTable.GetLength(1); c++)
                {
                    var coeff = coeffs[r, c];
                    var (a, b) = divTable[r, c];
                    var str = coeff.ToString();
                    //var str = $"({a}*{b})";
                    Console.Write($"{str}" + padding.Substring(0, padding.Length - str.Length));
                }

                Console.WriteLine();
            }


            Debugger.Break();

        }

        public static Num[,] DivDiff2(LinearCongruenceSolver solver, ulong mmask, Num[] x, Num[] y)
        {
            var n = x.Length;            

            // Fill the first column with y
            var coeff = new Num[n, n];
            for (int i = 0; i < n; i++)
                coeff[i, 0] = y[i];

            //for(int i = 0;  i < n; i++)
            for (int j = 1; j < n; j++)
            {
                //for(int j = 1; i < n - j; i++)
                for (int i = 0; i < n - j; i++)
                {
                    var y1 = coeff[i, j - 1];
                    var y2 = coeff[i + 1, j - 1];
                    var a = mmask & (y2 - y1);

                    var x1 = x[i];
                    var x2 = x[i + j];
                    var b = mmask & (x2 - x1);
                    coeff[i, j] = mmask & (a / b);
                }
            }

            return coeff;
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

        public static (Num[,], (Num, Num)[,]) DividedDiff(LinearCongruenceSolver solver, ulong mmask, Num[] x, Num[] y)
        {
            int n = y.Length;
            Num[,] coeff = new Num[n, n];
            (Num, Num)[,] divTable = new (Num, Num)[n, n];

            // the first column is y
            for (int i = 0; i < n; i++)
            {
                coeff[i, 0] = y[i];
            }

            for (int j = 1; j < n; j++)
            {
                for (int i = 0; i < n - j; i++)
                {
                    var a = mmask & (coeff[i + 1, j - 1] - coeff[i, j - 1]);
                    var b = mmask & (x[i + j] - x[i]);
                    var div = mmask & (a / b);
                    coeff[i, j] = div;

                    // Undo the division.
                    var undo = mmask & (div * b);
                    if (undo != a)
                    {
                        var lc = solver.LinearCongruence(div, a, (UInt128)mmask + 1);
                        if (lc == null || lc.d == 0)
                            throw new InvalidOperationException("Non invertible multiplication!");

                        b = (ulong)solver.GetSolution(0, lc);
                        undo = mmask & (div * b);
                        Debug.Assert(undo == a);

                    }

                    bool isEven = (b % 2) == 0;
                    if (undo != a && isEven)
                        throw new InvalidOperationException("Not invertible mult");

                    divTable[i, j] = (a, b);
                }
            }

            return (coeff, divTable);
        }

        public static void Test2()
        {
            // 1 + 17*x + 33*x*x
            var poly = new SparsePolynomial(1, (byte)8);
            poly.SetCoeff(new Monomial(0), 1);
            poly.SetCoeff(new Monomial(1), 17);
            poly.SetCoeff(new Monomial(2), 33);
            //poly.SetCoeff(new Monomial(2), 3);

            Console.WriteLine(poly);

            var inputs = new List<ulong>() { 0, 1, 2};

            var outputs = inputs.Select(x => PolynomialEvaluator.Eval(poly, new ulong[] { x })).ToList();

            var numElements = inputs.Count;

            /*
            for(int i = 0; i < inputs.Count; i++)
            {
                var y = outputs[i];
                var coeffs = Enumerable.Repeat<ulong>(0, numElements);
                for(int j = i; j >= 0; j--)
                {

                }
            }
            */

            /*
            for(int i = 0; i < 3; i++)
            {
                var y = outputs[i];
                var coeffs = Enumerable.Repeat<ulong>(0, numElements).ToArray();
                coeffs[0] = 1;
            }
            */
            
            var equations = new List<LinearEquation>(numElements);
            for (int equationIndex = 0; equationIndex < inputs.Count; equationIndex++)
            {
                var y = outputs[equationIndex];
                var coeffs = Enumerable.Repeat<ulong>(0, numElements).ToArray();
                var cidx = 0;

                /*
                for(int i = 0; i <= equationIndex; i++)
                {
                    if (i == 0)
                    {
                        coeffs[cidx++] = 1;
                        continue;
                    }

                    if (i == 1)
                    {
                        coeffs[cidx++] = inputs[equationIndex] - inputs[0];
                        continue;
                    }
                }
                */

                //if(equationIndex)

                if (equationIndex == 2)
                    Debugger.Break();

                // Compute each coeff individually
                // i corresponds to one coeff in the equation, initally one
                for(int i = 0; i <= equationIndex; i++)
                {
                    // Start with one
                    ulong coeff = 1;

                    ulong start = inputs[equationIndex];
                    var range = Enumerable.Range(0, i);
                    foreach (var offsetIndex in range)
                    {
                        var input = inputs[offsetIndex];
                        coeff *= (start - input);
                    }

                    coeffs[i] = coeff;
                }



                var equation = new LinearEquation(numElements);
                equation.coeffs = coeffs;
                equation.result = y;

                // Reverse the coeff list for printing p
                //equation.coeffs = equation.coeffs.Reverse().ToArray();
                equations.Add(equation);

                //Debugger.Break();

                /*
                for (int j = equationIndex; j >= 0; j--)
                {
                    if(j == 0)
                    {
                        coeffs[cidx++] = 1;
                        continue;
                    }

                    if (j == 1)
                    {
                        coeffs[cidx++] = inputs[equationIndex] - inputs[0];
                    }
                }
                */
            }

            var system = new LinearSystem(poly.width, poly.numVars, equations);
           
            Console.WriteLine(system.ToString() + "\n\n\n");
            Console.WriteLine(system.ToZ3String());

            Debugger.Break();
        }

        private static void BuildTable2(int i, List<Point> points, List<Num> table)
        {
            if (i >= points.Count)
                return;

            var point = points[i];
            if (i == 0)
            {
                table.Add(points[i].Y);
                return;
            }


        }

        private static void BuildTable(int i, List<Point> points, List<Num> table)
        {
            if (i >= points.Count)
                return;

            var point = points[i];
            if(i == 0)
            {
                table.Add(points[i].Y);
                return;
            }

            if (i == 1)
            {
                var y = points[1].Y - points[0].Y;
                var x = points[1].X - points[0].X;
                var idiv = y / x;
                table.Add(idiv);
                return;
            }

            if (i == 3)
                Debugger.Break();

            // Sum (y2, y3, ..., yN + 1)
            Num x1 = 0;
            Num y1 = 0;
            for(int curr = i; curr > 0; curr--)
            {
                var coeff = (curr == i) ? (Num)1 : unchecked(((Num)(-1)));
                x1 += coeff * points[curr].X;
                y1 += coeff * points[curr].Y;
            }
            Num x2 = 0;
            Num y2 = 0;
            for(int curr = i - 1; curr >= 0; curr--)
            {
                var coeff = (curr == i - 1) ? (Num)1 : unchecked(((Num)(-1)));
                x2 += coeff * points[curr].X;
                y2 += coeff * points[curr].Y;
            }

            // x1, y1, x2, y2 correct
            //var diffY = y1 - y2;
            //var diffX = points[i].X - points[0].X;

            var op1 = y1 / x1;
            //var op2Real = table[i = 1];
            //var op2 = y2 / x2;
            var op2 = table[i - 1];
            var diff = op1 - op2;

            var divisor = points[i].X - points[0].X;
            var div = diff / divisor;
            table.Add(div);
            //table.Add(diffY / diffX);
            //Debugger.Break();
        }
    }
}
