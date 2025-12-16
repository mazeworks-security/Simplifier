using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Polynomial;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
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

        public static void Test3()
        {
            /*
            // 1 + 17*x + 33*x*x
            var poly = new SparsePolynomial(1, (byte)8);
            poly.SetCoeff(new Monomial(0), 1);
            poly.SetCoeff(new Monomial(1), 17);
            poly.SetCoeff(new Monomial(2), 33);
            poly.SetCoeff(new Monomial(3), 72);
            //poly.SetCoeff(new Monomial(2), 3);
            */


            /*
            var poly = new SparsePolynomial(1, (byte)64);
            poly.SetCoeff(new Monomial(0), 0x8000000000000000);
            poly.SetCoeff(new Monomial(1), 5260339532280414813);
            poly.SetCoeff(new Monomial(2), 14929154534604275712);
            poly.SetCoeff(new Monomial(3), 0x8000000000000000);
            */

            var poly = new SparsePolynomial(1, (byte)64);
            poly.SetCoeff(new Monomial(0), 9193501499183852111);
            poly.SetCoeff(new Monomial(1), 5260339532280414813);
            poly.SetCoeff(new Monomial(2), 14929154534604275712);
            poly.SetCoeff(new Monomial(3), 3178634119571570688);

            /*
            var poly = new SparsePolynomial(1, (byte)8);
            poly.SetCoeff(new Monomial(0), 132);
            poly.SetCoeff(new Monomial(1), 185);
            poly.SetCoeff(new Monomial(2), 42);
            */

            Console.WriteLine(poly);

            var mmask = ModuloReducer.GetMask(poly.width);
            var solver = new LinearCongruenceSolver(mmask);

            var inputs = new List<ulong>() { 0, 1, 2, 3 };
            var outputs = inputs.Select(x => PolynomialEvaluator.Eval(poly, new ulong[] { x })).ToList();



            var (coeffs, divTable) = DividedDiff(solver, mmask, inputs.Select(x => (Num)x).ToArray(), outputs.Select(x => (Num)x).ToArray());
            //var data = new List<Point>() { new(1, 1), new(2, 5), new(3, 2), new(3.2, 7), new(3.9, 4) };
            //var (coeffs, divTable) = DividedDiff(data.Select(x => x.X).ToArray(), data.Select(y => y.Y).ToArray());

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
