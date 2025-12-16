using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.LinEq
{
    using Num = Double;

    public struct Point
    {
        public Num X { get; }
        public Num Y { get; }

        public Point(Num x, Num y)
        {
            X = x;
            Y = y;
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
                BuildTable(i, data, table);
            }

            Debugger.Break();

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
                var coeff = (curr == i) ? 1 : -1;
                x1 += coeff * points[curr].X;
                y1 += coeff * points[curr].Y;
            }
            Num x2 = 0;
            Num y2 = 0;
            for(int curr = i - 1; curr >= 0; curr--)
            {
                var coeff = (curr == i - 1) ? 1 : -1;
                x2 += coeff * points[curr].X;
                y2 += coeff * points[curr].Y;
            }

            // x1, y1, x2, y2 correct
            //var diffY = y1 - y2;
            //var diffX = points[i].X - points[0].X;

            var op1 = y1 / x1;
            var op2 = y2 / x2;
            var diff = op1 - op2;

            var divisor = points[i].X - points[0].X;
            var div = diff / divisor;
            table.Add(div);
            //table.Add(diffY / diffX);
            //Debugger.Break();
        }
    }
}
