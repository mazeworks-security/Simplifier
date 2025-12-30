global using TableSize = Mba.Simplifier.FastGb.U8;
using Mba.Simplifier.Slgb;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Poly = Mba.Simplifier.FastGb.BoolPoly<Mba.Simplifier.FastGb.U8>;
namespace Mba.Simplifier.FastGb
{
    public class BoolGb
    {
        public List<Poly> Buchberger(List<Poly> polys)
        {
            //var G = polys;
            var G = Autoreduce(polys);
            //List<Polynomial> g = new();
            List<(int, int)> pairs = new();

            var M = new List<List<int>>();


            /*
            var k = polys.Count;
            for(int i = -table.NumVars; i < k; ++i)
            {
                for(int j = 0; j < k; ++j)
                {
                    if (i<j)
                    {
                        pairs.Add((i, j));
                    }
                }
            }
            */

            /*
            for (int i = 0; i < polys.Count; i++)
            {
                for (int j = i + 1; j < polys.Count; j++)
                {

                    pairs.Add((i, j));
                }
            }

            while (pairs.Count > 0)
            {
                var s = new Polynomial(new());
                var h = new Polynomial(new());
                var (i, j) = pairs.First();
                pairs.RemoveAt(0);

                if (i < 0)
                {

                }
            }
            */


            var pqs = new WorkList<(Poly, Poly)>();
            for (int i = 0; i < polys.Count; i++)
            {
                var p1 = polys[i];
                for (int j = i + 1; j < polys.Count; j++)
                {
                    var p2 = polys[j];
                    pqs.AddToBack((p1, p2));
                }
            }

            while (pqs.Count > 0)
            {
                var (p, q) = pqs.PopBack();
                var s = Spoly(p, q);
                var h = NormalForm(s, G);

                if (!h.IsZero())
                {
                    foreach (var g in G)
                        pqs.AddToBack((g, h));

                    G.Add(h);
                }
            }


            var output = Autoreduce(G);

            return output;
            Debugger.Break();

        }

        private static Poly Spoly(Poly f, Poly g)
        {
            var flm = f.Lm;
            var glm = g.Lm;

            var lcm = flm * glm;

            var div1 = (lcm / flm);
            var div2 = (lcm / glm);
            var m1 = f * div1;
            var m2 = g * div2;
            var res = m1 + m2;
            return res;
        }

        private static Poly NormalForm(Poly f, List<Poly> F)
        {
            var p = f.Clone();
            var r = new Poly();

            if (F.Count == 0)
                return p;

            while (!p.IsZero())
            {
                int i = 0;
                bool divisionoccurred = false;
                var plm = p.Lm;
                while (i < F.Count && !divisionoccurred)
                {
                    var film = F[i].Lm;
                    if (plm.IsDivisible(film))
                    {
                        /*
                        var div = (plm / film);

                        var fi = F[i];
                        var product = (fi * div);
                        p = p + product;
                        */

                        //p = p + F[i] * (plm / film);

                        var div = (plm / film);
                        p = p + F[i] * div;

                        divisionoccurred = true;
                    }

                    else
                    {
                        i++;
                    }
                }

                if (!divisionoccurred)
                {
                    r = r + plm;
                    p = p + plm;
                }
            }

            return r;
        }


        private static List<Poly> Autoreduce(List<Poly> F)
        {
            var g = F.Select(x => x.Clone()).ToList();
            var P = new List<Poly>();

            while (g.Any())
            {
                var h = g.Last();
                g.RemoveAt(g.Count - 1);
                h = NormalForm(h, P);
                if (!h.IsZero())
                {
                    var newP = new List<Poly>();
                    foreach (var itp in P)
                    {
                        if (itp.Lm.IsDivisible(h.Lm))
                        {
                            // We erase this element if not divisble
                            g.Add(itp);
                            continue;
                        }

                        newP.Add(itp);
                    }

                    P = newP;
                    P.Add(h);
                }
            }

            int pSize = P.Count;
            for (int i = 0; i < pSize; i++)
            {
                var h = P.First();
                P.RemoveAt(0);
                h = NormalForm(h, P);
                if (h.IsZero())
                {
                    --pSize;
                }

                else
                {
                    P.Add(h);
                }
            }

            return P;
            Console.WriteLine($"Computed groebner basis with {P.Count} elements\n[\n{String.Join("\n", P.Select(x => "    " + x.ToString() + ","))}\n]");


            var union = String.Join(" | ", P.Select(x => $"({x})"));

            union = union.Replace("*", "&");
            union = union.Replace("+", "^");


            Console.WriteLine($"Boolean: {union}");

            //Debugger.Break();
            return P;
        }
    }

}
