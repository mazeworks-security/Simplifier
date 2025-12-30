global using TableSize = Mba.Simplifier.FastGb.U64;
using Mba.Simplifier.Slgb;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Runtime.InteropServices.Marshalling;
using System.Text;
using System.Threading.Tasks;
using static System.Net.WebRequestMethods;
using Poly = Mba.Simplifier.FastGb.BoolPoly<Mba.Simplifier.FastGb.U64>;
namespace Mba.Simplifier.FastGb
{
    public class BoolGb
    {
        public List<Poly> Buchberger(List<Poly> F)
        {
            var numVars = TableSize.NumVars;
            var G = Autoreduce(F);
            var pairs = new List<(int i, int j)>();
            int k = G.Count;

            // Matrix M with treated pairs
            var M = Enumerable.Range(0, k)
                              .Select(_ => Enumerable.Repeat(false, k).ToList())
                              .ToList();

            for (int i = -numVars; i < k; ++i)
            {
                for (int j = 0; j < k; ++j)
                {
                    if (i < j) pairs.Add((i, j));
                }
            }

            while (pairs.Count > 0)
            {
                var (i, j) = pairs[0];
                pairs.RemoveAt(0);

                Poly s;
                if (i < 0)
                {
                    var gjLm = G[j].Lm;
                    var xi = new Monomial<TableSize>(1u << Math.Abs(i));

                    if (gjLm.IsRelativelyPrime(xi))
                        continue;

                    // TODO: We are doingm copy on write, maybe this is wrong?
                    s = G[j] * xi;
                }
                else
                {
                    M[i][j] = true;
                    var p = G[i];
                    var q = G[j];

                    if (Criteria(i, j, p, q, M, G))
                        continue;

                    s = Spoly(p, q);
                }

                var h = NormalForm(s, G);
                if (!h.IsZero())
                {
                    G.Add(h);
                    for (int ii = -numVars; ii < k; ++ii)
                    {
                        pairs.Add((ii, k));
                    }

                    ++k;

                    foreach (var row in M) row.Add(false);
                    M.Add(Enumerable.Repeat(false, k).ToList());
                }
            }

            G = Autoreduce(G);
            return G;
        }

        public static bool Criteria(
            int i,
            int j,
            Poly p,
            Poly q,
            List<List<bool>> M,
            List<Poly> G)
        {
            if (p.Lm.IsRelativelyPrime(q.Lm))
                return true;

            var pqLm = p.Lm * q.Lm;

            int gSize = G.Count;
            for (int k = 0; k < gSize; ++k)
            {
                if (M[i][k] && M[k][j] && G[k].Lm.IsDivisible(pqLm))
                    return true;
            }

            return false;
        }

        public List<Poly> BuchbergerOld(List<Poly> polys)
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
            //F = F.OrderByDescending(x => x.GetDegree()).ToList();
            //F.Sort(x => x.PopCount());

            //F = F.OrderByDescending(x => x.Lm).ToList();
            //F = F.OrderBy(x => x.Lm).ToList();

            var g = F.Select(x => x.Clone()).ToList();
            var P = new List<Poly>();
            ulong pCombinedMask = 0;

            var reducedSet = new List<Poly>();
            var notReducedSet = new List<Poly>();

            bool log = false;

            while (g.Any())
            {
                pCombinedMask = 0;
                //foreach(var p in )

                var h = g.Last();
                g.RemoveAt(g.Count - 1);
                var before = h.Clone();

                var hMask = h.AsUlong();
                bool prediction = (hMask & pCombinedMask) == 0;

                /*
                foreach (var m in h.Monomials)
                {
                    pCombinedMask |= (1UL << m.Index);
                }
                */

                h = NormalForm(h, P);

                //bool changed = h.AsUlong() != before.AsUlong();


                //Console.WriteLine(changed);
                //Console.WriteLine($"{prediction == changed}");
                //Console.WriteLine($"IsZero: {h.IsZero()} for poly{before}");
                if (log)
                {
                    if (h.IsZero())
                        notReducedSet.Add(before);
                    else
                        reducedSet.Add(before);
                }

                

                if (!h.IsZero())
                {
                    //pCombinedMask = 0;
                    var newP = new List<Poly>();
                    foreach (var itp in P)
                    {
                        if (itp.Lm.IsDivisible(h.Lm))
                        {
                            // We erase this element if not divisble
                            g.Add(itp);
                            continue;
                        }

                        /*
                        foreach(var m in itp.Monomials)
                        {
                            pCombinedMask |= (1UL << m.Index);
                        }
                        */
                        //pCombinedMask |= itp.AsUlong();

                        //pCombinedMask |= (1UL << itp.Lm.Index);

                        newP.Add(itp);
                    }

                    P = newP;

                    /*
                    foreach (var m in h.Monomials)
                    {
                        pCombinedMask |= (1UL << m.Index);
                    }
                    */

                    //pCombinedMask |= h.AsUlong();
                    //pCombinedMask |= (1UL << h.Lm.Index);

                    P.Add(h);

                    pCombinedMask = 0;
                    foreach(var poly in P)
                    {
                        pCombinedMask |= (1UL << poly.Lm.Index);
                    }


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


            if (log)
            {
                Console.WriteLine($"Reduced: ");
                foreach (var reduced in reducedSet)
                {
                    Console.WriteLine($"    {reduced}");
                }

                Console.WriteLine($"\n\nNot reduced:");
                foreach (var reduced in notReducedSet)
                {
                    Console.WriteLine($"    {reduced}");
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
