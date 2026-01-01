global using TableSize = Mba.Simplifier.FastGb.U64;
using Mba.Simplifier.Slgb;
using System;
using System.Collections;
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
        private static bool Pivot(List<Poly> F, int initialIndex, int mi)
        {
            for(int i = initialIndex; i < F.Count; i++)
            {
                // Skip if this is not a pivot candidate
                var p = F[i];
                if (p.GetBit(mi).IsZero)
                    continue;

                // Pivot was unnecessary
                if (i == initialIndex)
                    return true;

                // Swap
                var initial = F[initialIndex];
                var curr = F[i];
                F[initialIndex] = curr;
                F[i] = initial;
            }

            return false;
        }

        ulong BitReverse(ulong v)
        {
            ulong output = 0;

            for(ushort i = 0; i < 64; i++)
            {
                var isSet = (1 & (v >> i)) == 0 ? 0ul : 1;
                var otherEnd = 63 - i;

                output |= (isSet << otherEnd);

            }




            var og = v;
            // Swap odd and even bits
            v = ((v >> 1) & 0x5555555555555555UL) | ((v & 0x5555555555555555UL) << 1);
            // Swap consecutive pairs of bits
            v = ((v >> 2) & 0x3333333333333333UL) | ((v & 0x3333333333333333UL) << 2);
            // Swap nibbles (4 bits)
            v = ((v >> 4) & 0x0F0F0F0F0F0F0F0FUL) | ((v & 0x0F0F0F0F0F0F0F0FUL) << 4);
            // Swap bytes (8 bits)
            v = ((v >> 8) & 0x00FF00FF00FF00FFUL) | ((v & 0x00FF00FF00FF00FFUL) << 8);
            // Swap 16-bit words
            v = ((v >> 16) & 0x0000FFFF0000FFFFUL) | ((v & 0x0000FFFF0000FFFFUL) << 16);
            // Swap 32-bit double words to complete the 64-bit reversal
            v = (v >> 32) | (v << 32);


            return v;
        }

        // Convert lower triangular matrix to upper triangular, or vice versa
        private void FlipTriangle(List<Poly> F)
        {
            // Reverse the list of polynomials
            F.Reverse();
            // Bit reverse the truth tables
            foreach(var p in F)
            {
                p.SetUlong(BitReverse(p.AsUlong()));
            }

            //var sorted = F.OrderBy(x => x.Lm.li)

        }

        private void RREFUpperTriangular(List<Poly> F)
        {
            var rows = F.Count;
            var cols = F[0].NumBits;
            for (int r = rows - 1; r >= 0; r--)
            {
                // Get the trailing monomial
                var pivotCol = F[r].GetTm();
                // Skip zeroes
                if (pivotCol.IsZero)
                {
                    continue;
                }

                for (int upperRow = r - 1; upperRow >= 0; upperRow--)
                {
                    // Skip if this bit is zero.
                    if (F[upperRow].GetBit(pivotCol.Index).IsZero)
                        continue;

                    F[upperRow] = F[upperRow] + F[r];
                }
            }
        }

        private void RREFLowerTriangular(List<Poly> F)
        {
            var rows = F.Count;
            var cols = F[0].NumBits;
            for (int r = 0; r < rows; r++)
            {
                var p = F[r];
                var pivotCol = p.Lm;
                if (pivotCol.IsZero)
                    continue;

                for (int lowerRow = r + 1; lowerRow < rows; lowerRow++)
                {
                    if (F[lowerRow].GetBit(pivotCol.Index).IsZero)
                        continue;

                    F[lowerRow] = F[lowerRow] + F[r];
                    F[lowerRow].UpdateLm();
                }
            }
        }


        // Assumes that the matrix is already in RREF
        private void RREF(List<Poly> F)
        {
            /*
            Console.WriteLine(GetMatBinaryString(F));
            RREFLowerTriangular(F);
            Console.WriteLine(GetMatBinaryString(F));
            Debugger.Break();
            */

            // Convert the lower triangular matrix to upper triangular
            FlipTriangle(F);


            Console.WriteLine(GetMatBinaryString(F));
            // Compute RREF
            RREFUpperTriangular(F);


            Console.WriteLine(GetMatBinaryString(F));

            // Back to upper triangular
            FlipTriangle(F);

            Console.WriteLine(GetMatBinaryString(F));



            return;

            // Upper triangular
            bool upperTriangular = true;
            if(upperTriangular)
            {
                FlipTriangle(F);
                Debugger.Break();
            }

            var rows = F.Count;
            var cols = F[0].NumBits;
            if (upperTriangular)
            {
                F = F.Select(x => x.Clone()).ToList();
                foreach (var p in F)
                {
                    p.SetUlong(BitReverse(p.AsUlong()));
                }

                F.Reverse();

                Console.WriteLine(GetMatBinaryString(F));

                for (int r = rows - 1; r >= 0; r--)
                {
                    // Get the trailing monomial
                    var pivotCol = F[r].GetTm();
                    // Skip zeroes
                    if (pivotCol.IsZero)
                    {
                        continue;
                    }

                    for (int upperRow = r - 1; upperRow >= 0; upperRow--)
                    {
                        // Skip if this bit is zero.
                        if (F[upperRow].GetBit(pivotCol.Index).IsZero)
                            continue;

                        F[upperRow] = F[upperRow] + F[r];
                    }
                }
            }

            // Lower triangular is not gonna work
            /*
            // Lower triangular
            F = F.Select(x => x.Clone()).ToList();
            Console.WriteLine(GetMatBinaryString(F));

            for(int r = 0; r < rows; r++)
            {
                var pivotCol = F[r].Lm;
                if (pivotCol.IsZero)
                    continue;

                for (int lowerRow = r + 1; lowerRow < rows; lowerRow++)
                {
                    if (F[lowerRow].GetBit(pivotCol.Index).IsZero)
                        continue;

                    F[lowerRow] = F[lowerRow] + F[r];
                    F[lowerRow].UpdateLm();
                }
            }
            */

            /*
            var demandedBits = new BitArray(F[0].NumBits);

            int lmIndex = F[0].NumBits - 1;
            Console.WriteLine(GetMatBinaryString(F));
            for (int i = 0; i < F.Count; i++)
            {
            start:
                var p = F[i];
                //var bitIndex = F.Count - i;
                //var bitIndex = p.Lm.Index;
                var bitIndex = lmIndex;
                var m = p.GetBit(bitIndex);

                if (i == 3)
                {
                    Console.WriteLine(GetMatBinaryString(F));
                    Debugger.Break();
                }

                if (m.IsZero)
                {
                    bool found = false;
                    for(int j = i + 1; j < F.Count; j++)
                    {
                        // Skip if this polynomial does not have the set bit we are looking for
                        var other = F[j];
                        if (other.Lm.Index != bitIndex)
                            continue;

                        // Otherwise we found a pivot.
                        // Swap them
                        F[i] = other;
                        F[j] = p;

                        p = F[i];

                        found = true;
                        break;
                    }

                    // This column is fully zero!
                    if(!found)
                    {
                        lmIndex -= 1;
                        continue;
                    }
                }

                for(int j = i + 1; j < F.Count; j++)
                {
                    // Skip if this bit is not set in the other poly
                    var other = F[j];
                    if (other.GetBit(bitIndex).IsZero)
                        continue;

                    F[j] = other + p;
                    F[j].UpdateLm();
                }

                lmIndex -= 1;

            }
            */

            Console.WriteLine(GetMatBinaryString(F));


            Debugger.Break();
        }

        private string GetMatBinaryString(List<Poly> F)
        {
            var sb = new StringBuilder();
            foreach (var p in F)
            {
                var binaryString = Convert.ToString((long)p.AsUlong(), 2);
                int totalLength = p.NumBits;
                string formattedBinaryString = binaryString.PadLeft(totalLength, '0');
                sb.AppendLine(formattedBinaryString);
            }
            return sb.ToString();
        }

        private List<Poly> Preprocess(List<Poly> F)
        {


            //var integers = new List<ulong>() { 0x8000000000000000, 0x4000000000000000, 0x2000000000000000, 0x1000000000000000, 0x800000000000000, 0x400000000000000, 0x200000000000000, 0x100000000000000, 0x80000000000000, 0x40000000000000, 0x20000000000000, 0x10000000000000, 0x8000000000000, 0x4000000000000, 0x2000000000000, 0x1000000000000, 0x800000000000, 0x400000000000, 0x200000000000, 0x100000000000, 0x80000000000, 0x40000000000, 0x20000000000, 0x10000000000, 0x8000000000, 0x4000000000, 0x2000000000, 0x1000000000, 0x800000000, 0x400000000, 0x200000000, 0x100000000, 0x80000000, 0x40000000, 0x20000000, 0x10000000, 0x8000000, 0x4000000, 0x2000000, 0x1000000, 0x800000, 0x400000, 0x200000, 0x100000, 0x80000, 0x40000, 0x20000, 0x10000, 0x8000, 0x4000, 0x2000, 0x1000, 0xa00, 0x600, 0xa0, 0x60, 0xa, 0x6 };

            /*
            var integers = new List<ulong>() { 0x8000000000000000, 0x4000000000000000, 0x2000000000000000, 0x1000000000000000, 0x800000000000000, 0x400000000000000, 0x200000000000000, 0x100000000000000, 0x80000000000000, 0x40000000000000, 0x20000000000000, 0x10000000000000, 0x8000000000000, 0x4000000000000, 0x2000000000000, 0x1000000000000, 0x800000000000, 0x400000000000, 0x200000000000, 0x100000000000, 0x80000000000, 0x40000000000, 0x20000000000, 0x10000000000, 0x8000000000, 0x4000000000, 0x2000000000, 0x1000000000, 0x800000000, 0x400000000, 0x200000000, 0x100000000, 0x80000000, 0x40000000, 0x20000000, 0x10000000, 0x8000000, 0x4000000, 0x2000000, 0x1000000, 0x800000, 0x400000, 0x200000, 0x100000, 0x80000, 0x40000, 0x20000, 0x10000, 0x8000, 0x4000, 0x2000, 0x1000, 0x800, 0x400, 0x200, 0x100, 0x80, 0x40, 0x20, 0x10, 0x8, 0x4, 0x2 };

            integers = new List<ulong>() { 0x8000000000000000, 0x4000000000000000, 0x2000000000000000, 0x1000000000000000, 0x800000000000000, 0x400000000000000, 0x200000000000000, 0x100000000000000, 0x80000000000000, 0x40000000000000, 0x20000000000000, 0x10000000000000, 0x8000000000000, 0x4000000000000, 0x2000000000000, 0x1000000000000, 0x800000000000, 0x400000000000, 0x200000000000, 0x100000000000, 0x80000000000, 0x40000000000, 0x20000000000, 0x10000000000, 0x8000000000, 0x4000000000, 0x2000000000, 0x1000000000, 0x800000000, 0x400000000, 0x200000000, 0x100000000, 0x80000000, 0x40000000, 0x20000000, 0x10000000, 0x8000000, 0x4000000, 0x2000000, 0x1000000, 0x800000, 0x400000, 0x200000, 0x100000, 0x80000, 0x40000, 0x20000, 0x10000, 0x8000, 0x4000, 0x2000, 0x1000, 0xa00, 0x600, 0xa0, 0x60, 0xa, 0x6 };

            integers = new List<ulong>() { 0x8000000000000000, 0x4000000000000000, 0x2000000000000000, 0x1000001000101000, 0x800000000000000, 0x400000000000000, 0x200000000000000, 0x100001000101000, 0x80000000000000, 0x40000000000000, 0x20000000000000, 0x10001001111000, 0x8000000000000, 0x4000000000000, 0x2000000000000, 0x1001001111000, 0x800000000000, 0x400000000000, 0x200000000000, 0x101001010000, 0x80000000000, 0x40000000000, 0x20000000000, 0x10101010000, 0x8000000000, 0x4000000000, 0x2000000000, 0x800000000, 0x400000000, 0x200000000, 0x80000000, 0x40000000, 0x20000000, 0x11110000, 0x8000000, 0x4000000, 0x2000000, 0x800000, 0x400000, 0x200000, 0x80000, 0x40000, 0x20000, 0x8000, 0x4000, 0x2000, 0x800, 0x400, 0x200, 0x80, 0x40, 0x20, 0x8, 0x4, 0x2 };

            for (int i = 0; i < F.Count; i++)
            {
                var p = F[i];
                p.SetUlong(integers[i]);
                p.UpdateLm();
            }
            return F;

            */
            // Sort to put system in REF for free!
            F = F.OrderBy(x => x.Lm.Index).Reverse().ToList();

            // Now put it in RREF
            RREF(F);

            return F;

            //return F;
            Console.WriteLine("Before: ");
            foreach (var p in F)
            {
                Console.WriteLine(Convert.ToString((long)p.AsUlong(), 2));
            }

            //return F;

            Console.WriteLine("Before matrix: ");
            Console.Write("[");
            for(int i = 0; i < F.Count; i++)
            {
                var p = F[i];

                var binaryString = Convert.ToString((long)p.AsUlong(), 2);
                int totalLength = p.NumBits;
                string formattedBinaryString = binaryString.PadLeft(totalLength, '0');

                var mStr = String.Join(",", formattedBinaryString.ToList());
                Console.Write($"[{mStr}]");
                if (i != F.Count - 1)
                    Console.Write(",");

            }

            Console.Write("]");

            Console.WriteLine("\n\n");

            // Monomial we are eliminating
            int mi = F[0].NumBits - 1;

            for(int ii = 0; ii < F.Count; ii++)
            {
                if (!Pivot(F, ii, mi))
                {
                    mi -= 1;
                    continue;
                }

                var i = F[ii];
                Debug.Assert(!i.GetBit(mi).IsZero);
  

                for(int ji = ii + 1; ji < F.Count; ji++)
                {
                    var j = F[ji];
                    if (j.GetBit(mi).IsZero)
                        continue;

                    var xor = i + j;
                    F[ji] = xor;
                }

                mi -= 1;
            }

            Console.WriteLine("\n\nAfter: ");
            foreach (var p in F)
            {
                var binaryString = Convert.ToString((long)p.AsUlong(), 2);
                int totalLength = p.NumBits;
                string formattedBinaryString = binaryString.PadLeft(totalLength, '0');
                Console.WriteLine(formattedBinaryString);
            }

            return F;
            Debugger.Break();
        }

        public List<Poly> Buchberger(List<Poly> F)
        {
            var numVars = TableSize.NumVars;

            // Probably illegal.. gaussian elimination
            F = Preprocess(F);

            var G = Autoreduce(F);
            return G;

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
            // Console.WriteLine($"{f} with set len {F.Count}");
            var p = f.Clone();
            var r = new Poly();

            if (F.Count == 0)
                return p;

            // Take `f` and check if its leading monomial is divisible by some other monomial in `F`
            // 
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
                        //Console.WriteLine($"{plm} / {film} => {div}");
                        p = p + F[i] * div;

                        p.UpdateLm();

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
                    p.UpdateLm();
                }
            }

            return r;
        }


        private List<Poly> Autoreduce2(List<Poly> F)
        {

            var P = new List<Poly>(F.Count);

            int numNormal = 0;
            int numIter = 0;
            while(F.Count != 0)
            {
                var h = F[F.Count - 1];
                F.RemoveAt(F.Count - 1);

                numNormal += 1;
                h = NormalForm(h, P);
                if (h.IsZero())
                    continue;

                var hlm = h.Lm;

                int i = 0;
                while (i < P.Count)
                {
                    numIter += 1;
                    if (!P[i].Lm.IsDivisible(hlm))
                    {
                        ++i;
                        continue;
                    }

           
                    F.Add(P[i]);
                    P[i] = P[P.Count - 1];
                    P.RemoveAt(P.Count - 1);
                }

                P.Add(h);
            }

            return null;
        }

        // Heuristic ideas: After gaussian elimination, `NormalForm` returns zero often. We can heuristically spot this possibly... 
        // But thats really hard and requires some cursed logic

        // We could parallelize this with linear algebra too..
        // IsZero: True with prediction True for polyx0*x1*x3*x4, with set [x0 , x1]
        // Most polynomials fold to zero.. if a polynomial is a multiple of some meber of the set... it is zero
        // After doing gaussian elimination, the list of polynomials `F` usually consists of only monomials.. so we could do some kind of parallel(AVX based) check through all (single monomial) polynomials in F.. and see if our poly is a multiple of that monomial
        // But this only works 

        // Note to self: It's faster to store the booleans in bit reversed order.. biggest monomials are at bit index 0
        // Mainly because this creates an upper triangular matrix for free, meaning we can immediately do backward elimination. If it's lower triangular, I think we have to do some pivoting
        private static List<Poly> Autoreduce(List<Poly> F)
        {
            //F = F.OrderByDescending(x => x.GetDegree()).ToList();
            //F.Sort(x => x.PopCount());

            //F = F.OrderByDescending(x => x.Lm).ToList();
            //F = F.OrderBy(x => x.Lm).ToList();


            //F = F.OrderBy(x => x).ToList();


            var g = F.Select(x => x.Clone()).ToList();
            var P = new List<Poly>();
            ulong pCombinedMask = 0;

            var reducedSet = new List<Poly>();
            var notReducedSet = new List<Poly>();

            bool log = false;

            while (g.Any())
            {
                //foreach(var p in )

                var h = g.Last();
                g.RemoveAt(g.Count - 1);
                var before = h.Clone();

                //if (before.ToString() == "x0*x1*x2*x3*x4*x5")
                //    Debugger.Break();

                //var hMask = h.AsUlong();
                var hMask = (ulong)h.Lm.Index;
                bool prediction = (hMask & pCombinedMask) != hMask;

                /*
                foreach (var m in h.Monomials)
                {
                    pCombinedMask |= (1UL << m.Index);
                }
                */

                // Condition where it's zero... all monomials 

                h = NormalForm(h, P);

                bool changed = h.AsUlong() != before.AsUlong();


                //Console.WriteLine(changed);
                //Console.WriteLine($"{prediction == changed}");
                var setStr = String.Join(" , ", P);

                Console.WriteLine($"IsZero: {h.IsZero()} with prediction {prediction} for poly{before}, with set [{setStr}]");
                if (log)
                {
                    if (h.IsZero())
                        notReducedSet.Add(before);
                    else
                        reducedSet.Add(before);
                }

                if (h.IsZero())
                    continue;

                // Compute and cache leading monomial since this has not happened before
                h.UpdateLm();
                var hlm = h.Lm;

                //pCombinedMask = 0;
                var newP = new List<Poly>();
                foreach (var itp in P)
                {
                    if (itp.Lm.IsDivisible(hlm))
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
                    //pCombinedMask |= (1UL << poly.Lm.Index);
                    pCombinedMask |= (ulong)poly.Lm.Index;
                }


                
            }

            return P;

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
