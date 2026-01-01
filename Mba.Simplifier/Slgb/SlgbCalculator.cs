using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Minimization;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Metrics;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

// This file implements an attempt at constructing groebner bases for booleans with constants, e.g. (x&1111)|(y&535454)|1010.
// It works on some booleans, but fails on others. It's probably impossible in the general case due to division being undefined for booleans with different bitmasks.
namespace Mba.Simplifier.Slgb
{
    public class Globs
    {
        public static int Width = 64;

        public static ulong ModuloMask = ulong.MaxValue;
    }

    public struct Monomial : IEquatable<Monomial>, IComparable<Monomial>
    {
        // This is more of a bitmask than a coefficient...
        // but we're also working with polynomials where we pretend bitmasking don't exist..
        public readonly ulong Coefficient;

        public readonly ulong? Constant;

        public bool IsConstant => Constant != null;

        public readonly ulong Vars;

        public int TotalDeg => BitOperations.PopCount(Vars);

        public static Monomial CreateConstant(ulong constant)
            => new Monomial(constant);

        public static Monomial CreateProduct(ulong coefficient, ulong varMask)
        {
            // 0&(a&b) == 0
            if (coefficient == 0)
                return CreateConstant(0);
            if (varMask == 0)
                return CreateConstant(0);

            return new Monomial(coefficient, varMask);
        }

        private Monomial(ulong coefficient, ulong vars)
        {
            Coefficient = coefficient;
            Vars = vars;
        }

        private Monomial(ulong constant)
        {
            Constant = constant;
        }

        public bool Equals(Monomial other)
        {
            if (Coefficient != other.Coefficient)
                return false;
            if (Constant != other.Constant) 
                return false;
            if (Vars != other.Vars)
                return false;

            return true;
        }

        public override string ToString()
        {
            if (IsConstant)
                return Constant.Value.ToString();

            var terms = new List<string>();
            for (ushort i = 0; i < 64; i++)
            {
                if ((Vars & (1ul << i)) == 0)
                    continue;
                terms.Add($"x{i}");
            }

            return $"({Coefficient}*({String.Join('&', terms)}))";
        }

        public override int GetHashCode()
        {
            if (IsConstant)
                return Constant.Value.GetHashCode();

            return Coefficient.GetHashCode() + Vars.GetHashCode();
        }

        // TODO: Handle constant case
        public int CompareTo(Monomial other)
        {
            return Vars.CompareTo(other.Vars);
        }

        private static int CompareTo(Monomial a, Monomial b)
        {
            int first = 1;
            int last = -1;

            if (a.Equals(b))
                return 0;
            if (a.IsConstant && b.IsConstant)
                return a.Constant.Value.CompareTo(b.Constant.Value);
            if (a.IsConstant)
                return first;
            else if (b.IsConstant)
                return last;

            if (a.TotalDeg > b.TotalDeg)
                return first;
            else if (a.TotalDeg < b.TotalDeg)
                return last;

            // Otherwise the total degrees are equal...
            // Resort to lexicographic order
            if (a.Vars > b.Vars)
                return first;
            else if (a.Vars < b.Vars)
                return last;

            // In this case we two identical modulos, just with different coefficients... 
            // Sort by their coefficients:
            return a.Coefficient.CompareTo(b.Coefficient);
        }

        public static Monomial operator *(Monomial a, Monomial b)
        {
            if(a.IsConstant & b.IsConstant)
            {
                return CreateConstant(a.Constant.Value & b.Constant.Value);
            }

            // Move constant to the right 
            if (b.IsConstant)
                (a, b) = (b, a);

            // constant * (coeff*b.vars)
            if (a.IsConstant)
                return CreateProduct(a.Constant.Value & b.Coefficient, b.Vars);

            // Otherwise have have (coeff*conj1) * (coeff*conj2)
            return CreateProduct(a.Coefficient & b.Coefficient, a.Vars | b.Vars);
        }

        public bool IsDivisible(Monomial other)
            => IsDivisible(this, other);

        public static bool IsDivisible(Monomial a, Monomial b)
        {
            // If we have x/1 on any field.. yield true...
            // F... in the case of x/b10.... that gets messy....
            // if (other.isOne())
            //if (b.IsConstant && b.Constant.Value != 0)
            //    return true;
            if (b.IsConstant && b.Constant.Value == Globs.ModuloMask)
                return true;
            // else if (this.isOne())
            //if (a.IsConstant && a.Constant.Value != 0)
            //    return false;
            if (a.IsConstant && a.Constant != 0)
                return false;
            if (a.IsConstant)
                Debugger.Break();

            // In this case one of the constants is zero completely.. which shouldn't be happening..
            if(a.IsConstant || b.IsConstant)
            {
                Debugger.Break();
                return false;
            }

            bool varsMatch = a.Vars == (a.Vars | b.Vars);
            bool coeffsMatch = a.Coefficient == b.Coefficient;
            //bool coeffsMatch = (a.Coefficient & b.Coefficient) != 0;
            //bool coeffsMatch = a.Coefficient == (a.Coefficient | b.Coefficient);
            //var product = (a.Coefficient & b.Coefficient);
            //bool coeffsMatch = (product != 0) && product != a.Coefficient && product != b.Coefficient;
            //bool coeffsMatch = (a.Coefficient == b.Coefficient) || b.Coefficient == Globs.ModuloMask;
            return varsMatch && coeffsMatch;
        }

        public static Monomial operator /(Monomial a, Monomial b)
        {
            // If the two monomials are equal then we have a constant of 1(sign extended to the bit width,
            // because x/x == 1
            if (a.Equals(b))
                return CreateConstant(ulong.MaxValue & Globs.ModuloMask);

            // If we just two constants, divide them. This forms a truth table:
            // 00 => 0
            // 01 => 0
            // 10 => 0
            // 11 => 1
            if(a.IsConstant && b.IsConstant)
            {
                return Monomial.CreateConstant(a.Constant.Value & b.Constant.Value);
            }

            // constant / monomial = undefined?
            // 1 / b
            // ???????????????
            if (a.IsConstant)
            {
                return Monomial.CreateConstant(0);
                //throw new InvalidOperationException($"Undefined behavior");
            }

            // This case(mask&a) / constant forms another truth table:
            // E.g. (b1111 & a&b) / b1010 => b1010&a&b
            // a / 0 = 0
            // b / 1 = b
            if(b.IsConstant)
            {
                return CreateProduct(a.Coefficient & b.Constant.Value, a.Vars);
            }
            
            // Coefficients must match for division to be defined..
            //if(a.Coefficient != b.Coefficient)
            //    return CreateConstant(0);
            // x/x==1
            if (a.Vars == b.Vars)
            {
                return CreateProduct(a.Coefficient & b.Coefficient, a.Vars);
            }
            // Otherwise we have same coefficients but different variables..

            // 10*(x0&x1) / 10*(x0&x1)
            // Otherwise we finally have the form of (mask&a&b) & (mask&a&b&c)
            // If the monomials are not divisible then we just yield zero.
            // This is at least in line with symbsat... https://github.com/pavel-fokin/SymbSAT/blob/master/symbsat-cpp/monom.h#L148
            bool isMonomialDivisible = a.Vars == (a.Vars | b.Vars);
            if (!isMonomialDivisible)
                return CreateConstant(0);
            // If the coefficients would cancel out(equal to zero), e.g. b1010 & b0101 == b0000, we yield zero
            if ((a.Coefficient & b.Coefficient) == 0)
                return CreateConstant(0);

            // Otherwise this is divisble...
            var varMask = a.Vars ^ b.Vars;
            var coefficient = a.Coefficient & b.Coefficient;
            return CreateProduct(coefficient, varMask);
        }
    }

    public class Polynomial
    {
        public readonly List<Monomial> Monomials;

        public Monomial Lm => Monomials.Last();

        public bool IsZero => Monomials.Count == 0;

        public Polynomial(List<Monomial> monomials)
        {
            Monomials = Canonicalize(monomials.ToList());
        }

        public Polynomial Clone()
            => new Polynomial(Monomials.ToList());

        private static List<Monomial> Mul(List<Monomial> p1, List<Monomial> p2)
        {
            var monomials = new List<Monomial>();
            for(int i = 0; i < p1.Count; i++)
            {
                for(int j = i + 1; j < p2.Count; j++)
                {
                    monomials.Add(p1[i] * p2[j]);
                }
            }

            return Canonicalize(monomials);
        }

        private static List<Monomial> Mul(List<Monomial> poly, Monomial factor)
        {
            var output = new List<Monomial>();
            foreach (var m in poly)
                output.Add(m * factor);

            return Canonicalize(output);
        }

        // Return the canonicalized sum of two polynomials
        private static List<Monomial> Add(List<Monomial> a, List<Monomial> b) => Canonicalize(a.Concat(b));

        // Reduce modulo 2 then sort by monomial order
        private static List<Monomial> Canonicalize(IEnumerable<Monomial> monomials)
        {
            ulong constant = 0;
            var counts = new Dictionary<Monomial, int>();
            foreach (var monom in monomials)
            {
                if (monom.IsConstant)
                {
                    constant ^= monom.Constant.Value;
                    continue;
                }

                counts.TryAdd(monom, 0);
                counts[monom] += 1;
            }

            var output = new List<Monomial>();
            foreach (var (monom, count) in counts)
            {
                if ((count & 1) == 0)
                    continue;

                output.Add(monom);
            }

            if (constant != 0)
                output.Add(Monomial.CreateConstant(constant));

            output.Sort();
            return output;
        }

        public override string ToString()
        {
            return String.Join(" + ", Monomials);
        }

        public override int GetHashCode()
        {
            int hash = 17;
            foreach (var monom in Monomials)
                hash += 31 * monom.GetHashCode();

            return hash;
        }

        public override bool Equals(object? obj)
        {
            if (obj is not Polynomial other)
                return false;

            return Monomials.SequenceEqual(other.Monomials);
        }

        public static Polynomial operator +(Polynomial a, Polynomial b)
        {
            return new Polynomial(Add(a.Monomials, b.Monomials));
        }

        public static Polynomial operator +(Polynomial a, Monomial b)
        {
            return new Polynomial(Add(a.Monomials, new() { b }));
        }

        public static Polynomial operator *(Polynomial a, Polynomial b)
        {
            return new Polynomial(Mul(a.Monomials, b.Monomials));
        }

        public static Polynomial operator *(Polynomial poly, Monomial m)
        {
            return new Polynomial(Mul(poly.Monomials, m));
        }
    }

    public class SlgbCalculator
    {
        // Represent polynomial as a list of monomials.... 
        public void Run(AstCtx ctx, TruthTable table)
        {
            if (table.GetBit(0))
                throw new InvalidOperationException($"Constant offset");

            var polys = new List<List<uint>>();
            for (int i = 0; i < table.NumBits; i++)
            {
                // Skip nil rows
                if (!table.GetBit(i))
                    continue;

                // If the row is positive, construct algebraic normal form for this row.
                // TODO: Use a more space / time efficienty method, 'GetRowAnf' is overkill.
                var monoms = GetRowAnf(table.NumVars, i);
                polys.Add(monoms);
            }


            var system = polys
                .Select(x => new Polynomial(x.Select(y => Monomial.CreateProduct(1, y)).ToList()))
                .ToList();

            var gb = Buchberger(system);

        }

        // Convert a single truth table row to algebraic normal form
        public static unsafe List<uint> GetRowAnf(int numVars, int idx)
        {
            var variableCombinations = MultibitSiMBA.GetVariableCombinations(numVars);

            var resultVec = new ulong[(int)Math.Pow(2, numVars)];
            resultVec[idx] = 1;

            // Keep track of which variables are demanded by which combination,
            // as well as which result vector idx corresponds to which combination.
            var groupSizes = MultibitSiMBA.GetGroupSizes(numVars);
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var comb = variableCombinations[i];
                var myIndex = MultibitSiMBA.GetGroupSizeIndex(groupSizes, comb);
                combToMaskAndIdx.Add((comb, (int)myIndex));
            }

            var varCount = numVars;
            bool onlyOneVar = varCount == 1;
            int width = (int)(varCount == 1 ? 1 : 2u << (ushort)(varCount - 1));
            List<uint> terms = new();
            fixed (ulong* ptr = &resultVec[0])
            {
                for (int i = 0; i < variableCombinations.Length; i++)
                {
                    // Fetch the result vector index for this conjunction.
                    // If the coefficient is zero, we can skip it.
                    var comb = variableCombinations[i];
                    var (trueMask, index) = combToMaskAndIdx[i];
                    var coeff = ptr[index];
                    if (coeff == 0)
                        continue;

                    // Subtract the coefficient from the result vector.
                    MultibitSiMBA.SubtractCoeff(1, ptr, 0, coeff, index, width, varCount, onlyOneVar, trueMask);
                    terms.Add((uint)variableCombinations[i]);
                }
            }

            return terms;
        }

        public List<Polynomial> Buchberger(List<Polynomial> polys)
        {
            var G = polys;
            //var G = Autoreduce(polys);
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


            var pqs = new WorkList<(Polynomial, Polynomial)>();
            for(int i = 0; i < polys.Count; i++)
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
                    
                if(!h.IsZero)
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

        private static Polynomial Spoly(Polynomial f, Polynomial g)
        {
            var flm = f.Lm;
            var glm = g.Lm;

            //if (flm.ToString() == "1*(x3)" && glm.ToString() == "1*(x0&x1&x2)")
            //    Debugger.Break();
            var lcm = flm * glm;

            var div1 = (lcm / flm);
            var div2 = (lcm / glm);
            var m1 = f * div1;
            var m2 = g * div2;
            var res = m1 + m2;
            return res;
        }

        private static Polynomial NormalForm(Polynomial f, List<Polynomial> F)
        {
            Polynomial p = f.Clone();
            Polynomial r = new Polynomial(new());

            if (F.Count == 0)
                return p;

            while(!p.IsZero)
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

        private static List<Polynomial> Autoreduce(List<Polynomial> F)
        {
            var g = F.Select(x => x.Clone()).ToList();
            var P = new List<Polynomial>();

            while(g.Any())
            {
                var h = g.Last();
                g.RemoveAt(g.Count - 1);
                h = NormalForm(h, P);
                if(!h.IsZero)
                {
                    var newP = new List<Polynomial>();
                    foreach(var itp in P)
                    {
                        if(itp.Lm.IsDivisible(h.Lm))
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
            for(int i = 0; i < pSize; i++)
            {
                var h = P.First();
                P.RemoveAt(0);
                h = NormalForm(h, P);
                if(h.IsZero)
                {
                    --pSize;
                }

                else
                {
                    P.Add(h);
                }
            }

            Console.WriteLine($"Computed groebner basis with {P.Count} elements\n[\n{String.Join("\n", P.Select(x => "    " + x.ToString() + ","))}\n]");


            var union = String.Join(" | ", P.Select(x => $"({x})"));

            union = union.Replace("*", "&");
            union = union.Replace("+", "^");


            Console.WriteLine($"Boolean: {union}");

            //Debugger.Break();
            return P;
        }

        public static List<Polynomial> Optimize(List<Polynomial> polys)
        {
            var output = new List<Polynomial>();

            var varsToCoeff = new Dictionary<ulong, ulong>();
            foreach(var poly in polys)
            {
                if(poly.Monomials.Count != 1)
                {
                    output.Add(poly);
                    continue;
                }

                var m = poly.Monomials.Single();
                varsToCoeff.TryAdd(m.Vars, 0);
                varsToCoeff[m.Vars] |= m.Coefficient;
            }

            foreach(var (vMask, coeff) in varsToCoeff)
            {
                output.Add(new Polynomial(new() { Monomial.CreateProduct(coeff, vMask) }));
            }

            return output;
        }
    }
}
