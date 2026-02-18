using Mba.Simplifier.Bindings;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Verification
{

    public class Poly
    {
        public Dictionary<Monomial, long> Coeffs { get; private set; }

        public Monomial Lm => Coeffs.Keys.Max();

        public Poly(Dictionary<Monomial, long> coeffs)
        {
            Coeffs = coeffs.ToDictionary();
        }

        public Poly(IEnumerable<Monomial> coeffs)
        {
            Coeffs = new();
            foreach (var m in coeffs)
                Add(m, 1);
        }

        public Poly()
        {
            Coeffs = new();
        }

        public void Simplify()
        {
            var toRemove = Coeffs.Where(x => x.Value == 0).Select(x => x.Key).ToList();
            foreach (var del in toRemove)
                Coeffs.Remove(del);


        }

        public void ReduceMod(uint w)
        {
            foreach (var key in Coeffs.Keys.ToList())
                Coeffs[key] &= (long)ModuloReducer.GetMask(w);
        }

        public Poly(params Monomial[] coeffs) : this(coeffs.AsEnumerable())
        {
        }

        public static Poly Add(Poly a, Poly b)
        {
            var output = new Poly();
            foreach (var p in new Poly[] { a, b })
            {
                foreach (var (m, c) in p.Coeffs)
                    output.Add(m, c);
            }

            return output;
        }

        public void SetCoeff(Monomial m, long coeff)
        {
            Coeffs[m] = coeff;
        }

        public void Add(Monomial m, long coeff)
        {
            Coeffs.TryGetValue(m, out var existing);
            existing += coeff;
            Coeffs[m] = existing;
        }

        public void Sub(Monomial m, long coeff)
        {
            Add(m, -1 * coeff);
        }

        public void Replace(Monomial a, Poly other)
        {
            var coeff = Coeffs[a];
            Remove(a);

            other = coeff * other;
            var sum = Add(this, other);
            Coeffs = sum.Coeffs;
        }

        public void Remove(Monomial a) => Coeffs.Remove(a);


        public static Poly Mul(Poly a, Poly b)
        {
            var outPoly = new Poly();
            foreach (var (monomA, coeffA) in a.Coeffs)
            {
                var isAConstant = IsConstant(monomA);
                foreach (var (monomB, coeffB) in b.Coeffs)
                {
                    var newCoeff = coeffA * coeffB;

                    // Then we need to construct a new monomial.
                    Monomial newMonom = monomA * monomB;
                    outPoly.Add(newMonom, newCoeff);
                }
            }

            return outPoly;
        }

        public static bool IsConstant(Monomial m)
        {
            return m.SortedVars.Count == 0;
        }


        public Poly Clone()
        {
            return new Poly(Coeffs);
        }

        public static Poly operator +(Poly a, Poly b)
            => Poly.Add(a, b);

        public static Poly operator -(Poly a, Poly b)
            => Poly.Add(a, -1 * b);

        public static Poly operator +(Poly a, SymVar b)
            => Poly.Add(a, new Monomial(b));

        public static Poly operator -(Poly a, SymVar b)
          => Poly.Add(a, new Monomial(b));

        public static Poly operator *(long coeff, Poly a)
        {
            var output = new Poly();
            foreach (var (m, c) in a.Coeffs.ToDictionary())
                output.Add(m, c * coeff);
            return output;
        }
        public static Poly operator *(Poly a, Poly b)
            => Poly.Mul(a, b);


        public unsafe static implicit operator Poly(Monomial m) => new Poly(m);

        public unsafe static implicit operator Poly(SymVar m) => new Poly(new Monomial(m));

        public static Poly Constant(long value)
        {
            return new Poly() { Coeffs = { { new Monomial(), value } } };
        }

        public override string ToString()
        {
            return String.Join(" + ", Coeffs.OrderByDescending(x => x.Key).Select(x => $"{x.Value}*({x.Key})"));
        }
    }

    public class Monomial : IEquatable<Monomial>, IComparable<Monomial>
    {
        public readonly List<SymVar> SortedVars;

        public Monomial(IEnumerable<SymVar> vars)
        {
            SortedVars = vars.Distinct().OrderByDescending(x => x).ToList();
        }

        public Monomial(params SymVar[] vars) : this(vars.AsEnumerable())
        {

        }

        public static Monomial Constant()
            => new Monomial();

        public static Poly operator *(long coeff, Monomial a)
        {
            return new Poly(new Dictionary<Monomial, long>() { { a, coeff } });
        }

        public static Monomial operator *(Monomial a, Monomial b)
        {
            return new Monomial(a.SortedVars.AsEnumerable().Concat(b.SortedVars));
        }

        public static bool operator ==(Monomial? left, Monomial? right)
        {
            if (ReferenceEquals(left, right))
                return true;
            if (ReferenceEquals(left, null) || ReferenceEquals(right, null))
                return false;
            return left.Equals(right);
        }

        public static bool operator !=(Monomial? left, Monomial? right)
        {
            return !(left == right);
        }

        public override string ToString()
        {
            return String.Join("*", SortedVars);
        }

        public override int GetHashCode()
        {
            var hash = 17;
            foreach (var v in SortedVars)
                hash += 31 * v.GetHashCode();
            return hash;
        }

        public override bool Equals(object? obj)
        {
            if (obj is Monomial other)
                return Equals(other);
            return false;
        }

        public bool Equals(Monomial? other)
        {
            return SortedVars.SequenceEqual(other.SortedVars);
        }

        
        public bool Divides(Monomial other)
        {
            if (SortedVars.Count > other.SortedVars.Count)
                return false;

            int j = 0;
            for (int i = 0; i < SortedVars.Count; i++)
            {
                while (j < other.SortedVars.Count && other.SortedVars[j].CompareTo(SortedVars[i]) > 0)
                    j++;

                if (j >= other.SortedVars.Count || !other.SortedVars[j].Equals(SortedVars[i]))
                    return false;

                j++;
            }

            return true;
        }

        public int CompareTo(Monomial? other)
        {
            var below = 1;
            var above = -1;

            if (this == other)
                return 0;

            for (int i = 0; i < Math.Min(SortedVars.Count, other.SortedVars.Count); i++)
            {
                var a = SortedVars[i];
                var b = other.SortedVars[i];
                var cmp = a.CompareTo(b);
                if (cmp != 0)
                    return cmp;
            }

            var tie = SortedVars.Count.CompareTo(other.SortedVars.Count);
            if (tie == 0)
                Debugger.Break();
            return tie;
        }
    }

    public enum SymKind
    {
        Input = 1,
        InternalGate = 2,
        Output = 3,
    }

    public struct SymVar : IEquatable<SymVar>, IComparable<SymVar>
    {
        public SymKind Kind { get; set; }

        public int BitIndex { get; private set; }

        public uint TotalOrder { get; set; }

        public string Name { get; set; }

        public static SymVar Symbol(AstCtx ctx, AstIdx idx, int bitIdx)
            => new SymVar() { Kind = SymKind.Input, Name = $"{ctx.GetSymbolName(idx)}{bitIdx}", BitIndex = bitIdx };

        public static SymVar Symbol(AstCtx ctx, string name, int bitIdx)
           => new SymVar() { Kind = SymKind.Input, Name = name, BitIndex = bitIdx };

        public static SymVar Temp(SymKind kind, int bitIdx, uint sliceIndex, string name)
            => new SymVar() { Kind = kind, BitIndex = bitIdx, TotalOrder = sliceIndex, Name = name };

        public static Poly operator *(long coeff, SymVar a)
        {
            return new Poly(new Dictionary<Monomial, long>() { { new Monomial(a), coeff } });
        }

        public override string ToString()
            => Name;

        public override bool Equals([NotNullWhen(true)] object? obj)
        {
            if (obj is SymVar other)
                return Equals(other);
            return false;
        }

        public bool Equals(SymVar other)
        {
            return Kind == other.Kind && Name == other.Name && this.BitIndex == other.BitIndex;
        }

        public int CompareTo(SymVar other)
        {
            var below = 1;
            var above = -1;

            var cmp = Kind.CompareTo(other.Kind);
            if (cmp != 0)
                return cmp;
            cmp = BitIndex.CompareTo(other.BitIndex);
            if (cmp != 0)
                return cmp;
            cmp = TotalOrder.CompareTo(other.TotalOrder);
            if (cmp != 0)
                return cmp;
            cmp = Name.CompareTo(other.Name);
            if (cmp != 0)
                return cmp;

            return 0;
        }

        public override int GetHashCode()
        {
            return Kind.GetHashCode() + Name.GetHashCode() + BitIndex.GetHashCode();
        }
    }

}
