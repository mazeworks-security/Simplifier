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

    public class Poly : IComparable<Poly>, IEquatable<Poly>
    {
        public SortedDictionary<Monomial, long> Coeffs { get; private set; }

        public Monomial Lm => Coeffs.First().Key;

        public Poly(Dictionary<Monomial, long> coeffs)
        {
            Coeffs = new SortedDictionary<Monomial, long>(coeffs);
        }

        public Poly(SortedDictionary<Monomial, long> coeffs) : this(coeffs.ToDictionary())
        {

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

        public static Poly Reduce(Poly f, List<Poly> basis)
        {
            return NormalForm(f, basis);
        }

        public static Poly NormalForm(Poly f, List<Poly> basis)
        {
            var p = f.Clone();
            var r = new Poly();

            // Cache LMs of basis for efficiency
            var basisEntries = basis.Where(b => b.Coeffs.Count > 0)
                                    .Select(b => new { Poly = b, Lm = b.Lm, Lc = b.Coeffs[b.Lm] })
                                    .Reverse()
                                    .ToList();

            while (p.Coeffs.Count > 0)
            {
                p.Simplify();
                if (p.Coeffs.Count == 0) break;

                var lt_p_monom = p.Lm;
                var lt_p_coeff = p.Coeffs[lt_p_monom];

                bool divided = false;
                foreach (var entry in basisEntries)
                {
                    if (entry.Lm.Divides(lt_p_monom))
                    {
                        if (lt_p_coeff % entry.Lc == 0)
                        {
                            long c = lt_p_coeff / entry.Lc;
                            var m = lt_p_monom.Divide(entry.Lm);

                            var subC = -1 * c;
                            var subM = m;
                            var g = entry.Poly;

                            foreach (var kp in g.Coeffs)
                            {
                                var newCoeff = subC * kp.Value;
                                var newMonom = subM * kp.Key;
                                p.Add(newMonom, newCoeff);
                            }

                            divided = true;
                            break;
                        }
                    }
                }

                if (!divided)
                {
                    // No divisor found for LT(p), move it to remainder
                    r.Add(lt_p_monom, lt_p_coeff);
                    p.Remove(lt_p_monom);
                }
            }
            r.Simplify();
            return r;
        }


        public void Simplify()
        {
            var toRemove = Coeffs.Where(x => x.Value == 0).Select(x => x.Key).ToList();
            foreach (var del in toRemove)
                Coeffs.Remove(del);
        }

        public void PruneDuplicates()
        {
            var clone = Coeffs.ToDictionary(x => x.Key, x => x.Value);
            Coeffs.Clear();
            foreach (var (m, c) in clone)
            {
                Add(new Monomial(m.SortedVars.Distinct()), c);
            }
            //Coeffs = new(Coeffs.ToDictionary(x => new Monomial(x.Key.SortedVars.Distinct()), x => x.Value)); 
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

        public Poly Rhs()
        {
            var coeff = Coeffs[Lm];
            var p = Clone();
            p.Remove(Lm);
            if (coeff == 1)
                p = -1L * p;
            else
                Debug.Assert(coeff == -1);

            return p;
        }

        public void Replace(Monomial a, Poly other)
        {
            var coeff = Coeffs[a];
            Remove(a);

            other = coeff * other;
            var sum = Add(this, other);
            Coeffs = sum.Coeffs;
        }

        public bool ReplaceSubset(Monomial a, Poly other)
        {


            var toReplace = Coeffs.Where(x => a.Divides(x.Key))
                                  .Select(x => (x.Key, x.Value))
                                  .ToList();

            if (toReplace.Count == 0)
                return false;

            foreach (var (m, coeff) in toReplace)
            {
                // Remove the original term
                Coeffs.Remove(m);

                // Compute the remainder: m / a
                // Since a.Divides(m), the remainder is well-defined.
                // Monomial.Divide computes this - other (multiset difference)
                var remainder = m.Divide(a);

                // Compute the replacement term: coeff * remainder * other
                // 'other' is the polynomial that replaces 'a'
                var termFactor = coeff * remainder;
                var replacementPoly = termFactor * other;

                // Add the expanded terms to the polynomial
                foreach (var (pm, pc) in replacementPoly.Coeffs)
                {
                    Add(pm, pc);
                }
            }

            this.Simplify();

            return true;
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

        public bool IsEq(Poly other)
        {
            return Coeffs.Count == other.Coeffs.Count && Coeffs.OrderBy(x => x.Key).SequenceEqual(other.Coeffs.OrderBy(x => x.Key));
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

        public int CompareTo(Poly? other)
        {
            if (other == null) return 1;

            using var thisEnum = Coeffs.GetEnumerator();
            using var otherEnum = other.Coeffs.GetEnumerator();

            while (thisEnum.MoveNext())
            {
                if (!otherEnum.MoveNext())
                    return 1;

                var thisMonom = thisEnum.Current.Key;
                var otherMonom = otherEnum.Current.Key;

                int cmp = thisMonom.CompareTo(otherMonom);
                if (cmp != 0)
                    return -cmp; // Invert because Monomial.CompareTo is negated

                int coeffCmp = thisEnum.Current.Value.CompareTo(otherEnum.Current.Value);
                if (coeffCmp != 0)
                    return coeffCmp;
            }

            if (otherEnum.MoveNext())
                return -1;

            return 0;
        }

        public override string ToString()
        {
            return String.Join(" + ", Coeffs.Select(x => $"{x.Value}*({x.Key})"));
        }

        public override bool Equals(object? obj)
        {
            if (obj is Poly other)
                return Equals(other);
            return false;
        }

        public bool Equals(Poly? other)
        {
            if (other is null) return false;
            if (ReferenceEquals(this, other)) return true;
            return IsEq(other);
        }

        public override int GetHashCode()
        {
            int hash = 17;
            foreach (var (m, c) in Coeffs)
            {
                hash = hash * 31 + m.GetHashCode();
                hash = hash * 31 + c.GetHashCode();
            }
            return hash;
        }

        public static bool operator ==(Poly? left, Poly? right)
        {
            if (ReferenceEquals(left, right)) return true;
            if (left is null || right is null) return false;
            return left.Equals(right);
        }

        public static bool operator !=(Poly? left, Poly? right)
            => !(left == right);
    }

    public class Monomial : IEquatable<Monomial>, IComparable<Monomial>
    {
        public const bool LEXORDER = true;

        public readonly List<SymVar> SortedVars;

        public int Degree => SortedVars.Count;

        private readonly int hash = 17;

        public static Monomial Quadratic(SymVar var)
            => new Monomial(new SymVar[] { var, var}, distinct: false);

        // TODO: If a variable is boolean, eliminate x*x constraints
        public Monomial(IEnumerable<SymVar> vars, bool distinct = true)
        {
            if (distinct)
                vars = vars.Distinct();

            if (LEXORDER)
                SortedVars = vars.OrderByDescending(x => x).ToList();
            else
                SortedVars = vars.OrderByDescending(x => x).ToList();



            foreach (var v in SortedVars)
                hash = hash * 23 + v.GetHashCode();
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

        public static bool operator <(Monomial left, Monomial right)
            => left.CompareTo(right) < 0;

        public static bool operator >(Monomial left, Monomial right)
            => left.CompareTo(right) > 0;

        public static bool operator <=(Monomial left, Monomial right)
            => left.CompareTo(right) <= 0;

        public static bool operator >=(Monomial left, Monomial right)
            => left.CompareTo(right) >= 0;

        public override string ToString()
        {
            return String.Join("*", SortedVars);
        }

        public override int GetHashCode()
        {
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

        public Monomial Divide(Monomial other)
        {
            var vars = new List<SymVar>(SortedVars);
            foreach (var v in other.SortedVars)
            {
                vars.Remove(v);
            }
            return new Monomial(vars);
        }

        public bool Divides(Monomial other)
        {

            if (SortedVars.Count > other.SortedVars.Count)
                return false;

            return SortedVars.ToHashSet().IsSubsetOf(other.SortedVars);

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

        public int CompareTo(Monomial? o)
        {


            var (t, other) = (this, o);


            if (LEXORDER)
            {
                int minLen = Math.Min(t.SortedVars.Count, other.SortedVars.Count);
                for (int i = 0; i < minLen; i++)
                {
                    int cmp = t.SortedVars[i].CompareTo(other.SortedVars[i]);
                    if (cmp != 0)
                        return -cmp;
                }
                return -(t.SortedVars.Count.CompareTo(other.SortedVars.Count));
            }

            if (t.Equals(other))
                return 0;

            int degDiff = t.SortedVars.Count - other.SortedVars.Count;
            if (degDiff != 0)
                return -degDiff;

            var allVars = new SortedSet<SymVar>();
            var thisExp = new Dictionary<SymVar, int>();
            var otherExp = new Dictionary<SymVar, int>();

            foreach (var v in t.SortedVars)
            {
                allVars.Add(v);
                thisExp.TryGetValue(v, out int c);
                thisExp[v] = c + 1;
            }
            foreach (var v in other.SortedVars)
            {
                allVars.Add(v);
                otherExp.TryGetValue(v, out int c);
                otherExp[v] = c + 1;
            }

            foreach (var v in allVars.Reverse())
            {
                thisExp.TryGetValue(v, out int a);
                otherExp.TryGetValue(v, out int b);
                if (a != b)
                    return a - b;
            }

            return 0;
        }
    }

    public enum SymKind
    {
        Input = 0,
        InternalGate = 1,
        Output = 2, // This is highly dubious, change this.
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
            var (v0, v1) = (this, other);
            //var (v1, v0) = (this, other);

            var below = 1;
            var above = -1;

            var cmp = v0.Kind.CompareTo(v1.Kind);
            if (cmp != 0)
                return cmp;
            cmp = v0.BitIndex.CompareTo(v1.BitIndex);
            if (cmp != 0)
                return cmp;
            cmp = v0.TotalOrder.CompareTo(v1.TotalOrder);
            if (cmp != 0)
                return cmp;
            cmp = v0.Name.CompareTo(v1.Name);
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
