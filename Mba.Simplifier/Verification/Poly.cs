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
        public SortedDictionary<Monomial, long> Coeffs { get; set; }

        public Monomial Lm
        {
            get
            {
                // Avoid boxing
                var e = Coeffs.GetEnumerator();
                e.MoveNext();
                return e.Current.Key;
            }
        }

        public long Lcoeff
        {
            get
            {
                var e = Coeffs.GetEnumerator();
                e.MoveNext();
                return e.Current.Value;
            }
        }

        public Poly(SymVar sv) : this(new Monomial(sv))
        {

        }

        public Poly(params SymVar[] sv) : this(new Monomial(sv))
        {

        }


        public Poly(SortedDictionary<Monomial, long> coeffs) : this()
        {
            Coeffs = coeffs;
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
                            //long c = lt_p_coeff / entry.Lc;
                            long c = (long)((ulong)lt_p_coeff / (ulong)entry.Lc);
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
            ReduceMod();


            Monomial[] keys = null;
            int count = 0;
            foreach (var kv in Coeffs)
            {
                if (kv.Value == 0)
                {
                    keys ??= new Monomial[Coeffs.Count];
                    keys[count++] = kv.Key;
                }
            }

            for (int i = 0; i < count; i++)
                Coeffs.Remove(keys[i]);
        }

        public void PruneDuplicates()
        {
            var clone = Coeffs.ToDictionary(x => x.Key, x => x.Value);
            Coeffs.Clear();
            foreach (var (m, c) in clone)
            {
                Add(m, c);
            }
            //Coeffs = new(Coeffs.ToDictionary(x => new Monomial(x.Key.SortedVars.Distinct()), x => x.Value)); 
        }

        public long ReduceCoeff(long value)
        {
            //return value;

            var w = GroebnerVerifier.w;
            var mod = ((long)ModuloReducer.GetMask(w));
            return value & mod;

        }

        public void ReduceMod(uint ingore = 0)
        {
            //return;
            /*
            var w = GroebnerVerifier.w;
            var mod = ((long)ModuloReducer.GetMask(w)) + 1;
            foreach (var key in Coeffs.Keys.ToList())
                Coeffs[key] %= mod;
            */
            
            foreach (var key in Coeffs.Keys.ToList())
                Coeffs[key] = ReduceCoeff(Coeffs[key]);
            
            
            //foreach (var key in Coeffs.Keys.ToList())
            //   Coeffs[key] &= (long)ModuloReducer.GetMask(w);
        }

        public Poly(params Monomial[] coeffs) : this(coeffs.AsEnumerable())
        {
        }

        public static Poly Add(Poly a, Poly b)
        {
            var output = a.Clone();
            foreach (var (m, c) in b.Coeffs)
            {
                output.Add(m, c);
            }
            return output;
        }

        public void SetCoeff(Monomial m, long coeff)
        {
            coeff = ReduceCoeff(coeff);
            Coeffs[m] = coeff;
        }

        public void Add(Monomial m, long coeff)
        {
            coeff = ReduceCoeff(coeff);
            //if (coeff >= 234423243234 || coeff <= -234423243234)
            //    Debugger.Break();

            if (coeff == 0) return;
            if (Coeffs.TryGetValue(m, out var existing))
            {
                existing += coeff;
                if (existing == 0)
                    Coeffs.Remove(m);
                else
                    Coeffs[m] = existing;
            }
            else
            {
                Coeffs[m] = coeff;
            }

            Simplify();
            //ReduceMod();
          
        }

        public void Sub(Monomial m, long coeff)
        {
            Add(m, -coeff);
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

        public Poly Lhs()
        {
            var p = Clone();
            p.Coeffs.Clear();

            var coeff = Coeffs[Lm];
            p.Coeffs[Lm] = coeff;
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
                foreach (var (monomB, coeffB) in b.Coeffs)
                {
                    var newCoeff = coeffA * coeffB;
                    Monomial newMonom = monomA * monomB;
                    outPoly.Add(newMonom, newCoeff);
                }
            }

            return outPoly;
        }

        public static Poly Div(Poly a, ulong value)
        {
            var outPoly = new Poly();
            foreach (var (monom, coeff) in a.Coeffs)
            {
                if ((ulong)coeff % value != 0)
                    throw new InvalidOperationException("Cannot div");

                var d = (ulong)coeff / value;
                outPoly.Add(monom, (long)d);
            }

            return outPoly;
        }

        public static Poly Lshr(Poly a, ushort value)
        {
            var outPoly = new Poly();
            foreach (var (monom, coeff) in a.Coeffs)
            {
                if ((ulong)coeff % value != 0)
                    throw new InvalidOperationException("Cannot div");

                var d = (ulong)coeff >> value;
                outPoly.Add(monom, (long)d);
            }

            return outPoly;
        }


        public static bool IsConstant(Monomial m)
        {
            return m.SortedVars.Length == 0;
        }

        public bool IsEq(Poly other)
        {
            if (Coeffs.Count != other.Coeffs.Count) return false;
            using var e1 = Coeffs.GetEnumerator();
            using var e2 = other.Coeffs.GetEnumerator();
            while (e1.MoveNext())
            {
                e2.MoveNext();
                if (!e1.Current.Key.Equals(e2.Current.Key) || e1.Current.Value != e2.Current.Value)
                    return false;
            }
            return true;
        }


        public Poly Clone()
        {
            var copy = new SortedDictionary<Monomial, long>(Coeffs);
            return new Poly(copy);
        }

        public static Poly operator +(Poly a, Poly b)
            => Poly.Add(a, b);

        public static Poly operator -(Poly a, Poly b)
        {
            var output = a.Clone();
            foreach (var (m, c) in b.Coeffs)
                output.Add(m, -c);
            return output;
        }

        public static Poly operator +(Poly a, SymVar b)
            => Poly.Add(a, new Monomial(b));

        public static Poly operator -(Poly a, SymVar b)
          => Poly.Add(a, new Monomial(b));

        public static Poly operator *(long coeff, Poly a)
        {
            coeff = a.ReduceCoeff(coeff);

            if (coeff == 0) return new Poly();
            if (coeff == 1) return a.Clone();
            var output = new Poly();
            foreach (var (m, c) in a.Coeffs)
            {
                var nc = c * coeff;
                nc = a.ReduceCoeff(nc);
                if (nc != 0)
                    output.Coeffs[m] = nc;
            }
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

        public readonly SymVar[] SortedVars;

        public int Degree => SortedVars.Length;

        private readonly int hash = 17;

        public static Monomial Quadratic(SymVar var)
            => new Monomial(new SymVar[] { var, var }, distinct: false);

        public Monomial(SymVar var)
        {
            SortedVars = new[] { var };
            hash = 17 * 23 + var.GetHashCode();
        }

        public Monomial()
        {
            SortedVars = Array.Empty<SymVar>();
        }

        public Monomial(IEnumerable<SymVar> vars, bool distinct = true)
        {
            if (distinct)
                vars = vars.Distinct();

            SortedVars = vars.OrderByDescending(x => x).ToArray();

            foreach (var v in SortedVars)
                hash = hash * 23 + v.GetHashCode();
        }

        private Monomial(SymVar[] sortedVars, bool isSortedAndDistinct)
        {
            SortedVars = sortedVars;
            foreach (var v in SortedVars)
                hash = hash * 23 + v.GetHashCode();
        }

        public Monomial(params SymVar[] vars) : this(vars.AsEnumerable())
        {

        }

        private static readonly Monomial _constant = new Monomial(Array.Empty<SymVar>(), true);

        public static Monomial Constant() => _constant;

        public static Poly operator *(long coeff, Monomial a)
        {
            return new Poly(new SortedDictionary<Monomial, long>() { { a, coeff } });
        }

        public static Monomial operator *(Monomial a, Monomial b)
        {
            // Fast path: multiplying by constant monomial (degree 0) is identity.
            // This is the most common case in LexReduce when the quotient monomial is 1.
            if (a.SortedVars.Length == 0) return b;
            if (b.SortedVars.Length == 0) return a;

            var res = new SymVar[a.SortedVars.Length + b.SortedVars.Length];
            int i = 0, j = 0, k = 0;
            while (i < a.SortedVars.Length && j < b.SortedVars.Length)
            {
                int cmp = a.SortedVars[i].CompareTo(b.SortedVars[j]);
                if (cmp > 0)
                {
                    if (k == 0 || !res[k - 1].Equals(a.SortedVars[i]))
                        res[k++] = a.SortedVars[i];
                    i++;
                }
                else if (cmp < 0)
                {
                    if (k == 0 || !res[k - 1].Equals(b.SortedVars[j]))
                        res[k++] = b.SortedVars[j];
                    j++;
                }
                else
                {
                    if (k == 0 || !res[k - 1].Equals(a.SortedVars[i]))
                        res[k++] = a.SortedVars[i];
                    i++;
                    j++;
                }
            }
            while (i < a.SortedVars.Length)
            {
                if (k == 0 || !res[k - 1].Equals(a.SortedVars[i]))
                    res[k++] = a.SortedVars[i];
                i++;
            }
            while (j < b.SortedVars.Length)
            {
                if (k == 0 || !res[k - 1].Equals(b.SortedVars[j]))
                    res[k++] = b.SortedVars[j];
                j++;
            }

            if (k == res.Length)
                return new Monomial(res, true);

            var finalRes = new SymVar[k];
            Array.Copy(res, finalRes, k);
            return new Monomial(finalRes, true);
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
            if (other is null) return false;
            if (hash != other.hash) return false;
            if (SortedVars.Length != other.SortedVars.Length) return false;
            for (int i = 0; i < SortedVars.Length; i++)
            {
                if (!SortedVars[i].Equals(other.SortedVars[i]))
                    return false;
            }
            return true;
        }

        public Monomial Divide(Monomial other)
        {
            if (other.SortedVars.Length == 0) return this;

            var res = new SymVar[SortedVars.Length];
            int i = 0, j = 0, k = 0;
            while (i < SortedVars.Length && j < other.SortedVars.Length)
            {
                int cmp = SortedVars[i].CompareTo(other.SortedVars[j]);
                if (cmp > 0)
                {
                    res[k++] = SortedVars[i++];
                }
                else if (cmp < 0)
                {
                    j++;
                }
                else
                {
                    i++;
                    j++;
                }
            }
            while (i < SortedVars.Length)
            {
                res[k++] = SortedVars[i++];
            }

            if (k == 0) return _constant;

            if (k == res.Length)
                return new Monomial(res, true);

            var finalRes = new SymVar[k];
            Array.Copy(res, finalRes, k);
            return new Monomial(finalRes, true);
        }

        public bool Divides(Monomial other)
        {
            if (SortedVars.Length == 0) return true;
            if (SortedVars.Length > other.SortedVars.Length)
                return false;

            int i = 0, j = 0;
            while (i < SortedVars.Length && j < other.SortedVars.Length)
            {
                int cmp = SortedVars[i].CompareTo(other.SortedVars[j]);
                if (cmp > 0)
                {
                    return false;
                }
                else if (cmp < 0)
                {
                    j++;
                }
                else
                {
                    i++;
                    j++;
                }
            }
            return i == SortedVars.Length;
        }

        public int CompareTo(Monomial? other)
        {

            var thisVars = SortedVars;
            var otherVars = other.SortedVars;
            int minLen = Math.Min(thisVars.Length, otherVars.Length);
            for (int i = 0; i < minLen; i++)
            {
                int cmp = thisVars[i].CompareTo(otherVars[i]);
                if (cmp != 0)
                    return -cmp;
            }
            return otherVars.Length - thisVars.Length;
        }
    }

    public enum SymKind : byte
    {
        Input = 0,
        Dual = 1,
        InternalGate = 1,
        Output = 1,
    }

    public struct SymVar : IEquatable<SymVar>, IComparable<SymVar>
    {
        public SymKind Kind { get; set; }

        public int BitIndex { get; private set; }

        public uint TotalOrder { get; set; }

        public bool IsDual { get; set; }

        public string Name { get; set; }

        public static SymVar Symbol(AstCtx ctx, AstIdx idx, int bitIdx)
            => new SymVar() { Kind = SymKind.Input, Name = $"{ctx.GetSymbolName(idx)}{bitIdx}", BitIndex = bitIdx };

        public static SymVar Symbol(AstCtx ctx, string name, int bitIdx)
           => new SymVar() { Kind = SymKind.Input, Name = name, BitIndex = bitIdx };

        public static SymVar Temp(SymKind kind, int bitIdx, uint sliceIndex, string name, bool isDual = false)
        {
            kind = isDual ? SymKind.Dual : kind;
            var v = new SymVar() { Kind = kind, BitIndex = bitIdx, TotalOrder = sliceIndex, IsDual = isDual, Name = name };
            return v;
        }

        public static Poly operator *(long coeff, SymVar a)
        {
            return new Poly(new SortedDictionary<Monomial, long>() { { new Monomial(a), coeff } });
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
            int cmp = ((byte)Kind) - ((byte)other.Kind);
            if (cmp != 0)
                return cmp;
            cmp = BitIndex.CompareTo(other.BitIndex);
            if (cmp != 0)
                return cmp;
            cmp = TotalOrder.CompareTo(other.TotalOrder);
            if (cmp != 0)
                return cmp;

            cmp = string.CompareOrdinal(Name.Replace("dual", ""), other.Name.Replace("dual", ""));
            if (cmp != 0)
                return cmp;

            //return other.IsDual.CompareTo(IsDual);
            return IsDual.CompareTo(other.IsDual);
        }

        public override int GetHashCode()
        {
            return HashCode.Combine(Kind, Name, BitIndex);
        }
    }

}
