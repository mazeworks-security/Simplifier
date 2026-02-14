using Mba.Ast;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Polynomial;
using Mba.Simplifier.Utility;
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

        public Poly(params Monomial[] coeffs) : this(coeffs.AsEnumerable())
        {
        }

        public static Poly Add(Poly a, Poly b)
        {
            var output = new Poly();
            foreach(var p in new Poly[] { a, b})
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
            return m.SymVars.Count == 0;
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
            foreach(var (m, c) in a.Coeffs.ToDictionary())
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
        public readonly HashSet<SymVar> SymVars = new();

        public readonly List<SymVar> SortedVars;

        public Monomial(IEnumerable<SymVar> vars)
        {
            SymVars = vars.ToHashSet();
            SortedVars = SymVars.ToList();
            SortedVars.Sort();
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
            return new Monomial(a.SymVars.AsEnumerable().Concat(b.SymVars));
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

        public int CompareTo(Monomial? other)
        {
            var below = 1;
            var above = -1;

            if (this == other)
                return 0;

            for(int i = 0; i < Math.Min(SortedVars.Count, other.SortedVars.Count); i++)
            {
                var a = SortedVars[i];
                var b = other.SortedVars[i];
                var cmp = a.CompareTo(b);
                if (cmp != 0)
                    return cmp;
            }

            return SortedVars.Count.CompareTo(other.SortedVars.Count);

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
        // Indicates whether the symvar corresponds to an input bit or an intermediate variable
        /*
        public readonly bool IsInput;

        public readonly AstIdx? inputId;

        // If this corresponds to an input variable, what bit is it?
        public readonly int sliceIndex;
        */

        public SymKind Kind { get; set; }

        //public AstIdx? InputId { get; private set; }

        public string Name { get; set; }

        public int SliceIndex { get; private set; }

        public static SymVar Symbol(AstCtx ctx, AstIdx idx, int bitIdx)
            => new SymVar() { Kind = SymKind.Input, Name = $"{ctx.GetSymbolName(idx)}{bitIdx}", SliceIndex = bitIdx };

        public static SymVar Temp(SymKind kind, string name)
            => new SymVar() { Kind = kind, Name = name };

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
            return Kind == other.Kind && Name == other.Name && other.SliceIndex == other.SliceIndex;
        }

        public int CompareTo(SymVar other)
        {
            var below = 1;
            var above = -1;

            var cmp = Kind.CompareTo(other.Kind);
            if (cmp != 0)
                return cmp;
            cmp = SliceIndex.CompareTo(other.SliceIndex);
            if (cmp != 0)
                return cmp;
            cmp = Name.CompareTo(other.Name);
            if (cmp != 0)
                return cmp;

            return 0;
        }

        public override int GetHashCode()
        {
            return Kind.GetHashCode() + Name.GetHashCode() + SliceIndex.GetHashCode();
        }
    }

    public record ArithInfo(Poly cin, Poly cout);

    // https://danielakaufmann.at/wp-content/uploads/2020/11/Kaufmann-PhD-Thesis-2020.pdf
    // "Formal Verification of Multiplier Circuits using Computer Algebra"
    public class GroebnerVerifier
    {
        AstCtx ctx = new();

        AstIdx before;

        List<AstIdx> beforeNodes = new();

        AstIdx after;

        List<AstIdx> afterNodes = new();

        uint w = 2;

        public Dictionary<AstIdx, (uint, List<ArithInfo>)> carryIdentifiers = new();

        public GroebnerVerifier()
        {
            before = RustAstParser.Parse(ctx, "x+y", w);
            after = RustAstParser.Parse(ctx, "((x&y) + (x&y)) + (x^y)", w);
        }

        public void Run()
        {
            var ideal = new List<(int, uint, Poly)>();

            uint totalOrder = 0;
            foreach(var curr in new AstIdx[] { before, after})
            {
                Console.WriteLine("\n\n");
                for (int i = 0; i < w; i++)
                    GetSpecification(curr, i, ideal, ref totalOrder, true);

                //foreach (var member in ideal)
                //    Console.WriteLine(member);

                //ideal.Clear();
            }

            ideal = ideal.OrderBy(x => x.Item1).ThenBy(x => x.Item2).ToList();
            foreach(var member in ideal)
                Console.WriteLine(member.Item3);

            var target = ideal[3].Item3;
            var bar = target.Coeffs.Keys.ToList();

            //var eq = bar[2].Equals(bar[3]);


            Debugger.Break();
        }

        // Each node gets an x, y, carry in, carry out bits
        private Poly GetSpecification(AstIdx idx, int bitIdx, List<(int bitIndex, uint opIndex, Poly poly)> ideal, ref uint totalOrder, bool isOutput = false)
        {
            var opc = ctx.GetOpcode(idx);
            if (opc == AstOp.Symbol)
            {
                totalOrder++;
                return new Poly(new Monomial(SymVar.Symbol(ctx, idx, bitIdx)));
            }

            if (opc == AstOp.Constant)
            {
                totalOrder++;
                return Poly.Constant((long)ctx.GetConstantValue(idx));
            }

            if (!carryIdentifiers.ContainsKey(idx))
                carryIdentifiers.Add(idx, ((uint)carryIdentifiers.Count, new()));

            var (carryId, arithInfo) = carryIdentifiers[idx];
            if (opc == AstOp.Add)
            {
               
                Debug.Assert(arithInfo.Count == bitIdx);
                var a = GetSpecification(ctx.GetOp0(idx), bitIdx, ideal, ref totalOrder);
                var b = GetSpecification(ctx.GetOp1(idx), bitIdx, ideal, ref totalOrder);
                //var sum = SymVar.Temp($"a[{carryId}][{bitIdx}].sum");
                var sum = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate,  $"op{carryId}_{bitIdx}sum");
                //Poly cin = SymVar.Temp($"arith[{carryId}][{bitIdx}].cin");
                //if (bitIdx == 0)
                //    cin = Poly.Constant(0);
                Poly cin = Poly.Constant(0);
                if (bitIdx > 0)
                    cin = arithInfo[bitIdx - 1].cout;

                //var cout = SymVar.Temp($"a[{carryId}][{bitIdx}].cout");
                var cout = SymVar.Temp(SymKind.InternalGate, $"op{carryId}_{bitIdx}cout");

                var bar = sum - a;

                var p0 = 2L * cout + sum;

                var member = (2L * cout) + sum - a - b - cin;
                ideal.Add((bitIdx, totalOrder, member));

                arithInfo.Add(new(cin, cout));

                totalOrder++;
                return sum;
            }

            if (opc == AstOp.And)
            {
                var a = GetSpecification(ctx.GetOp0(idx), bitIdx, ideal, ref totalOrder);
                var b = GetSpecification(ctx.GetOp1(idx), bitIdx, ideal, ref totalOrder);

                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, $"r{carryId}_{bitIdx}");
                ideal.Add((bitIdx, totalOrder, y - (a * b)));

                totalOrder++;
                return y;
            }

            if (opc == AstOp.Xor)
            {
                var a = GetSpecification(ctx.GetOp0(idx), bitIdx, ideal, ref totalOrder);
                var b = GetSpecification(ctx.GetOp1(idx), bitIdx, ideal, ref totalOrder);

                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, $"r{carryId}_{bitIdx}");
                ideal.Add((bitIdx, totalOrder, (y - (a+b - (2 * (a*b))))));

                totalOrder++;
                return y;

            }

            throw new InvalidOperationException();

        }

        // TODO: Canonicalize 123*a into 7 shifted add circuits
        private void Linearize(AstIdx node, List<AstIdx> dfs, HashSet<AstIdx> seen)
        {
            if (seen.Contains(node))
                return;
        }
    }
}
