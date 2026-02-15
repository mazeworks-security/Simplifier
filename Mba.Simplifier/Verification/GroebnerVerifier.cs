using Mba.Ast;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Polynomial;
using Mba.Simplifier.Utility;
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
        public readonly HashSet<SymVar> SymVars = new();

        public readonly List<SymVar> SortedVars;

        public Monomial(IEnumerable<SymVar> vars)
        {
            SymVars = vars.ToHashSet();
            SortedVars = SymVars.ToList();
            SortedVars = SymVars.OrderByDescending(x => x).ToList();


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
        // Indicates whether the symvar corresponds to an input bit or an intermediate variable
        /*
        public readonly bool IsInput;

        public readonly AstIdx? inputId;

        // If this corresponds to an input variable, what bit is it?
        public readonly int sliceIndex;
        */

        public SymKind Kind { get; set; }

        //public AstIdx? InputId { get; private set; }


        public int BitIndex { get; private set; }

        public uint TotalOrder { get; set; }

        public string Name { get; set; }

        public static SymVar Symbol(AstCtx ctx, AstIdx idx, int bitIdx)
            => new SymVar() { Kind = SymKind.Input, Name = $"{ctx.GetSymbolName(idx)}{bitIdx}", BitIndex = bitIdx };

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

    public record ArithInfo(Poly cin, Poly cout, Poly result);

    // https://danielakaufmann.at/wp-content/uploads/2020/11/Kaufmann-PhD-Thesis-2020.pdf
    // "Formal Verification of Multiplier Circuits using Computer Algebra"
    public class GroebnerVerifier
    {
        AstCtx ctx = new();

        AstIdx before;

        List<AstIdx> beforeNodes = new();

        AstIdx after;

        List<AstIdx> afterNodes = new();

        uint w = 4;

        public Dictionary<AstIdx, (uint, List<ArithInfo>)> carryIdentifiers = new();

        public GroebnerVerifier()
        {
            before = RustAstParser.Parse(ctx, "x+y", w);
            //after = RustAstParser.Parse(ctx, "x+x+x+x+x+y", w);
            after = RustAstParser.Parse(ctx, "((x&y) + (x&y)) + (x^y)", w);


            //before = RustAstParser.Parse(ctx, "x+x+x+x", w);

            //after = RustAstParser.Parse(ctx, "x+x+x+x+x+y", w);
            //after = RustAstParser.Parse(ctx, "x+x+x+y", w);

            //before = RustAstParser.Parse(ctx, "x+y", w);
            //after = RustAstParser.Parse(ctx, "((x&y) + (x&y)) + (x^y)", w);
            //before = RustAstParser.Parse(ctx, "x&y", w);
            //after = RustAstParser.Parse(ctx, "x&y", w);
        }

        public static bool Validate(List<Poly> ideal, int w)
        {
            // Collect all input variables across the entire ideal.
            var allVars = new HashSet<SymVar>();
            foreach (var p in ideal)
                foreach (var m in p.Coeffs.Keys)
                    foreach (var v in m.SymVars)
                        allVars.Add(v);

            var inputVars = allVars.Where(v => v.Kind == SymKind.Input).OrderBy(v => v).ToList();
            int numInputs = inputVars.Count;

            // Enumerate all 2^numInputs boolean assignments.
            for (ulong combo = 0; combo < (1UL << numInputs); combo++)
            {
                var assignment = new Dictionary<SymVar, long>();
                for (int i = 0; i < numInputs; i++)
                    assignment[inputVars[i]] = (long)((combo >> i) & 1);

                // Process each ideal member in order.
                // Each non-last member defines a gate variable in terms of previously known variables.
                // The last member is the specification / difference polynomial to check.
                for (int i = 0; i < ideal.Count; i++)
                {
                    var poly = ideal[i];

                    if (i < ideal.Count - 1)
                    {
                        // Find the unassigned gate variable defined by this polynomial.
                        // The ideal member has the form: coeff*gate + f(known_vars) = 0
                        // So gate = -f(known_vars) / coeff
                        SymVar? unassigned = null;
                        foreach (var m in poly.Coeffs.Keys)
                        {
                            if (m.SymVars.Count == 1)
                            {
                                var v = m.SymVars.First();
                                if (!assignment.ContainsKey(v))
                                {
                                    unassigned = v;
                                    break;
                                }
                            }
                        }

                        if (unassigned == null)
                        {
                            // All variables are known; just verify this member is zero.
                            long check = EvaluatePoly(poly, assignment) & (long)ModuloReducer.GetMask((uint)w);
                            if (check != 0)
                                return false;
                            continue;
                        }

                        var gate = unassigned.Value;
                        var gateMono = new Monomial(gate);

                        // Evaluate all terms that don't contain the gate variable.
                        long restSum = 0;
                        long gateCoeff = 0;
                        foreach (var (monomial, coeff) in poly.Coeffs)
                        {
                            if (monomial.SymVars.Contains(gate))
                            {
                                // This term contains the gate variable.
                                // It should be of the form coeff * gate (linear in gate).
                                Debug.Assert(monomial.SymVars.Count == 1, $"Gate variable {gate} appears in higher-degree monomial {monomial}");
                                gateCoeff += coeff;
                            }
                            else
                            {
                                restSum += EvaluateMonomial(monomial, coeff, assignment);
                            }
                        }

                        // coeff * gate + rest = 0  =>  gate = -rest / coeff
                        Debug.Assert(gateCoeff != 0);
                        Debug.Assert(restSum % gateCoeff == 0 || (gateCoeff == 1 || gateCoeff == -1),
                            $"Non-unit coefficient {gateCoeff} for gate {gate}");
                        assignment[gate] = -restSum / gateCoeff;
                    }
                    else
                    {
                        // Last member: evaluate and check it equals zero.
                        long result = EvaluatePoly(poly, assignment) & (long)ModuloReducer.GetMask((uint)w);
                        if (result != 0)
                            return false;
                    }
                }
            }

            return true;
        }

        private static long EvaluatePoly(Poly poly, Dictionary<SymVar, long> assignment)
        {
            long result = 0;
            foreach (var (monomial, coeff) in poly.Coeffs)
                result += EvaluateMonomial(monomial, coeff, assignment);
            return result;
        }

        private static long EvaluateMonomial(Monomial monomial, long coeff, Dictionary<SymVar, long> assignment)
        {
            long termVal = coeff;
            foreach (var v in monomial.SymVars)
            {
                if (!assignment.TryGetValue(v, out var val))
                    throw new InvalidOperationException($"Variable {v} is not assigned.");
                termVal *= val;
            }

            return termVal;
        }

        private void BackwardsEliminate(List<Poly> ideal, int targetIdx, bool linearOnly = false, bool singleUseOnly = false)
        {

            var mmask = ModuloReducer.GetMask(w);
            var solver = new LinearCongruenceSolver(mmask);


            Console.WriteLine($"Initial: {ideal[targetIdx]}");
            //while (ideal.Last().Coeffs.Count != 0)
            bool changed = true;
            while (changed)
            {
                changed = false;
                for (int i = 0; i < targetIdx; i++)
                //for(int i = ideal.Count - 2; i >= 0; i--)
                {
                    var next = ideal[targetIdx].Clone();
                    var curr = ideal[i].Clone();
                    //if (!ideal.Any(x => x.Lm.SymVars.Count == 1 && x)))
                    //    continue;
                    var v = next.Lm.SortedVars.First();
                    var currLm = new Monomial(v);

                    // If linearOnly, only do substitution of terms with 1 or more variables
                    if (linearOnly && curr.Coeffs.Count > 2)
                        continue;

                    // If a term only has one use, immediately substitute it.
                    // 1*(r4_1) + 2*(y1*x1) + 15*(y1) + 15*(x1)
                    // 15 * (r4_1 * y0 * x0) + 1 * (op1_1cout)

                    if (singleUseOnly && next.ToString() == "15*(r4_1*y0*x0) + 1*(op1_1cout)" && i == 17)
                        Debugger.Break();

                    var skip = ideal.Skip(i+1).ToList();
                    if (singleUseOnly && skip.Count(x => x.Lm.SortedVars[0].Equals(v)) != 1)
                        continue;


                    if (!curr.Coeffs.ContainsKey(currLm))
                        continue;

                    var nextLm = next.Lm;

                    var lc = solver.LinearCongruence((UInt128)curr.Coeffs[currLm] & mmask, (UInt128)(next.Coeffs[nextLm]) & mmask, mmask + 1);
                    if (lc == null)
                        continue;

                    var sol = solver.GetSolution(0, lc);

                    // Move the value over to the RHS
                    var currRhs = curr.Clone();
                    currRhs.Remove(currLm);
                    currRhs = -1L * currRhs;

                    var temp = new Poly();

                    if (nextLm.SymVars.Count == 1)
                    {
                        temp.Add(Monomial.Constant(), 1);
                    }
                    else
                    {
                        var map = nextLm.SymVars.ToHashSet();
                        map.Remove(v);

                        // Now temp has the monomial without the variable..
                        temp.Add(new Monomial(map), 1);
                    }

                    next.Remove(nextLm);


                    next = next + ((long)sol * (currRhs * temp));

                    next.ReduceMod(w);
                    next.Simplify();
                    changed = true;
                    ideal[targetIdx] = next;


                    Console.WriteLine($"Intermediate product: {next}\n");
                    //var rr = Validate(ideal, (int)w);


                    //break;


                    //Debugger.Break();
                }
                //var curr = ideal.First(x => x.Lm.SymVars.Contains(last.Lm.SymVars.First()));



            }

            //Debugger.Break();
        }

        private void LinElim(List<Poly> ideal)
        {
            var mmask = ModuloReducer.GetMask(w);
            var solver = new LinearCongruenceSolver(mmask);

            bool changed = true;
            while (changed)
            {
                changed = false;
                // Identify linear equations of the form c1*v1 + c2*v2 = 0 (or constant)
                // And substitute them forward into other ideals.
                for (int i = 0; i < ideal.Count; i++)
                {
                    var curr = ideal[i];
                    if (curr.Coeffs.Count != 2 && curr.Coeffs.Count != 1)
                        continue;

                    // Check if we have (v1) and (v2) or (v1) and (constant)
                    var mons = curr.Coeffs.Keys.ToList();
                    var m1 = mons[0];
           
                    // One of them must be a single variable leading term we want to eliminate.
                    // Usually the leading monomial is the one we want to substitute out.
                    var lm = curr.Lm;
                    if (lm.SymVars.Count != 1)
                        continue;

                    // The other term must be "simpler", which implies it should be smaller or equal in order,
                    // but if it's in the ideal, we are just looking for structure `c * v + rest = 0`.
                    // The example `1*op + 3*x0` implies `op = -3*x0`.

                    var variable = lm.SymVars.Single();
                    var coeff = curr.Coeffs[lm]; // c1

                    // Find the "rhs" poly (which is just the other term negated)
                    var rhs = curr.Clone();
                    rhs.Remove(lm);
                    rhs = -1L * rhs; // -c2*v2

                    // Now substitute 'variable' in all subsequent polynomials
                    for (int j = i + 1; j < ideal.Count; j++)
                    {
                        if (i == j) continue;

                        var next = ideal[j].Clone();
                        bool onlyOne = curr.Coeffs.Count == 1;
                        if (onlyOne && next.Coeffs.Keys.Any(x => lm.SymVars.IsSubsetOf(x.SymVars)))
                        {
                            var banned = next.Coeffs.Keys.Where(x => lm.SymVars.IsSubsetOf(x.SymVars)).ToList();
                            foreach (var t in banned)
                                next.Remove(t);

                            ideal[j] = next;
                            changed = true;
                            continue;
                        }

                        // We are looking for occurrences of 'lm' (the variable v1) in 'next'.
                        // Since 'lm' is a single variable, we look for monomials containing it?
                        // Or just linear occurrences? Groebner basis usually eliminates leading monomials.
                        // But if we have `x = y`, we want to replace `x` everywhere.

                        // Let's filter for monomials in 'next' that contain 'variable'.
                        var targets = next.Coeffs.Keys.Where(k => k.SymVars.Contains(variable)).ToList();
                        if (targets.Count == 0)
                            continue;

                        // Substitute v = (rhs / coeff)
                        // For each term T = c_T * v * M (where M is monomial without v)
                        // We have c_T * (rhs / coeff) * M
                        // We need solution s such that s * coeff = c_T (mod m)

                        bool instantiated = false;
                        foreach (var targetM in targets)
                        {
                            var targetCoeff = next.Coeffs[targetM];
                            var lc = solver.LinearCongruence((UInt128)coeff & mmask, (UInt128)targetCoeff & mmask, mmask + 1);

                            if (lc == null || lc.n == 0)
                                continue; // Cannot divide

                            var s = solver.GetSolution(0, lc);

                            // The term T is removed
                            next.Remove(targetM);

                            // Construct M (monomial without variable)
                            var map = targetM.SymVars.ToHashSet();
                            map.Remove(variable);
                            var remainderM = new Monomial(map);

                            // Add s * rhs * M
                            var increment = (long)s * rhs;

                            // Multiply by remainderM
                            var temp = new Poly();
                            temp.Add(remainderM, 1);

                            increment = increment * temp;

                            next = next + increment;

                            // Keep clean
                            next.ReduceMod(w);
                            next.Simplify();
                            instantiated = true;
                        }

                        if (instantiated)
                        {
                            ideal[j] = next;
                            changed = true;
                        }
                    }
                }
            }
        }

        public void Run()
        {

            var idealArr = new List<(int, uint, Poly)>();

            uint totalOrder = 0;
            var firstSeen = new Dictionary<SymVar, uint>();

            var results = new List<Poly>();
            foreach (var curr in new AstIdx[] { before, after })
            {
                Console.WriteLine("\n\n");
                for (int i = 0; i < w; i++)
                    results.Add(GetSpecification(curr, i, idealArr, firstSeen, ref totalOrder, true));

                //foreach (var member in ideal)
                //    Console.WriteLine(member);

                //ideal.Clear();
            }


            //var ideal = idealArr.OrderBy(x => x.Item1).ThenBy(x => x.Item3.Lm).ThenBy(x => x.Item2).ToList().Select(x => x.Item3).ToList();
            var ideal = idealArr.ToList().Select(x => x.Item3).ToList();
            foreach (var member in ideal)
            {
                member.Simplify();
                Console.WriteLine(member);
            }



            //var target = ideal[3].Item3;
            //var bar = target.Coeffs.Keys.ToList();

            //var eq = bar[2].Equals(bar[3]);

            // Compute difference of the output variables, not the ideal members
            //var last = results[0] - results[1];

            // 63 - 127
            //var last = results[results.Count - 2] - results[results.Count - 1];

            //var last = results[15] - results[7];

            //var last = results[15] - results[31];

            //var last = results[3] - results[1];

            // var last = results[2] - results[5];

            var last = results[3] - results[7];

            //var last = results[11] - results[5];

            //var last = results[3] - results[7];

            ideal.Add(last);


            Console.WriteLine($"\n\nDifference: {last}\n");


            Console.WriteLine("\n\n\nInitial ideal with difference: ");
            foreach (var p in ideal)
            {
                foreach (var key in p.Coeffs.Keys.ToList())
                    p.Coeffs[key] &= (long)ModuloReducer.GetMask(w);

                p.Simplify();
                if (p.Coeffs.Count == 0)
                    continue;
                Console.WriteLine(p);
            }

            ideal = ideal.Where(x => x.Coeffs.Count > 0).ToList();


            // For each bit i, we need to compute a carry bit expression for each bit [i+1..N]
            // Reduce each carry bit.. check if equivalent..
            // Problem (a&b&0).. at each bit, how do we even identify the incoming carry?
            // How do you get the carry when its inside of a bitwise expression?

            //var r = Validate(ideal, ctx.GetWidth(before));
            //Debug.Assert(r == true);

            var mmask = ModuloReducer.GetMask(w);
            var solver = new LinearCongruenceSolver(mmask);


            bool changed = true;
            while (changed)
            {
                changed = false;

                for (int i = 0; i < ideal.Count; i++)
                {
                    ideal[i].Simplify();
                    if (ideal[i].Coeffs.Count == 0)
                        continue;




                    for (int j = i + 1; j < ideal.Count; j++)
                    {
                        var curr = ideal[i].Clone();
                        var lm = curr.Lm;

                        var next = ideal[j].Clone();
                        bool onlyOne = curr.Coeffs.Count == 1;
                        if (onlyOne && next.Coeffs.Keys.Any(x => lm.SymVars.IsSubsetOf(x.SymVars)))
                        {
                            var targets = next.Coeffs.Keys.Where(x => lm.SymVars.IsSubsetOf(x.SymVars)).ToList();
                            foreach (var t in targets)
                                next.Remove(t);

                            ideal[j] = next;
                            changed = true;
                            continue;
                        }


                        if (!next.Coeffs.ContainsKey(lm))
                            continue;
                        //if (next.Lm.CompareTo(lm) == -1)
                        //    continue;

                        Console.WriteLine("\n\n\n\n\n\n");



                        Console.WriteLine($"{curr}\n{next}");

                        var lc = solver.LinearCongruence((UInt128)curr.Coeffs[lm] & mmask, (UInt128)(next.Coeffs[lm]) & mmask, mmask + 1);
                        if (lc == null)
                            continue;
                        Console.WriteLine($"c1*{curr.Coeffs[lm]} == {next.Coeffs[lm]}");
                        if (lc.n == 0)
                            continue;

                        var sol = solver.GetSolution(0, lc);
                        Console.WriteLine($"Solution: {sol}");

                        // Delete the monomial
                        next.Remove(lm);

                        // Move the value over to the RHS
                        curr.Remove(lm);
                        curr = -1L * curr;

                        // Substitute the RHS back in 
                        next = next + ((long)(ulong)sol * curr);

                        next.Simplify();
                        next.ReduceMod(w);

                        Console.WriteLine($"=> \n{next}");


                        ideal[j] = next;

                        //next = Poly.Add(next, (long)(ulong)sol * curr);


                        /*
                         * 
                         *  var first = curr.Clone();
                        if (first.Coeffs[lm] != 1 && first.Coeffs[lm] != -1)
                        {
                            Console.WriteLine($"todo: fix with coeff {first.Coeffs[lm]}");
                            continue;
                        }


                        //Debug.Assert(first.Coeffs[lm] == 1);

                        var factor = first.Coeffs[lm] == 1 ? -1L : 1L;

                        Console.WriteLine($"c1*{-first.Coeffs[lm]} == {-next.Coeffs[lm]}. Solution={factor * next.Coeffs[lm]}");


                        first.Sub(lm, first.Coeffs[lm]);


                        //first = -1L * first;
                        first = factor * first;
                        //first = -1L * first;

                        first.Simplify();

                        next.Replace(lm, first);
                        next.Simplify();
                        ideal[j] = next;
                        //last.Simplify();
                        changed = true;
                        */
                    }
                }
            }

            changed = false;
            while (changed)
            {
                changed = false;
                for (int i = 0; i < ideal.Count; i++)
                {
                    if (ideal[i].Coeffs.Count == 0)
                        continue;

                    var curr = ideal[i].Clone();
                    var lm = curr.Lm;

                    if (lm.SymVars.Count != 1)
                        continue;

                    var v = lm.SymVars.Single();

                    for (int j = i + 1; j < ideal.Count; j++)
                    {
                        var next = ideal[j].Clone();
                        var targets = next.Coeffs.Keys.Where(x => x.SymVars.Contains(lm.SymVars.Single())).ToList();
                        if (targets.Count == 0)
                            continue;


                        // Compute the rhs
                        var first = curr.Clone();
                        //Debug.Assert(first.Coeffs[lm] == 1);


                        if (first.Coeffs[lm] != 1 && first.Coeffs[lm] != -1)
                        {
                            Console.WriteLine($"todo: fix");
                            continue;
                        }
                        first.Sub(lm, first.Coeffs[lm]);
                        // dubious or not verified
                        var factor = first.Coeffs[lm] == 1 ? -1L : 1L;

                        //first = -1L * first;
                        first = factor * first;
                        first.Simplify();

                        var temp = new Poly();
                        foreach (var m in targets)
                        {
                            if (m.SymVars.Count == 1)
                            {
                                temp.Add(Monomial.Constant(), next.Coeffs[m]);
                                continue;
                            }

                            var map = m.SymVars.ToHashSet();
                            map.Remove(v);

                            temp.Add(new Monomial(map), next.Coeffs[m]);
                        }

                        temp = temp * first;
                        foreach (var t in targets)
                            next.Remove(t);

                        next += temp;
                        next.Simplify();
                        ideal[j] = next;
                        changed = true;


                    }
                }
            }

            /*
            var barr = ideal.Last();
            var list = barr.Coeffs.Keys.ToList();

            var op0 = list[1];
            var op2 = list[13];

            var s1 = op0.SymVars.OrderBy(x => x).ToList();
            var s2 = op2.SymVars.OrderBy(x => x).ToList();


            var cmp = s1[0].CompareTo(s2[0]);

            for(int i = 0; i < list.Count - 1; i++)
            {
                var a = list[i];
                var b = list[i + 1];
                Console.WriteLine($"{a} == {b}: {a == b}");
            }
            */

            Console.WriteLine("\n\n\nReduced ideal: ");
            foreach (var p in ideal)
            {
                foreach (var key in p.Coeffs.Keys.ToList())
                    p.Coeffs[key] &= (long)ModuloReducer.GetMask(w);

                p.Simplify();
                if (p.Coeffs.Count == 0)
                    continue;
                Console.WriteLine(p);
            }

            ideal = ideal.Where(x => x.Coeffs.Count > 0).ToList();


            for (int i = 0; i < ideal.Count - 1; i++)
            {
                //continue;

                var p = ideal[i];


                BackwardsEliminate(ideal, i, linearOnly: false, singleUseOnly: true);

                Console.WriteLine($"ROUND {i}");
                //if (p.Lm.SymVars.Count == 1 && (p.Lm.SortedVars.Single().Name.Contains("cout") || p.Lm.SortedVars.Single().Name.Contains("sum")))
                //    BackwardsEliminate(ideal, i);
            }

            LinElim(ideal);
            LinElim(ideal);
            LinElim(ideal);



            Console.WriteLine("\n\n\nBack reduced ideal: ");
            foreach (var p in ideal)
            {
                foreach (var key in p.Coeffs.Keys.ToList())
                    p.Coeffs[key] &= (long)ModuloReducer.GetMask(w);

                p.Simplify();
                if (p.Coeffs.Count == 0)
                    continue;
                Console.WriteLine(p);
            }



            for (int i = 0; i < ideal.Count - 1; i++)
            {
                //continue;

                var p = ideal[i];


                BackwardsEliminate(ideal, i, linearOnly: false, singleUseOnly: true);

                Console.WriteLine($"ROUND {i}");
                //if (p.Lm.SymVars.Count == 1 && (p.Lm.SortedVars.Single().Name.Contains("cout") || p.Lm.SortedVars.Single().Name.Contains("sum")))
                //    BackwardsEliminate(ideal, i);
            }




            Console.WriteLine("\n\n\nFinal reduced ideal: ");
            foreach (var p in ideal)
            {
                foreach (var key in p.Coeffs.Keys.ToList())
                    p.Coeffs[key] &= (long)ModuloReducer.GetMask(w);

                p.Simplify();
                if (p.Coeffs.Count == 0)
                    continue;
                Console.WriteLine(p);
            }




            var rr = Validate(ideal, (int)w);

            BackwardsEliminate(ideal, ideal.Count - 1);

            rr = Validate(ideal, (int)w);



            Debugger.Break();

            /*
            ideal.Reverse();

            while (true)
            {
                Monomial lm = last.Lm;

     

                var first = ideal.First(x => x.Item3.Lm == lm).Item3.Clone();
                Debug.Assert(first.Coeffs[lm] == 1);

                first.Sub(lm, first.Coeffs[lm]);
                first = -1L * first;

                first.Simplify();

                //var oldCoeff = last.Coeffs[lm];
                last.Replace(lm, first);
                last.Simplify();

                Debugger.Break();
            }
            */



            Debugger.Break();
        }

        // Each node gets an x, y, carry in, carry out bits
        private Poly GetSpecification(AstIdx idx, int bitIdx, List<(int bitIndex, uint opIndex, Poly poly)> ideal, Dictionary<SymVar, uint> firstSeen, ref uint totalOrder, bool isOutput = false)
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

            var update = (SymVar sym) =>
            {
                var existing = firstSeen.TryGetValue(sym, out var val);
                if (existing)
                {
                    sym.TotalOrder = val;
                    return sym;
                }

                firstSeen.Add(sym, (uint)firstSeen.Count);
                sym.TotalOrder = (uint)firstSeen.Count;
                return sym;
            };

            var (carryId, arithInfo) = carryIdentifiers[idx];
            if (opc == AstOp.Add)
            {
                if (arithInfo.Count > bitIdx)
                    return arithInfo[bitIdx].result;
                Debug.Assert(arithInfo.Count == bitIdx);
                var a = GetSpecification(ctx.GetOp0(idx), bitIdx, ideal, firstSeen, ref totalOrder);
                var b = GetSpecification(ctx.GetOp1(idx), bitIdx, ideal, firstSeen, ref totalOrder);
                //var sum = SymVar.Temp($"a[{carryId}][{bitIdx}].sum");
                var sum = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}sum");
                update(sum);




                //Poly cin = SymVar.Temp($"arith[{carryId}][{bitIdx}].cin");
                //if (bitIdx == 0)
                //    cin = Poly.Constant(0);
                Poly cin = Poly.Constant(0);
                if (bitIdx > 0)
                    cin = arithInfo[bitIdx - 1].cout;

                //var cout = SymVar.Temp($"a[{carryId}][{bitIdx}].cout");
                var cout = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}cout");
                update(cout);

                /*
                var sumLhs = sum;
                var sumRhs = a + b + cin + (-2 * (a * b + b * cin + a * cin)) + 4 * (a * b * cin);

                ideal.Add((bitIdx, totalOrder++, sumLhs - sumRhs));
                   */



                var carryLhs = cout;
                var carryRhs = a * b + b * cin + a * cin + (-1 * (2 * a * b * cin));
                ideal.Add((bitIdx, totalOrder++, carryLhs - carryRhs));


                var member = (2L * cout) + sum - a - b - cin;
                ideal.Add((bitIdx, totalOrder, member));

                arithInfo.Add(new(cin, cout, sum));

                totalOrder++;
                return sum;
            }

            if (opc == AstOp.And)
            {
                var a = GetSpecification(ctx.GetOp0(idx), bitIdx, ideal, firstSeen, ref totalOrder);
                var b = GetSpecification(ctx.GetOp1(idx), bitIdx, ideal, firstSeen, ref totalOrder);

                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"r{carryId}_{bitIdx}");
                update(y);
                ideal.Add((bitIdx, totalOrder, y - (a * b)));

                totalOrder++;
                return y;
            }

            if (opc == AstOp.Xor)
            {
                var a = GetSpecification(ctx.GetOp0(idx), bitIdx, ideal, firstSeen, ref totalOrder);
                var b = GetSpecification(ctx.GetOp1(idx), bitIdx, ideal, firstSeen, ref totalOrder);

                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"r{carryId}_{bitIdx}");
                update(y);
                ideal.Add((bitIdx, totalOrder, (y - (a + b - (2 * (a * b))))));

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
