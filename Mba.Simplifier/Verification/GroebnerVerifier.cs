using Antlr4.Runtime;
using Mba.Ast;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Minimization;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Polynomial;
using Mba.Simplifier.Utility;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Diagnostics.Metrics;
using System.Linq;
using System.Reflection;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;
using static System.Net.Mime.MediaTypeNames;

namespace Mba.Simplifier.Verification
{
    public record ArithInfo(Poly cin, Poly cout, Poly pcout0, Poly pcout1, Poly result);

    // https://danielakaufmann.at/wp-content/uploads/2020/11/Kaufmann-PhD-Thesis-2020.pdf
    // "Formal Verification of Multiplier Circuits using Computer Algebra"
    public class GroebnerVerifier
    {
        AstCtx ctx = new();

        AstIdx obfuscated;

        List<AstIdx> beforeNodes = new();

        AstIdx deob;

        List<AstIdx> afterNodes = new();

        uint w = 64;

        public Dictionary<AstIdx, (uint, List<ArithInfo>)> carryIdentifiers = new();

        public GroebnerVerifier()
        {
            AstIdx.ctx = ctx;
            // only works with x+y, mba currently... x+x+x+x+x+y mod 2 does notwork
            //before = RustAstParser.Parse(ctx, "x+y", w);

            //after = RustAstParser.Parse(ctx, "((x&y) + (x&y)) + (x^y)", w);


            //before = RustAstParser.Parse(ctx, "x+x+x+x", w);

            //after = RustAstParser.Parse(ctx, "x+x+x+x+x+y", w);
            //after = RustAstParser.Parse(ctx, "x+x+x+y", w);

            //before = RustAstParser.Parse(ctx, "((x&y) + (x&y)) + (x^y)", w);
            //before = RustAstParser.Parse(ctx, "(x+x+x+x+x+x+x+x+y)&(x+y)", w);
            //before = RustAstParser.Parse(ctx, "((x+y) & (y+x)) & ((x+x+x+x+x+x+x+x+x+y)&(x+y))", w);
            //obfuscated = RustAstParser.Parse(ctx, "((x+y) & (y+x)) & ((x+x+x+x+x+x+x+x+x+y)&(x+y))", w);
            //obfuscated = RustAstParser.Parse(ctx, "x+y", w);
            //before = RustAstParser.Parse(ctx, "x+y", w);
            //before = RustAstParser.Parse(ctx, "x+y", w);
            //after = RustAstParser.Parse(ctx, "x+y", w);
            //obfuscated = RustAstParser.Parse(ctx, "((x&y) + (x&y)) + (x^y)", w);
            //deob = RustAstParser.Parse(ctx, "y+x", w);

            obfuscated = RustAstParser.Parse(ctx, "(x&((~x + 1)&(x+x)))", w);
            deob = RustAstParser.Parse(ctx, "x&~x", w);



            obfuscated = RustAstParser.Parse(ctx, "(x&((~x + 1)&(x+x)))", w);
            deob = RustAstParser.Parse(ctx, "x&0", w);

            //obfuscated = RustAstParser.Parse(ctx, "~(~x + 1) + 1", w);
            //deob = RustAstParser.Parse(ctx, "x", w);

            //before = RustAstParser.Parse(ctx, "x&y", w);
            //after = RustAstParser.Parse(ctx, "x&y", w);


            //obfuscated = RustAstParser.Parse(ctx, "(x&((~x + 1)&(x+x)))", w);
            //deob = RustAstParser.Parse(ctx, "x&0", w);


            obfuscated = RustAstParser.Parse(ctx, "(((x&y) + (x&y)) + (x^y)) & (x+y)", w);
            deob = RustAstParser.Parse(ctx, "x+y", w);


            obfuscated = RustAstParser.Parse(ctx, "(x&((~x + 1)&(x+x)))", w);
            deob = RustAstParser.Parse(ctx, "x&~x", w);



            obfuscated = RustAstParser.Parse(ctx, "2*x + 2*y + 1*x + 1*y", w);
            deob = RustAstParser.Parse(ctx, "3*x + 3*y", w);

            obfuscated = RustAstParser.Parse(ctx, "25*x + 25*y + 27*x + 27*y", w);
            deob = RustAstParser.Parse(ctx, "52*x + 52*y", w);

            obfuscated = RustAstParser.Parse(ctx, "2*x + 2*y + 1*x + 1*y", w);
            deob = RustAstParser.Parse(ctx, "3*x + 3*y", w);

            obfuscated = RustAstParser.Parse(ctx, "3*x + 3*y + 1*x + 1*y", w);
            deob = RustAstParser.Parse(ctx, "4*x + 4*y", w);


            obfuscated = RustAstParser.Parse(ctx, "25*x + 25*y + 27*x + 27*y", w);
            deob = RustAstParser.Parse(ctx, "52*x + 52*y", w);


            obfuscated = RustAstParser.Parse(ctx, "3*x + 3*y + 1*x + 1*y", w);
            deob = RustAstParser.Parse(ctx, "4*x + 4*y", w);


            obfuscated = RustAstParser.Parse(ctx, "(((x&y) + (x&y)) + (x^y)) & (x+y)", w);
            deob = RustAstParser.Parse(ctx, "x+y", w);

            obfuscated = RustAstParser.Parse(ctx, "3*x + 3*y + 1*x + 1*y", w);
            deob = RustAstParser.Parse(ctx, "4*x + 4*y", w);

            obfuscated = RustAstParser.Parse(ctx, "25*x + 25*y + 27*x + 27*y", w);
            deob = RustAstParser.Parse(ctx, "52*x + 52*y", w);

            obfuscated = RustAstParser.Parse(ctx, "((x&y) + (x&y)) + (x^y)", w);
            deob = RustAstParser.Parse(ctx, "((x&y) + (x&y)) + (x^y)", w);


            obfuscated = RustAstParser.Parse(ctx, "(((x&y) + (x&y)) + (x^y)) & (x+y)", w);
            deob = RustAstParser.Parse(ctx, "x+y", w);

            obfuscated = RustAstParser.Parse(ctx, "3*x + 3*y + 1*x + 1*y", w);
            deob = RustAstParser.Parse(ctx, "4*x + 4*y", w);

            obfuscated = RustAstParser.Parse(ctx, "x+y+x", w);
            deob = RustAstParser.Parse(ctx, "x+x+y", w);

            obfuscated = RustAstParser.Parse(ctx, "(((x&y) + (x&y)) + (x^y)) & (x+y)", w);
            deob = RustAstParser.Parse(ctx, "x+y", w);

            obfuscated = RustAstParser.Parse(ctx, "x+y+x", w);
            deob = RustAstParser.Parse(ctx, "x+x+y", w);

            obfuscated = RustAstParser.Parse(ctx, "(((x&y) + (x&y)) + (x^y)) & (x+y)", w);
            deob = RustAstParser.Parse(ctx, "x+y", w);

            obfuscated = RustAstParser.Parse(ctx, "(((x&y) + (x&y)) + (x^y)) & (x+y)", w);
            deob = RustAstParser.Parse(ctx, "x+y", w);

            obfuscated = RustAstParser.Parse(ctx, "25*x + 25*y + 27*x + 27*y", w);
            deob = RustAstParser.Parse(ctx, "52*x + 52*y", w);

            obfuscated = RustAstParser.Parse(ctx, "(((x&y) + (x&y)) + (x^y)) & (x+y)", w);
            deob = RustAstParser.Parse(ctx, "x+y", w);

            obfuscated = RustAstParser.Parse(ctx, "3*x + 3*y + 4*x + 4*y", w);
            deob = RustAstParser.Parse(ctx, "7*x + 7*y", w);


            obfuscated = RustAstParser.Parse(ctx, "2*x + y + y", w);
            deob = RustAstParser.Parse(ctx, "x+x+y+y", w);

            obfuscated = RustAstParser.Parse(ctx, "(2*x + 2*y + 2*x + 2*y) & (4*(x+y))", w);
            deob = RustAstParser.Parse(ctx, "4*x+4*y", w);

            obfuscated = RustAstParser.Parse(ctx, "3*x + 3*y + 4*x + 4*y", w);
            deob = RustAstParser.Parse(ctx, "7*x + 7*y", w);

            obfuscated = RustAstParser.Parse(ctx, "2*x + 2*y + 1*x + 1*y", w);
            deob = RustAstParser.Parse(ctx, "3*x + 3*y", w);

            obfuscated = RustAstParser.Parse(ctx, "x+y+x", w);
            deob = RustAstParser.Parse(ctx, "x+x+y", w);

            obfuscated = RustAstParser.Parse(ctx, "2*x + 2*y + 1*x + 1*y", w);
            deob = RustAstParser.Parse(ctx, "3*x + 3*y", w);

            //obfuscated = RustAstParser.Parse(ctx, "(((x&y) + (x&y)) + (x^y)) & (x+y)+0", w);
            //deob = RustAstParser.Parse(ctx, "x+y", w);

            //obfuscated = RustAstParser.Parse(ctx, "25*x + 25*y + 27*x + 27*y", w);
            //deob = RustAstParser.Parse(ctx, "52*x + 52*y", w);

            var cache = new Dictionary<AstIdx, AstIdx>();


            obfuscated = Canonicalize(obfuscated, cache);
            deob = Canonicalize(deob, cache);

        }



        private AstIdx Canonicalize(AstIdx idx, Dictionary<AstIdx, AstIdx> cache)
        {
            if (cache.TryGetValue(idx, out var existing))
                return existing;

            var opc = ctx.GetOpcode(idx);

            if (opc == AstOp.Symbol || opc == AstOp.Constant)
            {
                cache[idx] = idx;
                return idx;
            }

            if (opc == AstOp.Neg)
            {
                var result = ctx.Neg(Canonicalize(ctx.GetOp0(idx), cache));
                cache[idx] = result;
                return result;
            }

            var op0 = Canonicalize(ctx.GetOp0(idx), cache);
            var op1 = Canonicalize(ctx.GetOp1(idx), cache);

            if (opc == AstOp.Mul && ctx.GetOpcode(ctx.GetOp1(idx)) == AstOp.Constant)
                (op0, op1) = (op1, op0);


            if (opc == AstOp.Mul && ctx.GetOpcode(op0) == AstOp.Constant)
            {

                var c = ctx.GetConstantValue(op0);
                var isNegative = (c & (1ul << (ushort)(w - 1)));
                var result = ExpandMulAsRepeatedAdd(op1, c);



                cache[idx] = result;

                return result;
            }


            var rebuilt = ctx.Binop(opc, op0, op1);
            cache[idx] = rebuilt;
            return rebuilt;
        }


        // Rewrite c1*a as a DAG of add nodes 
        private AstIdx ExpandMulAsRepeatedAdd(AstIdx x, ulong c)
        {
            if (c == 0)
                return ctx.Constant(0, ctx.GetWidth(x));
            if (c == 1)
                return x;


            int highBit = 63;
            while (highBit > 0 && ((c >> highBit) & 1) == 0)
                highBit--;

            AstIdx acc = x;
            for (int i = highBit - 1; i >= 0; i--)
            {

                acc = ctx.Add(acc, acc);


                if (((c >> i) & 1) == 1)
                    acc = ctx.Add(acc, x);
            }

            return acc;
        }

        private void SimplifyMany(IEnumerable<Poly> toSimplify, Dictionary<Monomial, Poly> mapping, bool actually = true)
        {
            if (!actually)
                return;
            foreach (var p in toSimplify)
            {
                foreach (var (monomial, value) in mapping)
                {
                    p.ReplaceSubset(monomial, value);
                    p.Simplify();
                }
            }
        }

        private void SimplifyViaMapping(Poly toSimplify, Dictionary<Monomial, Poly> mapping)
        {
            foreach (var (monomial, value) in mapping)
                toSimplify.ReplaceSubset(monomial, value);
        }

        private Dictionary<Monomial, Poly> LearnLinearSimplifications(List<Poly> graded, List<Poly> original)
        {
            var mapping = new Dictionary<Monomial, Poly>();

            var update = (int start, Monomial lm, Poly v) =>
            {
                mapping.Add(lm, v);
                for (int i = start + 1; i < graded.Count; i++)
                {
                    graded[i].ReplaceSubset(lm, v);
                }
            };

        start:
            bool changed = true;
            while (changed)
            {
                changed = false;
                graded.Sort();

                for (int i = 0; i < graded.Count; i++)
                {
                    var curr = graded[i].Clone();
                    if (mapping.ContainsKey(curr.Lm))
                        continue;

                    // If the polynomial is zero, update it accordingly.
                    var lm = curr.Lm;
                    if (curr.Coeffs.Count == 1)
                    {
                        var v = Poly.Constant(0);
                        update(i, lm, v);
                        changed = true;
                        goto start;
                    }

                    var other = graded[i].Clone();
                    if (mapping.ContainsKey(other.Lm))
                        continue;

                    var rhs = other.Clone();
                    rhs.Remove(other.Lm);
                    rhs = -1L * rhs;

                    if (other.Coeffs[other.Lm] == -1)
                    {
                        rhs = -1L * rhs;
                    }

                    else if (other.Coeffs[other.Lm] != 1)
                    {
                        Console.WriteLine("Skipping case that we could probably handle..");
                        continue;
                    }



                    update(i, other.Lm, rhs);
                    changed = true;
                    goto start;

                    /*
                    for(int j = i + 1; j < graded.Count; j++)
                    {
                        var other = graded[j].Clone();
                        if (mapping.ContainsKey(other.Lm))
                            continue;

                        var rhs = other.Clone();
                        rhs.Remove(other.Lm);
                        rhs = -1L * rhs;

                        if (other.Coeffs[other.Lm] == -1)
                            rhs = -1L * rhs;
                        else
                            Debug.Assert(other.Coeffs[other.Lm] == 1);

                        

                        update(j, other.Lm, rhs);
                        changed = true;
                        goto start;
                    }
                    */
                }


            }

            // Debugger.Break();

            return mapping;

        }

        public void Gauss(List<Poly> ideal, Dictionary<Monomial, Poly> simplificationMapping)
        {
            var temp = new List<Poly>();
            var seen = new HashSet<Monomial>(0);
            foreach (var p in ideal.ToList())
            {
                if (p.Coeffs.Count == 0)
                    continue;

                if (seen.Contains(p.Lm))
                    continue;

                seen.Add(p.Lm);
                temp.Add(p);
            }

            ideal = temp;

            var changed = new bool[ideal.Count];

            ideal = ideal.OrderBy(x => x.Coeffs.Count).ToList();

            for (int i = 0; i < ideal.Count; i++)
            {
                for (int j = i + 1; j < ideal.Count; j++)
                {
                    var p0 = ideal[i];
                    var p1 = ideal[j];

                    if (p0.Coeffs.Count > 0 && p0.Coeffs[p0.Lm] != 1 && p0.Coeffs[p0.Lm] != -1)
                        continue;

                    var rhs = p0.Rhs();

                    var shared = rhs.Coeffs.Keys.Intersect(p1.Coeffs.Keys).OrderBy(x => x).ToList().FirstOrDefault();
                    if (shared == null)
                        continue;

                    var coeff = rhs.Coeffs[shared];
                    var targetCoeff = p1.Coeffs[shared];
                    // Over Z (infinite integers): we need targetCoeff to be
                    // exactly divisible by coeff. s = targetCoeff / coeff.
                    if (coeff == 0 || targetCoeff % coeff != 0)
                        continue;
                    var s = targetCoeff / coeff;

                    var newValue = p1 - (s * rhs);
                    newValue += s * p0.Lm;
                    newValue.Simplify();

                    if (newValue.Coeffs.Count <= p1.Coeffs.Count && p1 != newValue)
                    {
                        changed[j] = true;
                        ideal[j] = newValue;
                    }
                }
            }

            for (int i = 0; i < ideal.Count; i++)
            {
                if (!changed[i])
                    continue;

                simplificationMapping[ideal[i].Lm] = ideal[i].Rhs();
            }

            //Debugger.Break();
        }

        private void LearnTrivialFacts(List<Poly> currIdeal, Dictionary<Monomial, Poly> simplificationMapping)
        {
            for (int i = 0; i < currIdeal.Count; i++)
            {
                var p0 = currIdeal[i];
                if (p0.Coeffs.Count == 1)
                {
                    simplificationMapping.TryAdd(p0.Lm, Poly.Constant(0));
                    continue;
                }

                // Experiment: Forward trivial identities like `op1 = x`.
                // I have a suspicion that we'll want to disable this unless it corresponds to an intermediate variable?
                if (p0.Coeffs.Count == 2)
                //if (false)
                //if (false)
                {
                    var rhs = p0.Rhs();
                    var lm = rhs.Lm;
                    if (lm.SortedVars.Length > 1)
                        goto skip;
                    if (lm.SortedVars.Length != 1 || lm.SortedVars.Single().Kind == SymKind.Input || p0.Lm.SortedVars.Length != 1 || lm.SortedVars.Single().BitIndex == p0.Lm.SortedVars.Single().BitIndex)
                        goto skip;
                    if (lm.SortedVars.Length != 1)
                        goto skip;

                    simplificationMapping.TryAdd(p0.Lm, rhs);
                    continue;
                }


            skip:
                for (int j = i + 1; j < currIdeal.Count; j++)
                {
                    var p1 = currIdeal[j];
                    if (simplificationMapping.ContainsKey(p1.Lm))
                        continue;

                    var diff0 = p0.Clone() - p0.Lm;
                    var diff1 = p1.Clone() - p1.Lm;
                    var final = (diff0 - diff1);
                    final.Simplify();
                    if (final.Coeffs.Count == 0)
                    {
                        //simplificationMapping[p1.Lm] = p0.Lm;
                        simplificationMapping.TryAdd(p1.Lm, p0.Lm);
                        continue;
                    }
                }
            }
        }

        // TODO: The result vector pruning stuff could be incorrect. Have not tested heavily
        private List<Poly> GetNonlinearFacts(List<Poly> currIdeal, Dictionary<Poly, Poly> lexCache)
        {
            // Compute like 64 input combinations.. for each variable store a result vector..
            //var allVars = MsolveWrapper.GetSortedVars(currIdeal);
            var inputVars = new List<SymVar>();
            var otherVars = new List<SymVar>();
            foreach (var p in currIdeal)
            {
                foreach (var m in p.Coeffs.Keys.Skip(1))
                {
                    foreach (var v in m.SortedVars)
                        inputVars.Add(v);
                }

                otherVars.Add(p.Coeffs.Keys.First().SortedVars.Single());
            }

            inputVars = inputVars.Distinct().ToList();
            otherVars = otherVars.Distinct().ToList();

            // var numCombinations = 1ul << (ushort)Math.Max(inputVars.Count, 4);
            var numCombinations = 1ul << 4;
            var signatureVectors = otherVars.ToDictionary(x => x, x => new TruthTable(5));

            // Ulongs can only fit 64 vars
            Debug.Assert(inputVars.Count < 64);


            var rand = new SeededRandom();

            // 2^t input combinations... assigning values to each variable
            for (ulong varComb = 0; varComb < numCombinations; varComb++)
            {
                // Assign values to the input combinations
                Dictionary<SymVar, ulong> varValues = new();
                for (int i = 0; i < inputVars.Count; i++)
                {
                    // Compute an assignment for this variable
                    var value = (varComb >> (ushort)i) & 1;
                    if (i > 16)
                        value = rand.GetRandUlong() & 1;

                    varValues[inputVars[i]] = value;
                }

                for (int pi = 0; pi < currIdeal.Count; pi++)
                {
                    var p = currIdeal[pi];
                    if (p.Lm.SortedVars.Length != 1)
                        continue;

                    long result = 0;
                    foreach (var (monom, coeff) in p.Coeffs.Skip(1))
                    {
                        long isSet = 1;
                        foreach (var v in monom.SortedVars)
                            isSet &= (long)varValues[v];

                        result += coeff * isSet;
                    }

                    result *= -1L;

                    //Debug.Assert(result == 0 || result == 1);
                    var leadingVar = p.Lm.SortedVars.Single();
                    varValues[leadingVar] = (ulong)result;
                    signatureVectors[leadingVar].SetBit((int)varComb, result != 0);
                }
            }


            var facts = new HashSet<Poly>();
            for (int i = 0; i < currIdeal.Count; i++)
            {
                var p0 = currIdeal[i];
                if (p0.Coeffs.Count == 0)
                    continue;

                var tbl0 = signatureVectors[p0.Lm.SortedVars.Single()];

                bool ignore = false;
                for (int j = i + 1; j < currIdeal.Count; j++)
                {
                    var p1 = currIdeal[j];

                    if (p1.Coeffs.Count == 0)
                        continue;

                    // Limit exponential growth of learned facts
                    if (p0.Lm.SortedVars.Concat(p1.Lm.SortedVars).Distinct().Count() > 2)
                        continue;

                    var tbl1 = signatureVectors[p1.Lm.SortedVars.Single()];

                    var prod = p0.Lm * p1.Lm;
                    var prodTbl = tbl0.Clone();
                    prodTbl.And(tbl1);
                    if (ignore || prodTbl.IsZero)
                    {
                        var reduced = LexReduce(prod, currIdeal, lexCache);
                        if (reduced.Coeffs.Count == 0)
                        {
                            facts.Add(prod);
                            continue;
                        }
                    }

                    for (int k = j + 1; k < currIdeal.Count; k++)
                    {
                        break;
                        var p2 = currIdeal[k];

                        if (p2.Coeffs.Count == 0)
                            continue;

                        // Limit exponential growth of learned facts
                        if (p0.Lm.SortedVars.Concat(p1.Lm.SortedVars).Concat(p2.Lm.SortedVars).Distinct().Count() > 3)
                            continue;

                        var tbl2 = signatureVectors[p2.Lm.SortedVars.Single()];
                        var prod2 = p0.Lm * p1.Lm * p2.Lm;
                        var prodTbl2 = tbl0.Clone();
                        prodTbl2.And(tbl1);
                        prodTbl2.And(tbl2);
                        if (ignore || prodTbl2.IsZero)
                        {
                            var reduced = LexReduce(prod2, currIdeal, lexCache);
                            if (reduced.Coeffs.Count == 0)
                            {
                                facts.Add(prod2);
                                continue;
                            }
                        }
                    }

                    var cand0Tbl = prodTbl.Clone();
                    cand0Tbl.Xor(tbl0);
                    if (ignore || cand0Tbl.IsZero)
                    {

                        var cand0 = prod - new Poly(p0.Lm);
                        var diff0 = LexReduce(cand0, currIdeal, lexCache);
                        if (diff0.Coeffs.Count == 0)
                        {
                            facts.Add(cand0);
                            continue;

                        }
                    }

                    var cand1Tbl = prodTbl.Clone();
                    cand1Tbl.Xor(tbl1);
                    if (ignore || cand1Tbl.IsZero)
                    {
                        var cand1 = prod - new Poly(p1.Lm);
                        var diff1 = LexReduce(cand1, currIdeal, lexCache);
                        if (diff1.Coeffs.Count == 0)
                        {
                            facts.Add(cand1);
                            continue;
                        }
                    }


                }
            }

            foreach (var f in facts)
                f.Simplify();

            facts.RemoveWhere(x => x.Coeffs.Count == 0);

            return facts.ToList();
        }

        public void SimplifyIdeal(List<Poly> ideal, Dictionary<Monomial, Poly> trivialFacts)
        {
            SimplifyMany(ideal, trivialFacts);
            var temp = new List<Poly>();
            var seen = new HashSet<Monomial>(0);
            foreach (var p in ideal.ToList())
            {
                p.Simplify();
                if (p.Coeffs.Count == 0)
                    continue;

                if (seen.Contains(p.Lm))
                    continue;

                seen.Add(p.Lm);
                temp.Add(p);
            }

            ideal.Clear();
            ideal.AddRange(temp);
        }


        public void ReduceIdeal(List<Poly> ideal, List<Poly> nonlinearFacts)
        {
            var temp = new List<Poly>();
            var seen = new HashSet<Monomial>(0);
            foreach (var _p in ideal.ToList())
            {
                // Reduce and update coefficients
                _p.Simplify();
                var p = LexReduce(_p, nonlinearFacts);
                p.Simplify();
                _p.Coeffs = p.Clone().Coeffs;


                if (p.Coeffs.Count == 0)
                    continue;

                if (seen.Contains(p.Lm))
                    continue;

                seen.Add(p.Lm);
                temp.Add(p);
            }

            ideal.Clear();
            ideal.AddRange(temp);
        }

        private void TailMerge(List<Poly> ideal)
        {
            var bar = Nullspace.FindLinearIdentities(ideal);
            //Debugger.Break();
        }

        public void Run()
        {
            var throwaway = new List<(int, uint, Poly)>();
            uint totalOrder = 0;
            var firstSeen = new Dictionary<SymVar, uint>();
            var visit = new List<AstIdx>() { deob, obfuscated };

            List<int> counts = new();
            Dictionary<(AstIdx, int bitIdx), Poly> cache = new();

            // Trivial identities (merge equivalent nodes and zero identities)
            var trivialFacts = new Dictionary<Monomial, Poly>();


            List<List<Poly>> ideals = new();
            List<List<Poly>> nonlinearFactLists = new();

            List<Poly> nullspaceFacts = new();

            HashSet<Poly> rcache = new();




            var definitions = new Dictionary<Monomial, HashSet<Poly>>();


            for (int sliceIdx = 0; sliceIdx < w; sliceIdx++)
            {
                Dictionary<Poly, Poly> lexCache = new();

                var results = new List<List<Poly>>();
                foreach (var _ in visit)
                    results.Add(new());

                // Compute the polynomials corresponding to the ith output bit
                for (int i = 0; i < visit.Count; i++)
                {
                    results[i].Add(GetSpecification(visit[i], sliceIdx, cache, throwaway, firstSeen, ref totalOrder, true).Clone());
                }

                // Update the ideal with previous facts
                var all = throwaway.Select(x => x.Item3).ToList();
                var ideal = all.Skip(counts.LastOrDefault()).Select(x => x.Clone()).ToList();

                counts.Add(throwaway.Count);
                SimplifyMany(ideal, trivialFacts);

                /*
                var allLex = all.Select(x => x.Clone()).ToList();
                SimplifyMany(all, trivialFacts);
                allLex = ReduceLexGroebnerBasis(allLex, new());
                Console.WriteLine("All lex: ");
                foreach (var p in allLex)
                    Console.WriteLine($"    {p}");
                */

                // Compute a reduced lexicographic groebner basis
                var lexGb = ideal.Select(x => x.Clone()).ToList();
                lexGb = ReduceLexGroebnerBasis(lexGb, lexCache);

                // Use this basis to learn new facts.
                LearnTrivialFacts(lexGb, trivialFacts);
                // Update both ideals
                SimplifyIdeal(ideal, trivialFacts);
                SimplifyIdeal(lexGb, trivialFacts);

                var nonlinearFacts = new List<Poly>();
                if (nonlinearFactLists.Count != 0)
                    nonlinearFacts = nonlinearFactLists.Last();

                ReduceIdeal(ideal, nonlinearFacts);
                ReduceIdeal(lexGb, nonlinearFacts);

                Console.WriteLine("Partial lex gb: ");
                foreach (var p in lexGb)
                    Console.WriteLine($"    {p}");
                TailMerge(lexGb);


                lexGb.AddRange(nullspaceFacts);
                //var bar = Nullspace.FindLinearIdentities(lexGb);
                //nullspaceFacts.AddRange(bar);




                /*
                var allLex = all.Select(x => x.Clone()).ToList();
                SimplifyMany(all, trivialFacts);
                allLex = ReduceLexGroebnerBasis(allLex, new());
                Console.WriteLine("All lex: ");
                foreach (var p in allLex)
                    Console.WriteLine($"    {p}");
                */
                
                //if(sliceIdx >= 2)
                /*
                if (false)
                //if (true)
                {
                    var prev = all.Skip(counts[counts.Count - 3]).Select(x => x.Clone()).ToList();
                    SimplifyMany(prev, trivialFacts);
                    var allLex = ReduceLexGroebnerBasis(prev, new());

                    allLex.RemoveAll(x => x.Lm.SortedVars.Single().BitIndex != sliceIdx);

                    ReduceIdeal(allLex, nonlinearFactLists[sliceIdx - 2]);

                    Console.WriteLine("All lex: ");
                    foreach (var p in allLex)
                        Console.WriteLine($"    {p}");

                    var otherFacts = GetNonlinearFacts(allLex, new());

                    Debugger.Break();

                }
                */
                
                

                //var stupidFacts = GetNonlinearFacts(allLex, new());


                // Problem: We're simplifying
                // Using a lex reduced gb should make things much faster..
                var nfacts = GetNonlinearFacts(lexGb, lexCache);
                //nfacts.AddRange(bar);
                //SimplifyIdeal(nfacts, trivialFacts);
                nonlinearFactLists.Add(nfacts);

                ideal.AddRange(nonlinearFacts);

                ideals.Add(ideal.ToList());


                Console.WriteLine($"Ideal: ");
                foreach (var p in ideal)
                    Console.WriteLine($"    {p}");



                // Update the ideal with nonlinear facts
                //ideal.AddRange(nonlinearFacts);
                // Append the previous ideal




                /*

                var linearFacts = MsolveWrapper.Run(ideal.Select(x => x.Clone()).ToList(), MsolveWrapper.GetSortedVars(ideal));
                foreach (var p in linearFacts)
                    p.Simplify();
                linearFacts.RemoveAll(x => x.Coeffs.Count == 0);
                var otherFacts = linearFacts.Select(x => x.Clone()).ToList();
                linearFacts.RemoveAll(x => x.Coeffs.Keys.Any(x => x.SortedVars.Count > 1));
                linearFacts.Sort();
                */

                SageGb(ideal, false);


                var before = results[0][0].Clone();
                var after = results[1][0].Clone();
                foreach (var list in results)
                {
                    SimplifyMany(list, trivialFacts);
                }

                var r0 = results[0][0];
                var r1 = results[1][0];
                SimplifyViaMapping(r0, trivialFacts);
                SimplifyViaMapping(r1, trivialFacts);


                Console.WriteLine($"Result variables:\n    {r0}\n    {r1}\n");

                var diff = results[0][0] - results[1][0];

                Console.WriteLine("Reductions: ");

                var rDiff = LexReduce(diff, ideal);
                if (rDiff.Coeffs.Count != 0)
                {
                    Console.WriteLine(rDiff);
                    var temp = rDiff;



                    /*
                    var rewrites = new Dictionary<Monomial, Poly>();
                    Gauss(lexGb, rewrites);
                    foreach (var (monomial, rhs) in rewrites)
                    {
                        if (rhs.Coeffs.Keys.Any(x => x.SortedVars.Count > 1 || x.SortedVars.Single().BitIndex != sliceIdx || x.SortedVars.Single().Kind == SymKind.Input))
                            continue;

                        nonlinearFacts.Add(monomial - rhs);
                    }
                    */

                    // It's hard to know upfront what linear facts we should learn.


                    //GeneralizeCarriedRelationships(rDiff, ideals, trivialFacts, nonlinearFacts);

                    var reduc = ReduceRec(rDiff, ideals, trivialFacts, nonlinearFactLists, rcache, definitions);

                    for (int i = ideals.Count - 2; i > 0; i--)
                    { 
                        break;
                        temp = LexReduce(temp, ideals[i]);
                        Console.WriteLine(temp);
                        if (temp.Coeffs.Count == 0)
                            break;
                    }
                    //var other = LexReduce(rDiff, ideals[ideals.Count - 2]);
                    ///var other = LexReduce(rDiff, ideals[ideals.Count - 3]);
                    Console.WriteLine($"REDUCED to: {reduc}\n\n");
                    // Debugger.Break();


                }

                else
                {
                    if (r0.Coeffs.Count != 0 && r1.Coeffs.Count != 0)
                    {
                        var m0 = r0.Coeffs.Single().Key;
                        var m1 = r1.Coeffs.Single().Key;
                        trivialFacts[m1] = m0;
                    }
                    //trivialFacts[]
                }


            }
        }


        private Poly PCanon(Poly rDiff)
        {
            rDiff = rDiff.Clone();
            rDiff.Simplify();

            if (rDiff.Coeffs.Count == 0)
                return rDiff;

            var gcd = FindGCDOfList(rDiff.Coeffs.Select(x => x.Value).ToList());
            foreach (var key in rDiff.Coeffs.Keys.ToList())
                rDiff.Coeffs[key] /= gcd;

            if (rDiff.Coeffs[rDiff.Lm] < 0)
                rDiff = -1L * rDiff;

            return rDiff;
        }

        private Poly ReduceRec(Poly rDiff, List<List<Poly>> ideals, Dictionary<Monomial, Poly> trivialFacts, List<List<Poly>> nonlinearFacts, HashSet<Poly> cache, Dictionary<Monomial, HashSet<Poly>> definitions)
        {
            rDiff = PCanon(rDiff);

            var zero = Poly.Constant(0);
            zero.Simplify();
            if (cache.Contains(rDiff))
                return zero;

            /*
            definitions.TryAdd(rDiff.Lm, new());
            definitions[rDiff.Lm].Add(rDiff.Clone());
            bool changed = true;
            while (changed)
            {
                if (rDiff.Coeffs.Count == 0)
                    break;

                var exists = definitions.TryGetValue(rDiff.Lm, out var candidates);
                if (!exists)
                    break;

                candidates = candidates.ToHashSet();
                candidates.Remove(rDiff);

                if (candidates.Count == 0)
                    break;

                Poly best = null;
                foreach (var cand in candidates)
                {
                    var cc = rDiff.Coeffs[rDiff.Lm];
                    var dd = cand.Coeffs[cand.Lm];

                    if (cc % dd != 0)
                        continue;

                    if(best == null)
                    {
                        best = cand;
                        continue;
                    }

                    if (Math.Abs(cand.Coeffs[cand.Lm]) < Math.Abs(cand.Coeffs[best.Lm]))
                        best = cand;
                    
                }

                if (best == null)
                    break;

                var c = rDiff.Coeffs[rDiff.Lm];
                var d = best.Coeffs[best.Lm];

                if (c % d == 0)
                {
                    var factor = c / d;
                    var toSub = factor * best;
                    rDiff = rDiff - toSub;
                }
                else
                {
                    break;
                }
                
                rDiff = PCanon(rDiff);
            }
            */

            if (rDiff.Coeffs.Count == 0)
                return rDiff;

            var targets = rDiff.Coeffs.Keys.SelectMany(x => x.SortedVars).Where(x => x.Kind != SymKind.Input).Distinct().ToHashSet();
            var targetIdx = targets.First().BitIndex;

            var ideal = ideals[targetIdx];

            var nlFacts = nonlinearFacts[targetIdx];



            foreach (var v in rDiff.Coeffs.Keys.SelectMany(x => x.SortedVars).Distinct().ToList())
            {
                //if (v.Kind != SymKind.Input)
                //    continue;
                var withX = rDiff.Clone();
                var withoutX = Poly.Constant(0);
                withoutX.Simplify();
                foreach (var key in rDiff.Coeffs.Keys.ToList())
                {
                    var hasVar = key.SortedVars.Contains(v);
                    if (!hasVar)
                    {
                        withX.Remove(key);
                        withoutX.Add(key, rDiff.Coeffs[key]);
                    }
                    /*
                    if (!hasVar)
                        withX.Coeffs.Remove(key);
                    else
                        withoutX.Add(key, withX.Coeffs[key]);
                    */
                }

                withX.ReplaceSubset(new Monomial(v), Poly.Constant(1));



                if (withX == -2L * withoutX)
                {
                    rDiff = withX;
                }

                else
                {
                    //if (withX.Lhs() == -2L * withoutX.Lhs())
                    //    Debugger.Break();

                }

                /*
                withX.ReplaceSubset(new Monomial(v), Poly.Constant(1));

                var withoutX = rDiff.Clone();
                withoutX.ReplaceSubset(new Monomial(v), Poly.Constant(1));

                withX.Simplify();
                withoutX.Simplify();
                */

                //if (withX == -1L * withoutX || withoutX == -1L * withX)
                //   Debugger.Break();
            }



            /*
            foreach (var v in rDiff.Coeffs.Keys.SelectMany(x => x.SortedVars).Distinct().ToList())
            {
   
                var withX = rDiff.Clone();
                var withoutX = Poly.Constant(0);
                withoutX.Simplify();
                foreach (var key in rDiff.Coeffs.Keys.ToList())
                {
                    var hasVar = key.SortedVars.Contains(v);
                    if (!hasVar)
                    {
                        withX.Remove(key);
                        withoutX.Add(key, rDiff.Coeffs[key]);
                    }
   
                }

                withX.ReplaceSubset(new Monomial(v), Poly.Constant(1));



                if (withX == -2L * withoutX)
                {
                   
                }

                else
                {
                    var div = withX.Clone();
                    foreach (var m in div.Coeffs.Keys.ToList())
                    {
                        if (div.Coeffs[m] % 2 != 0)
                            goto end;

                        div.Coeffs[m] /= 2;
                    }

                    Poly misses = Poly.Constant(0);
                    Poly rr = Poly.Constant(0);
                    foreach(var (m, c) in div.Coeffs)
                    {
                        if (m.SortedVars.Length == 0)
                            continue;

                        if (!withoutX.Coeffs.ContainsKey(m) || withoutX.Coeffs[m] != -c)
                            misses.Add(m, c);
                        else
                            rr.Add(m, c);

                    }

                    misses.Simplify();
                    rr.Simplify();

                    if (misses.Coeffs.Count == 0)
                        rDiff = rr;

                    //if (withX.Lhs() == -2L * withoutX.Lhs())
                    //    Debugger.Break();

                }

            end:
                continue;

            }
            */


            rDiff.Simplify();
            if (cache.Contains(rDiff))
                return zero;

            rDiff = PCanon(rDiff);
            if (cache.Contains(rDiff))
                return zero;

            Console.WriteLine($"\nReducing {rDiff}\n");

            /*
            var changed2 = true;
            var ii = targetIdx;
            while (changed2)
            {
                var reduced = LexReduce(rDiff, nonlinearFacts[ii]);
                ii--;
                changed2 = reduced != rDiff;
                if (changed2)
                    Debugger.Break();


            }
            */

            //var linearTerms = rDiff.Coeffs.Where(x => x.Key.SortedVars.All(x => targets.Contains(x))).ToDictionary(x => x.Key, x => x.Value);
            var groups = new Dictionary<Monomial, Poly>();
            var remainder = Poly.Constant(0);
            foreach (var (monom, coeff) in rDiff.Coeffs)
            {
                if (!monom.SortedVars.Any(x => targets.Contains(x)))
                {
                    remainder += coeff * monom;
                    continue;
                }
                // If its only variables then throw it in a group.
                if (monom.SortedVars.All(x => targets.Contains(x)))
                {
                    groups.TryAdd(Monomial.Constant(), Poly.Constant(0));
                    groups[Monomial.Constant()] += coeff * monom;
                    continue;
                }

                var ourVars = new Monomial(monom.SortedVars.Where(x => targets.Contains(x)));
                var factoredFactors = new Monomial(monom.SortedVars.Where(x => !targets.Contains(x)));
                groups.TryAdd(factoredFactors, Poly.Constant(0));
                groups[factoredFactors] += coeff * ourVars;

            }


            List<Poly> reducIdeal = new();
            Dictionary<Poly, Poly> rcache = new();
            foreach (var best in groups.Values)
            {
                foreach (var p in groups.Values)
                    p.Simplify();

                var linearTerms = best.Coeffs;
                var gcd = FindGCDOfList(linearTerms.Select(x => x.Value).ToList());
                foreach (var key in linearTerms.Keys.ToList())
                    linearTerms[key] /= gcd;


                var slicePoly = new Poly(linearTerms);

                if (linearTerms.Count == 0)
                    continue;


                //var reduced = LexReduce(slicePoly, ideal, rcache);
                var exists = cache.Contains(slicePoly);
                Poly reduced = Poly.Constant(0);
                reduced.Simplify();
                if(!exists)
                    reduced = LexReduce(slicePoly, ideal, rcache);

                if (reduced.Coeffs.Count != 0)
                {
                    var inter = ReduceRec(reduced, ideals, trivialFacts, nonlinearFacts, cache, definitions);
                    reduced = inter;
                    Debug.Assert(reduced.Coeffs.Count == 0);
                }
                reducIdeal.Add(slicePoly);
                cache.Add(slicePoly);
            }

            remainder.Simplify();
            if (remainder.Coeffs.Count > 0)
                throw new InvalidOperationException();
            cache.Add(rDiff.Clone());

            return remainder;
        }

        public static long GCD(long a, long b)
        {
            while (b != 0)
            {
                long remainder = a % b;
                a = b;
                b = remainder;
            }
            return a;
        }

        // Include the FindGCDOfList function from step 2 here
        public static long FindGCDOfList(List<long> numbers)
        {
            if (numbers == null || numbers.Count == 0)
            {
                throw new ArgumentException("The list of numbers cannot be null or empty.", nameof(numbers));
            }

            long result = numbers[0];
            for (int i = 1; i < numbers.Count; i++)
            {
                result = GCD(result, numbers[i]);
                if (result == 1)
                {
                    return 1;
                }
            }
            return result;
        }

        // This is not gonna work.. exponential time again.
        private void GeneralizeCarriedRelationships(Poly rDiff, List<List<Poly>> ideals, Dictionary<Monomial, Poly> trivialFacts, List<Poly> nonlinearFacts, Dictionary<Poly, Poly> cache)
        {
            var targets = rDiff.Coeffs.Keys.SelectMany(x => x.SortedVars).Where(x => x.Kind != SymKind.Input).Distinct().ToList();
            var targetIdx = targets.First().BitIndex;

            var ideal = ideals[targetIdx];

            // Compute a reduced lexicographic groebner basis
            var lexGb = ideal.Select(x => x.Clone()).ToList();
            lexGb = ReduceLexGroebnerBasis(lexGb, cache);


            // Use this basis to learn new facts.
            LearnTrivialFacts(lexGb, trivialFacts);

            // Update both ideals
            SimplifyIdeal(ideal, trivialFacts);
            SimplifyIdeal(lexGb, trivialFacts);

            //lexGb.RemoveAll(x => !targets.Contains(x.Lm.SortedVars.Single()));
            lexGb.RemoveAll(x => x.Lm.SortedVars.Length > 1 || !targets.Contains(x.Lm.SortedVars.Single()));

            var rewrites = new Dictionary<Monomial, Poly>();
            Gauss(lexGb, rewrites);

            foreach (var (monomial, rhs) in rewrites)
            {
                //if (rhs.Coeffs.Keys.Any(x => x.SortedVars.Count > 1 || x.SortedVars.Single().BitIndex != targetIdx || x.SortedVars.Single().Kind == SymKind.Input))
                //     continue;
                //if (rhs.Coeffs.Keys.Any(x => x.SortedVars.Count > 1 || x.SortedVars.Single().Kind == SymKind.Input))
                //    continue;


                nonlinearFacts.Add(monomial - rhs);
                ideal.Remove(ideal.Single(x => x.Lm == monomial));
                ideal.Add(nonlinearFacts.Last());
            }


            var withNonlinear = ideal.ToList();
            withNonlinear.AddRange(nonlinearFacts);

            var other = LexReduce(rDiff, withNonlinear);

            Debugger.Break();

        }

        public void RunOld()
        {
            var throwaway = new List<(int, uint, Poly)>();
            uint totalOrder = 0;
            var firstSeen = new Dictionary<SymVar, uint>();
            var visit = new List<AstIdx>() { deob, obfuscated };

            List<int> counts = new();
            Dictionary<(AstIdx, int bitIdx), Poly> cache = new();

            var simplificationMapping = new Dictionary<Monomial, Poly>();

            var nonlinearFacts = new HashSet<Poly>();

            for (int sliceIdx = 0; sliceIdx < w; sliceIdx++)
            {
                var results = new List<List<Poly>>();
                foreach (var _ in visit)
                    results.Add(new());

                // Compute the polynomials corresponding to the ith output bit
                for (int i = 0; i < visit.Count; i++)
                {
                    results[i].Add(GetSpecification(visit[i], sliceIdx, cache, throwaway, firstSeen, ref totalOrder, true).Clone());
                }

                var ideal = throwaway.Select(x => x.Item3).ToList();

                // Add the set of nonlinear facts
                var temp = ideal.Skip(counts.LastOrDefault()).ToList();
                SimplifyMany(temp, simplificationMapping);
                temp.AddRange(nonlinearFacts);
                temp.Sort();

                // Probably highly illegal: Rewrite the groebner basis based on learned facts from earlier..
                SimplifyMany(temp, simplificationMapping);

                var currIdeal = ReduceLexGroebnerBasis(temp, null);
                Console.WriteLine($"Lex ideal: ");
                foreach (var p in currIdeal)
                    Console.WriteLine(p);



                //var simplified = mm.LookupSimplification(new Monomial(myVar)); // query one variable


                // Compute a groebner basis in graded lex order to learn linear facts.
                // i.e. rewrite polynomials in terms of each other


                Console.WriteLine("");

                // Learn obvious facts (a*b = 0)
                for (int i = 0; i < currIdeal.Count; i++)
                {
                    var p0 = currIdeal[i];
                    if (p0.Coeffs.Count == 1)
                    {
                        simplificationMapping.TryAdd(p0.Lm, Poly.Constant(0));
                        continue;
                    }

                    if (p0.Coeffs.Count == 2 && p0.Coeffs.Last().Key.Degree == 1)
                    {
                        if (p0.Coeffs.First().Value != 1 && p0.Coeffs.First().Value != -1)
                            continue;

                        simplificationMapping.TryAdd(p0.Lm, p0.Rhs());
                        continue;
                    }


                    for (int j = i + 1; j < currIdeal.Count; j++)
                    {
                        var p1 = currIdeal[j];
                        if (simplificationMapping.ContainsKey(p1.Lm))
                            continue;

                        var diff0 = p0.Clone() - p0.Lm;
                        var diff1 = p1.Clone() - p1.Lm;
                        var final = (diff0 - diff1);
                        final.Simplify();
                        if (final.Coeffs.Count == 0)
                        {
                            //simplificationMapping[p1.Lm] = p0.Lm;
                            simplificationMapping.TryAdd(p1.Lm, p0.Lm);
                            continue;
                        }
                    }
                }




                // Apply rewriting
                var fixedIdeal = currIdeal.Select(x => x.Clone()).ToList();
                SimplifyMany(fixedIdeal, simplificationMapping);
                fixedIdeal = fixedIdeal.Distinct().ToList();

                Gauss(fixedIdeal.Select(x => x.Clone()).ToList(), simplificationMapping);
                SimplifyMany(fixedIdeal, simplificationMapping);

                var linearFacts = MsolveWrapper.Run(fixedIdeal.Select(x => x.Clone()).ToList(), MsolveWrapper.GetSortedVars(fixedIdeal));
                foreach (var p in linearFacts)
                    p.Simplify();
                linearFacts.RemoveAll(x => x.Coeffs.Count == 0);
                var otherFacts = linearFacts.Select(x => x.Clone()).ToList();
                linearFacts.RemoveAll(x => x.Coeffs.Keys.Any(x => x.SortedVars.Length > 1));
                linearFacts.Sort();

                var other = LearnLinearSimplifications(linearFacts, fixedIdeal);
                foreach (var (k, v) in other)
                    simplificationMapping.TryAdd(k, v);



                // Update the cache with learned facts
                SimplifyMany(cache.Values, simplificationMapping);


                var before = results[0][0].Clone();
                var after = results[1][0].Clone();

                foreach (var list in results)
                {
                    SimplifyMany(list, simplificationMapping);
                }


                var diff = results[0][0] - results[1][0];

                var rDiff = LexReduce(diff, currIdeal);

                SageGb(currIdeal, false);

                Console.WriteLine($"Difference: {rDiff}");

                if (rDiff.Coeffs.Count != 0)
                    Debugger.Break();
                else
                    simplificationMapping[before.Lm] = after;

                //simplificationMapping.Add(before.Lm, after);

                //nonlinearFacts.Clear();
                Dictionary<Monomial, Poly> seen = new();
                for (int i = 0; i < currIdeal.Count; i++)
                {
                    //for (int j = i + 1; j < currIdeal.Count; j++)
                    for (int j = 0; j < currIdeal.Count; j++)
                    {
                        if (i == j)
                            continue;

                        //if (i == 4 && j == 5)
                        //    Debugger.Break();

                        var before0 = currIdeal[i];
                        var before1 = currIdeal[j];

                        var p0 = currIdeal[i].Clone();
                        var p1 = currIdeal[j].Clone();


                        //if (p1.Lm.ToString() == "op3_0cout")
                        //    Debugger.Break();


                        Poly bar0 = p0.Lm;
                        Poly bar1 = p1.Lm;

                        //if (bar0.Lm.ToString() == "op0_1cout" && bar1.Lm.ToString() == "op3_1cout")
                        //{
                        //    Debugger.Break();
                        //}


                        SimplifyViaMapping(bar0, simplificationMapping);
                        SimplifyViaMapping(bar1, simplificationMapping);
                        Poly prod = (LexReduce(bar0, currIdeal) * LexReduce(bar1, currIdeal)) - LexReduce(bar1, currIdeal);
                        prod.Simplify();
                        prod = LexReduce(prod, currIdeal);
                        if (bar0.Coeffs.Count > 0 && bar1.Coeffs.Count > 0 && prod.Coeffs.Count == 0)
                        {
                            nonlinearFacts.Add((bar0 * bar1) - bar1);
                            //Debugger.Break();
                        }


                        // this might be wrong
                        SimplifyViaMapping(p0, simplificationMapping);
                        SimplifyViaMapping(p1, simplificationMapping);
                        if (p0.Coeffs.Count == 0 || p1.Coeffs.Count == 0)
                            continue;

                        var m = p0.Lm * p1.Lm;
                        if (p0.Lm == p1.Lm)
                            continue;
                        if (seen.ContainsKey(m))
                            continue;

                        var reduced = LexReduce(m, currIdeal);
                        Console.WriteLine($"{m} => {reduced}");

                        //if (m.ToString().Contains("r4_1*op0_1cout"))
                        //    Debugger.Break();

                        if (reduced.Coeffs.Count == 0)
                        {
                            nonlinearFacts.Add(m - (reduced));
                        }

                        var r0 = LexReduce(p0.Lm, currIdeal);
                        var r1 = LexReduce(p1.Lm, currIdeal);
                        if (reduced == r0)
                        {
                            nonlinearFacts.Add(m - new Poly(p0.Lm));
                        }


                        if (reduced == r1)
                        {
                            nonlinearFacts.Add(m - new Poly(p1.Lm));
                        }


                        seen[m] = reduced;
                    }
                }


                //Debugger.Break();

                // Keep track of the "slice" corresponding to this bit
                counts.Add(throwaway.Count);



                Console.WriteLine("");



                /*
              


                var reduced = ReduceLexGroebnerBasis(tempIdeal);

                var diff = results[0][sliceIdx] - results[1][sliceIdx];

                var rDiff = LexReduce(diff, tempIdeal);

                Console.WriteLine($"Difference: {rDiff}");

                Debugger.Break();
                */
            }
        }


        public void RunSpecification()
        {
            var throwaway = new List<(int, uint, Poly)>();
            uint totalOrder = 0;
            var firstSeen = new Dictionary<SymVar, uint>();
            var visit = new List<AstIdx>() { obfuscated };
            var results = new List<Poly>();
            Dictionary<(AstIdx, int bitIdx), Poly> cache = new();

            var COLUMN = w;

            var roundIdx = 0;
            for (int sliceIdx = 0; sliceIdx < COLUMN; sliceIdx++)
            {
                // Compute the polynomials corresponding to the ith output bit
                for (int i = 0; i < visit.Count; i++)
                {
                    results.Add(GetSpecification(visit[i], sliceIdx, cache, throwaway, firstSeen, ref totalOrder, true));
                }
            }

            var ideal = throwaway.Select(x => x.Item3).ToList();

            var cin = Poly.Constant(0);
            for (int bitIdx = 0; bitIdx < w; bitIdx++)
            {
                List<List<Poly>> bits = new();
                var vars = ctx.CollectVariables(obfuscated);
                foreach (var v in vars)
                {
                    List<Poly> l = new();
                    bits.Add(l);
                    for (int vIdx = 0; vIdx < w; vIdx++)
                        l.Add(GetSpecification(v, vIdx, cache, throwaway, firstSeen, ref totalOrder, false));

                }
                Poly spec = bits[0][0] - bits[0][0];
                for (int bitIndex = bitIdx; bitIndex <= bitIdx; bitIndex++)
                {
                    Poly term = bits[0][0] - bits[0][0];
                    for (int varIndex = 0; varIndex < vars.Count; varIndex++)
                    {
                        //term += (1L << (ushort)bitIndex) * bits[varIndex][bitIndex];
                        var b = bits[varIndex][bitIndex];
                        term += b;
                    }

                    spec += term;
                }

                spec += cin;

                //Poly result = Poly.Constant(0);
                //foreach (var r in results)
                //    result += r;
                var result = results[bitIdx];

                var diff = spec - result;

                SageGb(ideal, false);

                foreach (var p in ideal)
                    p.Simplify();
                //var rrr = Reduce(diff, ideal);
                var rrr = LexReduce(diff, ideal);

                var tempCin = Poly.Constant(0);
                foreach (var (monom, coeff) in rrr.Coeffs)
                {
                    if (coeff % 2 != 0)
                        throw new InvalidOperationException();

                    tempCin += ((coeff / 2) * monom);
                }

                Console.WriteLine(rrr);

                cin = tempCin;

            }
            Debugger.Break();
        }

        public List<Poly> ReduceLexGroebnerBasis(List<Poly> ideal, Dictionary<Poly, Poly> cache)
        {
            var reduced = new List<Poly>();

            // 1. Remove polynomials whose leading monomial is divisible by the leading monomial of another polynomial in the basis
            var sorted = ideal.Where(p => p.Coeffs.Count > 0).OrderBy(p => p).ToList();
            var minimalBasis = new List<Poly>();

            foreach (var p in sorted)
            {
                bool isRedundant = false;
                foreach (var m in minimalBasis)
                {
                    if (m.Lm.Divides(p.Lm))
                    {
                        isRedundant = true;
                        break;
                    }
                }

                if (!isRedundant)
                {
                    minimalBasis.Add(p);
                }
            }

            // 2. Make the basis monic (leading coefficient = 1)
            // Since we are working over Z or Z/2^w, we might not always be able to divide by the leading coefficient.
            // Assuming we are working over a field or the leading coefficients are already 1 or -1.
            for (int i = 0; i < minimalBasis.Count; i++)
            {
                var p = minimalBasis[i].Clone();
                var lc = p.Coeffs[p.Lm];
                if (lc == -1)
                {
                    p = -1L * p;
                }
                else if (lc != 1)
                {
                    // If we can't make it monic, we just leave it as is for now.
                    // In a true field, we would multiply by the modular inverse.
                }
                minimalBasis[i] = p;
            }

            // 3. Fully reduce each polynomial against the rest of the basis
            for (int i = 0; i < minimalBasis.Count; i++)
            {
                var p = minimalBasis[i];
                var others = minimalBasis.Where((_, index) => index != i).ToList();

                var reducedP = LexReduce(p, others, cache);
                if (reducedP.Coeffs.Count > 0)
                {
                    reduced.Add(reducedP);
                }
            }

            return reduced.OrderBy(p => p).ToList();
        }

        public static HashSet<Poly> allSeen = new();

        public Poly LexReduce(Poly poly, List<Poly> ideal, Dictionary<Poly, Poly> cache = null)
        {
            var clone = poly.Clone();
            poly = poly.Clone();
            poly.Simplify();
            if (poly.Coeffs.Count == 0)
                return poly;

            if (cache != null && cache.TryGetValue(poly, out var existing))
                return existing;

            var sorted = ideal.Where(g => g.Coeffs.Count > 0).OrderBy(g => g).ToList();

            var remainder = new Poly();
            bool changed = true;
            while (poly.Coeffs.Count > 0 && changed)
            {
                changed = false;
                poly.Simplify();
                if (poly.Coeffs.Count == 0)
                    break;

                var lm = poly.Lm;
                var lc = poly.Coeffs[lm];

                foreach (var g in sorted)
                {
                    var gLm = g.Lm;
                    var gLc = g.Coeffs[gLm];

                    if (gLm.Divides(lm) && lc % gLc == 0)
                    {
                        long c = lc / gLc;
                        var quotientMonom = lm.Divide(gLm);

                        foreach (var kp in g.Coeffs)
                        {
                            poly.Add(quotientMonom * kp.Key, -c * kp.Value);
                        }

                        poly.Simplify();
                        changed = true;
                        break;
                    }
                }

                if (!changed)
                {
                    remainder.Add(lm, lc);
                    poly.Remove(lm);
                    changed = poly.Coeffs.Count > 0;
                }
            }

            // Append leftover terms
            foreach (var (m, c) in poly.Coeffs)
                remainder.Add(m, c);

            remainder.Simplify();

            cache?.TryAdd(clone, remainder.Clone());
            return remainder;
        }

        public Poly Reduce(Poly poly, List<Poly> ideal)
        {
            poly.Simplify();
            poly = poly.Clone();
            if (poly.Coeffs.Count == 0)
                return poly;

            if (poly.Coeffs.Keys.All(x => x.SortedVars.All(x => x.Kind == SymKind.Input)))
                return poly;

            var lm = poly.Lm;
            var target = ideal.FirstOrDefault(x => x.Lm == lm && x.Coeffs[lm] == 1)?.Clone();
            if (target == null)
            {
                var cand = ideal.First(x => x.Coeffs.ContainsKey(lm) && x.Coeffs[lm] == 1).Clone();
                Debug.Assert(cand.Lm <= lm);

                cand.Remove(lm);

                target = Reduce(cand, ideal);
            }

            else
            {
                target.Remove(lm);
            }

            var subst = -1L * target;

            var replaced = poly.Clone();
            replaced.Replace(lm, subst);

            return Reduce(replaced, ideal);

            //Debugger.Break();
        }


        // Now we need to figure out how to prune dead elements from the groebner basis
        // "Cone of influence", only problem is that `x0*x1` gets rewritten as 
        public void DeprecatedRunOld()
        {
            var idealArr = new List<(int, uint, Poly)>();
            uint totalOrder = 0;
            var firstSeen = new Dictionary<SymVar, uint>();
            var visit = new List<AstIdx>() { deob, obfuscated };
            var results = new List<List<Poly>>();
            foreach (var _ in visit)
                results.Add(new());
            Dictionary<(AstIdx, int bitIdx), Poly> cache = new();

            var linearFacts = new List<Poly>();
            var allSeen = new List<Poly>();

            var roundIdx = 0;
            for (int sliceIdx = 0; sliceIdx < w; sliceIdx++)
            {
                // Compute the polynomials corresponding to the ith output bit
                for (int i = 0; i < visit.Count; i++)
                {
                    results[i].Add(GetSpecification(visit[i], sliceIdx, cache, idealArr, firstSeen, ref totalOrder, true));
                }




                var iArr = idealArr.Select(x => x.Item3).ToList();
                foreach (var p in iArr)
                {
                    p.PruneDuplicates();
                    p.Simplify();
                }

                // Update the list of linear facts from the last GB
                iArr.AddRange(linearFacts);

                SageGb(iArr, false);



                var allVars = MsolveWrapper.GetSortedVars(iArr);
                var boolVars = new List<SymVar>();
                var skip = new List<SymVar>();
                foreach (var v in allVars)
                {
                    // Adding all variables seems to yield huge performance benefits for some reason
                    boolVars.Add(v);
                    continue;

                    if (v.Kind == SymKind.Input)
                    {
                        boolVars.Add(v);
                        continue;
                    }

                    if (v.BitIndex < sliceIdx)
                    {
                        boolVars.Add(v);
                        continue;
                    }

                    skip.Add(v);
                }




                var vars = ctx.CollectVariables(obfuscated);
                Poly spec0 = Monomial.Constant();
                Poly spec1 = Monomial.Constant();
                spec0 += results[0][sliceIdx];
                spec1 += results[1][sliceIdx];


                var specDiff = spec0 - spec1;
                allSeen.AddRange(iArr);
                var tempGb = MsolveWrapper.Run(iArr, boolVars);
                var reduction = Poly.Reduce(specDiff, tempGb);
                continue;


                var gb = MsolveWrapper.Run(iArr, boolVars);


                Console.WriteLine("GB: ");
                foreach (var p in gb)
                {
                    Console.WriteLine($"    {p}");
                }


                linearFacts.Clear();
                // Simplify the carry in info
                foreach (var (_, (bitIdx, arithInfos)) in carryIdentifiers.ToList())
                {
                    // Skip if there's no carry info
                    if (arithInfos.Count == 0)
                        continue;

                    var arithInfo = arithInfos.Last();
                    //if (bitIdx != sliceIdx)
                    //    continue;

                    var cin = Poly.Reduce(arithInfo.cin, gb);
                    var result = Poly.Reduce(arithInfo.result, gb);

                    var cout = CollectLinearFacts(arithInfo.cout, gb, linearFacts);
                    var pcout0 = CollectLinearFacts(arithInfo.pcout0, gb, linearFacts);
                    var pcout1 = CollectLinearFacts(arithInfo.pcout1, gb, linearFacts);

                    /*
                    var cout = Poly.Reduce(arithInfo.cout, gb);
                    var pcout0 = Poly.Reduce(arithInfo.pcout0, gb);
                    if (pcout0.IsEq(arithInfo.pcout0))
                        Debugger.Break();
                    var pcout1 = Poly.Reduce(arithInfo.pcout1, gb);
                    if (pcout1.IsEq(arithInfo.pcout1))
                        Debugger.Break();
             

                    if (result.IsEq(arithInfo.cout))
                        Debugger.Break();


                    // This works and gives us results
                    // Essentially we're finding facts like `op15_0cout = x0*y0` and propagating them up.
                    // This is enough usually..

                    if (cout.IsEq(arithInfo.cout) && arithInfo.cout.Coeffs.Count == 1)
                    {
                        var prevMonomial = arithInfo.cout.Coeffs.Keys.Single();
                        if (prevMonomial.SortedVars.Count == 1)
                        {
                            foreach (var p in gb)
                            {
                                if (p.Coeffs.Count != 1)
                                    continue;
                                var mm = p.Coeffs.Keys.Single();
                                if (!mm.SortedVars.Contains(prevMonomial.SortedVars.Single()))
                                    continue;

                                linearFacts.Add(p);

                                // Debugger.Break();
                            }
                        }
                    }
                    */

                    // But the above is not always enough^
                    // So now we propagate any fact where this variable is in the leading monomial
                    /*
                    if(cout.IsEq(arithInfo.cout) && arithInfo.cout.Coeffs.Count == 1)
                    {
                        var prevMonomial = arithInfo.cout.Coeffs.Keys.Single();
                        foreach (var p in gb)
                        {
                            if (p.Coeffs.Count > 2)
                                continue;

                            var mm = p.Lm;
                            var v = prevMonomial.SortedVars.Single();
                            if (!mm.SortedVars.Contains(v))
                                continue;

                            if (p.Coeffs.Count == 2 && p.Coeffs.Keys.SequenceEqual(new List<Monomial>() { new Monomial(v, v), new Monomial(v) }))
                                continue;

                            linearFacts.Add(p);

                            // Debugger.Break();
                        }
                    }
                    */

                    arithInfos[arithInfos.Count - 1] = new(cin, cout, pcout0, pcout1, result);
                }



                foreach (var (key, input) in cache.ToList())
                {
                    var p = input;
                    var r = Poly.Reduce(p.Clone(), gb);
                    Console.WriteLine($"{input}=>\n{r}\n\n");
                    cache[key] = r;
                }



                var reducedSpec = Poly.Reduce(specDiff, gb);
                reducedSpec = Poly.Reduce(reducedSpec, gb);
                if (reducedSpec.Coeffs.Count != 0)
                {
                    SageGb(allSeen, false);

                    var r = MsolveWrapper.Run(allSeen, MsolveWrapper.GetSortedVars(allSeen).Where(x => x.Kind == SymKind.Input).ToList());
                    var reduced = Poly.Reduce(specDiff, r);

                    Debugger.Break();
                }

                Console.WriteLine($"Round {roundIdx}");
                roundIdx++;

                idealArr.Clear();

                // Then any intermediate product that might be called on



            }

            Debugger.Break();
        }

        private Poly CollectLinearFacts(Poly before, List<Poly> gb, List<Poly> linearFacts)
        {
            var cout = Poly.Reduce(before, gb);
            if (!cout.IsEq(before))
                return cout;

            var prevMonomial = cout.Coeffs.Keys.Single();

            if (prevMonomial.SortedVars.Length == 1)
            {
                foreach (var p in gb)
                {
                    if (p.Coeffs.Count != 1)
                        continue;
                    //var mm = p.Coeffs.Keys.Single();
                    var mm = p.Lm;
                    if (!mm.SortedVars.Contains(prevMonomial.SortedVars.Single()))
                        continue;

                    Console.WriteLine($"Added linear fact: {p}");
                    linearFacts.Add(p);
                }
            }


            return cout;
        }


        // Each node gets an x, y, carry in, carry out bits
        private Poly GetSpecification(AstIdx idx, int bitIdx, Dictionary<(AstIdx, int bitIdx), Poly> cache, List<(int bitIndex, uint opIndex, Poly poly)> ideal, Dictionary<SymVar, uint> firstSeen, ref uint totalOrder, bool isOutput = false)
        {
            var key = (idx, bitIdx);
            if (cache.TryGetValue(key, out var existing))
                return existing;


            var opc = ctx.GetOpcode(idx);
            if (opc == AstOp.Symbol)
            {
                totalOrder++;
                cache[key] = new Poly(new Monomial(SymVar.Symbol(ctx, idx, bitIdx)));
                return cache[key];
            }

            if (opc == AstOp.Constant)
            {
                totalOrder++;

                var v = ctx.GetConstantValue(idx);
                var constant = (v & (1ul << (ushort)bitIdx)) == 0 ? 0ul : 1ul;

                cache[key] = Poly.Constant((long)constant);
                return cache[key];
            }

            if (!carryIdentifiers.ContainsKey(idx))
                carryIdentifiers.Add(idx, ((uint)carryIdentifiers.Count, new()));

            var update = (ref SymVar sym) =>
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

            var getOp = (uint index, ref uint totalOrder) =>
            {
                if (index == 0)
                    return GetSpecification(ctx.GetOp0(idx), bitIdx, cache, ideal, firstSeen, ref totalOrder);
                Debug.Assert(index == 1);
                return GetSpecification(ctx.GetOp1(idx), bitIdx, cache, ideal, firstSeen, ref totalOrder);
            };

            /*
            if(opc == AstOp.Add)
            {
                var a = getOp(0, ref totalOrder);
                var b = getOp(1, ref totalOrder);

                Poly cin = Poly.Constant(0);
                if (bitIdx > 0)
                    cin = arithInfo[bitIdx - 1].cout;

                // 2. Declare INTERMEDIATE variables FIRST (Medium rank)
                var psum = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}psum");
                update(psum);

                var pcout1 = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}pcout1");
                update(pcout1);

                var pcout2 = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}pcout2");
                update(pcout2);

 
                var cout = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}cout");
                update(cout);

                var sum = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}sum");
                update(sum);

                // Half adder
                ideal.Add((bitIdx, totalOrder++, psum - (a + b - 2 * a * b)));
                ideal.Add((bitIdx, totalOrder++, pcout1 - (a * b)));

                // 2nd half carry
                ideal.Add((bitIdx, totalOrder++, pcout2 - (psum * cin)));

                // Outputs
                Poly pc1 = new Monomial(pcout1);
                Poly pc2 = new Monomial(pcout2);
                ideal.Add((bitIdx, totalOrder++, cout - (pc1 + pc2)));
                ideal.Add((bitIdx, totalOrder++, sum - (psum + cin - 2 * psum * cin)));

                // 5. Save to info tracking
                arithInfo.Add(new(cin, cout, pc1, pc2, sum));



                totalOrder++;

                cache[key] = sum;

                return sum;
         
            }
            */
            if (opc == AstOp.Add)
            {
                if (arithInfo.Count > bitIdx)
                    return arithInfo[bitIdx].result;
                Debug.Assert(arithInfo.Count == bitIdx);
                var a = getOp(0, ref totalOrder);
                var b = getOp(1, ref totalOrder);

                var generate = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}gen");
                update(ref generate);

                var propagate = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}prop");
                update(ref propagate);

                var cout = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}cout");
                update(ref cout);

                var sum = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}sum");
                update(ref sum);


                Poly cin = Poly.Constant(0);
                if (bitIdx > 0)
                    cin = arithInfo[bitIdx - 1].cout;

                // I think this encoding is technically more optimal for the linear extraction idea


                ideal.Add((bitIdx, totalOrder++, generate - a * b));
                ideal.Add((bitIdx, totalOrder++, propagate - (a + b - 2 * generate)));
                // Is there another encoding that would simplify things? 
                ideal.Add((bitIdx, totalOrder++, cout - (generate + propagate * cin)));
                ideal.Add((bitIdx, totalOrder++, sum - (propagate + 2 * generate + cin - 2 * cout)));

                arithInfo.Add(new(cin, cout, propagate, generate, sum));


                //var cout = SymVar.Temp($"a[{carryId}][{bitIdx}].cout");

                /*
                var carryLhs = cout;
                var carryRhs = a * b + a * cin + b * cin - 2 * (a * b * cin);
                ideal.Add((bitIdx, totalOrder++, carryLhs - carryRhs));

                var member = sum - (a + b + cin + (-2 * (cout)));
                ideal.Add((bitIdx, totalOrder, member));

                arithInfo.Add(new(cin, cout, null, null, sum));
                */



                totalOrder++;

                cache[key] = sum;

                return sum;
            }

            if (opc == AstOp.And)
            {
                var a = getOp(0, ref totalOrder);
                var b = getOp(1, ref totalOrder);

                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"r{carryId}_{bitIdx}");
                update(ref y);
                ideal.Add((bitIdx, totalOrder, y - (a * b)));

                totalOrder++;
                cache[key] = y;
                return y;
            }

            if (opc == AstOp.Or)
            {
                var a = getOp(0, ref totalOrder);
                var b = getOp(1, ref totalOrder);

                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"r{carryId}_{bitIdx}");
                update(ref y);
                ideal.Add((bitIdx, totalOrder, y - (a - b + a * b)));

                totalOrder++;
                cache[key] = y;
                return y;
            }

            if (opc == AstOp.Xor)
            {
                var a = getOp(0, ref totalOrder);
                var b = getOp(1, ref totalOrder);

                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"r{carryId}_{bitIdx}");
                update(ref y);
                ideal.Add((bitIdx, totalOrder, (y - (a + b - (2 * (a * b))))));

                totalOrder++;
                cache[key] = y;
                return y;
            }

            if (opc == AstOp.Neg)
            {
                var a = getOp(0, ref totalOrder);
                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"r{carryId}_{bitIdx}");
                update(ref y);
                ideal.Add((bitIdx, totalOrder, y + (a - Poly.Constant(1))));

                totalOrder++;
                cache[key] = y;
                return y;
            }

            throw new InvalidOperationException();

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
            foreach (var v in monomial.SortedVars)
            {
                if (!assignment.TryGetValue(v, out var val))
                    throw new InvalidOperationException($"Variable {v} is not assigned.");
                termVal *= val;
            }

            return termVal;
        }

        private void BackwardsEliminate(List<Poly> ideal, int targetIdx, bool linearOnly = false, bool singleUseOnly = false, bool skipZeroes = false)
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
                    if (next.Lm == null && skipZeroes)
                        continue;
                    var v = next.Lm.SortedVars.First();
                    var currLm = new Monomial(v);

                    // If linearOnly, only do substitution of terms with 1 or more variables
                    if (linearOnly && curr.Coeffs.Count > 2)
                        continue;

                    var skip = ideal.Skip(i + 1).ToList();
                    if (singleUseOnly && skip.Count(x => x.Lm != null && x.Lm.SortedVars[0].Equals(v)) != 1)
                        continue;


                    if (!curr.Coeffs.ContainsKey(currLm))
                        continue;

                    var nextLm = next.Lm;

                    /*
                    var cmp = curr.Lm.CompareTo(nextLm);
                    if (cmp == 1)
                    {
                        continue;
                    }
                    */

                    var lc = solver.LinearCongruence((UInt128)curr.Coeffs[currLm] & mmask, (UInt128)(next.Coeffs[nextLm]) & mmask, mmask + 1);
                    if (lc == null)
                        continue;



                    var sol = solver.GetSolution(0, lc);

                    // Move the value over to the RHS
                    var currRhs = curr.Clone();
                    currRhs.Remove(currLm);
                    currRhs = -1L * currRhs;

                    var temp = new Poly();

                    if (nextLm.SortedVars.Length == 1)
                    {
                        temp.Add(Monomial.Constant(), 1);
                    }
                    else
                    {
                        var map = nextLm.SortedVars.ToHashSet();
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


                    Console.WriteLine($"Intermediate product:  {next}\n");
                    //var rr = Validate(ideal, (int)w);


                    //break;


                    //Debugger.Break();
                }
                //var curr = ideal.First(x => x.Lm.SymVars.Contains(last.Lm.SymVars.First()));



            }

            //Debugger.Break();
        }

        // Identify c1*v1 + c2*v2 and substitute `v2` for all instances of `c1`

        private void LinElim(List<Poly> ideal, bool allowNonlinear = false, bool QQ = true)
        {
            var mmask = ModuloReducer.GetMask(w);
            var solver = new LinearCongruenceSolver(mmask);

            bool changed = true;
            while (changed)
            {
                changed = false;
                // Find ideal members with two terms c1*v1 + c2*v2 = 0 
                // and substitute the rhs in 
                for (int i = 0; i < ideal.Count; i++)
                {
                    var curr = ideal[i];
                    if (curr.Coeffs.Count != 2 && curr.Coeffs.Count != 1)
                        continue;

                    var mons = curr.Coeffs.Keys.ToList();
                    var m1 = mons[0];

                    var lm = curr.Lm;

                    if (lm.SortedVars.Length != 1)
                        continue;

                    var variable = lm.SortedVars.Single();
                    var coeff = curr.Coeffs[lm]; // c1

                    // Compute rhs
                    var rhs = curr.Clone();
                    rhs.Remove(lm);
                    rhs = -1L * rhs; // -c2*v2

                    // Substitute assignment into all polynomials
                    for (int j = i + 1; j < ideal.Count; j++)
                    {
                        if (i == j) continue;

                        var next = ideal[j].Clone();

                        bool onlyOne = curr.Coeffs.Count == 1;
                        if (onlyOne && next.Coeffs.Keys.Any(x => lm.Divides(x)))
                        {
                            var banned = next.Coeffs.Keys.Where(x => lm.Divides(x)).ToList();
                            foreach (var t in banned)
                                next.Remove(t);

                            ideal[j] = next;
                            changed = true;
                            continue;
                        }

                        var targets = next.Coeffs.Keys.Where(k => k.SortedVars.Contains(variable)).ToList();
                        if (targets.Count == 0)
                            continue;

                        bool instantiated = false;
                        foreach (var targetM in targets)
                        {
                            var targetCoeff = next.Coeffs[targetM];

                            long s;
                            if (QQ)
                            {
                                // Over Z (infinite integers): we need targetCoeff to be
                                // exactly divisible by coeff. s = targetCoeff / coeff.
                                if (coeff == 0 || targetCoeff % coeff != 0)
                                    continue;
                                s = targetCoeff / coeff;
                            }
                            else
                            {
                                // Over Z/(2^w): solve coeff * s ≡ targetCoeff (mod 2^w).
                                var lc = solver.LinearCongruence((UInt128)coeff & mmask, (UInt128)targetCoeff & mmask, mmask + 1);
                                if (lc == null || lc.n == 0)
                                    continue;
                                s = (long)solver.GetSolution(0, lc);
                            }

                            // The term T is removed
                            next.Remove(targetM);

                            // Remove M from the monomial
                            var map = targetM.SortedVars.ToHashSet();
                            map.Remove(variable);
                            var remainderM = new Monomial(map);

                            // Add s * rhs * M
                            var increment = s * rhs;

                            // Multiply by remainderM
                            var temp = new Poly();
                            temp.Add(remainderM, 1);

                            increment = increment * temp;

                            next = next + increment;

                            if (!QQ)
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

        private void SageGb(List<Poly> ideal, bool linearize = true)
        {
            var mask = (long)ModuloReducer.GetMask(w);
            mask = -1;


            var seen = new HashSet<SymVar>();
            var varOrder = new List<SymVar>();

            var linMap = new Dictionary<Monomial, string>();
            int linCounter = 0;

            foreach (var poly in ideal)
            {
                foreach (var monomial in poly.Coeffs.Keys.OrderByDescending(x => x))
                {
                    foreach (var v in monomial.SortedVars)
                    {
                        if (seen.Add(v))
                            varOrder.Add(v);
                    }

                    if (linearize && monomial.SortedVars.Length > 1 && !linMap.ContainsKey(monomial))
                    {
                        linMap[monomial] = $"lin{linCounter++}";
                    }
                }
            }

            varOrder = varOrder.OrderByDescending(x => x).ToList();
            var allNames = new List<string>(varOrder.Select(v => v.Name));
            if (linearize)
                allNames.AddRange(linMap.Values);

            var sb = new StringBuilder();
            sb.AppendLine($"n = {w}  # Exponent for 2^n (e.g., 2^{w} = {1L << (int)w})");
            sb.AppendLine("modulus = 2**n");
            sb.AppendLine();
            sb.AppendLine("R = PolynomialRing(QQ, ");
            sb.AppendLine("    names=[");

            for (int i = 0; i < allNames.Count; i += 3)
            {
                var chunk = allNames.Skip(i).Take(3).Select(v => $"'{v}'");
                var trailing = (i + 3 < allNames.Count) ? "," : "";
                sb.AppendLine($"        {string.Join(", ", chunk)}{trailing}");
            }

            sb.AppendLine("    ],");
            sb.AppendLine("    order='lex'");
            sb.AppendLine(")");
            sb.AppendLine();
            sb.AppendLine("R.inject_variables()");
            sb.AppendLine();
            sb.AppendLine("polys = [");


            bool skipAND = false;
            for (int polyIdx = 0; polyIdx < ideal.Count; polyIdx++)
            {
                var poly = ideal[polyIdx];
                var terms = new List<string>();

                foreach (var (monomial, rawCoeff) in poly.Coeffs)
                {
                    var coeff = rawCoeff & mask;
                    if (coeff == 0)
                        continue;



                    if (monomial.SortedVars.Length == 0)
                    {
                        terms.Add(coeff.ToString());
                    }
                    else if (linearize && monomial.SortedVars.Length > 1 && !(skipAND && poly.Lm.SortedVars[0].Name.StartsWith("r0_")) && linMap.TryGetValue(monomial, out var linName))
                    {
                        if (coeff == 1)
                            terms.Add(linName);
                        else
                            terms.Add($"{coeff}*{linName}");
                    }
                    else
                    {
                        var varStr = string.Join("*", monomial.SortedVars.Select(v => v.Name));
                        if (coeff == 1)
                            terms.Add(varStr);
                        else
                            terms.Add($"{coeff}*{varStr}");
                    }
                }

                var polyStr = terms.Count > 0 ? string.Join(" + ", terms) : "0";
                var comma = polyIdx < ideal.Count - 1 ? "," : "";
                sb.AppendLine($"    {polyStr}{comma}");
            }

            sb.AppendLine("]");

            if (linearize)
            {
                sb.AppendLine();
                sb.AppendLine("# Linearization mapping:");
                foreach (var (monomial, linName) in linMap)
                {
                    var varStr = string.Join("*", monomial.SortedVars.Select(v => v.Name));
                    sb.AppendLine($"# {linName} = {varStr}");
                }
            }

            Console.WriteLine(sb.ToString());
        }

        public static bool Validate(List<Poly> ideal, int w)
        {
            Console.WriteLine("Skipping validat");
            return true;
            // Collect all input variables across the entire ideal.
            var allVars = new HashSet<SymVar>();
            foreach (var p in ideal)
                foreach (var m in p.Coeffs.Keys)
                    foreach (var v in m.SortedVars)
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
                            if (m.SortedVars.Length == 1)
                            {
                                var v = m.SortedVars.First();
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
                            if (monomial.SortedVars.Contains(gate))
                            {
                                // This term contains the gate variable.
                                // It should be of the form coeff * gate (linear in gate).
                                Debug.Assert(monomial.SortedVars.Length == 1, $"Gate variable {gate} appears in higher-degree monomial {monomial}");
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

        // TODO: Canonicalize 123*a into 7 shifted add circuits
        private void Linearize(AstIdx node, List<AstIdx> dfs, HashSet<AstIdx> seen)
        {
            if (seen.Contains(node))
                return;
        }
    }
}