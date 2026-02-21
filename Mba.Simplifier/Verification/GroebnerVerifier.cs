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
using System.Reflection;
using System.Text;
using System.Threading.Tasks;
using static System.Net.Mime.MediaTypeNames;

namespace Mba.Simplifier.Verification
{
    public record ArithInfo(Poly cin, Poly cout, Poly result);

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

        // Now we need to figure out how to prune dead elements from the groebner basis
        // "Cone of influence", only problem is that `x0*x1` gets rewritten as 
        public void Run()
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

            var roundIdx = 0;
            for (int sliceIdx = 0; sliceIdx < w; sliceIdx++)
            {
                // Compute the polynomials corresponding to the ith output bit
                for(int i = 0; i < visit.Count; i++)
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
                foreach(var v in allVars)
                {
                    // Adding all variables seems to yield huge performance benefits for some reason
                    boolVars.Add(v);
                    continue;

                    if(v.Kind == SymKind.Input)
                    {
                        boolVars.Add(v);
                        continue;
                    }

                    if(v.BitIndex < sliceIdx)
                    {
                        boolVars.Add(v);
                        continue;
                    }

                    skip.Add(v);
                }

                var gb = MsolveWrapper.Run(iArr, boolVars);

                Console.WriteLine("GB: ");
                foreach(var p in gb)
                {
                    Console.WriteLine($"    {p}");
                }


                linearFacts.Clear();
                // Simplify the carry in info
                foreach(var (_, (bitIdx, arithInfos)) in carryIdentifiers.ToList())
                {
                    // Skip if there's no carry info
                    if(arithInfos.Count == 0)
                            continue;

                    var arithInfo = arithInfos.Last();
                    //if (bitIdx != sliceIdx)
                    //    continue;

                    var cin = Poly.Reduce(arithInfo.cin, gb);
                    var cout = Poly.Reduce(arithInfo.cout, gb);
                    var result = Poly.Reduce(arithInfo.result, gb);

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

                    arithInfos[arithInfos.Count - 1] = new(cin, cout, result);
                }


                
                foreach(var (key, input) in cache.ToList())
                {
                    var p = input;
                    var r = Poly.Reduce(p.Clone(), gb);
                    Console.WriteLine($"{input}=>\n{r}\n\n");
                    cache[key] = r;
                }

                



                var vars = ctx.CollectVariables(obfuscated);
   

                Poly spec0 = Monomial.Constant();
                Poly spec1 = Monomial.Constant();
    

                spec0 += results[0][sliceIdx];
                spec1 += results[1][sliceIdx];

  
                var specDiff = spec0 - spec1;
                var reducedSpec = Poly.Reduce(specDiff, gb);
                reducedSpec = Poly.Reduce(reducedSpec, gb);
                if (reducedSpec.Coeffs.Count != 0)
                    Debugger.Break();

                Console.WriteLine($"Round {roundIdx}");
                roundIdx++;

                idealArr.Clear();

                // Then any intermediate product that might be called on



            }

            Debugger.Break();
        }



        // Old version attempting to implement the old paper
        public void RunOld()
        {
            var idealArr = new List<(int, uint, Poly)>();

            uint totalOrder = 0;
            var firstSeen = new Dictionary<SymVar, uint>();

            Dictionary<(AstIdx, int bitIdx), Poly> cache = new();

            var results = new List<Poly>();
            foreach (var curr in new AstIdx[] { obfuscated, deob })
            {
                Console.WriteLine("\n\n");
                for (int i = 0; i < w; i++)
                    results.Add(GetSpecification(curr, i, cache, idealArr, firstSeen, ref totalOrder, true));

                foreach (var m in idealArr)
                {
                    m.Item3.Simplify();
                    Console.WriteLine(m.Item3);
                }

                break;
            }

            var ideal = idealArr.ToList().Select(x => x.Item3).ToList();
            foreach (var member in ideal)
            {
                member.Simplify();
                Console.WriteLine(member);
            }

            var vars = ctx.CollectVariables(obfuscated);

            List<List<Poly>> bits = new();
            foreach (var v in vars)
            {
                List<Poly> l = new();
                bits.Add(l);
                for (int i = 0; i < w; i++)
                    l.Add(GetSpecification(v, i, cache, idealArr, firstSeen, ref totalOrder, false));

            }
            // Adder specification
            Poly spec = bits[0][0] - bits[0][0];
            for (int bitIndex = 0; bitIndex < w; bitIndex++)
            {
                Poly term = bits[0][0] - bits[0][0];
                for (int varIndex = 0; varIndex < vars.Count; varIndex++)
                {
                    term += (1L << (ushort)bitIndex) * bits[varIndex][bitIndex];
                }

                spec += term;
            }

            // Compute groebner basis using msolve
            var ourGb = MsolveWrapper.Run(ideal, null);

            // Linear linearFacts
            var linearTerms = ourGb.Where(x => x.Coeffs.Keys.All(x => x.SortedVars.Count <= 1)).ToList();

            Debugger.Break();

            //SageGb(ideal, linearize: false);




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

            var getOp = (uint index, ref uint totalOrder) =>
            {
                if(index == 0)
                    return GetSpecification(ctx.GetOp0(idx), bitIdx, cache, ideal, firstSeen, ref totalOrder);
                Debug.Assert(index == 1);
                return GetSpecification(ctx.GetOp1(idx), bitIdx, cache, ideal, firstSeen, ref totalOrder);
            };

            var (carryId, arithInfo) = carryIdentifiers[idx];
            if (opc == AstOp.Add)
            {
                if (arithInfo.Count > bitIdx)
                    return arithInfo[bitIdx].result;
                Debug.Assert(arithInfo.Count == bitIdx);
                var a = getOp(0, ref totalOrder);
                var b = getOp(1, ref totalOrder);

                var generate = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}gen");
                update(generate);

                var propagate = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}prop");
                update(propagate);

                var cout = SymVar.Temp(SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}cout");
                update(cout);

                //var sum = SymVar.Temp($"a[{carryId}][{bitIdx}].sum");
                var sum = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"op{carryId}_{bitIdx}sum");
                update(sum);



                //Poly cin = SymVar.Temp($"arith[{carryId}][{bitIdx}].cin");
                //if (bitIdx == 0)
                //    cin = Poly.Constant(0);
                Poly cin = Poly.Constant(0);
                if (bitIdx > 0)
                    cin = arithInfo[bitIdx - 1].cout;

                // I think this encoding is technically more optimal for the linear extraction idea
                /*
                ideal.Add((bitIdx, totalOrder++, generate - a * b));
                ideal.Add((bitIdx, totalOrder++, propagate - (a + b - 2 * generate)));
                ideal.Add((bitIdx, totalOrder++, cout - (generate + propagate * cin)));
                ideal.Add((bitIdx, totalOrder++, sum - (propagate + 2 * generate + cin - 2 * cout)));

                arithInfo.Add(new(cin, cout, sum));
                */

                //var cout = SymVar.Temp($"a[{carryId}][{bitIdx}].cout");


                /*
                var sumLhs = sum;
                var sumRhs = a + b + cin + (-2 * (a * b + b * cin + a * cin)) + 4 * (a * b * cin);

                ideal.Add((bitIdx, totalOrder++, sumLhs - sumRhs));
                */


                /*
                var carryLhs = cout;
                //var carryRhs = a*b + b*cin + a*cin + (-1*(2*a*b*cin));
                var carryRhs = a * b + b * cin + a * cin + (-1 * (2 * a * b * cin));
                ideal.Add((bitIdx, totalOrder++, carryLhs - carryRhs));
                */


                var carryLhs = cout;
                var carryRhs = a * b + a * cin + b * cin - 2 * (a * b * cin);
                ideal.Add((bitIdx, totalOrder++, carryLhs - carryRhs));

                //var member = (2L*cout)+sum-a-b-cin;
                var member = sum - (a + b + cin + (-2 * (cout)));
                //var member = (2L * cout) + sum - a - b - cin;
                ideal.Add((bitIdx, totalOrder, member));

                arithInfo.Add(new(cin, cout, sum));




                totalOrder++;

                cache[key] = sum;

                return sum;
            }

            if (opc == AstOp.And)
            {
                var a = getOp(0, ref totalOrder);
                var b = getOp(1, ref totalOrder);

                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"r{carryId}_{bitIdx}");
                update(y);
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
                update(y);
                ideal.Add((bitIdx, totalOrder, y - (a - b + a*b)));

                totalOrder++;
                cache[key] = y;
                return y;
            }

            if (opc == AstOp.Xor)
            {
                var a = getOp(0, ref totalOrder);
                var b = getOp(1, ref totalOrder);

                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"r{carryId}_{bitIdx}");
                update(y);
                ideal.Add((bitIdx, totalOrder, (y - (a + b - (2 * (a * b))))));

                totalOrder++;
                cache[key] = y;
                return y;
            }

            if (opc == AstOp.Neg)
            {
                var a = getOp(0, ref totalOrder);
                var y = SymVar.Temp(isOutput ? SymKind.Output : SymKind.InternalGate, bitIdx, 0, $"r{carryId}_{bitIdx}");
                update(y);
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

                    if (nextLm.SortedVars.Count == 1)
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


                    Console.WriteLine($"Intermediate product: {next}\n");
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

                    if (lm.SortedVars.Count != 1)
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

                    if (linearize && monomial.SortedVars.Count > 1 && !linMap.ContainsKey(monomial))
                    {
                        linMap[monomial] = $"lin{linCounter++}";
                    }
                }
            }

            varOrder.Sort();
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
            sb.AppendLine("    order='degrevlex'");
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

                foreach (var (monomial, rawCoeff) in poly.Coeffs.OrderByDescending(x => x.Key))
                {
                    var coeff = rawCoeff & mask;
                    if (coeff == 0)
                        continue;



                    if (monomial.SortedVars.Count == 0)
                    {
                        terms.Add(coeff.ToString());
                    }
                    else if (linearize && monomial.SortedVars.Count > 1 && !(skipAND && poly.Lm.SortedVars[0].Name.StartsWith("r0_")) && linMap.TryGetValue(monomial, out var linName))
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
                            if (m.SortedVars.Count == 1)
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
                                Debug.Assert(monomial.SortedVars.Count == 1, $"Gate variable {gate} appears in higher-degree monomial {monomial}");
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
