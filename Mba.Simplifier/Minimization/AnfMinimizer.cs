using Mba.Ast;
using Mba.Common.MSiMBA;
using Mba.Common.Utility;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    public class AnfMinimizer
    {
        private readonly AstCtx ctx;

        private readonly IReadOnlyList<AstIdx> variables;

        private readonly BooleanTruthTable truthTable;

        private readonly Dictionary<AstIdx, uint> demandedVarsMap = new();

        // Simplify the boolean expression as a 1-bit polynomial.
        // When the ground truth contains many XORs, this yields exponentially more compact results than DNF.
        // TODO: The result can be refined through factoring and other means.
        public static unsafe AstIdx SimplifyBoolean(AstCtx ctx, IReadOnlyList<AstIdx> variables, BooleanTruthTable truthTable)
            => new AnfMinimizer(ctx, variables, truthTable).SimplifyBoolean();

        private AnfMinimizer(AstCtx ctx, IReadOnlyList<AstIdx> variables, BooleanTruthTable truthTable)
        {
            this.ctx = ctx;
            this.variables = variables;
            this.truthTable = truthTable;
        }

        private unsafe AstIdx SimplifyBoolean()
        {
            // If the truth table has a positive constant offset, negate the result vector.
            bool negated = truthTable.GetBit(0);
            var resultVec = truthTable.AsList().Select(x => negated ? Negate((int)x) : (uint)x).ToArray();
            var variableCombinations = MultibitSiMBA.GetVariableCombinations(variables.Count);

            // Keep track of which variables are demanded by which combination,
            // as well as which result vector idx corresponds to which combination.
            var groupSizes = MultibitSiMBA.GetGroupSizes(variables.Count);
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var comb = variableCombinations[i];
                var myIndex = MultibitSiMBA.GetGroupSizeIndex(groupSizes, comb);
                combToMaskAndIdx.Add((comb, (int)myIndex));
            }

            var varCount = variables.Count;
            bool onlyOneVar = varCount == 1;
            int width = (int)(varCount == 1 ? 1 : 2u << (ushort)(varCount - 1));
            List<int> terms = new();
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
                    terms.Add(i);
                }
            }

            AstIdx? result = null;
            foreach (var term in terms)
            {
                var conj = LinearSimplifier.ConjunctionFromVarMask(ctx, variables, 1, variableCombinations[term], null);
                if (result == null)
                    result = conj;
                else
                    result = ctx.Xor(result.Value, conj);
            }

            // Leave the new minimization algorithm disabled by default. 
            // It should return substantially better results for high variable counts, but it's not well tested (yet).
            bool newMinimizationAlgo = true;
            if (!newMinimizationAlgo)
                return negated ? ctx.Neg(result.Value) : result.Value;

            // Set the initial demanded variable masks.
            for (int i = 0; i < variables.Count; i++)
            {
                var mask = 1u << i;
                var var = variables[i];
                demandedVarsMap.Add(var, mask);
            }

            // Yield a XOR of factored variable conjunctions
            // e.g. e ^ (a&(b&c))
            var factored = Factor(ctx, variables, terms.Select(x => (uint)variableCombinations[x]).ToList(), demandedVarsMap);

            // TODO: Apply the identify a^(~a&b) => a|b
            var simplified = SimplifyRec(factored.Value);

            // The results are somewhat improved by running the simplifier a few times, but we don't want to pay this cost for now.
            /*
            simplified = SimplifyRec(factored.Value);
            for (int i = 0; i < 3; i++)
            {
                simplified = SimplifyRec(simplified);
                simplified = ctx.RecursiveSimplify(simplified);
            }
            */

            return negated ? ctx.Neg(simplified) : simplified;
        }

        private ulong Negate(int x)
        {
            return (uint)((~x) & 1);
        }

        // Apply greedy factoring over a sum of variable conjunctions
        public static AstIdx? Factor(AstCtx ctx, IReadOnlyList<AstIdx> variables, List<uint> conjs, Dictionary<AstIdx, uint> demandedVarsMap)
        {
            var getConjFromMask = (uint mask) => LinearSimplifier.ConjunctionFromVarMask(ctx, variables, 1, mask, null);

            // Remove the constant term if it exists
            bool has = conjs.Remove(uint.MaxValue);

            var variableCounts = new (int, uint)[variables.Count];
            // Collect the number of times we encounter each variable.
            foreach (var conj in conjs)
            {
                for (int i = 0; i < variables.Count; i++)
                {
                    var mask = (uint)1 << i;
                    if ((conj & mask) != 0)
                        variableCounts[i] = (i, variableCounts[i].Item2 + 1);
                }
            }

            // Order the variables by the number of times they appear.
            Array.Sort(variableCounts, (a, b) => b.Item2.CompareTo(a.Item2));

            // For each conjunction, we take out the leading factor.
            var groups = new Dictionary<int, List<uint>>();
            foreach (var conj in conjs)
            {
                for (int index = 0; index < variableCounts.Length; index++)
                {
                    var i = variableCounts[index].Item1;

                    var mask = (uint)1 << i;
                    if ((conj & mask) != 0)
                    {
                        var newConj = conj & ~mask;
                        if (!groups.ContainsKey(i))
                            groups[i] = new List<uint>();

                        if (newConj != 0)
                            groups[i].Add(newConj);
                        else
                            groups[i].Add(uint.MaxValue);

                        break;
                    }
                }
            }

            // Recursively factor each group.
            var output = new List<AstIdx>();
            foreach (var (varIdx, elems) in groups)
            {
                AstIdx result = variables[varIdx];
                // If we have just 1 a single variable, yield it.
                if (elems.Count == 0 || (elems.Count == 1 && elems[0] == uint.MaxValue))
                {
                    output.Add(result); // In this case we already know the demanded mask
                    continue;
                }
                // If we have 1 variable by another conjunction, yield it.
                else if (elems.Count == 1)
                {
                    var mask = elems[0];
                    var conj = ctx.And(result, getConjFromMask(mask));
                    output.Add(conj);

                    mask |= 1u << varIdx;
                    demandedVarsMap.TryAdd(conj, mask);
                    continue;
                }

                // Otherwise recursively factor
                var other = Factor(ctx, variables, elems, demandedVarsMap);
                var and = ctx.And(result, other.Value);
                output.Add(and);

                // Update the demanded mask.
                var demanded = (1u << varIdx) | demandedVarsMap[other.Value];
                demandedVarsMap.TryAdd(and, demanded);
            }

            // Compute the union of all demanded variables.
            var demandedSum = 0u;
            foreach (var id in output)
                demandedSum |= demandedVarsMap[id];

            // Compute the XOR of all the terms.
            var xored = ctx.Xor(output);
            demandedVarsMap.TryAdd(xored, demandedSum);

            // If we have a constant offset of one, add it back.
            if (has)
            {
                xored = ctx.Xor(ctx.Constant(ulong.MaxValue, ctx.GetWidth(variables[0])), xored);
                demandedVarsMap.TryAdd(xored, demandedSum);
            }

            return xored;
        }

        private AstIdx SimplifyRec(AstIdx id)
        {
            var kind = ctx.GetOpcode(id);
            if (kind == AstOp.Symbol)
                return id;
            if (kind == AstOp.Constant)
                return id;
            if (kind == AstOp.Neg)
                return ctx.Neg(SimplifyRec(ctx.GetOp0(id)));

            // If we have 4 or less variables, pull the optimal representation from the truth table.
            var currMask = GetDemandedVarsMask(id);
            var count = BitOperations.PopCount(currMask);
            if (count == 1)
                return id;
            if (count <= 4)
                return SimplifyViaLookupTable(id, currMask);

            // Otherwise we cannot use a lookup table. 
            // In this case we want to check if we can decompose the boolean into terms with disjoint variable sets.
            var worklist = new Stack<AstIdx>();
            worklist.Push(id);

            // First recursively hoist all associative terms.
            // TODO: Rewrite negations as XORs, then normalize after the fact.
            var terms = new List<AstIdx>();
            while (worklist.Any())
            {
                var current = worklist.Pop();
                if (ctx.GetOpcode(current) != kind)
                {
                    terms.Add(current);
                    continue;
                }

                var a = ctx.GetOp0(current);
                var b = ctx.GetOp1(current);

                var visit = (AstIdx idx) =>
                {
                    // Skip if this node is not of the same kind.
                    var opcode = ctx.GetOpcode(idx);
                    if (opcode != kind)
                    {
                        terms.Add(idx);
                        return;
                    }

                    // Otherwise we want to visit its children.
                    worklist.Push(ctx.GetOp0(idx));
                    worklist.Push(ctx.GetOp1(idx));
                };

                visit(a);
                visit(b);
            }

            Debug.Assert(terms.All(x => ctx.GetOpcode(x) != kind));

            // Do a disjoint variable decomposition. We can start from the least common variables and work our way up.
            var decompositions = new List<(uint, AstIdx)>();
            foreach (var term in terms)
            {
                var demandedMask = GetDemandedVarsMask(term);

                // Try to find the any fit. TODO: We could come up with a better heuristic approach for variable partitioning.
                bool found = false;
                for (int i = 0; i < decompositions.Count; i++)
                {
                    // Union the demanded mask and check if we can fit it in anywhere.
                    var old = decompositions[i];
                    var (oldMask, oldId) = (old.Item1, old.Item2);
                    var sum = oldMask | demandedMask;
                    if (BitOperations.PopCount(sum) <= 4)
                    {
                        var newId = ctx.Binop(kind, oldId, term);
                        decompositions[i] = (sum, newId);
                        found = true;
                        break;
                    }
                }

                // Skip if we found a fit.
                if (found)
                    continue;

                decompositions.Add((demandedMask, term));
            }

            // Recursively simplify each term.
            var simplifiedTerms = decompositions.Select(x => SimplifyRec(x.Item2)).ToList();

            var simplified = ctx.Binop(kind, simplifiedTerms);

            return simplified;
        }

        private uint GetDemandedVarsMask(AstIdx id)
        {
            // If we already know the mask, return it.
            uint mask = 0;
            if (demandedVarsMap.TryGetValue(id, out mask))
                return mask;

            var op0 = () => GetDemandedVarsMask(ctx.GetOp0(id));
            var op1 = () => GetDemandedVarsMask(ctx.GetOp1(id));

            var kind = ctx.GetOpcode(id);
            mask = kind switch
            {
                AstOp.And or AstOp.Or or AstOp.Xor => op0() | op1(),
                AstOp.Neg => op0(),
                AstOp.Constant => 0,
                AstOp.Symbol => 1u << variables.IndexOf(id), // N is generally so small (<= 8) that this is fine. 
            };

            demandedVarsMap.TryAdd(id, mask);
            return mask;
        }

        private AstIdx SimplifyViaLookupTable(AstIdx id, uint demandedMask)
        {
            var varSet = new List<AstIdx>();
            for (int i = 0; i < variables.Count; i++)
            {
                if ((demandedMask & (1u << i)) != 0)
                    varSet.Add(variables[i]);
            }

            // Build a result vector for the millionth time..
            var w = ctx.GetWidth(id);
            var rv = LinearSimplifier.JitResultVector(ctx, 1, 1, varSet, id, false, (ulong)Math.Pow(2, varSet.Count));

            var table = new BooleanTruthTable(varSet.Count);
            for (int i = 0; i < rv.Length; i++)
                table.SetBit(i, rv[i] != 0);

            return BooleanMinimizer.FromTruthTable(ctx, varSet, table);
        }
    }
}