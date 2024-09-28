using Mba.Ast;
using Mba.Common.MSiMBA;
using Mba.Common.Utility;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    public static class AnfMinimizer
    {
        // Simplify the boolean expression as a 1-bit polynomial.
        // When the ground truth contains many XORs, this yields exponentially more compact results than DNF.
        // TODO: The result can be refined through factoring and other means.
        public static unsafe AstIdx SimplifyBoolean(AstCtx ctx, IReadOnlyList<AstIdx> variables, List<int> resultVector)
        {
            var resultVec = resultVector.Select(x => (ulong)x).ToArray();
            var variableCombinations = MultibitSiMBA.GetVariableCombinations(variables.Count);

            // Keep track of which variables are demanded by which combination,
            // as well as which result vector idx corresponds to which combination.
            var groupSizes = MultibitSiMBA.GetGroupSizes(variables.Count);
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var myMask = variableCombinations[i];
                var myIndex = MultibitSiMBA.GetGroupSizeIndex(groupSizes, myMask);
                combToMaskAndIdx.Add((myMask, (int)myIndex));
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
                    result = ctx.Xor(result.Value, conj.Value);
            }

            // Set the initial demanded variable masks.
            var demandedVarsMap = new Dictionary<AstIdx, uint>();
            for (int i = 0; i < variables.Count; i++)
            {
                var mask = 1u << i;
                var var = variables[i];
                demandedVarsMap.Add(var, mask);
            }

            var other = Factor(ctx, variables, terms.Select(x => (uint)variableCombinations[x]).ToList(), demandedVarsMap);

            // var min = ctx.RecursiveSimplify(other.Value);
            // min = ctx.RecursiveSimplify(other.Value);
            // min = ctx.RecursiveSimplify(other.Value);

            return result.Value;
        }

        private static AstIdx? Factor(AstCtx ctx, IReadOnlyList<AstIdx> variables, List<uint> conjs, Dictionary<AstIdx, uint> demandedVarsMap)
        {
            var getConjFromMask = (uint mask) => LinearSimplifier.ConjunctionFromVarMask(ctx, variables, 1, mask, null);

            // Remove the constant term if it exists
            bool has = conjs.Remove(uint.MaxValue);

            var variableCounts = new (int, uint)[variables.Count];
            // Collect the number of times we encounter each variable.
            foreach(var conj in conjs)
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
            foreach(var conj in conjs)
            {
                for(int index = 0; index < variableCounts.Length; index++)
                {
                    var i = variableCounts[index].Item1;

                    var mask = (uint)1 << i;
                    if ((conj & mask) != 0)
                    {
                        var newConj = conj & ~mask;
                        if (!groups.ContainsKey(i))
                            groups[i] = new List<uint>();

                        if(newConj != 0)
                            groups[i].Add(newConj);
                        else
                            groups[i].Add(uint.MaxValue);

                        break;
                    }
                }
            }

            var output = new List<AstIdx>();
            foreach(var (varIdx, elems) in groups)
            {
                AstIdx result = variables[varIdx];
                // If we have just 1 a single variable, yield it.
                if(elems.Count == 0 || (elems.Count == 1 && elems[0] == uint.MaxValue))
                {
                    output.Add(result); // In this case we already know the demanded mask
                    continue;
                }
                // If we have 1 variable by another conjunction, yield it.
                else if(elems.Count == 1)
                {
                    var mask = elems[0];
                    var conj = ctx.And(result, getConjFromMask(mask).Value);
                    output.Add(conj);

                    mask |= 1u << varIdx;
                    demandedVarsMap.TryAdd(conj, mask);
                    continue;
                }

                // Otherwise recurisvely factor
                var other = Factor(ctx, variables, elems, demandedVarsMap);
                var and = ctx.And(result, other.Value);
                output.Add(and);

                // Update the demanded mask.
                var demanded = (1u << varIdx) | demandedVarsMap[other.Value];
                demandedVarsMap.TryAdd(and, demanded);
            }

            // Compute the union of all of the demanded variables.
            var demandedSum = 0u;
            foreach (var id in output)
                demandedSum |= demandedVarsMap[id];
            
            // Compute the XOR of all the terms.
            var xored = ctx.Xor(output);
            demandedVarsMap.TryAdd(xored, demandedSum);

            // If we have a constant offset of one, add it back.
            if (has)
            {
                xored = ctx.Neg(xored);
                demandedVarsMap.TryAdd(xored, demandedSum);
            }

            return xored;
        }
    }
}
