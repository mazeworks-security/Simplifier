using Mba.Simplifier.Bindings;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.InteropServices.Marshalling;
using System.Runtime.Intrinsics.X86;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Wintellect.PowerCollections;

namespace Mba.Simplifier.Minimization
{
    public class AnfMinimizerV2
    {
        private readonly AstCtx ctx;

        private readonly uint width;

        private readonly int[] mutVarCounts;

        Dictionary<BoolPoly, AstIdx?> cache = new();

        public static unsafe AstIdx SimplifyBoolean(AstCtx ctx, IReadOnlyList<AstIdx> variables, BoolPoly truthTable)
            => new AnfMinimizerV2(ctx, variables).SimplifyBoolean(variables.ToArray(), truthTable);

        private AnfMinimizerV2(AstCtx ctx, IReadOnlyList<AstIdx> variables)
        {
            this.ctx = ctx;
            this.width = ctx.GetWidth(variables[0]);
            mutVarCounts = new int[variables.Count];
        }

        private AstIdx SimplifyBoolean(AstIdx[] variables, BoolPoly boolPoly)
        {
            // Change boolean to algebraic normal form
            boolPoly.ChangeBasis();

            // Sifting implementation seems to hurt for multi-bit booleans..
            bool sift = boolPoly.bitWidth == 1;
            var (negMask, constOffset) = sift ? boolPoly.Sift() : (0u, 0ul);

            // If 1-bit, the constant offset needs to be extended.
            if (boolPoly.bitWidth == 1 && constOffset != 0)
                constOffset = ulong.MaxValue;

            // Update the variable
            var negatedVariables = variables.ToArray();
            for (int i = 0; i < variables.Length; i++)
            {
                var isNeg = (negMask & (1u << (ushort)i)) != 0;
                if (isNeg)
                    negatedVariables[i] = Neg(negatedVariables[i]);
            }

            var r = SimplifyRec(boolPoly, 64, new PackedList<AstIdx>(negatedVariables, (uint)ModuloReducer.GetMask((uint)negatedVariables.Length)));

            // Append the constant offset
            if (constOffset != 0)
                r = Add(ctx.Constant(constOffset, width), r);

            r = ctx.RecursiveSimplify(r);

            // Revert changes to boolpoly
            boolPoly.ChangeBasis();
            return r;
        }

        private AstIdx SimplifyRec(BoolPoly boolPoly, uint fuel, PackedList<AstIdx> negatedVariables)
        {
            // Return the result if we've already encountered this boolean
            ref var slot = ref CollectionsMarshal.GetValueRefOrAddDefault(cache, boolPoly, out var exists);
            if (exists && slot != null)
                return slot.Value;

            // Return early if the boolean polynomial is a constant
            boolPoly.GetVariableCounts(mutVarCounts);
            var activeMask = GetActiveVarMask(mutVarCounts);
            var asConstant = TrySimplifyAsConstant(boolPoly, activeMask);
            if (asConstant != null)
            {
                slot = asConstant.Value;
                return asConstant.Value;
            }

            // Pull the optimal result from a lookup table if N <= 5
            if (BitOperations.PopCount(activeMask) <= 5 && boolPoly.bitWidth == 1)
            {
                var r = SimplifyViaLookupTable(boolPoly, activeMask, negatedVariables);
                slot = r;
                return r;
            }

            // If we have multiple bits, try to express the boolean as c1 + c2*(1_bit_bool)
            var asOneBit = TrySimplifyAs1Bit(boolPoly, fuel, negatedVariables);
            if (asOneBit != null)
            {
                slot = asOneBit.Value;
                return asOneBit.Value;
            }

            // Split the boolean polynomial on the most common variable
            var toRemove = (uint)GetMostCommonVarIdx(mutVarCounts);
            var with = boolPoly.FilterByVar(toRemove, true);
            var without = boolPoly.FilterByVar(toRemove, false);

            // Eliminate the factored variable
            with.EliminateVar(toRemove);
            // Minimize `with`, `without` separately, then compose back into `toRemove*(with) + without`
            var p0 = Mul(negatedVariables.GetAt((int)toRemove), SimplifyRec(with, fuel / 2, negatedVariables));
            var p1 = SimplifyRec(without, fuel / 2, negatedVariables);
            var best = ctx.RecursiveSimplify(Add(p0, p1));
            // Stop exploring alternative solutions if we've reached our limit
            if (fuel == 0)
            {
                slot = best;
                return best;
            }

            // If either side is a constant then we can return early.
            if (ctx.IsConstant(p1) && ctx.GetConstantValue(p1) == 0)
            {
                slot = p0;
                return p0;
            }
            if (ctx.IsConstant(p0) && ctx.GetConstantValue(p0) == 0)
            {
                slot = p1;
                return p1;
            }

            // Try to match one OR pattern
            var singleVar = negatedVariables.GetAt((int)toRemove);
            ProcessCandidate(ref best, TryMatchMergedOr(singleVar, with, without, fuel / 2, negatedVariables));
      
            // Multiply the factored variable back into `with`
            // a + b + ab
            // =>
            // a*(1 + b) 
            // b
            with.MultiplyByVar(toRemove);

            // Try different methods of factoring or decomposing the polynomial (up to some cost bound)
            // and pick the best one at the end.
            var div = BoolPoly.Create(with.numVars, with.bitWidth);
            var rem = BoolPoly.Create(with.numVars, with.bitWidth);

            with.DivRem(without, div, rem);
            ProcessCandidate(ref best, TryMatchProduct(with, without, div, rem, fuel / 2, negatedVariables));
            ProcessCandidate(ref best, TryMatchOr(with, without, div, rem, fuel / 2, negatedVariables));

            without.DivRem(with, div, rem);
            ProcessCandidate(ref best, TryMatchProduct(without, with, div, rem, fuel / 2, negatedVariables));

            slot = best;
            return best;
        }

        private static uint GetActiveVarMask(int[] arr)
        {
            uint mask = 0;
            for(int i = 0; i < arr.Length; i++)
            {
                if (arr[i] != 0)
                    mask |= 1u << (ushort)i;
            }
            return mask;
        }

        private static AstIdx[] GetActiveVars(uint activeMask, PackedList<AstIdx> variables)
        {
            var output = new AstIdx[BitOperations.PopCount(activeMask)];
            var count = 0;
            for(int i = 0; i < variables.Length; i++)
            {
                if ((activeMask & (1u << (ushort)i)) == 0)
                    continue;

                output[count++] = variables.GetAt(i);
            }

            return output;
        }

        private AstIdx? TrySimplifyAsConstant(BoolPoly boolPoly, uint activeMask)
        {
            if (activeMask != 0)
                return null;

            // If this is a 1-bit polynomial, the constant offset needs to be extended to N bits
            var constant = boolPoly.GetConstantOffset();
            if (constant == 1 && boolPoly.bitWidth == 1)
                constant = ulong.MaxValue;

            var r = ctx.Constant(constant, width);
            return r;
        }

        // Pull the optimal representation from a lookup table
        private AstIdx SimplifyViaLookupTable(BoolPoly boolPoly, uint activeMask, PackedList<AstIdx> negatedVariables)
        {
            var elim = boolPoly.RemoveVars(~activeMask & (uint)ModuloReducer.GetMask((uint)negatedVariables.Length));

            elim.ChangeBasis();
            var table = elim.GetRowTable(0);
            elim.ChangeBasis();

            var activeVars = GetActiveVars(activeMask, negatedVariables);

            AstIdx r = 0;
            if (BitOperations.PopCount(activeMask) == 5)
            {
                var optTable = BooleanMinimizer.AppendVariables((uint)table.Arr[0], (uint)activeVars.Length, 5 - (uint)activeVars.Length);
                r = BooleanMinimizer.GetOptimalNpnCircuit(ctx, activeVars.ToList(), optTable);
            }
            else
            {
                var vi = BitOperations.TrailingZeroCount(activeMask);
                if (activeVars.Length == 1)
                    r = table.GetBit(0) == false ? negatedVariables.GetAt(vi) : ctx.Neg(negatedVariables.GetAt(vi));
                else
                    r = BooleanMinimizer.FromTruthTable(ctx, activeVars.ToList(), table);
            }

            return r;
        }

        // If we have multiple bits, try to express the boolean as c1 + c2*(1_bit_bool)
        private AstIdx? TrySimplifyAs1Bit(BoolPoly boolPoly, uint fuel, PackedList<AstIdx> negatedVariables)
        {
            if (boolPoly.bitWidth == 1)
                return null;

            var maybeRed = boolPoly.TryReduceTo1Bit();
            if (maybeRed == null)
                return null;
            
            var red = maybeRed.Value;
            var r = SimplifyRec(red.table, fuel + 4, negatedVariables);
            r = Mul(ctx.Constant(red.coefficient, width), r);
            r = Add(ctx.Constant(red.constantOffset, width), r);
            return r;
        }

        private static int GetMostCommonVarIdx(int[] varCounts)
        {
            int bestIdx = 0;
            for(int i = 0; i < varCounts.Length; i++)
            {
                if (varCounts[i] > varCounts[bestIdx])
                    bestIdx = i;
            }

            return bestIdx;
        }

        // Given a+b:
        //  div, rem = DivRem(a,b)
        // return (div+1)*b + rem
        private AstIdx TryMatchProduct(BoolPoly a, BoolPoly b, BoolPoly div, BoolPoly rem, uint fuel, PackedList<AstIdx> negatedVariables)
        {
            var divPlusOne = Neg(SimplifyRec(div, fuel / 2, negatedVariables));
            // to = div+1
            var bIdx = SimplifyRec(b, fuel / 2, negatedVariables);
            // t2 = (div+1)*b + 1
            var p0 = Mul(divPlusOne, bIdx);
            var p1 = SimplifyRec(rem, fuel, negatedVariables);
            var result = Add(p0, p1);
            return result;
        }

        // Pattern match (a+1)*b + a => a|b
        private AstIdx? TryMatchOr(BoolPoly a, BoolPoly b, BoolPoly div, BoolPoly rem, uint fuel, PackedList<AstIdx> negatedVariables)
        {
            if (div.IsEqual(rem))
            {
                var a0 = SimplifyRec(div, fuel / 2, negatedVariables);
                var b0 = SimplifyRec(b, fuel / 2, negatedVariables);
                return ctx.Or(a0, b0);
            }

            var cond0 = a.IsOr(b, div);
            if (cond0)
            {
                var a0 = SimplifyRec(div, fuel / 2, negatedVariables);
                var b0 = SimplifyRec(b, fuel / 2, negatedVariables);
                return ctx.Or(a0, b0);
            }

            return null;
        }

        // Given (a&b) ^ c, try to decompose into `(a&b)^b^c`, then simplify to `c^~(a|~b)`
        // `c` can be an arbitrary liner combination
        private AstIdx? TryMatchMergedOr(AstIdx a0, BoolPoly b, BoolPoly c, uint fuel, PackedList<AstIdx> negatedVariables)
        {
            var b0 = SimplifyRec(b, fuel / 2, negatedVariables);
            var product = Neg(ctx.Or(a0, Neg(b0)));

            var diff = b;
            diff.Xor(c);
            var r = Add(SimplifyRec(diff, fuel / 2, negatedVariables), product);
            // Undo the XOR
            diff.Xor(c);

            return r;
        }

        private void ProcessCandidate(ref AstIdx best, AstIdx? candidate)
        {
            if (candidate == null)
                return;

            candidate = ctx.RecursiveSimplify(candidate.Value);
            candidate = ctx.RecursiveSimplify(candidate.Value);
            candidate = ctx.RecursiveSimplify(candidate.Value);

            if (ctx.GetCost(candidate.Value) < ctx.GetCost(best))
                best = candidate.Value;
        }

        private AstIdx Add(AstIdx a, AstIdx b)
        {
            return ctx.Xor(a, b);
        }

        private AstIdx Mul(AstIdx a, AstIdx b)
        {
            return ctx.And(a, b);
        }

        private AstIdx Neg(AstIdx a)
        {
            return ctx.Neg(a);
        }
    }

    // Represents a list of N elements where elements can be removed while preserving their order 
    public unsafe struct PackedList<T>
    {
        private readonly T[] elems;

        public uint mask;

        public int Length => BitOperations.PopCount(mask);

        public PackedList(T[] elems, uint mask)
        {
            this.elems = elems;
            this.mask = mask;
        }

        public T GetAt(int logicalIdx)
        {
            ulong vMask = Bmi2.ParallelBitDeposit(1u << logicalIdx, mask);
            int arrIdx = BitOperations.TrailingZeroCount(vMask);
            return elems[arrIdx];
        }

        public uint RemoveAt(int logicalIdx)
        {
            ulong vMask = Bmi2.ParallelBitDeposit(1u << logicalIdx, mask);
            return (uint)(mask & ~vMask);
        }
    }
}
