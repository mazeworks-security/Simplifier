using Mba.Simplifier.Minimization;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Bindings
{
    public struct OpaqueBoolPoly { }

    // This class represents a word-level boolean polynomial
    // E.g. "111&a ^ 222&b ^ 333&a&b"
    public class BoolPoly : IEquatable<BoolPoly>
    {
        private readonly nint handle;

        public readonly byte numVars;

        public readonly byte bitWidth;

        public int NumCombinations => 1 << (ushort)numVars;

        public int NumWords => NumCombinations <= 64 ? 1 : (NumCombinations >> 6);

        public static unsafe BoolPoly Create(byte numVars, byte bitWidth)
            => new BoolPoly(numVars, bitWidth, Api.CreateBoolPoly(numVars, bitWidth));

        public static unsafe BoolPoly Create(byte numVars, byte bitWidth, ulong[] vector)
        {
            fixed (ulong* ptr = vector)
            {
                return new BoolPoly(numVars, bitWidth, Api.CreateBoolPolyFromVec(numVars, bitWidth, ptr));
            }
        }

        public static unsafe BoolPoly CreateFromVariable(byte numVars, byte bitWidth, uint varIdx)
        {
            return new BoolPoly(numVars, bitWidth, Api.CreateBoolPolyFromVariable(numVars, bitWidth, varIdx));
        }

        private unsafe BoolPoly(byte numVars, byte bitWidth, OpaqueBoolPoly* ptr)
        {
            handle = (nint)ptr;
            this.numVars = numVars;
            this.bitWidth = bitWidth;
        }

        unsafe ~BoolPoly()
        {
            Api.FreeBoolPoly(numVars, this);
        }

        public unsafe void And(BoolPoly other)
            => Api.BoolPolyAnd(numVars, this, other);

        public unsafe void Or(BoolPoly other)
            => Api.BoolPolyOr(numVars, this, other);

        public unsafe void Xor(BoolPoly other)
            => Api.BoolPolyXor(numVars, this, other);

        public unsafe void Not()
            => Api.BoolPolyNot(numVars, this);

        public unsafe void Mul(BoolPoly other)
        {
            ChangeBasis();
            other.ChangeBasis();
            And(other);
            other.ChangeBasis();
            ChangeBasis();
        }

        public unsafe void DivRem(BoolPoly other, BoolPoly div, BoolPoly rem)
            => Api.BoolPolyDivRem(numVars, this, other, div, rem);

        public unsafe bool IsEqual(BoolPoly other)
            => Api.BoolPolyEquals(numVars, this, other) != 0;

        public unsafe bool IsOr(BoolPoly b, BoolPoly c)
            => Api.BoolPolyIsOr(numVars, this, b, c) != 0;

        public unsafe ulong GetConstantOffset()
            => Api.BoolPolyGetConstantOffset(numVars, this);

        public unsafe ulong GetHash()
            => Api.BoolPolyGetHash(numVars, this);

        public unsafe Span<ulong> GetRow(int idx)
        {
            var ptr = Api.BoolPolyGetRow(numVars, this, (uint)idx);
            return new Span<ulong>(ptr, NumWords);
        }

        public unsafe BooleanTruthTable GetRowTable(int idx)
        {
            var ptr = Api.BoolPolyGetRow(numVars, this, (uint)idx);
            var arr = new Span<ulong>(ptr, NumWords).ToArray();
            var table = new BooleanTruthTable(numVars);
            table.Arr = arr;
            return table;
        }

        public unsafe (BoolPoly table, ulong constantOffset, ulong coefficient)? TryReduceTo1Bit()
        {
            OpaqueBoolPoly* pTable;
            ulong constantOffset = 0;
            ulong coefficient = 0;
            if (Api.BoolPolyTryReduceTo1Bit(numVars, this, &pTable, &constantOffset, &coefficient) == 0)
                return null;

            var table = new BoolPoly(numVars, 1, pTable);
            return (table, constantOffset, coefficient);
        }

        public unsafe void GetVariableCounts(int[] arr)
        {
            fixed(int* ptr = &arr[0])
            {
                Api.BoolPolyGetVariableCounts(numVars, this, ptr);
            }
        }

        // Return a new polynomial containing only the monomials with or without the selected variable,
        // with that variable removed from the monomial basis.
        public unsafe BoolPoly FilterByVar(uint varIndex, bool contains)
        {
            var ptr = Api.BoolPolyFilterByVar(numVars, this, varIndex, contains ? (byte)1 : (byte)0);
            return new BoolPoly((byte)(numVars), bitWidth, ptr);
        }

        // Eliminate all monomials containing the selected variable
        public unsafe void EliminateVar(uint varIndex)
            => Api.BoolPolyEliminateVar(numVars, this, varIndex);

        // Multiply all monomials by the selected variable
        public unsafe void MultiplyByVar(uint varIndex)
            => Api.BoolPolyMultiplyByVar(numVars, this, varIndex);

        // Return a new polynomial not containing the selected vars
        public unsafe BoolPoly RemoveVars(uint varMask)
            => new BoolPoly((byte)(numVars - (byte)BitOperations.PopCount(varMask)), bitWidth, Api.BoolPolyRemoveVars(numVars, this, varMask));

        public unsafe (uint negMask, ulong constantOffset) Sift()
        {
            uint negMask = 0;
            ulong constantOffset = 0;
            Api.BoolPolySift(numVars, this, &negMask, &constantOffset);
            return (negMask, constantOffset);
        }

        public override string ToString()
        {
            return ToString(constOffset: true);
        }

        public string ToString(bool constOffset = true)
        {
            var masks = new ulong[NumCombinations];
            for (ushort bitIdx = 0; bitIdx < bitWidth; bitIdx++)
            {
                var row = GetRow(bitIdx);
                var table = new BooleanTruthTable(numVars);
                table.Arr = row.ToArray();

                for (int i = 0; i < table.NumCombinations; i++)
                {
                    var value = table.GetBit(i) ? 1ul << bitIdx : 0;
                    masks[i] |= value;
                }
            }

            var terms = new List<string>();
            var c = constOffset ? masks[0] : 0;
           
            terms.Add(c.ToString());
            for (int i = 1; i < NumCombinations; i++)
            {
                if (masks[i] == 0)
                    continue;
                var mstr = GetMonomialStr(numVars, (ulong)i);
                terms.Add($"{masks[i].ToString()}*{mstr}");
            }

            return String.Join($" + ", terms);
        }

        private static string GetMonomialStr(int numVars, ulong idx)
        {
            if (idx == 0)
                return "1";

            List<string> vars = new();
            for(ushort i = 0; i < numVars;i++)
            {
                var isNegated = (idx & (1ul << i)) == 0;
                if (isNegated)
                    continue;

                var vName = $"x{i}";
                vars.Add(isNegated ? "~" + vName : vName);
            }

            return String.Join("*", vars);
        }

        // Convert from disjunctive normal form to algebraic normal form
        // Works both ways
        public unsafe void ChangeBasis()
            => Api.BoolPolyChangeBasis(numVars, this);

        public unsafe BoolPoly Clone()
            => new BoolPoly(numVars, bitWidth, Api.BoolPolyClone(numVars, this));

        public override int GetHashCode()
            => (int)(uint)GetHash();

        public override bool Equals(object? obj)
            => obj is BoolPoly other && Equals(other);

        public bool Equals(BoolPoly? other)
            => IsEqual(other);

        public unsafe static implicit operator OpaqueBoolPoly*(BoolPoly ctx) => (OpaqueBoolPoly*)ctx.handle;

        public static class Api
        {
            [DllImport("eq_sat")]
            public unsafe static extern OpaqueBoolPoly* CreateBoolPoly(byte numVars, byte bitWidth);

            [DllImport("eq_sat")]
            public unsafe static extern OpaqueBoolPoly* CreateBoolPolyFromVec(byte numVars, byte bitWidth, ulong* vecPtr);

            [DllImport("eq_sat")]
            public unsafe static extern OpaqueBoolPoly* CreateBoolPolyFromVariable(byte numVars, byte bitWidth, uint varIdx);

            [DllImport("eq_sat")]
            public unsafe static extern void FreeBoolPoly(byte numVars, OpaqueBoolPoly* a);

            [DllImport("eq_sat")]
            public unsafe static extern void BoolPolyAnd(byte numVars, OpaqueBoolPoly* a, OpaqueBoolPoly* b);

            [DllImport("eq_sat")]
            public unsafe static extern void BoolPolyOr(byte numVars, OpaqueBoolPoly* a, OpaqueBoolPoly* b);

            [DllImport("eq_sat")]
            public unsafe static extern void BoolPolyXor(byte numVars, OpaqueBoolPoly* a, OpaqueBoolPoly* b);

            [DllImport("eq_sat")]
            public unsafe static extern void BoolPolyNot(byte numVars, OpaqueBoolPoly* a);

            [DllImport("eq_sat")]
            public unsafe static extern void BoolPolyDivRem(byte numVars, OpaqueBoolPoly* a, OpaqueBoolPoly* b, OpaqueBoolPoly* pDiv, OpaqueBoolPoly* pRem);

            [DllImport("eq_sat")]
            public unsafe static extern void BoolPolyWeakDivRem(byte numVars, OpaqueBoolPoly* a, OpaqueBoolPoly* b, OpaqueBoolPoly** pDiv, OpaqueBoolPoly** pRem);

            [DllImport("eq_sat")]
            public unsafe static extern byte BoolPolyEquals(byte numVars, OpaqueBoolPoly* a, OpaqueBoolPoly* b);

            [DllImport("eq_sat")]
            public unsafe static extern byte BoolPolyIsOr(byte numVars, OpaqueBoolPoly* a, OpaqueBoolPoly* b, OpaqueBoolPoly* c);

            [DllImport("eq_sat")]
            public unsafe static extern ulong BoolPolyGetConstantOffset(byte numVars, OpaqueBoolPoly* a);

            [DllImport("eq_sat")]
            public unsafe static extern ulong BoolPolyGetHash(byte numVars, OpaqueBoolPoly* a);

            [DllImport("eq_sat")]
            public unsafe static extern ulong* BoolPolyGetRow(byte numVars, OpaqueBoolPoly* a, uint index);

            [DllImport("eq_sat")]
            public unsafe static extern byte BoolPolyTryReduceTo1Bit(byte numVars, OpaqueBoolPoly* a, OpaqueBoolPoly** table, ulong* constantOffset, ulong* coefficient);

            [DllImport("eq_sat")]
            public unsafe static extern void BoolPolyChangeBasis(byte numVars, OpaqueBoolPoly* a);

            [DllImport("eq_sat")]
            public unsafe static extern void BoolPolyGetVariableCounts(byte numVars, OpaqueBoolPoly* a, int* vecPtr);

            [DllImport("eq_sat")]
            public unsafe static extern OpaqueBoolPoly* BoolPolyFilterByVar(byte numVars, OpaqueBoolPoly* a, uint varIndex, byte contains);

            [DllImport("eq_sat")]
            public unsafe static extern OpaqueBoolPoly* BoolPolyEliminateVar(byte numVars, OpaqueBoolPoly* a, uint varIndex);

            [DllImport("eq_sat")]
            public unsafe static extern OpaqueBoolPoly* BoolPolyMultiplyByVar(byte numVars, OpaqueBoolPoly* a, uint varIndex);

            [DllImport("eq_sat")]
            public unsafe static extern OpaqueBoolPoly* BoolPolyRemoveVars(byte numVars, OpaqueBoolPoly* a, uint varMask);

            [DllImport("eq_sat")]
            public unsafe static extern byte BoolPolyEliminateDeadVars(byte numVars, OpaqueBoolPoly* a, uint* varMask, OpaqueBoolPoly** output);

            [DllImport("eq_sat")]
            public unsafe static extern void BoolPolySift(byte numVars, OpaqueBoolPoly* a, uint* pNegatedMask, ulong* negatedConstant);

            [DllImport("eq_sat")]
            public unsafe static extern OpaqueBoolPoly* BoolPolyClone(byte numVars, OpaqueBoolPoly* a);
        }
    }
}
