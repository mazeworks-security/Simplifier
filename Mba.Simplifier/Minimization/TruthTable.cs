using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    public struct TruthTable
    {
        private readonly int numVars;

        public int NumBits => 1 << (ushort)numVars;

        public readonly ulong[] arr;

        public TruthTable(int numVars)
        {
            if (numVars == 127)
                Debugger.Break();


            this.numVars = numVars;
            int width = NumBits <= 64 ? 1 : (NumBits >> 6);
            arr = new ulong[width];
        }

        public bool GetBit(int index)
        {
            var wordIdx = index >> 6;
            var bitIdx = index - (64 * wordIdx);
            return Convert.ToBoolean(1 & (arr[wordIdx] >> (ushort)bitIdx));
        }

        public void SetBit(int index, bool bitVal)
        {
            var word = index >> 6;
            var bitIdx = index - (64 * word);

            var val = Convert.ToUInt64(bitVal);
            arr[word] &= ~(1ul << bitIdx);
            arr[word] |= (val << bitIdx);
        }

        public void Negate()
        {
            for (int i = 0; i < NumBits; i++)
                SetBit(i, GetBit(i) ? false : true);
        }

        public void SetAllZeroes()
        {
            for (int i = 0; i < arr.Length; i++)
                arr[i] = 0;
        }

        public override int GetHashCode()
        {
            int hash = 17;
            foreach(var value in arr)
            {
                hash = hash * 23 + value.GetHashCode();
            }

            return hash;
        }

        public override bool Equals([NotNullWhen(true)] object? obj)
        {
            if(obj is not TruthTable table)
                return false;

            if (numVars != table.numVars)
                return false;

            for(int i = 0; i < arr.Length; i++)
            {
                if (arr[i] != table.arr[i])
                    return false;
            }

            return true;
        }

        public List<int> AsList()
        {
            var vec = new List<int>();
            for (ushort i = 0; i < (ushort)NumBits; i++)
            {
                var value = GetBit(i);
                if (value)
                    vec.Add(1);
                else
                    vec.Add(0);
            }

            return vec;
        }
    }
}
