using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Minimization
{
    public interface ITruthTable<T> 
    {
        public int NumVars { get; }

        // Number of unique variable combinations
        public int NumCombinations { get; }

        public int Width { get; }

        public ulong[] Arr { get; }

        public T GetBit(int index);

        public void SetBit(int index, T value);

        public void Or(ITruthTable<T> other);

        public void Clear();

        public bool IsDisjoint(ITruthTable<T> other);

        public ulong AsUlong(T value);

        public List<ulong> AsList()
        {
            var vec = new List<ulong>();
            for (ushort i = 0; i < (ushort)NumCombinations; i++)
            {
                var value = AsUlong(GetBit(i));
                vec.Add(value);
            }

            return vec;
        }
    }

    public struct SlBooleanTruthTable : ITruthTable<ulong>
    {
        public int NumVars { get; }

        public int NumCombinations => 1 << (ushort)NumVars;

        public ulong[] Arr { get; }

        public int Width { get; }

        public SlBooleanTruthTable(int numVars, uint width)
        {
            NumVars = numVars;
            Width = Width;
            int numArrayEntries = NumCombinations;
            Arr = new ulong[numArrayEntries];
        }

        public ulong GetBit(int index)
        {
            return Arr[index];
        }

        public void SetBit(int index, ulong value)
        {
            Arr[index] = value;
        }

        public void Or(ITruthTable<ulong> other)
        {
            throw new NotImplementedException();
        }

        public void Clear()
        {
            throw new NotImplementedException();
        }

        public bool IsDisjoint(ITruthTable<ulong> other)
        {
            throw new NotImplementedException();
        }

        public ulong AsUlong(ulong value)
        {
            return value;
        }
    }

    public struct BooleanTruthTable : ITruthTable<bool>
    {
        public int NumVars { get; }

        public int NumCombinations => 1 << (ushort)NumVars;

        public ulong[] Arr { get; }

        public int Width => 1;

        public BooleanTruthTable(int numVars)
        {
            this.NumVars = numVars;
            int width = NumCombinations <= 64 ? 1 : (NumCombinations >> 6);
            Arr = new ulong[width];
        }

        public bool GetBit(int index)
        {
            var wordIdx = index >> 6;
            var bitIdx = index - (64 * wordIdx);
            return Convert.ToBoolean(1 & (Arr[wordIdx] >> (ushort)bitIdx));
        }

        public void SetBit(int index, bool bitVal)
        {
            var word = index >> 6;
            var bitIdx = index - (64 * word);

            var val = Convert.ToUInt64(bitVal);
            Arr[word] &= ~(1ul << bitIdx);
            Arr[word] |= (val << bitIdx);
        }

        public void Negate()
        {
            for (int i = 0; i < NumCombinations; i++)
                SetBit(i, GetBit(i) ? false : true);
        }

        public void Or(ITruthTable<bool> other)
        {
            for (int i = 0; i < Arr.Length; i++)
                Arr[i] |= other.Arr[i];
        }

        public void Clear()
        {
            for (int i = 0; i < Arr.Length; i++)
                Arr[i] = 0;
        }

        public bool IsDisjoint(ITruthTable<bool> other)
        {
            for (int i = 0; i < Arr.Length; i++)
            {
                if ((Arr[i] & other.Arr[i]) != 0)
                    return false;
            }

            return true;
        }

        public BooleanTruthTable Clone()
        {
            var table = new BooleanTruthTable(NumVars);
            for(int i = 0; i < Arr.Length ; i++)
                table.Arr[i] = Arr[i];
            return table;
        }

        public override int GetHashCode()
        {
            int hash = 17;
            foreach(var value in Arr)
                hash = hash * 23 + value.GetHashCode();
            return hash;
        }

        public override bool Equals([NotNullWhen(true)] object? obj)
        {
            if(obj is not BooleanTruthTable table)
                return false;
            if (NumVars != table.NumVars)
                return false;

            for(int i = 0; i < Arr.Length; i++)
            {
                if (Arr[i] != table.Arr[i])
                    return false;
            }

            return true;
        }

        public List<ulong> AsList()
        {
            var vec = new List<ulong>();
            for (ushort i = 0; i < (ushort)NumCombinations; i++)
            {
                var value = GetBit(i);
                if (value)
                    vec.Add(1);
                else
                    vec.Add(0);
            }

            return vec;
        }

        public int[] AsArray()
        {
            var arr = new int[NumCombinations];
            for (ushort i = 0; i < (ushort)NumCombinations; i++)
            {
                var value = GetBit(i);
                arr[i] = value ? 1 : 0;
            }

            return arr;
        }

        public ulong AsUlong(bool value)
        {
            return value ? 1ul : 0;
        }
    }
}
