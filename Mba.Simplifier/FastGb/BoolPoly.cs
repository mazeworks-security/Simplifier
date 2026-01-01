using Mba.Simplifier.Polynomial;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Numerics;
using System.Reflection;
using System.Runtime.Intrinsics;
using System.Security.Cryptography;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.FastGb
{
    public interface IVector<T, TSelf> : IEquatable<TSelf>  where TSelf: IVector<T, TSelf>
    {
        static abstract int NumVars { get; }

        static abstract int NumBits { get; }

        static abstract int NumWords { get; }

        ulong GetWord(int index);

        void SetWord(int index, ulong value);

        bool IsConstant(ulong value);

        void SetConstant(ulong value);

        bool Eq(TSelf other);

        static abstract TSelf operator +(TSelf left, TSelf right);
        static abstract TSelf operator *(TSelf left, TSelf right);
    }

    public struct U8 : IVector<ulong, U8>
    {
        public Vector64<ulong> Value;

        public static int NumVars => BitOperations.TrailingZeroCount(NumBits);

        public static int NumBits => 8;

        public static int NumWords => NumBits <= 64 ? 1 : (NumBits >> 6);

        public bool Eq(U8 other)
        {
            return Value == other.Value;
        }

        public bool Equals(U8 other)
        {
            return Value == other.Value;
        }

        public ulong GetWord(int index)
        {
            return Value.GetElement(index);
        }

        public bool IsConstant(ulong value)
        {
            return Value == Vector64.Create<ulong>(value);
        }

        public void SetConstant(ulong value)
        {
            Value = Vector64.Create<ulong>(value); 
        }

        public void SetWord(int index, ulong value)
        {
            Value = Value.WithElement(index, value);
        }

        public static U8 operator +(U8 left, U8 right)
        {
            return new() { Value = left.Value ^ right.Value };
        }

        public static U8 operator *(U8 left, U8 right)
        {
            return new() { Value = left.Value & right.Value };
        }


        //public static U4 operator +(U4 left, U4 right) => new U4 { Value = left.Value + right.Value };
    }


    public struct U64 : IVector<ulong, U64>
    {
        public ulong Value;

        public static int NumVars => BitOperations.TrailingZeroCount(NumBits);

        public static int NumBits => 64;

        public static int NumWords => NumBits <= 64 ? 1 : (NumBits >> 6);

        public bool Eq(U64 other)
        {
            return Value == other.Value;
        }

        public bool Equals(U64 other)
        {
            return Value == other.Value;
        }

        public ulong GetWord(int index)
        {
            return Value;
        }

        public bool IsConstant(ulong value)
        {
            return Value == value;
        }

        public void SetConstant(ulong value)
        {
            Value = value;
        }

        public void SetWord(int index, ulong value)
        {
            Value = value;
        }

        public static U64 operator +(U64 left, U64 right)
        {
            return new() { Value = left.Value ^ right.Value };
        }

        public static U64 operator *(U64 left, U64 right)
        {
            return new() { Value = left.Value & right.Value };
        }
    }

    /*
    public struct U64 : IVector<ulong, U64>
    {
        public Vector64<ulong> Value;

        public static int NumVars => BitOperations.TrailingZeroCount(NumBits);

        public static int NumBits => 64;

        public static int NumWords => NumBits <= 64 ? 1 : (NumBits >> 6);

        public bool Eq(U64 other)
        {
            return Value == other.Value;
        }

        public bool Equals(U64 other)
        {
            return Value == other.Value;
        }

        public ulong GetWord(int index)
        {
            return Value.GetElement(index);
        }

        public bool IsConstant(ulong value)
        {
            return Value == Vector64.Create<ulong>(value);
        }

        public void SetConstant(ulong value)
        {
            Value = Vector64.Create<ulong>(value);
        }

        public void SetWord(int index, ulong value)
        {
            Value = Value.WithElement(index, value);
        }

        public static U64 operator +(U64 left, U64 right)
        {
            return new() { Value = left.Value ^ right.Value };
        }

        public static U64 operator *(U64 left, U64 right)
        {
            return new() { Value = left.Value & right.Value };
        }
    }
    */

    /*
    public struct U64 : IVector<Vector64<ulong>, U64>
    {
        public Vector64<ulong> Value;

        public static int NumVars => BitOperations.TrailingZeroCount(NumBits);

        public static int NumBits => 64;

        public static int NumWords => NumBits <= 64 ? 1 : (NumBits >> 6);

        //public static U64 operator +(U64 left, U64 right) => new U64 { Value = left.Value + right.Value };
    }

    public struct U256 : IVector<Vector256<ulong>, U256>
    {
        public Vector256<ulong> Value;

        public static int NumVars => BitOperations.TrailingZeroCount(NumBits);

        public static int NumBits => 256;

        public static int NumWords => NumBits <= 64 ? 1 : (NumBits >> 6);

    }
    */

    // Problem: Monomial needs to have `isOne` field
    // Monomials are created by indices..
    // isOne = varMask == -1
    public struct Monomial<T> : IComparable<Monomial<T>>, IEquatable<Monomial<T>> where T : IVector<ulong, T>
    {
        public static int NumVars => T.NumVars;

        public static int NumBits => T.NumBits;

        public bool isOne;

        public uint mVars;

        public Monomial(uint varMask, bool isOne = false)
        {
            mVars = varMask;
            this.isOne = isOne;
        }

        public override bool Equals([NotNullWhen(true)] object? obj)
        {
            if (obj is Monomial<T> other)
                return Equals(other);
            return false;
        }

        public bool Equals(Monomial<T> other)
        {
            return mVars == other.mVars && IsOne == other.IsOne;
        }

        public override int GetHashCode()
        {
            return isOne.GetHashCode() + 17 * mVars.GetHashCode();
        }

        public bool IsZero => !isOne && mVars == 0;

        public bool IsOne => isOne;

        public int Index => isOne ? 0 : (int)mVars;

        public int Degree => BitOperations.PopCount((uint)mVars);

        public bool IsDivisible(Monomial<T> other)
        {
            if (other.IsOne)
                return true;
            if (IsOne)
                return false;
            return mVars == (mVars | other.mVars);
        }

        public bool IsRelativelyPrime(Monomial<T> other)
        {
            if (mVars == other.mVars)
                return true;
            if (IsOne)
                return true;

            var lcm = mVars | other.mVars;
            return (lcm ^ mVars) == other.mVars;
        }

        public static bool operator ==(Monomial<T> a, Monomial<T> b) => a.Equals(b);
        public static bool operator !=(Monomial<T> a, Monomial<T> b) => !a.Equals(b);

        public static Monomial<T> operator *(Monomial<T> a, Monomial<T> b)
        {
            // a*a == a
            if (a == b)
                return a;

            // 1*b == b
            if (a.IsOne)
                return b;
            
            // a*1 == 1
            if (b.IsOne)
                return a;

            // a*0 == 0 
            if (a.IsZero || b.IsZero)
                return Monomial<T>.Zero();

            return new(a.mVars | b.mVars);
        }

        public static Monomial<T> operator /(Monomial<T> a, Monomial<T> b)
        {
            if (b.IsOne)
                return a;
            if (a == b)
                return One();
            if (!a.IsDivisible(b))
                return Zero();
            return new(a.mVars ^ b.mVars);
        }

        public override string ToString()
        {
            if (IsZero)
                return "0";
            if (IsOne)
                return "1";

            List<string> vNames = new();
            for(int i = 0; i < T.NumVars; i++)
            {
                if ((mVars & (1u << i)) == 0)
                    continue;

                vNames.Add($"x{i}");
            }

            return String.Join($"*", vNames);
        }

        public static Monomial<T> Zero()
           => new Monomial<T>(0);

        public static Monomial<T> One()
            => new Monomial<T>(0, true);

        public int CompareTo(Monomial<T> other)
        {
            var totalA = BitOperations.PopCount(mVars);
            var totalB = BitOperations.PopCount(other.mVars);

            if (totalA > totalB)
                return 1;
            if (totalB > totalA)
                return -1;

            if (mVars > other.mVars)
                return 1;
            if (mVars < other.mVars)
                return -1;

            // Otherwise total degree and integer is identical..
            return 0;
        }
    }

    // Dense truth table in algebraic normal form
    public class BoolPoly<T> : IComparable<BoolPoly<T>> where T : IVector<ulong, T>, IEquatable<T>
    {
        public T value;

        private Monomial<T> cachedLm = new(uint.MaxValue);

        public IEnumerable<Monomial<T>> Monomials => GetMonomials();

        public int NumBits => T.NumBits;

        // Only exists for the debugger view, because I hate expanding enumerators
        public List<Monomial<T>> MList => GetMonomials().ToList();

        public Monomial<T> Lm
        {
            get
            {
                return cachedLm;

                var computed = GetLm();
                if (computed != cachedLm)
                    throw new InvalidOperationException("Cache not maintianed!");
                return cachedLm;
            }
        }

        public BoolPoly()
        {
            
        }

        public BoolPoly(T value)
        {
            this.value = value;
        }

        public void UpdateLm()
        {
            cachedLm = GetLm();
        }

        private Monomial<T> GetLm()
        {
            var index = (uint)LeadingZeroCount();
            var nb = T.NumBits;
            if (nb < 64)
                index -= (uint)(64 - nb);

            if (index >= nb)
                return Monomial<T>.Zero();

            var invIndex = (uint)-(index - (nb - 1));

            Monomial<T> inv = new(invIndex);
            //return (index - (nb - 1)


            return index >= nb ? Monomial<T>.Zero() : inv;
        }

        public Monomial<T> GetTm()
        {
            var index = (uint)TrailingZeroCount();
            var nb = T.NumBits;
            if (index >= nb)
                return Monomial<T>.Zero();

            return new Monomial<T>(index, index == 0);
        }

        public bool IsZero()
            => value.IsConstant(0);

        public bool IsOne()
            => GetBit(0).IsOne && value.IsConstant(1);

        //public void SetZero() => value.SetConstant(0);
        // 0th bit indicates whether the polynomial has a constant offset
        //public void SetOne() => value.SetConstant(1);

        public int PopCount()
        {
            return BitOperations.PopCount(value.GetWord(0));
        }

        public int GetDegree()
        {
            int max = 0;
            var word = value.GetWord(0);
            for(int i = 0; i < 64; i++)
            {
                var v = 1 & (word >> (ushort)i);
                if (v == 0)
                    continue;

                max = Math.Max(max, BitOperations.PopCount((uint)i));
            }
            return max;
        }

        private int TrailingZeroCount()
        {
            return BitOperations.TrailingZeroCount(value.GetWord(0));

            for (int i = 0; i < T.NumWords; i++)
            {
                var word = value.GetWord(i);
                var tzcnt = BitOperations.TrailingZeroCount(word);
                if (tzcnt != 0)
                {
                    return (64 * i) + tzcnt;
                }
            }

            return T.NumBits;
        }

        private int LeadingZeroCount()
        {
            return BitOperations.LeadingZeroCount(value.GetWord(0));

            /*
            for (int i = T.NumWords - 1; i >= 0; i--)
            {
                var word = value.GetWord(i);
                var lzcnt = BitOperations.LeadingZeroCount(word);
                if (lzcnt == 0)
                {
                    return (64 * i) + lzcnt;
                }
            }

            return T.NumBits;
            */

            for (int i = T.NumWords - 1; i >= 0; i--)
            {
                var word = value.GetWord(i);
                if (word != 0)
                {
                    var lzcnt = BitOperations.LeadingZeroCount(word);
                    // Account for all the zero words above this one
                    return ((T.NumWords - 1 - i) * 64) + lzcnt;
                }
            }

            return T.NumBits;
        }

        private IEnumerable<Monomial<T>> GetMonomials()
        {
            /*
            for(int wordIdx = 0;  wordIdx < T.NumWords; wordIdx++)
            {
                var word = value.GetWord(wordIdx);
                for(int i = 0; i < T.NumBits; i++)
                {
                    var bit = (1 & (word >> i));
                    if (bit == 0)
                        continue;

                    // If the 0th bit is demanded, we have a 1.
                    if (wordIdx == 0 && i == 0)
                        yield return Monomial<T>.One();

                    yield return new Monomial<T>((uint)i);
                }
            }
            */

            // Slower but less chance of screwing up the "isOne" check
            for (int i = 0; i < T.NumBits; i++)
            {
                var m = GetBit(i);
                if (m.IsZero)
                    continue;

                yield return m;
            }
        }

        public ulong AsUlong()
            => value.GetWord(0);

        public void SetUlong(ulong v)
            => value.SetWord(0, v);

        public Monomial<T> GetBit(int index)
        {
            var wordIdx = index >> 6;
            var bitIdx = index - (64 * wordIdx);
            var v = 1 & (value.GetWord(wordIdx) >> (ushort)bitIdx);
            // Return zero if the monomial is not present in the set.
            if (v == 0)
                return Monomial<T>.Zero();
            // Special case: The 0th bit is set, indicating a constant offset of one
            if (index == 0)
                return Monomial<T>.One();

            return new((uint)index);
        }

        public void SetBit(int index, bool v)
        {
            var wordIdx = index >> 6;
            var bitIdx = index - (64 * wordIdx);

            var val = Convert.ToUInt64(v);
            var word = value.GetWord(wordIdx);
            word &= ~(1ul << bitIdx);
            word |= (val << bitIdx);

            value.SetWord(wordIdx, word);
        }

        private void XorBit(int index, bool v)
        {
            var wordIdx = index >> 6;
            var bitIdx = index - (64 * wordIdx);

            var val = Convert.ToUInt64(v);
            var word = value.GetWord(wordIdx);
            word ^= (val << bitIdx);
            value.SetWord(wordIdx, word);
        }

        public static BoolPoly<T> operator +(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { value = left.value + right.value };
        public static BoolPoly<T> operator +(BoolPoly<T> left, Monomial<T> right)
        {
            // Clone the poly
            left = left.Clone();

            // Fetch the nth bit containing the `right` monomial
            var idx = right.Index;
            var a = left.GetBit(idx);

            // XOR the bit coefficient by 1
            bool value = !a.IsZero ^ true;
            left.SetBit(idx, value);
            return left;
        }


        public static BoolPoly<T> operator *(BoolPoly<T> left, Monomial<T> right)
        {
            // Zero / one identities
            if (right.IsZero)
                return new BoolPoly<T>();
            if (right.IsOne)
                return new BoolPoly<T>() { value = left.value };

            var r2 = FastAnfMultiply(left.value.GetWord(0), 1ul << (ushort)right.Index);
            var r = new BoolPoly<T>();
            r.value.SetConstant(r2);
            return r;



            // Construct a new polynomial and multiply
            var rhs = new BoolPoly<T>();
            rhs.SetBit(right.Index, true);

            var r1 = left * rhs;




            if (r1.value.GetWord(0) != r2)
                Debugger.Break();

            return r1;
        }

        // Might be wrong?
        public static BoolPoly<T> operator *(BoolPoly<T> left, BoolPoly<T> right)
        {
            /*
            var result = new BoolPoly<T>();

            var a = left.Clone();
            while(!a.IsZero())
            {
                var i = a.TrailingZeroCount();
                a.SetBit(i, false);

                var b = right.Clone();
                while (!b.IsZero())
                {
                    int j = b.TrailingZeroCount();
                    b.SetBit(j, false);

                    result.XorBit(i | j, true);
                }
            }

            return result;
            */

            // Correct but probably should not be used
            throw new InvalidOperationException();
        }

        /*
        public static ulong Mul(ulong left, ulong right)
        {

            ulong result = 0;

            var a = left;
            while (a != 0)
            {
                var i = BitOperations.TrailingZeroCount(a);
                //a.SetBit(i, false);
                a &= (a - 1);

                var b = right;
                while (b != 0)
                {
                    int j = BitOperations.TrailingZeroCount(b);
                    b &= (b - 1);
                    //b.SetBit(j, false);

                    //result.XorBit(i | j, true);
                    result ^= 1UL << (i | j);
                }
            }

            return result;
        }
        */
        public static ulong AnfMultiply(ulong left, ulong right)
        {
            // If either is zero, the product is zero
            if (left == 0 || right == 0) return 0;

            ulong result = 0;
            ulong a = left;

            while (a != 0)
            {
                int i = BitOperations.TrailingZeroCount(a);
                a &= a - 1; // Clear lowest set bit

                ulong b = right;
                while (b != 0)
                {
                    int j = BitOperations.TrailingZeroCount(b);
                    b &= b - 1; // Clear lowest set bit

                    // Monomial multiplication: x^I * x^J = x^(I OR J)
                    // Coefficient addition: XOR
                    result ^= 1UL << (i | j);
                }
            }

            return result;
        }

        // Algebraic normal form multiplication, but assuming that `right` is just a single monomial index
        public static ulong FastAnfMultiply(ulong left, ulong right)
        {
            // If either is zero, the product is zero
            if (left == 0 || right == 0) return 0;

            ulong result = 0;
            ulong a = left;

            while (a != 0)
            {
                int i = BitOperations.TrailingZeroCount(a);
                a &= a - 1; // Clear lowest set bit

                ulong b = right;

                int j = BitOperations.TrailingZeroCount(b);
                b &= b - 1; // Clear lowest set bit


                result ^= 1UL << (i | j);
                
            }

            return result;
        }

        public BoolPoly<T> Clone() => new BoolPoly<T>() {  cachedLm = cachedLm, value = value};

        public static bool operator ==(BoolPoly<T> left, BoolPoly<T> right) => Equals(left, right);
        public static bool operator !=(BoolPoly<T> left, BoolPoly<T> right) => !Equals(left, right);

        public override bool Equals(object? obj)
        {
            if (obj == null || obj is not BoolPoly<T> other)
                return false;

            return Equals(this, other);
        }

        public override int GetHashCode()
        {
            return value.GetHashCode();
        }

        private static bool Equals(BoolPoly<T> a, BoolPoly<T> b)
        {
            return a.value.Eq(b.value);
        }

        public override string ToString()
        {
            var mStrs = Monomials.Select(x => x.ToString()).ToList();
            return String.Join(" + ", mStrs);
        }

        public int CompareTo(BoolPoly<T>? other)
        {
            // Compare leading monomial
            var cmp = Lm.CompareTo(other.Lm);
            if (cmp != 0)
                return cmp;

            // Compare total degree
            var totalA = GetDegree();
            var totalB = other.GetDegree();
            if (totalA > totalB)
                return 1;
            if (totalB > totalA)
                return -1;

            // Finally number of terms
            totalA = PopCount();
            totalB = other.PopCount();
            if (totalA > totalB)
                return 1;
            if (totalB > totalA)
                return -1;

            return 0;

        }
    }

    public static class VecUtil
    {
        public static int GetNumBits(int numVars)
            => 1 << (ushort)numVars;
    }
}
