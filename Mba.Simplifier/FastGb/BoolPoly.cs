using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Numerics;
using System.Runtime.Intrinsics;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.FastGb
{
    public interface IVector<T, TSelf> : IBitwiseOperators<TSelf, TSelf, TSelf>, IEquatable<TSelf>  where TSelf: IVector<T, TSelf>
    {
        static abstract int NumVars { get; }

        static abstract int NumBits { get; }

        static abstract int NumWords { get; }

        ulong GetWord(int index);

        bool IsZero();

        bool Eq(TSelf other);
    }

    public struct U4 : IVector<Vector64<ulong>, U4>
    {
        public Vector64<ulong> Value;

        public static int NumVars => BitOperations.TrailingZeroCount(NumBits);

        public static int NumBits => 4;

        public static int NumWords => NumBits <= 64 ? 1 : (NumBits >> 6);

        public static U4 operator +(U4 left, U4 right)
        {
            throw new NotImplementedException();
        }

        //public static U4 operator +(U4 left, U4 right) => new U4 { Value = left.Value + right.Value };
    }


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

    // Problem: Monomial needs to have `isOne` field
    // Monomials are created by indices..
    // isOne = varMask == -1
    public struct Monomial<T> : IEquatable<Monomial<T>> where T : IVector<ulong, T>
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

        public bool IsZero => !isOne && mVars == 0;

        public bool IsOne => isOne;

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

        public static Monomial<T> Zero()
           => new Monomial<T>(0);

        public static Monomial<T> One()
            => new Monomial<T>(0);

    }


    // Dense truth table in algebraic normal form
    public class BoolPoly<T> where T : IVector<ulong, T>, IBitwiseOperators<T, T, T>, IEquatable<T>
    {
        public T value;

        public IEnumerable<Monomial<T>> Monomials => GetMonomials();

        // Only exists for the debugger view, because I hate expanding enumerators
        public List<Monomial<T>> MList => GetMonomials().ToList();

        public BoolPoly()
        {
            
        }

        public BoolPoly(T value)
        {
            this.value = value;
        }

        public Monomial<T> Lm()
        {
            var index = (uint)LeadingZeroCount();
            return index == T.NumBits ? new(0) : new(index);
        }

        public bool IsZero()
            => value.IsZero();

        private int TrailingZeroCount()
        {
            for(int i = 0; i < T.NumWords; i++)
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
            for (int i = T.NumWords - 1; i >= 0; i--)
            {
                var word = value.GetWord(i);
                var lzcnt = BitOperations.LeadingZeroCount(word);
                if (lzcnt != 0)
                {
                    return (64 * i) + lzcnt;
                }
            }

            return T.NumBits;
        }

        private IEnumerable<Monomial<T>> GetMonomials()
        {
            for(int wordIdx = 0;  wordIdx < T.NumWords; wordIdx++)
            {
                var word = value.GetWord(wordIdx);
                for(int i = 0; i < T.NumBits; i++)
                {
                    var bit = (uint)(1 & (word >> i));
                    if (bit == 0)
                        continue;

                    // If the 0th bit is demanded, we have the zero monomial.
                    if (wordIdx == 0 && i == 0)
                        yield return new Monomial<T>(uint.MaxValue);

                    yield return new Monomial<T>(bit);
                }
            }
        }

        public static BoolPoly<T> operator +(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { value = left.value ^ right.value };
        public static BoolPoly<T> operator *(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { value = left.value & right.value };
        public static BoolPoly<T> operator &(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { value = left.value & right.value };
        public static BoolPoly<T> operator |(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { value = left.value | right.value };
        public static BoolPoly<T> operator ^(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { value = left.value ^ right.value };
        public static BoolPoly<T> operator ~(BoolPoly<T> left) => new BoolPoly<T> { value = ~left.value };

        public static bool operator ==(BoolPoly<T> left, BoolPoly<T> right) => Equals(left, right);
        public static bool operator !=(BoolPoly<T> left, BoolPoly<T> right) => !Equals(left, right);

        public override bool Equals(object? obj)
        {
            if (obj == null || obj is not BoolPoly<T> other)
                return false;

            return Equals(this, other);
        }

        private static bool Equals(BoolPoly<T> a, BoolPoly<T> b)
        {
            return a.value.Eq(b.value);
        }
    }

    public static class VecUtil
    {
        public static int GetNumBits(int numVars)
            => 1 << (ushort)numVars;
    }
}
