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

    public struct Monomial<T> : IEquatable<Monomial<T>> where T : IVector<ulong, T>
    {
        public static int NumVars => T.NumVars;

        public static int NumBits => T.NumBits;
         
        public int VarMask;

        public Monomial(int varMask)
        {
            VarMask = varMask;
        }

        public override bool Equals([NotNullWhen(true)] object? obj)
        {
            if (obj is Monomial<T> other)
                return Equals(other);
            return false;
        }

        public bool Equals(Monomial<T> other)
        {
            return VarMask == other.VarMask;
        }

        public bool IsZero => VarMask == 0;

        public int Degree => BitOperations.PopCount((uint)VarMask);

        public bool IsDivisible(Monomial<T> other)
        {

        }

        public static bool operator ==(Monomial<T> a, Monomial<T> b) => a.Equals(b);
        public static bool operator !=(Monomial<T> a, Monomial<T> b) => !a.Equals(b);

        public static Monomial<T> operator *(Monomial<T> a, Monomial<T> b)
        {
            // a * 0 == 0
            if (a.VarMask == 0 || b.VarMask == 0)
                return new(0);

            // (a*b) * (c*d) == a*b*c*d
            return new(a.VarMask | b.VarMask);
        }

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
            var index = LeadingZeroCount();
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
                    var bit = 1 & (word >> i);
                    yield return new Monomial<T>((int)bit);
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
