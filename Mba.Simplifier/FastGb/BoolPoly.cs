using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Runtime.Intrinsics;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.FastGb
{
    public interface IVector<T, TSelf> : IAdditionOperators<TSelf, TSelf, TSelf> where TSelf: IVector<T, TSelf>
    {
        static abstract int NumVars { get; }

        static abstract int NumBits { get; }

        static abstract int NumWords { get; }
    }

    public struct U4 : IVector<Vector64<ulong>>
    {
        public Vector64<ulong> Value;

        public static int NumVars => BitOperations.TrailingZeroCount(NumBits);

        public static int NumBits => 4;

        public static int NumWords => NumBits <= 64 ? 1 : (NumBits >> 6);

        //public static U4 operator +(U4 left, U4 right) => new U4 { Value = left.Value + right.Value };
    }


    public struct U64 : IVector<Vector64<ulong>>
    {
        public Vector64<ulong> Value;

        public static int NumVars => BitOperations.TrailingZeroCount(NumBits);

        public static int NumBits => 64;

        public static int NumWords => NumBits <= 64 ? 1 : (NumBits >> 6);

        //public static U64 operator +(U64 left, U64 right) => new U64 { Value = left.Value + right.Value };
    }

    public struct U256 : IVector<Vector256<ulong>>
    {
        public Vector256<ulong> Value;

        public static int NumVars => BitOperations.TrailingZeroCount(NumBits);

        public static int NumBits => 256;

        public static int NumWords => NumBits <= 64 ? 1 : (NumBits >> 6);

    }

    public struct Monomial<T> where T : IVector<ulong>
    {
        public static int NumVars => T.NumVars;

        public static int NumBits => T.NumBits;
    }


    // Dense truth table in algebraic normal form
    public class BoolPoly<T> where T : IVector<ulong>, IBitwiseOperators<T, T, T>
    {
        public T Value;

        public BoolPoly()
        {
            
        }

        public BoolPoly(T value)
        {
            Value = value;
        }

        private void Tzcnt()
        {
            value.
        }

        public static BoolPoly<T> operator +(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { Value = left.Value ^ right.Value };
        public static BoolPoly<T> operator *(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { Value = left.Value & right.Value };
        public static BoolPoly<T> operator &(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { Value = left.Value & right.Value };
        public static BoolPoly<T> operator |(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { Value = left.Value | right.Value };
        public static BoolPoly<T> operator ^(BoolPoly<T> left, BoolPoly<T> right) => new BoolPoly<T> { Value = left.Value ^ right.Value };
        public static BoolPoly<T> operator ~(BoolPoly<T> left) => new BoolPoly<T> { Value = ~left.Value };

    }

    public static class VecUtil
    {
        public static int GetNumBits(int numVars)
            => 1 << (ushort)numVars;
    }
}
