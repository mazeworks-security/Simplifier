using Mba.Interop;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Bindings
{
    public struct KnownBits
    {
        public readonly uint Width;

        public readonly ulong Zeroes;

        public readonly ulong Ones;

        public readonly ulong UnknownBits => (~(Zeroes | Ones) & ModuloReducer.GetMask(Width));

        public KnownBits(uint width, ulong zeroes, ulong ones)
        {
            Width = width;
            Zeroes = zeroes;
            Ones = ones;
        }

        public static KnownBits Empty(uint width)
            => new KnownBits(width, 0, 0);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static unsafe KnownBits Add(KnownBits lhs, KnownBits rhs)
        {
            KnownBits result;
            Api.GetAddKnownBits(&lhs, &rhs, &result);
            return result;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static unsafe KnownBits Mul(KnownBits lhs, KnownBits rhs)
        {
            KnownBits result;
            Api.GetMulKnownBits(&lhs, &rhs, &result);
            return result;
        }

        public static KnownBits MakeConstant(ulong c, uint width)
        {
            var mask = ModuloReducer.GetMask(width);
            c &= mask;
            return new KnownBits(width, ~c & mask, c);
        }

        public override string ToString()
        {
            var arr = new char[Width];
            for(ushort i = 0; i < arr.Length; i++)
            {
                bool isOne = (Ones & (1ul << i)) != 0;
                bool isZero = (Zeroes & (1ul << i)) != 0;
                if (isOne && isZero)
                    throw new InvalidOperationException($"Conflicting known bits!");

                if (isOne)
                    arr[i] = '1';
                else if (isZero)
                    arr[i] = '0';
                else
                    arr[i] = '?';
            }
            return string.Join("", arr.Reverse());
        }

        private static class Api
        {
            [DllImport("Mba.FFI")]
            public unsafe static extern void GetAddKnownBits(KnownBits* lhs, KnownBits* rhs, KnownBits* output);

            [DllImport("Mba.FFI")]
            public unsafe static extern void GetMulKnownBits(KnownBits* lhs, KnownBits* rhs, KnownBits* output);
        }
    }
}