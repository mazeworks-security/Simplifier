using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Fuzzing
{
    public class SeededRandom
    {
        private readonly Random random = new(int.MaxValue);

        public int Next(int minValue, int maxValue) => random.Next(minValue, maxValue);

        public ulong GetRandUlong()
        {
            // The builtin random API can only return positive int64s,
            // so the sign-bit must be flipped at random manually.
            var value = (ulong)random.NextInt64(0, long.MaxValue);
            ulong signBit = GetRandBool() ? 0x8000000000000000 : 0;
            value |= signBit;
            return value;
        }

        public ulong GetRandUlong(ulong minValue, ulong maxValue)
        {
            var value = (ulong)random.NextInt64((long)minValue, (long)maxValue);
            return value;
        }

        public ushort GetRandUshort(ushort min, ushort max)
            => (ushort)random.Next((int)min, (int)max);

        public bool GetRandBool()
            => random.Next(0, 2) == 1;
    }
}
