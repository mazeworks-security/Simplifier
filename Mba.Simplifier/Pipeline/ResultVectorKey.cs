using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Pipeline
{
    public struct ResultVectorKey : IEquatable<ResultVectorKey>
    {
        public readonly ulong[] resultVector;

        private readonly int hashCode;

        public ResultVectorKey(ulong[] resultVector)
        {
            this.resultVector = resultVector;

            hashCode = resultVector.Length;
            foreach(ulong val in resultVector)
                hashCode = hashCode * 17 + val.GetHashCode();
        }

        public bool Equals(ResultVectorKey other)
        {
            return hashCode == other.hashCode && resultVector.SequenceEqual(other.resultVector);
        }

        public override int GetHashCode()
        {
            return hashCode;
        }
    }

    public struct NthOrderKey : IEquatable<NthOrderKey>
    {
        public readonly int k;

        public readonly int[] indices;

        private readonly int hashCode;

        public NthOrderKey(int k, int[] resultVector)
        {
            this.k = k;
            this.indices = resultVector;

            hashCode = k.GetHashCode();
            foreach (var val in resultVector)
                hashCode = hashCode * 17 + val.GetHashCode();

        }

        public bool Equals(NthOrderKey other)
        {
            return k == other.k && hashCode == other.hashCode &&  indices.SequenceEqual(other.indices);
        }

        public override int GetHashCode()
        {
            return hashCode;
        }

    }
}
