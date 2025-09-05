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
}
