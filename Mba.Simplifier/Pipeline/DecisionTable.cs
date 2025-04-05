using Mba.Simplifier.Minimization;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Pipeline
{
    [Flags]
    public enum Decision : byte
    {
        None = 1,
        First = 2,
        Second = 4,
        Both = 8,
    }

    // This is a quaternary truth table implemented in a somewhat adhoc way.
    // TODO: Abstract truth table struct to support arbitrary sizes.
    // Alternative TODO: Compact two decisions into a single `byte`, instead of allocating a byte for each decision
    public class DecisionTable
    {
        private readonly int numVars;

        public int NumBits => 1 << (ushort)numVars;

        public readonly Decision[] arr;

        public DecisionTable(int numVars)
        {
            this.numVars = numVars;
            arr = new Decision[NumBits];
        }

        public Decision GetDecision(int index)
        {
            return arr[index];
        }

        public void AddDecision(int index, Decision value)
        {
            arr[index] |= value;
        }

        public void SetDecision(int index, Decision value)
        {
            arr[index] = value;
        }

        public List<List<Decision>> AsList()
        {
            var output = new List<List<Decision>>();
            foreach(var decision in arr)
            {
                var curr = new List<Decision>();
                if (decision.HasFlag(Decision.None))
                    curr.Add(Decision.None);
                if (decision.HasFlag(Decision.First))
                    curr.Add(Decision.First);
                if (decision.HasFlag(Decision.Second))
                    curr.Add(Decision.Second);
                if (decision.HasFlag(Decision.Both))
                    curr.Add(Decision.Both);

                output.Add(curr);
            }

            return output;
        }
    }
}
