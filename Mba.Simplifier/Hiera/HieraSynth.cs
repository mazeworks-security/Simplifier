using Mba.Simplifier.Bindings;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Hiera
{
    public record SynthConfig(
        // The opcodes that may be chosen during synthesis
        SynthOpc[] Opcodes,
        // Minimum number of instructions a solution must use
        int MinLength, 
        // Maximal number of instructions a solution may use
        int MaxLength, 
        // Maximum number of unique constants
        int MaxConstants
        );

    // A component has multiple choices for an instruction
    // If we want to allow synthesizing variable length sequences, we 
    public class SynthLine
    {
        // The possible instructions the component can choose from
        public SynthOpc[] Choices { get; }

        // The DAG index of the component
        // Inputs get assigned the first N indices, so this is an offset starting from N
        public Term LocOffset { get; set; }

        // Selector variable choosing which semantic(add, sub, etc) to assign to the component
        public Term Opcode { get; set; }

        // The operands of the component
        public SynthOperand Operands { get; set; }

        // Result of the component
        public Term Output { get; set; }

        public SynthLine(params SynthOpc[] opcodes)
        {
            Choices = opcodes;
        }
    }

    public class SynthOperand
    {
        // Boolean variable indicating whether the first operand is a constant
        public Term IsImm { get; }

        // The index of the operand. 
        public Term OperandIndex { get; }

        // The immediate value of this operand
        public Term ImmValue { get; set; }

        public SynthOperand(Term isConstant, Term index, Term immValue)
        {
            IsImm = isConstant;
            OperandIndex = index;
            ImmValue = immValue;
        }

        public override string ToString()
        {
            return $"(IsConstant: {IsImm}) (Index: {OperandIndex})";
        }
    }

    // "HieraSynth: A Parallel Framework for Complete Super-Optimization with Hierarchical Space Decomposition"
    //https://lsrcz.github.io/files/OOPSLA25.pdf
    //
    // Phd thesis going into more detail
    // https://digital.lib.washington.edu/server/api/core/bitstreams/62255959-5c63-40f4-8190-aa51835c848e/content
    public class HieraSynth
    {
        private readonly SynthConfig config;

        private readonly AstCtx mbaCtx;
        private readonly AstIdx mbaIdx;
        private readonly AstIdx[] mbaVariables;

        private TermManager ctx = new();

        // Original input expression
        private Term groundTruth;
        // Input variables
        private Term[] symbols;

        // Bitvector variable selecting the length of the synthesized program
        private readonly Term numInstsVar;

        private readonly List<SynthLine> allLines;

        // Get the index of the first instruction in lines
        private int FirstInstIdx => symbols.Length;

        public IReadOnlyList<SynthLine> RealLines => allLines.Skip(FirstInstIdx).ToList();

        // Get the max number of operands that one instruction may contain.
        private int MaxArity => RealLines.Max(x => x.Choices.Max(x => x.GetOperandCount()));
    }
}
