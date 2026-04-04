using Mba.Simplifier.Bindings;
using Mba.Simplifier.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Reflection.Emit;
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
        // Gets or sets whether the line is a symbol or instruction
        public bool IsSymbol { get; set; }

        // The possible instructions the component can choose from
        public SynthOpc[] Choices { get; set; }

        public int MaxArity => Choices.Max(x => x.GetOperandCount());

        // The DAG index of the component
        // Inputs get assigned the first N indices, so this is an offset starting from N
        public Term LocOffset { get; set; }

        // Selector variable choosing which semantic(add, sub, etc) to assign to the component
        public Term Opcode { get; set; }

        // The operands of the component
        public SynthOperand[] Operands { get; set; }

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
        public Term IsConst { get; }

        // The immediate value of this operand
        public Term ConstValue { get; set; }

        // The index of the operand. 
        public Term OperandIndex { get; }

        public SynthOperand(Term isConstant, Term constVal, Term index)
        {
            IsConst = isConstant;
            ConstValue = constVal;
            OperandIndex = index;
        }

        public override string ToString()
        {
            return $"(IsConstant: {IsConst}) (Index: {OperandIndex})";
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

        private readonly uint w;

        public static void Test()
        {
            var config = new SynthConfig(new SynthOpc[] { SynthOpc.Add, SynthOpc.Sub }, 5, 5, 0);

            var (ctx, idx) = Parse("(a+b)-c", 8);
            var synth = new HieraSynth(config, ctx, idx);

            synth.Run();
            Debugger.Break();
        }

        public HieraSynth(SynthConfig config, AstCtx mbaCtx, AstIdx mbaIdx)
        {
            this.config = config;
            this.mbaCtx = mbaCtx;
            this.mbaIdx = mbaIdx;

            this.mbaVariables = mbaCtx.CollectVariables(mbaIdx).ToArray();

            // Set the global width that all expressions use
            w = mbaVariables.Select(x => mbaCtx.GetWidth(x)).Append(mbaCtx.GetWidth(mbaIdx)).Max();

            // Zero extend the output if needed
            var outputWidth = mbaCtx.GetWidth(mbaIdx);
            if (w > outputWidth)
                mbaIdx = mbaCtx.Zext(mbaIdx, (byte)w);

            // Translate inputs to SMT
            var translator = new BitwuzlaTranslator(mbaCtx, ctx);

            groundTruth = translator.Translate(mbaIdx);
            symbols = mbaCtx.CollectVariables(mbaIdx).Select(x => translator.Translate(x)).ToArray();
        }

        public void Run()
        {
            GetLines();
        }

        private List<SynthLine> GetLines()
        {
            var lines = new List<SynthLine>();

            // Each variable gets a dedicated line
            for (int i = 0; i < symbols.Length; i++)
                lines.Add(new() { IsSymbol = true });

            var maxOperandSize = BvWidth(config.MaxLength);
            var opcodeSize = BvWidth(config.Opcodes.Length - 1);
            for (int lineIndex = symbols.Length; lineIndex < config.MaxLength; lineIndex++)
            {
                var line = new SynthLine();
                line.Choices = config.Opcodes.ToArray();
                line.IsSymbol = false;
                line.Opcode = ctx.MkBvConst($"compCode{lineIndex}", opcodeSize);

              
                line.Operands = new SynthOperand[line.MaxArity];
                for(int i = 0; i < line.MaxArity; i++)
                {
                    var isConstant = config.MaxConstants == 0 ? ctx.MkFalse() : ctx.MkBoolConst($"line{lineIndex}_op{i}is_const");
                    var constant = ctx.MkBvConst($"line{lineIndex}_op{i}const", w);
                    var operandIndex = ctx.MkBvConst($"line{lineIndex}_op{i}", maxOperandSize);

                    var operand = new SynthOperand(isConstant, constant, operandIndex);
                    line.Operands[i] = operand;
                }

                lines.Add(line);
            }

            return lines;
        }

        // Get the minimum number of bits needed to fit an integer that ranges from 0..N (inclusive)
        public static int BvWidth(int maxValue)
        {
            if (maxValue == 0)
                return 1;

            return BitOperations.Log2((uint)maxValue) + 1;
        }


        private static (AstCtx Ctx, AstIdx Idx) Parse(string text, uint width)
        {
            var ctx = new AstCtx();
            AstIdx.ctx = ctx;
            var parsed = RustAstParser.Parse(ctx, text, width);
            return (ctx, parsed);
        }
    }

   
}
