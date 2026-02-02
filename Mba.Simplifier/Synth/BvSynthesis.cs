using Mba.Simplifier.Bindings;
using Mba.Simplifier.Utility;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Synth
{
    // Synthesis configuration
    public record SynthConfig(
        // List of all synthesis components and their metadata
        IReadOnlyList<SynthComponent> Components, 

        // Exact number of instructions
        int NumInstructions, 

        // Maximum number of allowed constants
        int maxConstants);

    public record ComponentData(int MaxUsers = -1);

    // A component is a group of opcodes
    // E.g. {add, sub} can be a single component,
    // or {neg, and, or, xor}
    // Alternatively you can put all operations into a single component.
    public class SynthComponent
    {
        private readonly ComponentData data;
        private readonly SynthOpc[] opcodes;

        public SynthComponent(ComponentData data, params SynthOpc[] opcodes)
        {
            this.data = data;
            this.opcodes = opcodes;
        }

        public SynthComponent(params SynthOpc[] opcodes)
        {
            this.data = new ComponentData();
            this.opcodes = opcodes;
        }
    }

    public class SynthOperand
    {
        // Boolean variable indicating whether the first operand is a constant
        public Term IsConstant { get; }

        // The index of the operand. This can be an index into lines[] or constants[].
        public Term Index { get; }

        public SynthOperand(Term isConstant, Term index)
        {
            IsConstant = isConstant;
            Index = index;
        }
    }

    public class SynthLine
    {
        // Gets or sets whether the line is a symbol or instruction
        public bool IsSymbol { get; set; }

        // Index of the component
        public Term ComponentIndex { get; set; }

        // Which opcode was picked for the component
        public Term ComponentOpcode { get; set; }

        // The operands of the line.
        public SynthOperand[] Operands { get; set; }
    }


    public class BvSynthesis
    {
        private readonly SynthConfig config;

        private readonly AstCtx mbaCtx;
        private readonly AstIdx mbaIdx;
        private TermManager ctx = new();

        // Original input expression
        private Term groundTruth;
        // Input variables
        private Term[] symbols;

        public BvSynthesis(SynthConfig config, AstCtx mbaCtx, AstIdx mbaIdx)
        {
            this.config = config;
            this.mbaCtx = mbaCtx;
            this.mbaIdx = mbaIdx;
        }

        public void Run()
        {
            var translator = new BitwuzlaTranslator(mbaCtx, ctx);
            groundTruth = translator.Translate(mbaIdx);
            symbols = mbaCtx.CollectVariables(mbaIdx).Select(x => translator.Translate(x)).ToArray();

            CreateSkeleton();
            Debugger.Break();

            var x = ctx.MkBvConst("x", 8);
            Debugger.Break();
        }

        private void CreateSkeleton()
        {

        }
    }

    public class SynthTests
    {
        public static void P0()
        {
            var (ctx, idx) = Parse("(a&b) + c", 8);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                new(SynthOpc.Add, SynthOpc.Sub),
            };

            var config = new SynthConfig(components, 5, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
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
