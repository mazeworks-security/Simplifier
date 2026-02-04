using Bitwuzla;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Synthesis;
using Mba.Simplifier.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
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
        int MaxConstants
        );

    public record ComponentData(int MaxUsers = -1);

    // A component is a group of opcodes
    // E.g. {add, sub} can be a single component,
    // or {neg, and, or, xor}
    // Alternatively you can put all operations into a single component.
    public class SynthComponent
    {
        public ComponentData Data { get; }
        public SynthOpc[] Opcodes { get; }

        public SynthComponent(ComponentData data, params SynthOpc[] opcodes)
        {
            Data = data;
            Opcodes = opcodes;
        }

        public SynthComponent(params SynthOpc[] opcodes)
        {
            Data = new ComponentData();
            Opcodes = opcodes;
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

        public override string ToString()
        {
            return $"(IsConstant: {IsConstant}) (Index: {Index})";
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

        // Get the index of the first instruction in lines
        public int FirstInstIdx => symbols.Length;

        // Get the max number of operands that one instruction may contain.
        public int MaxArity => config.Components.Max(x => x.Opcodes.Max(x => x.GetOperandCount()));

        IReadOnlyList<SynthComponent> components;

        private List<SynthLine> lines;

        private List<Term> constants;

        private readonly int w;

        private readonly uint componentIndexSize;

        private readonly uint componentOpcodeSize;

        public BvSynthesis(SynthConfig config, AstCtx mbaCtx, AstIdx mbaIdx)
        {
            this.config = config;
            this.mbaCtx = mbaCtx;
            this.mbaIdx = mbaIdx;
            this.components = config.Components;
            w = mbaCtx.GetWidth(mbaIdx);

            // Get the minimum size bitvector needed to store the component index and component opcode
            componentIndexSize = (uint)BvWidth(components.Count - 1);
            componentOpcodeSize = (uint)BvWidth(components.Max(x => x.Opcodes.Length) - 1);
        }

        public void Run()
        {
            var translator = new BitwuzlaTranslator(mbaCtx, ctx);
            groundTruth = translator.Translate(mbaIdx);
            symbols = mbaCtx.CollectVariables(mbaIdx).Select(x => translator.Translate(x)).ToArray();

            lines = GetLines();
            constants = Enumerable.Repeat(0, config.MaxConstants).Select(x => ctx.MkBvConst($"const{x}", w)).ToList();

            var skeleton = GetSkeleton();



            Debugger.Break();
        }

        private List<SynthLine> GetLines()
        {
            var lines = new List<SynthLine>();

            // Each variable gets a dedicated line
            for (int i = 0; i < symbols.Length; i++)
                lines.Add(new() { IsSymbol = true});



            for (int lineIndex = lines.Count; lineIndex < config.NumInstructions; lineIndex++)
            {
                var line = new SynthLine();
                line.IsSymbol = false;
                line.ComponentIndex = components.Count == 1 ? ctx.MkBvValue(0, 1) : ctx.MkBvConst($"compIdx{lineIndex}", componentIndexSize);
                line.ComponentOpcode = ctx.MkBvConst($"compCode{lineIndex}", componentOpcodeSize);
                line.Operands = new SynthOperand[MaxArity];
                var operandBitsize = BvWidth(Math.Max(lineIndex - 1, config.MaxConstants - 1));
                for (int i = 0; i < MaxArity; i++)
                {
                    var isConstant = config.MaxConstants == 0 ? ctx.MkFalse() : ctx.MkBoolConst($"{lineIndex}_op{i}Const");
                    var operandIndex = ctx.MkBvConst($"{lineIndex}_op{i}", operandBitsize);
                    var operand = new SynthOperand(isConstant, operandIndex);
                    line.Operands[i] = operand;
                }

                lines.Add(line);
            }

            return lines;
        }

        private Term GetSkeleton()
        {
            var exprs = new List<Term>();
            for(int lineIndex = 0; lineIndex < lines.Count; lineIndex++)
            {
                // The first N lines are symbols
                var line = lines[lineIndex];
                if (line.IsSymbol)
                {
                    exprs.Add(symbols[lineIndex]);
                    continue;
                }

                // Select all of the operands
                var operands = line.Operands.Select(x => SelectOperand(x, exprs));
                var op0 = operands.ElementAtOrDefault(0);
                var op1 = operands.ElementAtOrDefault(1);

                // Need to get the opcode choices first.
                var componentChoices = new List<Term>();
                foreach(var component in components)
                {
                    List<Term> terms = new();
                    foreach(var opcode in component.Opcodes)
                    {
                        var term = opcode switch
                        {
                            SynthOpc.Not => ~op0,
                            SynthOpc.And => (op0 & op1),
                            SynthOpc.Or => (op0 | op1),
                            SynthOpc.Xor => (op0 ^ op1),
                            SynthOpc.Add => (op0 + op1),
                            SynthOpc.Sub => (op0 - op1),
                            SynthOpc.Mul => (op0 * op1),
                            _ => throw new InvalidOperationException()
                        };

                        terms.Add(term);
                    }

                    componentChoices.Add(LinearSelect(line.ComponentOpcode, terms));
                }

                var select = LinearSelect(line.ComponentIndex, componentChoices);
                exprs.Add(select);
            }

            return exprs.Last();
        }

        private Term SelectOperand(SynthOperand operand, List<Term> prev)
        {
            var constSelect = LinearSelect(operand.Index, constants);
            var operandSelect = LinearSelect(operand.Index, prev);
            return ctx.MkIte(operand.IsConstant, constSelect, operandSelect);
        }

        private Term LinearSelect(Term index, List<Term> options)
        {
            var n = options.Count;

            if (n == 0)
                throw new InvalidOperationException();
            if (n == 1)
                return options[0];

            // TODO: If n > 12, use the `PrunedTree` algorithm from your old version
            if (n > 12)
                Debugger.Break();

            var result = options[n - 1];

            for (int i = n - 2; i >= 0; i--)
            {
                var condition = index == ctx.MkBvValue(i, index.Sort.BvSize);
                result = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_ITE, condition, options[i], result);
            }

            return result;
        }

        // Get the minimum number of bits needed to fit an integer that ranges from 0..N (inclusive)
        public static int BvWidth(int maxValue)
        {
            if (maxValue == 0)
                return 1;

            return BitOperations.Log2((uint)maxValue) + 1;
        }

        private Term GetComponentIdxBv(SynthComponent component)
        {
            return null;
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
