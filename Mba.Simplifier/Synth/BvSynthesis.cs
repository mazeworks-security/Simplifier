using Antlr4.Runtime.Tree;
using Bitwuzla;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Synthesis;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Reflection.Emit;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
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

    public record ComponentData(int MaxInstances = -1);

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

    //// ComponentDbEntry(SynthComponent Component, Index, Opc

    //// List of components
    //// Integer assignments for component index and component opcode
    //public class ComponentDatabase
    //{
    //    public List<SynthComponent> Components { get; set; }


    //}

    public class SynthOperand
    {
        // Boolean variable indicating whether the first operand is a constant
        public Term IsConstant { get; }

        // The index of the operand. This can be an index into lines[] or constants[].
        public Term Index { get; }

        // The chain of ITEs corresponding to this operand's value
        public Term ConcreteValue { get; set; }

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
        //public Term ComponentIndex { get; set; }

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
        private readonly AstIdx[] mbaVariables;

        private TermManager ctx = new();

        // Original input expression
        private Term groundTruth;
        // Input variables
        private Term[] symbols;

        // Get the index of the first instruction in lines
        private int FirstInstIdx => symbols.Length;

        // Get the max number of operands that one instruction may contain.
        private int MaxArity => config.Components.Max(x => x.Opcodes.Max(x => x.GetOperandCount()));

        public List<SynthOpc> Opcodes => components.SelectMany(x => x.Opcodes).ToList();

        private readonly IReadOnlyList<SynthComponent> components;

        private List<SynthLine> lines;

        public IReadOnlyList<SynthLine> RealLines => lines.Skip(FirstInstIdx).ToList();

        private List<Term> constants;

        private readonly int w;

        private readonly uint componentIndexSize;

        private readonly uint componentOpcodeSize;

        public BvSynthesis(SynthConfig config, AstCtx mbaCtx, AstIdx mbaIdx)
        {
            this.config = config;
            this.mbaCtx = mbaCtx;
            this.mbaIdx = mbaIdx;
            this.mbaVariables = mbaCtx.CollectVariables(mbaIdx).ToArray();
            this.components = config.Components;
            w = mbaCtx.GetWidth(mbaIdx);

            // Translate inputs to LLVM IR
            var translator = new BitwuzlaTranslator(mbaCtx, ctx);



            groundTruth = translator.Translate(mbaIdx);
            symbols = mbaCtx.CollectVariables(mbaIdx).Select(x => translator.Translate(x)).ToArray();

            // parity
            /*
            var x = symbols[0];
            var o1 = x >> (ulong)1;
            var o2 = o1 ^ x;
            var o3 = o2 >> 2;
            var o4 = o2 ^ o3;
            var o5 = o4 & 0x11111111;
            var o6 = o5 * 0x11111111;
            var o7 = o6 >> 28;
            var res = o7 & 1;
            groundTruth = res;
            */


            // Get the minimum size bitvector needed to store the component index and component opcode
            componentIndexSize = (uint)BvWidth(components.Count - 1);
            componentOpcodeSize = (uint)BvWidth(Opcodes.Count - 1);
        }

        public void Run()
        {
            // Get a list of lines
            lines = GetLines();
            constants = Enumerable.Range(0, config.MaxConstants).Select(x => ctx.MkBvConst($"const{x}", w)).ToList();

            // Get the skeleton expression
            var skeleton = GetSkeleton();

            var constraints = GetProgramConstraints();

            CegisT(constraints, skeleton);

            Debugger.Break();
        }

        private void Log(string x)
            => Console.Write(x);

        private List<SynthLine> GetLines()
        {
            var lines = new List<SynthLine>();

            // Each variable gets a dedicated line
            for (int i = 0; i < symbols.Length; i++)
                lines.Add(new() { IsSymbol = true });

            var maxOperandSize = BvWidth(Math.Max(config.NumInstructions - 2, config.MaxConstants - 1));

            for (int lineIndex = lines.Count; lineIndex < config.NumInstructions; lineIndex++)
            {
                var line = new SynthLine();
                line.IsSymbol = false;
                //line.ComponentIndex = components.Count == 1 ? ctx.MkBvValue(0, 1) : ctx.MkBvConst($"compIdx{lineIndex}", componentIndexSize);
                line.ComponentOpcode = ctx.MkBvConst($"compCode{lineIndex}", componentOpcodeSize);
                line.Operands = new SynthOperand[MaxArity];
                var operandBitsize = BvWidth(Math.Max(lineIndex - 1, config.MaxConstants - 1));
                for (int i = 0; i < MaxArity; i++)
                {
                    var isConstant = config.MaxConstants == 0 ? ctx.MkFalse() : ctx.MkBoolConst($"line{lineIndex}_op{i}Const");
                    var operandIndex = ctx.MkBvConst($"line{lineIndex}_op{i}", operandBitsize);

                    // Zero extend all operands to the same width.
                    operandIndex = ctx.MkZext((uint)maxOperandSize - (uint)operandBitsize, operandIndex);

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
            for (int lineIndex = 0; lineIndex < lines.Count; lineIndex++)
            {
                // The first N lines are symbols
                var line = lines[lineIndex];
                if (line.IsSymbol)
                {
                    exprs.Add(symbols[lineIndex]);
                    continue;
                }

                // Select all of the operands
                var operands = line.Operands.Select(x => SelectOperand(x, exprs)).ToList();

                // Provide the concrete value just for lazy editing.
                for (int i = 0; i < line.Operands.Length; i++)
                    line.Operands[i].ConcreteValue = operands[i].justConstants;

                var terms = new List<Term>();
                foreach (var opcode in Opcodes)
                {
                    var term = ApplyOperator(opcode, operands.Select(x => x.expr).ToList());

                    terms.Add(term);
                }

                var select = LinearSelect(line.ComponentOpcode, terms);
                exprs.Add(select);
            }

            return exprs.Last();
        }

        private Term ApplyOperator(SynthOpc opcode, List<Term> operands)
        {
            var op0 = () => operands[0];
            var op1 = () => operands[1];

            var term = opcode switch
            {
                SynthOpc.Not => ~op0(),
                SynthOpc.And => (op0() & op1()),
                SynthOpc.Or => (op0() | op1()),
                SynthOpc.Xor => (op0() ^ op1()),
                SynthOpc.Add => (op0() + op1()),
                SynthOpc.Sub => (op0() - op1()),
                SynthOpc.Mul => (op0() * op1()),
                SynthOpc.Lshr => (op0() >> op1()),
                SynthOpc.Shl => (op0() << op1()),
                _ => throw new InvalidOperationException()
            };

            return term;
        }

        private (Term expr, Term justOperands, Term justConstants) SelectOperand(SynthOperand operand, List<Term> prev)
        {
            var operandSelect = LinearSelect(operand.Index, prev);
            if (config.MaxConstants == 0)
                return (operandSelect, operandSelect, null);

            var constSelect = LinearSelect(operand.Index, constants);
            var expr = ctx.MkIte(operand.IsConstant, constSelect, operandSelect);
            return (expr, operandSelect, constSelect);
        }

        private Term LinearSelect(Term index, List<Term> options)
        {
            var n = options.Count;

            if (n == 0)
                throw new InvalidOperationException();
            if (n == 1)
                return options[0];

            //if (false)
            //if (n > 12)
            //if (n > 13)
            if (false)
            {
                // TODO: Sometimes this encoding is more efficient
                Debugger.Break();
                //return PrunedTree(index, options, 0, n);
            }

            var result = options[n - 1];

            for (int i = n - 2; i >= 0; i--)
            {
                var condition = index == ctx.MkBvValue(i, index.Sort.BvSize);
                result = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_ITE, condition, options[i], result);
            }

            return result;
        }

        private Term PrunedTree(Term index, List<Term> options, int offset, int count)
        {
            if (count == 1) return options[offset];

            int requiredBits = (int)Math.Ceiling(Math.Log2(count));
            int msbIndex = requiredBits - 1;
            int splitSize = 1 << msbIndex;
            int rightCount = count - splitSize;

            var condBit = ctx.MkExtract((uint)msbIndex, (uint)msbIndex, index);
            var condition = condBit == ctx.MkBvValue(1, 1);

            var lowResult = PrunedTree(index, options, offset, splitSize);
            var highResult = PrunedTree(index, options, offset + splitSize, rightCount);

            return ctx.MkIte(condition, highResult, lowResult);
        }

        private Term AndOrSelect(Term index, List<Term> options)
        {
            var n = options.Count;

            if (n == 0)
                throw new InvalidOperationException();
            if (n == 1)
                return options[0];

            var terms = new List<Term>();
            var zero = ctx.MkBvZero(options[0].Sort);

            for (int i = 0; i < n; i++)
            {
                var idxVal = ctx.MkBvValue(i, index.Sort.BvSize);
                var eq = index == idxVal;
                var masked = ctx.MkIte(eq, options[i], zero);
                terms.Add(masked);
            }

            return Or(terms);
        }



        private List<Term> GetProgramConstraints()
        {
            var constraints = new List<Term>();
            AddAcyclicConstraints(constraints);
            AddPruningConstraints(constraints);
            AddSymmetricConstantsConstraint(constraints);
            AddLimitConstraints(constraints);

            return constraints;
        }

        private void AddAcyclicConstraints(List<Term> constraints)
        {
            // Constrain each operand to be less than `i-1`
            for (int i = FirstInstIdx; i < lines.Count; i++)
            {
                var line = lines[i];


                foreach (var operand in line.Operands)
                {
                    var ult = operand.Index <= (uint)(i - 1);
                    var opConstraint = Implies(~operand.IsConstant, ult);
                    // TODO: Being a constant should also imply that the chosen constant is less than the current line index?
                    // There's at least something weird with the constant symmetry constraints improving this case even when only partially enabled
                    var constConstraint = Implies(operand.IsConstant, operand.Index <= (uint)Math.Max((config.MaxConstants - 1), 0));

                    constraints.Add(opConstraint);
                    constraints.Add(constConstraint);
                }
            }

        }

        // Assert that the first constant must be used before the second constant.
        private void AddSymmetricConstantsConstraint(List<Term> constraints)
        {
            //return;
            var first = lines[FirstInstIdx].Operands[0];
            constraints.Add(ctx.MkImplies(first.IsConstant, first.Index == 0));

            var operands = lines.Skip(FirstInstIdx).SelectMany(x => x.Operands).ToList();
            for (int i = 1; i < operands.Count; i++)
            {
                var isCurrConstant = operands[i].IsConstant;
                var idxCurr = operands[i].Index;

                var limit = Math.Min(i, constants.Count - 1);

                for (int v = 1; v < limit + 1; v++)
                {
                    var usingVal = isCurrConstant & (idxCurr == v);

                    var prevUsage = new List<Term>();
                    for (int j = 0; j < i; j++)
                    {
                        var isPrevConstant = operands[j].IsConstant;
                        var idxPrev = operands[j].Index;

                        var match = isPrevConstant & (idxPrev == (v - 1));
                        prevUsage.Add(match);
                    }

                    constraints.Add(Implies(usingVal, Or(prevUsage)));
                }
            }

            //var isUsed = Enumerable.Range(0, constants.Count).Select(x => ctx.False()); 
            //for (int i = FirstInstIdx; i < lines.Count; i++)
            //{

            //}

            // This encoding is not good
            /*
            var size = (uint)BvWidth(constants.Count + 1); // works
            //var size = (uint)BvWidth(constants.Count);

            // works like this
            //var maxConstant = ctx.MkBvValue(constants.Count, size);

            var maxConstant = ctx.MkBvValue(0, 1);

            //var maxOperandSize = BvWidth(Math.Max(config.NumInstructions - 2, config.MaxConstants - 1));

            for (int i = FirstInstIdx; i < lines.Count; i++)
            {
                var line = lines[i];
                //var size0 = maxConstant.Sort.BvSize;
                // var size1 = lines[i].Operands[0].Index.Sort.BvSize;

                //if (size0 < size1)
                //    maxConstant = ctx.MkZext((uint)size1 - (uint)size0, maxConstant);

                List<Term> constConds = new List<Term>();
                foreach (var operand in line.Operands)
                {
                    var opIdx = operand.Index;
                    var size0 = operand.Index.Sort.BvSize;
                    var size1 = maxConstant.Sort.BvSize;

                    if (size0 < size1)
                        opIdx = ctx.MkZext((uint)size1 - (uint)size0, opIdx);
                    else if (size0 > size1)
                        maxConstant = ctx.MkZext((uint)size0 - (uint)size1, maxConstant);


                    // Even if we just stop here with `maxConstant` set to something small.. why does this somehow makes solving faster??
                    constraints.Add(Implies(operand.IsConstant, opIdx <= maxConstant));


                    constConds.Add(operand.IsConstant & opIdx == maxConstant);
                }

                // 
                //maxConstant = ctx.MkIte(Or(constConds), maxConstant + 1, maxConstant);

            }
            */
        }

        private void AddPruningConstraints(List<Term> constraints)
        {
            var sum = ctx.MkBvValue(0, 4);

            // Sort constants
            /*
            for (int i = 1; i < constants.Count; i++)
            {
                constraints.Add(constants[i] > constants[i - 1]);
            }
            */

            for (int i = 0; i < constants.Count - 1; i++)
            {
                //constraints.Add(constants[i] < constants[i + 1]);
            }

            /*
            List<Term> isUsed = Enumerable.Range(0, lines.Count - FirstInstIdx).Select(x => ctx.MkBoolConst($"used_{x}")).ToList();
            for(int k = lines.Count - 1; k >= FirstInstIdx; k--)
            {
                var usageConditions = new List<Term>();
            }
            */



            // Constrain each opcode to be less than its maximum
            for (int lineIdx = 0; lineIdx < lines.Count; lineIdx++)
            {
                var line = lines[lineIdx];


                bool dce = true;

                // Assert that every instruction (including variables) is used
                if (dce && lineIdx != lines.Count - 1)
                {
                    // TODO: For some reason we get worse results if we assert that each variable be used?
                    if (lines[lineIdx].IsSymbol)
                        continue;

                    var usageConditions = new List<Term>();
                    for (int j = lineIdx + 1; j < lines.Count; j++)
                    {
                        if (lines[j].IsSymbol)
                            continue;

                        var operands = lines[j].Operands;
                        var used0 = (~operands[0].IsConstant) & (operands[0].Index == lineIdx);
                        var used1 = (~operands[1].IsConstant) & (operands[1].Index == lineIdx);

                        usageConditions.Add(used0);
                        usageConditions.Add(used1);
                    }

                    var anyUses = Or(usageConditions);
                    constraints.Add(anyUses);

                    // Experimental:
                    // Not helpful
                    /*
                    constraints.Add(Implies(~anyUses, line.Operands[0].Index == 0));
                    constraints.Add(Implies(~anyUses, line.Operands[1].Index == 0));
                    constraints.Add(Implies(~anyUses, line.Operands[0].IsConstant == false));
                    constraints.Add(Implies(~anyUses, line.Operands[1].IsConstant == false));
                    */
                }


                if (lineIdx < FirstInstIdx)
                    continue;

                // Both operands should not be constant.
                bool constFold = true;
                if (constFold)
                    constraints.Add(~And(line.Operands.Select(x => x.IsConstant)));

                var toBv = (Term term) => ctx.MkIte(term, ctx.MkBvValue(1, 1), ctx.MkBvValue(0, 1));
                bool cse = false;
                if (cse)
                {

                    var sigs = new List<Term>();
                    var comb1 = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_CONCAT, line.ComponentOpcode, toBv(line.Operands[0].IsConstant), line.Operands[0].Index, toBv(line.Operands[1].IsConstant), line.Operands[1].Index);
                    sigs.Add(comb1);

                    for (int j = lineIdx + 1; j < lines.Count; j++)
                    {
                        var other = lines[j];

                        //var concats = Enumerable.Range(0, MaxArity).Select(x => ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_CONCAT))

                        var differences = Enumerable.Range(0, MaxArity).Select(x => (line.Operands[x].IsConstant != other.Operands[x].IsConstant) | (line.Operands[x].Index != other.Operands[x].Index));



                        //var comb2 = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_CONCAT, other.ComponentOpcode, toBv(other.Operands[0].IsConstant), other.Operands[0].Index, toBv(other.Operands[1].IsConstant), other.Operands[1].Index);

                        //sigs.Add(comb2)

                        var imply = Implies(line.ComponentOpcode == other.ComponentOpcode, Or(differences));
                        constraints.Add(imply);
                    }
                }

                bool limitOpcodeIndex = true;
                if (limitOpcodeIndex)
                {
                    constraints.Add(line.ComponentOpcode <= (uint)(Opcodes.Count - 1));
                }

                bool limitConstantIndex = true;
                if (limitConstantIndex && constants.Count > 0)
                {
                    foreach (var operand in line.Operands)
                    {
                        constraints.Add(Implies(operand.IsConstant, operand.Index <= (uint)(constants.Count - 1)));
                    }
                }

                // Constant shift opt
                bool constantShiftsOnly = true;
                if (components.Any(x => x.Opcodes.Contains(SynthOpc.Shl)) && constantShiftsOnly)
                {
                    var isShift = IsInstance(line, SynthOpc.Shl);
                    constraints.Add(Implies(isShift, line.Operands[1].IsConstant));
                }
                //continue;

                //var isMul = line.ComponentOpcode == components.Single().Opcodes.IndexOf(SynthOpc.Mul);
                //sum += ctx.MkIte(isMul, ctx.MkBvValue(1, 4), ctx.MkBvValue(0, 4));

                /*
                continue;

                var isMul = line.ComponentOpcode == components.Single().Opcodes.IndexOf(SynthOpc.Mul);
                var isXor = line.ComponentOpcode == components.Single().Opcodes.IndexOf(SynthOpc.Xor);
                var isLshr = line.ComponentOpcode == components.Single().Opcodes.IndexOf(SynthOpc.Lshr);

                constraints.Add(Implies(isLshr, line.Operands[1].IsConstant));

                if (i == lines.Count - 3)
                {
                    constraints.Add(isMul);
                    constraints.Add(line.Operands[1].IsConstant);
                    constraints.Add(line.Operands[1].Index == constants.Count - 1);
                }

                else
                {
                    constraints.Add(~isMul);
                }

                if(i == 2)
                {
                    constraints.Add(isXor);
                }
                */


                //constraints.Add(Implies( line.Operands[1].IsConstant, line.Operands[1].ConcreteValue != 0));

                foreach (var component in components)
                {
                    for (int opcodeIndex = 0; opcodeIndex < component.Opcodes.Length; opcodeIndex++)
                    {
                        var opc = component.Opcodes[opcodeIndex];
                        //var matches = line.ComponentOpcode == opcodeIndex;
                        var matches = IsInstance(line, opc);


                        bool pruneRhs = true;
                        if (pruneRhs && opc.GetOperandCount() == 1)
                        {
                            // TODO: Maybe we could instead make this a constant?
                            constraints.Add(Implies(matches, line.Operands[1].Index == 0));

                            // this does seem to speed things up
                            constraints.Add(Implies(matches, line.Operands[1].IsConstant == false));
                        }

                        // For some reason this heavily degrades performance.
                        bool foldTrivialConstantIdentities = false;
                        if (foldTrivialConstantIdentities && opc.GetOperandCount() == 2)
                        {
                            // Ban trivial expressions: (a&0), (a|0), (a|0)
                            constraints.Add(Implies(matches & line.Operands[1].IsConstant, line.Operands[1].ConcreteValue != 0));

                            // Ban (a&-1), (a|-1)
                            var uMax = ModuloReducer.GetMask((uint)line.Operands[1].ConcreteValue.Sort.BvSize);
                            if (opc == SynthOpc.Or || opc == SynthOpc.And)
                                constraints.Add(Implies(matches & line.Operands[1].IsConstant, line.Operands[1].ConcreteValue != uMax));
                        }


                        var sameType = (line.Operands[0].IsConstant == line.Operands[1].IsConstant);
                        // 
                        bool optCommutative = true;
                        if (optCommutative && opc.IsCommutative())
                        {
                            constraints.Add(Implies(matches & sameType, line.Operands[0].Index < line.Operands[1].Index));

                            // TODO: If the operation is commutative and only one operand is a constant, move the constant to the right.
                            constraints.Add(~(matches & line.Operands[0].IsConstant & ~line.Operands[1].IsConstant));
                        }

                        bool optOrder = true;
                        if (optOrder && lineIdx != FirstInstIdx)
                        {
                            var prevIdx = lineIdx - 1;
                            var prev = lines[lineIdx - 1];
                            // For each operand, assert that the operand is not the previous construction
                            var depConstraints = new List<Term>();
                            for (int i = 0; i < opc.GetOperandCount(); i++)
                            {
                                var different = line.Operands[i].IsConstant | (line.Operands[i].Index != prevIdx);
                                depConstraints.Add(different);
                            }

                            var isIndependent = matches & And(depConstraints);
                            var sameOpcode = line.ComponentOpcode == prev.ComponentOpcode;

                            // Sort by opcode
                            constraints.Add(Implies(isIndependent, line.ComponentOpcode >= prev.ComponentOpcode));

                            // If they have identical opcodes, 
                            var comb0 = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_CONCAT, toBv(prev.Operands[0].IsConstant), toBv(prev.Operands[1].IsConstant), prev.Operands[0].Index, prev.Operands[1].Index);
                            var comb1 = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_CONCAT, toBv(line.Operands[0].IsConstant), toBv(line.Operands[1].IsConstant), line.Operands[0].Index, line.Operands[1].Index);
                            var tie = matches & sameOpcode;

                            constraints.Add(Implies(tie, comb0 <= comb1));


                            //var (j, k) = prev.Operands[0].Index

                            //var tie = isIndependent & sameOpcode;
                            //var ags0 = prev.Operands.Select(x => x.)



                            //var same = line.ComponentOpcode == next.ComponentOpcode;
                        }

                        if (!opc.IsIdempotent())
                            continue;

                        // If both operands have the same type, their indices must differ.
                        bool idempotencyOpt = true;
                        if (idempotencyOpt)
                        {
                            var isIdempotent = matches & sameType;
                            constraints.Add(Implies(isIdempotent, line.Operands[0].Index != line.Operands[1].Index));
                        }
                    }

                }
            }

            // Constrain the number of multipliers
            //constraints.Add(sum <= 5);
        }

        private void AddLimitConstraints(List<Term> constraints)
        {
            /*
            var size = lines.Count - FirstInstIdx;
            var zero = ctx.MkBvValue(0, (ulong)size);
            var one = ctx.MkBvValue(1, (ulong)size);
            var sums = Opcodes.Select(x => zero).ToArray();
            for(int i = FirstInstIdx; i < lines.Count; i++)
            {
                var line = lines[i];
                for(int opcodeIdx = 0; opcodeIdx < Opcodes.Count; opcodeIdx++)
                {
                    var isTarget = IsInstance(line, Opcodes[opcodeIdx]);
                    var cost = ctx.MkIte(isTarget, one, zero);

                    sums[opcodeIdx] += cost;
                }
            }
            */

            var size = lines.Count - FirstInstIdx;
            var zero = ctx.MkBvValue(0, (ulong)size);
            var one = ctx.MkBvValue(1, (ulong)size);
            var sums = components.Select(x => zero).ToArray();

            foreach (var line in RealLines)
            {
                for (int i = 0; i < components.Count; i++)
                {
                    var component = components[i];
                    foreach (var opcode in component.Opcodes)
                    {
                        var isTarget = IsInstance(line, opcode);
                        var cost = ctx.MkIte(isTarget, one, zero);
                        sums[i] += cost;
                    }
                }
            }

            for (int i = 0; i < components.Count; i++)
            {
                var component = components[i];
                var data = component.Data;
                // Assert no limit
                if (data.MaxInstances == -1)
                    continue;

                constraints.Add(sums[i] <= (ulong)data.MaxInstances);
                //constraints.Add(sums[i] == (ulong)data.MaxInstances);
            }

        }

        private Term IsComponent(SynthLine line, SynthComponent component)
        {
            throw new InvalidOperationException();
            //return line.ComponentIndex == components.IndexOf(component);
        }

        private Term IsInstance(SynthLine line, SynthOpc opcode)
        {
            var index = Opcodes.IndexOf(opcode);
            if (index == -1)
                throw new InvalidOperationException();
            if (opcode != Opcodes.Last())
                return line.ComponentOpcode == index;

            return line.ComponentOpcode >= (ulong)index;
        }



        // Implements CEGIS(T)
        // https://www.kroening.com/papers/cav2018-synthesis.pdf
        private void CegisT(List<Term> constraints, Term skeleton)
        {
            // Randomly evaluate the expression on N initial points and assert its equivalence
            var rng = new SeededRandom();

            // New idea: All possible bitwise functions put in individual 
            var inputCombinations = new List<List<ulong>>()
            {
               // new() { 18446744073709551364, 248},
              //   new() { 18446744073709551421, 128},
              new() { 58229829, 160749783, 2180495597, 2149681939 },
               new() { 73896448, 2944159190, 2163435311, 3323985711 },
               //new() { 0, 0, 0, 0 },
              //new() { ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue },
            };



            inputCombinations = null;

            int NUMINPUTS = 1;


            bool minv = false;

            for (int i = 0; i < NUMINPUTS; i++)
            {
                Term[] values = null;
                if (inputCombinations == null)
                {
                    values = Enumerable.Range(0, symbols.Length)
                    .Select(x => ctx.MkBvValue(rng.GetRandUlong() & ModuloReducer.GetMask((uint)symbols[x].Sort.BvSize), symbols[x].Sort.BvSize))
                    .ToArray();
                }

                else
                {
                    values = Enumerable.Range(0, symbols.Length)
                   .Select(x => ctx.MkBvValue(inputCombinations[i][x] & ModuloReducer.GetMask((uint)symbols[x].Sort.BvSize), symbols[x].Sort.BvSize))
                   .ToArray();
                }

                if (minv)
                {
                    values[0] |= 1;
                    if ((i % 2) == 0)
                        values[0] = ctx.MkBvValue(ModuloReducer.GetMask((uint)i), symbols[0].Sort.BvSize);
                    else
                        values[0] = ctx.MkBvValue(ModuloReducer.GetMask(12 - (uint)i), symbols[0].Sort.BvSize);
                }




                var constraint = GetBehavioralConstraint(skeleton, values);
                constraints.Add(constraint);
            }

            var options = new Options();
            options.Set(BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS, true);

            bool abstraction = true;
            if (abstraction)
            {
                options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION, true);
                options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION_INC_BITBLAST, true);
                options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION_BV_SIZE, 32);
                options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION_INC_BITBLAST, true);
            }

            var s = new BvSolver(ctx, options);


            if (minv)
                constraints.Add((symbols[0] & 1) == 1);

            /*
            constraints.Add(constants[0] == 1);
            constraints.Add(constants[1] == 2);
            constraints.Add(constants[2] == 0x11111111);
            constraints.Add(constants[3] == 28);
            */

            /*
            constraints.Add(IsInstance(lines[6], SynthOpc.Mul));
            constraints.Add(lines[6].Operands[1].IsConstant);
            constraints.Add(lines[6].Operands[1].Index == 2);

            constraints.Add(lines[8].Operands[1].IsConstant);
            constraints.Add(lines[8].Operands[1].Index == 0);

            var skeletonOpcodes = new List<SynthOpc>()
            {
                SynthOpc.TruthTable,
                SynthOpc.Lshr,
                SynthOpc.Xor,
                SynthOpc.Lshr,
                SynthOpc.Xor,
                SynthOpc.And,
                SynthOpc.Mul,
                SynthOpc.Lshr,
                SynthOpc.And,
            };


            for (int i = FirstInstIdx; i < lines.Count; i++)
            {
                var tgt = skeletonOpcodes[i];
                Console.WriteLine($"lines{i} == {tgt}");
                constraints.Add(IsInstance(lines[i], tgt));
            }
            */

            foreach (var c in constraints)
                s.Assert(c);





            var totalTime = Stopwatch.StartNew();
            while (true)
            {
                var curr = Stopwatch.StartNew();
                s.Simplify();
                s.Write();
                var check = s.CheckSat();
                curr.Stop();


                if (check == Result.Unsat)
                {
                    Console.WriteLine($"No solution.  Took {totalTime.ElapsedMilliseconds}");
                    Debugger.Break();
                    return;
                }


                // Ask the solver for a fitting solution
                var (ourSolution, cegisSolution, cegisConstants) = SolutionToExpr(s);

                Console.WriteLine($"Found solution. Took {curr.ElapsedMilliseconds}ms\n\n{ourSolution}\n\n\n");

                //if(curr.ElapsedMilliseconds >= 5000)
                if (false)
                {
                    Debugger.Break();
                }


                // Yield the solution if its equivalent
                options = new Options();
                options.Set(BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS, true);
                var temp = new BvSolver(ctx, options);

                if (minv)
                    temp.Assert((symbols[0] & 1) == 1);

                temp.Assert(~(groundTruth == cegisSolution));
                var isEquiv = temp.CheckSat() == Result.Unsat;
                if (isEquiv)
                {
                    Console.WriteLine($"Solved in total time {totalTime.ElapsedMilliseconds}ms");
                    Debugger.Break();
                }

                bool generalize = true;
                if (generalize)
                {
                    Console.WriteLine("Beginning generalization...");
                    var (generalizedSolution, generalizedBan) = Generalize(s, cegisSolution, cegisConstants);
                    Console.WriteLine("Finished generalization...");
                    Debug.Assert(generalizedSolution is null);
                    s.Assert(generalizedBan);
                    constraints.Add(generalizedBan);
                }
                var vs = symbols.Select(x => temp.GetValue(x)).ToArray();
                s.Assert(GetBehavioralConstraint(skeleton, vs));
                constraints.Add(GetBehavioralConstraint(skeleton, vs));

                // Reset to disable incremental solving
                //s = new BvSolver(ctx, options);
                //foreach (var c in constraints)
                //    s.Assert(c);

                //Console.WriteLine($"Equiv: {temp.CheckSat()}");
                //foreach(var symbol in symbols)
                //{
                //    Console.WriteLine($"Invalid input: {ctx.GetIntegerValue(temp.GetValue(symbol))}");
                //}

                //Debugger.Break();
                // Otherwise we found a solution.
            }
        }

        // Constrain that expr1(x0, x1) == expr2(x0, x1) on some concrete inputs
        private Term GetBehavioralConstraint(Term skeleton, Term[] points)
        {
            var before = ctx.SubstituteTerm(groundTruth, symbols, points);
            var after = ctx.SubstituteTerm(skeleton, symbols, points);
            return before == after;
        }

        private (AstIdx ourSolution, Term cegisSolution, List<Term> constants) SolutionToExpr(BvSolver s)
        {
            // Compute the list of constant terms
            List<Term> cegisConstants = new();
            List<AstIdx> ourConstants = new();
            for (int i = 0; i < config.MaxConstants; i++)
            {
                var eval = s.GetValue(constants[i]);

                var w = constants[i].Sort.BvSize;
                var myConstant = ctx.GetIntegerValue(eval);
                ourConstants.Add(mbaCtx.Constant(myConstant, (byte)w));
                cegisConstants.Add(eval);
            }

            foreach (var line in lines)
            {
                if (line.IsSymbol)
                    continue;

                var a = s.GetValue(line.ComponentOpcode);
                //var b = s.GetValue(line.ComponentIndex);
                Console.WriteLine($"{a}");
            }

            // Compute the list of nodes
            List<Term> cegisNodes = new();
            List<AstIdx> ourNodes = new();
            for (int li = 0; li < lines.Count; li++)
            {
                var line = lines[li];
                if (line.IsSymbol)
                {
                    cegisNodes.Add(symbols[li]);
                    ourNodes.Add(mbaVariables[li]);
                    continue;
                }

                //var index = (int)ctx.GetIntegerValue(s.GetValue(line.ComponentIndex));
                var opcode = ctx.GetIntegerValue(s.GetValue(line.ComponentOpcode));
                if (opcode >= (ulong)Opcodes.Count)
                    opcode = (ulong)Opcodes.Count - 1;

                var cegisOperands = new List<Term>();
                var ourOperands = new List<AstIdx>();
                foreach (var operand in line.Operands)
                {
                    var isConstant = ctx.GetBoolValue(s.GetValue(operand.IsConstant));
                    var operandIndex = (int)ctx.GetIntegerValue(s.GetValue(operand.Index));

                    var cegisOperand = isConstant ? cegisConstants[operandIndex] : cegisNodes[operandIndex];
                    cegisOperands.Add(cegisOperand);

                    var ourOperand = isConstant ? ourConstants[operandIndex] : ourNodes[operandIndex];
                    ourOperands.Add(ourOperand);
                }

                var op0 = () => ourOperands[0];
                var op1 = () => ourOperands[1];

                var opc = Opcodes[(int)opcode];
                AstIdx ourNode = opc switch
                {
                    SynthOpc.Not => mbaCtx.Neg(op0()), // Neg() is actually bvnot in my IR
                    SynthOpc.And => mbaCtx.And(op0(), op1()),
                    SynthOpc.Or => mbaCtx.Or(op0(), op1()),
                    SynthOpc.Xor => mbaCtx.Xor(op0(), op1()),
                    SynthOpc.Add => mbaCtx.Add(op0(), op1()),
                    // Note: My IR does not have a subtract operator. `a-b` becomes `a + -1*b`. This may cause weird printed output but is fine otherwise.
                    SynthOpc.Sub => mbaCtx.Sub(op0(), op1()),
                    SynthOpc.Mul => mbaCtx.Mul(op0(), op1()),
                    SynthOpc.Lshr => mbaCtx.Lshr(op0(), op1()),
                    SynthOpc.Shl => mbaCtx.Symbol("SHL_PLACEHOLDER", mbaCtx.GetWidth(op0())),
                    _ => throw new NotImplementedException(),
                };
                ourNodes.Add(ourNode);


                Term cegisNode = ApplyOperator(opc, cegisOperands);
                cegisNodes.Add(cegisNode);
            }

            //Debugger.Break();
            return (ourNodes.Last(), cegisNodes.Last(), cegisConstants);
        }

        private (Term generalizedSolution, Term generalizedConstraints) Generalize(BvSolver oldModel, Term candidate, List<Term> cegisConstants)
        {
            // Replace the constants with symbolic holes
            var skeleton = ctx.SubstituteTerm(candidate, cegisConstants.ToArray(), constants.ToArray());


            var options = new Options();
            options.Set(BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS, true);
            var solver = new BvSolver(ctx, options);


            // Instantiate new quantifier variables.
            var quantVars = new List<Term>();
            for (int i = 0; i < symbols.Length; i++)
            {
                var v = ctx.MkVar(symbols[i].Sort, mbaCtx.GetSymbolName(mbaVariables[i]));
                quantVars.Add(v);
            }

            // Substitute the global constants (symbols) with the bound variables in the check
            var groundTruthBody = ctx.SubstituteTerm(groundTruth, symbols, quantVars.ToArray());
            var skeletonBody = ctx.SubstituteTerm(skeleton, symbols, quantVars.ToArray());

            var equality = groundTruthBody == skeletonBody;
            var concat = quantVars.Append(equality).ToArray();
            var forall = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_FORALL, concat);


            solver.Assert(forall);

            solver.Write();

            solver.Write();

            var res = solver.CheckSat();
            if (res == Result.Sat)
                Debugger.Break();

            // Otherwise this solution is impossible.
            List<Term> structureVars = new();
            foreach (var line in lines)
            {
                if (line.IsSymbol)
                    continue;

                //structureVars.Add(line.ComponentIndex);
                structureVars.Add(line.ComponentOpcode);
                foreach (var operand in line.Operands)
                {
                    structureVars.Add(operand.Index);
                    structureVars.Add(operand.IsConstant);
                }
            }

            List<Term> structureConstraints = new();
            foreach (var svar in structureVars)
            {
                var eval = oldModel.GetValue(svar);
                if (eval.Kind != BitwuzlaKind.BITWUZLA_KIND_VALUE)
                    Debugger.Break();

                if (eval.Sort.IsBv)
                    structureConstraints.Add(svar == ctx.GetIntegerValue(eval));
                else
                    structureConstraints.Add(svar == ctx.GetBoolValue(eval));
            }

            //Debugger.Break();


            return (null, ~And(structureConstraints));
        }



        private Term Implies(Term a, Term b)
            => ctx.MkImplies(a, b);

        private Term Or(IEnumerable<Term> terms)
            => MkBw(BitwuzlaKind.BITWUZLA_KIND_OR, terms);

        private Term And(IEnumerable<Term> terms)
            => MkBw(BitwuzlaKind.BITWUZLA_KIND_AND, terms);

        // Bitwise constructor operator that allows passing less than 2 operands.
        private Term MkBw(BitwuzlaKind kind, IEnumerable<Term> terms)
        {
            var c = terms.Count();
            if (c == 0)
                throw new InvalidOperationException();
            if (c == 1)
                return terms.Single();
            return ctx.MkTerm(kind, terms);
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

            var config = new SynthConfig(components, 5, 0);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PDemo()
        {
            var (ctx, idx) = Parse("(a&b) + 255", 8);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                new(SynthOpc.Add, SynthOpc.Sub),
            };

            var config = new SynthConfig(components, 4, 2);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void P1()
        {
            var (ctx, idx) = Parse("~(a|b|c|d|e|f|g)", 8);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 14, 0);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void P2()
        {
            var (ctx, idx) = Parse("(((x|1111)+y)^y)", 64);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                new(SynthOpc.Add, SynthOpc.Sub),
            };

            var config = new SynthConfig(components, 5, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void P3()
        {
            //var (ctx, idx) = Parse("(a|b|c|d) + (a+1111)", 8);

            // 3000s initially
            var (ctx, idx) = Parse("(((a^b)) - ((c&d))) + (b&111)", 16);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),
                //new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Add, SynthOpc.Sub),
            };

            var config = new SynthConfig(components, 9, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void P4()
        {
            var (ctx, idx) = Parse("(a+b)-c", 8);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                new(SynthOpc.Add, SynthOpc.Sub),

            };

            var config = new SynthConfig(components, 5, 0);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }


        public static void P5()
        {
            var (ctx, idx) = Parse("(171^((a+23)^(b)))^((((a|1111)+b)^b))", 32);

            // Works with 7 components and 3 constants. 500ms
            //var (ctx, idx) = Parse("(((a+23)^(b)))^((((a|1111)+b)))", 8);

            //var (ctx, idx) = Parse("(((a+23423434)^(b)))^((((a|432324234)+b)))^343433", 8);

            var components = new List<SynthComponent>()
            {
                // new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Or, SynthOpc.Xor, SynthOpc.Add),

                new(new ComponentData(4), SynthOpc.Or),
                new(new ComponentData(4), SynthOpc.Xor),
                new(new ComponentData(4), SynthOpc.Add),

            };

            var config = new SynthConfig(components, 9, 3);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }



        // P14 from brahma
        public static void P14()
        {
            var (ctx, idx) = Parse("((x&y) + (((x^y)) >> 1))", 64);

            //var (ctx, idx) = Parse("(x^y)", 8);

            //var (ctx, idx) = Parse("(((x^y)) & a)", 8); // fails with 4/5 comps

            //var (ctx, idx) = Parse("(((x^y)) & z)", 8);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.Add, SynthOpc.Sub),

                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor, SynthOpc.Lshr, SynthOpc.Add),
                //new(SynthOpc.And, SynthOpc.Xor),

                new SynthComponent(new ComponentData(1), SynthOpc.And),
                new SynthComponent(new ComponentData(1), SynthOpc.Xor),
                new SynthComponent(new ComponentData(1), SynthOpc.Lshr),
                new SynthComponent(new ComponentData(1), SynthOpc.Add),

            };

            var config = new SynthConfig(components, 6, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void P15()
        {
            //var (ctx, idx) = Parse("((x | (x^y)) - (((x^y)) >> 1))", 64);


            //var (ctx, idx) = Parse("(x^y)", 8);

            //var (ctx, idx) = Parse("(((x^y)) & a)", 8); // fails with 4/5 comps

            //var (ctx, idx) = Parse("(((x^y)) & z)", 8);

            var (ctx, idx) = Parse("(x|y) - ((x^y) >> 1)", 64);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.Add, SynthOpc.Sub),

                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Lshr, SynthOpc.Sub),
                new(SynthOpc.Or, SynthOpc.Xor, SynthOpc.Lshr, SynthOpc.Sub),
                //new(SynthOpc.And, SynthOpc.Xor),

            };

            var config = new SynthConfig(components, 6, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void P22()
        {
            // This formula might be wrong
            var (ctx, idx) = Parse("(((((v ^ (v >> 1)) ^ ((v ^ (v >> 1)) >> 2)) & 0x11111111) * 0x11111111) >> 28) & 1", 32);


            //var (ctx, idx) = Parse("(x^y)", 8);

            //var (ctx, idx) = Parse("(((x^y)) & a)", 8); // fails with 4/5 comps

            //var (ctx, idx) = Parse("(((x^y)) & z)", 8);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.Add, SynthOpc.Sub),

                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                // new(SynthOpc.And, SynthOpc.Xor, SynthOpc.Lshr, SynthOpc.Mul),
                //new(SynthOpc.Xor, SynthOpc.Lshr, SynthOpc.Mul, SynthOpc.And),
                //new(SynthOpc.And, SynthOpc.Xor),

                
                new SynthComponent(new ComponentData(1), SynthOpc.Mul),
                new SynthComponent(new ComponentData(2), SynthOpc.Xor),
                new SynthComponent(new ComponentData(2), SynthOpc.And),
                new SynthComponent(new ComponentData(3), SynthOpc.Lshr),

            };

            var config = new SynthConfig(components, 9, 4);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        // Modular oiinverse
        public static void Pminv()
        {
            // 6 lines
            var (ctx, idx) = Parse("((x ^ 60) * ((82 - (x * (x ^ 60)))))", 64);

            //var (ctx, idx) = Parse("(((3*a)^2)*(1 + (1 - a*((3*a)^2))))*(1 + (1 - a*((3*a)^2))*(1 - a*((3*a)^2)))", 8);


            //var (ctx, idx) = Parse("(x^y)", 8);

            //var (ctx, idx) = Parse("(((x^y)) & a)", 8); // fails with 4/5 comps

            //var (ctx, idx) = Parse("(((x^y)) & z)", 8);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.Add, SynthOpc.Sub),

                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                // new(SynthOpc.And, SynthOpc.Xor, SynthOpc.Lshr, SynthOpc.Mul),
               // new(SynthOpc.Sub, SynthOpc.Add, SynthOpc.Mul, SynthOpc.And, SynthOpc.Xor),
               new(SynthOpc.Sub, SynthOpc.Add, SynthOpc.Mul, SynthOpc.And, SynthOpc.Or, SynthOpc.Not, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),

            };

            // works for 8-bit with {SUB, ADD, MUL, AND, XOR}
            var config = new SynthConfig(components, 5, 2);
            //var config = new SynthConfig(components, 10, 3);

            //var config = new SynthConfig(components, 11, 4);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }


        public static void Phardboolean()
        {
            var (ctx, idx) = Parse("(x0^x1^x2^x3)&(x3|(x4|x5&x6))", 1);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 14, 0);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PMediumBoolean()
        {
            //var (ctx, idx) = Parse("(a|b|c|d|e)&f", 1);

            // ~(a|b|c|d|e|f|g)
            //var (ctx, idx) = Parse("~(((a|b))&c)", 1);
            //var (ctx, idx) =  Parse("~(((a|b|c|d|e|f|g))&h)", 1);

            var (ctx, idx) = Parse("(x0^x1^x2^x3)&(x3|(x4|x5&x6))", 1);

            //var (ctx, idx) = Parse("(x0^x1^x2^x3)&(x3|(x4|x5&x6))", 1);
            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),

                new(new ComponentData(6), SynthOpc.And),
                new(new ComponentData(6), SynthOpc.Or),
                new(new ComponentData(6), SynthOpc.Xor),
                new(new ComponentData(6), SynthOpc.Not),
                //new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 14, 0);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PReallyHardBoolean()
        {
            var (ctx, idx) = Parse("(x0^x1^x2^x3)&(x3|(x4|x5&x6))|x7|x8|x9", 32);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 20, 0);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }


        public static void PImpossibleBoolean()
        {
            var (ctx, idx) = Parse("(~((((((c^d)&(~(a^f)))|((((d&c)^(f&c))^(f&d))^c))|(f&(a^d)))^(b&((((f&(~c))&a)|((f&(~d))&a))|((((d&c)^(f&c))^(f&d))^f))))^(e&(((d&c)|(((((f&c)^(f&d))^a)^c)^d))^(b&((((~c)&(a^f))|(~((((d&a)^(f&c))^a)^d)))|(f&d)))))))", 1);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 25, 0);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }


        public static void PFastSynth()
        {
            var (ctx, idx) = Parse("15795372935317283107 + parameter0 + -(34359717887 & parameter0 ^ 9511600802393731071)", 64);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),
                //new(SynthOpc.Add),

                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Sub, SynthOpc.Add),

                //new(SynthOpc.Or, SynthOpc.Sub, SynthOpc.Not),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 5, 3);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PMatteo()
        {
            var (ctx, idx) = Parse("((b ^ ((c + d) ^ (7992590397050383240))) + ((a & (134217727)) << 5)) & 4294967295", 64);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),
                //new(SynthOpc.Add),

                //new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Sub, SynthOpc.Add, SynthOpc.Shl),
                //new(new ComponentData(3), SynthOpc.Not),
                new(new ComponentData(3), SynthOpc.And),
                 //new(new ComponentData(3), SynthOpc.Or),
                new(new ComponentData(3), SynthOpc.Xor),
                 new(new ComponentData(3), SynthOpc.Sub),
                new(new ComponentData(3), SynthOpc.Add),
                 new(new ComponentData(3), SynthOpc.Shl),
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Add, SynthOpc.Shl),


                //new(SynthOpc.Or, SynthOpc.Sub, SynthOpc.Not),
                // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),

                // Optional
                //new(new ComponentData(), SynthOpc.Not),
                //new(new ComponentData(), SynthOpc.Or),

                /*
                new(new ComponentData(2), SynthOpc.And),

                new(new ComponentData(2), SynthOpc.Xor),
                new(new ComponentData(2), SynthOpc.Add),

                new(new ComponentData(2), SynthOpc.Shl),
                */
            };

            var config = new SynthConfig(components, 11, 4);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PBenchSlot()
        {
            var (ctx, idx) = Parse("(x^y) & (15795372935317283107 + parameter0 + -(34359717887 & parameter0 ^ 9511600802393731071))", 64);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),
                //new(SynthOpc.Add),

                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Sub, SynthOpc.Add, SynthOpc.Lshr),

                //new(SynthOpc.Or, SynthOpc.Sub, SynthOpc.Not),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 8, 3);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }


        public static void PBSwap()
        {
            //  var (ctx, idx) = Parse("((val & 0x000000FF) << 24) | ((val & 0x0000FF00) << 8)  | ((val & 0x00FF0000) >> 8)  | ((val & 0xFF000000) >> 24)", 32);
            var (ctx, idx) = Parse("(val << 24) | ((val << 8) & 0x00FF0000) | ((val >> 8) & 0x0000FF00) | (val >> 24)", 32);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),
                //new(SynthOpc.Add),

                new(new ComponentData(4), SynthOpc.Lshr),
                new(new ComponentData(4), SynthOpc.Or),
                new(new ComponentData(4), SynthOpc.And),
                new(new ComponentData(4), SynthOpc.Shl),

                //new(SynthOpc.Or, SynthOpc.Sub, SynthOpc.Not),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 10, 4);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }


        public static void Ptest()
        {

            var (ctx, idx) = Parse("(x&87)", 8);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                new(SynthOpc.And),
                new(SynthOpc.Add),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 2, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();

            /*
            var (ctx, idx) = Parse("15795372935317283107 + parameter0 + -(34359717887 & parameter0 ^ 9511600802393731071)", 64);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                new(SynthOpc.And, SynthOpc.Xor),
                new(SynthOpc.Add),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 8, 3);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
            */
        }







        public static void PVerilog()
        {
            var text = "(((((1:i4&(in2:i4>>0:i4))^(1:i4&(in1:i4>>0:i4)))|(2:i4*((~((1:i4&(in2:i4>>0:i4))&(1:i4&(in1:i4>>0:i4))))^(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4)))))))|(4:i4*((~(((~((1:i4&(in2:i4>>0:i4))&(1:i4&(in1:i4>>0:i4))))|(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4)))))&(~((1:i4&(in2:i4>>1:i4))&(1:i4&(in1:i4>>1:i4))))))^((1:i4&(in2:i4>>2:i4))^(1:i4&(in1:i4>>2:i4))))))|(8:i4*((~(((~(((~((1:i4&(in2:i4>>0:i4))&(1:i4&(in1:i4>>0:i4))))|(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4)))))&(~((1:i4&(in2:i4>>1:i4))&(1:i4&(in1:i4>>1:i4))))))&((1:i4&(in2:i4>>2:i4))^(1:i4&(in1:i4>>2:i4))))|((1:i4&(in2:i4>>2:i4))&(1:i4&(in1:i4>>2:i4)))))^(~((1:i4&(in2:i4>>3:i4))^(1:i4&(in1:i4>>3:i4)))))))";

            text = "(4:i4*((~(((~((1:i4&(in2:i4>>0:i4))&(1:i4&(in1:i4>>0:i4))))|(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4)))))&(~((1:i4&(in2:i4>>1:i4))&(1:i4&(in1:i4>>1:i4))))))^((1:i4&(in2:i4>>2:i4))^(1:i4&(in1:i4>>2:i4)))))";

            text = "((2:i4*((~(1:i4&((in2:i4&in1:i4)>>0:i4)))^(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4))))))+(8:i4*((~(1:i4&(((in2:i4&in1:i4)>>2:i4)|((((1:i4&(in2:i4>>1:i4))|(1:i4&(in1:i4>>1:i4)))&(((in2:i4&in1:i4)>>1:i4)|((in2:i4&in1:i4)>>0:i4)))&((in1:i4|in2:i4)>>2:i4)))))^(~((1:i4&(in2:i4>>3:i4))^(1:i4&(in1:i4>>3:i4)))))))";

            text = "((((a:i8&b:i8)>>7:i8)&((1:i8&(a:i8>>6:i8))^(1:i8&(b:i8>>6:i8))))|((~((1:i8&((a:i8&b:i8)>>6:i8))&(((a:i8&b:i8)>>4:i8)|(((a:i8&b:i8)>>3:i8)|(((a:i8&b:i8)>>2:i8)|(((a:i8&b:i8)>>1:i8)|((a:i8&b:i8)>>5:i8)))))))&((~(1:i8&((a:i8&b:i8)>>7:i8)))&((1:i8&(a:i8>>6:i8))^((1:i8&(b:i8>>6:i8))^(1:i8&(((a:i8&b:i8)>>5:i8)|((((a:i8|b:i8)>>5:i8)&((a:i8|b:i8)>>4:i8))&(((a:i8&b:i8)>>4:i8)|(((a:i8|b:i8)>>3:i8)&(1:i8&((((a:i8&b:i8)>>3:i8)|((a:i8&b:i8)>>2:i8))|((((a:i8&b:i8)>>1:i8)|((a:i8&b:i8)>>0:i8))&(((a:i8|b:i8)>>1:i8)&((a:i8|b:i8)>>2:i8)))))))))))))))";

            text = "(32:i8*((1:i8&(a:i8>>5:i8))^((1:i8&(b:i8>>5:i8))^(1:i8&((~(1:i8&((a:i8&b:i8)>>7:i8)))&((((a:i8&b:i8)>>4:i8)|(((a:i8|b:i8)>>3:i8)&(1:i8&((((a:i8&b:i8)>>3:i8)|((a:i8&b:i8)>>2:i8))|((((a:i8&b:i8)>>1:i8)|((a:i8&b:i8)>>0:i8))&(((a:i8|b:i8)>>1:i8)&((a:i8|b:i8)>>2:i8)))))))&((~((1:i8&((a:i8&b:i8)>>6:i8))&(((a:i8&b:i8)>>4:i8)|(((a:i8&b:i8)>>3:i8)|(((a:i8&b:i8)>>2:i8)|(((a:i8&b:i8)>>1:i8)|((a:i8&b:i8)>>5:i8)))))))&((a:i8|b:i8)>>4:i8))))))))";

            text = "(1:i8&((((a:i8&b:i8)>>3:i8)|((a:i8&b:i8)>>2:i8))|((((a:i8&b:i8)>>1:i8)|((a:i8&b:i8)>>0:i8))&(((a:i8|b:i8)>>1:i8)&((a:i8|b:i8)>>2:i8)))))";

            text = "((2:i4*((~(1:i4&((in2:i4&in1:i4)>>0:i4)))^(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4))))))+(8:i4*((~(1:i4&(((in2:i4&in1:i4)>>2:i4)|((((1:i4&(in2:i4>>1:i4))|(1:i4&(in1:i4>>1:i4)))&(((in2:i4&in1:i4)>>1:i4)|((in2:i4&in1:i4)>>0:i4)))&((in1:i4|in2:i4)>>2:i4)))))^(~((1:i4&(in2:i4>>3:i4))^(1:i4&(in1:i4>>3:i4)))))))";

            text = "(((1:i4&(in2:i4>>1:i4))|(1:i4&(in1:i4>>1:i4)))&(((in2:i4&in1:i4)>>1:i4)|((in2:i4&in1:i4)>>0:i4)))";

            text = "(a > b) ? 1111 : 0";

            var (ctx, idx) = Parse(text, 4);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                new(SynthOpc.Add, SynthOpc.Sub),
                new (SynthOpc.Lshr),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 7, 3);
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
