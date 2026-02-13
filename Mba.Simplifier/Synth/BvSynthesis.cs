using Antlr4.Runtime.Tree;
using Bitwuzla;
using Mba.Common.Ast;
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
using System.Xml.Linq;

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

    public record SynthOptimizations();

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

        private readonly uint w;

        private readonly uint componentOpcodeSize;

        public BvSynthesis(SynthConfig config, AstCtx mbaCtx, AstIdx mbaIdx)
        {
            this.config = config;
            this.mbaCtx = mbaCtx;
            this.mbaIdx = mbaIdx;
            this.mbaVariables = mbaCtx.CollectVariables(mbaIdx).ToArray();
            this.components = config.Components;

            // Set the global width that all expressions use
            w = mbaVariables.Select(x => mbaCtx.GetWidth(x)).Append(mbaCtx.GetWidth(mbaIdx)).Max();

            // Zero extend the output if needed
            var outputWidth = mbaCtx.GetWidth(mbaIdx);
            if (w > outputWidth)
                mbaIdx = mbaCtx.Zext(mbaIdx, (byte)w);

            // Translate inputs to LLVM IR
            var translator = new BitwuzlaTranslator(mbaCtx, ctx);

            groundTruth = translator.Translate(mbaIdx);
            symbols = mbaCtx.CollectVariables(mbaIdx).Select(x => translator.Translate(x)).ToArray();

            // Get the minimum size bitvector needed to store the component index and component opcode
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
            => Console.WriteLine(x);

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
                line.ComponentOpcode = ctx.MkBvConst($"compCode{lineIndex}", componentOpcodeSize);
                line.Operands = new SynthOperand[MaxArity];
                var operandBitsize = BvWidth(Math.Max(lineIndex - 1, config.MaxConstants - 1));
                for (int i = 0; i < MaxArity; i++)
                {
                    var isConstant = config.MaxConstants == 0 ? ctx.MkFalse() : ctx.MkBoolConst($"line{lineIndex}_op{i}Const");
                    var operandIndex = ctx.MkBvConst($"line{lineIndex}_op{i}", operandBitsize);
                    // Sometimes this will emit useless zero extensions. Zext(a, 0)
                    // For some reason there are performance regressions with Bitwuzla if you remove this redundant zext. Specifically on the `PBenchSlot` benchmark
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
                SynthOpc.Lshr => (op0() >> (op1() & (op1().Sort.BvSize - 1))), // Truncate the shift width
                SynthOpc.Ashr => (op0() >>> (op1() & (op1().Sort.BvSize - 1))), // Truncate the shift width
                SynthOpc.Shl => (op0() << (op1() & (op1().Sort.BvSize - 1))),
                SynthOpc.Eq => ToBv(op0() == op1(), w),
                SynthOpc.Ult => ToBv(op0() < op1(), w),

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

        // Select one of N values using a chain of ITEs
        private Term LinearSelect(Term index, List<Term> options)
        {
            var n = options.Count;

            if (n == 0)
                throw new InvalidOperationException();
            if (n == 1)
                return options[0];

            var result = options[n - 1];
            for (int i = n - 2; i >= 0; i--)
            {
                var condition = index == ctx.MkBvValue(i, index.Sort.BvSize);
                result = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_ITE, condition, options[i], result);
            }

            return result;
        }

        // Select one of N values using a binary search
        private Term BinarySelect(Term index, List<Term> options, int offset, int count)
        {
            if (count == 1) return options[offset];

            int requiredBits = (int)Math.Ceiling(Math.Log2(count));
            int msbIndex = requiredBits - 1;
            int splitSize = 1 << msbIndex;
            int rightCount = count - splitSize;

            var condBit = ctx.MkExtract((uint)msbIndex, (uint)msbIndex, index);
            var condition = condBit == ctx.MkBvValue(1, 1);

            var lowResult = BinarySelect(index, options, offset, splitSize);
            var highResult = BinarySelect(index, options, offset + splitSize, rightCount);

            return ctx.MkIte(condition, highResult, lowResult);
        }

        private List<Term> GetProgramConstraints()
        {
            var constraints = new List<Term>();
            AddWfpConstraints(constraints);
            AddLivenessConstraints(constraints);
            AddPruningConstraints(constraints);
            AddSymmetricConstantsConstraint(constraints);
            //AddLimitConstraints(constraints);

            return constraints;
        }

        // Constrain the synthesis template to be a valid program
        private void AddWfpConstraints(List<Term> constraints)
        {
            for (int i = FirstInstIdx; i < lines.Count; i++)
            {
                var line = lines[i];

                // Each line can only refer to lines below it
                foreach (var operand in line.Operands)
                {
                    var ult = operand.Index <= (uint)(i - 1);
                    var opConstraint = Implies(~operand.IsConstant, ult);
                    // TODO: If the operand is a constant, maybe the bounds should be Min(i-1, config.MaxConstants)
                    var constConstraint = Implies(operand.IsConstant, operand.Index <= (uint)Math.Max((config.MaxConstants - 1), 0));

                    constraints.Add(opConstraint);
                    constraints.Add(constConstraint);
                }
            }

        }

        // Assert that the first constant must be used before the second constant.
        private void AddSymmetricConstantsConstraint(List<Term> constraints)
        {
            // All operands of the first instruction that are constants must use constant index 0.
            foreach (var operand in lines[FirstInstIdx].Operands)
            {
                constraints.Add(Implies(operand.IsConstant, operand.Index == 0));
            }

            // For the remaining operands, the constants must be used in ascending order
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
        }

        // Add constraints asserting that every instruction is used in the final computation
        // `skipVars` skips input variables
        private void AddLivenessConstraints(List<Term> constraints)
        {
            // TODO: If a constant is not used, maybe force it to zero?
            bool skipVars = true;
            for (int lineIdx = 0; lineIdx < lines.Count; lineIdx++)
            {
                if (lineIdx != lines.Count - 1)
                {
                    // TODO: For some reason we get worse results if we assert that each variable be used?
                    if (skipVars && lines[lineIdx].IsSymbol)
                        continue;

                    var usageConditions = new List<Term>();
                    for (int j = lineIdx + 1; j < lines.Count; j++)
                    {
                        if (lines[j].IsSymbol)
                            continue;

                        var operands = lines[j].Operands;
                        var used0 = (~operands[0].IsConstant) & (operands[0].Index == lineIdx);
                        var used1 = (~operands[1].IsConstant) & operands[1].Index == lineIdx;


                        usageConditions.Add(used0);
                        usageConditions.Add(used1);
                    }

                    var anyUses = Or(usageConditions);
                    constraints.Add(anyUses);
                }
            }

            return;
        }

        private void AddPruningConstraints(List<Term> constraints)
        {
            bool sortConstants = false;
            if (sortConstants)
            {
                for (int i = 1; i < constants.Count; i++)
                {
                    constraints.Add(constants[i] > constants[i - 1]);
                }
            }   

            // Constrain each opcode to be less than its maximum
            for (int lineIdx = FirstInstIdx; lineIdx < lines.Count; lineIdx++)
            {
                var line = lines[lineIdx];

                // The opcode must be valid
                constraints.Add(line.ComponentOpcode <= (uint)(Opcodes.Count - 1));

                bool limitConstantIndex = true;
                if (limitConstantIndex && constants.Count > 0)
                {
                    foreach (var operand in line.Operands)
                    {
                        constraints.Add(Implies(operand.IsConstant, operand.Index <= (uint)(constants.Count - 1)));
                    }
                }

                
                foreach (var component in components)
                {
                    for (int opcodeIndex = 0; opcodeIndex < component.Opcodes.Length; opcodeIndex++)
                    {
                        var opc = component.Opcodes[opcodeIndex];
                        var matches = IsComponent(line, opc);

                        // If enabled, require shift amounts to be constant and within the ranges of the bitwidth
                        bool constShiftsOnly = true;
                        if(constShiftsOnly && new SynthOpc[] { SynthOpc.Shl, SynthOpc.Lshr, SynthOpc.Ashr}.Contains(opc))
                        {
                            var maxW = (uint)mbaCtx.GetWidth(mbaIdx) - 1;
                            constraints.Add(Implies(matches, line.Operands[1].IsConstant));
                            constraints.Add(Implies(matches, line.Operands[1].ConcreteValue <= maxW));
                            constraints.Add(Implies(matches, line.Operands[1].ConcreteValue != 0));
                        }


                        // If the instruction only needs one operand, set the 2nd operand to zero.
                        bool pruneRhs = true;
                        if (pruneRhs && opc.GetOperandCount() == 1)
                        {
                            constraints.Add(Implies(matches, line.Operands[1].Index == 0));

                            // this does seem to speed things up
                            constraints.Add(Implies(matches, line.Operands[1].IsConstant == false));
                        }

                        bool constFold = true;


                        // Constant fold unary instrunctions
                        if (constFold)
                        {
                            if (opc.GetOperandCount() == 1)
                                constraints.Add(Implies(matches, line.Operands[0].IsConstant == false));
                            if (opc.GetOperandCount() == 2)
                                constraints.Add(Implies(matches, ~And(line.Operands.Select(x => x.IsConstant))));
                        }

                        // Rewrite (a - 1111) as (a + -1111)
                        bool canonicalizeConstSubtraction = true;
                        if (canonicalizeConstSubtraction)
                        {
                            if (opc == SynthOpc.Sub && HasComponent(SynthOpc.Add))
                            {
                                constraints.Add(Implies(matches, ~line.Operands[1].IsConstant));
                            }
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
                            var comb0 = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_CONCAT, ToBv(prev.Operands[0].IsConstant), ToBv(prev.Operands[1].IsConstant), prev.Operands[0].Index, prev.Operands[1].Index);
                            var comb1 = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_CONCAT, ToBv(line.Operands[0].IsConstant), ToBv(line.Operands[1].IsConstant), line.Operands[0].Index, line.Operands[1].Index);
                            var tie = matches & sameOpcode;

                            // CSE only helps if the CEGIS(T) opcode generalization is turned on
                            bool CSE = true;
                            if (CSE)
                                constraints.Add(Implies(tie, comb0 < comb1));
                            else
                                constraints.Add(Implies(tie, comb0 <= comb1));
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
        }

        private void AddLimitConstraints(List<Term> constraints)
        {
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
                        var isTarget = IsComponent(line, opcode);
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
            }
        }

        private Term IsComponent(SynthLine line, SynthOpc opcode)
        {
            var index = Opcodes.IndexOf(opcode);
            if (index == -1)
                throw new InvalidOperationException();
            if (opcode != Opcodes.Last())
                return line.ComponentOpcode == index;

            return line.ComponentOpcode >= (ulong)index;
        }

        private bool HasComponent(SynthOpc opcode)
        {
            return Opcodes.Contains(opcode);
        }

        // Implements CEGIS(T)
        // https://www.kroening.com/papers/cav2018-synthesis.pdf
        private void CegisT(List<Term> constraints, Term skeleton)
        {
            var options = new Options();
            options.Set(BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS, true);

            bool abstraction = true;
            if (abstraction)
            {
                options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION, true);
                options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION_INC_BITBLAST, true);
                options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION_BV_SIZE, 32);
                options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION_INC_BITBLAST, true);
                options.Set(BitwuzlaOption.BITWUZLA_OPT_SEED, 0);
            }

            var s = new BvSolver(ctx, options);

            foreach (var c in constraints)
                s.Assert(c);

            s.Write();


            var rng = new SeededRandom();
            var inputCombinations = new List<List<ulong>>();
            inputCombinations = null;

            int NUMINPUTS = 1;
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

                var constraint = GetBehavioralConstraint(skeleton, values);
                s.Assert(constraint);
            }

            var totalTime = Stopwatch.StartNew();
            while (true)
            {
                var curr = Stopwatch.StartNew();
                s.Write();
                var check = s.CheckSat();
                curr.Stop();


                if (check == Result.Unsat)
                {
                    Log($"No solution.  Took {totalTime.ElapsedMilliseconds}");
                    Debugger.Break();
                    return;
                }

                // Ask the solver for a fitting solution
                var (ourSolution, cegisSolution, cegisConstants) = SolutionToExpr(s);

                Log($"Found solution. Took {curr.ElapsedMilliseconds}ms with global time {totalTime.ElapsedMilliseconds}\n\n{ourSolution}\n\n\n");

                if (curr.ElapsedMilliseconds > 75000)
                    Debugger.Break();

                // Yield the solution if its equivalent
                options = new Options();
                options.Set(BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS, true);
                var temp = new BvSolver(ctx, options);

                temp.Assert(~(groundTruth == cegisSolution));
                var isEquiv = temp.CheckSat() == Result.Unsat;
                if (isEquiv)
                {
                    Log($"Solved in total time {totalTime.ElapsedMilliseconds}ms");
                    Debugger.Break();
                }

                bool generalize = false;
                if (generalize)
                {
                    Log("Beginning generalization...");
                    var sww = Stopwatch.StartNew();
                    var (generalizedSolution, generalizedBan) = Generalize(s, cegisSolution, cegisConstants, totalTime);

                    sww.Stop();
                    Log($"Generalizing took {sww.ElapsedMilliseconds}ms");

                    if (generalizedBan is not null)
                    {

                        Log("Finished generalization...");
                        Debug.Assert(generalizedSolution is null);
                        s.Assert(generalizedBan);
                        constraints.Add(generalizedBan);
                    }
                }


                // Probably need better heuristic for IO points?
                var vs = symbols.Select(x => temp.GetValue(x)).ToArray();
                s.Assert(GetBehavioralConstraint(skeleton, vs));
                constraints.Add(GetBehavioralConstraint(skeleton, vs));
            }
        }

        // Constrain that expr1(x0, x1) == expr2(x0, x1) on some concrete inputs
        private Term GetBehavioralConstraint(Term skeleton, Term[] points)
        {
            var before = ctx.SubstituteTerm(groundTruth, symbols, points);
            var after = ctx.SubstituteTerm(skeleton, symbols, points);
            return before == after;
        }

        // TODO: We're getting tons of identical duplicates even with CEGIS(T). I think the forall query is broken?
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

                Log($"const{i} = {myConstant}");
            }

            foreach (var line in lines)
            {
                if (line.IsSymbol)
                {
                    continue;
                }

                var a = s.GetValue(line.ComponentOpcode);
                Log($"{a}");
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
                    Log($"%{li} = {mbaCtx.GetSymbolName(mbaVariables[li])}\n");
                    continue;
                }

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
                    SynthOpc.Ashr => mbaCtx.Symbol("ASHR_PLACEHOLDER", mbaCtx.GetWidth(op0())),
                    SynthOpc.Shl => mbaCtx.Symbol("SHL_PLACEHOLDER", mbaCtx.GetWidth(op0())),
                    SynthOpc.Eq => mbaCtx.ICmp(Predicate.Eq, op0(), op1()),
                    SynthOpc.Ult => mbaCtx.ICmp(Predicate.Ult, op0(), op1()),
                    _ => throw new NotImplementedException(),
                };
                ourNodes.Add(ourNode);


                List<string> operandStrs = new();
                for (int i = 0; i < MaxArity; i++)
                {
                    var operand = line.Operands[i];
                    var isConstant = ctx.GetBoolValue(s.GetValue(operand.IsConstant));
                    var operandIndex = (int)ctx.GetIntegerValue(s.GetValue(operand.Index));
                    operandStrs.Add($"{isConstant} {operandIndex}");
                }

                Log($"%{li} = {opc}({String.Join(", ", operandStrs)})\n");

                Term cegisNode = ApplyOperator(opc, cegisOperands);
                cegisNodes.Add(cegisNode);
            }

            return (ourNodes.Last(), cegisNodes.Last(), cegisConstants);
        }

        private (Term generalizedSolution, Term generalizedConstraints) Generalize(BvSolver oldModel, Term candidate, List<Term> cegisConstants, Stopwatch totalTime)
        {
            // Replace the constants with symbolic holes
            var skeleton = ctx.SubstituteTerm(candidate, cegisConstants.ToArray(), constants.ToArray());

            var options = new Options();
            options.Set(BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS, true);
            options.Set(BitwuzlaOption.BITWUZLA_OPT_TIME_LIMIT_PER, 5000);
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

            var sw = Stopwatch.StartNew();
            var res = solver.CheckSat();
            if (res == Result.Sat)
            {
                totalTime.Stop();
                sw.Stop();
                Console.WriteLine($"Found global solution in {totalTime.ElapsedMilliseconds}ms. Solving generalized query took {sw.ElapsedMilliseconds}");
                Debugger.Break();
            }

            if (res == Result.Unknown)
            {
                Console.WriteLine("Generalization timed out.");
                return (null, null);
            }

            // Otherwise this solution is impossible.
            List<Term> structureVars = new();
            foreach (var line in lines)
            {
                if (line.IsSymbol)
                    continue;

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

            return (null, ~And(structureConstraints));
        }

        private Term ToBv(Term term, uint width = 1)
            => ctx.MkIte(term, ctx.MkBvValue(1, width), ctx.MkBvValue(0, width));

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
            var (ctx, idx) = Parse("(((a^b)) - ((c&d))) + (b&111)", 16);

            var components = new List<SynthComponent>()
            {
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

            var components = new List<SynthComponent>()
            {
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

            var components = new List<SynthComponent>()
            {
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
            var (ctx, idx) = Parse("(x|y) - ((x^y) >> 1)", 64);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.Or, SynthOpc.Xor, SynthOpc.Lshr, SynthOpc.Sub),
            };

            var config = new SynthConfig(components, 6, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void P22()
        {
            // This formula might be wrong
            var (ctx, idx) = Parse("(((((v ^ (v >> 1)) ^ ((v ^ (v >> 1)) >> 2)) & 0x11111111) * 0x11111111) >> 28) & 1", 32);

            var components = new List<SynthComponent>()
            {
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
            var (ctx, idx) = Parse("((x ^ 60) * ((82 - (x * (x ^ 60)))))", 64);

            var components = new List<SynthComponent>()
            {
               new(SynthOpc.Sub, SynthOpc.Add, SynthOpc.Mul, SynthOpc.And, SynthOpc.Or, SynthOpc.Not, SynthOpc.Xor),
            };

            var config = new SynthConfig(components, 5, 2);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PTestSymmetry()
        {
            var (ctx, idx) = Parse("a + b + (c&d) + 11111", 8);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Add, SynthOpc.Sub),
            };

            var config = new SynthConfig(components, 8, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }


        public static void PDebugZextIssue()
        {
            var (ctx, idx) = Parse("~((a|b)*342324342234234)", 64);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.And, SynthOpc.Or, SynthOpc.Mul, SynthOpc.Not),
            };

            var config = new SynthConfig(components, 5, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }



        public static void Phardboolean()
        {
            var (ctx, idx) = Parse("(x0^x1^x2^x3)&(x3|(x4|x5&x6))", 1);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
            };

            var config = new SynthConfig(components, 14, 0);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PMediumBoolean()
        {
            var (ctx, idx) = Parse("(x0^x1^x2^x3)&(x3|(x4|x5&x6))", 1);

            var components = new List<SynthComponent>()
            {
                new(new ComponentData(6), SynthOpc.And),
                new(new ComponentData(6), SynthOpc.Or),
                new(new ComponentData(6), SynthOpc.Xor),
                new(new ComponentData(6), SynthOpc.Not),
            };

            var config = new SynthConfig(components, 14, 0);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PReallyHardBoolean()
        {
            var (ctx, idx) = Parse("(x0^x1^x2^x3)&(x3|(x4|x5&x6))|x7|x8|x9", 1);

            var components = new List<SynthComponent>()
            {
                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
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
                new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Sub, SynthOpc.Add),
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
                new(new ComponentData(3), SynthOpc.And),
                new(new ComponentData(3), SynthOpc.Xor),
                new(new ComponentData(3), SynthOpc.Sub),
                new(new ComponentData(3), SynthOpc.Add),
                new(new ComponentData(1), SynthOpc.Shl),
            };

            var config = new SynthConfig(components, 11, 4);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PDebugZext()
        {
            var s0 = "-(~8830963753255973168|(~y&z)) + (z^(~8830963753255973168&(y|z))) - ~(8830963753255973168^z) + (y|~(8830963753255973168^z)) - 1";
            var s1 = "8830963753255973168 + y";

            s0 = "-7360133807098015136 + (1*(-1863238229756760676&x)) + (576460752303423487*(32&x)) + (288230376151711743*(64&x)) + (36028797018963967*(512&x)) + (4503599627370495*(4096&x)) + (1125899906842623*(16384&x)) + (70368744177663*(262144&x)) + (17592186044415*(1048576&x)) + (2199023255551*(8388608&x)) + (68719476735*(268435456&x)) + (17179869183*(1073741824&x)) + (1073741823*(17179869184&x)) + (536870911*(34359738368&x)) + (67108863*(274877906944&x)) + (16777215*(1099511627776&x)) + (4194303*(4398046511104&x)) + (2097151*(8796093022208&x)) + (131071*(140737488355328&x)) + (65535*(281474976710656&x)) + (32767*(562949953421312&x)) + (8191*(2251799813685248&x)) + (4095*(4503599627370496&x)) + (1023*(18014398509481984&x)) + (511*(36028797018963968&x)) + (255*(72057594037927936&x)) + (31*(576460752303423488&x)) + (15*(1152921504606846976&x))";
            s1 = "-7360133807098015136^(-4&x)";

            s0 = "((((x ^ 533433953090025345) ^ ~2477519675323023630) & 4390262060064730371) * 8506239995682776553) + ((((x ^ 533433953090025345) | ~2477519675323023630) & 4390262060064730371) * -8506239995682775442) + ((((x ^ 533433953090025345) | 2477519675323023630) ^ 4390262060064730371) * 4160415173633232112) + ((((x & 533433953090025345) & ~2477519675323023630) & 4390262060064730371) * -4160415173633233223) + ((((x ^ 533433953090025345) & ~2477519675323023630) & 4390262060064730371) * 7398805680029297517) + ((((x ^ ~533433953090025345) | 2477519675323023630) ^ 4390262060064730371) * 1107434315653479036) + ((((x | 533433953090025345) | 2477519675323023630) ^ 4390262060064730371) * 3557466608742890343) + ((((x | 533433953090025345) | 2477519675323023630) ^ 4390262060064730371) * -7717881782376123566) + ((((x ^ 533433953090025345) | 2477519675323023630) & ~4390262060064730371) * 7991277945930471858) + ((((x ^ ~533433953090025345) | 2477519675323023630) & ~4390262060064730371) * -9098712261583949783) + ((((~x ^ ~533433953090025345) | ~2477519675323023630) & ~4390262060064730371) * 923009115682583261) + ((((~x | ~533433953090025345) ^ ~2477519675323023630) & ~4390262060064730371) * -923009115682582150) + ((((x | 533433953090025345) ^ 2477519675323023630) & ~4390262060064730371) * 8056370110469764822) + ((((x | 533433953090025345) ^ 2477519675323023630) & ~4390262060064730371) * -7133360994787182672) + ((((x & 533433953090025345) & ~2477519675323023630) & ~4390262060064730371) * 8643096519935237325) + ((((x ^ ~533433953090025345) & ~2477519675323023630) & ~4390262060064730371) * 2585587483945883384) + ((((x ^ 533433953090025345) & ~2477519675323023630) & ~4390262060064730371) * 7669063500040012620) + ((((~x ^ ~533433953090025345) & ~2477519675323023630) & ~4390262060064730371) * 940384396373903949) + ((((~x & ~533433953090025345) & ~2477519675323023630) & ~4390262060064730371) * 819475353985819650) + ((((~x & ~533433953090025345) & ~2477519675323023630) & ~4390262060064730371) * 3663205992316184452)";
            s1 = "1111*(x^533433953090025345)";

            var (ctx, idx1) = Parse(s0, 48);
            var idx2 = RustAstParser.Parse(ctx, s1, 48);

            var tm = new TermManager();
            var translator = new BitwuzlaTranslator(ctx, tm);

            var before = translator.Translate(idx1);
            var after = translator.Translate(idx2);

            before = tm.MkZext(16, before);
            after = tm.MkZext(16, after);

            var solver = new BvSolver(tm);
            solver.Assert(before != after);

            solver.Write();

            var sw = Stopwatch.StartNew();
            var sat = solver.CheckSat();
            sw.Stop();

            Console.WriteLine($"{sat} in {sw.ElapsedMilliseconds}ms");

            Debugger.Break();


        }

        public static void PBenchSlot()
        {
            var (ctx, idx) = Parse("(x^y) & (15795372935317283107 + parameter0 + -(34359717887 & parameter0 ^ 9511600802393731071))", 64);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),
                //new(SynthOpc.Add),

                //new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Sub, SynthOpc.Add, SynthOpc.Lshr),

                new(new ComponentData(4), SynthOpc.Not),
                new(new ComponentData(4), SynthOpc.And),
                new(new ComponentData(4), SynthOpc.Or),
                new(new ComponentData(4), SynthOpc.Xor),
                new(new ComponentData(4), SynthOpc.Add),
                new(new ComponentData(4), SynthOpc.Sub),
                //new(new ComponentData(1), SynthOpc.Lshr),


                //new(SynthOpc.Or, SynthOpc.Sub, SynthOpc.Not),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 9, 3);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PBenchSlotSlightlyMoreTractable()
        {
            var (ctx, idx) = Parse("(x^y) & (15795372935317283107 + parameter0 + -(34359717887 & parameter0 ^ 9511600802393731071))", 64);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),
                //new(SynthOpc.Add),

                new(SynthOpc.And, SynthOpc.Xor, SynthOpc.Sub, SynthOpc.Add),

                //new(SynthOpc.Or, SynthOpc.Sub, SynthOpc.Not),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 9, 3);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }


        // Completes in 140s
        public static void PBSwap()
        {
            //  var (ctx, idx) = Parse("((val & 0x000000FF) << 24) | ((val & 0x0000FF00) << 8)  | ((val & 0x00FF0000) >> 8)  | ((val & 0xFF000000) >> 24)", 32);
            //     val = ((val << 8) & 0xFF00FF00 ) | ((val >> 8) & 0xFF00FF ); 
            //     return (val << 16) | (val >> 16);
            var (ctx, idx) = Parse("((((val << 8) & 0xFF00FF00 ) | ((val >> 8) & 0xFF00FF )) << 16) | ((((val << 8) & 0xFF00FF00 ) | ((val >> 8) & 0xFF00FF )) >> 16)", 32);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),
                //new(SynthOpc.Add),

                new(new ComponentData(2), SynthOpc.Lshr),
                new(new ComponentData(3), SynthOpc.Or),
                new(new ComponentData(3), SynthOpc.And),
                new(new ComponentData(4), SynthOpc.Shl),

                //new(SynthOpc.Or, SynthOpc.Sub, SynthOpc.Not),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 9, 4);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void PBSwapReduced()
        {
            //  var (ctx, idx) = Parse("((val & 0x000000FF) << 24) | ((val & 0x0000FF00) << 8)  | ((val & 0x00FF0000) >> 8)  | ((val & 0xFF000000) >> 24)", 32);
            var (ctx, idx) = Parse("((val << 8) & 0x00FF0000) | ((val >> 8) & 0x0000FF00)", 32);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),
                //new(SynthOpc.Add),

                new(new ComponentData(2), SynthOpc.Lshr),
                new(new ComponentData(3), SynthOpc.Or),
                new(new ComponentData(3), SynthOpc.And),
                new(new ComponentData(4), SynthOpc.Shl),

                //new(SynthOpc.Or, SynthOpc.Sub, SynthOpc.Not),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 7, 2);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }


        public static void PDebugShiftPerformance()
        {
            //  var (ctx, idx) = Parse("((val & 0x000000FF) << 24) | ((val & 0x0000FF00) << 8)  | ((val & 0x00FF0000) >> 8)  | ((val & 0xFF000000) >> 24)", 32);
            var (ctx, idx) = Parse("(x+y+111) >> 5", 32);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.And, SynthOpc.Xor),
                //new(SynthOpc.Add),

                new(new ComponentData(2), SynthOpc.Lshr),
                new(new ComponentData(3), SynthOpc.And),
                new(new ComponentData(3), SynthOpc.Or),
                 new(new ComponentData(3), SynthOpc.Add),
                new(new ComponentData(4), SynthOpc.Shl),

                //new(SynthOpc.Or, SynthOpc.Sub, SynthOpc.Not),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 5, 2);
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


        public static void PCmp()
        {
            var (ctx, idx) = Parse("(x+y) < z", 8);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                new(SynthOpc.Sub),
                new(SynthOpc.Add),
                new(SynthOpc.Eq),
                new(SynthOpc.Ult),
               // new(SynthOpc.Add, SynthOpc.Sub),
                //new(SynthOpc.Not, SynthOpc.Or),
            };

            var config = new SynthConfig(components, 5, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
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

            // Saw some shifts with > bitwidth on this one
            text = "((((1:i8&(a:i8>>2:i8))&(1:i8&(b:i8>>2:i8)))|(((1:i8&(a:i8>>2:i8))|(1:i8&(b:i8>>2:i8)))&(((1:i8&(a:i8>>1:i8))&(1:i8&(b:i8>>1:i8)))|(((1:i8&(a:i8>>0:i8))&(1:i8&(b:i8>>0:i8)))&((1:i8&(a:i8>>1:i8))|(1:i8&(b:i8>>1:i8)))))))&((1:i8&(a:i8>>3:i8))|(1:i8&(b:i8>>3:i8))))";

            text = "((~((1:i8&(a:i8>>7:i8))&(1:i8&(b:i8>>7:i8))))&(~(((1:i8&(a:i8>>6:i8))&(1:i8&(b:i8>>6:i8)))&((((1:i8&(a:i8>>4:i8))&(1:i8&(b:i8>>4:i8)))|((1:i8&(a:i8>>3:i8))&(1:i8&(b:i8>>3:i8))))|(((1:i8&(a:i8>>2:i8))&(1:i8&(b:i8>>2:i8)))|(((1:i8&(a:i8>>1:i8))&(1:i8&(b:i8>>1:i8)))|((1:i8&(a:i8>>5:i8))&(1:i8&(b:i8>>5:i8)))))))))";

            text = "((((1:i4&(in2:i4>>0:i4))^(1:i4&(in1:i4>>0:i4)))|(2:i4*((~((1:i4&(in2:i4>>0:i4))&(1:i4&(in1:i4>>0:i4))))^(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4)))))))|(4:i4*((~(((~((1:i4&(in2:i4>>0:i4))&(1:i4&(in1:i4>>0:i4))))|(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4)))))&(~((1:i4&(in2:i4>>1:i4))&(1:i4&(in1:i4>>1:i4))))))^((1:i4&(in2:i4>>2:i4))^(1:i4&(in1:i4>>2:i4))))))";

            text = "(8:i4*((~(((~(((~((1:i4&(in2:i4>>0:i4))&(1:i4&(in1:i4>>0:i4))))|(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4)))))&(~((1:i4&(in2:i4>>1:i4))&(1:i4&(in1:i4>>1:i4))))))&((1:i4&(in2:i4>>2:i4))^(1:i4&(in1:i4>>2:i4))))|((1:i4&(in2:i4>>2:i4))&(1:i4&(in1:i4>>2:i4)))))^(~((1:i4&(in2:i4>>3:i4))^(1:i4&(in1:i4>>3:i4))))))";

            // 4-bit adder circuit optimized using eqsat
            text = "(((2:i4*((~(1:i4&((in2:i4&in1:i4)>>0:i4)))^(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4))))))+(8:i4*((~(1:i4&(((in2:i4&in1:i4)>>2:i4)|((((in2:i4&in1:i4)>>1:i4)|((in2:i4&in1:i4)>>0:i4))&(((in2:i4|in1:i4)>>2:i4)&((in2:i4|in1:i4)>>1:i4))))))+(~((1:i4&(in2:i4>>3:i4))^(1:i4&(in1:i4>>3:i4)))))))+(((1:i4&(in2:i4>>0:i4))^(1:i4&(in1:i4>>0:i4)))+(4:i4*((1:i4&((((in2:i4&in1:i4)>>1:i4)|((in2:i4&in1:i4)>>0:i4))&((in2:i4|in1:i4)>>1:i4)))^((1:i4&(in2:i4>>2:i4))^(1:i4&(in1:i4>>2:i4)))))))";

            text = "((2:i4*((~(1:i4&((in2:i4&in1:i4)>>0:i4)))^(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4))))))+(8:i4*((~(1:i4&(((in2:i4&in1:i4)>>2:i4)|((((in2:i4&in1:i4)>>1:i4)|((in2:i4&in1:i4)>>0:i4))&(((in2:i4|in1:i4)>>2:i4)&((in2:i4|in1:i4)>>1:i4))))))+(~((1:i4&(in2:i4>>3:i4))^(1:i4&(in1:i4>>3:i4)))))))";

            text = "((2:i4*((~(1:i4&((in2:i4&in1:i4)>>0:i4)))^(~((1:i4&(in2:i4>>1:i4))^(1:i4&(in1:i4>>1:i4))))))+(8:i4*((~(1:i4&(((in2:i4&in1:i4)>>2:i4)|((((in2:i4&in1:i4)>>1:i4)|((in2:i4&in1:i4)>>0:i4))&(((in2:i4|in1:i4)>>2:i4)&((in2:i4|in1:i4)>>1:i4))))))+(~((1:i4&(in2:i4>>3:i4))^(1:i4&(in1:i4>>3:i4)))))))";

            var (ctx, idx) = Parse(text, 4);

            var components = new List<SynthComponent>()
            {
                new(new ComponentData(4), SynthOpc.And),
                new(new ComponentData(4), SynthOpc.Or),
                new(new ComponentData(4), SynthOpc.Xor),
                new(new ComponentData(4), SynthOpc.Add),
                new(new ComponentData(4), SynthOpc.Sub),

                //new(new ComponentData(2), SynthOpc.Ashr),
                new(new ComponentData(2), SynthOpc.Lshr),

            };

            var config = new SynthConfig(components, 4, 3);
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
