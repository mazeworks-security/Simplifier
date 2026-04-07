using Bitwuzla;
using Mba.Common.Ast;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Synth;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.VisualBasic;
using Microsoft.Z3;
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
        SynthOpc[] Opcodes,
        // Minimum number of instructions a solution must use
        int MinLength, 
        // Maximal number of instructions a solution may use
        int MaxLength, 
        // Maximum number of unique constants
        int MaxConstants
        );

    public class SynthComponent
    {
        // The possible instructions the component can choose from
        public SynthOpc[] Choices { get; set; }

        // Selector variable choosing which semantic(add, sub, etc) to assign to the component
        public Term Opcode { get; set; }

        public int NumOperands => Choices.MaxBy(x => x.GetOperandCount()).GetOperandCount();

        // Inputs and outputs should not be stored here... they need to be instantiated
    }

    // A component has multiple choices for an instruction
    // If we want to allow synthesizing variable length sequences, we 
    public class SynthLine
    {
        // Gets or sets whether the line is a symbol or instruction
        public bool IsSymbol { get; set; }

        // The index of the component
        public Term ComponentIdx { get; set; }

        // The operands of the component
        public LineOperand[] Operands { get; set; }
    }

    public class LineOperand
    {
        // Boolean variable indicating whether the first operand is a constant
        public Term IsConstant { get; }

        // The index of the operand. 
        public Term Index { get; }

        public LineOperand(Term isConstant, Term index)
        {
            IsConstant = isConstant;
            Index = index;
        }

        public override string ToString()
        {
            return $"(IsConstant: {IsConstant}) (Index: {Index})";
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

        // Get the index of the first instruction in lines
        private int FirstInstIdx => symbols.Length;

        // Get the max number of operands that one instruction may contain.
        private int MaxArity => components.Max(x => x.Choices.Max(x => x.GetOperandCount()));

        public List<SynthOpc> Opcodes => config.Opcodes.ToList();

        private readonly IReadOnlyList<SynthComponent> components;

        private List<SynthLine> lines;

        public IReadOnlyList<SynthLine> RealLines => lines.Skip(FirstInstIdx).ToList();

        private List<Term> constants;

        private readonly uint w;


        public HieraSynth(SynthConfig config, AstCtx mbaCtx, AstIdx mbaIdx)
        {
            this.config = config;
            this.mbaCtx = mbaCtx;
            this.mbaIdx = mbaIdx;
            this.mbaVariables = mbaCtx.CollectVariables(mbaIdx).ToArray();
            
            var numInstructions = config.MaxLength - mbaVariables.Length;
            var opcodeSelectorSize = (uint)BvWidth(config.Opcodes.Length - 1);

            this.components = Enumerable.Range(0, numInstructions).Select(x => new SynthComponent() { Choices = config.Opcodes, Opcode = ctx.MkBvConst($"comp{x}_code", opcodeSelectorSize) }).ToList();

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
        }

        public void Run()
        {
            // Get a list of lines
            lines = GetLines();
            constants = Enumerable.Range(0, config.MaxConstants).Select(x => ctx.MkBvConst($"const{x}", w)).ToList();



            var constraints = GetProgramConstraints();

            CegisT(constraints);

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

            var maxOperandSize = BvWidth(Math.Max(config.MaxLength - 2, config.MaxConstants - 1));

            // Get the minimum size bitvector needed to store the component index and component opcode
            var componentIndexSize = (uint)BvWidth(components.Count - 1);
            for (int lineIndex = lines.Count; lineIndex < config.MaxLength; lineIndex++)
            {
                var line = new SynthLine();
                line.IsSymbol = false;
                line.ComponentIdx = ctx.MkBvConst($"line{lineIndex}_compIdx", componentIndexSize);
                line.Operands = new LineOperand[MaxArity];
                var operandBitsize = BvWidth(Math.Max(lineIndex - 1, config.MaxConstants - 1));
                for (int i = 0; i < MaxArity; i++)
                {
                    var isConstant = config.MaxConstants == 0 ? ctx.MkFalse() : ctx.MkBoolConst($"line{lineIndex}_op{i}Const");
                    var operandIndex = ctx.MkBvConst($"line{lineIndex}_op{i}", operandBitsize);
                    // Sometimes this will emit useless zero extensions. Zext(a, 0)
                    // For some reason there are performance regressions with Bitwuzla if you remove this redundant zext. Specifically on the `PBenchSlot` benchmark
                    operandIndex = ctx.MkZext((uint)maxOperandSize - (uint)operandBitsize, operandIndex);

                    var operand = new LineOperand(isConstant, operandIndex);
                    line.Operands[i] = operand;
                }

                //line.Output = ctx.MkBvConst($"line{lineIndex}_output", w);

                lines.Add(line);
            }

            return lines;
        }

        public record ComponentInstance(Term[] inputs, Term output);
        public record LineInstance(Term output);

        int numInstances = 0;
        private (List<Term> constraints, List<Term> lineOutputs) GetDataflowConstraints()
        {
            // For each component instantiate an instance.
            var componentInstances = new List<ComponentInstance>();
            for(int i = 0; i < components.Count; i++)
            {
                var component = components[i];
                var operands = Enumerable.Range(0, component.NumOperands).Select(x => ctx.MkBvConst($"comp{i}_op{x}_instance{numInstances}", w)).ToList();
                var terms = new List<Term>();
                foreach (var opcode in component.Choices)
                {
                    var term = ApplyOperator(opcode, operands);
                    terms.Add(term);
                }

                var select = LinearSelect(component.Opcode, terms);
                componentInstances.Add(new ComponentInstance(operands.ToArray(), select));
            }

            var constraints = new List<Term>();
            var lineInstances = new List<LineInstance>();
            for(int lineIndex = 0; lineIndex < lines.Count; lineIndex++)
            {
                // The first N lines are symbols
                var line = lines[lineIndex];
                if (line.IsSymbol)
                {
                    lineInstances.Add(new(symbols[lineIndex]));
                    continue;
                }

                // Select all of the operands
                var operands = line.Operands.Select(x => SelectOperand(x, lineInstances.Select(x => x.output).ToList())).ToList();

                // Problem: We need a canonical ordering for the instructions..
                var output = ctx.MkBvConst($"line{lineIndex}_output{numInstances}", w);
                for (int componentIndex = 0; componentIndex < components.Count; componentIndex++)
                {
                    var component = components[componentIndex];
                    var isComponent = line.ComponentIdx == (ulong)componentIndex;
                    var compInstance = componentInstances[componentIndex];
                    // If we picked this component, use it's output.
                    constraints.Add(Implies(isComponent, output == compInstance.output));
                    for(int operandIdx = 0; operandIdx < operands.Count; operandIdx++)
                    {
                        // If we picked this component, set its input to the line inputs.
                        constraints.Add(Implies(isComponent, operands[operandIdx].expr == compInstance.inputs[operandIdx]));
                    }
                }

                lineInstances.Add(new(output));
            }

            numInstances++;
            return (constraints, lineInstances.Select(x => x.output).ToList());

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

                var terms = new List<Term>();
                foreach (var opcode in Opcodes)
                {
                    var term = ApplyOperator(opcode, operands.Select(x => x.expr).ToList());

                    terms.Add(term);
                }

                //var select = LinearSelect(line.ComponentOpcode, terms);
                //exprs.Add(select);
            }

            return exprs.Last();
        }

        private Term ApplyOperator(SynthOpc opcode, List<Term> operands)
        {
            var op0 = () => operands[0];
            var op1 = () => operands[1];
            var op2 = () => operands[2];

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
                SynthOpc.Select => ctx.MkIte(ToBool(op0()), op1(), op2()),

                _ => throw new InvalidOperationException()
            };

            return term;
        }

        private (Term expr, Term justOperands, Term justConstants) SelectOperand(LineOperand operand, List<Term> prev)
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

                // Each instruction must choose a valid component
                constraints.Add(line.ComponentIdx <= (uint)(components.Count - 1));
            }

            // Each line must be assigned a unique component
            constraints.Add(ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_DISTINCT, lines.Skip(FirstInstIdx).Select(x => x.ComponentIdx)));

            foreach(var component in components)
            {
                constraints.Add(component.Opcode <= (uint)(component.Choices.Length - 1));
            }

        }

        private bool HasComponent(SynthOpc opcode)
        {
            return Opcodes.Contains(opcode);
        }

        // Implements CEGIS(T)
        // https://www.kroening.com/papers/cav2018-synthesis.pdf
        private void CegisT(List<Term> constraints)
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

            bool mba = false;
            if (mba)
                s.Assert(symbols[0] >= 50);



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

                while (mba && ctx.GetIntegerValue(values[0]) < 50)
                {
                    values[0] |= (rng.GetRandUlong() & ModuloReducer.GetMask((uint)symbols[0].Sort.BvSize));
                }



                var (flowConstraints, flowResults) = GetDataflowConstraints();
                flowConstraints.Add(flowResults.Last() == groundTruth);

                var adj = flowConstraints.Select(x => ctx.SubstituteTerm(x, symbols, values));
                foreach (var c in adj)
                    s.Assert(c);
                //var constraint = GetBehavioralConstraint(skeleton, values);
                //s.Assert(constraint);
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

                if (mba)
                    temp.Assert(symbols[0] >= 50);

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
                    var (generalizedSolution, generalizedBan) = Generalize(s, cegisSolution, cegisConstants, totalTime, mba);

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
                /*
                var vs = symbols.Select(x => temp.GetValue(x)).ToArray();
                s.Assert(GetBehavioralConstraint(null, vs));
                constraints.Add(GetBehavioralConstraint(null, vs));
                */
                var vs = symbols.Select(x => temp.GetValue(x)).ToArray();
                var (flowConstraints, flowResults) = GetDataflowConstraints();
                flowConstraints.Add(flowResults.Last() == groundTruth);

                var adj = flowConstraints.Select(x => ctx.SubstituteTerm(x, symbols, vs));
                foreach (var c in adj)
                    s.Assert(c);
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

                var a = s.GetValue(line.ComponentIdx);
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

                var compIdx = ctx.GetIntegerValue(s.GetValue(line.ComponentIdx));
                var component = components[(int)compIdx];

                var opcode = ctx.GetIntegerValue(s.GetValue(component.Opcode));
                //if (opcode >= (ulong)Opcodes.Count)
                //    opcode = (ulong)Opcodes.Count - 1;

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
                var op2 = () => ourOperands[2];



                var opc = component.Choices[(int)opcode];

                if (opc == SynthOpc.Select)
                {
                    Console.WriteLine("\n\n");
                    foreach (var operand in ourOperands)
                        Console.WriteLine(mbaCtx.GetAstString(operand));
                }

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
                    SynthOpc.Eq => mbaCtx.Zext(mbaCtx.ICmp(Predicate.Eq, op0(), op1()), (byte)w),
                    SynthOpc.Ult => mbaCtx.Zext(mbaCtx.ICmp(Predicate.Ult, op0(), op1()), (byte)w),
                    SynthOpc.Select => mbaCtx.Select(mbaCtx.Trunc(op0(), 1), op1(), op2()),

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

        private (Term generalizedSolution, Term generalizedConstraints) Generalize(BvSolver oldModel, Term candidate, List<Term> cegisConstants, Stopwatch totalTime, bool mba)
        {
            return (null, null);
        }

        private Term ToBv(Term term, uint width = 1)
            => ctx.MkIte(term, ctx.MkBvValue(1, width), ctx.MkBvValue(0, width));

        private Term ToBool(Term term)
           => ctx.MkExtract(0, 0, term) == 1;

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


        public class Tests
        {
            public static void P0()
            {
                var (ctx, idx) = Parse("(a&b) + c", 8);


                var config = new SynthConfig(new SynthOpc[] { SynthOpc.Add, SynthOpc.And }, 5, 5, 0);
                var synth = new HieraSynth(config, ctx, idx);

                synth.Run();
            }


            public static void PEasyBoolean()
            {
                var (ctx, idx) = Parse("x0^x1^x2^x3", 1);


                var config = new SynthConfig(new SynthOpc[] { SynthOpc.And, SynthOpc.Or, SynthOpc.Xor }, 7, 7, 0);
                var synth = new HieraSynth(config, ctx, idx);

                synth.Run();
            }

            public static void PEasyBoolean2()
            {
                var (ctx, idx) = Parse("AAA|BBB^CCC&DDD|EEE", 1);


                var config = new SynthConfig(new SynthOpc[] { SynthOpc.And, SynthOpc.Or, SynthOpc.Xor }, 9, 9, 0);
                var synth = new HieraSynth(config, ctx, idx);

                synth.Run();
            }



            // (x0^x1^x2^x3)&(x3|(x4|x5&x6))
            public static void Throw()
            {
                var (ctx, idx) = Parse("(x0^x1^x2^x3)&(x3|(x4^x2))", 1);


                var config = new SynthConfig(new SynthOpc[] { SynthOpc.And, SynthOpc.Or, SynthOpc.Xor }, 11, 11, 0);
                var synth = new HieraSynth(config, ctx, idx);

                synth.Run();
            }

            public static void Phardboolean()
            {
                var (ctx, idx) = Parse("(x0^x1^x2^x3)&(x3|(x4|x5&x6))", 1);


                var config = new SynthConfig(new SynthOpc[] { SynthOpc.And, SynthOpc.Or, SynthOpc.Xor }, 14, 14, 0);
                var synth = new HieraSynth(config, ctx, idx);

                synth.Run();
            }

            public static void P3Adapted()
            {
                var (ctx, idx) = Parse("(((a^b)) - ((c&d))) + (b&e)", 64);


                var config = new SynthConfig(new SynthOpc[] { SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Add, SynthOpc.Sub }, 11, 11, 0);
                var synth = new HieraSynth(config, ctx, idx);

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



}
