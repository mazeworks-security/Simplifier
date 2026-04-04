using Bitwuzla;
using Mba.Common.Ast;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Fuzzing;
using Mba.Simplifier.Synth;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.VisualBasic;
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
        public Term Loc { get; set; }

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
        public Term IsConstant { get; }

        // The immediate value of this operand
        public Term ConstValue { get; set; }

        // The index of the operand. 
        public Term OperandIndex { get; }

        public SynthOperand(Term isConstant, Term constVal, Term index)
        {
            IsConstant = isConstant;
            ConstValue = constVal;
            OperandIndex = index;
        }

        public override string ToString()
        {
            return $"(IsConstant: {IsConstant}) (Index: {OperandIndex})";
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
        private readonly Term lastInstVar;

        private List<SynthLine> lines;

        // Get the index of the first instruction in lines
        private int FirstInstIdx => symbols.Length;

        public IReadOnlyList<SynthLine> RealLines => lines.Skip(FirstInstIdx).ToList();

        private readonly uint w;

        public bool VariableLength => config.MinLength != config.MaxLength;

        public static void P4()
        {
            var config = new SynthConfig(new SynthOpc[] { SynthOpc.Add, SynthOpc.Sub }, 5, 5, 0);

            var (ctx, idx) = Parse("(a+b)-c", 8);
            var synth = new HieraSynth(config, ctx, idx);

            synth.Run();
            Debugger.Break();
        }

        
        public static void PMediumBoolean()
        {
            var config = new SynthConfig(new SynthOpc[] { SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Not }, 14, 14, 0);

            var (ctx, idx) = Parse("(x0^x1^x2^x3)&(x3|(x4|x5&x6))", 1);
            var synth = new HieraSynth(config, ctx, idx);

            synth.Run();
            Debugger.Break();
        }


        public HieraSynth(SynthConfig config, AstCtx mbaCtx, AstIdx mbaIdx)
        {
            this.config = config;
            this.mbaCtx = mbaCtx;
            this.mbaIdx = mbaIdx;
            this.lastInstVar = ctx.MkBvValue(config.MinLength - 1, (uint)BvWidth(config.MinLength - 1));

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
            lines = GetLines();
            var outputs = GetOutputs();

            var constraints = GetProgramConstraints(outputs);
            
            // Compute the result variable
            var result = LinearSelect(lastInstVar, outputs);


            CegisT(constraints, result);

            Debugger.Break();
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
                line.Loc = ctx.MkBvConst($"loc{lineIndex}", maxOperandSize);
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

                var output = ctx.MkBvConst($"line{lineIndex}_out", w);
                line.Output = output;

                lines.Add(line);
            }

            return lines;
        }

        // Instantiate the semantics of each instruction
        private List<Term> GetOutputs()
        {
            var exprs = new List<Term>();
            List<Term> prev = new();
            prev.AddRange(symbols);
            prev.AddRange(RealLines.Select(x => x.Output));

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
                foreach (var opcode in line.Choices)
                {
                    var term = ApplyOperator(opcode, operands.Select(x => x.expr).ToList());

                    terms.Add(term);
                }

                var select = LinearSelect(line.Opcode, terms);
                exprs.Add(select);
            }

            return exprs;
        }

        private (Term expr, Term justOperands, Term justConstants) SelectOperand(SynthOperand operand, List<Term> prev)
        {
            var operandSelect = LinearSelect(operand.OperandIndex, prev);
            if (config.MaxConstants == 0)
                return (operandSelect, operandSelect, null);

            var expr = ctx.MkIte(operand.IsConstant, operand.ConstValue, operandSelect);
            return (expr, operandSelect, null);
        }

        // Select the ith value of an array using a chain of ITEs
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
        
        // We have a list of components each with a unique index, and are looking for 

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

        private List<Term> GetProgramConstraints(List<Term> instantiations)
        {
            var constraints = new List<Term>();
            AddNumInstructionsConstraint(constraints);
            AddWfpConstraints(constraints, instantiations);
            return constraints;
        }

        // If we are synthesizing an instruction with a variable number of instructions, constrain the length of the solution accordingly
        private void AddNumInstructionsConstraint(List<Term> constraints)
        {
            // Skip if there is only one allowed length
            if (!VariableLength)
                return;

            Debugger.Break();
        }

        private void AddWfpConstraints(List<Term> constraints, List<Term> instantiations)
        {
            for (int i = FirstInstIdx; i < lines.Count; i++)
            {
                var line = lines[i];
                // Each line can only refer to lines below it
                foreach(var operand in line.Operands)
                {
                    var ult = operand.OperandIndex < line.Loc;
                    constraints.Add(ult);
                }

                // The location must be within range
                constraints.Add(line.Loc <= (uint)lines.Count - 1);
                // The opcode must be within range
                constraints.Add(line.Opcode <= (uint)line.Choices.Length - 1);

                // The semantics must be instantiated
                constraints.Add(line.Output == instantiations[i]);
            }

            // The locations should be distinct
            constraints.Add(ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_DISTINCT, RealLines.Select(x => x.Loc)));
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

                
                foreach(var line in RealLines)
                {
                    Console.WriteLine($"Loc: {s.GetValue(line.Loc)}");
                    Console.WriteLine($"Opc: {s.GetValue(line.Opcode)}");
                    foreach(var operand in line.Operands)
                    {
                        Console.WriteLine($"    {s.GetValue(operand.IsConstant)}");
                        Console.WriteLine($"    {s.GetValue(operand.OperandIndex)}");
                        Console.WriteLine($"    {s.GetValue(operand.ConstValue)}");
                        Console.WriteLine("    ");
                    }
                    Console.WriteLine("\n");
                }

                //Console.WriteLine(s.mod);

                var cegisSolution = SolutionToExprNew(s, (int)ctx.GetIntegerValue(s.GetValue(lastInstVar)));

                // Ask the solver for a fitting solution
                //var (ourSolution, cegisSolution, cegisConstants) = SolutionToExpr(s);



                Log($"Found solution. Took {curr.ElapsedMilliseconds}ms with global time {totalTime.ElapsedMilliseconds}\n\n{"todo"}\n\n\n");

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

                // Probably need better heuristic for IO points?
                var vs = symbols.Select(x => temp.GetValue(x)).ToArray();
                s.Assert(GetBehavioralConstraint(skeleton, vs));
                constraints.Add(GetBehavioralConstraint(skeleton, vs));

                s.Write();
            }
        }

        // Constrain that expr1(x0, x1) == expr2(x0, x1) on some concrete inputs
        private Term GetBehavioralConstraint(Term skeleton, Term[] points)
        {
            var before = ctx.SubstituteTerm(groundTruth, symbols, points);
            var after = ctx.SubstituteTerm(skeleton, symbols, points);
            return before == after;
        }

        private Term SolutionToExprNew(BvSolver s, int loc)
        {
            if (loc < symbols.Length)
                return symbols[loc];

            foreach (var l in lines)
            {
                if (l.IsSymbol)
                    continue;

                var lVar = l.Loc.Kind == BitwuzlaKind.BITWUZLA_KIND_CONSTANT ? ctx.GetIntegerValue(s.GetValue(l.Loc)).ToString() : "undefined";
                //Console.WriteLine($"Loc var: {lVar}");
            }

            //Console.WriteLine("\n\n");
            var line = lines.Single(x => !x.IsSymbol && x.Loc.Kind == BitwuzlaKind.BITWUZLA_KIND_CONSTANT && (int)ctx.GetIntegerValue(s.GetValue(x.Loc)) == loc);

            var opcode = ctx.GetIntegerValue(s.GetValue(line.Opcode));
            if (opcode >= (ulong)line.Choices.Length)
                opcode = (ulong)line.Choices.Length - 1;

            var operands = new List<Term>();
            foreach(var operand in line.Operands)
            {
                var isConstant = ctx.GetBoolValue(s.GetValue(operand.IsConstant));
                var operandIndex = (int)ctx.GetIntegerValue(s.GetValue(operand.OperandIndex));

                var cegisOperand = isConstant ? operand.ConstValue : SolutionToExprNew(s, operandIndex);
                operands.Add(cegisOperand);
            }

            Term cegisNode = ApplyOperator(line.Choices[opcode], operands);
            return cegisNode;
        }

        // TODO: We're getting tons of identical duplicates even with CEGIS(T). I think the forall query is broken?
        private (AstIdx ourSolution, Term cegisSolution, List<Term> constants) SolutionToExpr(BvSolver s)
        {
            foreach (var line in lines)
            {
                if (line.IsSymbol)
                {
                    continue;
                }

                var a = s.GetValue(line.Opcode);
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

                var opcode = ctx.GetIntegerValue(s.GetValue(line.Opcode));
                if (opcode >= (ulong)line.Choices.Length)
                    opcode = (ulong)line.Choices.Length - 1;

                var cegisOperands = new List<Term>();
                var ourOperands = new List<AstIdx>();
                foreach (var operand in line.Operands)
                {
                    var isConstant = ctx.GetBoolValue(s.GetValue(operand.IsConstant));
                    var operandIndex = (int)ctx.GetIntegerValue(s.GetValue(operand.OperandIndex));

                    var cegisOperand = isConstant ? operand.ConstValue : cegisNodes[operandIndex];
                    cegisOperands.Add(cegisOperand);

                    var ourOperand = isConstant ? mbaCtx.Constant(ctx.GetIntegerValue(s.GetValue(operand.ConstValue)), (byte)w) : ourNodes[operandIndex];
                    ourOperands.Add(ourOperand);
                }

                var op0 = () => ourOperands[0];
                var op1 = () => ourOperands[1];
                var op2 = () => ourOperands[2];



                var opc = line.Choices[(int)opcode];

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
                for (int i = 0; i < line.MaxArity; i++)
                {
                    var operand = line.Operands[i];
                    var isConstant = ctx.GetBoolValue(s.GetValue(operand.IsConstant));
                    var operandIndex = (int)ctx.GetIntegerValue(s.GetValue(operand.OperandIndex));
                    operandStrs.Add($"{isConstant} {operandIndex}");
                }

                Log($"%{li} = {opc}({String.Join(", ", operandStrs)})\n");

                Term cegisNode = ApplyOperator(opc, cegisOperands);
                cegisNodes.Add(cegisNode);
            }

            return (ourNodes.Last(), cegisNodes.Last(), null);
       
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

        private void Log(string x)
            => Console.WriteLine(x);

        private static (AstCtx Ctx, AstIdx Idx) Parse(string text, uint width)
        {
            var ctx = new AstCtx();
            AstIdx.ctx = ctx;
            var parsed = RustAstParser.Parse(ctx, text, width);
            return (ctx, parsed);
        }
    }

   
}
