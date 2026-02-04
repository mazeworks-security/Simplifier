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

        private readonly IReadOnlyList<SynthComponent> components;

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
            this.mbaVariables = mbaCtx.CollectVariables(mbaIdx).ToArray();
            this.components = config.Components;
            w = mbaCtx.GetWidth(mbaIdx);

            // Translate inputs to LLVM IR
            var translator = new BitwuzlaTranslator(mbaCtx, ctx);
            groundTruth = translator.Translate(mbaIdx);
            symbols = mbaCtx.CollectVariables(mbaIdx).Select(x => translator.Translate(x)).ToArray();

            // Get the minimum size bitvector needed to store the component index and component opcode
            componentIndexSize = (uint)BvWidth(components.Count - 1);
            componentOpcodeSize = (uint)BvWidth(components.Max(x => x.Opcodes.Length) - 1);
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

        private List<SynthLine> GetLines()
        {
            var lines = new List<SynthLine>();

            // Each variable gets a dedicated line
            for (int i = 0; i < symbols.Length; i++)
                lines.Add(new() { IsSymbol = true});

            var maxOperandSize = BvWidth(Math.Max(config.NumInstructions - 2, config.MaxConstants - 1));

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
                var operands = line.Operands.Select(x => SelectOperand(x, exprs)).ToList();

                // Need to get the opcode choices first.
                var componentChoices = new List<Term>();
                foreach(var component in components)
                {
                    List<Term> terms = new();

                    // If the component is {add, sub}, try to share the adder circuit.
                    var opcodes = component.Opcodes;
                    //if (opcodes.Length == 2 && opcodes[0] == SynthOpc.Add && opcodes[1] == SynthOpc.Sub)
                    if (false)
                    {
                        /*
                        var size = operands[0].Sort.BvSize;
                        var one = ctx.MkBvValue(1, size);
                        var zero = ctx.MkBvValue(0, size);
                        var allOnes = ~zero;

                        var isSub = line.ComponentOpcode == 1;
                        var mask = ctx.MkIte(isSub, allOnes, zero);
                        var cin = ctx.MkIte(isSub, one, zero);

                        var b = operands[1] ^ mask;
                        var tmp = operands[0] + b;
                        terms.Add(tmp + cin);
                        */

                        var isSub = line.ComponentOpcode == 1;
                        var b = operands[1];
                        var negB = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_BV_NEG, b);
                        var selectedB = ctx.MkIte(isSub, negB, b);
                        var result = operands[0] + selectedB;
                        terms.Add(result);
                    }

                    else
                    {
                        foreach (var opcode in opcodes)
                        {
                            var term = ApplyOperator(opcode, operands);

                            terms.Add(term);
                        }
                    }

                    componentChoices.Add(LinearSelect(line.ComponentOpcode, terms));
                }

                var select = LinearSelect(line.ComponentIndex, componentChoices);
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
                _ => throw new InvalidOperationException()
            };

            return term;
        }

        private Term SelectOperand(SynthOperand operand, List<Term> prev)
        {
            var operandSelect = LinearSelect(operand.Index, prev);
            if (config.MaxConstants == 0)
                return operandSelect;

            var constSelect = LinearSelect(operand.Index, constants);
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
            //if (n > 12)
            //    Debugger.Break();

            var result = options[n - 1];

            for (int i = n - 2; i >= 0; i--)
            {
                var condition = index == ctx.MkBvValue(i, index.Sort.BvSize);
                result = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_ITE, condition, options[i], result);
            }

            return result;
        }

        private List<Term> GetProgramConstraints()
        {
            var constraints = new List<Term>();
            AddAcyclicConstraints(constraints);
            AddPruningConstraints(constraints);


            return constraints;
        }

        private void AddAcyclicConstraints(List<Term> constraints)
        {
            // Constrain each operand to be less than `i-1`
            for(int i = FirstInstIdx; i < lines.Count; i++)
            {
                var line = lines[i];
                foreach(var operand in line.Operands)
                {
                    var ult = operand.Index <= (uint)(i - 1);
                    var opConstraint = Implies(~operand.IsConstant, ult);
                    var constConstraint = Implies(operand.IsConstant, operand.Index <= (uint)Math.Max((config.MaxConstants - 1), 0));

                    constraints.Add(opConstraint);
                    constraints.Add(constConstraint);
                }
            }
        }

        private void AddPruningConstraints(List<Term> constraints)
        {
            // Sort constants
            for(int i = 1; i < constants.Count; i++)
            {
                //constraints.Add(constants[i] > constants[i - 1]);
            }

            // Constrain each opcode to be less than its maximum
            for (int i = FirstInstIdx; i < lines.Count; i++)
            {
                var line = lines[i];


                // Both operands should not be constant.
                constraints.Add(~And(line.Operands.Select(x => x.IsConstant)));

                
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


                    foreach (var component in components)
                    {
                        var isComponent = IsComponent(line, component);
                        /*
                         * if (component.Opcodes.Length == 4)
                            continue;
                        var implies = Implies(isComponent, line.ComponentOpcode <= (uint)(component.Opcodes.Length - 1));
                        constraints.Add(implies);
                        */

                        // Both of these ideas actually degrade performance
                        //var implies = Implies(isComponent, line.ComponentOpcode <= (uint)(component.Opcodes.Length - 1));
                        //constraints.Add(implies);

                        //var implies = Implies(isComponent, ctx.MkZext(1, line.ComponentOpcode) < (uint)component.Opcodes.Length);
                        //constraints.Add(implies);


                        for (int opcodeIndex = 0; opcodeIndex < component.Opcodes.Length; opcodeIndex++)
                        {
                            var opc = component.Opcodes[opcodeIndex];


                        /*
                        var isUnary = line.ComponentOpcode == opcodeIndex;
                        if (opc.IsCommutative())
                        {
                            constraints.Add(Implies(isUnary, line.Operands[0].Index < line.Operands[1].Index));
                        }
                        */

                        /*
                        var isUnary = isComponent & line.ComponentOpcode == opcodeIndex;
                        if (opc.IsCommutative())
                        {
                            constraints.Add(Implies(isUnary, line.Operands[0].Index < line.Operands[1].Index));
                        }
                        */

                        /*
                        if (opc.GetOperandCount() >= 2)
                            continue;

                        var isUnary = isComponent & line.ComponentOpcode == opcodeIndex;
                        constraints.Add(Implies(isUnary, line.Operands[1].Index == 0));
                        constraints.Add(Implies(isUnary, line.Operands[1].IsConstant == false));
                        */

                        if (!opc.IsIdempotent())
                            continue;

                        //var isIdempotent = line.ComponentOpcode == opcodeIndex;
                        //constraints.Add(Implies(isIdempotent, line.Operands[0].Index != line.Operands[1].Index));
                    }

                    }
            }
        }

        private Term IsComponent(SynthLine line, SynthComponent component)
        {
            return line.ComponentIndex == components.IndexOf(component);
        }

        // Implements CEGIS(T)
        // https://www.kroening.com/papers/cav2018-synthesis.pdf
        private void CegisT(List<Term> constraints, Term skeleton)
        {
            // Randomly evaluate the expression on N initial points and assert its equivalence
            var rng = new SeededRandom();
            int NUMSAMPLES = 4;
            for(int i = 0; i < NUMSAMPLES; i++)
            {
                var values = Enumerable.Range(0, symbols.Length)
                    .Select(x => ctx.MkBvValue(rng.GetRandUlong() & ModuloReducer.GetMask((uint)symbols[x].Sort.BvSize), symbols[x].Sort.BvSize))
                    .ToArray();

                var constraint = GetBehavioralConstraint(skeleton, values);
                constraints.Add(constraint);
            }

            var options = new Options();
            options.Set(BitwuzlaOption.BITWUZLA_OPT_PRODUCE_MODELS, true);
            //options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION, true);
            //options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION_BV_SIZE, 16);
            //options.Set(BitwuzlaOption.BITWUZLA_OPT_ABSTRACTION_INC_BITBLAST, true);

            var s = new BvSolver(ctx, options);

      

            foreach (var c in constraints)
                s.Assert(c);

            //s.Write();
            //Debugger.Break();


            var totalTime = Stopwatch.StartNew();
            while(true)
            {
                var curr = Stopwatch.StartNew();
                var check = s.CheckSat();
                curr.Stop();
                if (check == Result.Unsat)
                {
                    Console.WriteLine($"No solution. Took {totalTime.ElapsedMilliseconds}");
                    Debugger.Break();
                    return;
                }

                else
                {
                    Console.WriteLine($"Found solution. Took {totalTime.ElapsedMilliseconds}ms");
                }

                // Ask the solver for a fitting solution
                var (ourSolution, cegisSolution, cegisConstants) = SolutionToExpr(s);

                // Yield the solution if its equivalent
                var temp = new BvSolver(ctx, options);
                temp.Assert(~(groundTruth == cegisSolution));
                var isEquiv = temp.CheckSat() == Result.Unsat;
                if(isEquiv)
                {
                    Console.WriteLine("Solved");
                    Debugger.Break();
                }

                var (generalizedSolution, generalizedBan) = Generalize(s, cegisSolution, cegisConstants);
                Debug.Assert(generalizedSolution is null);

                s.Assert(generalizedBan);
                var vs = symbols.Select(x => temp.GetValue(x)).ToArray();
                s.Assert(GetBehavioralConstraint(skeleton, vs));

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
            for(int i = 0; i < config.MaxConstants; i++)
            {
                var eval = s.GetValue(constants[i]);

                var w = constants[i].Sort.BvSize;
                var myConstant = ctx.GetIntegerValue(eval);
                ourConstants.Add(mbaCtx.Constant(myConstant, (byte)w));
                cegisConstants.Add(eval);
            }

            foreach(var line in lines)
            {
                if (line.IsSymbol)
                    continue;

                var a = s.GetValue(line.ComponentOpcode);
                var b = s.GetValue(line.ComponentIndex);
                Console.WriteLine($"{a},  {b}");
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

                var index = (int)ctx.GetIntegerValue(s.GetValue(line.ComponentIndex));
                var opcode = ctx.GetIntegerValue(s.GetValue(line.ComponentOpcode));
                if (opcode >= (ulong)components[index].Opcodes.Length)
                    opcode = (ulong)components[index].Opcodes.Length - 1;

                var cegisOperands = new List<Term>();
                var ourOperands = new List<AstIdx>();
                foreach(var operand in line.Operands)
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

                var opc = components[index].Opcodes[opcode];
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
            for(int i = 0; i < symbols.Length; i++)
            {
                var v = ctx.MkVar(symbols[i].Sort, mbaCtx.GetSymbolName(mbaVariables[i]));
                solver.Assert(symbols[i] == v);
                quantVars.Add(v);
            }

            var equality = groundTruth == skeleton;
            var concat = quantVars.Append(equality).ToArray();
            var forall = ctx.MkTerm(BitwuzlaKind.BITWUZLA_KIND_FORALL, concat);


            solver.Assert(forall);

            var res = solver.CheckSat();
            if (res == Result.Sat)
                Debugger.Break();

            // Otherwise this solution is impossible.
            List<Term> structureVars = new();
            foreach(var line in lines)
            {
                if (line.IsSymbol)
                    continue;

                structureVars.Add(line.ComponentIndex);
                structureVars.Add(line.ComponentOpcode);
                foreach(var operand in line.Operands)
                {
                    structureVars.Add(operand.Index);
                    structureVars.Add(operand.IsConstant);
                }
            }

            List<Term> structureConstraints = new(); 
            foreach(var svar in structureVars)
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
            => MkBw(BitwuzlaKind.BITWUZLA_KIND_BV_OR, terms);

        private Term And(IEnumerable<Term> terms)
            => MkBw(BitwuzlaKind.BITWUZLA_KIND_AND, terms);

        // Bitwise constructor operator that allows passing less than 2 operands.
        private Term MkBw(BitwuzlaKind kind, IEnumerable<Term> terms)
        {
            var c = terms.Count();
            if (c == 0)
                return ctx.MkFalse();
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
            var (ctx, idx) = Parse("(((x|1111)+y)^y)", 8);

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
            //var (ctx, idx) = Parse("(171^((a+23)^(b)))^((((a|1111)+b)^b))", 8);

            // Works with 7 components and 3 constants. 500ms
            var (ctx, idx) = Parse("(((a+23)^(b)))^((((a|1111)+b)))", 8);

            //var (ctx, idx) = Parse("(((a+23423434)^(b)))^((((a|432324234)+b)))^343433", 8);

            var components = new List<SynthComponent>()
            {
                // new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor, SynthOpc.Add, SynthOpc.Sub),
                new(SynthOpc.Or, SynthOpc.Xor, SynthOpc.Add),

            };

            var config = new SynthConfig(components, 7, 3);
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
                new(SynthOpc.And, SynthOpc.Xor, SynthOpc.Lshr, SynthOpc.Add),
                //new(SynthOpc.And, SynthOpc.Xor),

            };

            var config = new SynthConfig(components, 6, 1);
            var synth = new BvSynthesis(config, ctx, idx);

            synth.Run();
        }

        public static void P15()
        {
            var (ctx, idx) = Parse("((x | (x^y)) - (((x^y)) >> 1))", 8);


            //var (ctx, idx) = Parse("(x^y)", 8);

            //var (ctx, idx) = Parse("(((x^y)) & a)", 8); // fails with 4/5 comps

            //var (ctx, idx) = Parse("(((x^y)) & z)", 8);

            var components = new List<SynthComponent>()
            {
                //new(SynthOpc.Not, SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                //new(SynthOpc.Add, SynthOpc.Sub),

                //new(SynthOpc.And, SynthOpc.Or, SynthOpc.Xor),
                new(SynthOpc.And, SynthOpc.Xor, SynthOpc.Lshr, SynthOpc.Add),
                //new(SynthOpc.And, SynthOpc.Xor),

            };

            var config = new SynthConfig(components, 8, 1);
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
                new(SynthOpc.Xor, SynthOpc.Lshr, SynthOpc.Mul, SynthOpc.And),
                //new(SynthOpc.And, SynthOpc.Xor),

            };

            var config = new SynthConfig(components, 9, 4);
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
