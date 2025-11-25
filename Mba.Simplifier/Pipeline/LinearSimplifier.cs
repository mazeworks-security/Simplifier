// #define DBG
using Antlr4.Runtime.Atn;
using Mba.Ast;
using Mba.Testing;
using Mba.Utility;
using Mba.Common;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using ApInt = System.UInt64;
using Mba.Common.MSiMBA;
using Mba.Common.Utility;
using Mba.Common.Minimization;
using System.Numerics;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Minimization;
using Mba.Common.Interop;
using System.Runtime.CompilerServices;
using System.Reflection.Metadata;
using static Antlr4.Runtime.Atn.SemanticContext;
using Mba.Simplifier.Interpreter;
using Mba.Simplifier.Utility;
using Microsoft.VisualBasic;

namespace Mba.Simplifier.Pipeline
{
    // Note that this is a near 1:1 port of MSiMBA, just adapted to use a new ast representation.
    public class LinearSimplifier
    {
        private Metric metric = Metric.String;

        private readonly AstCtx ctx;

        private readonly IReadOnlyList<AstIdx> variables;

        private readonly uint width;

        private readonly bool refine;

        // If enabled, we perform multi-bit simba.
        private bool multiBit;

        // If enabled, we try to find a simpler representation of grouping of basis expressions.
        private readonly bool tryDecomposeMultiBitBases;

        // For internal use in private projects (do not use)
        private readonly Action<ulong[], ulong>? resultVectorHook;

        private readonly int depth;

        // For internal use in private projects (do not use)
        // Optionally used to track which variables bits are demanded in the expression
        private readonly Dictionary<ApInt, ApInt> anfDemandedBits;

        private readonly ApInt moduloMask = 0;

        // Number of combinations of input variables(2^n), for a single bit index.
        // For multi-bit this must be multiplied by the bit width.
        private ApInt numCombinations;

        private readonly List<int> groupSizes;

        private ApInt[] resultVector;

        private readonly MultibitRefiner refiner;

        private AstIdx? bestSolution = null;

        private AstIdx? univariateParts = null;

        private int? lincombTerms = null;

        private readonly bool newLine = false;

        private AstIdx? initialInput = null;

        public static AstIdx Run(uint bitSize, AstCtx ctx, AstIdx? ast, bool alreadySplit = false, bool multiBit = false, bool tryDecomposeMultiBitBases = false, IReadOnlyList<AstIdx> variables = null, Action<ulong[], ApInt>? resultVectorHook = null, ApInt[] inVec = null, int depth = 0, Dictionary<ApInt, ApInt> anfDemandedBits = null)
        {
            if (variables == null)
                variables = ctx.CollectVariables(ast.Value);
            return new LinearSimplifier(ctx, ast, variables, bitSize, refine: true, multiBit, tryDecomposeMultiBitBases, resultVectorHook, inVec, depth, anfDemandedBits).Simplify(false, alreadySplit);
        }

        public LinearSimplifier(AstCtx ctx, AstIdx? ast, IReadOnlyList<AstIdx> variables, uint bitSize, bool refine = true, bool multiBit = false, bool tryDecomposeMultiBitBases = true, Action<ulong[], ApInt>? resultVectorHook = null, ApInt[] inVec = null, int depth = 0, Dictionary<ApInt, ApInt> anfDemandedBits = null)
        {
            // If we are given an AST, verify that the correct width was passed.
            if (ast != null && bitSize != ctx.GetWidth(ast.Value))
                throw new InvalidOperationException($"Incorrect width passed to linear simplifier!");

            this.initialInput = ast;
            this.ctx = ctx;
            this.variables = variables;
            width = bitSize;
            this.refine = refine;
            this.multiBit = multiBit;
            this.tryDecomposeMultiBitBases = tryDecomposeMultiBitBases;
            this.resultVectorHook = resultVectorHook;
            this.depth = depth;
            this.anfDemandedBits = anfDemandedBits;
            moduloMask = (ApInt)ModuloReducer.GetMask(bitSize);
            groupSizes = GetGroupSizes(variables.Count);
            numCombinations = (ApInt)Math.Pow(2, variables.Count);

            refiner = new MultibitRefiner(bitSize, moduloMask);
            // TODO: Refactor out into two different constructors.
            // We need to support accepting an expression in both AST and result vector form.
            if (inVec != null)
            {
                resultVector = inVec;
            }

            else
            {
                // TODO: If multi-bit, try to rewrite as linear result vector.
                // If for some reason the user inputs a constant, just yield that constant.
                var asConstant = ctx.TryGetConstantValue(ast.Value);
                if (asConstant != null)
                    resultVector = new ApInt[] { asConstant.Value };
                else
                    resultVector = JitResultVector(ctx, bitSize, moduloMask, variables, ast.Value, multiBit, numCombinations);
            }

            // After constructing the result vector, cast all of the variables to the size of the output expression.
            // This enables us to support mixing operations of different widths without inserting adhoc checks all over the place.
            this.variables = CastVariables(ctx, variables, bitSize);

            if (resultVectorHook != null)
            {
                resultVectorHook(resultVector, numCombinations);
                return;
            }
        }

        public static IReadOnlyList<AstIdx> CastVariables(AstCtx ctx, IReadOnlyList<AstIdx> variables, uint bitSize)
        {
            // If all variables are of a correct size, no casting is necessary.
            if (!variables.Any(x => ctx.GetWidth(x) != bitSize))
                return variables;

            var result = new List<AstIdx>();
            foreach(var v in variables)
            {
                // Skip if the variable is of the correct size
                var w = ctx.GetWidth(v);
                if (w == bitSize)
                {
                    result.Add(v);
                    continue;
                }

                // Either truncate or extend the variable to the expected size.
                // Note that this is a sound / legal transformation.
                result.Add(w < bitSize ? ctx.Zext(v, (byte)bitSize) : ctx.Trunc(v, (byte)bitSize));
            }

            return result;
        }

        // Initialize the group sizes of the various variables, i.e., their numbers
        // of subsequent occurences in the truth table.
        public static List<int> GetGroupSizes(int varCount)
        {
            var groupSizes = new List<int>() { 1 };
            for (int i = 0; i < varCount; i++)
                groupSizes.Add(2 * groupSizes[groupSizes.Count - 1]);

            return groupSizes;
        }

        public unsafe static ApInt[] JitResultVector(AstCtx ctx, uint bitWidth, ApInt mask, IReadOnlyList<AstIdx> variables, AstIdx ast, bool multiBit, ApInt numCombinations)
        {
            return JitResultVectorNew(ctx, bitWidth, mask, variables, ast, multiBit, numCombinations);
        }

        public unsafe static ApInt[] JitResultVectorOld(AstCtx ctx, uint bitWidth, ApInt mask, IReadOnlyList<AstIdx> variables, AstIdx ast, bool multiBit, ApInt numCombinations)
        {
            uint capacity = (uint)(numCombinations * (multiBit ? bitWidth : 1u));
            var resultVec = new ApInt[capacity];
            fixed (ulong* vecPtr = &resultVec[0])
            {
                ctx.JitEvaluate(ast, mask, multiBit, bitWidth, variables.ToArray(), numCombinations, MultibitSiMBA.JitPage.Value, (nint)vecPtr);
            }

            return resultVec;
        }

        public unsafe static ApInt[] JitResultVectorNew(AstCtx ctx, uint bitWidth, ApInt mask, IReadOnlyList<AstIdx> variables, AstIdx ast, bool multiBit, ApInt numCombinations)
        {
            ctx.Compile(ast, ModuloReducer.GetMask(bitWidth), variables.ToArray(), MultibitSiMBA.JitPage.Value);
            var vec = LinearSimplifier.Execute(ctx, bitWidth, mask, variables, multiBit, numCombinations, MultibitSiMBA.JitPage.Value, false);
            return vec;
        }

        public unsafe static nint CompileLegacy(AstCtx ctx, ApInt mask, IReadOnlyList<AstIdx> variables, AstIdx ast, nint codePtr)
        {
            return ctx.CompileLegacy(ast, mask, variables.ToArray(), codePtr);
        }

        public unsafe static ApInt[] Execute(AstCtx ctx, uint bitWidth, ApInt mask, IReadOnlyList<AstIdx> variables, bool multiBit, ApInt numCombinations, nint codePtr, bool isOneBitVars)
        {
            uint capacity = (uint)(numCombinations * (multiBit ? bitWidth : 1u));
            var resultVec = new ApInt[capacity];
            fixed (ulong* vecPtr = &resultVec[0])
            {
                ctx.Execute(multiBit, bitWidth, variables.ToArray(), numCombinations, codePtr, (nint)vecPtr, isOneBitVars);
            }

            return resultVec;
        }

        // Evaluate for all possible combinations of zeroes and ones.
        private static ApInt[] BuildResultVector(AstCtx ctx, AstIdx id, ApInt mask)
        {
            return ctx.EvaluateForZeroesAndOnes(id, mask);
        }

        // If multibit is requested, return the bit width of the expression.
        // Otherwise return 1 for single bit MBA simplification.
        public static int GetNumBitIterations(bool multiBit, uint bitSize)
        {
            return (int)(multiBit ? bitSize : 1);
        }

        private AstIdx Simplify(bool useZ3 = false, bool alreadySplit = false)
        {
            // Remove the constant offset
            var constant = SubtractConstantOffset(moduloMask, resultVector, (int)numCombinations);

            // If we were given a semi-linear expression, and the ground truth of that expression is linear,
            // truncate the size of the result vector down to 2^t, then treat it as a linear MBA.
           if (multiBit && IsLinearResultVector())
            {
                multiBit = false;
                Array.Resize(ref resultVector, (int)numCombinations);
            }

            if (multiBit)
            {
                return SimplifyMultibit(constant);
            }

            return SimplifyOneBit(constant, useZ3, alreadySplit);
        }

        // If we have a multi-bit result vector, try to rewrite as a linear result vector. If possible, update state accordingly.
        private unsafe bool IsLinearResultVector()
        {
            foreach(var v in variables)
            {
                // If the variable is zero extended or truncated, we treat this as a semi-linear signature vector.
                // Truncation cannot be treated as linear, though in the future we may be able to get away with treating zero extension as linear?
                if (!ctx.IsSymbol(v))
                    return false;
            }

            fixed (ApInt* ptr = &resultVector[0])
            {
                ushort bitIndex = 0;
                for (int comb = 0; comb < resultVector.Length; comb += (int)numCombinations)
                {
                    ApInt mask = 1ul << bitIndex;
                    for (int i = 0; i < (int)numCombinations; i++)
                    {
                        var bit0Coeff = ptr[i];
                        var bitICoeff = ptr[comb + i];

                        var op0 = moduloMask & (bit0Coeff * mask);
                        var op1 = moduloMask & (bitICoeff * mask);
                        if (op0 != op1)
                            return false;
                    }

                    bitIndex += 1;
                }
            }

            return true;
        }

        private AstIdx SimplifyMultibit(ApInt constant)
        {
            // Find an initial solution.
            SimplifyGeneric(constant);

            var solution = bestSolution;
            return bestSolution.Value;
        }

        private int GetCost(AstCtx ctx, AstIdx ast, bool inBitwise)
            => GetCost(ctx, ast, inBitwise, moduloMask);

        public static int GetCost(AstCtx ctx, AstIdx ast, bool inBitwise, ApInt mask)
        {
            return (int)ctx.GetCost(ast);
        }

        private AstIdx Add(AstIdx? t0, AstIdx? t1)
        {
            if (t0 == null)
                return t1.Value;

            return ctx.Add(t0.Value, t1.Value);
        }

        private AstIdx Or(AstIdx? t0, AstIdx? t1)
        {
            if (t0 == null)
                return t1.Value;

            return ctx.Or(t0.Value, t1.Value);
        }

        // Algorithm:
        // (1) If the result vector is constant, we can immediately return this value.
        // (2) If the result vector has one term, we can immediately find the optimal result.
        // (3) If any variables are "dead", we we eliminate them and recursively simplify this reduced variable count version instead.
        //      - But first we need to construct algebraic normal form to figure out which variables are dead... TODO: Find a better way to do this 
        // (4) If the result vector has two terms (and optionally some constant offset), we can exhaustively enumerate all possible solutions.
        //      - For t <= 3 we find the optimal result. 
        //      - For t == 4 we find are guaranteed to find a result that is close to optimal.
        //      - For t >= 5 we do not perform the exhaustive search(though we could, up to some limit). 
        // (5) Try to split the result vector into linearly independent parts using based on the normal form. E.g. "a + b + c + (c&d)" gets partitioned into the groups ["a", "b", "c + c&d"],
        //     then try to simplify the parts individually.
        // (6) Combine all of the simplified parts together, yielding a final simplified result.
        // (7) Return either the "combined" result, or the algebraic normal form, depending upon some cost function.
        private AstIdx SimplifyOneBitNew(ApInt constant, bool useZ3 = false, bool alreadySplit = false)
        {
            // Group each unique coefficient to a truth table.
            var coeffToTable = new Dictionary<ApInt, TruthTable>();
            for (int i = 1; i < (int)numCombinations; i++)
            {
                var coeff = resultVector[i];
                if (coeff == 0)
                    continue;

                if (!coeffToTable.TryGetValue(coeff, out var table))
                {
                    table = new TruthTable(variables.Count);
                    coeffToTable[coeff] = table;
                }

                table.SetBit(i, true);
            }

            // (1) If no terms exist, we have a constant.
            if (coeffToTable.Count == 0)
                return ctx.Constant(constant, width);
            // (2) If only a single term exists, we can immediately find the optimal solution.
            // For more terms we need to take special care to eliminate dead variables, but the boolean minimizer will eliminate dead variables for the single term case!
            if (coeffToTable.Count == 1)
            {
                var (coeff, truthTable) = coeffToTable.First();
                var single = SimplifyOneTerm(constant, coeff, truthTable);
                return single;
            }

            // (3) Construct a linear combination using ANF as the basis. This will roughly tell us which variables are dependent upon one another.
            var copy = resultVector.ToArray();
            var (variableCombinations, linearCombinations) = GetAnf();
            resultVector = copy;

            // Identify the demanded(live) variables of the input expression
            ApInt demandedVariables = 0;
            for (int i = linearCombinations.Count - 1; i >= 0; i--)
            {
                // Skip if this variable combination is not demanded.
                var curr = linearCombinations[i];
                if (curr.Count == 0)
                    continue;
                demandedVariables |= variableCombinations[i];
            }

            // If the linear MBA has dead variables, eliminate them and recursively simplify this fewer variable count version.
            if(BitOperations.PopCount(demandedVariables) < variables.Count)
            {
                return EliminateDeadVarsAndSimplify(constant, demandedVariables, variableCombinations, linearCombinations);
            }

            // (4) If the result vector has two terms and <= 4 variables we can find an optimal answer.
            // Disabled because `((-407:i64*(uns21:i64|subst0:i64))+(uns21:i64&subst0:i64))` triggers assert!
            //if(variables.Count <= 4 && coeffToTable.Count == 2)
            if (false)
            {
                return SimplifyTwoTerm(constant, coeffToTable);
            }

            // (2) Try to partition the terms into disjoint variable sets.
            // Note that we're iterating backwards to heuristically see terms with the most variables first.
            int anfCost = constant == 0 ? 0 : 1;
            List<ApInt> disjointSets = new();
            for(int i = linearCombinations.Count - 1; i >= 0; i--)
            {
                // Skip if this variable combination is not demanded.
                var curr = linearCombinations[i];
                if (curr.Count == 0)
                    continue;

                // Search through disjoint sets, checking if this variable combination has an intersection.
                // Merge intersecting variable combinations, otherwise emplace in a new disjoint set.
                var combMask = variableCombinations[i];
                var coeffCost = curr[0].coeff == 1 ? 0 : 1;
                anfCost += 1 + coeffCost + BitOperations.PopCount(combMask);
                anfCost += BitOperations.PopCount(combMask) - 1; // Account for the number of AND nodes.

                bool found = false;
                for(int setIdx = 0; setIdx < disjointSets.Count; setIdx++)
                {
                    var set = disjointSets[setIdx];
                    if((set&combMask) != 0)
                    {
                        disjointSets[setIdx] |= combMask;
                        found = true;
                        break;
                    }
                }
                
                if(!found)
                {
                    disjointSets.Add(combMask);
                }
            }

            // Merge intersecting variable sets
            for(int i = 0; i < disjointSets.Count; i++)
            {
                for(int j = i + 1; j < disjointSets.Count; j++)
                {
                    var jMask = disjointSets[j];
                    if (jMask == 0)
                        continue;

                    var iMask = disjointSets[i];
                    if ((jMask & iMask) == 0)
                        continue;

                    disjointSets[i] |= jMask;
                    disjointSets[j] = 0;
                }
            }

            // Remove empty sets.
            disjointSets = disjointSets.Where(x => x != 0).ToList();

            // If we have a single disjoint set, we can immediately yield a solution.
            // TODO: Our cost function is not as good as the one in msimba.
            // We use AST size because it's cheap to compute, but the original msimba accounts for both the AST size and the number of terms.
            if(disjointSets.Count == 1)
            {
                // First try to reduce the number of terms.
                EliminateUniqueValues(coeffToTable);
                // Refine the linear combination if possible.
                var dnf = TryRefineBitwiseCombination(constant, coeffToTable);
                // If the bitwise combination is better than the anf combination, yield it.
                var dnfCost = ctx.GetCost(dnf);

                // Otherwise we want ANF. First append the constant offset.
                var terms = new List<AstIdx>();
                if (constant != 0)
                    terms.Add(ctx.Constant(constant, width));
                // Then append conjunctions of variables in increasing order.
                for(int i = 0; i < linearCombinations.Count; i++)
                {
                    // Skip if this variable combination is not demanded.
                    var curr = linearCombinations[i];
                    if (curr.Count == 0)
                        continue;

                    // Search through disjoint sets, checking if this variable combination has an intersection.
                    // Merge intersecting variable combinations, otherwise emplace in a new disjoint set.
                    var combMask = variableCombinations[i];
                    var coeff = curr[0].coeff;
                    terms.Add(ConjunctionFromVarMask(coeff, combMask));
                }

                var anfSum = ctx.Add(terms);
                var otherCost = ctx.GetCost(anfSum);
                if (dnfCost < otherCost) // Our cost function is still not correct for ANF(at least it is not matching the DNF cost)
                    return dnf;

                return anfSum;
            }

            // Otherwise have multiple disjoint sets that we want to simplify individually.
            // First put each disjoint set into algebraic normal form.
            var disjointTerms = new List<AstIdx?>();
            for (int i = 0; i < disjointSets.Count; i++)
                disjointTerms.Add(null);
            for(int i = 0; i < linearCombinations.Count; i++)
            {
                // Skip if this variable combination is not demanded.
                var curr = linearCombinations[i];
                if (curr.Count == 0)
                    continue;

                var mask = variableCombinations[i]; 
                var coeff = curr[0].coeff;
                // Find the index
                var insertIdx = disjointSets.FindIndex(x => (x & mask) != 0);
                var other = disjointSets.Single(x => (x & mask) != 0);
                if (disjointTerms[insertIdx] == null)
                    disjointTerms[insertIdx] = ConjunctionFromVarMask(coeff, mask);
                else
                    disjointTerms[insertIdx] = ctx.Add(disjointTerms[insertIdx].Value, ConjunctionFromVarMask(coeff, mask));
            }

            // Then recursively simplify the disjoint sets.
            List<AstIdx> mutVars = new(variables.Count);
            for(int i = 0; i < disjointTerms.Count; i++)
            {
                // Fetch the demanded variables. If only one variable is demanded in this term, it is already optimal.
                var demandedMask = disjointSets[i];
                if (BitOperations.PopCount(demandedVariables) == 1)
                    continue;

                // Collect all of the variables.
                mutVars.Clear();
                while(demandedMask != 0)
                {
                    var xorIdx = BitOperations.TrailingZeroCount(demandedMask);
                    mutVars.Add(variables[xorIdx]);
                    demandedMask &= ~(1ul << xorIdx);
                }

                // Recursively simplify.
                var oldId = disjointTerms[i].Value;
                var newId = Run(width, ctx, oldId, false, false, false, mutVars);
                disjointTerms[i] = newId;   
            }

            var sum = ctx.Add(disjointTerms.Select(x => x.Value));
            if (constant != 0)
                sum = ctx.Add(ctx.Constant(constant, width), sum);
            return sum;
        }

        private AstIdx SimplifyOneTerm(ApInt constant, ApInt coeff, TruthTable truthTable)
        {
            // If there is no constant offset, we can just yield the boolean expression.
            if(constant == 0)
                return Term(GetBooleanTableAst(truthTable), coeff);
            // If we have c1 + c1*x, we can rewrite as a single term solution of -c1*~x.
            if(constant == coeff)
            {
                truthTable.Negate();
                return Term(GetBooleanTableAst(truthTable), moduloMask & (moduloMask * coeff));
            }

            // If the constant offset is equal to -1, we want to embed it as a negation.
            // We could leave it outside, but embedding it as a negation gives the rest of the simplification pipeline
            // a stronger chance of identifying trivial negations of substituted parts.
            else if(constant == moduloMask)
            {
                return ctx.Neg(Term(GetBooleanTableAst(truthTable), moduloMask & (moduloMask * coeff)));
            }
            
            // If all else fails we have a two term solution.
            return ctx.Add(ctx.Constant(constant, width), Term(GetBooleanTableAst(truthTable), coeff));
        }

        private AstIdx SimplifyTwoTerm(ApInt constant, Dictionary<ApInt, TruthTable> coeffToTable)
        {
            Debug.Assert(coeffToTable.Count == 2);
            // Get the first and second coefficient from the dictionary. 
            ApInt a = 0;
            ApInt b = 0;
            foreach(var coeff in coeffToTable.Keys)
            {
                if (a == 0)
                    a = coeff;
                else
                    b = coeff;
            }

            // Find two unnegated terms + some constant offset.
            var cand1 = FindTwoTermsUnnegated(constant, a, b);
            if (constant == 0)
                return cand1;

            var cand2 = TryFindTwoTermsNegatedAndUnnegated(constant, a, b);
            return cand1;

            // There is one more missing pattern, "TryFindTwoNegatedExpressions"...
        }

        // Find a two term linear combination + some constant offset
        // This is guaranteed to always find a solution.
        private AstIdx FindTwoTermsUnnegated(ApInt constant, ApInt a, ApInt b)
        {
            var cand1 = DetermineCombOfTwoFast(a, b).Value;
            var cand2 = DetermineCombOfTwoFast(moduloMask & a - b, b).Value;
            var cand3 = DetermineCombOfTwoFast(a, moduloMask & b - a).Value;

            var min = new AstIdx[] { cand1, cand2, cand3 }.MinBy(x => ctx.GetCost(x));
            if (constant == 0)
                return min;
            return ctx.Add(ctx.Constant(constant, (byte)width), min);
        }

        private AstIdx? TryFindTwoTermsNegatedAndUnnegated(ApInt constant, ApInt a, ApInt b)
        {
            if (a == constant || b == constant)
            {
                // TODO: Given "x + ~y", we are yielding "~y + x", when the result ideally should be canonicalized such that x is to the right.
                var _a = a == constant ? b : a;
                var cand1 = DetermineCombOfTwoFast(_a, constant, null, true).Value;
                var cand2 = DetermineCombOfTwoFast((_a - constant) & moduloMask, constant, null, true).Value;
                return new AstIdx[] { cand1, cand2 }.MinBy(x => ctx.GetCost(x));
            }
            
            var negCoeff = constant;
            if (((b - a - negCoeff) & moduloMask) != 0)
            {
                (a, b) = (b, a);
                if (((b - a - negCoeff) & moduloMask) != 0)
                    return null;
            }

            // TODO: Verify this version is correct!
            //Debugger.Break();
            var option1 = DetermineCombOfTwoFast(a, constant, null, true).Value;
            var option2 = DetermineCombOfTwoFast((a - constant) & moduloMask, constant, null, true).Value;
            return new AstIdx[] { option1, option1 }.MinBy(x => ctx.GetCost(x));
        }

        private AstIdx EliminateDeadVarsAndSimplify(ApInt constantOffset, ApInt demandedMask, ApInt[] variableCombinations, List<List<(ApInt coeff, ApInt bitMask)>> linearCombinations)
        {
            // Collect all variables used in the output expression.
            List<AstIdx> mutVars = new(variables.Count);
            while (demandedMask != 0)
            {
                var xorIdx = BitOperations.TrailingZeroCount(demandedMask);
                mutVars.Add(variables[xorIdx]);
                demandedMask &= ~(1ul << xorIdx);
            }


            var clone = variables.ToList();
            AstIdx sum = ctx.Constant(constantOffset, width);
            for (int i = 0; i < linearCombinations.Count; i++)
            {
                // Skip if this variable combination is not demanded.
                var curr = linearCombinations[i];
                if (curr.Count == 0)
                    continue;

                var combMask = variableCombinations[i];
                var widths = variables.Select(x => ctx.GetWidth(x)).ToList();

                var vComb = ctx.GetConjunctionFromVarMask(clone, combMask);
                var term = Term(vComb, curr[0].coeff);
                sum = ctx.Add(sum, term);
            }

            // TODO: Instead of constructing a result vector inside the recursive linear simplifier call, we could instead convert the ANF vector back to DNF.
            // This should be much more efficient than constructing a result vector via JITing and evaluating an AST representation of the ANF vector.
            return LinearSimplifier.Run(width, ctx, sum, false, false, false, mutVars, depth: depth + 1);
        }

        private void EliminateUniqueValues(Dictionary<ApInt, TruthTable> coeffToTable)
        {
            (ApInt coeff, TruthTable table)[] uniqueValues = coeffToTable.Select(x => (x.Key, x.Value)).ToArray();
            var l = uniqueValues.Length;
            if (l == 0)
                return;

            // Try to get rid of a value by representing it as a sum of the others.
            foreach (var i in RangeUtil.Get(l - 1))
            {
                foreach (var j in RangeUtil.Get(i + 1, l))
                {
                    foreach (var k in RangeUtil.Get(l))
                    {
                        if (k == i || k == j)
                            continue;

                        // Skip any entries with zero coefficients.
                        var op0 = uniqueValues[i];
                        var op1 = uniqueValues[j];
                        var op2 = uniqueValues[k];
                        if (op0.coeff == 0 || op1.coeff == 0 || op2.coeff == 0)
                            continue;

                        // TODO: Use 2 sum + hashmap lookup instead of enumerating through all 3 pairs?
                        if (TryEliminateTriple(uniqueValues, i, j, k))
                            continue;
                        if (TryEliminateTriple(uniqueValues, i, k, j))
                            continue;
                        if (TryEliminateTriple(uniqueValues, j, i, k))
                            continue;
                        if (TryEliminateTriple(uniqueValues, j, k, i))
                            continue;
                        if (TryEliminateTriple(uniqueValues, k, i, j))
                            continue;
                        if (TryEliminateTriple(uniqueValues, k, j, i))
                            continue;
                    }
                }
            }

            coeffToTable.Clear();
            foreach (var (coeff, table) in uniqueValues)
            {
                if (coeff == 0)
                    continue;

                coeffToTable[coeff] = table;
            }
        }

        // If we have two terms and less than four variables, semi-exhaustively explore the search space of possible boolean expressions.
        // Otherwise yield a linear combination
        private AstIdx TryRefineBitwiseCombination(ApInt constantOffset, Dictionary<ApInt, TruthTable> coeffToTable)
        {
            // TODO: Exhaustively search bitwise expressions.
            var terms = new List<AstIdx>();
            if (constantOffset != 0)
                terms.Add(ctx.Constant(constantOffset, width));
            foreach (var (coeff, table) in coeffToTable)
            {
                var bitwise = GetBooleanTableAst(table);
                terms.Add(Term(bitwise, coeff));
            }

            return ctx.Add(terms);
        }

        private bool TryEliminateTriple((ApInt coeff, TruthTable table)[] uniqueValues, int idx0, int idx1, int idx2)
        {
            var op0 = uniqueValues[idx0];
            var op1 = uniqueValues[idx1];
            var op2 = uniqueValues[idx2];

            // The first two coefficients must sum up to the second coefficient.
            var sum = moduloMask & (op1.coeff + op2.coeff);
            if (sum != op0.coeff)
                return false;

            if (!op0.table.IsDisjoint(op1.table))
                return false;
            if (!op0.table.IsDisjoint(op2.table))
                return false;
            if(!op1.table.IsDisjoint(op2.table))
                return false;

            uniqueValues[idx0] = (0, op0.table);
            op1.table.Or(op0.table);
            op2.table.Or(op0.table);
            op0.table.Clear();
            return true;
        }

        private AstIdx SimplifyOneBit(ApInt constant, bool useZ3 = false, bool alreadySplit = false)
        {
            // TODO: Delete old simplification logic once we're confident that the new logic is better in all cases.
            return SimplifyOneBitNew(constant, useZ3, alreadySplit);
        }

        // Convert a 1-bit result vector into a linear combination.
        private (AstIdx expr, int termCount) SimplifyOneBitGeneric(ulong[] variableCombinations, List<List<(ApInt coeff, ApInt bitMask)>> linearCombinations)
        {
            AstIdx? expr = null;
            int termCount = 0;
            for (int i = 0; i < linearCombinations.Count; i++)
            {
                // Skip if there are no terms with this basis expression.
                var entries = linearCombinations[i];
                if (entries.Count == 0)
                    continue;

                // For a 1-bit result vector there is only 1 entry for any given basis expression.
                var entry = entries[0];

                // Construct the term.
                var term = ConjunctionFromVarMask(entry.coeff, variableCombinations[i]);
                if (expr == null)
                    expr = term;
                else
                    expr = ctx.Add(expr.Value, term);
                termCount++;
            }

            return (expr.Value, termCount);
        }

        private void SimplifyOneValue(HashSet<ApInt> resultSet)
        {
            // TODO: Compute a bitwise expression for the vector entry here?
            //Debugger.Break();
            var coefficient = resultSet.First();
            resultSet.Remove(coefficient);
            CheckSolutionComplexity(ctx.Constant(coefficient, width), 1);
        }

        public static ApInt SubtractConstantOffset(ApInt moduloMask, ApInt[] resultVector, int numCombinations)
        {
            var l = resultVector.Length;

            // Fetch the constant offset. If the offset is zero then there is nothing to subtract.
            var constant = resultVector[0];
            if (constant == 0)
                return 0;

            // Subtract the constant offset from the result vector.
            // Note that doing this on the multi-bit level requires that you shift 
            // the constant offset down, accordingly to the bit index you are operating at.
            unsafe
            {
                fixed (ApInt* ptr = &resultVector[0])
                {
                    ushort bitIndex = 0;
                    for (int comb = 0; comb < l; comb += (int)numCombinations)
                    {
                        ApInt constantOffset = moduloMask & constant >> bitIndex;
                        for (int i = 0; i < (int)numCombinations; i++)
                        {
                            var newCoeff = moduloMask & (ptr[comb + i] - constantOffset);
                            if (comb == 0)
                            {
                                ptr[comb + i] = newCoeff;
                                continue;
                            }

                            // Canonicalize the coefficient to ensure that we are returning a canonical result vector
                            // TODO: This may actually interfere with our ability to find good coefficients for single bitwise terms
                            // Might need to disable this
                            newCoeff = (moduloMask & (newCoeff * (1ul << bitIndex))) >> bitIndex;
                            ptr[comb + i] = newCoeff;
                        }

                        bitIndex += 1;
                    }
                }
            }

            return constant;
        }

        private (ApInt[], List<List<(ApInt coeff, ApInt bitMask)>>) GetAnf()
        {
            // Get all combinations of variables.
            var variableCombinations = GetVariableCombinations(variables.Count);

            // Linear combination, where the index can be seen as an index into `variableCombinations`,
            // and the element at that index is a list of terms operating over that boolean combination.
            // Term = coeff*(bitMask&basisExpression).
            var linearCombinations = new List<List<(ApInt coeff, ApInt bitMask)>>(variableCombinations.Length);
            for (int i = 0; i < variableCombinations.Length; i++)
                linearCombinations.Add(new((int)width));

            // Keep track of which variables are demanded by which combination,
            // as well as which result vector idx corresponds to which combination.
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var myMask = variableCombinations[i];
                var myIndex = GetGroupSizeIndex(groupSizes, myMask);
                combToMaskAndIdx.Add((myMask, (int)myIndex));
            }

            bool allZeroes = true;
            var varCount = variables.Count;
            bool onlyOneVar = varCount == 1;
            int vecWidth = (int)(varCount == 1 ? 1 : 2u << (ushort)(varCount - 1));

            unsafe
            {
                fixed (ApInt* ptr = &resultVector[0])
                {
                    for (ushort bitIndex = 0; bitIndex < GetNumBitIterations(multiBit, width); bitIndex++)
                    {
                        // If multi-bit simba is enabled, we need to take our base expression
                        // and isolate only the bit at the current bit index.
                        var maskForIndex = multiBit ? (ApInt)1 << bitIndex : moduloMask;
                        // Offset the result vector index such that we are fetching entries for the current bit index.
                        var offset = bitIndex * numCombinations;
                        for (int i = 0; i < variableCombinations.Length; i++)
                        {
                            // Fetch the result vector index for this conjunction.
                            // If the coefficient is zero, we can skip it.
                            var comb = variableCombinations[i];
                            var (trueMask, index) = combToMaskAndIdx[i];
                            var coeff = ptr[(int)offset + index];
                            if (coeff == 0)
                                continue;

                            // Subtract the coefficient from the result vector.
                            allZeroes = false;
                            MultibitSiMBA.SubtractCoeff(moduloMask, ptr, bitIndex, coeff, index, vecWidth, varCount, onlyOneVar, trueMask);

                            // Add an entry to the linear combination list.
                            linearCombinations[i].Add((coeff, maskForIndex));
                        }
                    }
                }
            }

            return (variableCombinations, linearCombinations);
        }

        // Find an initial linear combination of conjunctions.
        private (ulong withNoConjunctions, AstIdx? univariateParts, AstIdx? otherParts) SimplifyGeneric(ApInt constant)
        {
            // Short circuit if we can find a single term solution.
            if (false)
            {
                var asBoolean = AsPureBoolean(constant);
                if (asBoolean != null)
                {
                    CheckSolutionComplexity(asBoolean.Value, 1, null);
                    // Note that we return 0 because the "single variable with no conjunctions" logic is only used in the linear case.
                    return (0, null, null);
                }
            }

            var first = true;
            int termCount = 0;
            AstIdx? expr = null;
            if (constant != 0)
            {
                expr = ctx.Constant(constant, width);
                termCount += 1;
            }

            // Get all combinations of variables.
            var variableCombinations = GetVariableCombinations(variables.Count);

            if (multiBit)
            {
                var r = SimplifyOneValueMultibit(constant, resultVector.ToArray());
                if (r != null)
                {
                    CheckSolutionComplexity(r.Value, 1, null);
                    return (0, null, null);
                }
            }
            

            // Linear combination, where the index can be seen as an index into `variableCombinations`,
            // and the element at that index is a list of terms operating over that boolean combination.
            // Term = coeff*(bitMask&basisExpression).
            var linearCombinations = new List<List<(ApInt coeff, ApInt bitMask)>>(variableCombinations.Length);
            for (int i = 0; i < variableCombinations.Length; i++)
                linearCombinations.Add(new((int)width));

            // Keep track of which variables are demanded by which combination,
            // as well as which result vector idx corresponds to which combination.
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var myMask = variableCombinations[i];
                var myIndex = GetGroupSizeIndex(groupSizes, myMask);
                combToMaskAndIdx.Add((myMask, (int)myIndex));
            }

            bool allZeroes = true;
            var varCount = variables.Count;
            bool onlyOneVar = varCount == 1;
            int vecWidth = (int)(varCount == 1 ? 1 : 2u << (ushort)(varCount - 1));

            unsafe
            {
                fixed (ApInt* ptr = &resultVector[0])
                {
                    for (ushort bitIndex = 0; bitIndex < GetNumBitIterations(multiBit, width); bitIndex++)
                    {
                        // If multi-bit simba is enabled, we need to take our base expression
                        // and isolate only the bit at the current bit index.
                        var maskForIndex = multiBit ? (ApInt)1 << bitIndex : moduloMask;
                        // Offset the result vector index such that we are fetching entries for the current bit index.
                        var offset = bitIndex * numCombinations;
                        for (int i = 0; i < variableCombinations.Length; i++)
                        {
                            // Fetch the result vector index for this conjunction.
                            // If the coefficient is zero, we can skip it.
                            var comb = variableCombinations[i];
                            var (trueMask, index) = combToMaskAndIdx[i];
                            var coeff = ptr[(int)offset + index];
                            if (coeff == 0)
                                continue;

                            // Subtract the coefficient from the result vector.
                            allZeroes = false;
                            MultibitSiMBA.SubtractCoeff(moduloMask, ptr, bitIndex, coeff, index, vecWidth, varCount, onlyOneVar, trueMask);

                            // Add an entry to the linear combination list.
                            linearCombinations[i].Add((coeff, maskForIndex));
                        }
                    }
                }
            }

            if(anfDemandedBits != null)
            {
                for(int i = 0; i < linearCombinations.Count; i++)
                {
                    anfDemandedBits.TryAdd((ApInt)i, 0);
                    foreach(var (coeff, mask) in linearCombinations[i])
                    {
                        anfDemandedBits[(ApInt)i] |= mask;
                    }
                }
            }

            // Identify variables that are not present in any conjunction.
            // E.g. if we have a + (b&c), then a is not present in a conjunction, while b is.
            var withNoConjunctions = GetVariablesWithNoConjunctions(variableCombinations, linearCombinations);

            // Simplify the linear combination and turn it back into an expression.
            if (multiBit)
            {
                // If multi-bit, we do not perform the heuristic to exclude parts with only a single variable.
                var (simplified, numTerms) = SimplifyMultiBitGeneric(constant, variableCombinations, linearCombinations);
                CheckSolutionComplexity(simplified);
                lincombTerms = termCount;
                return (withNoConjunctions, null, null);
            }

            else
            {
                AstIdx? univariateParts = null;

                // Make the other parts contain the constant offset.
                AstIdx? otherParts = expr;

                for (int i = 0; i < linearCombinations.Count; i++)
                {
                    // Skip if there are no terms with this basis expression.
                    var entries = linearCombinations[i];
                    if (entries.Count == 0)
                        continue;

                    // For a 1-bit result vector there is only 1 entry for any given basis expression.
                    var entry = entries[0];

                    // Construct the term.
                    var varComb = variableCombinations[i];
                    var term = ConjunctionFromVarMask(entry.coeff, varComb);
                    if (BitOperations.PopCount(varComb) == 1 && (varComb & withNoConjunctions) != 0)
                    {
                        if (univariateParts == null)
                            univariateParts = term;
                        else
                            univariateParts = ctx.Add(univariateParts.Value, term);
                    }

                    else
                    {
                        if (otherParts == null)
                            otherParts = term;
                        else
                            otherParts = ctx.Add(otherParts.Value, term);
                    }
                }

                return (withNoConjunctions, univariateParts, otherParts);
            }
        }

        // Try to find a single boolean term fitting the result vector.
        private unsafe AstIdx? AsPureBoolean(ApInt constantOffset)
        {
            // Is there a single, canonical coefficient for each bit idx?
            var demandedBits = new ulong[(int)numCombinations];
            var bitCoeffs = new ulong[width];
            for (ushort bitIndex = 0; bitIndex < GetNumBitIterations(multiBit, width); bitIndex++)
            {
                var offset = bitIndex * numCombinations;
                for (int i = 0; i < (int)numCombinations; i++)
                {
                    var coeff = resultVector[(int)offset + i];
                    if (coeff == 0)
                        continue;

                    demandedBits[i] |= (ulong)1 << bitIndex;
                    var oldCoeff = bitCoeffs[bitIndex];
                    if (oldCoeff == 0)
                    {
                        bitCoeffs[bitIndex] = coeff;
                        continue;
                    }

                    // If two base bitwise expressions have different coefficients at the same bit index,
                    // we cannot find a solution using this technique.
                    if (oldCoeff != coeff)
                    {
                        return null;
                    }
                }
            }

            // Union all of the demanded bits.
            ulong demandedSum = 0;
            foreach (var db in demandedBits)
                demandedSum |= db;

            // If there are no demanded bits then this is a constant result vector, which will be handled elsewhere.
            if (demandedSum == 0)
                return null;

            // Combine all of the terms, in hopes of finding a single term result.
            var len = BitOperations.PopCount(demandedSum);
            var arr = stackalloc CoeffWithMask[len];
            int arrIdx = 0;
            for (ushort i = 0; i < width; i++)
            {
                // Skip if this bit is not demanded.
                var mask = (ulong)1 << i;
                if ((mask & demandedSum) == 0)
                    continue;

                arr[arrIdx] = new CoeffWithMask(bitCoeffs[i], mask);
                arrIdx++;
            }
            UnmanagedAnalyses.SimplifyDisjointSumMultiply(arr, len, demandedSum);

            CoeffWithMask? result = null;
            var foobar = new List<CoeffWithMask>();
            for (int i = 0; i < len; i++)
            {
                var entry = arr[i];
                if (entry.mask == 0)
                    continue;
                if (entry.coeff == 0)
                    continue;

                // There must only be one coefficient across all terms
                if (result != null)
                    return null;
                result = entry;
            }

            return GetAstForSingleTerm(demandedBits, demandedSum, result.Value.coeff, constantOffset);
        }

        private AstIdx GetAstForSingleTerm(ApInt[] demandedBits, ApInt demandedSum, ApInt coeff, ApInt constantOffset)
        {
            // Try to fit the constant offset into the undemanded bits.
            // TODO: If 'isFit' is false, we still may be able to fit the constant offset by 
            // searching for a different coefficient that divides the constant offset with no remainder.
            bool isFit = false;
            ulong div = 0;
            var cand = FindFittingConstantFactor(coeff, constantOffset, demandedSum);
            if (cand != null)
            {
                isFit = true;
                div = cand.Value;
            }

            Dictionary<ApInt, AstIdx> maskToTerms = new();
            for (int i = 1; i < (int)numCombinations; i++)
            {
                // Skip null terms
                var demandedMask = demandedBits[i];
                if (demandedMask == 0)
                    continue;

                // Compute mask&bitwise
                var boolean = GetBooleanForIndex(i);

                // OR two boolean expressions if they have the same demanded bits mask
                if (!maskToTerms.TryGetValue(demandedMask, out var term))
                {
                    maskToTerms[demandedMask] = boolean;
                }

                else
                {
                    term = ctx.Or(term, boolean);
                    maskToTerms[demandedMask] = term;
                }
            }

            AstIdx? result = null;
            foreach (var (mask, term) in maskToTerms)
            {
                var t = term;
                if (mask != moduloMask)
                    t = ctx.And(ctx.Constant(mask, (byte)width), t);

                result = result == null ? t : ctx.Or(result.Value, t);
            }

            // Partition the constant offset into the boolean expression if possible.
            if (isFit)
            {
                result = ctx.Or(result.Value, ctx.Constant(div, (byte)width));
            }

            // Compute m1*bitop
            result = ctx.Mul(ctx.Constant(coeff, (byte)width), result.Value);
            // Append the constant offset to the outside, if the constant offset does not fit.
            if (!isFit)
                result = ctx.Add(ctx.Constant(constantOffset, (byte)width), result.Value);

            return result.Value;
        }

        private ApInt? FindFittingConstantFactor(ApInt coeff, ApInt constantOffset, ApInt demandedBits)
        {
            // Try a trivial fit.
            var div = moduloMask & (constantOffset / coeff);
            var isDivFit = IsFit(coeff, div, constantOffset, demandedBits);
            if (isDivFit)
                return div;

            // We want to solve for coeff*unknown = constantOffset, where unknown is disjoint to the demanded bits set.
            var solver = new LinearCongruenceSolver(moduloMask);
            var modulus = (UInt128)moduloMask + 1;
            var lc = solver.LinearCongruence(coeff, constantOffset, modulus);
            if (lc == null)
                return null;

            var limit = lc.d;
            if (limit > 255)
                limit = 255;
            for (UInt128 i = 0; i < limit; i++)
            {
                var solution = (ApInt)solver.GetSolution(i, lc);
                if (IsFit(coeff, solution, constantOffset, demandedBits))
                {
                    return (ApInt)solution;
                }
            }

            return null;
        }

        private bool IsFit(ApInt coeff, ApInt div, ApInt constantOffset, ApInt demandedBits)
        {
            // The dividend must be disjoint to the demanded bits mask.
            bool isDisjoint = (div & demandedBits) == 0;
            if (!isDisjoint)
                return false;
            // It must multiply out to the target constant offset.
            bool isMultiple = (moduloMask & (div * coeff)) == constantOffset;
            if (!isMultiple)
                return false;
            return true;
        }

        // Get a naive boolean function for the given result vector idx.
        private AstIdx GetBooleanForIndex(int resultVecIdx)
        {
            return ctx.GetBooleanForIndex((List<AstIdx>)variables, resultVecIdx);
        }

        public static ulong[] GetVariableCombinations(int varCount)
        {
            return MultibitSiMBA.GetVariableCombinations(varCount);
        }

        public static uint GetGroupSizeIndex(List<int> groupSizes, ulong varMask)
        {
            return MultibitSiMBA.GetGroupSizeIndex(groupSizes, varMask);
        }

        private ulong GetVariablesWithNoConjunctions(ulong[] variableCombinations, List<List<(ApInt coeff, ApInt bitMask)>> linearCombinations)
        {
            ulong singleDemandedVars = 0;

            // First we want to identify all of conjunctions that are only used into single variable.
            for (int i = 0; i < linearCombinations.Count; i++)
            {
                // If there are no terms for this combination of variables, discard it.
                var items = linearCombinations[i];
                if (items.Count == 0)
                    continue;

                // If only a single variable is set and it has a non zero coefficient,
                // we want to mark it as demanded.
                var comb = variableCombinations[i];
                if (BitOperations.PopCount(comb) == 1)
                {
                    singleDemandedVars |= comb;
                }

                // Otherwise we have a conjunction of N vars.
                // We want to discard any univariate terms that appear within a conjunction of multiple variables.
                else
                {
                    singleDemandedVars = singleDemandedVars ^ singleDemandedVars & comb;
                }
            }

            return singleDemandedVars;
        }

        private ApInt? TryGetSingleCoeff((ApInt coeff, ApInt mask)[] uniqueCoeffs)
        {
            foreach (var (coeff, mask) in uniqueCoeffs)
            {
                bool success = true;
                for (int i = 0; i < uniqueCoeffs.Length; i++)
                {
                    // Skip ourselves
                    var (otherCoeff, otherMask) = uniqueCoeffs[i];
                    if (otherCoeff == coeff)
                        continue;

                    if (TryRewrite(otherCoeff, coeff, otherMask) == null)
                    {
                        success = false;
                        break;
                    }
                }

                if (success)
                    return coeff;
            }

            return null;
        }

        private (ApInt coeff, ApInt mask)[] TryReduceRows(ApInt constant, ApInt[] withoutConstant)
        {
            var coeffsToMasks = new Dictionary<ApInt, ApInt>(Math.Min(8, (int)numCombinations));
            for (ushort bitIndex = 0; bitIndex < GetNumBitIterations(multiBit, width); bitIndex++)
            {
                var mask = 1ul << bitIndex;
#if DBG
                Log($"\n(x&{mask}): ", false);
#endif

                var offset = bitIndex * numCombinations;
                ApInt curr = 0;
                for (int i = 1; i < (int)numCombinations; i++)
                {
                    var coeff = withoutConstant[(int)offset + i];
                    coeff = refiner.MinimizeCoeffOptimal(coeff, bitIndex);

                    withoutConstant[(int)offset + i] = coeff;
# if DBG
                    Log($"{coeff} + ", false);
#endif

                    if (coeff == 0)
                        continue;

                    // If this is the first non zero coeff in the row, set it.
                    if (curr == 0)
                    {
                        curr = coeff;
                        continue;
                    }

                    // If a row is not aligned, we cannot possibly have a solution.
                    else if (curr != coeff)
                    {
                        return null;
                    }
                }

                // Skip if the whole row was nil
                if (curr == 0)
                    continue;

                coeffsToMasks.TryAdd(curr, 0);
                coeffsToMasks[curr] |= mask;
            }

            var arr = coeffsToMasks.Select(x => (x.Key, x.Value)).ToArray();
            return arr;
        }

        private (ApInt xorMask, ApInt subOffset)? TryRewrite(ApInt coeff, ApInt targetCoeff, ApInt mask)
        {
            ApInt onZero = 0;
            ApInt onOne = moduloMask & (coeff * mask);

            var onZero1 = onZero;
            var onOne1 = onOne;

            var formula1 = moduloMask & (onOne + (targetCoeff * (mask)));
            var formula2 = moduloMask & (onOne + (targetCoeff * (0)));
            var onZero2 = formula1;
            var onOne2 = formula2;

            // In this case we can rewrite the term using a XOR by constant and an addition of a constant offset.
            ApInt xorMask = 0;
            ApInt subOffset = 0;
            if (onZero1 == onZero2 && onOne1 == onOne2)
            {
                xorMask = mask;
                subOffset = onOne;
                return (xorMask, subOffset);
            }

            // In this case we can just change the coefficient without making any other changes.
            else if (refiner.CanChangeCoefficientTo(coeff, targetCoeff, mask))
            {
                xorMask = 0;
                subOffset = 0;
                return (xorMask, subOffset);
            }

            // Otherwise there is no solution, we cannot use this coefficient.
            return null;
        }

        // Algorithm: Start at some point, check if you can change every coefficient to the target coefficient
        private AstIdx? SimplifyOneValueMultibit(ulong constant, ApInt[] withoutConstant)
        {
            // Reduce each row to a canonical form. If a row cannot be canonicalized, there is no solution.
            var uniqueCoeffs = TryReduceRows(constant, withoutConstant);
            if (uniqueCoeffs == null)
                return null;
            // Try to find a single coefficient that all result vector entries can be changed to.
            // If the result is nil, then a single term solution does not exist!
            // Note: It's possible that a solution exists with a coefficient that is not present in the set, though in practice I've never seen this happen.
            var singleCoeff = TryGetSingleCoeff(uniqueCoeffs);
            if (singleCoeff == null)
                return null;

            var targetCoeff = singleCoeff.Value;

            // Fill in a table for XOR masks.
            var xorMasks = new ApInt[withoutConstant.Length];

            // Compute XOR masks and adjusted constant offset
            var casted = (int)numCombinations;
            for (ushort bitIndex = 0; bitIndex < GetNumBitIterations(multiBit, width); bitIndex++)
            {
                var offset = (int)(bitIndex * numCombinations);
                var mask = 1ul << bitIndex;
                for (int i = 0; i < casted; i++)
                {
                    var coeff = withoutConstant[offset + i];
                    if (coeff == 0)
                        continue;

                    if (coeff == targetCoeff)
                        continue;
                    if (i == 0)
                        continue;

                    var (xorMask, subOffset) = TryRewrite(coeff, targetCoeff, mask).Value;
                    xorMasks[offset + i] = xorMask;
                    constant += subOffset;
                    constant &= moduloMask;
                }
            }

            // Walk result vector, get the ones with xor mask.. merge them, then merge the ones without the XOR mask..
            var combinedAnds = new ApInt[(int)numCombinations];
            // We want to group XOR terms by their base bitwise expressions
            var xorMap = new Dictionary<TruthTable, ApInt>();
            ApInt freeMask = moduloMask;
            for (ushort bitIndex = 0; bitIndex < GetNumBitIterations(multiBit, width); bitIndex++)
            {
                var offset = (int)(bitIndex * numCombinations);
                var mask = 1ul << bitIndex;

                ApInt globMask = 0;

                ushort truthIdx = 0;
                var xoredIndices = new TruthTable(variables.Count);

                int withXorCount = 0;
                for (int i = 0; i < (int)numCombinations; i++)
                {
                    var coeff = withoutConstant[offset + i];
                    if (coeff == 0)
                    {
                        truthIdx += 1;
                        continue;
                    }

                    var xorMask = xorMasks[offset + i];
                    freeMask &= ~mask;

                    if (xorMask == 0)
                    {
                        combinedAnds[i] |= mask;
                    }
                    else
                    {
                        withXorCount += 1;
                        globMask = xorMask;
                        xoredIndices.SetBit(truthIdx, true);
                    }

                    truthIdx += 1;
                }

                if (withXorCount > 0)
                {
                    var newOffset = moduloMask & (((ApInt)withXorCount - 1) * globMask);
                    newOffset = moduloMask & (targetCoeff * newOffset);

                    constant += newOffset;
                    xorMap.TryAdd(xoredIndices, globMask);
                    xorMap[xoredIndices] |= globMask;
                }
            }

            // Group by AND / XOR masks.
            var process = (ApInt[] arr) =>
            {
                Dictionary<ApInt, TruthTable> maskToBitwise = new();
                for (int i = 0; i < arr.Length; i++)
                {
                    var mask = arr[i];
                    if (mask == 0)
                        continue;

                    if (maskToBitwise.TryGetValue(mask, out var existing))
                    {
                        existing.SetBit((ushort)i, true);
                    }

                    else
                    {
                        var tt = new TruthTable(variables.Count);
                        tt.SetBit(i, true);
                        maskToBitwise[mask] = tt;
                    }
                }

                return maskToBitwise;
            };

            // Merging needs to be done carefully, because the constant offset adjustment is assuming we have already performed some merging
            // Merge bitwise terms.
           
            var andToBitwise = process(combinedAnds);
            var union = new List<AstIdx>();
            foreach (var x in andToBitwise)
                union.Add(MaskAndMinimize(GetBooleanTableAst(x.Value), AstOp.And, x.Key));
            foreach (var x in xorMap)
                union.Add(MaskAndMinimize(GetBooleanTableAst(x.Key), AstOp.Xor, x.Value));

            var combinedBitwise = ctx.Or(union);
            var solution = TryPartition(combinedBitwise, targetCoeff, constant, freeMask);
            return solution;
        }

        private AstIdx TryPartition(AstIdx bitwise, ApInt coeff, ApInt constant, ApInt freeMask)
        {
            // TODO: Refactor out code duplication
            if (refiner.CanChangeCoefficientTo(coeff, moduloMask, ~freeMask))
            {
                // Alternatively can we find a negated form?
                // TODO: Do we need to negate the free mask?
                // Note: Try (moduloMask*moduloMask) first because a coefficient of 1 can be omitted, yielding a bitwise classification term
                bestSolution = PartitionCoeffAndConstant(bitwise, (moduloMask * moduloMask) & moduloMask, (~constant & moduloMask), (freeMask) & moduloMask);
                if (bestSolution != null)
                {
                    bestSolution = ctx.Neg(bestSolution.Value);
                    return bestSolution.Value;
                }

                // Try to partition the constant offset.
                // Note: In the event that this fails, we could still try other means of partitioning the constant offset.
                // Trying to find a fitting coefficient / OR mask is exponential in the worst case, but there should be a linear time solution.
                // TODO: We need to find a better method of partitioning the constant offset.
                bestSolution = PartitionCoeffAndConstant(bitwise, moduloMask, constant, freeMask);
                if (bestSolution != null)
                    return bestSolution.Value;
            }

            // Try to partition the constant offset.
            // Note: In the event that this fails, we could still try other means of partitioning the constant offset.
            // Trying to find a fitting coefficient / OR mask is exponential in the worst case, but there should be a linear time solution.
            // TODO: We need to find a better method of partitioning the constant offset.
            bestSolution = PartitionCoeffAndConstant(bitwise, coeff, constant, freeMask);
            if (bestSolution != null)
                return bestSolution.Value;

            // Alternatively can we find a negated form?
            // TODO: Do we need to negate the free mask?
            bestSolution = PartitionCoeffAndConstant(bitwise, (coeff * moduloMask) & moduloMask, (~constant & moduloMask), (freeMask) & moduloMask);
            if (bestSolution != null)
            {
                bestSolution = ctx.Neg(bestSolution.Value);
                return bestSolution.Value;
            }

            // If all else fails, we cannot find a single term solution.
            // Place the constant offset on the outside of the expression.
            var mul = ctx.Mul(ctx.Constant(coeff, width), bitwise);
            if (constant == 0)
                return mul;

            var constTerm = ctx.Constant(constant, width);
            return ctx.Add(constTerm, mul);
        }

        // Heuristic: Identify flexibility in the coefficient, try again...
        private AstIdx? PartitionCoeffAndConstant(AstIdx bitwise, ApInt coeff, ApInt constant, ApInt freeMask)
        {
            if (constant == 0)
                return ctx.Mul(ctx.Constant(coeff, width), bitwise);

            // Trivial partition: -c1 + (-c1)*(x) => c1*~x,
            // or alternatively c1 + (c1*x) => (-c1)*~x
            if (coeff == constant)
            {
                var constantId = ctx.Constant(moduloMask * constant, width);
                return ctx.Mul(constantId, ctx.Neg(bitwise));
            }

            var modulus = (UInt128)moduloMask + 1;
            var solver = new LinearCongruenceSolver((UInt128)moduloMask);
            for (ushort bitIdx = 0; bitIdx < width; bitIdx++)
            {
                var bitMask = 1ul << bitIdx;
                if ((bitMask & freeMask) == 0)
                    continue;

                var lc = solver.LinearCongruence(bitMask, constant, moduloMask);
                var limit = lc.d;
                if (limit > 255)
                    limit = 255;
                for (UInt128 i = 0; i < limit; i++)
                {
                    var solution = (ApInt)solver.GetSolution(i, lc);
                    if (!refiner.CanChangeCoefficientTo(coeff, (ApInt)solution, moduloMask & (~freeMask)))
                        continue;

                    bitwise = ctx.Or(ctx.Constant(bitMask, width), bitwise);
                    return ctx.Mul(ctx.Constant(solution, width), bitwise);
                }
            }


            // If the sign bit pops out, try to move it back in.
            var signBit = 1ul << ((ushort)width - 1);
            if (constant == signBit)
            {
                var withoutSign = SubtractSignBit(coeff, bitwise);
                if (withoutSign != null)
                {
                    var coeffId = ctx.Constant(coeff, width);
                    return ctx.Mul(coeffId, withoutSign.Value);
                }
            }

            // Try to fit the constant offset into the undemanded bits.
            var coeffIdx = ctx.Constant(coeff, width);
            var fittingMask = FindFittingConstantFactor(coeff, constant, (~freeMask) & moduloMask);
            if (fittingMask != null)
            {
                var mask = ctx.Constant(fittingMask.Value, width);
                return ctx.Mul(coeffIdx, ctx.Or(mask, bitwise));
            }

            // If the constant offset does not fit, try to remove the sign bit from the constant offset,
            // then look for a fitting mask.
            ApInt adjusted = moduloMask & (constant - signBit);
            fittingMask = FindFittingConstantFactor(coeff, moduloMask & adjusted, (~freeMask) & moduloMask);
            if (fittingMask != null)
            {
                // Maybe TODO(probably not): Check if OR mask overlaps with sign bit mask.
                var withoutSb = SubtractSignBit(coeff, bitwise);
                if (withoutSb != null)
                {
                    var mask = ctx.Constant(fittingMask.Value, width);
                    return ctx.Mul(coeffIdx, ctx.Or(mask, withoutSb.Value));
                }
            }

            return null;
        }

        private AstIdx? SubtractSignBit(ApInt coeff, AstIdx bitwise)
        {
            var constant = 1ul << ((ushort)width - 1);
            var xorMask1 = 1ul << (ushort)(width - 1);
            var xorMask2 = 1ul << (ushort)(width - 2);

            ApInt xorMask = 0;
            if ((moduloMask & (xorMask1 * coeff)) == constant)
                xorMask = xorMask1;
            else if ((moduloMask & (xorMask2 * coeff)) == constant)
                xorMask = xorMask2;
            else
                return null;

            return ctx.Xor(ctx.Constant(xorMask, width), bitwise);
        }

        private unsafe AstIdx GetBooleanTableAst(TruthTable table)
        {
            var res = BooleanMinimizer.GetBitwise(ctx, variables, table.Clone());
            return res;
        }

        private AstIdx MaskAndMinimize(AstIdx idx, AstOp opcode, ApInt mask)
        {
            var maskId = ctx.Constant(mask, width);
            if (opcode == AstOp.Xor)
                idx = ctx.And(maskId, idx);
            return ctx.Binop(opcode, maskId, idx);
        }

        // Convert a N-bit result vector into a linear combination.
        private (AstIdx expr, int termCount) SimplifyMultiBitGeneric(ApInt constantOffset, ulong[] variableCombinations, List<List<(ApInt coeff, ApInt bitMask)>> linearCombinations)
        {
            Log("Initial solution: ");
            if (constantOffset != 0)
                Log(ctx.Constant(constantOffset, width));

            // Construct the lin comb vector.
            List<Dictionary<ApInt, ApInt>> results = new();
            for (int i = 0; i < linearCombinations.Count; i++)
            {
                // Skip if there are no entries for this basis expression.
                var entries = linearCombinations[i];
                if (entries.Count == 0)
                {
                    results.Add(new());
                    continue;
                }

                // Try to simplify the linear combination.
                var varComb = variableCombinations[i];
                var coeffToMask = refiner.SimplifyMultibitEntry(entries);
                results.Add(coeffToMask);

                // TODO: Comment
                foreach (var (coeff, mask) in coeffToMask)
                {
                    if (coeff == 0 || mask == 0)
                        continue;
                    var conj = ConjunctionFromVarMask(coeff, varComb, mask);
                    Log(conj);
                }
            }

            // We have a near-optimal linear combination of conjunctions.
            // Try to apply several more refinements, that are simpler but don't necessarily only result in a linear combinaton of conjunctions(e.g. we now allow XORs).
            var final = TryRefineMultibit(constantOffset, variableCombinations, results);

            return (final, GetCost(ctx, final, false));
        }

        private AstIdx TryRefineMultibit(ApInt constantOffset, ulong[] variableCombinations, List<Dictionary<ApInt, ApInt>> linearCombinations)
        {
            List<List<AstIdx>> extractedTerms = new();
            for (int i = 0; i < linearCombinations.Count; i++)
            {
                (constantOffset, var newTerms) = TryRefineMultibitEntry(constantOffset, variableCombinations[i], linearCombinations[i]);
                extractedTerms.Add(newTerms);
            }

            // Construct the linear combination.
            AstIdx? final = constantOffset != 0 ? ctx.Constant(constantOffset, width) : null;
            for (int i = 0; i < linearCombinations.Count; i++)
            {
                var newTerms = extractedTerms[i];
                foreach (var t in newTerms)
                {
                    if (final == null)
                        final = t;
                    else
                        final = ctx.Add(final.Value, t);
                }

                foreach (var (coeff, mask) in linearCombinations[i])
                {
                    if (coeff == 0)
                        continue;
                    if (mask == 0)
                        continue;

                    var newTerm = ConjunctionFromVarMask(coeff, variableCombinations[i], mask);
                    if (final == null)
                        final = newTerm;
                    else
                        final = ctx.Add(final.Value, newTerm);
                }
            }

#if DBG
            Log($"New solution: {ctx.GetAstString(final.Value)}");
#endif

            if (final == null)
                final = ctx.Constant(0, width);
            return final.Value;
        }

        // Given a linear combination where every node is using the same basis expression, try to find the simplest possible representation.
        private (ApInt newConstantOffset, List<AstIdx> newTerms) TryRefineMultibitEntry(ApInt constantOffset, ulong varComb, Dictionary<ApInt, ApInt> coeffToMask)
        {
            refiner.TryReduceMasks(coeffToMask);

            // If we succeeded, update accordingly.
            List<AstIdx> newTerms = new();
            var processXor = ((ApInt adjustedConstantOffset, ApInt coeff, ApInt xorMask)? maybeXor) =>
            {
                if (maybeXor == null)
                    return;
                // Update the constant offset.
                var xor = maybeXor.Value;
                constantOffset = xor.adjustedConstantOffset;

                // Add a new XOR term.
                var xorConst = ctx.Constant(xor.xorMask, width);
                var xorNode = ctx.Xor(xorConst, ConjunctionFromVarMask(1, varComb, null));
                var newTerm = ctx.Mul(ctx.Constant(xor.coeff, width), xorNode);
                newTerms.Add(newTerm);
            };

            // If we succeeded, update accordingly.
            var processOr = ((ApInt adjustedConstantOffset, ApInt coeff, ApInt orMask)? maybeOr) =>
            {
                if (maybeOr == null)
                    return;
                // Update the constant offset.
                var or = maybeOr.Value;
                constantOffset = or.adjustedConstantOffset;

                // Add a new OR term.
                // If the mask is -1 then we ignore it.
                var conj = ConjunctionFromVarMask(1, varComb, null);
                AstIdx? orNode = null;
                if (or.orMask != moduloMask)
                {
                    var orConst = ctx.Constant(or.orMask, width);
                    orNode = ctx.Or(orConst, conj);
                }

                else
                {
                    orNode = conj;
                }

                var newTerm = ctx.Mul(ctx.Constant(or.coeff, width), orNode.Value);
                newTerms.Add(newTerm);
            };

            var processIsolation = (ApInt? coeff) =>
            {
                if (coeff == null || coeff.Value == 0)
                    return;

                var conj = ConjunctionFromVarMask(coeff.Value, varComb, null);
                newTerms.Add(conj);
            };

            // Try to identify trivial XORs by constant.
            processXor(refiner.TrySimplifyXor(constantOffset, coeffToMask));

            // Try to identify whole instances of variables.
            var maybeIsolated = refiner.TryIsolateSingleVariableConjunction(coeffToMask);
            processIsolation(maybeIsolated);

            // If we succeeded in isolating out a whole term(no bit mask), try again to factor out a XOR by constant.
            if (maybeIsolated != null)
                processXor(refiner.TrySimplifyXor(constantOffset, coeffToMask));

            // While recovering XORs is almost guaranteed to be profitable, 
            // recovering bitwise ORs is generally not. The constant offset gets partitioned into
            // too many terms, which increases the complexity.
            // There may be a heuristic that can be used here.
            while (false)
            {
                var maybeOr = refiner.TrySimplifyOr(constantOffset, coeffToMask);
                if (maybeOr == null)
                    break;
                processOr(maybeOr);
            }

            refiner.TryReduceMasks(coeffToMask);

            // If enabled, use just one level of recursion to search for a simpler combination
            // of conjunctions after subtracting the constant offset.
            if (tryDecomposeMultiBitBases)
            {
                // TODO: Reimplement this step.
            }

            return (constantOffset, newTerms);
        }

        private AstIdx? Conjunction(ApInt coeff, IReadOnlyList<int> variables, ApInt? mask = null)
        {
            Debug.Assert(variables.Count > 0);
            if (coeff == 0)
                return null;

            AstIdx? conj = null;
            foreach (var v in variables)
            {
                var op = this.variables[v];
                if (conj == null)
                    conj = op;
                else
                    conj = ctx.And(conj.Value, op);
            }

            if (mask != null)
                conj = ctx.And(ctx.Constant(mask.Value, width), conj.Value);
            return Term(conj.Value, coeff);
        }

        private AstIdx ConjunctionFromVarMask(ApInt coeff, ApInt varMask, ApInt? mask = null)
            => ConjunctionFromVarMask(ctx, variables, coeff, varMask, mask);

        public static AstIdx ConjunctionFromVarMask(AstCtx ctx, IReadOnlyList<AstIdx> variables, ApInt coeff, ApInt varMask, ApInt? mask = null)
        {
            Debug.Assert(variables.Count > 0);
            Debug.Assert(BitOperations.PopCount(varMask) > 0);

            var casted = (List<AstIdx>)variables;
            var conj = ctx.GetConjunctionFromVarMask(casted, varMask);

            if (mask != null)
            {
                var width = ctx.GetWidth(variables[0]);
                conj = ctx.And(ctx.Constant(mask.Value, width), conj);
            }
            return Term(ctx, conj, coeff);
        }

        private AstIdx? Conjunction(ApInt coeff, AstIdx conj, ApInt? mask = null)
        {
            Debug.Assert(variables.Count > 0);
            if (coeff == 0)
                return null;

            if (mask != null)
                conj = ctx.And(ctx.Constant(mask.Value, width), conj);
            return Term(conj, coeff);
        }

        private AstIdx Term(AstIdx bitwise, ApInt coeff)
            => Term(ctx, bitwise, coeff);

        public static AstIdx Term(AstCtx ctx, AstIdx bitwise, ApInt coeff)
        {
            if (coeff == 1)
                return bitwise;

            var coeffAst = ctx.Constant(coeff, ctx.GetWidth(bitwise));
            return ctx.Mul(coeffAst, bitwise);
        }

        private ApInt NegateCoefficient(ApInt coeff)
        {
            // Note that the mask & maxValue * a should be equivalent to taking -a under the modular field.
            return moduloMask & ApInt.MaxValue * coeff;
        }

        // Determine the optimal two term solution fitting the result vector
        private AstIdx? DetermineCombOfTwoFast(ApInt coeff1, ApInt coeff2, ApInt[] vec = null, bool secNegated = false)
        {
            if (vec == null)
                vec = resultVector;

            var tt1 = new TruthTable(variables.Count);
            var tt2 = new TruthTable(variables.Count);
            var d = GetDecisionVectorFast(coeff1, coeff2, vec);

            int numSolutions = 0;
            uint bestCost = uint.MaxValue;
            AstIdx? bestSolution = null;

            EnumerateTwoTermSolutions(ref numSolutions, ref bestCost, ref bestSolution, d, 0, coeff1, coeff2, tt1, tt2, secNegated);
            return bestSolution;
        }

        // Given a two term linear MBA, exhaustively enumerate all possible term combinations fitting the result vector,
        // picking the optimal one based on some cost function.
        private void EnumerateTwoTermSolutions(ref int numSolutions, ref uint bestCost, ref AstIdx? bestSolution, DecisionTable cases, int i, ApInt coeff1, ApInt coeff2, TruthTable tt1, TruthTable tt2, bool secNegated = false)
        {
            // Do not explore more than 32 solutions! 
            if (numSolutions >= 32)
                return;

            // We found a solution, now handle it:
            if (i >= cases.NumBits)
            {
                numSolutions += 1;

                // Don't allocate an AST for this solution if it would be worse than the best result we found so far.
                var firstCost = TableDatabase.Instance.GetTableEntryCost(ctx, variables.Count, (int)tt1.arr[0]);
                var secondCost = TableDatabase.Instance.GetTableEntryCost(ctx, variables.Count, (int)tt2.arr[0]);
                var newCost = firstCost + secondCost;
                if (newCost >= bestCost)
                    return;

                var first = BooleanMinimizer.GetBitwise(ctx, variables, tt1);
                var second = BooleanMinimizer.GetBitwise(ctx, variables, tt2, secNegated);

                // Compose the terms together, optionally negating the second coefficient if requested.
                var secondCoeff = secNegated ? NegateCoefficient(coeff2) : coeff2;
                var e = Compose(new() { first, second }, new() { coeff1, secondCoeff });

                bestSolution = e;
                bestCost = newCost;
                return;
            }

            var value = cases.GetDecision(i);
            if (value.HasFlag(Decision.None))
            {
                var old1 = tt1.GetBit(i);
                var old2 = tt2.GetBit(i);
                tt1.SetBit(i, false);
                tt2.SetBit(i, false);
                EnumerateTwoTermSolutions(ref numSolutions, ref bestCost, ref bestSolution, cases, i + 1, coeff1, coeff2, tt1, tt2, secNegated);
                tt1.SetBit(i, old1);
                tt2.SetBit(i, old2);
            }

            if (value.HasFlag(Decision.First))
            {
                var old1 = tt1.GetBit(i);
                tt1.SetBit(i, true);
                EnumerateTwoTermSolutions(ref numSolutions, ref bestCost, ref bestSolution, cases, i + 1, coeff1, coeff2, tt1, tt2, secNegated);
                tt1.SetBit(i, old1);
            }

            if (value.HasFlag(Decision.Second))
            {
                var old2 = tt2.GetBit(i);
                tt2.SetBit(i, true);
                EnumerateTwoTermSolutions(ref numSolutions, ref bestCost, ref bestSolution, cases, i + 1, coeff1, coeff2, tt1, tt2, secNegated);
                tt2.SetBit(i, old2);
            }

            if (value.HasFlag(Decision.Both))
            {
                var old1 = tt1.GetBit(i);
                var old2 = tt2.GetBit(i);
                tt1.SetBit(i, true);
                tt2.SetBit(i, true);
                EnumerateTwoTermSolutions(ref numSolutions, ref bestCost, ref bestSolution, cases, i + 1, coeff1, coeff2, tt1, tt2, secNegated);
                tt1.SetBit(i, old1);
                tt2.SetBit(i, old2);
            }
        }

        private DecisionTable GetDecisionVectorFast(ApInt coeff1, ApInt coeff2, ApInt[] vec)
        {
            if (vec == null)
                vec = resultVector;

            var e = new DecisionTable(variables.Count);

            for(int i = 0; i < vec.Length; i++)
            {
                var r = vec[i];

                var f = (r - coeff1 & moduloMask) == 0;
                var s = (r - coeff2 & moduloMask) == 0;
                var b = (r - coeff1 - coeff2 & moduloMask) == 0;
                // For more variables, this would take too long.
                if (r == 0 && variables.Count > 4)
                    b = false;
                // Same.
                if (f && s && variables.Count > 4)
                    s = false;

                if ((r & moduloMask) == 0)
                    e.AddDecision(i, Decision.None);
                if (b)
                    e.AddDecision(i, Decision.Both);
                if (f)
                    e.AddDecision(i, Decision.First);
                if (s)
                    e.AddDecision(i, Decision.Second);

                Debug.Assert((byte)e.arr[i] != 0);
            }

            return e;
        }

        private AstIdx Compose(List<AstIdx> bitwises, List<ApInt> coeffs)
        {
            Debug.Assert(bitwises.Count > 0);
            Debug.Assert(bitwises.Count == coeffs.Count);

            AstIdx? comb = null;
            for (int i = 0; i < bitwises.Count; i++)
            {
                uint term = 0;
                if (coeffs[i] == 1)
                {
                    term = bitwises[i];
                }

                else
                {
                    var coeff = ctx.Constant(coeffs[i], width);
                    term = ctx.Mul(coeff, bitwises[i]);
                }
                if (comb == null)
                    comb = term;
                else
                    comb = ctx.Add(comb.Value, term);
            }

            return comb.Value;
        }

        // Returns true iff a is double b in the modular field
        private bool IsSumModulo(ApInt s1, ApInt s2, ApInt a)
        {
            return (moduloMask & s1 + s2) == a;
        }

        // Returns true iff a is double b in the modular field
        private bool IsDoubleModulo(ApInt a, ApInt b)
        {
            var mul = moduloMask & (2 * b);
            return mul == a;
        }

        // Build an expression by summing up bitwise expressions, each corresponding to a value in the lookup table
        // and multiplied by this value thereafter.
        private AstIdx ExpressionForEachUniqueValue(HashSet<ApInt> resultSet)
        {
            AstIdx? expr = null;
            foreach (var r in resultSet)
            {
                // Skip zero entries.
                if (r == 0)
                    continue;

                var term = TermRefinement(r);
                if (expr == null)
                    expr = term;
                else
                    expr = ctx.Add(expr.Value, term);
            }

            return expr.Value;
        }

        // Returns a simple bitwise expression corresponding to the positions where
        // the vector of results for truth value combinations has a value of r1 or
        // rAlt to the given expression.
        private AstIdx TermRefinement(ApInt r1, ApInt? rAlt = null)
        {
            var t = new TruthTable(variables.Count);
            for(int i = 0; i < resultVector.Length; i++)
            {
                var r2 = resultVector[i];
                var cond = r2 == r1 || rAlt != null && r2 == rAlt.Value ? true : false;
                t.SetBit(i, cond);
            }

            // Return m1 * bitop.
            var bitwise = BooleanMinimizer.GetBitwise(ctx, variables, t);
            return Term(bitwise, r1);
        }

        // Check whether the given solution is less complex than the currently
        // optimal known one. If so or if there is not yet any solution known, store
        // its computed complexity values. The term count is optionally given. If a
        // constant is given, this constant has to be added tot he expression and
        // the given term count has to be incremented by one accordingly.
        private void CheckSolutionComplexity(AstIdx e, int? t = null, AstIdx? constant = null)
        {
            if (constant != null)
            {
                e = AddConstant(e, constant.Value);
            }

            if(bestSolution == null)
            {
                bestSolution = e;
                return;
            }

            // Take the new solution if the cost is lower.
            var cost1 = ctx.GetCost(bestSolution.Value);
            var cost2 = ctx.GetCost(e);
            if(cost2 < cost1)
                bestSolution = e;
        }

        private AstIdx AddConstant(AstIdx expr, AstIdx constant)
        {
            var constValue = ctx.GetConstantValue(constant);
            if (constValue == 0)
                return expr;

            return ctx.Add(constant, expr);
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private void Log(string message, bool newLine = true)
        {
#if DBG
            if (newLine)
                Console.WriteLine(message);
            else
                Console.Write(message);
#endif
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private void Log(AstIdx conj)
        {
#if DBG
            if (newLine)
                Console.WriteLine(ctx.GetAstString(conj));
            else
                Console.Write(ctx.GetAstString(conj) + " + ");
#endif
        }
    }
}
