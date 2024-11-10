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

        private readonly Action<ulong[], ulong>? resultVectorHook;

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

        public static AstIdx Run(uint bitSize, AstCtx ctx, AstIdx? ast, bool alreadySplit = false, bool multiBit = false, bool tryDecomposeMultiBitBases = false, IReadOnlyList<AstIdx> variables = null, Action<ulong[], ApInt>? resultVectorHook = null, ApInt[] inVec = null)
        {
            if (variables == null)
                variables = ctx.CollectVariables(ast.Value);
            return new LinearSimplifier(ctx, ast, variables, bitSize, refine: true, multiBit, tryDecomposeMultiBitBases, resultVectorHook, inVec).Simplify(false, alreadySplit);
        }

        public LinearSimplifier(AstCtx ctx, AstIdx? ast, IReadOnlyList<AstIdx> variables, uint bitSize, bool refine = true, bool multiBit = false, bool tryDecomposeMultiBitBases = true, Action<ulong[], ApInt>? resultVectorHook = null, ApInt[] inVec = null)
        {
            this.initialInput = ast;
            this.ctx = ctx;
            this.variables = variables;
            width = bitSize;
            this.refine = refine;
            this.multiBit = multiBit;
            this.tryDecomposeMultiBitBases = tryDecomposeMultiBitBases;
            this.resultVectorHook = resultVectorHook;
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

            if (resultVectorHook != null)
            {
                resultVectorHook(resultVector, numCombinations);
                return;
            }

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
            uint capacity = (uint)(numCombinations * (multiBit ? bitWidth : 1u));
            var resultVec = new ApInt[capacity];
            fixed (ulong* vecPtr = &resultVec[0])
            {
                ctx.JitEvaluate(ast, mask, multiBit, bitWidth, variables.ToArray(), numCombinations, MultibitSiMBA.JitPage.Value, (nint)vecPtr);
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
            if(multiBit)
                TryMakeLinear();

            if (multiBit)
            {
                return SimplifyMultibit(constant);
            }

            return SimplifyOneBit(constant, useZ3, alreadySplit);
        }

        // If we have a multi-bit result vector, try to rewrite as a linear result vector. If possible, update state accordingly.
        private unsafe bool TryMakeLinear()
        {
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

            multiBit = false;
            Array.Resize(ref resultVector, (int)numCombinations);

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

            // If no terms exist, we have a constant.
            if (coeffToTable.Count == 0)
                return ctx.Constant(constant, width);
            // If only a single term exists, we can immediately find the optimal solution.
            // For more terms we need to take special care to eliminate dead variables, but the boolean minimizer will eliminate dead variables for the single term case!
            if (coeffToTable.Count == 1)
            {
                var (coeff, truthTable) = coeffToTable.First();
                var single = SimplifyOneTerm(constant, coeff, truthTable);
                return single;
            }

            // (1) Construct a linear combination using ANF as the basis. This will roughly tell us which variables are dependent upon one another.
            var (variableCombinations, linearCombinations) = GetAnf();

            // (2) Try to partition the terms into disjoint variable sets.
            int anfCost = constant == 0 ? 0 : 1;
            ApInt demandedVariables = 0;
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
                demandedVariables |= combMask;
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
            foreach(var (coeff, table) in coeffToTable)
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

            // Convert the result vector to a set.
            HashSet<ApInt> resultSet = null;
            resultSet = resultVector.ToHashSet();

            // Clone the result vector.
            ApInt[] clone = null;
            clone = new ApInt[resultVector.Length];
            resultVector.CopyTo(clone, 0);

            // Simplify the generic part.
            // TODO: If (a) alreadySplit is false, (b) there are any terms with only a single variable, and (c) there is more than one term,
            // extract out those terms.
            var (singleDemandedVars, univariateParts, otherParts) = SimplifyGeneric(constant);

            AstIdx? combined = null;
            if (otherParts != null)
                combined = otherParts;
            if (univariateParts != null)
                combined = combined == null ? univariateParts : ctx.Add(combined.Value, univariateParts.Value);

            if (combined == null)
                combined = ctx.Constant(0, width);

            lincombTerms = GetCost(ctx, combined.Value, false);

            CheckSolutionComplexity(combined.Value);

            resultVector = clone;

            // If there is more than 3 variables:
            if (variables.Count > 3)
            {
                if (alreadySplit)
                {
                    //resultSet = resultVector.ToHashSet();
                    if (refine && resultSet.Count == 1)
                    {
                        SimplifyOneValue(resultSet);
                    }

                    else
                    {
                        //SimplifyGeneric();
                        if (refine)
                        {
                            resultVector = clone;
                            TryRefine();
                        }
                    }
                }

                else
                {
                    // If we cannot simplify the linear MBA further using knowledge of a newly reduced variable count,
                    // try to partition the linear MBA by it's variables, then simplify further.
                    if (!TrySimplifyFewerVariables())
                    {
                        TrySplit();
                    }
                }
            }

            else
            {
                resultSet = resultVector.ToHashSet();
                if (refine && resultSet.Count == 1)
                {
                    SimplifyOneValue(resultSet);
                }

                else
                {
                    //SimplifyGeneric();
                    if (refine)
                    {
                        resultVector = clone;
                        TryRefine();
                    }
                }
            }

            Debug.Assert(bestSolution != null);
            return bestSolution.Value;
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

        private static ApInt SubtractConstantOffset(ApInt moduloMask, ApInt[] resultVector, int numCombinations)
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
                            ptr[comb + i] = moduloMask & (ptr[comb + i] - constantOffset);
                        }

                        bitIndex += 1;
                    }
                }
            }

            return constant;
        }

        private new (ApInt[], List<List<(ApInt coeff, ApInt bitMask)>>) GetAnf()
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
                var r = SimplifyOneValueMultibit(constant, resultVector.ToArray(), variableCombinations).Value;
                if (r != null)
                {
                    CheckSolutionComplexity(r, 1, null);
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

        private void ExtractVarsWithNoConjunctions(ulong varsWithNoConjunctions)
        {
            throw new InvalidOperationException("TODO");
            // If there are no variables to isolate, just skip this step.
            if (varsWithNoConjunctions == 0)
                return;

            var constantOffset = resultVector[0];
            List<AstIdx> terms = new();
            while (varsWithNoConjunctions != 0)
            {
                var lsb = BitOperations.TrailingZeroCount(varsWithNoConjunctions);
                var op = variables[lsb];

                // Fetch the coefficient over this single variable.
                var varMask = 1ul << (ushort)lsb;
                var coeff = resultVector[varMask];

                // Subtract out the constant offset, because we don't know whether 
                // other steps have already done this.
                coeff = moduloMask & coeff - constantOffset;

                for (int i = 0; i < resultVector.Length; i++)
                {
                    // Skip if this term does not have the variable set.
                    if (((uint)i & varMask) == 0)
                        continue;

                    // Subtract out the coefficient over this variable.
                    resultVector[i] = moduloMask & resultVector[i] - coeff;
                }

                terms.Add(Term(op, coeff));

                varsWithNoConjunctions ^= varMask;
            }

            Debug.Assert(terms.Count > 0);
            var sum = ctx.Add(terms);
            univariateParts = sum;
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

        private AstIdx? SimplifyOneValueMultibit(ulong constant, ApInt[] withoutConstant, ApInt[] variableCombinations)
        {
            // Algorithm: Start at some point, check if you can change every coefficient to the target coefficient
            bool truthTableIdx = true;
            if (!truthTableIdx)
                variableCombinations = new List<ApInt>() { 0 }.Concat(variableCombinations).ToArray();

            var getConj = (ApInt i, ApInt? mask) =>
            {
                if (truthTableIdx)
                {
                    var boolean = GetBooleanForIndex((int)i);
                    if (mask == null)
                        return boolean;

                    return ctx.And(ctx.Constant(mask.Value, width), boolean);
                }

                return ConjunctionFromVarMask(1, i, mask);
            };

            AstIdx.ctx = ctx;

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

            // Merging needs to be carefully, because the constant offset adjustment is assuming we have already performed some merging
            // Merge bitwise terms.
            var andToBitwise = process(combinedAnds);
            var union = new List<AstIdx>();
            foreach(var x in andToBitwise)
                union.Add(MaskAndMinimize(GetBooleanTableAst(x.Value), AstOp.And, x.Key));
            foreach (var x in xorMap)
                union.Add(MaskAndMinimize(GetBooleanTableAst(x.Key), AstOp.Xor, x.Value));


            var combinedBitwise = ctx.Or(union);

            var bar = TryPartition(combinedBitwise, targetCoeff, constant, freeMask);
            return bar;
        }

        private AstIdx TryPartition(AstIdx bitwise, ApInt coeff, ApInt constant, ApInt freeMask)
        {
            // Identify how many undemanded bits there are in the coefficient.
            // As a heuristic, how do prune the search space for coeff candidates.
            // You have a set of possible coefficients, and a set of possible undemanded bits where you can cram the constant offset..
            var undemanded = refiner.FindUndemandedCoeffBits(coeff, moduloMask & ~freeMask, constant);
            var minimal = refiner.FindMinimalCoeff(coeff, moduloMask & ~freeMask, constant);
            var maximal = refiner.FindMaximalCoeff(coeff, moduloMask & ~freeMask);

            // Try to partition the constant offset.
            // Note: In the event that this fails, we could still try other means of partitioning the constant offset.
            // Trying to find a fitting coefficient / OR mask is exponential in the worst case, but there should be a linear time solution.
            bestSolution = PartitionCoeffAndConstant(bitwise, coeff, constant, freeMask);
            if (bestSolution != null)
                return bestSolution.Value;

            // If all else fails, we cannot find a single term solution.
            // Place the constant offset on the outside of the expression.
            var constTerm = ctx.Constant(constant, width);
            var mul = ctx.Mul(ctx.Constant(coeff, width), bitwise);
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
                if (withoutSign == null)
                    throw new InvalidOperationException($"Failed to partition constant offset!");
                var coeffId = ctx.Constant(coeff, width);
                return ctx.Mul(coeffId, withoutSign.Value);
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

        // For the optimal currently known solution, check how many variables it uses effectively.
        // If it is not more than 3, run the simplification procedure again for that variable count,
        // since we might be able to simplify the expression using truth tables.
        bool TrySimplifyFewerVariables()
        {
            Debug.Assert(bestSolution != null);

            // Get the unique set of variables.
            // Note that this mutates the variable objects such that their 
            // index field is updated based off of their alphabetical name ordering.
            var newVariables = ctx.CollectVariables(bestSolution.Value);

            // If there are more than three variables, we cannot simplify it any further.
            if (newVariables.Count > 3)
                return false;
            // If the variable count remains unchanged, we cannot simplify any further.
            if (newVariables.Count == variables.Count)
                return false;

            // Run the linear MBA simplifier on the expression.
            var expr = Run(width, ctx, bestSolution.Value);
            CheckSolutionComplexity(expr);

            return true;
        }

        // Try to split the given expression, which is supposed to be a linear MBA,
        // into subexpressions with at most 3 variables each such that the list of 
        // occurring variables is partitioned thereby, simplify these subexpressions
        // and compose the results.
        void TrySplit()
        {
            var expr = bestSolution.Value;
            Debug.Assert(expr != null);

            var l = new List<AstIdx>();
            SplitIntoTerms(ctx, expr, l);
            var v = FindVariablesInTerms(l);

            var (constIdx, l1, l2, l3, lrem) = PartitionTermsByVariableCount(l, v);
            var partition = Partition(v, l1, l2, l3, lrem);
            var e = SimplifyPartsAndCompose(l, partition, constIdx, lrem.ToHashSet());
            CheckSolutionComplexity(e);
            //Debugger.Break();
        }

        private int CountTerms(AstIdx expr)
        {
            var terms = new List<AstIdx>();
            SplitIntoTerms(ctx, expr, terms);
            return terms.Count;
        }

        private static void SplitIntoTerms(AstCtx ctx, AstIdx expr, List<AstIdx> terms)
        {
            SplitIntoTermsByOpcode(AstOp.Add, ctx, expr, terms);
        }

        public static void SplitIntoTermsByOpcode(AstOp op, AstCtx ctx, AstIdx expr, List<AstIdx> terms)
        {
            var opcode = ctx.GetOpcode(expr);
            if (opcode == op)
            {
                var op1 = ctx.GetOp0(expr);
                var op2 = ctx.GetOp1(expr);
                if (ctx.GetOpcode(op1) == op)
                {
                    SplitIntoTerms(ctx, op1, terms);
                }

                else
                {
                    terms.Add(op1);
                }

                if (ctx.GetOpcode(op2) == op)
                {
                    SplitIntoTerms(ctx, op2, terms);
                }

                else
                {
                    terms.Add(op2);
                }
            }

            else
            {
                terms.Add(expr);
            }
        }

        private List<HashSet<int>> FindVariablesInTerms(List<AstIdx> terms)
        {
            var sets = new List<HashSet<int>>();
            foreach (var e in terms)
            {
                //var vars = LinearMbaGen.GetVarSet(e).Select(x => variables.IndexOf(x)).ToHashSet();
                var vars = ctx.CollectVariables(e).Select(x => variables.IndexOf(x)).ToHashSet();
                sets.Add(vars);
            }

            return sets;
        }

        private (int, List<int>, List<int>, List<int>, List<int>) PartitionTermsByVariableCount(List<AstIdx> l, List<HashSet<int>> v)
        {
            var constIdx = -1;

            // Terms with 1 variable.
            var l1 = new List<int>();
            // Terms with 2 variables.
            var l2 = new List<int>();
            // Terms with 3 variables.
            var l3 = new List<int>();
            // Terms with at least 4 variables.
            var lrem = new List<int>();

            foreach (var i in RangeUtil.Get(v.Count))
            {
                var lv = v[i].Count;
                if (lv == 0)
                {
                    Debug.Assert(constIdx == -1);
                    constIdx = i;
                    continue;
                }

                else if (lv == 1)
                {
                    l1.Add(i);
                }

                else if (lv == 2)
                {
                    l2.Add(i);
                }

                else if (lv == 3)
                {
                    l3.Add(i);
                }

                else
                {
                    lrem.Add(i);
                }
            }

            return (constIdx, l1, l2, l3, lrem);
        }

        // Partition the variables of the given list and the terms of the given list
        // correspondingly such that all terms with indices in an entry of the term
        // partition only use variables of the corresponding part of the variable
        // partition. If the terms cannot perfectly be split, the indices of term
        // that cannot be distributed to the partition are stored in the list of
        // remaining term indices.
        List<HashSet<int>> Partition(List<HashSet<int>> v, List<int> l1, List<int> l2, List<int> l3, List<int> lrem)
        {
            var partitionV = new List<HashSet<int>>();
            var partitionT = new List<HashSet<int>>();
            var remV = new HashSet<int>();

            foreach (var i in lrem)
                remV.AddRange(v[i]);

            var l23 = l2.Concat(l3).ToList();
            foreach (var i in l23)
            {
                // The variable set has a nonempty intersection with the variables
                // we cannot split, so merge them.
                if (v[i].Intersect(remV).Any())
                {
                    remV.AddRange(v[i]);
                    lrem.Add(i);
                    continue;
                }

                // Now check whether the term matches any partition's part, if existent.
                if (TryFindMatchingPartition(i, v[i], partitionV, partitionT))
                    continue;

                // If the term does not match any, check whether it violates any.
                // If so, reject it.
                var (intersections, valid) = DetermineIntersections(v[i], partitionV);

                // Create the new part.
                if (intersections.Count == 0)
                {
                    partitionV.Add(v[i]);
                    partitionT.Add(new() { i });
                }

                // We can merge the variable set into an existing one.
                else if (intersections.Count == 1)
                {
                    partitionV[intersections[0]].AddRange(v[i]);
                    partitionT[intersections[0]].Add(i);
                }

                // We have a conflict.
                else
                {
                    remV.AddRange(v[i]);
                    lrem.Add(i);

                    foreach (var j in intersections.Reverse<int>())
                    {
                        remV.AddRange(partitionV[j]);
                        lrem.AddRange(partitionT[j]);

                        partitionV.RemoveAt(j);
                        partitionT.RemoveAt(j);
                    }
                }
            }

            // Now check for each term with 1 variable whether it matches any
            // partitions' part, if existent. Note that it cannot violate any.
            bool done = false;
            foreach (var i in l1)
            {
                var _var = v[i].First();
                v[i].Remove(_var);

                if (remV.Contains(_var))
                {
                    lrem.Add(i);
                    continue;
                }

                done = false;

                foreach (var j in RangeUtil.Get(partitionV.Count))
                {
                    var part = partitionV[j];

                    // The variable is included in the part.
                    if (part.Contains(_var))
                    {
                        partitionT[j].Add(i);
                        done = true;
                        break;
                    }
                }

                if (!done)
                {
                    partitionV.Add(new() { _var });
                    partitionT.Add(new() { i });
                }
            }


            return partitionT;
        }

        bool TryFindMatchingPartition(int i, HashSet<int> variables, List<HashSet<int>> partitionV, List<HashSet<int>> partitionT)
        {
            Debug.Assert(partitionV.Count == partitionT.Count);

            foreach (var j in RangeUtil.Get(partitionV.Count))
            {
                // The variable set matches the part.
                var diff = variables.Except(partitionV[j]);
                if (diff.Count() == 0)
                {
                    partitionT[j].Add(i);
                    return true;
                }
            }

            return false;
        }

        // Returns all indices of entries in the given partition having a nonempty
        // intersection with the given set of variables. Additionally returns False
        // iff there is at least one intersection with more than 3 variables.
        private (List<int>, bool) DetermineIntersections(HashSet<int> variables, List<HashSet<int>> partitionV)
        {
            var intersections = new List<int>();
            bool valid = true;

            foreach (var j in RangeUtil.Get(partitionV.Count))
            {
                var part = partitionV[j];

                // The variable set has an empty intersection with the part.
                if (variables.Intersect(part).Count() == 0)
                    continue;

                // The variable set has a nonempty intersection with the part,
                // but does not match it. Check whether we can merge it into the
                // part. If not, reject it.
                intersections.Add(j);

                if (valid && (intersections.Count > 0 || variables.Union(part).Count() > 3))
                    valid = false;
            }

            return (intersections, valid);
        }

        // Simplify the sum of terms in the given list for each given partition and
        // compose the results.
        AstIdx SimplifyPartsAndCompose(List<AstIdx> l, List<HashSet<int>> partition, int constIdx, HashSet<int> lrem)
        {
            // Simplify the partition's parts separately and compose the results.
            AstIdx? simpl = null;
            foreach (var part in partition)
            {
                var e = ComposeTerms(l, part);

                // Run the simplification procedure on the ast.
                var s = Run(width, ctx, e, true);

                // Append the constant if existent and check whether the result has the same number of terms.
                // If so, use that instead and eliminate the constant.
                if (constIdx != -1)
                {
                    Debug.Assert(constIdx > -1);
                    var constNode = l[constIdx];
                    e = ctx.Add(e, constNode);

                    // Run the simplification procedure on the newly created AST.
                    var s2 = Run(width, ctx, e, true);

                    if (CountTerms(s) == CountTerms(s2))
                    {
                        s = s2;
                        constIdx = -1;
                    }
                }

                // If the part is a constant zero, skip it.
                Debug.Assert(s != null);
                if (ctx.GetOpcode(s) == AstOp.Constant && ctx.GetConstantValue(s) == 0)
                    continue;

                if (simpl == null)
                    simpl = s;
                else
                    simpl = ctx.Add(simpl.Value, s);
            }

            // If there are no remaining terms but the constant, add the constant.
            if (lrem.Count == 0)
            {
                if (constIdx != -1)
                {
                    Debug.Assert(constIdx > -1);
                    var constNode = l[constIdx];
                    if (simpl == null)
                        simpl = constNode;
                    else
                        simpl = ctx.Add(simpl.Value, constNode);
                }

                return simpl == null ? ctx.Constant(0, width) : simpl.Value;
            }

            // Now consider the terms which did not fit into the partition, if existent.
            var remainingTerms = ComposeTerms(l, lrem);

            // Append the constant if existent and not used yet.
            if (constIdx != -1)
            {
                // Debug.Assert(constIdx > 0);
                var constNode = l[constIdx];
                remainingTerms = ctx.Add(constNode, remainingTerms);
            }

            // Run the simplifier on the remaining terms.
            remainingTerms = Run(width, ctx, remainingTerms, alreadySplit: true);

            if (simpl == null)
                simpl = remainingTerms;
            else
                simpl = ctx.Add(simpl.Value, remainingTerms);

            return simpl.Value;
        }

        // Returns a sum of the given list's entries with indices contained in the given list.
        AstIdx ComposeTerms(List<AstIdx> l, HashSet<int> indices)
        {
            AstIdx? e = null;
            foreach (var i in indices)
            {
                var term = l[i];
                if (e == null)
                    e = term;
                else
                    e = ctx.Add(e.Value, term);
            }

            return e.Value;
        }

        private void TryRefine()
        {
            Debug.Assert(lincombTerms != null);

            // Rebuild the result vector since it has been modified during simplification.
            // Note that this is performed by the parent.
            //resultVector = BuildResultVector(ctx, ast, moduloMask);

            // The number of terms in the linear combination of conjunctions only has one term.
            if (CheckTermCount(1))
                return;

            // Build a set of unique result vector values.
            var resultSet = resultVector.ToHashSet();
            var l = resultVector.Length;
            Debug.Assert(l > 0);

            // We apply a set of heuristics to try and find a solution that is simpler than
            // a linear combination of conjunctions. We perform several attempts, numbered according to
            // the paper.

            // (1-3) Try to find a single term that fits.
            TryRefineSingleTerm(resultSet);

            // We cannot simplify the expression better.
            if (CheckTermCount(2))
                return;

            // (4-8) Try to find a sum of two terms that fits.
            TryRefineTwoTerms(resultSet);

            // We cannot simplify the expression better.
            if (CheckTermCount(3))
                return;

            // (9) Try to reduce the number of unique values by expressing one as a
            // combination of the others.
            var constant = ReduceByConstant();
            var constNode = ctx.Constant(constant, width);
            var uniqueValues = resultVector.Where(x => x != 0).ToHashSet().ToList();
            TryEliminateUniqueValue(uniqueValues, constNode);

            var c = uniqueValues.Count + (constant == 0 ? 0 : 1);
            if (CheckTermCount(c))
                return;

            // (10) Find expressions corresponding to the unique values.
            var simpler = ExpressionForEachUniqueValue(uniqueValues.ToHashSet());
            simpler = AddConstant(simpler, constNode);
            CheckSolutionComplexity(simpler, c);
            //Debugger.Break();
        }

        private void TryRefineSingleTerm(HashSet<ApInt> resultSet)
        {
            var l = resultSet.Count;
            Debug.Assert(l > 1);

            // We cannot come down to a single expression in this case.
            if (l > 2)
                return;

            // NOTE: The case (1) that we only have one unique value has already been
            // handled in simplify_one_value().

            // (2) If only one nonzero value occurs and the result for all variables being zero is zero,
            // we can find a single expression.
            if (resultVector[0] == 0)
            {
                var e = ExpressionForEachUniqueValue(resultSet);
                CheckSolutionComplexity(e, 1);
            }

            // (3) Check whether we can find one single negated term.
            TryFindNegatedSingleExpression(resultSet);
        }

        // For the given set of results of the input expression for combinations of
        // truth values, try to find a single negated expression representing the
        // result vector.
        private void TryFindNegatedSingleExpression(HashSet<ApInt> resultSet)
        {
            // We can only find a negated expression if we have 2 distinct values.
            Debug.Assert(resultSet.Count == 2);

            var s = resultSet.ToArray();
            var a = s[0];
            var b = s[1];

            // Exit early if we don't have two terms where one is equivalent to (2 * other).
            var aDouble = IsDoubleModulo(a, b);
            var bDouble = IsDoubleModulo(b, a);
            if (!aDouble && !bDouble)
                return;

            // Make sure that b is double a
            if (aDouble)
            {
                (a, b) = (b, a);
            }

            if (resultVector[0] == b)
                return;

            // Get a negated representation of the boolean truth table.
            //var t = resultVector.Select(x => x == b ? 1 : 0).ToList();
            var t = new TruthTable(variables.Count);
            for (int i = 0; i < resultVector.Length; i++)
            {
                if (resultVector[i] == b)
                    t.SetBit(i, true);
            }

            var e = BooleanMinimizer.GetBitwise(ctx, variables, t, negate: true);

            e = Term(e, NegateCoefficient(a));

            CheckSolutionComplexity(e, 1);
        }

        private ApInt NegateCoefficient(ApInt coeff)
        {
            // Note that the mask & maxValue * a should be equivalent to taking -a under the modular field.
            return moduloMask & ApInt.MaxValue * coeff;
        }

        void TryRefineTwoTerms(HashSet<ApInt> resultSet)
        {
            if (resultVector[0] == 0)
                TryRefineTwoTermsFirstZero(resultSet);
            else
                TryRefineTwoTermsFirstNonZero(resultSet);
        }

        private void TryRefineTwoTermsFirstZero(HashSet<ApInt> resultSet)
        {
            Debug.Assert(resultVector[0] == 0);
            var l = resultSet.Count;

            // In this case 1==2 we know that the constant is nonzero since we would have
            // run into the case (2) otherwise.
            // TODO: We can still try to find a solution with 2 terms if we already have one with one term and then compare complexities.


            if (l == 3)
            {
                // (4) We can reduce the expression to two terms.
                FindTwoExpressionsByTwoValues();
            }

            else if (l == 4)
            {
                // (5) We can still come down to 2 expressions if we can express one
                // value as a sum of the others.
                var uniqueValues = resultVector.Where(x => x != 0).ToHashSet().ToList();
                TryEliminateUniqueValue(uniqueValues);
            }
        }

        // For the stored list of results of the input expression for combinations
        // of truth values, try to find two unnegated expressions representing the
        // result vector.
        private void FindTwoExpressionsByTwoValues()
        {
            // This step is disabled due to high performance overhead.
            return;

            Debug.Assert(resultVector[0] == 0);
            var resultSet = resultVector.ToHashSet();
            Debug.Assert(resultSet.Count == 3);

            // Remove the zero entry.
            resultSet.Remove(0);
            Debug.Assert(resultSet.Count == 2);

            var a = resultSet.First();
            resultSet.Remove(a);
            var b = resultSet.First();
            resultSet.Remove(b);

            // We have three possible solutions. Return the solution with the lowest complexity.
            DetermineCombOfTwo(a, b);
            DetermineCombOfTwo(moduloMask & a - b, b);
            DetermineCombOfTwo(a, moduloMask & b - a);
        }

        private void DetermineCombOfTwo(ApInt coeff1, ApInt coeff2, ApInt[] vec = null, bool secNegated = false)
        {
            //throw new InvalidOperationException($"Should be disabled");

            var d = GetDecisionVector(coeff1, coeff2, vec);
            var cases = new Stack<List<List<Decision>>>();
            cases.Push(d);
            while (cases.Count > 0)
            {
                // Perform splitting if necessary.
                var c = cases.Pop();
                if (MustSplit(c))
                {
                    var split = Split(c);
                    foreach (var s in split)
                        cases.Push(s);
                    continue;
                }

                DetermineCombOfTwoForCase(coeff1, coeff2, c, secNegated);
            }
        }

        public enum Decision
        {
            None = 0,
            First = 1,
            Second = 2,
            Both = 3,
        }

        private List<List<Decision>> GetDecisionVector(ApInt coeff1, ApInt coeff2, ApInt[] vec)
        {
            if (vec == null)
                vec = resultVector;

            var d = new List<List<Decision>>();
            foreach (var r in vec)
            {
                var e = new List<Decision>();
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
                    e.Add(Decision.None);
                if (b)
                    e.Add(Decision.Both);
                if (f)
                    e.Add(Decision.First);
                if (s)
                    e.Add(Decision.Second);

                Debug.Assert(e.Count > 0);
                d.Add(e);
            }

            return d;
        }

        private bool MustSplit(List<List<Decision>> d)
        {
            foreach (var e in d)
            {
                Debug.Assert(e.Count > 0);
                if (e.Count > 1)
                    return true;
            }

            return false;
        }

        private List<List<List<Decision>>> Split(List<List<Decision>> d)
        {
            var sec = new List<List<Decision>>();
            bool split = false;

            foreach (var e in d)
            {
                Debug.Assert(e.Count > 0);
                // Splitting has already happened.
                if (split)
                {
                    sec.Add(e.ToList());
                    continue;
                }

                // Split at this entry.
                if (e.Count > 1)
                {
                    split = true;
                    var popped = e[e.Count - 1];
                    e.RemoveAt(e.Count - 1);

                    sec.Add(new() { popped });
                    continue;
                }

                sec.Add(e.ToList());
            }

            Debug.Assert(split);
            return new List<List<List<Decision>>>() { d, sec };
        }

        private void DetermineCombOfTwoForCase(ApInt coeff1, ApInt coeff2, List<List<Decision>> _case, bool secNegated)
        {
            // Flatten the list structure. 
            List<Decision> cases = _case.Select(x => x.Single()).ToList();

            // Compute a boolean function for the first term.
            //var l = cases.Select(x => x == Decision.First || x == Decision.Both ? 1 : 0).ToList();
            var l = new TruthTable(variables.Count);
            for(int i = 0; i < cases.Count; i++)
            {
                if (cases[i] == Decision.First || cases[i] == Decision.Both)
                    l.SetBit(i, true);
            }

            var first = BooleanMinimizer.GetBitwise(ctx, variables, l);
            l.Clear();
            // l = cases.Select(x => x == Decision.Second || x == Decision.Both ? 1 : 0).ToList();
            for (int i = 0; i < cases.Count; i++)
            {
                if (cases[i] == Decision.Second || cases[i] == Decision.Both)
                    l.SetBit(i, true);
            }
            // Compute a boolean function for the second term.
            var second = BooleanMinimizer.GetBitwise(ctx, variables, l, secNegated);

            // Compose the terms together, optionally negating the second coefficient if requested.
            var secondCoeff = secNegated ? NegateCoefficient(coeff2) : coeff2;
            var e = Compose(new() { first, second }, new() { coeff1, secondCoeff });

            CheckSolutionComplexity(e, 2);
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

        private void TryRefineTwoTermsFirstNonZero(HashSet<ApInt> resultSet)
        {
            Debug.Assert(resultVector[0] != 0);
            var l = resultSet.Count;

            // Clone the result vec since we mutate it.
            var resultVec = resultVector.ToArray();

            if (l == 2)
            {
                // (6) In this case we know that the constant is nonzero since we 
                // would have run into the case (2) otherwise.
                var constant = ReduceByConstant();
                var e = ExpressionForEachUniqueValue(resultVector.ToHashSet());
                //Console.WriteLine(ctx.GetAstString(e));
                e = AddConstant(e, ctx.Constant(constant, width));
                CheckSolutionComplexity(e, 2);

                // Restore the result vector since it has been modified above.
                // TODO: Since we only subtracted a single coefficient, we can shave off
                // via adding the constant back to all of the entries instead of cloning.
                resultVector = resultVec;
            }

            if (l <= 4)
            {
                // (7) Try to express the expression as a linear combination of a 
                // negated and an unnegated bitwise expression.
                TryFindNegatedAndUnnegatedExpression();

                // (8) Try to express the expression as the linear combination of two negated
                // bitwise expressions.
                TryFindTwoNegatedExpressions();
            }
        }

        // For the stored list of results of the input expression for combinations
        // of truth values, try to find a negated and an unnegated expression
        // representing the result vector.
        void TryFindNegatedAndUnnegatedExpression()
        {
            return;

            // TODO: We can still try to find a solution with 2 terms if we already
            // have one with one terms, and then compare complexities.
            if (!HasOnlyThreeOrFourEntries(resultVector))
                return;

            var negCoeff = resultVector[0];
            Debug.Assert(negCoeff != 0);
            var vec = resultVector.Select(x => x - negCoeff & moduloMask).ToArray();
            Debug.Assert(vec[0] == 0);

            var uniqueValues = vec.ToHashSet().Where(x => x != 0 && x != negCoeff).ToList();
            Debug.Assert(uniqueValues.Count >= 1);

            // Not possible to find a combination if we still have more than two
            // unique values.
            if (uniqueValues.Count > 2)
                return;

            if (uniqueValues.Count == 2)
            {
                var a = uniqueValues[0];
                var b = uniqueValues[1];

                // Try to express one of these values as the sum of the negated bitwise
                // expression's coefficient and the other value.
                if ((b - a - negCoeff & moduloMask) != 0)
                {
                    (a, b) = (b, a);
                    if ((b - a - negCoeff & moduloMask) != 0)
                        return;
                }

                var unnegCoeff = a;
                DetermineCombOfTwo(unnegCoeff, negCoeff, vec, true);
                return;
            }

            var _a = uniqueValues[0];
            // If we have just one unique value(a) left, we have on degree of freedom
            // to choose the unnegated bitwise expression's coefficient:
            // It can be either be 'a' or 'a' reduced by the negated expression's coefficient.
            DetermineCombOfTwo(_a, negCoeff, vec, true);
            DetermineCombOfTwo(_a - negCoeff & moduloMask, negCoeff, vec, true);
        }

        private void TryFindTwoNegatedExpressions()
        {
            return;

            if (!HasOnlyThreeOrFourEntries(resultVector))
                return;

            var coeffSum = resultVector[0];
            Debug.Assert(coeffSum != 0);

            var vec = resultVector.Select(x => x - coeffSum & moduloMask).ToList();
            Debug.Assert(vec[0] == 0);

            var uniqueValues = vec.ToHashSet().Where(x => x != 0 && x != coeffSum).ToList();
            Debug.Assert(uniqueValues.Count >= 1);

            // Not possible to find a combination if we still have more than two
            // unique values.
            if (uniqueValues.Count > 2)
                return;

            // This case has already been handled in
            // try_find_negated_and_unnegated_expression().
            // TODO: Handle here too and compare complexity?
            if (uniqueValues.Count == 1)
                return;

            var a = uniqueValues[0];
            var b = uniqueValues[1];

            // Try to express one of these values as the difference of coeffSum and
            // the other value.
            if ((b + a - coeffSum & moduloMask) != 0)
                return;

            var coeff1 = a;
            //var l = vec.Select(x => x == coeff1 || x == coeffSum ? 1 : 0).ToList();
            var l = new TruthTable(variables.Count);
            for(int i = 0; i < vec.Count; i++)
            {
                if (vec[i] == coeff1 || vec[i] == coeffSum)
                    l.SetBit(i, true);
            }

            var bitwise1 = BooleanMinimizer.GetBitwise(ctx, variables, l, negate: true);

            var coeff2 = b;
            vec = RangeUtil.Get(vec.Count).Select(x => moduloMask & vec[x] - coeff1 * (ApInt)(l.GetBit(x) ? 1 : 0)).ToList();
            // l = vec.Select(x => x == coeff2 ? 1 : 0).ToList();
            l.Clear();
            for(int i = 0; i < vec.Count; i++)
            {
                if (vec[i] == coeff2)
                    l.SetBit(i, true);
            }
            var bitwise2 = BooleanMinimizer.GetBitwise(ctx, variables, l, negate: true);

            var e = Compose(new() { bitwise1, bitwise2 }, new() { NegateCoefficient(coeff1), NegateCoefficient(coeff2) });
            CheckSolutionComplexity(e, 2);
        }

        private static bool HasOnlyThreeOrFourEntries(ApInt[] resultVector)
        {
            // TODO: We can still try to find a solution with 2 terms if we already
            // have one with one terms, and then compare complexities.
            var uv = resultVector.ToHashSet();
            if (uv.Count != 3 && uv.Count != 4)
                return false;

            return true;
        }

        // Returns true iff a is double b in the modular field
        private bool IsSumModulo(ApInt s1, ApInt s2, ApInt a)
        {
            return (moduloMask & s1 + s2) == a;
        }

        // Returns true iff a is double b in the modular field
        private bool IsDoubleModulo(ApInt a, ApInt b)
        {
            var mul = moduloMask & 2 * b;
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

        private void TryEliminateUniqueValue(List<ApInt> uniqueValues, AstIdx? constant = null)
        {
            // Would be possible also for higher l, implementation is generic.
            var l = uniqueValues.Count;
            if (l > 4)
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

                        // Skip if these terms do not sum up to each other.
                        bool isSum = IsSumModulo(uniqueValues[i], uniqueValues[j], uniqueValues[k]);
                        if (!isSum)
                            continue;

                        // We have a match.
                        AstIdx? simpler = null;
                        foreach (var i1 in new int[] { i, j })
                        {
                            var term = TermRefinement(uniqueValues[i1], uniqueValues[k]);
                            if (simpler == null)
                                simpler = term;
                            else
                                simpler = ctx.Add(simpler.Value, term);
                        }

                        if (l > 3)
                        {
                            var resultSet = uniqueValues.ToHashSet();
                            resultSet.Remove(uniqueValues[i]);
                            resultSet.Remove(uniqueValues[j]);
                            resultSet.Remove(uniqueValues[k]);

                            while (resultSet.Count > 0)
                            {
                                var r1 = resultSet.First();
                                resultSet.Remove(r1);

                                var term = TermRefinement(r1);
                                if (simpler == null)
                                    simpler = term;
                                else
                                    simpler = ctx.Add(simpler.Value, term);
                            }
                        }

                        CheckSolutionComplexity(simpler.Value, l - 1, constant);
                    }
                }
            }

            if (l < 4)
                return;

            // Compute the sum of all unique entries.
            ApInt sum = 0;
            foreach (var entry in uniqueValues)
                sum += entry;
            sum &= moduloMask;

            // Finally, if we have more than 3 values, try to express one of them as
            // a sum of all others.
            foreach (var i in RangeUtil.Get(l))
            {
                // Skip if this entry cannot be expressed as the sum of all others.
                bool isSum = 2 * uniqueValues[i] == sum;
                if (!isSum)
                    continue;

                AstIdx? simpler = null;
                foreach (var j in RangeUtil.Get(l))
                {
                    if (i == j)
                        continue;

                    var term = TermRefinement(uniqueValues[j], uniqueValues[i]);
                    if (simpler == null)
                        simpler = term;
                    else
                        simpler = ctx.Add(simpler.Value, term);
                }

                CheckSolutionComplexity(simpler.Value, l - 1, constant);
            }
        }

        private ApInt ReduceByConstant()
        {
            var constant = resultVector[0];
            if (constant == 0)
                return constant;

            foreach (var i in RangeUtil.Get(resultVector.Length))
            {
                resultVector[i] -= constant;
                resultVector[i] = moduloMask & resultVector[i];
            }

            return constant;
        }

        private bool CheckTermCount(int value)
        {
            /*
            if (lincombTerms.GetValueOrDefault() <= value)
                return false;
            if (metric != Metric.Terms)
                return false;

            var currTermCount = GetTermCountOfCurrentSolution();
            return currTermCount <= value;
            */

            return false;
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

        private AstIdx AddConstant(AstIdx expr, AstIdx constant)
        {
            var constValue = ctx.GetConstantValue(constant);
            if (constValue == 0)
                return expr;

            return ctx.Add(constant, expr);
        }
    }
}
