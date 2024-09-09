using Iced.Intel;
using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Pipeline.Intermediate;
using Mba.Simplifier.Polynomial;
using Mba.Utility;
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Linq;
using System.Reflection.Metadata.Ecma335;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.Pipeline
{
    public class GeneralSimplifier
    {
        private readonly AstCtx ctx;

        // For any given node, we store the best possible ISLE result.
        private readonly Dictionary<uint, uint> isleCache = new();

        // For any given node, we store the optimal representation yielded by SiMBA.
        private readonly Dictionary<uint, uint> simbaCache = new();

        public static AstIdx Simplify(AstCtx ctx, AstIdx id) => new GeneralSimplifier(ctx).SimplifyGeneral(id);

        public GeneralSimplifier(AstCtx ctx)
        {
            this.ctx = ctx;
        }

        public AstIdx SimplifyGeneral(AstIdx id, bool useIsle = true)
        {
            // Simplify the AST via efficient, recursive term rewriting(ISLE).
            if (useIsle)
                id = SimplifyViaTermRewriting(id);

            // Simplify via recursive SiMBA.
            id = SimplifyViaRecursiveSiMBA(id);
            return id;
        }

        // Simplify the AST via efficient, recursive term rewriting(ISLE).
        private AstIdx SimplifyViaTermRewriting(AstIdx id)
        {
            if (isleCache.TryGetValue(id, out var existingIdx))
                return existingIdx;
            var initialId = id;

            // Repeatedly apply recursive term rewriting, until a fixed point is reached.
            uint? oldIdx = null;
            while (oldIdx != id)
            {
                oldIdx = id;
                id = ctx.RecursiveSimplify(id);
            }

            // TODO: Add to isle cache
            bool cacheIsle = true;
            if (cacheIsle)
            {
                isleCache.TryAdd(initialId, id);
                isleCache.TryAdd(id, id);
            }
            return id;
        }

        // Simplify the AST via recursive SiMBA application.
        private AstIdx SimplifyViaRecursiveSiMBA(AstIdx id, bool polySimplify = true)
        {
            if (simbaCache.TryGetValue(id, out var existing))
                return existing;
            // TODO: We should probably apply ISLE before attempting any other steps.

            // For linear and semi-linear MBAs, we can skip the substitution / polynomial simplification steps.
            var linClass = ctx.GetClass(id);
            if (ctx.IsConstant(id))
                return id;

            if(linClass != AstClassification.Nonlinear)
            {
                // Bail out if there are too many variables.
                var vars = ctx.CollectVariables(id);
                if(vars.Count > 11 || vars.Count == 0)
                {
                    var simplified = SimplifyViaTermRewriting(id);
                    simbaCache.Add(id, simplified);
                    return simplified;
                }

                var linSimplified = LinearSimplifier.Run(ctx.GetWidth(id), ctx, id, false, linClass == AstClassification.SemiLinear || linClass == AstClassification.BitwiseWithConstants, false, vars);
                linSimplified = SimplifyViaTermRewriting(linSimplified);
                simbaCache.TryAdd(id, linSimplified);
                simbaCache.TryAdd(linSimplified, linSimplified);
                return linSimplified;
            }


            // Apply substitution.
            var substMapping = new Dictionary<AstIdx, AstIdx>();
            bool isSemiLinear = false;
            var withSubstitutions = GetAstWithSubstitutions(id, substMapping, ref isSemiLinear);

            // If there are multiple substitutions, try to minimize the number of substitutions.
            if (substMapping.Count > 1)
                withSubstitutions = TryUnmergeLinCombs(withSubstitutions, substMapping);

            // If polynomial parts are present, try to simplify them.
            var inverseMapping = substMapping.ToDictionary(x => x.Value, x => x.Key);
            AstIdx? reducedPoly = null;
            if (polySimplify && ctx.GetHasPoly(id))
            {
                // Try to reduce the polynomial parts using "pure" polynomial reduction algorithms.
                reducedPoly = ReducePolynomials(GetRootTerms(ctx, withSubstitutions), substMapping, inverseMapping);

                // If we succeeded, reset the state.
                if(reducedPoly != null)
                {
                    // Back substitute the original substitutions.
                    reducedPoly = ApplyBackSubstitution(ctx, reducedPoly.Value, inverseMapping);

                    // Reset internal state.
                    substMapping.Clear();
                    isSemiLinear = false;
                    withSubstitutions = GetAstWithSubstitutions(reducedPoly.Value, substMapping, ref isSemiLinear);
                    inverseMapping = substMapping.ToDictionary(x => x.Value, x => x.Key);
                }
            }

            // If there are any substitutions, we want to try simplifying the polynomial parts.
            var variables = ctx.CollectVariables(withSubstitutions);
            if (polySimplify && substMapping.Count > 0 && ctx.GetHasPoly(id))
            {
                var maybeSimplified = TrySimplifyMixedPolynomialParts(withSubstitutions, substMapping, inverseMapping, variables);
                if (maybeSimplified != null && maybeSimplified.Value != id)
                {
                    // Reset internal state.
                    substMapping.Clear();
                    isSemiLinear = false;
                    withSubstitutions = GetAstWithSubstitutions(maybeSimplified.Value, substMapping, ref isSemiLinear);
                    inverseMapping = substMapping.ToDictionary(x => x.Value, x => x.Key);
                    variables = ctx.CollectVariables(withSubstitutions);
                }
            }

            // If there are still more too many variables remaining, bail out.
            if (variables.Count > 11)
            {
                var simplified = SimplifyViaTermRewriting(id);
                simbaCache.Add(id, simplified);
                return simplified;
            }

            // Simplify the resulting expression via term rewriting.
            // TODO: If there are too many variables(more than 5), we should partition wrt variable count and simplify each partition.
            withSubstitutions = SimplifyViaTermRewriting(withSubstitutions);

            var result = withSubstitutions;
            if (!ctx.IsConstant(withSubstitutions))
                result = LinearSimplifier.Run(ctx.GetWidth(withSubstitutions), ctx, withSubstitutions, false, isSemiLinear, false, variables);
            var backSub = ApplyBackSubstitution(ctx, result, inverseMapping);

            // Apply constant folding / term rewriting.
            var propagated = SimplifyViaTermRewriting(backSub);

            // Cache the result.
            simbaCache.TryAdd(id, propagated);

            // After applying SiMBA, check if the number of variables has decreased.
            // If it has, we want to run SiMBA again. 
            // TODO: 
            //  - (1) Implement better heuristic for when to re-run SiMBA
            //  - (2) Stop duplicating work. We are are collecting variables / applying substitution, then throwing that info away.
            bool isSl = false;
            var newSubstMapping = new Dictionary<AstIdx, AstIdx>();
            var newWithSubst = GetAstWithSubstitutions(propagated, newSubstMapping, ref isSemiLinear, false);
            var newVars = ctx.CollectVariables(newWithSubst);
            if (newVars.Count < variables.Count)
            {
                propagated = SimplifyViaRecursiveSiMBA(propagated, true);
            }

            simbaCache.TryAdd(propagated, propagated);

            return propagated;
        }

        private AstIdx GetAstWithSubstitutions(AstIdx id, Dictionary<AstIdx, AstIdx> substitutionMapping, ref bool isSemiLinear, bool inBitwise = false)
        {
            var op0 = (bool inBitwise, ref bool isSemiLinear) => GetAstWithSubstitutions(ctx.GetOp0(id), substitutionMapping, ref isSemiLinear, inBitwise);
            var op1 = (bool inBitwise, ref bool isSemiLinear) => GetAstWithSubstitutions(ctx.GetOp1(id), substitutionMapping, ref isSemiLinear, inBitwise);

        start:
            var opcode = ctx.GetOpcode(id);
            switch (opcode)
            {
                case AstOp.Add:
                case AstOp.Mul:
                    // If we encounter an arithmetic subtree inside of a bitwise operator, it is not linear.
                    // In this case we try to recursively simplify the subtree and check if it was made linear.
                    if (inBitwise)
                    {
                        var simplified = SimplifyViaRecursiveSiMBA(id);
                        if (simplified != id)
                        {
                            id = simplified;
                            goto start;
                        }
                    }

                    // If the above check still yielded something that is not linear, we apply substitution.
                    if (inBitwise)
                    {
                        return GetSubstitution(id, substitutionMapping);
                    }

                    // Otherwise we can carry on and fetch the children.
                    // In the case of multiplication, if the first operand is not a constant,
                    // we want to check if applying recursive SiMBA would yield another constant.
                    var v0 = ctx.GetOp0(id);
                    var v1 = ctx.GetOp1(id);

                    // If the first operand is not a constant, then we want to recursively simplify both children and
                    // check if it yields a constant.
                    if (opcode == AstOp.Mul && ctx.GetOpcode(v0) != AstOp.Constant)
                    {
                        v0 = SimplifyViaRecursiveSiMBA(v0);
                        v1 = SimplifyViaRecursiveSiMBA(v1);

                        if (ctx.GetOpcode(v1) == AstOp.Constant)
                            (v0, v1) = (v1, v0);
                    }

                    // If both children are still not constant after applying recursive simplification,
                    // then we need to perform substitution.
                    if (opcode == AstOp.Mul && ctx.GetOpcode(v0) != AstOp.Constant)
                    {
                        var mul = ctx.Mul(v0, v1);
                        return GetSubstitution(mul, substitutionMapping);
                    }

                    // Otherwise we have a multiplication where one term is a constant(linear).
                    if (opcode == AstOp.Mul)
                    {
                        var constTerm = v0;

                        // In the case of coeff*(x+y), where coeff is a constant, we want to distribute it, yielding coeff*x + coeff*y.
                        if (ctx.GetOpcode(v1) == AstOp.Add)
                        {
                            var left = ctx.Mul(constTerm, ctx.GetOp0(v1));
                            left = ctx.SingleSimplify(left);

                            var right = ctx.Mul(constTerm, ctx.GetOp1(v1));
                            right = ctx.SingleSimplify(right);
                            var sum = ctx.Add(left, right);

                            var oldSum = sum;
                            var newSum = ctx.SingleSimplify(sum);
                            sum = newSum;
                            // In this case, we apply constant folding(but we do not search recursively).

                            return GetAstWithSubstitutions(sum, substitutionMapping, ref isSemiLinear, inBitwise);
                        }

                        else
                        {
                            return ctx.Mul(constTerm, GetAstWithSubstitutions(v1, substitutionMapping, ref isSemiLinear, inBitwise));
                        }
                    }

                    else
                    {
                        return ctx.Add(op0(inBitwise, ref isSemiLinear), op1(inBitwise, ref isSemiLinear));
                    }
                case AstOp.Pow:
                    var basis = SimplifyViaRecursiveSiMBA(ctx.GetOp0(id));
                    var degree = SimplifyViaRecursiveSiMBA(ctx.GetOp1(id));
                    if (ctx.IsConstant(basis))
                        throw new InvalidOperationException($"TODO: Handle base folding to constant");
                    
                    var pow = ctx.Pow(basis, degree);
                    return GetSubstitution(pow, substitutionMapping);

                    // We need to check if one of the terms folds to a constant like we do in the multiplication case.
                    throw new InvalidOperationException("TODO");

                case AstOp.And:
                case AstOp.Or:
                case AstOp.Xor:
                    if (opcode == AstOp.And)
                        return ctx.And(op0(true, ref isSemiLinear), op1(true, ref isSemiLinear));
                    if (opcode == AstOp.Or)
                        return ctx.Or(op0(true, ref isSemiLinear), op1(true, ref isSemiLinear));
                    if (opcode == AstOp.Xor)
                        return ctx.Xor(op0(true, ref isSemiLinear), op1(true, ref isSemiLinear));
                    throw new InvalidOperationException("Unrecognized opcode!");
                case AstOp.Neg:
                    if (inBitwise)
                    {
                        // If we encounter a negation inside of a bitwise operator, try to simplify the subtree.
                        var simplified = SimplifyViaRecursiveSiMBA(id);
                        if (simplified != id)
                        {
                            id = simplified;
                            goto start;
                        }

                        // Otherwise we have a negation that cannot be distributed, so we leave it as is.
                        return ctx.Neg(op0(inBitwise, ref isSemiLinear));
                    }

                    else
                    {
                        // Since negation can be either arithmetic or bitwise, we forward the inBitwise argument.
                        return ctx.Neg(op0(inBitwise, ref isSemiLinear));
                    }


                case AstOp.Constant:
                    // If a bitwise constant is present, we want to mark it as semi-linear
                    if (inBitwise)
                        isSemiLinear = true;

                    return id;
                case AstOp.Symbol:
                    return id;
                default:
                    throw new InvalidOperationException($"Unrecognized opcode: {opcode}!");
            }
        }

        public record PolynomialParts(uint width, ulong coeffSum, Dictionary<AstIdx, ulong> ConstantPowers, List<AstIdx> Others);

        public AstIdx GetAstForPolynomialParts(PolynomialParts parts)
        {
            var width = parts.width;
            var coeffSum = parts.coeffSum;
            var constantPowers = parts.ConstantPowers;
            var others = parts.Others;

            List<AstIdx> factors = new();
            var pows = constantPowers.ToList();
            pows.Sort((x, y) => { return VarsFirst(ctx, x.Key, y.Key); });
            factors.Add(ctx.Constant(coeffSum, width));
            factors.AddRange(pows.Select(x => x.Value == 1 ? x.Key : ctx.Pow(x.Key, ctx.Constant(x.Value, width))));
            factors.AddRange(others);

            var result = ctx.Mul(factors);
            return result;
        }

        // Decompose a monomial into structured factors(coefficient, nodes raised to constant powers, then miscellaneous nodes).
        public static PolynomialParts GetPolynomialParts(AstCtx ctx, AstIdx id)
        {
            // Skip if this is not a multiplication.
            var opcode = ctx.GetOpcode(id);

            var roots = GetRootMultiplications(ctx,id);
            ulong coeffSum = 0;
            Dictionary<AstIdx, ulong> constantPowers = new();
            List<AstIdx> others = new();

            foreach(var root in roots)
            {
                var code = ctx.GetOpcode(root);
                if (code == AstOp.Constant)
                {
                    coeffSum += ctx.GetConstantValue(root);
                }
                else if (code == AstOp.Symbol)
                {
                    constantPowers.TryAdd(root, 0);
                    constantPowers[root]++;
                }
                else if(code == AstOp.Pow)
                {
                    // If we have a power by a nonconstant, we can't really do much here.
                    var degree = ctx.GetOp1(root);
                    var constPower = ctx.TryGetConstantValue(degree);
                    if(constPower == null)
                    {
                        others.Add(root);
                        continue;
                    }

                    // Otherwise we can combine terms.
                    var basis = ctx.GetOp0(root);
                    constantPowers.TryAdd(basis, 0);
                    constantPowers[basis] += constPower.Value;
                }

                // In the case of e.g. (x+y) being a root, we can still collect the constant powers(the number of times x+y is seen).
                else
                {
                    constantPowers.TryAdd(root, 0);
                    constantPowers[root]++;
                }
            }

            var width = ctx.GetWidth(id);
            var parts = new PolynomialParts(width, coeffSum, constantPowers, others);
            return parts;
        }

        // Ast comparer that places symbols first, sorted alphabetically.
        public static int VarsFirst(AstCtx ctx, AstIdx a, AstIdx b)
        {
            var comeFirst = -1;
            var comeLast = 1;
            var eq = 0;

            var op0 = ctx.IsSymbol(a);
            var op1 = ctx.IsSymbol(b);
            if (op0 && !op1)
                return comeFirst;
            if (op1 && !op0)
                return comeLast;
            if(op0 && op1)
                return ctx.GetSymbolName(a).CompareTo(ctx.GetSymbolName(b));
            return comeLast;
        }

        // Sort nodes canonically:
        // - constants, variables, powers sorted by their base(todo), then the rest.
        private int CompareTo(AstIdx a, AstIdx b)
        {
            var comeFirst = -1;
            var comeLast = 1;
            var eq = 0;

            // Push constants to the left
            var op0 = ctx.GetOpcode(a);
            var op1 = ctx.GetOpcode(b);
            if (op0 == AstOp.Constant)
                return comeFirst;
            if (op1 == AstOp.Constant)
                return comeLast;

            // Sort symbols alphabetically
            if(op0 == AstOp.Symbol && op1 == AstOp.Symbol)
                return ctx.GetSymbolName(a).CompareTo(ctx.GetSymbolName(b));
            if (op0 == AstOp.Pow)
                return comeLast;
            if (op1 == AstOp.Pow)
                return comeFirst;
            return -1;
        }

        private AstIdx GetSubstitution(AstIdx id, Dictionary<AstIdx, AstIdx> substitutionMapping)
        {
            if (substitutionMapping.TryGetValue(id, out var existing))
                return existing;

            var subst = ctx.Symbol($"subst{substitutionMapping.Count}", ctx.GetWidth(id));
            substitutionMapping.TryAdd(id, subst);
            return subst;
        }

        // Try to reduce the number of substituted variables via expressing them in terms of each other.
        // E.g. (x & (x+y) + (x & -(x+y+1)) would yield (x & subst0) + (x & subst1) after substitution,
        // which can then be expressed as (x & subst0) + (x& ~subst0), noting that "-(x+y+1)" is just a negation of "x+y".
        private AstIdx TryUnmergeLinCombs(AstIdx withSubstitutions, Dictionary<AstIdx, AstIdx> substitutionMapping)
        {
            // This could probably be more efficient, but it's a start.
            var rewriteMapping = new Dictionary<AstIdx, AstIdx>();
            bool changed = true;
            while (changed)
            {
            start:
                changed = false;
                var clone = substitutionMapping.ToDictionary(x => x.Key, x => x.Value);
                foreach (var (ast, substVariable) in clone)
                {
                    var neg = ctx.Neg(ast);
                    neg = SimplifyViaRecursiveSiMBA(neg);

                    if (clone.TryGetValue(neg, out var otherSubstVar))
                    {
                        rewriteMapping.Add(substVariable, ctx.Neg(otherSubstVar));
                        substitutionMapping.Remove(ast);
                        goto start;
                    }
                }
            }

            // If we found any substitutions that could be rewritten as negations of other substitutions, replace them.
            // TODO: Cleanup bookkeeping logic. This is a bit messy due an invariant that we maintain.
            if (rewriteMapping.Any())
            {
                // Replace the substitutions
                withSubstitutions = ApplyBackSubstitution(ctx, withSubstitutions, rewriteMapping);

                var substReplacementMapping = new Dictionary<AstIdx, AstIdx>();
                Dictionary<AstIdx, AstIdx> replacementToOriginal = new();
                foreach (var (original, subst) in substitutionMapping)
                {
                    var replacement = ctx.Symbol($"replacement_{substReplacementMapping.Count}", ctx.GetWidth(original));
                    substReplacementMapping.Add(subst, replacement);
                    replacementToOriginal.Add(replacement, original);
                }

                // Replacement the variables again.
                withSubstitutions = ApplyBackSubstitution(ctx, withSubstitutions, substReplacementMapping);

                // Finally apply back substitution again
                var finalMapping = new Dictionary<AstIdx, AstIdx>();
                var delMapping = new Dictionary<AstIdx, AstIdx>();
                substitutionMapping.Clear();
                foreach (var replacement in substReplacementMapping)
                {
                    var subst = ctx.Symbol($"subst{finalMapping.Count}", ctx.GetWidth(replacement.Key));
                    substitutionMapping.Add(replacementToOriginal[replacement.Value], subst);
                    finalMapping.Add(replacement.Value, subst);
                }

                withSubstitutions = ApplyBackSubstitution(ctx, withSubstitutions, finalMapping);
            }

            return withSubstitutions;
        }

        private AstIdx? TrySimplifyMixedPolynomialParts(AstIdx id, Dictionary<AstIdx, AstIdx> substMapping, Dictionary<AstIdx, AstIdx> inverseSubstMapping, List<AstIdx> varList)
        {
            // Back substitute in the (possibly) polynomial parts
            var newId = ApplyBackSubstitution(ctx, id, inverseSubstMapping);

            // Decompose each term into structured polynomial parts
            var terms = GetRootTerms(ctx, newId);
            List<PolynomialParts> polyParts = terms.Select(x => GetPolynomialParts(ctx, x)).ToList();
            // Remove anything we cannot handle.
            var banned = polyParts.Where(x => x.Others.Any()).ToList();
            polyParts.RemoveAll(x => x.Others.Any());

            // Apply the simplification.
            var result = SimplifyParts(ctx.GetWidth(id), polyParts);
            if (result == null)
                return null;

            // Add back any banned parts.
            if(banned.Any())
            {
                var sum = ctx.Add(banned.Select(x => GetAstForPolynomialParts(x)));
                result = ctx.Add(result.Value, sum);
            }

            // Do a full back substitution again.
            result = ApplyBackSubstitution(ctx, result.Value, inverseSubstMapping);

            // Bail out if this resulted in a worse result.
            var cost1 = ctx.GetCost(result.Value);
            var cost2 = ctx.GetCost(newId);
            if (cost1 > cost2)
            {
                return null;
            }

            return result;
        }

        // Rewrite factors of polynomials as linear MBAs(with substitution) with a canonical basis, expand & reduce, then back substitute.
        private AstIdx? SimplifyParts(uint bitSize, IReadOnlyList<PolynomialParts> polyParts)
        {
            var substMapping = new Dictionary<AstIdx, AstIdx>();
            bool isSemiLinear = false;

            // Rewrite as a sum of polynomial parts, where the factors are linear MBAs with substitution of nonlinear parts.
            HashSet<AstIdx> varSet = new();
            List<PolynomialParts> partsWithSubstitutions = new();
            ulong maxDegree = 0;
            int maxVarsInOnePart = 0;
            foreach(var polyPart in polyParts)
            {
                Dictionary<AstIdx, ulong> powers = new();
                ulong degree = 0;

                HashSet<AstIdx> partVars = new();
                foreach(var factor in polyPart.ConstantPowers)
                {
                    var withSubstitutions = GetAstWithSubstitutions(factor.Key, substMapping, ref isSemiLinear);
                    partVars.AddRange(ctx.CollectVariables(withSubstitutions));
                    powers.TryAdd(withSubstitutions, 0);
                    powers[withSubstitutions] += factor.Value;
                    degree += factor.Value;
                }

                varSet.AddRange(partVars);

                partsWithSubstitutions.Add(new PolynomialParts(polyPart.width, polyPart.coeffSum, powers, polyPart.Others));
                if (degree > maxDegree)
                    maxDegree = degree;
                if(partVars.Count > maxVarsInOnePart)
                    maxVarsInOnePart = partVars.Count;   
            }

            var allVars = varSet.OrderBy(x => ctx.GetSymbolName(x)).ToList().AsReadOnly();
            var numCombinations = (ulong)Math.Pow(2, allVars.Count);
            var groupSizes = LinearSimplifier.GetGroupSizes(allVars.Count);

            // Get all possible conjunctions of variables.
            var variableCombinations = LinearSimplifier.GetVariableCombinations(allVars.Count);

            // Keep track of which variables are demanded by which combination,
            // as well as which result vector idx corresponds to which combination.
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var myMask = variableCombinations[i];
                var myIndex = LinearSimplifier.GetGroupSizeIndex(groupSizes, myMask);
                combToMaskAndIdx.Add((myMask, (int)myIndex));
            }

            Dictionary<ulong, AstIdx> basisSubstitutions = new();
            var moduloMask = (ulong)ModuloReducer.GetMask(bitSize);

            var bannedParts = new List<PolynomialParts>();
            List<AstIdx> polys = new();
            foreach (var polyPart in partsWithSubstitutions)
            {
                List<AstIdx> factors = new();
                ulong size = 1;
                foreach (var (factor, degree) in polyPart.ConstantPowers)
                {
                    // Construct a result vector for the linear part.
                    var resultVec = LinearSimplifier.JitResultVector(ctx, bitSize, moduloMask, allVars, factor, isSemiLinear, numCombinations);

                    // Change to the basis referenced in the SiMBA paper. It's just nicer to work with here IMO.
                    var anfVector = new ulong[resultVec.Length];
                    MixedPolynomialSimplifier.GetAnfVector(bitSize, allVars, variableCombinations, combToMaskAndIdx, resultVec, anfVector);

                    // Count the number of non zero elements.
                    ulong numNonZeroes = 0;
                    for (int i = 0; i < anfVector.Length; i++)
                    {
                        // Skip zero elements.
                        var coeff = anfVector[i];
                        if (coeff == 0)
                            continue;
                        numNonZeroes++;
                    }

                    // Calculate the max possible size of the resulting expression when multiplied out.
                    for(ulong i = 0; i < degree; i++)
                    {
                        size = SaturatingMul(size, numNonZeroes);
                    }

                    List<AstIdx> terms = new();
                    for (int i = 0; i < anfVector.Length; i++)
                    {
                        // Skip zero elements.
                        var coeff = anfVector[i];
                        if (coeff == 0)
                            continue;

                        // When the basis is the constant offset, we want to make it just `1`.
                        // Otherwise we just substitute it with a variable.
                        AstIdx basis = ctx.Constant(1, (byte)bitSize);
                        if(i != 0)
                        {
                            if (!basisSubstitutions.TryGetValue((ulong)i, out basis))
                            {
                                basis = ctx.Symbol($"basis{i}", (byte)bitSize);
                                basisSubstitutions.Add((ulong)i, basis);
                            }
                        }

                        var term = ctx.Mul(ctx.Constant(coeff, (byte)bitSize), basis);
                        terms.Add(term);
                    }

                    // Add this as a factor.
                    var sum = ctx.Add(terms);
                    factors.Add(ctx.Pow(sum, ctx.Constant(degree, (byte)bitSize)));
                }

                // If the expanded form would be too large, we want to block this polynomial.
                // It would take too long.
                if(size >= 1000)
                {
                    bannedParts.Add(polyPart);
                    continue;
                }

                // Add in the coefficient.
                AstIdx? poly = null;
                var constOffset = ctx.Constant(polyPart.coeffSum, (byte)bitSize);
                if (factors.Any())
                {
                    poly = ctx.Mul(factors);
                    poly = ctx.Mul(constOffset, poly.Value);
                }

                // If no factors exist, we have a constant term.
                else
                {
                    poly = constOffset;
                }

  
                polys.Add(poly.Value);
            }

            var linComb = ctx.Add(polys);
            var reduced = ExpandReduce(linComb, false);

            if(bannedParts.Any())
            {
                var sum = ctx.Add(bannedParts.Select(x => GetAstForPolynomialParts(x)));
                reduced = ctx.Add(reduced, sum);
            }

            var invBases = basisSubstitutions.ToDictionary(x => x.Value, x => LinearSimplifier.ConjunctionFromVarMask(ctx, allVars, 1, x.Key).Value);
            var backSub = ApplyBackSubstitution(ctx, reduced, invBases);
            backSub = ApplyBackSubstitution(ctx, backSub, substMapping.ToDictionary(x => x.Value, x => x.Key));
            return backSub;
        }

        private ulong SaturatingMul(ulong a, ulong b)
        {
            var value = (UInt128)a * (UInt128)b;
            if (value > ulong.MaxValue)
                return ulong.MaxValue;
            return (ulong)value;
        }

        public static IReadOnlyList<AstIdx> GetRootTerms(AstCtx ctx, AstIdx id)
        {
            var terms = new List<AstIdx>();
            var toVisit = new Stack<AstIdx>();
            toVisit.Push(id);
            while (toVisit.Any())
            {
                var term = toVisit.Pop();
                var opcode = ctx.GetOpcode(term);
                if (opcode == AstOp.Add)
                {
                    toVisit.Push(ctx.GetOp0(term));
                    toVisit.Push(ctx.GetOp1(term));
                }

                // If we have coeff*(x+y) and coeff is a constant, rewrite as coeff*x + coeff*y.
                // If coeff is not a constant then we do not apply it - it would yield exponential growth in the worst case.
                // TODO: Handle polynomial expansion more uniformly.
                else if (opcode == AstOp.Mul && ctx.IsConstant(ctx.GetOp0(term)))
                {
                    var coeff = ctx.GetOp0(term);
                    var other = ctx.GetOp1(term);
                    if (ctx.IsAdd(other))
                    {
                        var sum1 = ctx.Mul(coeff, ctx.GetOp0(other));
                        var sum2 = ctx.Mul(coeff, ctx.GetOp1(other));
                        toVisit.Push(sum1);
                        toVisit.Push(sum2);
                    }

                    else
                    {
                        terms.Add(term);
                    }
                }

                else
                {
                    terms.Add(term);
                }
            }

            return terms;
        }

        public static List<AstIdx> GetRootMultiplications(AstCtx ctx, AstIdx id)
        {
            var terms = new List<AstIdx>();
            var toVisit = new Stack<AstIdx>();
            toVisit.Push(id);
            while (toVisit.Any())
            {
                var term = toVisit.Pop();
                var opcode = ctx.GetOpcode(term);
                if (opcode == AstOp.Mul)
                {
                    toVisit.Push(ctx.GetOp0(term));
                    toVisit.Push(ctx.GetOp1(term));
                }

                else
                {
                    terms.Add(term);
                }
            }

            List<AstIdx> newTerms = new();
            ulong coeff = 1;
            foreach (var term in terms)
            {
                var asConstant = ctx.TryGetConstantValue(term);
                if (asConstant != null)
                {
                    coeff *= asConstant.Value;
                }

                else
                {
                    newTerms.Add(term);
                }
            }

            if (coeff != null)
                newTerms.Insert(0, ctx.Constant(coeff, ctx.GetWidth(id)));

            return newTerms;
        }

        // Try to reduce the polynomial parts of an expression using the polynomial reduction algorithm.
        private AstIdx? ReducePolynomials(IReadOnlyList<AstIdx> terms, IReadOnlyDictionary<AstIdx, AstIdx> substMapping, IReadOnlyDictionary<AstIdx, AstIdx> inverseSubstMapping)
        {
            // Try to decompose into high degree polynomials parts.
            List<PolynomialParts> polyTerms = new();
            List<AstIdx> other = new();
            foreach(var term in terms)
            {
                // Typically this is going to be a multiplication(coefficient over substituted variable), or whole substituted variable.
                // TODO: Handle negation.
                var opcode = ctx.GetOpcode(term);
                if(opcode != AstOp.Mul && opcode != AstOp.Symbol)
                    goto skip;
                
                // Search for coeff*subst
                if(opcode == AstOp.Mul)
                {
                    // If multiplication, we are looking for coeff*(subst), where coeff is a constant.
                    var coeff = ctx.GetOp0(term);
                    if (!ctx.IsConstant(coeff))
                        goto skip;

                    // Look for a variable on the rhs of the multiplication.
                    var rhs = ctx.GetOp1(term);
                    if (!IsSubstitutedPolynomialSymbol(rhs, inverseSubstMapping))
                        goto skip;

                    // We found a polynomial part, add it to the list.
                    var invSubst = inverseSubstMapping[rhs];
                    polyTerms.Add(GetPolynomialParts(ctx, ctx.Mul(coeff, invSubst)));
                    continue;
                }

                // Search for a plain substitution(omitted coefficient of 1)
                if(opcode == AstOp.Symbol && IsSubstitutedPolynomialSymbol(term, inverseSubstMapping))
                {
                    var invSubst = inverseSubstMapping[term];
                    polyTerms.Add(GetPolynomialParts(ctx, invSubst));
                    continue;
                }

                skip:
                other.Add(term);
                continue;
            }

            // For now we ignore polynomials with e.g. nonconstant powers.
            var discarded = polyTerms.Where(x => x.Others.Any()).ToList();
            polyTerms.RemoveAll(x => x.Others.Any());

            // Bail out if we found no polynomial terms.
            if (!polyTerms.Any())
                return null;

            // Now we have a list of polynomial parts, we want to try to simplify them.
            var uniqueBases = new Dictionary<AstIdx, ulong>();
            foreach (var poly in polyTerms)
            {
                foreach(var (_base, degree) in poly.ConstantPowers)
                {
                    // Set the default degree to zero.
                    uniqueBases.TryAdd(_base, 0);

                    // For each unique base, we want to keep track of the highest degree.
                    var oldDegree = uniqueBases[_base];
                    var newDeg = degree;
                    if(newDeg > oldDegree)
                        uniqueBases[_base] = newDeg;
                }
            }

            // Bail out if there are more than three variables.
            // Nothing prevents more variables, but in general more than 3 variables indicates that there are bitwise parts
            // that we are not handling.
            if (uniqueBases.Count > 3)
                return null;

            // Compute the dense vector size as a heuristic.
            ulong vecSize = 1;
            foreach (var degree in uniqueBases.Values)
                vecSize *= degree;

            // If the dense vector size would be greater than 64**3, we bail out.
            // In those cases, we may consider implementing variable partitioning and simplifying each partition separately.
            if (vecSize > 64*64*64)
                return null;

            // For now we only support polynomials up to degree 255, although this is a somewhat arbitrary limit.
            ulong limit = 254;
            var maxDeg = uniqueBases.MaxBy(x => x.Value).Value;
            if (maxDeg > limit)
                throw new InvalidOperationException($"Polynomial has degree {maxDeg} which is greater than the limit {limit}");

            // Otherwise we can carry on and simplify.
            var width = ctx.GetWidth(terms.First());
            var sparsePoly = new SparsePolynomial(uniqueBases.Count, width);

            // Sort the bases alphabetically.
            var orderedVars = uniqueBases.Keys.ToList();
            orderedVars.Sort((x, y) => { return VarsFirst(ctx, x, y); });

            // Fill in the sparse polynomial data structure.
            foreach (var poly in polyTerms)
            {
                var coeff = poly.coeffSum;
              
                var constPowers = poly.ConstantPowers;
                var degrees = new byte[orderedVars.Count];
                for(int varIdx = 0; varIdx < orderedVars.Count; varIdx++)
                {
                    var variable = orderedVars[varIdx];
                    ulong degree = 0;
                    constPowers.TryGetValue(variable, out degree);
                    degrees[varIdx] = (byte)degree;
                }

                // Add this monomial to the sparse polynomial.
                var monom = new Monomial(degrees);
                sparsePoly.Sum(monom, coeff);
            }

            // Reduce.
            var simplified = PolynomialReducer.Reduce(sparsePoly);

            // The polynomial reduction algorithm guarantees a minimal degree result, but it's often not the most simple result.
            // E.g. "x**10" becomes "96*x0 + 40*x0**2 + 84*x0**3 + 210*x0**4 + 161*x0**5 + 171*x0**6 + 42*x0**7 + 220*x0**8 + 1*x0**9" on 8 bits.
            // In the case of a single term solution, we reject the result if it is more complex.
            if (polyTerms.Count == 1 && simplified.coeffs.Count(x => x.Value != 0) > 1)
                return null;

            List<AstIdx> newTerms = new();
            // Add back all of the ignored parts.
            newTerms.AddRange(other);
            // Add back all of the discarded polynomial parts
            foreach(var part in discarded)
            {
                var ast = GetAstForPolynomialParts(part);
                newTerms.Add(ast);
            }

            // Then finally convert the sparse polynomial back to an AST.
            foreach(var (monom, coeff) in simplified.coeffs)
            {
                if (coeff == 0)
                    continue;

                List<AstIdx> factors = new();
                factors.Add(ctx.Constant(coeff, width));
                for(int i = 0; i < orderedVars.Count; i++)
                {
                    var deg = monom.GetVarDeg(i);
                    if(deg == 0)
                    {
                        factors.Add(ctx.Constant(1, width));
                        continue;
                    }

                    var variable = orderedVars[i];
                    if (deg == 1)
                    {
                        factors.Add(variable);
                        continue;
                    }

                    factors.Add(ctx.Pow(variable, ctx.Constant(deg, width)));
                }

                var term = ctx.Mul(factors);
                newTerms.Add(term);
            }


            // If the whole polynomial was folded to zero, discard it.
            if (newTerms.Count == 0)
                newTerms.Add(ctx.Constant(0, width));

            var result = ctx.Add(newTerms);
            // Constant fold.
            result = ctx.RecursiveSimplify(result);
            return result;
        }

        private bool IsSubstitutedPolynomialSymbol(AstIdx id, IReadOnlyDictionary<AstIdx, AstIdx> inverseSubstMapping)
        {
            if (!ctx.IsSymbol(id))
                return false;

            // Make sure the variable is a substituted part
            if (!inverseSubstMapping.TryGetValue(id, out var substituted))
                return false;
            // Ensure that the substituted part atleast contains a polynomial somewhere.
            if(!ctx.GetHasPoly(substituted))
                return false;

            // Now we are looking for either a mul or pow.
            var opcode = ctx.GetOpcode(substituted);
            if(opcode == AstOp.Pow)
            {
                return true;
            }

            if(opcode == AstOp.Mul)
            {
                // If the first operand is not a constant, we have a polynomial part.
                var rhs = ctx.GetOp0(substituted);
                if (!ctx.IsConstant(rhs))
                    return true;

                // Otherwise we need to look for a polynomial part in the second operand.
                var lhs = ctx.GetOp1(substituted);
                var lhsKind = ctx.GetOpcode(lhs);
                if(lhsKind == AstOp.Mul || lhsKind == AstOp.Pow)
                    return true;
            }

            return false;
        }

        // Recursive try to expand the polynomial parts, then reduce.
        public AstIdx ExpandReduce(AstIdx id, bool polySimplify = true)
        {
            var substMapping = new Dictionary<AstIdx, AstIdx>();
            var result = TryExpand(id, substMapping, true);

            List<AstIdx> terms = new();
            var width = ctx.GetWidth(id);
            foreach(var (monom, coeff) in result.coeffs)
            {
                List<AstIdx> factors = new();
                factors.Add(ctx.Constant(coeff, width));
                foreach(var (varIdx, degree) in monom.varDegrees)
                {
                    // Skip a constant factor of 1
                    if (degree == 0)
                        continue;
                    if(degree == 1)
                    {
                        factors.Add(varIdx);
                        continue;
                    }

                    var pow = ctx.Pow(varIdx, ctx.Constant(degree, width));
                    factors.Add(pow);
                }

                var product = ctx.Mul(factors);
                terms.Add(product);
            }

            // Convert the reduced polynomial to an ast.
            var sum = ctx.Add(terms);

            // Back substitute the substitute variables.
            var inverseMapping = substMapping.ToDictionary(x => x.Value, x => x.Key);
            sum = ApplyBackSubstitution(ctx, sum, inverseMapping);

            // Try to simplify using the general simplifier.
            sum = ctx.RecursiveSimplify(sum);
            sum = SimplifyViaRecursiveSiMBA(sum, polySimplify);

            // Reject solution if it is more complex.
            if (ctx.GetCost(sum) > ctx.GetCost(id))
                return id;

            return sum;
        }

        // Recursively expand and reduce polynomial parts.
        private IntermediatePoly TryExpand(AstIdx id, Dictionary<AstIdx, AstIdx> substMapping, bool isRoot)
        {
            var width = ctx.GetWidth(id);
            var opcode = ctx.GetOpcode(id);
            IntermediatePoly resultPoly = null;

            // Substitute a node.
            var subst = (AstIdx id) =>
            {
                var subst = GetSubstitution(id, substMapping);
                var poly = new IntermediatePoly(width);
                var monom = new IntermediateMonomial(new Dictionary<AstIdx, ulong>() { { subst, 1 } });
                poly.Sum(monom, 1);
                return poly;
            };

            switch(opcode)
            {
                case AstOp.Mul:
                    var factors = GetRootMultiplications(ctx, id);
                    var facPolys = factors.Select(x => TryExpand(x, substMapping, false)).ToList();
                    var product = IntermediatePoly.Mul(ctx,facPolys);
                    resultPoly = product;

                    // In this case we should probably distribute the coefficient down always.
                    break;
                case AstOp.Add:
                    var terms = GetRootTerms(ctx, id);
                    var termPolys = terms.Select(x => TryExpand(x, substMapping, false)).ToList();
                    var sum = IntermediatePoly.Add(termPolys);
                    resultPoly = sum;

                    break;

                case AstOp.Pow:
                    var raisedTo = ctx.TryGetConstantValue(ctx.GetOp1(id));
                    if (raisedTo == null)
                        throw new InvalidOperationException($"TODO: Handle powers of nonconstant degree");

                    // Unroll the power into repeated multiplications, then recurse down.
                    var facs = Enumerable.Repeat(ctx.GetOp0(id), (int)(uint)raisedTo).ToList();
                    var mul = ctx.Mul(facs);
                    resultPoly = TryExpand(mul, substMapping, false);

                    break;

                // In the case of a symbol, just directly convert it a polynomial.
                case AstOp.Symbol:
                    var symbolPoly = new IntermediatePoly(width);
                    var symbolMonomial = new IntermediateMonomial(new Dictionary<AstIdx, ulong>() { { id, 1 } });
                    symbolPoly.coeffs[symbolMonomial] = 1;
                    resultPoly = symbolPoly;
                    break;

                case AstOp.Constant:
                    var constPoly = new IntermediatePoly(width);
                    var constant = ctx.GetConstantValue(id);
                    var constMonom = IntermediateMonomial.Constant(ctx, width);
                    constPoly.coeffs[constMonom] = constant;
                    resultPoly = constPoly;
                    break;

                case AstOp.And:
                case AstOp.Or:
                case AstOp.Xor:
                    // Recursively try to expand and reduce the results.
                    var v0 = ExpandReduce(ctx.GetOp0(id));
                    var v1 = ExpandReduce(ctx.GetOp1(id));
                    var bitwise = ctx.Binop(opcode, v0, v1);

                    // Substitute the bitwise operation.
                    var poly = subst(bitwise);
                    return poly;

                case AstOp.Neg:
                    // In the case of a negation, we can apply the identify ~x = -x-1
                    var neg1 = ctx.Constant(ulong.MaxValue, width);
                    var negated = ctx.Add(neg1, ctx.Mul(neg1, ctx.GetOp0(id)));
                    // Forward the isRoot argument.
                    return TryExpand(negated, substMapping, isRoot);

                default:
                    throw new InvalidOperationException($"Unrecognized operator: {opcode}");
            }

            // If this is the root of a polynomial part, we want to try and reduce it.
            // Alternatively we may apply a reduction if there are too many terms.
            bool shouldReduce = isRoot || resultPoly?.coeffs?.Count > 10;
            if(shouldReduce && resultPoly != null)
            {
                resultPoly = TryReduce(resultPoly);
            }

            // TODO: Backoff heuristic if the swell is still too large.
            return resultPoly;
        }

        private IntermediatePoly TryReduce(IntermediatePoly poly)
        {
            var uniqueBases = new Dictionary<AstIdx, ulong>();
            foreach (var monom in poly.coeffs.Keys)
            {
                foreach (var (basis, degree) in monom.varDegrees)
                {
                    uniqueBases.TryAdd(basis, 0);
                    var oldDegree = uniqueBases[basis];
                    if (degree > oldDegree)
                        uniqueBases[basis] = degree;
                }
            }

            // For now we only support up to 8 variables. Note that in practice this limit could be increased.
            if (uniqueBases.Count > 8)
                return poly;

            // Place a hard limit on the max degree.
            ulong limit = 254;
            if (uniqueBases.Any(x => x.Value > limit))
                return poly;

            ulong matrixSize = 1;
            foreach (var deg in uniqueBases.Keys)
            {
                // Bail out if the result would be too large.
                UInt128 result = matrixSize * deg;
                if (result > (UInt128)(64*64*64))
                    return poly;

                matrixSize *= deg;
                matrixSize &= poly.moduloMask;
            }
            
            // Place a limit on the matrix size.
            if (matrixSize > (ulong)(64*64*64))
                return poly;

            var width = poly.bitWidth;
            var sparsePoly = new SparsePolynomial(uniqueBases.Count, (byte)width);

            // Sort the bases alphabetically.
            var orderedVars = uniqueBases.Keys.ToList();
            orderedVars.Sort((x, y) => { return VarsFirst(ctx, x, y); });

            // Fill in the sparse polynomial data structure.
            var degrees = new byte[orderedVars.Count];
            foreach (var (monom, coeff) in poly.coeffs)
            {
                for(int varIdx = 0; varIdx < orderedVars.Count; varIdx++)
                {
                    var variable = orderedVars[varIdx];
                    ulong degree = 0;
                    monom.varDegrees.TryGetValue(variable, out degree);
                    degrees[varIdx] = (byte)degree;
                }

                // Add this momomial to the sparse polynomial.
                var m = new Monomial(degrees);
                sparsePoly.Sum(m, coeff);
            }

            // Reduce.
            var simplified = PolynomialReducer.Reduce(sparsePoly);
            var oldCount = poly.coeffs.Count(x => x.Value != 0);
            var newCount = simplified.coeffs.Count(x => x.Value != 0);
            // If we got a result with more terms, skip it.
            // This is required when doing expansion, since expansion is exponential in the number of terms.
            if(newCount > oldCount)
                return poly;


            var outPoly = new IntermediatePoly(width);
            // Otherwise we can convert the sparse polynomial back to an AST.
            foreach(var (monom, coeff) in simplified.coeffs)
            {
                if (coeff == 0)
                    continue;

                Dictionary<AstIdx, ulong> varDegrees = new();
                for(int i = 0; i < orderedVars.Count; i++)
                {
                    var deg = monom.GetVarDeg(i);
                    if (deg == 0)
                        continue;
                    varDegrees.Add(orderedVars[i], deg);
                }

                // Handle the case of a constant offset.
                if(varDegrees.Count == 0)
                {
                    varDegrees.Add(ctx.Constant(1, width), 1);
                }

                var m = new IntermediateMonomial(varDegrees);
                outPoly.Sum(m, coeff);
            }

            return outPoly;
        }

        private static AstIdx ApplyBackSubstitution(AstCtx ctx, AstIdx id, Dictionary<AstIdx, AstIdx> backSubstitutions)
        {
            if (backSubstitutions.TryGetValue(id, out var backSub))
                return backSub;

            var op0 = () => ApplyBackSubstitution(ctx, ctx.GetOp0(id), backSubstitutions);
            var op1 = () => ApplyBackSubstitution(ctx, ctx.GetOp1(id), backSubstitutions);

            var opcode = ctx.GetOpcode(id);
            return opcode switch
            {
                AstOp.None => throw new NotImplementedException(),
                AstOp.Add => ctx.Add(op0(), op1()),
                AstOp.Mul => ctx.Mul(op0(), op1()),
                AstOp.Pow => ctx.Pow(op0(), op1()),
                AstOp.And => ctx.And(op0(), op1()),
                AstOp.Or => ctx.Or(op0(), op1()),
                AstOp.Xor => ctx.Xor(op0(), op1()),
                AstOp.Neg => ctx.Neg(op0()),
                AstOp.Constant => id,
                AstOp.Symbol => id,
            };
        }
    }
}
