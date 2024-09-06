using Iced.Intel;
using Mba.Simplifier.Bindings;
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

        private GeneralSimplifier(AstCtx ctx)
        {
            this.ctx = ctx;
        }

        private AstIdx SimplifyGeneral(AstIdx id, bool useIsle = true)
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
                // Try to simplify the polynomial parts.
                // Note that "TrySimplifyPolynomialParts" will update all of the data structures according(substMapping, inverseMapping, variables).
                var maybeSimplified = TrySimplifyMixedPolynomialParts(withSubstitutions, substMapping, inverseMapping, variables);
                if (maybeSimplified != null)
                    withSubstitutions = maybeSimplified.Value;
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

        // Identify and try to eliminate polynomial MBA parts.
        private AstIdx? TrySimplifyMixedPolynomialParts(AstIdx id, Dictionary<AstIdx, AstIdx> substMapping, Dictionary<AstIdx, AstIdx> inverseSubstMapping, List<AstIdx> varList)
        {
            // Decompose the input expression into a summation of terms.
            var terms = GetRootTerms(ctx,id);

            // Decompose the summation of terms into a list of possible candidates, and a list of terms that cannot possibly be candidates.
            List<AstIdx> cands = new();
            List<AstIdx> other = new();
            foreach (var term in terms)
            {
                var opcode = ctx.GetOpcode(term);

                // (subst) is a possible candidate,
                if (inverseSubstMapping.TryGetValue(term, out var existing))
                {
                    cands.Add(existing);
                }
                else if (opcode == AstOp.Neg && inverseSubstMapping.TryGetValue(ctx.GetOp0(term), out existing))
                {
                    // Get the term without negation.
                    var op0 = existing;

                    // Rewrite ~x as -x-1, and throw the -1 offset into the term list.
                    var negativeOne = ctx.Constant(ulong.MaxValue, ctx.GetWidth(op0));
                    op0 = ctx.Mul(negativeOne, op0);
                    other.Insert(0, negativeOne);
                    cands.Add(op0);
                }
                // coeff * subst is another possible candidate
                else if (opcode == AstOp.Mul && inverseSubstMapping.TryGetValue(ctx.GetOp1(term), out existing))
                {
                    cands.Add(ctx.Mul(ctx.GetOp0(term), existing));
                }
                else
                {
                    other.Add(term);
                }
            }

            // Now we have a summation of candidates where each cand could possibly be a polynomial MBA.
            // Walk through the terms and decompose them into polynomial parts.
            List<AstIdx> degreeTwoPolys = new();
            List<AstIdx> notDegreeTwoPolys = new();
            var newSubstMapping = new Dictionary<AstIdx, AstIdx>();
            foreach (var cand in cands)
            {
                // Split the candidate into a summation of terms.
                var candTerms = GetRootTerms(ctx, cand);

                // Decompose each term into a degree two polynomial.
                foreach (var term in candTerms)
                {
                    var multiplications = GetRootMultiplications(ctx, term);

                    // If we have 1111*x*y, rewrite as (1111*x)*y.
                    if (multiplications.Count == 3 && ctx.IsConstant(multiplications[0]))
                    {
                        multiplications[0] = ctx.Mul(multiplications[0], multiplications[1]);
                        multiplications.RemoveAt(1);
                    }

                    if (multiplications.Count == 2)
                    {
                        bool isSemiLinear = false;
                        var op0 = GetAstWithSubstitutions(multiplications[0], newSubstMapping, ref isSemiLinear, false);
                        if (isSemiLinear)
                            throw new InvalidOperationException("Constants are not allowed in polynomials during simplification!");
                        var op1 = GetAstWithSubstitutions(multiplications[1], newSubstMapping, ref isSemiLinear, false);

                        var poly = ctx.Mul(op0, op1);
                        degreeTwoPolys.Add(poly);
                    }

                    else
                    {
                        // Otherwise this is not a polynomial part.
                        notDegreeTwoPolys.Add(term);
                    }
                }
            }

            // If we failed to find any degree two polynomials, we can exit early.
            if (!degreeTwoPolys.Any())
                return null;

            if (degreeTwoPolys.Any())
            {
                // If we have a degree two polynomial simplify it.
                // Note that we only support up to two vars for now,
                AstIdx? simpl = null;
                var allVars = degreeTwoPolys.SelectMany(x => ctx.CollectVariables(x)).ToHashSet();
                if (allVars.Count == 2)
                {
                    var hello = ctx.Add(degreeTwoPolys);
                    simpl = MixedPolynomialSimplifier.Simplify(ctx, ctx.GetWidth(degreeTwoPolys.First()), degreeTwoPolys);
                }

                else
                {
                    simpl = ctx.Add(degreeTwoPolys);
                }

                simpl = ApplyBackSubstitution(ctx, simpl.Value, newSubstMapping.ToDictionary(x => x.Value, x => x.Key));

                degreeTwoPolys.Clear();
                degreeTwoPolys.Add(simpl.Value);
            }

            // Now comes the fun part: Trying to piece the parts back together.
            var termList = new List<AstIdx>();
            // First we add all of non-candidates
            termList.AddRange(other);

            // Then we add all of the nonpolynomial parts of the candidates.
            termList.AddRange(notDegreeTwoPolys);

            // And finally we add the polynomial parts.
            termList.AddRange(degreeTwoPolys);

            // Sum up all of the parts.
            var sum = ctx.Add(termList);

            // Simplify the final result via term rewriting.
            bool isSl = false;
            sum = SimplifyViaTermRewriting(sum);
            // Apply substitution again to get a linear result.
            sum = GetAstWithSubstitutions(sum, substMapping, ref isSl);

            // Simplify the linear part via SiMBA, and disable the polynomial simplification step
            // to avoid infinite recursion.
            sum = SimplifyViaRecursiveSiMBA(sum, polySimplify: false);

            varList.Clear();
            ctx.CollectVariables(sum, varList);
            var vars = varList.ToHashSet();
            inverseSubstMapping.Clear();
            foreach (var (value, substitute) in substMapping.ToList())
            {
                if (!vars.Contains(substitute))
                    substMapping.Remove(value);
                else
                    inverseSubstMapping.Add(substitute, value);
            }

            return sum;
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
