using Iced.Intel;
using Mba.Ast;
using Mba.Common.MSiMBA;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Interpreter;
using Mba.Simplifier.LinEq;
using Mba.Simplifier.Polynomial;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Linq;
using System.Numerics;
using System.Reflection.Metadata.Ecma335;
using System.Text;
using System.Threading.Tasks;
using System.Xml.Linq;

namespace Mba.Simplifier.Pipeline
{
    public class GeneralSimplifier
    {
        private const bool REDUCE_POLYS = true;

        private readonly AstCtx ctx;

        // For any given node, we store the best possible ISLE result.
        private readonly Dictionary<uint, uint> isleCache = new();

        // For any given node, we store the optimal representation yielded by SiMBA.
        private readonly Dictionary<uint, uint> simbaCache = new();

        private int substCount = 0;

        public static AstIdx Simplify(AstCtx ctx, AstIdx id) => new GeneralSimplifier(ctx).SimplifyGeneral(id);

        public GeneralSimplifier(AstCtx ctx)
        {
            this.ctx = ctx;
        }

        public AstIdx SimplifyGeneral(AstIdx id, bool useIsle = true)
        {
            // Simplify the AST via efficient, recursive term rewriting(ISLE).
            if(useIsle)
                id = SimplifyViaTermRewriting(id);

            // Simplify via recursive SiMBA.
            id = SimplifyViaRecursiveSiMBA(id);
            return id;
        }

        // Simplify the AST via efficient, recursive term rewriting(ISLE).
        private AstIdx SimplifyViaTermRewriting(AstIdx id)
        {
            if(isleCache.TryGetValue(id, out var existingIdx))
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
            if(cacheIsle)
            {
                isleCache.TryAdd(initialId, id);
                isleCache.TryAdd(id, id);
            }
            return id;
        }

        // Simplify the AST via recursive SiMBA application.
        private AstIdx SimplifyViaRecursiveSiMBA(AstIdx id, bool polySimplify = true)
        {
            if(simbaCache.TryGetValue(id, out var existing))
                return existing;
            id = SimplifyViaTermRewriting(id);
            // TODO: We should probably apply ISLE before attempting any other steps.

            // For linear and semi-linear MBAs, we can skip the substitution / polynomial simplification steps.
            var linClass = ctx.GetClass(id);
            if(ctx.IsConstant(id))
                return id;

            if(linClass != AstClassification.Nonlinear)
            {
                // Bail out if there are too many variables.
                var vars = ctx.CollectVariables(id);
                if(vars.Count > 11 || vars.Count == 0)
                {
                    var simplified = SimplifyViaTermRewriting(id);
                    simbaCache.TryAdd(id, simplified);
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
            // Apply recursive term rewriting again in hopes that it will cheaply reduce some parts.
            withSubstitutions = SimplifyViaTermRewriting(withSubstitutions);

            // Discard any vanished substitutions
            var usedVars = ctx.CollectVariables(withSubstitutions).ToHashSet();
            foreach(var (substValue, substVar) in substMapping.ToList())
            {
                if(!usedVars.Contains(substVar))
                    substMapping.Remove(substValue);
            }

            // Try to take a guess (MSiMBA) and prove it's equivalence
            var guess = SimplifyViaGuessAndProve(withSubstitutions, substMapping, ref isSemiLinear);
            if(guess != null)
            {
                // Apply constant folding / term rewriting.
                var simplGuess = SimplifyViaTermRewriting(guess.Value);

                // Cache the result.
                simbaCache.TryAdd(id, simplGuess);
                return simplGuess;
            }


            // If there are multiple substitutions, try to minimize the number of substitutions.
            if(substMapping.Count > 1)
                withSubstitutions = TryUnmergeLinCombs(withSubstitutions, substMapping, ref isSemiLinear);
            withSubstitutions = SimplifyViaTermRewriting(withSubstitutions);


            // If polynomial parts are present, try to simplify them.
            var inverseMapping = substMapping.ToDictionary(x => x.Value, x => x.Key);
            AstIdx? reducedPoly = null;
            if(polySimplify && ctx.GetHasPoly(id))
            {
                // Try to reduce the polynomial parts using "pure" polynomial reduction algorithms.
                reducedPoly = ReducePolynomials(GetRootTerms(ctx, withSubstitutions), substMapping, inverseMapping);

                // If we succeeded, reset the state.
                if(reducedPoly != null)
                {
                    // Back substitute the original substitutions.
                    reducedPoly = BackSubstitute(ctx, reducedPoly.Value, inverseMapping);

                    // Reset internal state.
                    substMapping.Clear();
                    isSemiLinear = false;
                    withSubstitutions = GetAstWithSubstitutions(reducedPoly.Value, substMapping, ref isSemiLinear);
                    inverseMapping = substMapping.ToDictionary(x => x.Value, x => x.Key);
                }
            }

            // If there are any substitutions, we want to try simplifying the polynomial parts.
            var variables = ctx.CollectVariables(withSubstitutions);
            if(REDUCE_POLYS && polySimplify && substMapping.Count > 0 && ctx.GetHasPoly(id))
            {
                var maybeSimplified = TrySimplifyMixedPolynomialParts(withSubstitutions, substMapping, inverseMapping, variables);
                if(maybeSimplified != null && maybeSimplified.Value != id)
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
            if(variables.Count > 11)
            {
                var simplified = SimplifyViaTermRewriting(id);
                simbaCache.TryAdd(id, simplified);
                return simplified;
            }

            // Simplify the resulting expression via term rewriting.
            // TODO: If there are too many variables(more than 5), we should partition wrt variable count and simplify each partition.
            withSubstitutions = SimplifyViaTermRewriting(withSubstitutions);

            var result = withSubstitutions;
            if(!ctx.IsConstant(withSubstitutions))
                result = LinearSimplifier.Run(ctx.GetWidth(withSubstitutions), ctx, withSubstitutions, false, isSemiLinear, false, variables);
            var backSub = BackSubstitute(ctx, result, inverseMapping);

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
            if(newVars.Count < variables.Count)
            {
                propagated = SimplifyViaRecursiveSiMBA(propagated, true);
            }

            simbaCache.TryAdd(propagated, propagated);

            return propagated;
        }

        private static ulong Pow(ulong bbase, ulong exponent)
        {
            ulong result = 1;

            for (ulong term = bbase; exponent != 0; term = term * term)
            {
                if(exponent % 2 != 0) { result *= term; }
                exponent /= 2;
            }

            return result;
        }

        private AstIdx GetAstWithSubstitutions(AstIdx id, Dictionary<AstIdx, AstIdx> substitutionMapping, ref bool isSemiLinear, bool inBitwise = false)
        {
            // Sometimes we perform constant folding in this method.
            // To make sure that we correctly track whether the expression is semi-linear, we use this method to process replacements.
            var visitReplacement = (AstIdx replacementIdx, bool inBitwise, ref bool isSemiLinear) => GetAstWithSubstitutions(replacementIdx, substitutionMapping, ref isSemiLinear, inBitwise);
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
                    if(inBitwise)
                    {
                        var simplified = SimplifyViaRecursiveSiMBA(id);
                        if(simplified != id)
                        {
                            id = simplified;
                            goto start;
                        }
                    }

                    // If the above check still yielded something that is not linear, we apply substitution.
                    if(inBitwise)
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
                    if(opcode == AstOp.Mul && ctx.GetOpcode(v0) != AstOp.Constant)
                    {
                        v0 = SimplifyViaRecursiveSiMBA(v0);
                        v1 = SimplifyViaRecursiveSiMBA(v1);

                        if(ctx.GetOpcode(v1) == AstOp.Constant)
                            (v0, v1) = (v1, v0);
                    }

                    // If both children are still not constant after applying recursive simplification,
                    // then we need to perform substitution.
                    if(opcode == AstOp.Mul && ctx.GetOpcode(v0) != AstOp.Constant)
                    {
                        var mul = ctx.Mul(v0, v1);
                        return GetSubstitution(mul, substitutionMapping);
                    }

                    // Otherwise we have a multiplication where one term is a constant(linear).
                    if(opcode == AstOp.Mul)
                    {
                        var constTerm = v0;

                        // In the case of coeff*(x+y), where coeff is a constant, we want to distribute it, yielding coeff*x + coeff*y.
                        if(ctx.GetOpcode(v1) == AstOp.Add)
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
                    if(ctx.IsConstant(basis) && ctx.IsConstant(degree))
                    {
                        var folded = Pow(ctx.GetConstantValue(basis), ctx.GetConstantValue(degree));
                        return visitReplacement(ctx.Constant(folded, ctx.GetWidth(basis)), inBitwise, ref isSemiLinear);
                    }

                    var pow = ctx.Pow(basis, degree);
                    return GetSubstitution(pow, substitutionMapping);

                case AstOp.And:
                case AstOp.Or:
                case AstOp.Xor:
                    if(opcode == AstOp.And)
                    {
                        // Simplify both children.
                        var and0 = op0(true, ref isSemiLinear);
                        var and1 = op1(true, ref isSemiLinear);

                        var id0 = ctx.GetOp0(id);
                        var id1 = ctx.GetOp1(id);
                        // Move constants to the left
                        if(ctx.IsConstant(and1))
                        {
                            (and0, and1) = (and1, and0);
                            (id0, id1) = (id1, id0);
                        }

                        // Rewrite (a&mask) as `Trunc(a)`, or `Trunc(a & mask)` if mask is not completely a bit mask.
                        // This is a form of adhoc demanded bits based simplification
                        if(ctx.IsConstant(and0) && !ctx.IsConstant(and1))
                        {
                            var andMask = ctx.GetConstantValue(and0);
                            if(CanEliminateMask(andMask, id1))
                                return visitReplacement(id1, inBitwise, ref isSemiLinear);


                            var truncWidth = ConstantToTruncWidth(andMask);
                            if(truncWidth != 0 && truncWidth < ctx.GetWidth(id))
                            {
                                isSemiLinear = true;
                                var moduloWidth = 64 - (uint)BitOperations.LeadingZeroCount(andMask);
                                var moduloMask = ModuloReducer.GetMask(moduloWidth);
                                var trunc = Truncate(id1, (uint)truncWidth, moduloMask);

                                var before = trunc;
                                trunc = visitReplacement(before, true, ref isSemiLinear);
                                var ext = ctx.Zext(trunc, ctx.GetWidth(id));
                                if(ModuloReducer.GetMask((uint)truncWidth) != andMask)
                                    ext = ctx.And(ctx.Constant(andMask, ctx.GetWidth(id)), ext);

                                return ext;
                            }
                        }


                        return ctx.And(and0, and1);
                    }
                    if(opcode == AstOp.Or)
                        return ctx.Or(op0(true, ref isSemiLinear), op1(true, ref isSemiLinear));
                    if(opcode == AstOp.Xor)
                        return ctx.Xor(op0(true, ref isSemiLinear), op1(true, ref isSemiLinear));
                    throw new InvalidOperationException("Unrecognized opcode!");
                case AstOp.Neg:
                    if(inBitwise)
                    {
                        // Temporary disabled because it can cause stack overflows.
                        /*
                        // If we encounter a negation inside of a bitwise operator, try to simplify the subtree.
                        var simplified = SimplifyViaRecursiveSiMBA(id);
                        if(simplified != id)
                        {
                            id = simplified;
                            goto start;
                        }
                        */

                        // Otherwise we have a negation that cannot be distributed, so we leave it as is.
                        return ctx.Neg(op0(inBitwise, ref isSemiLinear));
                    }

                    else
                    {
                        // Since negation can be either arithmetic or bitwise, we forward the inBitwise argument.
                        return ctx.Neg(op0(inBitwise, ref isSemiLinear));
                    }

                case AstOp.Lshr:
                    var src = SimplifyViaRecursiveSiMBA(ctx.GetOp0(id));
                    var by = SimplifyViaRecursiveSiMBA(ctx.GetOp1(id));
                    // Apply constant propagation if both nodes fold.
                    if(ctx.IsConstant(src) && ctx.IsConstant(by))
                    {
                        var value = ctx.GetConstantValue(src) >> (ushort)(ctx.GetConstantValue(by) % (ulong)ctx.GetWidth(id));
                        var constant = ctx.Constant(value, ctx.GetWidth(id));
                        return visitReplacement(constant, inBitwise, ref isSemiLinear);
                    }

                    return GetSubstitution(ctx.Lshr(src, by), substitutionMapping);

                case AstOp.Zext:
                    isSemiLinear = true;
                    return ctx.Zext(op0(true, ref isSemiLinear), ctx.GetWidth(id));

                case AstOp.Trunc:
                    isSemiLinear = true;
                    var child = ctx.GetOp0(id);
                    var w = ctx.GetWidth(id);
                    var truncated = AstRewriter.ChangeBitwidth(ctx, child, w, ModuloReducer.GetMask(w), new());
                    return ctx.Trunc(truncated, ctx.GetWidth(id));

                case AstOp.Constant:
                    // If a bitwise constant is present, we want to mark it as semi-linear
                    if(inBitwise)
                        isSemiLinear = true;

                    return id;
                case AstOp.Symbol:
                    return id;

                default:
                    throw new InvalidOperationException($"Unrecognized opcode: {opcode}!");
            }
        }

        // Look for (mask&expr), where the knownbits of expr allow us to eliminate the mask
        private bool CanEliminateMask(ulong andMask, AstIdx idx)
        {
            var knownBits = ctx.GetKnownBits(idx);

            var zeroes = ~andMask & ModuloReducer.GetMask(ctx.GetWidth(idx));
            if((zeroes & knownBits.Zeroes) == zeroes)
                return true;

            return false;

        }

        private ulong ConstantToTruncWidth(ulong c)
        {
            var lz = BitOperations.LeadingZeroCount(c);
            var minWidth = 64 - lz;
            if(minWidth <= 7)
                return 8;
            if(minWidth <= 16)
                return 16;
            if(minWidth <= 32)
                return 32;
            return 0;
        }

        private AstIdx Truncate(AstIdx idx, uint width, ulong moduloMask)
        {
            var trunc = AstRewriter.ChangeBitwidth(ctx, idx, width, moduloMask, new());
            return trunc;
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

            var roots = GetRootMultiplications(ctx, id);
            ulong coeffSum = 0;
            Dictionary<AstIdx, ulong> constantPowers = new();
            List<AstIdx> others = new();

            foreach(var root in roots)
            {
                var code = ctx.GetOpcode(root);
                if(code == AstOp.Constant)
                {
                    coeffSum += ctx.GetConstantValue(root);
                }
                else if(code == AstOp.Symbol)
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
            if(op0 && !op1)
                return comeFirst;
            if(op1 && !op0)
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
            if(op0 == AstOp.Constant)
                return comeFirst;
            if(op1 == AstOp.Constant)
                return comeLast;

            // Sort symbols alphabetically
            if(op0 == AstOp.Symbol && op1 == AstOp.Symbol)
                return ctx.GetSymbolName(a).CompareTo(ctx.GetSymbolName(b));
            if(op0 == AstOp.Pow)
                return comeLast;
            if(op1 == AstOp.Pow)
                return comeFirst;
            return -1;
        }

        private AstIdx GetSubstitution(AstIdx id, Dictionary<AstIdx, AstIdx> substitutionMapping)
        {
            if(substitutionMapping.TryGetValue(id, out var existing))
                return existing;

            while (true)
            {
                var subst = ctx.Symbol($"subst{substCount}", ctx.GetWidth(id));
                substCount++;
                if(substitutionMapping.Values.Contains(subst))
                {
                    continue;
                }

                substitutionMapping.TryAdd(id, subst);
                return subst;
            }
        }

        private AstIdx TryUnmergeLinCombs(AstIdx withSubstitutions, Dictionary<AstIdx, AstIdx> substitutionMapping, ref bool isSemiLinear)
        {
            // We cannot rewrite substitutions as negations of one another if there is only one substitution.
            if(substitutionMapping.Count == 1)
                return withSubstitutions;

            var result = UnmergeDisjointParts(withSubstitutions, substitutionMapping, ref isSemiLinear);
            if(result != null)
                withSubstitutions = result.Value;

            var rewriteMapping = UnmergeNegatedParts(substitutionMapping);

            // Return if we cannot rewrite any substitutions as negations of one another.
            if(!rewriteMapping.Any())
                return withSubstitutions;

            withSubstitutions = BackSubstitute(ctx, withSubstitutions, rewriteMapping);
            return withSubstitutions;
        }

        private Dictionary<AstIdx, AstIdx> UnmergeNegatedParts(Dictionary<AstIdx, AstIdx> substitutionMapping)
        {
            var rewriteMapping = new Dictionary<AstIdx, AstIdx>();
            bool changed = true;
            while (changed)
            {
            start:
                changed = false;
                var clone = substitutionMapping.ToDictionary();
                foreach(var (ast, substVariable) in clone)
                {
                    var neg = ctx.Neg(ast);
                    neg = SimplifyViaRecursiveSiMBA(neg);

                    if(clone.TryGetValue(neg, out var otherSubst))
                    {
                        rewriteMapping.TryAdd(substVariable, ctx.Neg(otherSubst));
                        substitutionMapping.Remove(ast);
                        goto start;
                    }
                }
            }

            return rewriteMapping;
        }

        // We are looking for nonlinear MBAs of the form:
        // (-3689350793862841103*(RSI&(4040198467629586701 + 1099511628211*((5292288&RBX))))) + 
        // (-3689348594839584681*(RSI&(4040198467629586696+(1099511628211*(5292288&RBX))))) + 
        // (7378699388702425784*(RSI&(4040198467629586909+(1099511628211*(5292288&RBX)))))
        // , where the same semi-linear expression(minus the constant offset) is substituted in multiple terms.
        // We then try to decompose each substituted part into `known_ones | (shared_bits + 1099511628211*(5292288&RBX))`
        // , allowing us to reduce the number of substituted terms. This (a) unblurs the relationship between the expression, and (b) allows msimba to take advantage of the known bits.
        // TODO: Bail out when no semi-linear parts are found!
        private AstIdx? UnmergeDisjointParts(AstIdx withSubstitutions, Dictionary<AstIdx, AstIdx> substitutionMapping, ref bool isSemiLinear)
        {
            var list = substitutionMapping.ToList();
            var inputExpressions = list.Select(x => x.Key).ToList();
            var inputSubstVars = list.Select(x => x.Value).ToList();

            // We have a list of <substVar, expr>, where expression is an arbitary nonlinear expression.
            var parts = new List<(AstIdx idx, Dictionary<AstIdx, AstIdx> substitutions)>();

            var tempSubstMapping = new Dictionary<AstIdx, AstIdx>();
            var results = new List<AstIdx>();
            for (int i = 0; i < inputExpressions.Count; i++)
            {
                // Substitute all of the nonlinear parts for this expression
                // Here we share the list of substitutions 
                var expr = inputExpressions[i];
                bool isSl = false;
                var result = GetAstWithSubstitutions(expr, tempSubstMapping, ref isSemiLinear);
                results.Add(result);
            }
            // Invert the temp substitution mapping
            tempSubstMapping = tempSubstMapping.ToDictionary(x => x.Value, x => x.Key);

            var vars = results.SelectMany(x => ctx.CollectVariables(x)).Distinct().OrderBy(x => ctx.GetSymbolName(x)).ToList();
            if(vars.Count > 11)
                return null;

            // Compute a result vector for each expression
            Dictionary<ResultVectorKey, List<(int index, ulong constantOffset)>> vecToExpr = new();
            for (int i = 0; i < results.Count; i++)
            {
                var expr = results[i];
                var w = ctx.GetWidth(expr);
                var moduloMask = (ulong)ModuloReducer.GetMask(w);
                var numCombinations = (ulong)Math.Pow(2, vars.Count);

                var resultVec = LinearSimplifier.JitResultVector(ctx, ctx.GetWidth(expr), moduloMask, vars, expr, true, numCombinations);
                var constantOffset = LinearSimplifier.SubtractConstantOffset(moduloMask, resultVec, (int)numCombinations);

                var key = new ResultVectorKey(resultVec);
                vecToExpr.TryAdd(key, new());
                vecToExpr[key].Add((i, constantOffset));
            }

            Dictionary<AstIdx, AstIdx> varToNewSubstValue = new Dictionary<AstIdx, AstIdx>();
            foreach(var (key, members) in vecToExpr)
            {
                var temp = results[members.First().index];
                var w = ctx.GetWidth(temp);
                var moduloMask = (ulong)ModuloReducer.GetMask(w);
                var numCombinations = (ulong)Math.Pow(2, vars.Count);

                int vecIdx = 0;
                KnownBits kb = KnownBits.MakeConstant(0, w);
                var resultVector = key.resultVector;
                // Compute the known bits of the result vector
                // TODO:
                // (1) If a column of the truth table shares the same coefficient, we can compute knownbits for the entire column in parallel.
                // (2) Port to C++
                for (int bitIndex = 0; bitIndex < w; bitIndex++)
                {
                    for (ulong i = 0; i < numCombinations; i++)
                    {
                        var coeff = resultVector[vecIdx];
                        if(coeff == 0)
                        {
                            vecIdx++;
                            continue;
                        }

                        // Knownbits += coeff*(x&whatever)
                        ulong value = moduloMask & ~(1ul << bitIndex);
                        var curr = new KnownBits(w, value, 0);
                        var mul = KnownBits.Mul(KnownBits.MakeConstant(coeff, w), curr);
                        kb = KnownBits.Add(kb, mul);
                        vecIdx++;
                    }
                }

                // Compute the shared bits among the constant offset.
                var union = moduloMask;
                foreach(var (_, constantOffset) in members)
                    union &= constantOffset;

                // Update the constant offset to extract out the shared bits
                for (int i = 0; i < members.Count; i++)
                {
                    var member = members[i];
                    members[i] = (member.index, member.constantOffset & ~union);
                }

                // Verify that we can rewrite every linear combination to be in the form of sharedBits | (sharedSubst)
                kb = KnownBits.Add(kb, KnownBits.MakeConstant(union, w));
                if(members.Any(x => !CanFitConstantInUndemandedBits(kb, x.constantOffset, moduloMask)))
                    continue;

                // Replace each substituted var with a new substituted var | some constant offset.
                var newSubstVar = ctx.Symbol($"subst{substCount}", (byte)w);
                substCount++;
                for (int i = 0; i < members.Count; i++)
                {
                    var member = members[i];
                    var expr = ctx.Or(ctx.Constant(member.constantOffset, w), newSubstVar);
                    var inVar = inputSubstVars[member.index];
                    if(varToNewSubstValue.ContainsKey(inVar))
                        throw new InvalidOperationException($"Cannot share substituted parts!");

                    varToNewSubstValue[inVar] = expr;
                }

                var vecExpr = LinearSimplifier.Run(w, ctx, null, false, true, false, vars, null, resultVector); // TODO: ToArray
                vecExpr = ctx.Add(ctx.Constant(union, w), vecExpr);
                // Back substitute in the variables we temporarily substituted.
                vecExpr = BackSubstitute(ctx, vecExpr, tempSubstMapping);
                substitutionMapping.Remove(vecExpr);
                substitutionMapping.TryAdd(vecExpr, newSubstVar);
                isSemiLinear = true;
            }

            withSubstitutions = BackSubstitute(ctx, withSubstitutions, varToNewSubstValue);
            var newVars = ctx.CollectVariables(withSubstitutions).ToHashSet();
            foreach(var (expr, substVar) in substitutionMapping.ToList())
            {
                if(!newVars.Contains(substVar))
                    substitutionMapping.Remove(expr);
            }

            return withSubstitutions;
        }

        // Returns true if the c1+(c2&x) can be rewritten as c1|(c2&x)
        private bool CanFitConstantInUndemandedBits(KnownBits kb, ulong constant, ulong moduloMask)
        {
            if((kb.Ones & constant) != 0)
                return false;
            if((kb.UnknownBits & constant) != 0)
                return false;
            return true;
        }

        // MSiMBA is guaranteed to return a correct result if the input expression can be represented as a semi-linear MBA
        // For some instances of nonlinear MBA we can soundly and efficiently prove that MSiMBAs result is equivalent to the input expression.
        // Here are we doing exactly that: Running MSiMBA and returning it's result if we can prove the equivalence of the expressions.
        private unsafe AstIdx? SimplifyViaGuessAndProve(AstIdx withSubstitutions, Dictionary<AstIdx, AstIdx> substitutionMapping, ref bool isSemiLinear)
        {
            // If there are no substituted parts, we have a semi-linear MBA.
            if(substitutionMapping.Count == 0)
                return null;

            // Compute demanded bits for each variable
            // TODO: Keep track of which bits are demanded by the parent(withSubstitutions)
            Dictionary<AstIdx, ulong> varToDemandedBits = new();
            var cache = new HashSet<(AstIdx idx, ulong currDemanded)>();
            int totalDemanded = 0;
            foreach(var (expr, substVar) in substitutionMapping)
            {
                ComputeSymbolDemandedBits(expr, ModuloReducer.GetMask(ctx.GetWidth(expr)), varToDemandedBits, cache, ref totalDemanded);
                if(totalDemanded > 12)
                    break;
            }


            // Bail if there are too many demanded bits!
            if(totalDemanded > 12)
                return null;

            // Partition the MBA into semi-linear, unconstrained, and constrained parts.
            var (semilinearIdx, unconstrainedIdx, constrainedIdx) = PartitionConstrainedParts(withSubstitutions, substitutionMapping);

            // If there are no constrained or unconstrained parts then this is a semi-linear MBA.
            if(unconstrainedIdx == null && constrainedIdx == null)
                throw new InvalidOperationException($"Expected nonlinear expression!");

            // If we have no unconstrained parts, we can prove the equivalence of the entire expression.
            if(unconstrainedIdx == null)
                return SimplifyConstrained(withSubstitutions, substitutionMapping, varToDemandedBits);

            // If we have have no constrained parts, we can simplify the entire expression individually.
            if(constrainedIdx == null)
            {
                // Simplify the constrained parts.
                var withoutSubstitutions = BackSubstitute(ctx, unconstrainedIdx.Value, substitutionMapping.ToDictionary(x => x.Value, x => x.Key));
                var r = SimplifyUnconstrained(withoutSubstitutions, varToDemandedBits);
                if(r == null)
                    return null;
                if(semilinearIdx == null)
                    return r.Value;

                // If there are some semi-linear parts, combine and simplify.
                var sum = ctx.Add(semilinearIdx.Value, r.Value);
                var simplified = LinearSimplifier.Run(ctx.GetWidth(sum), ctx, sum, false, true);
                return simplified;
            }

            // Otherwise we have both constrained and unconstrained parts, which need to be simplified individually and composed back together.
            if(semilinearIdx != null)
                constrainedIdx = ctx.Add(semilinearIdx.Value, constrainedIdx.Value);

            // Simplify constrained parts.
            var constrainedSimpl = SimplifyConstrained(constrainedIdx.Value, substitutionMapping, varToDemandedBits);
            if(constrainedSimpl == null)
                return null;

            // Simplify unconstrained parts.
            var unconstrainedBackSub = BackSubstitute(ctx, unconstrainedIdx.Value, substitutionMapping.ToDictionary(x => x.Value, x => x.Key));
            var unconstrainedSimpl = SimplifyUnconstrained(unconstrainedBackSub, varToDemandedBits);
            if(unconstrainedSimpl == null)
                return null;

            // Compose and simplify
            var composed = ctx.Add(constrainedSimpl.Value, unconstrainedSimpl.Value);
            var simplComposed = LinearSimplifier.Run(ctx.GetWidth(composed), ctx, composed, false, true);
            return simplComposed;
        }

        // Partition the result vector into semi-linear, constrained, and unconstrained parts.
        private (AstIdx? semilinearIdx, AstIdx? unconstrainedIdx, AstIdx? constrainedIdx) PartitionConstrainedParts(AstIdx withSubstitutions, Dictionary<AstIdx, AstIdx> substitutionMapping)
        {
            // Construct a result vector for the linear part.
            var substVars = substitutionMapping.Values.ToList();
            IReadOnlyList<AstIdx> allVars = ctx.CollectVariables(withSubstitutions);
            var bitSize = ctx.GetWidth(withSubstitutions);
            var numCombinations = (ulong)Math.Pow(2, allVars.Count);
            var groupSizes = LinearSimplifier.GetGroupSizes(allVars.Count);
            var moduloMask = ModuloReducer.GetMask(bitSize);
            var resultVec = LinearSimplifier.JitResultVector(ctx, bitSize, moduloMask, allVars, withSubstitutions, multiBit: true, numCombinations);
            // Subtract the constant offset
            var constantOffset = LinearSimplifier.SubtractConstantOffset(moduloMask, resultVec, (int)numCombinations);

            // Get all possible conjunctions of variables.
            var variableCombinations = LinearSimplifier.GetVariableCombinations(allVars.Count);
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var myMask = variableCombinations[i];
                var myIndex = LinearSimplifier.GetGroupSizeIndex(groupSizes, myMask);
                combToMaskAndIdx.Add((myMask, (int)myIndex));
            }

            // Change result vector basis to algebraic normal form
            var (_, linearCombinations) = GetAnf(bitSize, allVars, groupSizes, resultVec, true);

            // Compute a bitmask containing all substituted vars
            ulong substVarMask = 0;
            for (int i = 0; i < allVars.Count; i++)
            {
                if(!substVars.Contains(allVars[i]))
                    continue;

                substVarMask |= (1ul << (ushort)i);
            }

            List<AstIdx> semiLinearParts = new();
            if(constantOffset != 0)
                semiLinearParts.Add(ctx.Constant(constantOffset, bitSize));
            List<AstIdx> unconstrainedParts = new();
            List<AstIdx> constrainedParts = new();

            // Decompose result vector into semi-linear, unconstrained, and constrained parts.
            // Upcast variables as necessary!
            allVars = LinearSimplifier.CastVariables(ctx, allVars, bitSize);
            int resultVecIdx = 0;
            for (int i = 0; i < linearCombinations.Count; i++)
            {
                foreach(var (coeff, bitMask) in linearCombinations[i])
                {
                    if(coeff == 0)
                        goto skip;

                    // If the term only contains normal variables, its semi-linear.
                    var varComb = variableCombinations[i];
                    if((varComb & substVarMask) == 0)
                    {
                        semiLinearParts.Add(LinearSimplifier.ConjunctionFromVarMask(ctx, allVars, coeff, varComb, bitMask));
                        goto skip;
                    }

                    // If the term only contains substituted variables, it's unconstrained.
                    if((varComb & ~substVarMask) == 0)
                    {
                        unconstrainedParts.Add(LinearSimplifier.ConjunctionFromVarMask(ctx, allVars, coeff, varComb, bitMask));
                        goto skip;
                    }

                    // Otherwise we have some mix of variables and substituted parts.
                    // This is constrained!
                    constrainedParts.Add(LinearSimplifier.ConjunctionFromVarMask(ctx, allVars, coeff, varComb, bitMask));

                skip:
                    resultVecIdx++;
                }
            }

            AstIdx? semilinearIdx = semiLinearParts.Any() ? ctx.Add(semiLinearParts) : null;
            AstIdx? unconstrainedIdx = unconstrainedParts.Any() ? ctx.Add(unconstrainedParts) : null;
            AstIdx? constrainedIdx = constrainedParts.Any() ? ctx.Add(constrainedParts) : null;
            return (semilinearIdx, unconstrainedIdx, constrainedIdx);
        }

        // TODO: Refactor out!
        private static (ulong[], List<List<(ulong coeff, ulong bitMask)>>) GetAnf(uint width, IReadOnlyList<AstIdx> variables, List<int> groupSizes, ulong[] resultVector, bool multiBit)
        {
            // Get all combinations of variables.
            var moduloMask = ModuloReducer.GetMask(width);
            var numCombinations = (ulong)Math.Pow(2, variables.Count);
            var variableCombinations = LinearSimplifier.GetVariableCombinations(variables.Count);

            // Linear combination, where the index can be seen as an index into `variableCombinations`,
            // and the element at that index is a list of terms operating over that boolean combination.
            // Term = coeff*(bitMask&basisExpression).
            var linearCombinations = new List<List<(ulong coeff, ulong bitMask)>>(variableCombinations.Length);
            for (int i = 0; i < variableCombinations.Length; i++)
                linearCombinations.Add(new((int)width));

            // Keep track of which variables are demanded by which combination,
            // as well as which result vector idx corresponds to which combination.
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var myMask = variableCombinations[i];
                var myIndex = LinearSimplifier.GetGroupSizeIndex(groupSizes, myMask);
                combToMaskAndIdx.Add((myMask, (int)myIndex));
            }

            bool allZeroes = true;
            var varCount = variables.Count;
            bool onlyOneVar = varCount == 1;
            int vecWidth = (int)(varCount == 1 ? 1 : 2u << (ushort)(varCount - 1));

            unsafe
            {
                fixed (ulong* ptr = &resultVector[0])
                {
                    for (ushort bitIndex = 0; bitIndex < LinearSimplifier.GetNumBitIterations(multiBit, width); bitIndex++)
                    {
                        // If multi-bit simba is enabled, we need to take our base expression
                        // and isolate only the bit at the current bit index.
                        var maskForIndex = multiBit ? (ulong)1 << bitIndex : moduloMask;
                        // Offset the result vector index such that we are fetching entries for the current bit index.
                        var offset = bitIndex * numCombinations;
                        for (int i = 0; i < variableCombinations.Length; i++)
                        {
                            // Fetch the result vector index for this conjunction.
                            // If the coefficient is zero, we can skip it.
                            var comb = variableCombinations[i];
                            var (trueMask, index) = combToMaskAndIdx[i];
                            var coeff = ptr[(int)offset + index];
                            if(coeff == 0)
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

        private unsafe AstIdx? SimplifyConstrained(AstIdx withSubstitutions, Dictionary<AstIdx, AstIdx> substitutionMapping, Dictionary<AstIdx, ulong> varToDemandedBits)
        {
            // Compute a result vector for the original expression
            var withoutSubstitutions = BackSubstitute(ctx, withSubstitutions, substitutionMapping.ToDictionary(x => x.Value, x => x.Key));
            var w = ctx.GetWidth(withoutSubstitutions);
            var inputVars = ctx.CollectVariables(withoutSubstitutions);
            var originalResultVec = LinearSimplifier.JitResultVector(ctx, w, ModuloReducer.GetMask(w), inputVars, withoutSubstitutions, true, (ulong)Math.Pow(2, inputVars.Count));

            // Jit the function with substituted parts.
            var exprToSubstVar = substitutionMapping.OrderBy(x => ctx.GetAstString(x.Value)).ToList();
            var allVars = inputVars.Concat(exprToSubstVar.Select(x => x.Value)).ToList(); // Sort them....
            var pagePtr = JitUtils.AllocateExecutablePage(4096);
            new Amd64OptimizingJit(ctx).Compile(withSubstitutions, allVars, pagePtr, false);
            var jittedWithSubstitutions = (delegate* unmanaged[SuppressGCTransition]<ulong*, ulong>)pagePtr;

            // Return null if the expressions are not provably equivalent
            var demandedVars = varToDemandedBits.OrderBy(x => ctx.GetSymbolName(x.Key)).Select(x => (x.Key, x.Value)).ToList();
            if(!IsConstrainedExpressionEquivalent(w, inputVars, demandedVars, exprToSubstVar, jittedWithSubstitutions, originalResultVec))
            {
                JitUtils.FreeExecutablePage(pagePtr);
                return null;
            }

            // Otherwise they are equivalent. Return MSiMBA's result!
            JitUtils.FreeExecutablePage(pagePtr);
            var expected = LinearSimplifier.Run(w, ctx, null, false, true, false, inputVars, null, originalResultVec);
            return expected;
        }

        // Returns true if two expressions are guaranteed to be equivalent
        private unsafe bool IsConstrainedExpressionEquivalent(uint width, List<AstIdx> inputVars, List<(AstIdx demandedVar, ulong demandedMask)> demandedVars, List<KeyValuePair<AstIdx, AstIdx>> exprToSubstVar, delegate* unmanaged[SuppressGCTransition]<ulong*, ulong> jittedWithSubstitutions, ulong[] originalResultVec)
        {
            int totalDemanded = demandedVars.Sum(x => BitOperations.PopCount(x.demandedMask));

            // Compute a full result vector in (2^t*bitWidth)*(2^demandedSymbolBits) time
            // Proof for why this works:
            // - Constrained parts are always a part of a bitwise term.
            // - Substituted parts evaluate to constants, which get treated as semi-linear constants(inside bitwise terms)
            var numCombinations = (ulong)Math.Pow(2, inputVars.Count);
            var vDemandedMap = new Dictionary<AstIdx, ulong>();
            int vecIdx = 0;
            var vArray = new ulong[inputVars.Count + exprToSubstVar.Count];
            for (ushort bitIndex = 0; bitIndex < width; bitIndex++)
            {
                for (ulong i = 0; i < numCombinations; i++)
                {
                    // Set the value to zeroes or ones
                    for (int vIdx = 0; vIdx < inputVars.Count; vIdx++)
                    {
                        var value = ((i >> (ushort)vIdx) & 1) == 0 ? 0ul : 1ul;
                        value <<= bitIndex;
                        vArray[vIdx] = value;
                    }

                    // Enumerate through all 2^t combinations of input values for the demanded variable bits,
                    // evaluate the substituted parts on these input combinations, plug evaluated substituted parts into `withSubstitutions` expression,
                    // and compare their result vectors.
                    var numDemandedCombinations = (ulong)Math.Pow(2, totalDemanded);
                    for (ulong j = 0; j < numDemandedCombinations; j++)
                    {
                        // Choose one of 2^t input combinations for the demanded variable bits in the substitued parts
                        vDemandedMap.Clear();
                        int currVarIdx = 0;
                        ulong currDemandedVarMask = demandedVars[currVarIdx].demandedMask;
                        for (int vIdx = 0; vIdx < (int)totalDemanded; vIdx++)
                        {
                            // If we've chosen values for all bits in this variable, move onto the next one.
                            if(currDemandedVarMask == 0)
                            {
                                currVarIdx += 1;
                                currDemandedVarMask = demandedVars[currVarIdx].demandedMask;
                            }

                            // Get the index of the demanded variable bit we are setting
                            var vBitIdx = (ushort)BitOperations.TrailingZeroCount(currDemandedVarMask);

                            // Compute the value for this bit
                            var value = ((j >> (ushort)vIdx) & 1) == 0 ? 0ul : 1ul;
                            value <<= vBitIdx;

                            // Set the variable bit's value
                            vDemandedMap.TryAdd(demandedVars[currVarIdx].demandedVar, 0);
                            vDemandedMap[demandedVars[currVarIdx].demandedVar] |= value;

                            // Mark this bit as decided
                            currDemandedVarMask &= ~(1ul << vBitIdx);
                        }

                        // Evaluate each substituted part on this input combination
                        for (int substIdx = 0; substIdx < exprToSubstVar.Count; substIdx++)
                        {
                            var eval = SimpleAstEvaluator.Evaluate(ctx, exprToSubstVar[substIdx].Key, vDemandedMap);
                            vArray[inputVars.Count + substIdx] = eval;
                        }

                        // Evaluate withSubstitutions on f(x, y, z, subst0, subst1, subst...) and compare result vectors.
                        fixed (ulong* vPtr = &vArray[0])
                        {
                            var curr = jittedWithSubstitutions(vPtr) >> bitIndex;
                            if(curr != originalResultVec[vecIdx])
                                return false;
                        }
                    }

                    vecIdx += 1;
                }
            }

            return true;
        }

        private unsafe AstIdx? SimplifyUnconstrained(AstIdx withoutSubstitutions, Dictionary<AstIdx, ulong> varToDemandedBits)
        {
            List<(AstIdx demandedVar, ulong demandedMask)> demandedVars = varToDemandedBits.OrderBy(x => ctx.GetSymbolName(x.Key)).Select(x => (x.Key, x.Value)).ToList();

            // Compute a result vector for the nonlinear expression.
            var w = ctx.GetWidth(withoutSubstitutions);
            var inputVars = ctx.CollectVariables(withoutSubstitutions);
            Debug.Assert(inputVars.Count == demandedVars.Count && inputVars.SequenceEqual(demandedVars.Select(x => x.demandedVar)));
            var expectedExpr = LinearSimplifier.Run(w, ctx, withoutSubstitutions, false, true, false, inputVars);

            // Jit the input expression
            var pagePtr1 = JitUtils.AllocateExecutablePage(4096);
            new Amd64OptimizingJit(ctx).Compile(withoutSubstitutions, inputVars, pagePtr1, false);
            var jittedBefore = (delegate* unmanaged[SuppressGCTransition]<ulong*, ulong>)pagePtr1;

            // Jit the output expression
            var pagePtr2 = JitUtils.AllocateExecutablePage(4096);
            new Amd64OptimizingJit(ctx).Compile(expectedExpr, inputVars, pagePtr2, false);
            var jittedAfter = (delegate* unmanaged[SuppressGCTransition]<ulong*, ulong>)pagePtr2;

            // Prove that they are equivalent for all possible input combinations
            int totalDemanded = demandedVars.Sum(x => BitOperations.PopCount(x.demandedMask));
            var numDemandedCombinations = (ulong)Math.Pow(2, totalDemanded);
            var vArray = new ulong[inputVars.Count];
            for (ulong combIdx = 0; combIdx < numDemandedCombinations; combIdx++)
            {
                // Set all variable values to zero.
                for (int i = 0; i < vArray.Length; i++)
                    vArray[i] = 0;

                int currVarIdx = 0;
                ulong currDemandedVarMask = demandedVars[currVarIdx].demandedMask;
                for (int vIdx = 0; vIdx < (int)totalDemanded; vIdx++)
                {
                    // If we've chosen values for all bits in this variable, move onto the next one.
                    if(currDemandedVarMask == 0)
                    {
                        currVarIdx += 1;
                        currDemandedVarMask = demandedVars[currVarIdx].demandedMask;
                    }

                    // Get the index of the demanded variable bit we are setting
                    var vBitIdx = (ushort)BitOperations.TrailingZeroCount(currDemandedVarMask);

                    // Compute the value for this bit
                    var value = ((combIdx >> (ushort)vIdx) & 1) == 0 ? 0ul : 1ul;
                    value <<= vBitIdx;

                    // Set the variable bit's value
                    vArray[currVarIdx] |= value;
                    // Mark this bit as decided
                    currDemandedVarMask &= ~(1ul << vBitIdx);
                }

                fixed (ulong* vPtr = &vArray[0])
                {
                    var op1 = jittedBefore(vPtr);
                    var op2 = jittedAfter(vPtr);
                    if(op1 != op2)
                    {
                        JitUtils.FreeExecutablePage(pagePtr1);
                        JitUtils.FreeExecutablePage(pagePtr2);
                        return null;
                    }
                }
            }

            JitUtils.FreeExecutablePage(pagePtr1);
            JitUtils.FreeExecutablePage(pagePtr2);
            return expectedExpr;
        }

        // TODO: Cache results to avoid exponentially visiting shared nodes
        private void ComputeSymbolDemandedBits(AstIdx idx, ulong currDemanded, Dictionary<AstIdx, ulong> symbolDemandedBits, HashSet<(AstIdx idx, ulong currDemanded)> seen, ref int totalDemanded)
        {
            if(totalDemanded > 12)
                return;
            if(!seen.Add((idx, currDemanded)))
                return;

            totalDemanded += 1;

            var op0 = (ulong demanded, ref int totalDemanded) => ComputeSymbolDemandedBits(ctx.GetOp0(idx), demanded, symbolDemandedBits, seen, ref totalDemanded);
            var op1 = (ulong demanded, ref int totalDemanded) => ComputeSymbolDemandedBits(ctx.GetOp1(idx), demanded, symbolDemandedBits, seen, ref totalDemanded);

            var opc = ctx.GetOpcode(idx);
            switch (opc)
            {
                // If we have a symbol, union the set of demanded bits
                case AstOp.Symbol:
                    //symbolDemandedBits.TryAdd(idx, 0);
                    symbolDemandedBits.TryGetValue(idx, out var oldDemanded);
                    var newDemanded = oldDemanded | currDemanded;
                    symbolDemandedBits[idx] = newDemanded;
                    totalDemanded += BitOperations.PopCount(newDemanded & ~oldDemanded);
                    
                    break;
                // If we have a constant, there is nothing to do.
                case AstOp.Constant:
                    break;
                // TODO: If the multiplication can be rewritten as a constant, we can get more precision by ignoring bits that get shifted out?
                // Also check if mul can be rewritten as shl?
                // For addition by a constant we can also get more precision
                case AstOp.Add:
                case AstOp.Mul:
                case AstOp.Pow:
                    // If we have addition/multiplication, we only care about bits at and below the highest set bit.
                    var demandedWidth = 64 - (uint)BitOperations.LeadingZeroCount(currDemanded);
                    currDemanded = ModuloReducer.GetMask(demandedWidth);

                    op0(currDemanded, ref totalDemanded);
                    op1(currDemanded, ref totalDemanded);
                    break;
                case AstOp.Lshr:
                    var shiftBy = ctx.GetOp1(idx);
                    var shiftByConstant = ctx.TryGetConstantValue(shiftBy);
                    if(shiftByConstant == null)
                    {
                        op0(currDemanded, ref totalDemanded);
                        op1(currDemanded, ref totalDemanded);
                        break;
                    }

                    // If we know the value we are shifting by, we can truncate the demanded bits.
                    op0(currDemanded >> (ushort)shiftByConstant.Value, ref totalDemanded);
                    op1(currDemanded, ref totalDemanded);
                    break;

                case AstOp.And:
                    {
                        // If we have a&b, demandedbits(a) does not include any known zero bits from b. Works both ways.
                        var op0Demanded = ~ctx.GetKnownBits(ctx.GetOp1(idx)).Zeroes & currDemanded;
                        var op1Demanded = ~ctx.GetKnownBits(ctx.GetOp0(idx)).Zeroes & currDemanded;
                        op0(op0Demanded, ref totalDemanded);
                        op1(op1Demanded, ref totalDemanded);
                        break;
                    }

                case AstOp.Or:
                    {
                        // If we have a|b, demandedbits(a) does not include any known one bits from b. Works both ways.
                        var op0Demanded = ~ctx.GetKnownBits(ctx.GetOp1(idx)).Ones & currDemanded;
                        var op1Demanded = ~ctx.GetKnownBits(ctx.GetOp0(idx)).Ones & currDemanded;
                        op0(op0Demanded, ref totalDemanded);
                        op1(op1Demanded, ref totalDemanded);
                        break;
                    }
                // TODO: We can gain some precision by exploiting XOR known bits.
                case AstOp.Xor:
                    op0(currDemanded, ref totalDemanded);
                    op1(currDemanded, ref totalDemanded);
                    break;
                // TODO: Treat negation as x^-1, then use XOR transfer function
                case AstOp.Neg:
                    op0(currDemanded, ref totalDemanded);
                    break;
                case AstOp.Trunc:
                    currDemanded &= ModuloReducer.GetMask(ctx.GetWidth(idx));
                    op0(currDemanded, ref totalDemanded);
                    break;
                case AstOp.Zext:
                    op0(currDemanded & ModuloReducer.GetMask(ctx.GetWidth(ctx.GetOp0(idx))), ref totalDemanded);
                    break;
                default:
                    throw new InvalidOperationException($"Cannot compute demanded bits for {opc}");
            }
        }

        private AstIdx? TrySimplifyMixedPolynomialParts(AstIdx id, Dictionary<AstIdx, AstIdx> substMapping, Dictionary<AstIdx, AstIdx> inverseSubstMapping, List<AstIdx> varList)
        {
            // Back substitute in the (possibly) polynomial parts
            var newId = BackSubstitute(ctx, id, inverseSubstMapping);

            // Decompose each term into structured polynomial parts
            var terms = GetRootTerms(ctx, newId);
            List<PolynomialParts> polyParts = terms.Select(x => GetPolynomialParts(ctx, x)).ToList();
            // Remove anything we cannot handle.
            var banned = polyParts.Where(x => x.Others.Any()).ToList();
            polyParts.RemoveAll(x => x.Others.Any());


            var result = SimplifyParts(ctx.GetWidth(id), polyParts);
            if(result == null)
                return null;

            // Add back any banned parts.
            if(banned.Any())
            {
                var sum = ctx.Add(banned.Select(x => GetAstForPolynomialParts(x)));
                result = ctx.Add(result.Value, sum);
            }

            // Do a full back substitution again.
            result = BackSubstitute(ctx, result.Value, inverseSubstMapping);

            // Bail out if this resulted in a worse result.
            var cost1 = ctx.GetCost(result.Value);
            var cost2 = ctx.GetCost(newId);
            if(cost1 > cost2)
            {
                return null;
            }

            return result;
        }

        private List<PolynomialParts> UnmergePolynomialParts(Dictionary<AstIdx, AstIdx> substitutionMapping, List<PolynomialParts> parts)
        {
            // Skip if there is only one substituted part.
            if(substitutionMapping.Count <= 1)
                return parts;

            // Try to rewrite substituted parts as negations of one another. Exit early if this fails.
            var rewriteMapping = UnmergeNegatedParts(substitutionMapping);
            if(rewriteMapping.Count == 0)
                return parts;

            var output = new List<PolynomialParts>();
            foreach(var part in parts)
            {
                var outPowers = new Dictionary<AstIdx, ulong>();
                foreach(var (factor, degree) in part.ConstantPowers)
                {
                    var unmerged = BackSubstitute(ctx, factor, rewriteMapping);
                    outPowers.TryAdd(unmerged, 0);
                    outPowers[unmerged] += degree;
                }

                output.Add(new PolynomialParts(part.width, part.coeffSum, outPowers, part.Others));
            }

            return output;
        }

        // Rewrite factors of polynomials as linear MBAs(with substitution) with a canonical basis, expand & reduce, then back substitute.
        private AstIdx? SimplifyParts(uint bitSize, IReadOnlyList<PolynomialParts> polyParts, bool dbg = false)
        {
            var substMapping = new Dictionary<AstIdx, AstIdx>();

            // Rewrite as a sum of polynomial parts, where the factors are linear MBAs with substitution of nonlinear parts.
            var bannedParts = new List<PolynomialParts>();
            List<PolynomialParts> partsWithSubstitutions = new();
            foreach(var polyPart in polyParts)
            {
                bool isSemiLinear = false;
                Dictionary<AstIdx, ulong> powers = new();
                foreach(var factor in polyPart.ConstantPowers)
                {
                    var withSubstitutions = GetAstWithSubstitutions(factor.Key, substMapping, ref isSemiLinear);
                    powers.TryAdd(withSubstitutions, 0);
                    powers[withSubstitutions] += factor.Value;
                }

                // TODO: Handle the semi-linear case.
                if(isSemiLinear)
                {
                    bannedParts.Add(polyPart);
                    continue;
                }

                partsWithSubstitutions.Add(new PolynomialParts(polyPart.width, polyPart.coeffSum, powers, polyPart.Others));
            }

            // Unmerge polynomial parts that were substituted.
            partsWithSubstitutions = UnmergePolynomialParts(substMapping, partsWithSubstitutions);

            // Collect all variables.
            var withVars = partsWithSubstitutions.SelectMany(x => x.ConstantPowers.Keys);
            var varSet = new List<AstIdx>();
            if(withVars.Any())
                varSet = ctx.CollectVariables(ctx.Add(withVars));

            IReadOnlyList<AstIdx> allVars = varSet.OrderBy(x => ctx.GetSymbolName(x)).ToList();
            var numCombinations = (ulong)Math.Pow(2, allVars.Count);
            var groupSizes = LinearSimplifier.GetGroupSizes(allVars.Count);

            // Get all possible conjunctions of variables.
            var variableCombinations = LinearSimplifier.GetVariableCombinations(allVars.Count);
            List<(ulong trueMask, int resultVecIdx)> combToMaskAndIdx = new();
            for (int i = 0; i < variableCombinations.Length; i++)
            {
                var myMask = variableCombinations[i];
                var myIndex = LinearSimplifier.GetGroupSizeIndex(groupSizes, myMask);
                combToMaskAndIdx.Add((myMask, (int)myIndex));
            }

            // Rewrite each polynomial using the basis of the SiMBA paper.
            // TODO: Extend to the semi-linear case.
            var moduloMask = (ulong)ModuloReducer.GetMask(bitSize);
            Dictionary<ulong, AstIdx> basisSubstitutions = new();
            List<AstIdx> polys = new();
            foreach(var polyPart in partsWithSubstitutions)
            {
                List<AstIdx> factors = new();
                ulong size = 1;
                foreach(var (factor, degree) in polyPart.ConstantPowers)
                {
                    // Construct a result vector for the linear part.
                    var resultVec = LinearSimplifier.JitResultVector(ctx, bitSize, moduloMask, allVars, factor, multiBit: false, numCombinations);

                    // Change to the basis referenced in the SiMBA paper. It's just nicer to work with here IMO.
                    var anfVector = new ulong[resultVec.Length];
                    MixedPolynomialSimplifier.GetAnfVector(bitSize, allVars, variableCombinations, combToMaskAndIdx, resultVec, anfVector);

                    // Count the number of non zero elements.
                    ulong numNonZeroes = 0;
                    for (int i = 0; i < anfVector.Length; i++)
                    {
                        // Skip zero elements.
                        var coeff = anfVector[i];
                        if(coeff == 0)
                            continue;
                        numNonZeroes++;
                    }

                    // Calculate the max possible size of the resulting expression when multiplied out.
                    for (ulong i = 0; i < degree; i++)
                    {
                        size = SaturatingMul(size, numNonZeroes);
                    }

                    List<AstIdx> terms = new();
                    for (int i = 0; i < anfVector.Length; i++)
                    {
                        // Skip zero elements.
                        var coeff = anfVector[i];
                        if(coeff == 0)
                            continue;

                        // When the basis element corresponds to the constant offset, we want to make the base bitwise expression be `1`.
                        // Otherwise we just substitute it with a variable.
                        AstIdx basis = ctx.Constant(1, (byte)bitSize);
                        if(i != 0)
                        {
                            if(!basisSubstitutions.TryGetValue((ulong)i, out basis))
                            {
                                basis = ctx.Symbol($"basis{i}", (byte)bitSize);
                                basisSubstitutions.Add((ulong)i, basis);
                            }
                        }

                        var term = ctx.Mul(ctx.Constant(coeff, (byte)bitSize), basis);
                        terms.Add(term);
                    }

                    // Add this as a factor.
                    if(terms.Count == 0)
                        terms.Add(ctx.Constant(0, (byte)bitSize));
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
                if(factors.Any())
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

            // If there were no polynomial parts we could expand, return null.
            if(!polys.Any())
                return null;

            // Reduce the polynomial parts.
            var linComb = ctx.Add(polys);
            var reduced = ExpandReduce(linComb, false);
            // Add back banned parts
            if(bannedParts.Any())
            {
                var sum = ctx.Add(bannedParts.Select(x => GetAstForPolynomialParts(x)));
                reduced = ctx.Add(reduced, sum);
            }

            var invBases = basisSubstitutions.ToDictionary(x => x.Value, x => LinearSimplifier.ConjunctionFromVarMask(ctx, allVars, 1, x.Key));
            var backSub = BackSubstitute(ctx, reduced, invBases);
            backSub = BackSubstitute(ctx, backSub, substMapping.ToDictionary(x => x.Value, x => x.Key));
            return backSub;
        }

        private ulong SaturatingMul(ulong a, ulong b)
        {
            var value = (UInt128)a * (UInt128)b;
            if(value > ulong.MaxValue)
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
                if(opcode == AstOp.Add)
                {
                    toVisit.Push(ctx.GetOp0(term));
                    toVisit.Push(ctx.GetOp1(term));
                }

                // If we have coeff*(x+y) and coeff is a constant, rewrite as coeff*x + coeff*y.
                // If coeff is not a constant then we do not apply it - it would yield exponential growth in the worst case.
                // TODO: Handle polynomial expansion more uniformly.
                else if(opcode == AstOp.Mul && ctx.IsConstant(ctx.GetOp0(term)))
                {
                    var coeff = ctx.GetOp0(term);
                    var other = ctx.GetOp1(term);
                    if(ctx.IsAdd(other))
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
                if(opcode == AstOp.Mul)
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
            foreach(var term in terms)
            {
                var asConstant = ctx.TryGetConstantValue(term);
                if(asConstant != null)
                {
                    coeff *= asConstant.Value;
                }

                else
                {
                    newTerms.Add(term);
                }
            }

            if(coeff != null)
                newTerms.Insert(0, ctx.Constant(coeff, ctx.GetWidth(id)));

            return newTerms;
        }

        // Try to reduce the polynomial parts of an expression using the polynomial reduction algorithm.
        private AstIdx? ReducePolynomials(IReadOnlyList<AstIdx> terms, IReadOnlyDictionary<AstIdx, AstIdx> substMapping, IReadOnlyDictionary<AstIdx, AstIdx> inverseSubstMapping)
        {
            //if (terms.Count >= 64)
            //    Debugger.Break();
            // Try to decompose into high degree polynomials parts.
            List<PolynomialParts> polyTerms = new();
            List<AstIdx> other = new();
            foreach(var term in terms)
            {
                // Typically this is going to be a multiplication(coefficient over substituted variable), or whole substituted variable.
                // TODO: Handle negation.
                var opcode = ctx.GetOpcode(term);
                if(opcode == AstOp.Constant)
                {
                    polyTerms.Add(new PolynomialParts(ctx.GetWidth(term), ctx.GetConstantValue(term), new(), new()));
                    continue;
                }

                if(opcode != AstOp.Mul && opcode != AstOp.Symbol)
                    goto skip;

                // Search for coeff*subst
                if(opcode == AstOp.Mul)
                {
                    // If multiplication, we are looking for coeff*(subst), where coeff is a constant.
                    var coeff = ctx.GetOp0(term);
                    if(!ctx.IsConstant(coeff))
                        goto skip;

                    // Look for a substituted variable on the rhs of the multiplication.
                    var rhs = ctx.GetOp1(term);

                    if (IsSubstitutedPolynomialSymbol(rhs, inverseSubstMapping))
                    {

                        // We found a polynomial part, add it to the list.
                        var invSubst = inverseSubstMapping[rhs];
                        polyTerms.Add(GetPolynomialParts(ctx, ctx.Mul(coeff, invSubst)));
                        continue;
                    }

                    // Otherwise its a symbol
                    if (!ctx.IsSymbol(rhs))
                        goto skip;
                    polyTerms.Add(GetPolynomialParts(ctx, term));
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
            if(!polyTerms.Any())
                return null;

            // Now we have a list of polynomial parts, we want to try to simplify them.
            var uniqueBases = new Dictionary<AstIdx, ulong>();
            foreach(var poly in polyTerms)
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
            if(uniqueBases.Count > 3)
                return null;

            // Compute the dense vector size as a heuristic.
            ulong vecSize = 1;
            foreach(var degree in uniqueBases.Values)
                vecSize = SaturatingMul(vecSize, degree);

            // If the dense vector size would be greater than 64**3, we bail out.
            // In those cases, we may consider implementing variable partitioning and simplifying each partition separately.
            if(vecSize > 64 * 64 * 64)
                return null;

            // For now we only support polynomials up to degree 255, although this is a somewhat arbitrary limit.
            ulong limit = 254;
            var maxDeg = uniqueBases.MaxBy(x => x.Value).Value;
            if(maxDeg > limit)
                throw new InvalidOperationException($"Polynomial has degree {maxDeg} which is greater than the limit {limit}");

            // Otherwise we can carry on and simplify.
            var width = ctx.GetWidth(terms.First());
            var sparsePoly = new SparsePolynomial(uniqueBases.Count, width);

            // Sort the bases alphabetically.
            var orderedVars = uniqueBases.Keys.ToList();
            orderedVars.Sort((x, y) => { return VarsFirst(ctx, x, y); });

            // Fill in the sparse polynomial data structure.
            foreach(var poly in polyTerms)
            {
                var coeff = poly.coeffSum;

                var constPowers = poly.ConstantPowers;
                var degrees = new byte[orderedVars.Count];
                for (int varIdx = 0; varIdx < orderedVars.Count; varIdx++)
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

            if (terms.Count >= 63 || sparsePoly.ToString() == "64 + 224*x + 64*x*x + 212*x*x*x*x*x + 205*x*x*x*x*x*x*x")
            {
                PolyInverter.InterpolateExample(sparsePoly);
                Debugger.Break();
            }

            else
            {
                return null;
            }

                // Reduce.


                var simplified = PolynomialReducer.Reduce(sparsePoly);

            // The polynomial reduction algorithm guarantees a minimal degree result, but it's often not the most simple result.
            // E.g. "x**10" becomes "96*x0 + 40*x0**2 + 84*x0**3 + 210*x0**4 + 161*x0**5 + 171*x0**6 + 42*x0**7 + 220*x0**8 + 1*x0**9" on 8 bits.
            // In the case of a single term solution, we reject the result if it is more complex.
            if(polyTerms.Count == 1 && simplified.coeffs.Count(x => x.Value != 0) > 1)
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
                if(coeff == 0)
                    continue;

                List<AstIdx> factors = new();
                factors.Add(ctx.Constant(coeff, width));
                for (int i = 0; i < orderedVars.Count; i++)
                {
                    var deg = monom.GetVarDeg(i);
                    if(deg == 0)
                    {
                        factors.Add(ctx.Constant(1, width));
                        continue;
                    }

                    var variable = orderedVars[i];
                    if(deg == 1)
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
            if(newTerms.Count == 0)
                newTerms.Add(ctx.Constant(0, width));

            var result = ctx.Add(newTerms);
            // Constant fold.
            result = ctx.RecursiveSimplify(result);
            return result;
        }

        private bool IsSubstitutedPolynomialSymbol(AstIdx id, IReadOnlyDictionary<AstIdx, AstIdx> inverseSubstMapping)
        {
            if(!ctx.IsSymbol(id))
                return false;

            // Make sure the variable is a substituted part
            if(!inverseSubstMapping.TryGetValue(id, out var substituted))
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
                if(!ctx.IsConstant(rhs))
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
                    if(degree == 0)
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
            // If we have no terms then we have a zero.
            if(terms.Count == 0)
                terms.Add(ctx.Constant(0, width));
            var sum = ctx.Add(terms);

            // Back substitute the substitute variables.
            var inverseMapping = substMapping.ToDictionary(x => x.Value, x => x.Key);
            sum = BackSubstitute(ctx, sum, inverseMapping);

            // Try to simplify using the general simplifier.
            sum = ctx.RecursiveSimplify(sum);
            sum = SimplifyViaRecursiveSiMBA(sum, polySimplify);

            // Reject solution if it is more complex.
            if(ctx.GetCost(sum) > ctx.GetCost(id))
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

            switch (opcode)
            {
                case AstOp.Mul:
                    var factors = GetRootMultiplications(ctx, id);
                    var facPolys = factors.Select(x => TryExpand(x, substMapping, false)).ToList();
                    var product = IntermediatePoly.Mul(ctx, facPolys);
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
                    if(raisedTo == null)
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
            foreach(var monom in poly.coeffs.Keys)
            {
                foreach(var (basis, degree) in monom.varDegrees)
                {
                    uniqueBases.TryAdd(basis, 0);
                    var oldDegree = uniqueBases[basis];
                    if(degree > oldDegree)
                        uniqueBases[basis] = degree;
                }
            }

            // For now we only support up to 8 variables. Note that in practice this limit could be increased.
            if(uniqueBases.Count > 8)
                return poly;

            // Place a hard limit on the max degree.
            ulong limit = 254;
            if(uniqueBases.Any(x => x.Value > limit))
                return poly;

            ulong matrixSize = 1;
            foreach(var deg in uniqueBases.Keys)
            {
                // Bail out if the result would be too large.
                UInt128 result = matrixSize * deg;
                if(result > (UInt128)(64 * 64 * 64))
                    return poly;

                matrixSize = SaturatingMul(matrixSize, deg);
                matrixSize &= poly.moduloMask;
            }

            // Place a limit on the matrix size.
            if(matrixSize > (ulong)(64 * 64 * 64))
                return poly;

            var width = poly.bitWidth;
            var sparsePoly = new SparsePolynomial(uniqueBases.Count, (byte)width);

            // Sort the bases alphabetically.
            var orderedVars = uniqueBases.Keys.ToList();
            orderedVars.Sort((x, y) => { return VarsFirst(ctx, x, y); });

            // Fill in the sparse polynomial data structure.
            var degrees = new byte[orderedVars.Count];
            foreach(var (monom, coeff) in poly.coeffs)
            {
                for (int varIdx = 0; varIdx < orderedVars.Count; varIdx++)
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
                if(coeff == 0)
                    continue;

                Dictionary<AstIdx, ulong> varDegrees = new();
                for (int i = 0; i < orderedVars.Count; i++)
                {
                    var deg = monom.GetVarDeg(i);
                    if(deg == 0)
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

        public static AstIdx BackSubstitute(AstCtx ctx, AstIdx id, Dictionary<AstIdx, AstIdx> backSubstitutions)
            => BackSubstitute(ctx, id, backSubstitutions, new(16));

        public static AstIdx BackSubstitute(AstCtx ctx, AstIdx id, Dictionary<AstIdx, AstIdx> backSubstitutions, Dictionary<AstIdx, AstIdx> cache)
        {
            if(backSubstitutions.TryGetValue(id, out var backSub))
                return backSub;
            if(cache.TryGetValue(id, out var existing))
                return existing;


            var op0 = () => BackSubstitute(ctx, ctx.GetOp0(id), backSubstitutions, cache);
            var op1 = () => BackSubstitute(ctx, ctx.GetOp1(id), backSubstitutions, cache);

            var opcode = ctx.GetOpcode(id);
            var width = ctx.GetWidth(id);

            var result = opcode switch
            {
                AstOp.None => throw new NotImplementedException(),
                AstOp.Add => ctx.Add(op0(), op1()),
                AstOp.Mul => ctx.Mul(op0(), op1()),
                AstOp.Pow => ctx.Pow(op0(), op1()),
                AstOp.And => ctx.And(op0(), op1()),
                AstOp.Or => ctx.Or(op0(), op1()),
                AstOp.Xor => ctx.Xor(op0(), op1()),
                AstOp.Neg => ctx.Neg(op0()),
                AstOp.Lshr => ctx.Lshr(op0(), op1()),
                AstOp.Zext => ctx.Zext(op0(), width),
                AstOp.Trunc => ctx.Trunc(op0(), width),
                AstOp.Constant => id,
                AstOp.Symbol => id,
            };

            cache.TryAdd(id, result);
            return result;
        }
    }
}
