use egg::*;

use crate::{
    abstract_interpretation::KnownBitsWrapper,
    analysis::{reduce_modulo, Rewrite},
    classification::{AstClassification, MbaInfo},
    rules::{
        bitwise_power_of_two::{is_power_of_two, BitwisePowerOfTwoFactorApplier},
        duplicate_children_mul_add::{
            are_const, are_disjoint_const, are_disjoint_known_bits, are_minus_const,
            are_negated_const, are_subset_known_bits, const_a_contains_b, is_const,
            DuplicateChildrenMulAddApplier,
        },
        factor_integer_gcd::{has_significant_gcd, FactorIntegerGcdApplier},
        rewrite_power::{can_rewrite_power, RewritePowerApplier},
    },
};

mod bitwise_power_of_two;
mod duplicate_children_mul_add;
mod factor_integer_gcd;
mod rewrite_power;

// This is the preferred set of eqsat simplification rules.
// This ruleset consists of:
//  (a) Hand crafted rules that are known to be useful
//  (b) Almost all of the simplification rules from the GAMBA paper
//  (c) Some automatically generated rules
pub fn make_simplification_rules() -> Vec<Rewrite> {
    vec![
        // Or rules
        rewrite!("or-zero"; "(| ?a 0)" => "?a"),
        rewrite!("or-maxint"; "(| ?a -1)" => "-1"),
        rewrite!("or-itself"; "(| ?a ?a)" => "?a"),
        rewrite!("or-negated-itself"; "(| ?a (~ ?a))" => "-1"),
        rewrite!("or-commutativity"; "(| ?a ?b)" => "(| ?b ?a)"),
        rewrite!("or-associativity"; "(| ?a (| ?b ?c))" => "(| (| ?a ?b) ?c)"),
        // Xor rules
        rewrite!("xor-zero"; "(^ ?a 0)" => "?a"),
        rewrite!("xor-maxint"; "(^ ?a -1)" => "(~ ?a)"),
        rewrite!("xor-itself"; "(^ ?a ?a)" => "0"),
        rewrite!("xor-commutativity"; "(^ ?a ?b)" => "(^ ?b ?a)"),
        rewrite!("xor-associativity"; "(^ ?a (^ ?b ?c))" => "(^ (^ ?a ?b) ?c)"),
        rewrite!("xor-and-distribute"; "(& (^ ?a ?b) ?c)" => "(^ (& ?a ?c) (& ?b ?c))"),
        // xor simplification
        rewrite!("xor-reduce"; "(| (& (~ ?a) ?b) (& ?a (~ ?b)))" => "(^ ?a ?b)"),
        // And rules
        rewrite!("and-zero"; "(& ?a 0)" => "0"),
        rewrite!("and-maxint"; "(& ?a -1)" => "?a"),
        rewrite!("and-itself"; "(& ?a ?a)" => "?a"),
        rewrite!("and-negated-itself"; "(& ?a (~ ?a))" => "0"),
        rewrite!("and-commutativity"; "(& ?a ?b)" => "(& ?b ?a)"),
        rewrite!("and-associativity"; "(& ?a (& ?b ?c))" => "(& (& ?a ?b) ?c)"),
        // Add rules
        rewrite!("add-itself"; "(+ ?a ?a)" => "(* ?a 2)"),
        rewrite!("add-zero"; "(+ ?a 0)" => "?a"),
        rewrite!("add-cancellation"; "(+ ?a (* ?a -1))" => "0"),
        rewrite!("add-commutativity"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("add-associativity"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        // Mul rules
        rewrite!("mul-zero"; "(* ?a 0)" => "0"),
        rewrite!("mul-one"; "(* ?a 1)" => "?a"),
        rewrite!("mul-commutativity"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("mul-associativity"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rewrite!("mul-distributivity-expand-add"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        // Power rules
        rewrite!("power-zero"; "(** ?a 0)" => "1"),
        rewrite!("power-one"; "(** ?a 1)" => "?a"),
        rewrite!("unroll-power2"; "(** ?a 2)" => "(* ?a ?a)"),
        rewrite!("unroll-power3"; "(** ?a 3)" => "(* ?a (* ?a ?a))"),
        // Gamba rules
        // __check_duplicate_children
        rewrite!("expanded-add"; "(+ (* ?const ?x) ?x)" => {
            DuplicateChildrenMulAddApplier {
                const_factor : "?const",
                x_factor : "?x",
            }
        } if is_const("?const")),
        // ported rules:
        // __eliminate_nested_negations_advanced
        rewrite!("minus-twice"; "(* (* ?a -1) -1))" => "?a"),
        rewrite!("negate-twice"; "(~ (~ ?a))" => "?a"),
        // __check_bitwise_negations
        // bitwise -> arith
        rewrite!("add-bitwise-negation"; "(+ (~ ?a) ?b)" => "(+ (+ (* ?a -1) -1) ?b)"),
        rewrite!("sub-bitwise-negation"; "(+ (~ ?a) (* ?b -1))" => "(+ (+ (* ?a -1) -1) (* ?b -1))"),
        rewrite!("mul-bitwise-negation"; "(* (~ ?a) ?b)" => "(* (+ (* ?a -1) -1) ?b)"),
        rewrite!("pow-bitwise-negation"; "(** (~ ?a) ?b)" => "(** (+ (* ?a -1) -1) ?b)"),
        // arith -> bitwise
        rewrite!("and-bitwise-negation"; "(& (+ (* ?a -1) -1) ?b)" => "(& (~ ?a) ?b)"),
        rewrite!("or-bitwise-negation"; "(| (+ (* ?a -1) -1) ?b)" => "(| (~ ?a) ?b)"),
        rewrite!("xor-bitwise-negation"; "(^ (+ (* ?a -1) -1) ?b)" => "(^ (~ ?a) ?b)"),
        // __check_bitwise_powers_of_two
        rewrite!("bitwise_powers_of_two: "; "(& (* ?factor1 ?x) (* ?factor2 ?y))" => {
            BitwisePowerOfTwoFactorApplier {
                x_factor : "?factor1",
                y_factor : "?factor2",
            }
        } if (is_power_of_two("?factor1", "?factor2"))),
        rewrite!("factor_integer_gcd: "; "(+ (* ?factor1 ?x) (* ?factor2 ?y))" => {
            FactorIntegerGcdApplier {
                x_factor : "?factor1",
                y_factor : "?factor2",
            }
        } if (has_significant_gcd("?factor1", "?factor2"))),
        // __merge_inverse_bitwise_terms
        rewrite!("__merge_inverse_bitwise_terms-19"; "(+ (& ?x ?y) (& (~ ?x) ?y))" => "?y"),
        rewrite!("__merge_inverse_bitwise_terms-20"; "(+ (| ?x ?y) (| (~ ?x) ?y))" => "(+ (* 1 -1) ?y)"),
        rewrite!("__merge_inverse_bitwise_terms-21"; "(+ (^ ?x ?y) (^ (~ ?x) ?y))" => "(* 1 -1)"),
        rewrite!("__merge_inverse_bitwise_terms-22"; "(+ (| ?x ?y) (* (& (~ ?x) ?y) -1))" => "?x"),
        rewrite!("__merge_inverse_bitwise_terms-23"; "(+ (^ ?x ?y) (* (* 2 (& (~ ?x) ?y)) -1))" => "(+ ?x (* ?y -1))"),
        rewrite!("__merge_inverse_bitwise_terms-24"; "(+ (^ ?x ?y) (* 2 (| (~ ?x) ?y)))" => "(+ (+ -2 (* ?x -1)) ?y)"),
        //
        // __check_beautify_constants_in_products: todo
        // __check_move_in_bitwise_negations
        rewrite!("and-move-bitwise-negation-in"; "(~ (& (~ ?a) ?b))" => "(| ?a (~ ?b))"),
        rewrite!("or-move-bitwise-negation-in"; "(~ (| (~ ?a) ?b))" => "(& ?a (~ ?b))"),
        rewrite!("xor-move-bitwise-negation-in"; "(~ (^ (~ ?a) ?b))" => "(^ ?a ?b)"),
        // __check_bitwise_negations_in_excl_disjunctions
        rewrite!("xor-flip-negations"; "(^ (~ ?a) (~ ?b))" => "(^ ?a ?b)"),
        // __check_rewrite_powers
        rewrite!("extract-constant-factor-from-power"; "(** (* ?a ?b) ?exponent)" => {
            RewritePowerApplier {
                a: "?a".parse().unwrap(),
                b: "?b".parse().unwrap(),
                exponent: "?exponent".parse().unwrap(),
            }
        } if (can_rewrite_power("?a", "?exponent"))),
        // __check_resolve_product_of_powers
        // note: they say "Moreover merge factors that occur multiple times",
        // but I'm not sure what they mean
        rewrite!("merge-power-same-base"; "(* (** ?a ?b) (** ?a ?c))" => "(** ?a (+ ?b ?c))"),
        // __check_resolve_product_of_constant_and_sum: implemented above
        // __check_factor_out_of_sum
        rewrite!("factor"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        // __check_resolve_inverse_negations_in_sum
        rewrite!("invert-add-bitwise-not-self"; "(+ ?a (~ ?a))" => "-1"),
        rewrite!("invert-mul-bitwise-not-self"; "(+ (* ?a (~ ?b)) (* ?a ?b))" => "(* ?a -1)"),
        // __insert_fixed_in_conj: todo
        rewrite!("__insert_fixed_in_conj-1"; "(& ?y (~ (| ?y ?x)))" => "(& ?y (~ (| (* 1 -1) ?x)))"),
        // __insert_fixed_in_disj: todo
        // __check_trivial_xor: implemented above
        // __check_xor_same_mult_by_minus_one
        // "2*(x|-x) == x^-x"
        rewrite!("xor_same_mult_by_minus_one_1"; "(* (| ?a (* ?a -1)) 2)" => "(^ ?a (* ?a -1))"),
        // "-2*(x&-x) == x^-x"
        rewrite!("xor_same_mult_by_minus_one_2"; "(* (& ?a (* ?a -1)) -2)" => "(^ ?a (* ?a -1))"),
        // __check_conj_zero_rule
        // x&-x&2*x
        rewrite!("conj_zero_rule"; "(& ?a (& (* ?a -1) (* ?a 2)))" => "0"),
        // __check_conj_neg_xor_zero_rule
        // ~(2*x)&-(x^-x)
        rewrite!("conj_neg_xor_zero_rule"; "(& (~ (* ?a 2)) (* (^ ?a (* ?a -1)) -1))" => "0"),
        // __check_conj_neg_xor_minus_one_rule
        // 2*x|~-(x^-x)
        rewrite!("conj_neg_xor_minus_one_rule"; "(| (* ?a 2) (~ (* (^ ?a (* ?a -1)) -1)))" => "-1"),
        // __check_conj_negated_xor_zero_rule
        // 2*x&~(x^-x)
        rewrite!("conj_negated_xor_zero_rule"; "(& (* ?a 2) (~ (^ ?a (* ?a -1))))" => "0"),
        // __check_conj_xor_identity_rule
        // 2*x&(x^-x)
        rewrite!("conj_xor_identity_rule"; "(& (* ?a 2) (^ ?a (* ?a -1)))" => "(* ?a 2)"),
        // __check_disj_xor_identity_rule
        // 2*x|-(x^-x)
        rewrite!("disj_xor_identity_rule"; "(| (* ?a 2) (* -1 (^ ?a (* ?a -1))))" => "(* ?a 2)"),
        // __check_conj_neg_conj_identity_rule
        // -x&~(x&2*x)
        rewrite!("conj_neg_conj_identity_rule_1"; "(& (* ?a -1) (~ (& ?a (* ?a 2))))" => "(* ?a -1)"),
        // -x&~(x&-2*x)
        rewrite!("conj_neg_conj_identity_rule_2"; "(& (* ?a -1) (~ (& ?a (* ?a -2))))" => "(* ?a -1)"),
        // -x&(~x|~(2*x))
        rewrite!("conj_neg_conj_identity_rule_3"; "(& (* ?a -1) (| (~ ?a) (~ (* ?a 2))))" => "(* ?a -1)"),
        // -x&(~x|~(-2*x))
        rewrite!("conj_neg_conj_identity_rule_4"; "(& (* ?a -1) (| (~ ?a) (~ (* ?a -2))))" => "(* ?a -1)"),
        // __check_disj_disj_identity_rule
        // x|-(x|-x)
        rewrite!("disj_disj_identity_rule"; "(| ?a (* (| ?a (* ?a -1)) -1))" => "?a"),
        // __check_conj_conj_identity_rule
        // x&-(x&-x)
        rewrite!("conj_conj_identity_rule"; "(& ?a (* (& ?a (* ?a -1)) -1))" => "?a"),
        // __check_disj_conj_identity_rule
        // -x|(~x&2*x)
        rewrite!("disj_conj_identity_rule_1"; "(| (* ?a -1) (& (~ ?a) (* ?a 2)))" => "(* ?a -1)"),
        // -x|(~x&-2*x)
        rewrite!("disj_conj_identity_rule_2"; "(| (* ?a -1) (& (~ ?a) (* ?a -2)))" => "(* ?a -1)"),
        // -x|~(x|~(2*x))
        rewrite!("disj_conj_identity_rule_3"; "(| (* ?a -1) (~ (| ?a (~ (* ?a 2)))))" => "(* ?a -1)"),
        // -x|~(x|~(-2*x))
        rewrite!("disj_conj_identity_rule_4"; "(| (* ?a -1) (~ (| ?a (~ (* ?a -2)))))" => "(* ?a -1)"),
        // __check_disj_conj_identity_rule_2
        // x|(-~x&2*~x)
        rewrite!("disj_conj_identity_rule_2_1"; "(| ?x (& (* (~ ?x) -1) (* 2 (~ ?x))))" => "?x"),
        // x|(-~x&-2*~x)
        rewrite!("disj_conj_identity_rule_2_2"; "(| ?x (& (* (~ ?x) -1) (* (* 2 -1) (~ ?x))))" => "?x"),
        // __check_conj_disj_identity_rule
        // x&(-~(2*x)|-~x)
        rewrite!("conj_disj_identity_rule_1"; "(& ?x (| (* (~ (* 2 ?x)) -1) (* (~ ?x) -1)))" => "?x"),
        // x&(~(2*~x)|-~x)
        rewrite!("conj_disj_identity_rule_2"; "(& ?x (| (~ (* 2 (~ ?x))) (* (~ ?x) -1)))" => "?x"),
        // x&(~(-2*~x)|-~x)
        // Note that while GAMBA only solves this pattern for the constant '2', it is true if 'Y' is substituted with any value.
        rewrite!("conj_disj_identity_rule_3"; "(& ?x (| (~ (* (* ?y -1) (~ ?x))) (* (~ ?x) -1)))" => "?x"),
        // __check_disj_neg_disj_identity_rule
        // x|-(-x|2*x)
        rewrite!("disj_neg_disj_identity_rule_1"; "(| ?x (* (| (* ?x -1) (* ?y ?x)) -1))" => "?x"),
        // x|-(-x|-2*x)
        rewrite!("disj_neg_disj_identity_rule_2"; "(| ?x (* (| (* ?x -1) (* (* ?y -1) ?x)) -1))" => "?x"),
        // __check_disj_sub_disj_identity_rule
        // x|(x|y)-y
        rewrite!("disj_sub_disj_identity_rule_1"; "(| ?x (+ (| ?x ?y) (* ?y -1)))" => "?x"),
        // __check_disj_sub_disj_identity_rule
        // x|x-(x&y)
        rewrite!("disj_sub_disj_identity_rule_2"; "(| ?x (+ ?x (* (& ?x ?y) -1)))" => "?x"),
        // __check_conj_add_conj_identity_rule
        // x&x+(~x&y)
        rewrite!("conj_add_conj_identity_rule"; "(& ?x (+ ?x (& (~ ?x) ?y)))" => "?x"),
        // __check_disj_disj_conj_rule
        // x|-(-y|(x&y))
        rewrite!("disj_disj_conj_rule"; "(| ?x (* (| (* ?y -1) (& ?x ?y)) -1))" => "(| ?x ?y)"),
        // __check_conj_conj_disj_rule
        // x&-(-y&(x|y))
        rewrite!("conj_conj_disj_rule"; "(& ?x (* (& (* ?y -1) (| ?x ?y)) -1))" => "(& ?x ?y)"),
        // __check_disj_disj_conj_rule_2
        // -(-x|x&y&z)|x&y
        rewrite!("disj_disj_conj_rule_2"; "(| (* (| (* ?x -1) (& (& ?x ?y) ?z)) -1) (& ?x ?y))" => "?x"),
        // refine_after_substitution rules:
        // __check_bitwise_in_sums_cancel_terms
        rewrite!("__check_bitwise_in_sums_cancel_terms-1"; "(+ (& ?x ?y) (* ?x -1))" => "(+ ?y (* (| ?x ?y) -1))"),
        rewrite!("__check_bitwise_in_sums_cancel_terms-2"; "(+ (| ?x ?y) (* ?x -1))" => "(+ ?y (* (& ?x ?y) -1))"),
        rewrite!("__check_bitwise_in_sums_cancel_terms-3"; "(+ (* 2 (& ?x ?y)) (* ?x -1))" => "(+ ?y (* (^ ?x ?y) -1))"),
        rewrite!("__check_bitwise_in_sums_cancel_terms-4"; "(+ (* 2 (| ?x ?y)) (* ?x -1))" => "(+ ?y (^ ?x ?y))"),
        // __check_disj_involving_xor_in_sums
        rewrite!("__check_disj_involving_xor_in_sums_rule_1"; "(| (& ?x ?y) (^ ?x ?y))" => "(+ (& ?x ?y) (^ ?x ?y))"),
        rewrite!("__check_disj_involving_xor_in_sums_rule_2"; "(| (& (& ?z ?x) ?y) (^ ?x ?y))" => "(+ (& (& ?z ?x) ?y) (^ ?x ?y))"),
        // __check_xor_involving_disj
        rewrite!("__check_xor_involving_disj_rule"; "(^ ?x (| ?x ?y))" => "(& (~ ?x) ?y)"),
        // __check_negative_bitw_inverse
        // (a * a) + (a * ~a) => a * -1
        rewrite!("add-negated-itself-by-two"; "(+ (* ?a ?a) (* ?a (~ ?a)))" => "(* ?a -1)"),
        // Boolean simplification rules. Test case for the first 4: (2544496245092750091*(a|-11111112))+(((a^11111111)*1011494536914236835)+4517999858230595830)
        // c*(x|y) => (c*x) + (c*y) - (c*(x&y))
        //   rewrite!("or-expand"; "(* ?c (| ?x ?y))" => "(+ (+ (* ?c ?x) (* ?c ?y)) (* (* ?c (& ?x ?y)) -1))"),
        rewrite!("or-mul-shrink"; "(+ (+ (* ?c ?x) (* ?c ?y)) (* (* ?c (& ?x ?y)) -1))" => "(* ?c (| ?x ?y))"),
        rewrite!("or-shrink"; "(+ (& ?a ?b) (^ ?a ?b))" => "(| ?a ?b)"),
        rewrite!("or-shrink-2"; "(~ (& (~ ?a) (~ ?b)))" => "(| ?b ?a)"),
        rewrite!("or-shrink-3"; "(+ ?x (& ?y (~ ?x)))" => "(| ?x ?y)"),
        // (a^b) | a
        rewrite!("or-shrink-4"; "(| (^ ?a ?b) ?a)" => "(| ?a ?b)"),
        // c*(x^y) => c*x + c*y - 2*c*(x&y)
        // rewrite!("xor-expand"; "(* ?c (^ ?x ?y))" => "(+ (+ (* ?c ?x) (* ?c ?y)) (* (* (* 2 ?c) (& ?x ?y)) -1))"),
        // (c*x) + (c*y) - (2*c*(x&y)) => c*(x^y)
        rewrite!("xor-mul-shrink"; "(+ (+ (* ?c ?x) (* ?c ?y)) (* (* (* 2 ?c) (& ?x ?y)) -1))" => "(* ?c (^ ?x ?y))"),
        // (x+y) + (-2*(x&y)) => x^y
        rewrite!("xor-shrink"; "(+ (+ ?x ?y) (* -2 (& ?x ?y)))" => "(^ ?x ?y)"),
        // (a|b) + (-1*(a&b)) => a^b
        rewrite!("xor-shrink2"; "(+ (| ?a ?b) (* -1 (& ?a ?b)))" => "(^ ?a ?b)"),
        // expr => a^b
        rewrite!("xor-shrink-3"; "(& (~ (& (~ ?a) (~ ?b))) (~ (& ?a ?b)))" => "(^ ?b ?a)"),
        // (x&y) + (~(x|y)) => ~(x^y)
        rewrite!("negated-xor-shrink-4"; "(+ (& ?x ?y) (~ (| ?x ?y)))" => "(~ (^ ?x ?y))"),
        // a*(b&c) => (a*b) + (a*c) - (a*(b|c))
        //  rewrite!("and-expand"; "(* ?a (& ?b ?c))" => "(+ (+ (* ?a ?b) (* ?a ?c)) (* (* ?a (| ?b ?c)) -1))"),
        rewrite!("and-mul-shrink"; "(+ (+ (* ?a ?b) (* ?a ?c)) (* (* ?a (| ?b ?c)) -1))" => "(* ?a (& ?b ?c))"),
        // (a | b) + (-1 * (a^b)) => a & b
        rewrite!("and-shrink"; "(+ (| ?a ?b) (* -1 (^ ?a ?b)))" => "(& ?a ?b)"),
        // (a&b) + (a|b) => (a + b)
        rewrite!("add-shrink"; "(+ (& ?a ?b) (| ?a ?b))" => "(+ ?a ?b)"),
        // (b*a) - (b*(a&d)) => b*(a&~d)
        rewrite!("cancel-and-reduce-bitwise-subtraction"; "(+ (* ?b ?a) (* (* ?b (& ?a ?d)) -1))" => "(* ?b (& ?a (~ ?d)))"),
        // (x*(a&c)) - (y*(a&c)) => (x+-1*y)*(a&c)
        // TODO: Only apply this rule on linear subtrees or constants.
        rewrite!("merge-and-multipliers"; "(+ (* ?x (& ?a ?c)) (* (* ?y (& ?a ?c)) -1))" => "(* (+ ?x (* -1 ?y)) (& ?a ?c))"),
        // (b+a)+((~a)|x) => (b+(a&x)) - 1
        rewrite!("merge-and-plus-add-minus-one"; "(+ (+ ?b ?a) (| (~ ?a) ?x))" => "(+ (+ ?b (& ?a ?x)) -1)"),
        // "a + (~a|b) => (a&b) + -1
        rewrite!("merge-bitwise-and-minus-one"; "(+ ?a (| (~ ?a) ?b))" => "(+ (& ?a ?b) -1)"),
        rewrite!("mba-1"; "(+ ?d (* -1 (& ?d ?a)))" => "(& (~ ?a) ?d)"),
        rewrite!("mba-2"; "(+ (* -1 (& ?d ?a)) ?d)" => "(& (~ ?a) ?d)"),
        rewrite!("mba-3"; "(+ (+ ?a -2) (* -2 ?d))" => "(+ (+ -2 ?a) (* -2 ?d))"),
        rewrite!("mba-4"; "(+ (| ?d ?a) (* -1 (& ?a (~ ?d))))" => "?d"),
        rewrite!("mba-5"; "(+ (* -1 (& ?a (~ ?d))) (| ?d ?a))" => "?d"),
        rewrite!("mba-9"; "(+ (+ ?a (* -2 ?d)) (* 2 (& (~ ?a) (* 2 ?d))))" => "(^ ?a (* 2 ?d))"),
        rewrite!("mba-10"; "(~ (* ?x ?y))" => "(+ (* (~ ?x) ?y) (+ ?y -1))"),
        rewrite!("mba-12"; "(~ (+ ?x (* ?y -1)))" => "(+ (~ ?x) (* (+ (~ ?y) 1) -1))"),
        rewrite!("mba-13"; "(~ (& ?x ?y))" => "(| (~ ?x) (~ ?y))"),
        rewrite!("mba-14"; "(~ (^ ?x ?y))" => "(| (& ?x ?y) (~ (| ?x ?y)))"),
        rewrite!("mba-15"; "(~ (| ?x ?y))" => "(& (~ ?x) (~ ?y))"),
        rewrite!("not-to-arith"; "(~ ?a)" => "(+ (* ?a -1) -1)"),
        rewrite!("arith-to-not"; "(+ (* ?a -1) -1)" => "(~ ?a)"),
        // a*(a+1) => -a*~a
        //rewrite!("mul-add-one-to-neg"; "(* ?a (+ ?a 1))" => "(* (* ?a -1) (~ ?a))"),
        // a+(d*-1)
        rewrite!("new-1"; "(+ (^ ?x ?y) (* -1 ?x))" => "(+ ?y (* -2 (& ?x ?y)))"),
        rewrite!("new-2"; "(+ (^ ?x ?y) (* -1 (| ?x ?y)))" => "(* -1 (& ?x ?y))"),
        rewrite!("new-3"; "(+ (| ?a ?b) (* ?a -1))" => "(& (~ ?a) ?b)"),
        rewrite!("new-4"; "(+ (* ?a -1) ?b)" => "(* -1 (+ ?a (* ?b -1)))"),
        rewrite!("new-5"; "(* ?a 2)" => "(+ ?a ?a)"),
        rewrite!("new-10"; "(+ (~ (& ?a ?b)) ?a)" => "(+ -1 (& ?a (~ ?b)))"),
        //
        rewrite!("new-14"; "(+ (^ ?a ?b) ?a)" => "(+ ?b (* 2 (& ?a (~ ?b))))"),
        rewrite!("new-15"; "(+ (| ?a ?b) ?a)" => "(+ (~ (| ?a (~ ?b))) (* 2 ?a))"),
        rewrite!("new-16"; "(& (^ ?a ?b) ?a)" => "(& ?a (~ ?b))"),
        rewrite!("new-18"; "(+ (* ?a ?b) 1)" => "(* (~ (* ?a ?b)) -1)"),
        rewrite!("new-19"; "(+ (* ?a ?b) -1)" => "(~ (* (* ?a -1) ?b))"),
        rewrite!("new-20"; "(+ (* ?a ?b) ?a)" => "(* (* -1 ?a) (~ ?b))"),
        rewrite!("new-21"; "(& ?a (~ ?b))" => "(+ ?a (* (& ?a ?b) -1))"),
        rewrite!("new-23"; "(+ (& (~ ?x) ?y) (* ?y -1))" => "(* (& ?x ?y) -1)"),
        rewrite!("new-24"; "(+ (& (~ ?x) ?y) (* ?y (* 1 -1)))" => "(* (& ?x ?y) -1)"),
        rewrite!("and-norm-1"; "(& ?x (~ ?y))" => "(+ ?x (* -1 (& ?x ?y)))"),
        rewrite!("and-norm-2"; "(& (~ ?x) ?y)" => "(+ ?y (* -1 (& ?x ?y)))"),
        rewrite!("xor-norm-1"; "(^ ?x ?y)" => "(+ ?x (+ ?y (* -1 (* 2 (& ?x ?y)))))"),
        rewrite!("or-norm-1"; "(| ?x ?y)" => "(+ ?x (+ ?y (* -1 (& ?x ?y))))"),
        rewrite!("and-denorm-1"; "(+ ?x (* -1 (& ?x ?y)))" => "(& ?x (~ ?y))" ),
        rewrite!("and-denorm-2"; "(+ ?y (* -1 (& ?x ?y)))" => "(& (~ ?x) ?y)"),
        rewrite!("xor-denorm-1"; "(+ ?x (+ ?y (* -1 (* 2 (& ?x ?y)))))" => "(^ ?x ?y)"),
        rewrite!("or-denorm-1"; "(+ ?x (+ ?y (* -1 (& ?x ?y))))" => "(| ?x ?y)"),
        rewrite!("opaque-constant-1"; "(& 1 (^ ?y (+ (* 2 -1) ?y)))" => "0"),
        rewrite!("opaque-constant-1-again"; "(+ (& ?x ?y) (~ (& ?x ?y)))" => "-1"),
        rewrite!("opaque-constant-two"; "(^ (& 1 ?y) (& 1 (+ ?y (* 2 -1))))" => "0"),
        rewrite!("opaque-variable-or"; "(| (& ?a ?b) ?a)" => "?a"),
        rewrite!("opaque-variable-add"; "(+ (& ?a (~ ?d)) (& ?d ?a))" => "?a"),
        // This is only correct when the constant is 1. Note: There is a formula to distribute any constant into the multiplication, but I've never seen it be profitable.
        rewrite!("distribute-constant-and-into-multiplication"; "(& (* ?x ?y) 1)" => "(* (& ?x 1) (& ?y 1))"),
        rewrite!("unroll-xor"; "(^ ?x ?y)" => "(+ (+ (| (~ ?x) ?y) (& ?x (~ ?y))) (* (~ (^ ?x ?y)) -1))"),
        rewrite!("unroll-and"; "(& ?x ?y)" => "(+ (+ (| ?x ?y) (* (& (~ ?x) ?y) -1)) (* (& ?x (~ ?y)) -1))"),
        rewrite!("unroll-or"; "(| ?x ?y)" => "(+ (+ (+ ?x ?y) 1) (| (+ (* ?x -1) (* 1 -1)) (+ (* ?y -1) (* 1 -1))))"),
        rewrite!("unroll-mul"; "(* ?x ?y)" => "(+ (* (& ?x ?y) (| ?x ?y)) (* (& ?x (~ ?y)) (& (~ ?x) ?y)))"),
        rewrite!("unroll-add"; "(+ ?x ?y)" => "(+ (+ (^ ?x (~ ?y)) (* 2 (| ?x ?y))) 1)"),
        rewrite!("synthesis-19"; "(~ (* ?x ?y))" => "(+ (* (~ ?x) ?y) (+ ?y (* 1 -1)))"),
        rewrite!("synthesis-20"; "(~ (+ ?x ?y))" => "(+ (~ ?x) (+ (~ ?y) 1))"),
        rewrite!("synthesis-21"; "(~ (+ ?x (* ?y -1)))" => "(+ (~ ?x) (* (+ (~ ?y) 1) -1))"),
        rewrite!("synthesis-22"; "(~ (& ?x ?y))" => "(| (~ ?x) (~ ?y))"),
        rewrite!("synthesis-23"; "(~ (^ ?x ?y))" => "(| (& ?x ?y) (~ (| ?x ?y)))"),
        rewrite!("synthesis-24"; "(~ (| ?x ?y))" => "(& (~ ?x) (~ ?y))"),
        rewrite!("synthesis-25"; "(* (* ?x ?y) -1)" => "(* (* ?x -1) ?y)"),
        rewrite!("synthesis-26"; "(* (* ?x -1) ?y)" => "(* (* ?x ?y) -1)"),
        rewrite!("synthesis-27"; "(* ?x -1)" => "(+ (~ ?x) 1)"),
        rewrite!("synthesis-28"; "(+ (~ ?x) 1)" => "(* ?x -1)"),
        rewrite!("synthesis-29"; "(+ (* ?x ?y) ?y)" => "(* (+ ?x 1) ?y)"),
        rewrite!("synthesis-31"; "(* (+ ?x ?y) -1)" => "(+ (* ?x -1) (* ?y -1))"),
        rewrite!("synthesis-30"; "(+ ?x ?x)" => "(* 2 ?x)"),
        // Apply the rewrite ((y&c1)&x) + (x&c2) => ((y&c1) | c2) & x.
        // Note that this is only value if (c1&&c2) == 0. I.e. the constants have no set bits in common.
        rewrite!("disjoint-bitwise-add-into-or"; "(+ (& (& ?y ?c1) ?x) (& ?x ?c2))" => "(& (| (& ?y ?c1) ?c2) ?x)" if are_disjoint_const("?c1", "?c2")),
        // // Apply the rewrite (x & ((y & c1) + c2)) => (x & ((y & c1) | c2))
        // // Note that this is only value if (c1&&c2) == 0. I.e. the constants have no set bits in common.
        rewrite!("disjoint-bitwise-add-into-or2"; "(& ?x (+ (& ?y ?c1) ?c2))" => "(& ?x (| (& ?y ?c1) ?c2))" if are_disjoint_const("?c1", "?c2")),
        // // Apply the rewrite (a & c1) - (a & c2) => (a & (c1 & ~c2)).
        // // Note that this is only valid if (c1&c2) == c2.
        rewrite!("merge-and-subtraction-by-constant"; "(+ (& ?a ?c1) (* (& ?a ?c2) -1))" => "(& ?a (& ?c1 (~ ?c2)))" if const_a_contains_b("?c1", "?c2")),
        // // Apply the rewrite x * (a & c1) - x * (a & c2) => x * (a & (c1 & ~c2))
        // // Note that this is only valid if (c1&c2) == c2.
        rewrite!("merge-and-subtraction-by-constant-2"; "(+ (* ?x (& ?a ?c1)) (* (* ?x (& ?a ?c2)) -1))" => "(* ?x (& ?a (& ?c1 (~ ?c2))))" if const_a_contains_b("?c1", "?c2")),
        // Known bits rules:
        rewrite!("known-bits-0"; "(+ ?x ?y)" => "(| ?x ?y)" if are_disjoint_known_bits("?x", "?y")),
        rewrite!("known-bits-1"; "(^ ?x ?y)" => "(| ?x ?y)" if are_disjoint_known_bits("?x", "?y")),
        rewrite!("known-bits-1-rev"; "(| ?x ?y)" => "(+ ?x ?y)" if are_disjoint_known_bits("?x", "?y")),
        rewrite!("known-bits-2"; "(& ?x ?y)" => "?x" if are_subset_known_bits("?y", "?x")),
        rewrite!("known-bits-3"; "(| ?x ?y)" => "?x" if are_subset_known_bits("?x", "?y")),
        // // x*(a&c) + y*(a&b&c) => ((x + y)*(a&c)) - (y*((a&c)&~b))
        rewrite!("factor-bitwise-and"; "(+ (* ?x (& ?a ?c)) (* ?y (& (& ?a ?b) ?c)))" => "(+ (* (+ ?x ?y) (& ?a ?c)) (* (* ?y (& (& ?a ?c) (~ ?b))) -1))"),
        // // (x*a) + (y*(a&b)) => ((x+y)*a) - (y*(a&~b))
        rewrite!("can1357-1"; "(+ (* ?x ?a) (* ?y (& ?a ?b)))" => "(+ (* (+ ?x ?y) ?a) (* (* ?y (& ?a (~ ?b))) -1))"),
        // // a&b => a-(a&~b)
        rewrite!("can1357-2"; "(& ?a ?b)" => "(+ ?a (* (& ?a (~ ?b)) -1))"),
        // // (x * z) + (-x * y) => x*(-y+z)
        // rewrite!("neg-multiply"; "(+ (* 4545453343454543 ?z) (* -4545453343454543 ?y))" => "(* 4545453343454543 (+ (* ?y -1) ?z))"),
        // // (c1 * (a&b&c)) + (-c1 * (b&~a)) => c1 * ((b&a&c) - (~a&b))
        rewrite!("factor-bitwise-mul"; "(+ (* ?c1 (& (& ?a ?b) ?c)) (* (* ?c1 -1) (& ?b (~ ?a))))" => "(* ?c1 (+ (& (& ?b ?a) ?c) (* (& (~ ?a) ?b) -1)))"),
        // // (((c * c1) + a1) + ((-c1 * a2) + a3)) => a1+a3+c1*(-a2+c)
        rewrite!("factor-add"; "(+ (+ (* ?c ?c1) ?a1) (+ (* (* ?c1 -1) ?a2) ?a3))" => "(+ (+ ?a1 ?a3) (* ?c1 (+ (* ?a2 -1) ?c)))"),
        // // again
        rewrite!("factor-again-again"; "(+ (* (* ?c1 -1) (& ?b (~ ?c))) (* ?c1 (& ?c2 (& ?b ?c))))" => "(* ?c1 (+ (& (& ?b ?c) ?c2) (* (& (~ ?c) ?b) -1)))"),
        // // Inspired by the input `(((a1^65565665)&(y^(a1^-65565666)))^(y&(~x)))`, we use the rule:
        // // (a^b)&(c^(a^~b)) => c&(a^b)
        // // This reduces the input down to `((y&(a1^-65565666))^(y&x))`, which is still not perfect.
        rewrite!("reduce-and-xor-negated"; "(& (^ ?a ?b) (^ ?c (^ ?a (~ ?b))))" => "(& ?c (^ ?a ?b))"),
        // // Inspired by the failure above we apply the rule:
        // // (a&b)^(a&c) => a&(b^c)
        // // to finally reduce the input down to it's ground truth: `(y&(x^(a1^c1)))`.
        rewrite!("reduce-and-xor"; "(^ (& ?y (^ ?a1 ?c1)) (& ?y ?x))" => "(& ?y (^ ?x (^ ?a1 ?c1)))"),
        // // (((y^z)|(y&x))^(y)) => z&~(x&y)
        rewrite!("reduced-or-or-xor"; "(^ (| (^ ?y ?z) (& ?y ?x)) ?y)" => "(& ?z (~ (& ?x ?y)))"),
        rewrite!("xor-itself-twice"; "(^ (^ ?c1 ?a) (^ ?c2 ?a))" => "(^ ?c1 ?c2)" if are_const("?c1", "?c2")),
        // // ((x&y)+(z^(x|y))) + (2*(z|(~(x&y)))) => -2+(z^x^y)
        rewrite!("combine-and-add-xor-or"; "(+ (+ (& ?x ?y) (^ ?z (| ?x ?y))) (* 2 (| ?z (~ (& ?x ?y)))))" => "(+ -2 (^ (^ ?z ?x) ?y))"),
        // // (-((x&y)+(z^(x|y)))) + (-2*(z|(~(x&y)))) => 2-(z^x^y)
        rewrite!("combine-and-add-xor-or-2"; "(+ (* (+ (& ?x ?y) (^ ?z (| ?x ?y))) -1) (* -2 (| ?z (~ (& ?x ?y)))))" => "(+ 2 (* (^ (^ ?z ?x) ?y) -1))"),
        // // ((y^(x^z))+(z^(y&x))) => z+(z^(x|y))
        rewrite!("pack-add-xor-or"; "(+ (^ ?y (^ ?x ?z)) (^ ?z (& ?y ?x)))" => "(+ ?z (^ ?z (| ?x ?y)))"),
        // // (z&((~y)|(z^x))) => z&~(x&y)
        rewrite!("pack-negated-xor"; "(& ?z (| ?y (^ ?z ?x)))" => "(& ?z (| (~ ?x) ?y))"),
        // // (~x&y)+(y&x) => x
        rewrite!("negated-and-add"; "(+ (& (~ ?x) ?y) (& ?y ?x))" => "?y"),
        // ((d*a)^(d+(~a))) => ~(a*d^a-d)
        // Without this rule, we cannot deduce that:
        // ((((d*a)^(a+(d*-1)))&(d*(a*(a+1))))+((d*(a*(a+1)))&((d*a)^(d+(~a)))))
        // is actually (~(a*d^a-d)&-a*~a*d)+(-a*~a*d&(a*d^a-d)).
        // This rule seems to also apply to bitwise AND. We may to extend this to AND, or we may want to remove this rule entirely eventually.
        // I'm not sure if there is a more generic method of handling this case.
        rewrite!("factor-out-negation"; "(^ (* ?d ?a) (+ ?d (~ ?a)))" => "(~ (^ (* ?a ?d) (+ ?a (* ?d -1))))"),
        // ((a^b)*c1)+((a|b)*c2) => ((c1+c2)*(a+b)) + ((-2*c1-c2)*(a&b))
        // Note that this rule is technically true in all cases, but it causes the egraph to be bloated.
        // Currently we only apply this rule if c1 and c2 are constants, but it is sometimes helpful to always apply this rule.
        rewrite!("xor-add-or-into-constant"; "(+ (* (^ ?a ?b) ?c1) (* (| ?a ?b) ?c2))" => "(+ (* (+ ?c1 ?c2) (+ ?a ?b)) (* (+ (* -2 ?c1) (* ?c2 -1)) (& ?a ?b)))" if are_const("?c1", "?c2")),
        //rewrite!("add-xor-or-into-and"; "(+ (^ ?a ?b) (| ?a ?b))" => "(& ?a ?b)"),
        // Test case: `(5316414292264113613*(b&(~a))) + (2544496245092750091*(a|(~b)))` can be converted to `-2544496245092750091+2771918047171363522*(~a&b)`.
        // (c1*(b&(~a))) + (c2*(a|(~b))) => (-c2) + ((c1 - c2)*(~a&b))
        // Note that we could apply this if c1 and c2 are not constant, but we don't because it would bloat the egraph.
        rewrite!("pack-mul-negated-and"; "(+ (* ?c1 (& ?b (~ ?a))) (* ?c2 (| ?a (~ ?b))))" => "(+ (* ?c2 -1) (* (+ ?c1 (* ?c2 -1)) (& (~ ?a) ?b)))" if are_const("?c1", "?c2")),
        // (d&(~(c|b))) => ~b&~c&d
        rewrite!("distribute-neg-into-or"; "(& ?d (~ (| ?c ?b)))" => "(& (& (~ ?b) (~ ?c)) ?d)"),
        // From the input `(a&~b&~c&d&e&~f) + (a&b&c&d&e&~f)` comes:
        // (a&~b&~c) + (a&b&c)=> a&~(b^c)
        rewrite!("pack-negated-and-neg-into-xor"; "(+ (& (& ?a (~ ?b)) (~ ?c)) (& (& ?a ?b) ?c))" => "(& ?a (~ (^ ?b ?c)))"),
        // (~(b|c)|b&c) => ~(b^c)
        rewrite!("pack-neg-or-and-into-negated-xor"; "(| (~ (| ?b ?c)) (& ?b ?c))" => "(~ (^ ?b ?c))"),
        // (z^(x|(~(y&z)))) => ~(z&(x|~y))
        // Comes from: (z^(x|(~(y&z))))
        rewrite!("combine-xor-or"; "(^ ?z (| ?x (~ (& ?y ?z))))" => "(~ (& ?z (| ?x (~ ?y))))"),
        // (y&x)&(x^z) => x&y&~z
        rewrite!("pack-and-xor"; "(& (& ?y ?x) (^ ?x ?z))" => "(& (& ?x ?y) (~ ?z))"),
        // ((~(y&x))&(x^(z^(~y)))) => ~(x&y|x^y^z)
        rewrite!("pack-into-negated-and-or-xor"; "(& (~ (& ?y ?x)) (^ ?x (^ ?z (~ ?y))))" => "(~ (| (& ?x ?y) (^ (^ ?x ?y) ?z)))"),
        // ((y^(x|(y&(~z))))+((z^(x^y))|(x&y))) => x+(x^(y|z))
        rewrite!("linear-mba-1"; "(+ (^ ?y (| ?x (& ?y (~ ?z)))) (| (^ ?z (^ ?x ?y)) (& ?x ?y)))" => "(+ ?x (^ ?x (| ?y ?z)))"),
        // (c1*(z^(~(x|(z&y)))))+(-c1*((z&x)+(y|(x|(~z))))) => -c1*x
        rewrite!("linear-mba-2"; "(+ (* ?c1 (^ ?z (~ (| ?x (& ?z ?y))))) (* (* ?c1 -1) (+ (& ?z ?x) (| ?y (| ?x (~ ?z))))))" => "(* (* ?c1 -1) ?x)"),
    ]
}

// This ruleset is superseded by "make_simplification_rules".
pub fn make_original_rules() -> Vec<Rewrite> {
    vec![
        // Or rules
        rewrite!("or-zero"; "(| ?a 0)" => "?a"),
        rewrite!("or-maxint"; "(| ?a -1)" => "-1"),
        rewrite!("or-itself"; "(| ?a ?a)" => "?a"),
        rewrite!("or-negated-itself"; "(| ?a (~ ?a))" => "-1"),
        rewrite!("or-commutativity"; "(| ?a ?b)" => "(| ?b ?a)"),
        rewrite!("or-associativity"; "(| ?a (| ?b ?c))" => "(| (| ?a ?b) ?c)"),
        // Xor rules
        rewrite!("xor-zero"; "(^ ?a 0)" => "?a"),
        rewrite!("xor-maxint"; "(^ ?a -1)" => "(~ ?a)"),
        rewrite!("xor-itself"; "(^ ?a ?a)" => "0"),
        rewrite!("xor-commutativity"; "(^ ?a ?b)" => "(^ ?b ?a)"),
        rewrite!("xor-associativity"; "(^ ?a (^ ?b ?c))" => "(^ (^ ?a ?b) ?c)"),
        // And rules
        rewrite!("and-zero"; "(& ?a 0)" => "0"),
        rewrite!("and-maxint"; "(& ?a -1)" => "?a"),
        rewrite!("and-itself"; "(& ?a ?a)" => "?a"),
        rewrite!("and-negated-itself"; "(& ?a (~ ?a))" => "0"),
        rewrite!("and-commutativity"; "(& ?a ?b)" => "(& ?b ?a)"),
        rewrite!("and-associativity"; "(& ?a (& ?b ?c))" => "(& (& ?a ?b) ?c)"),
        // Add rules
        rewrite!("add-itself"; "(+ ?a ?a)" => "(* ?a 2)"),
        rewrite!("add-zero"; "(+ ?a 0)" => "?a"),
        rewrite!("add-cancellation"; "(+ ?a (* ?a -1))" => "0"),
        rewrite!("add-commutativity"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("add-associativity"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        // Mul rules
        rewrite!("mul-zero"; "(* ?a 0)" => "0"),
        rewrite!("mul-one"; "(* ?a 1)" => "?a"),
        rewrite!("mul-commutativity"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("mul-associativity"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rewrite!("mul-distributivity-expand-add"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        // Power rules
        rewrite!("power-zero"; "(** ?a 0)" => "1"),
        rewrite!("power-one"; "(** ?a 1)" => "?a"),
        // __check_duplicate_children
        rewrite!("expanded-add"; "(+ (* ?const ?x) ?x)" => {
            DuplicateChildrenMulAddApplier {
                const_factor : "?const",
                x_factor : "?x",
            }
        } if is_const("?const")),
        // ported rules:
        // __eliminate_nested_negations_advanced
        rewrite!("minus-twice"; "(* (* ?a -1) -1))" => "?a"),
        rewrite!("negate-twice"; "(~ (~ ?a))" => "?a"),
        // __check_bitwise_negations
        // bitwise -> arith
        // rewrite!("add-bitwise-negation"; "(+ (~ ?a) ?b)" => "(+ (+ (* ?a -1) -1) ?b)"),
        // rewrite!("sub-bitwise-negation"; "(+ (~ ?a) (* ?b -1))" => "(+ (+ (* ?a -1) -1) (* ?b -1))"),
        // rewrite!("mul-bitwise-negation"; "(* (~ ?a) ?b)" => "(* (+ (* ?a -1) -1) ?b)"),
        // rewrite!("pow-bitwise-negation"; "(** (~ ?a) ?b)" => "(** (+ (* ?a -1) -1) ?b)"),
        // arith -> bitwise
        // rewrite!("and-bitwise-negation"; "(& (+ (* ?a -1) -1) ?b)" => "(& (~ ?a) ?b)"),
        // rewrite!("or-bitwise-negation"; "(| (+ (* ?a -1) -1) ?b)" => "(| (~ ?a) ?b)"),
        // rewrite!("xor-bitwise-negation"; "(^ (+ (* ?a -1) -1) ?b)" => "(^ (~ ?a) ?b)"),
        // __check_bitwise_powers_of_two
        rewrite!("bitwise_powers_of_two: "; "(& (* ?factor1 ?x) (* ?factor2 ?y))" => {
            BitwisePowerOfTwoFactorApplier {
                x_factor : "?factor1",
                y_factor : "?factor2",
            }
        } if (is_power_of_two("?factor1", "?factor2"))),
        rewrite!("factor_integer_gcd: "; "(+ (* ?factor1 ?x) (* ?factor2 ?y))" => {
            FactorIntegerGcdApplier {
                x_factor : "?factor1",
                y_factor : "?factor2",
            }
        } if (has_significant_gcd("?factor1", "?factor2"))),
        // __check_beautify_constants_in_products: todo
        // __check_move_in_bitwise_negations
        rewrite!("and-move-bitwise-negation-in"; "(~ (& (~ ?a) ?b))" => "(| ?a (~ ?b))"),
        rewrite!("or-move-bitwise-negation-in"; "(~ (| (~ ?a) ?b))" => "(& ?a (~ ?b))"),
        rewrite!("xor-move-bitwise-negation-in"; "(~ (^ (~ ?a) ?b))" => "(^ ?a ?b)"),
        // __check_bitwise_negations_in_excl_disjunctions
        rewrite!("xor-flip-negations"; "(^ (~ ?a) (~ ?b))" => "(^ ?a ?b)"),
        // __check_rewrite_powers
        rewrite!("extract-constant-factor-from-power"; "(** (* ?a ?b) ?exponent)" => {
            RewritePowerApplier {
                a: "?a".parse().unwrap(),
                b: "?b".parse().unwrap(),
                exponent: "?exponent".parse().unwrap(),
            }
        } if (can_rewrite_power("?a", "?exponent"))),
        // __check_resolve_product_of_powers
        // note: they say "Moreover merge factors that occur multiple times",
        // but I'm not sure what they mean
        rewrite!("merge-power-same-base"; "(* (** ?a ?b) (** ?a ?c))" => "(** ?a (+ ?b ?c))"),
        // __check_resolve_product_of_constant_and_sum: implemented above
        // __check_factor_out_of_sum
        rewrite!("factor"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        // __check_resolve_inverse_negations_in_sum
        rewrite!("invert-add-bitwise-not-self"; "(+ ?a (~ ?a))" => "-1"),
        rewrite!("invert-mul-bitwise-not-self"; "(+ (* ?a (~ ?b)) (* ?a ?b))" => "(* ?a -1)"),
        // __insert_fixed_in_conj: todo
        // __insert_fixed_in_disj: todo
        // __check_trivial_xor: implemented above
        // __check_xor_same_mult_by_minus_one
        // "2*(x|-x) == x^-x"
        rewrite!("xor_same_mult_by_minus_one_1"; "(* (| ?a (* ?a -1)) 2)" => "(^ ?a (* ?a -1))"),
        // "-2*(x&-x) == x^-x"
        rewrite!("xor_same_mult_by_minus_one_2"; "(* (& ?a (* ?a -1)) -2)" => "(^ ?a (* ?a -1))"),
        // __check_conj_zero_rule
        // x&-x&2*x
        rewrite!("conj_zero_rule"; "(& ?a (& (* ?a -1) (* ?a 2)))" => "0"),
        // __check_conj_neg_xor_zero_rule
        // ~(2*x)&-(x^-x)
        rewrite!("conj_neg_xor_zero_rule"; "(& (~ (* ?a 2)) (* (^ ?a (* ?a -1)) -1))" => "0"),
        // __check_conj_neg_xor_minus_one_rule
        // 2*x|~-(x^-x)
        rewrite!("conj_neg_xor_minus_one_rule"; "(| (* ?a 2) (~ (* (^ ?a (* ?a -1)) -1)))" => "-1"),
        // __check_conj_negated_xor_zero_rule
        // 2*x&~(x^-x)
        rewrite!("conj_negated_xor_zero_rule"; "(& (* ?a 2) (~ (^ ?a (* ?a -1))))" => "0"),
        // __check_conj_xor_identity_rule
        // 2*x&(x^-x)
        rewrite!("conj_xor_identity_rule"; "(& (* ?a 2) (^ ?a (* ?a -1)))" => "(* ?a 2)"),
        // __check_disj_xor_identity_rule
        // 2*x|-(x^-x)
        rewrite!("disj_xor_identity_rule"; "(| (* ?a 2) (* -1 (^ ?a (* ?a -1))))" => "(* ?a 2)"),
        // __check_conj_neg_conj_identity_rule
        // -x&~(x&2*x)
        rewrite!("conj_neg_conj_identity_rule_1"; "(& (* ?a -1) (~ (& ?a (* ?a 2))))" => "(* ?a -1)"),
        // -x&~(x&-2*x)
        rewrite!("conj_neg_conj_identity_rule_2"; "(& (* ?a -1) (~ (& ?a (* ?a -2))))" => "(* ?a -1)"),
        // -x&(~x|~(2*x))
        rewrite!("conj_neg_conj_identity_rule_3"; "(& (* ?a -1) (| (~ ?a) (~ (* ?a 2))))" => "(* ?a -1)"),
        // -x&(~x|~(-2*x))
        rewrite!("conj_neg_conj_identity_rule_4"; "(& (* ?a -1) (| (~ ?a) (~ (* ?a -2))))" => "(* ?a -1)"),
        // __check_disj_disj_identity_rule
        // x|-(x|-x)
        rewrite!("disj_disj_identity_rule"; "(| ?a (* (| ?a (* ?a -1)) -1))" => "?a"),
        // __check_conj_conj_identity_rule
        // x&-(x&-x)
        rewrite!("conj_conj_identity_rule"; "(& ?a (* (& ?a (* ?a -1)) -1))" => "?a"),
        // __check_disj_conj_identity_rule
        // -x|(~x&2*x)
        rewrite!("disj_conj_identity_rule_1"; "(| (* ?a -1) (& (~ ?a) (* ?a 2)))" => "(* ?a -1)"),
        // -x|(~x&-2*x)
        rewrite!("disj_conj_identity_rule_2"; "(| (* ?a -1) (& (~ ?a) (* ?a -2)))" => "(* ?a -1)"),
        // -x|~(x|~(2*x))
        rewrite!("disj_conj_identity_rule_3"; "(| (* ?a -1) (~ (| ?a (~ (* ?a 2)))))" => "(* ?a -1)"),
        // -x|~(x|~(-2*x))
        rewrite!("disj_conj_identity_rule_4"; "(| (* ?a -1) (~ (| ?a (~ (* ?a -2)))))" => "(* ?a -1)"),
        // __check_disj_conj_identity_rule_2
        // x|(-~x&2*~x)
        rewrite!("disj_conj_identity_rule_2_1"; "(| ?x (& (* (~ ?x) -1) (* 2 (~ ?x))))" => "?x"),
        // x|(-~x&-2*~x)
        rewrite!("disj_conj_identity_rule_2_2"; "(| ?x (& (* (~ ?x) -1) (* (* 2 -1) (~ ?x))))" => "?x"),
        // __check_conj_disj_identity_rule
        // x&(-~(2*x)|-~x)
        rewrite!("conj_disj_identity_rule_1"; "(& ?x (| (* (~ (* 2 ?x)) -1) (* (~ ?x) -1)))" => "?x"),
        // x&(~(2*~x)|-~x)
        rewrite!("conj_disj_identity_rule_2"; "(& ?x (| (~ (* 2 (~ ?x))) (* (~ ?x) -1)))" => "?x"),
        // x&(~(-2*~x)|-~x)
        // Note that while GAMBA only solves this pattern for the constant '2', it is true if 'Y' is substituted with any value.
        rewrite!("conj_disj_identity_rule_3"; "(& ?x (| (~ (* (* ?y -1) (~ ?x))) (* (~ ?x) -1)))" => "?x"),
        // __check_disj_neg_disj_identity_rule
        // x|-(-x|2*x)
        rewrite!("disj_neg_disj_identity_rule_1"; "(| ?x (* (| (* ?x -1) (* ?y ?x)) -1))" => "?x"),
        // x|-(-x|-2*x)
        rewrite!("disj_neg_disj_identity_rule_2"; "(| ?x (* (| (* ?x -1) (* (* ?y -1) ?x)) -1))" => "?x"),
        // __check_disj_sub_disj_identity_rule
        // x|(x|y)-y
        rewrite!("disj_sub_disj_identity_rule_1"; "(| ?x (+ (| ?x ?y) (* ?y -1)))" => "?x"),
        // __check_disj_sub_disj_identity_rule
        // x|x-(x&y)
        rewrite!("disj_sub_disj_identity_rule_2"; "(| ?x (+ ?x (* (& ?x ?y) -1)))" => "?x"),
        // __check_conj_add_conj_identity_rule
        // x&x+(~x&y)
        rewrite!("conj_add_conj_identity_rule"; "(& ?x (+ ?x (& (~ ?x) ?y)))" => "?x"),
        // __check_disj_disj_conj_rule
        // x|-(-y|(x&y))
        rewrite!("disj_disj_conj_rule"; "(| ?x (* (| (* ?y -1) (& ?x ?y)) -1))" => "(| ?x ?y)"),
        // __check_conj_conj_disj_rule
        // x&-(-y&(x|y))
        rewrite!("conj_conj_disj_rule"; "(& ?x (* (& (* ?y -1) (| ?x ?y)) -1))" => "(& ?x ?y)"),
        // __check_disj_disj_conj_rule_2
        // -(-x|x&y&z)|x&y
        rewrite!("disj_disj_conj_rule_2"; "(| (* (| (* ?x -1) (& (& ?x ?y) ?z)) -1) (& ?x ?y))" => "?x"),
    ]
}

pub fn read_constant(data: &MbaInfo) -> Option<i128> {
    match data.classification {
        AstClassification::Constant { value } => Some(reduce_modulo(value)),
        _ => None,
    }
}

pub fn read_known_bits(data: &MbaInfo) -> KnownBitsWrapper {
    return data.known_bits;
}
