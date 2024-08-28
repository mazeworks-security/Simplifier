use std::collections::HashSet;

use egg::*;

use crate::{
    abstract_interpretation::KnownBitsWrapper,
    analysis::{reduce_modulo, try_fold_constant, EEGraph},
    cost::Cost,
    expr::Expr,
};

#[derive(Debug, Clone, Copy)]
pub enum AstClassification {
    Unknown,
    Constant { value: i128 },
    Bitwise,
    Linear { is_variable: bool },
    Nonlinear,
    Mixed,
}

#[derive(Debug, Clone)]
pub struct MbaInfo {
    pub classification: AstClassification,

    // If a node was constant folded during analysis, this was the result.
    pub const_fold: Option<i128>,

    pub cost: Cost,

    pub known_bits: KnownBitsWrapper,
}

impl MbaInfo {
    pub fn new(
        classification: AstClassification,
        const_fold: Option<i128>,
        cost: Cost,
        known_bits: KnownBitsWrapper,
    ) -> Self {
        Self {
            classification,
            const_fold,
            cost,
            known_bits,
        }
    }
}

pub fn classify(egraph: &EEGraph, enode: &Expr) -> Option<AstClassification> {
    let op = |i: &Id| egraph[*i].data.classification;

    // If we have any operation that may be folded into a constant(e.g. x + 0, x ** 0), then do it.
    if let Some(const_folded) = try_fold_constant(egraph, enode) {
        return Some(AstClassification::Constant {
            value: reduce_modulo(const_folded),
        });
    }

    // Otherwise const folding has failed. Now we need to classify it.
    let result: AstClassification = match enode {
        Expr::Constant(def) => AstClassification::Constant {
            value: reduce_modulo(*def),
        },
        Expr::Symbol(..) => AstClassification::Linear { is_variable: true },
        Expr::Pow(..) => AstClassification::Nonlinear,
        Expr::Mul([a, b]) => {
            // At this point constant propagation has handled all cases where two constant children are used.
            // So now we only have to handle the other cases. First we start by checking the classification of the other(non constant) child.
            let other = get_non_constant_child_classification(op(a), op(b));

            let result = match other {
                Some(AstClassification::Unknown) => {
                    unreachable!("Ast classification cannot be unknown.")
                }
                Some(AstClassification::Constant { .. }) => unreachable!(
                    "Constant propagation should have folded multiplication of constants."
                ),
                // const * bitwise = mixed expression
                Some(AstClassification::Bitwise) => AstClassification::Mixed,
                // const * linear = linear
                Some(AstClassification::Linear { .. }) => {
                    AstClassification::Linear { is_variable: false }
                }
                // const * nonlinear = nonlinear
                Some(AstClassification::Nonlinear) => AstClassification::Nonlinear,
                // const * mixed(bitwise and arithmetic) = mixed
                Some(AstClassification::Mixed) => AstClassification::Mixed,
                // If neither operand is a constant then the expression is not linear.
                None => AstClassification::Nonlinear,
            };

            return Some(result);
        }

        Expr::Add([a, b]) => {
            // Adding any operand (A) to any non linear operand (B) is always non linear.
            let children = [op(a), op(b)];
            if children
                .into_iter()
                .any(|x| matches!(x, AstClassification::Nonlinear))
            {
                return Some(AstClassification::Nonlinear);
            };

            // At this point we've established (above^) that there are no nonlinear children.
            // This leaves potentially constant, linear, bitwise, and mixed expressions left.
            // So now we check if either operand is mixed(bitwise + arithmetic) or bitwise.
            // In both cases, adding anything to a mixed or bitwise expression will be considered a mixed expression.
            if children
                .into_iter()
                .any(|x| matches!(x, AstClassification::Mixed | AstClassification::Bitwise))
            {
                return Some(AstClassification::Mixed);
            };

            // Now an expression is either a constant or a linear child.
            // If any child is linear then we consider this to be a linear arithmetic expression.
            // Note that constant folding has already eliminated addition of constants.
            if children.into_iter().any(|x| match x {
                AstClassification::Linear { .. } => true,
                AstClassification::Bitwise => false,
                _ => false,
            }) {
                return Some(AstClassification::Linear {
                    is_variable: (false),
                });
            };

            // This should never happen.
            unreachable!()
        }
        Expr::Neg([a]) => classify_bitwise(op(a), None),
        Expr::And([a, b]) => classify_bitwise(op(a), Some(op(b))),
        Expr::Or([a, b]) => classify_bitwise(op(a), Some(op(b))),
        Expr::Xor([a, b]) => classify_bitwise(op(a), Some(op(b))),
        Expr::Ashr(_) => AstClassification::Nonlinear,
        Expr::Lshr(_) => AstClassification::Nonlinear,
        Expr::Shl(_) => AstClassification::Nonlinear,
    };

    Some(result)
}

fn classify_bitwise(a: AstClassification, b: Option<AstClassification>) -> AstClassification {
    // TODO: Throw if we see negation with a constant, that should be fixed.
    let children = if let Some(maybe_b) = b {
        vec![a, maybe_b]
    } else {
        vec![a]
    };

    // Check if the expression contains constants or arithmetic expressions.
    let contains_constant_or_arithmetic = children.iter().any(|x| match x {
        AstClassification::Constant { .. } => true,
        // We only want to match linear arithmetic expressions - variables are excluded here.
        AstClassification::Linear { is_variable } => !*is_variable,
        _ => false,
    });

    // Check if the expression contains constants or arithmetic expressions.
    let contains_mixed_or_non_linear = children
        .iter()
        .any(|x| matches!(x, AstClassification::Mixed | AstClassification::Nonlinear));

    // Bitwise expressions are considered to be nonlinear if they contain constants,
    // arithmetic(linear) expressions, or non linear subexpressions.
    if contains_constant_or_arithmetic || contains_mixed_or_non_linear {
        return AstClassification::Nonlinear;
    } else if children.iter().any(|x: &AstClassification| match x {
        AstClassification::Linear { is_variable } => !*is_variable,
        AstClassification::Mixed => true,
        _ => false,
    }) {
        return AstClassification::Mixed;
    }

    // If none of the children are nonlinear or arithmetic then this is a pure
    // bitwise expression.
    AstClassification::Bitwise
}

// If either one of the children is a constant, return the other one.
fn get_non_constant_child_classification(
    a: AstClassification,
    b: AstClassification,
) -> Option<AstClassification> {
    let mut const_child: Option<AstClassification> = None;
    let mut other_child: Option<AstClassification> = None;
    if matches!(a, AstClassification::Constant { .. }) {
        const_child = Some(a);
    } else {
        other_child = Some(a);
    }

    if matches!(b, AstClassification::Constant { .. }) {
        const_child = Some(b);
    } else {
        other_child = Some(b);
    }

    const_child?;

    other_child
}
