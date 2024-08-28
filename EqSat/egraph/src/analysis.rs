use crate::{
    abstract_interpretation::{
        are_known_bits_equal, compute_known_bits, create_constant_known_bits,
        create_empty_known_bits, union_known_bits, KnownBitsTransferOpcode, KnownBitsWrapper,
    },
    classification::{classify, AstClassification, MbaInfo},
    cost::{get_cost, EGraphCostFn},
    expr::Expr,
};

use egg::*;

pub type EEGraph = egg::EGraph<Expr, MbaAnalysis>;
pub type Rewrite = egg::Rewrite<Expr, MbaAnalysis>;

// Since Egg only supports a single analysis class per egraph,
// we must perform multiple analyses at once. Namely constant folding, classification(e.g., "is this mba linear?"), and known bits analysis.
#[derive(Default)]
pub struct MbaAnalysis;
impl Analysis<Expr> for MbaAnalysis {
    type Data = MbaInfo;

    fn make(egraph: &mut EEGraph, enode: &Expr) -> Self::Data {
        let transfer = |op, a: &Id, b: &Id| -> KnownBitsWrapper {
            let lhs = egraph[*a].data.known_bits;
            let rhs = egraph[*b].data.known_bits;

            compute_known_bits(op, lhs, Some(rhs))
        };

        let to = match enode {
            Expr::Add([a, b]) => transfer(KnownBitsTransferOpcode::Add, a, b),
            Expr::Mul([a, b]) => transfer(KnownBitsTransferOpcode::Mul, a, b),
            Expr::Shl([a, b]) => transfer(KnownBitsTransferOpcode::Shl, a, b),
            Expr::And([a, b]) => transfer(KnownBitsTransferOpcode::And, a, b),
            Expr::Or([a, b]) => transfer(KnownBitsTransferOpcode::Or, a, b),
            Expr::Xor([a, b]) => transfer(KnownBitsTransferOpcode::Xor, a, b),
            Expr::Neg([a]) => compute_known_bits(
                KnownBitsTransferOpcode::Neg,
                egraph[*a].data.known_bits,
                None,
            ),
            Expr::Constant(c) => create_constant_known_bits(64, reduce_modulo(*c) as u64),
            _ => create_empty_known_bits(64),
        };

        if let Some(cst) = to.try_as_const() {
            return MbaInfo::new(
                AstClassification::Constant {
                    value: cst as u128 as i128,
                },
                Some(cst as u128 as i128),
                1,
                to,
            );
        }

        let classification = classify(egraph, enode).unwrap();
        let cost = get_cost(egraph, enode);

        // If we classified the AST and returned a new PatternAst<Expr>, that means
        // constant folding succeeded. Now we return the newly detected
        // classification and the pattern ast
        match classification {
            AstClassification::Constant { value } => {
                return MbaInfo::new(classification, Some(value), 1, to);
            }
            _ => {}
        };

        // Otherwise we've classified the AST but there was no constant folding
        // to be performed.
        MbaInfo::new(classification, None, cost, to)
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let kb1 = to.known_bits;
        let kb2 = from.known_bits;

        // Already known
        if to.const_fold.is_some() {
            return DidMerge(false, from.const_fold.is_some() /* maybe */);
        }

        if let Some(new_cst) = from.const_fold {
            // Const in rhs, update analysis
            to.known_bits = from.known_bits;
            to.const_fold = Some(new_cst as u128 as i128);
            to.cost = 1;
            return DidMerge(true, false);
        }

        // Union until a fixedpoint is reached.
        if let Some(new) = union_known_bits(kb1, kb2) {
            to.known_bits = new;

            if let Some(cst) = new.try_as_const() {
                to.const_fold = Some(cst as u128 as i128);
                to.cost = 1;
                return DidMerge(true, true); // yep
            }

            let new_for_to = !are_known_bits_equal(new, kb1);
            let new_for_from = !are_known_bits_equal(new, kb2);
            return DidMerge(new_for_to, new_for_from);
        }

        // Otherwise no updates occurred.
        return DidMerge(false, false);
    }

    fn modify(egraph: &mut EEGraph, id: Id) {
        let expr = &egraph[id];
        if let Some(new) = &egraph[id].data.const_fold {
            let c = Expr::Constant(*new);
            let new_id = egraph.add(c);

            egraph.union(id, new_id);

            // To not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());
        }
    }
}

// Reduce the integer mod 2^64
pub fn reduce_modulo(n: i128) -> i128 {
    return (n as u64) as i128;
}

pub fn try_fold_constant(egraph: &EEGraph, enode: &Expr) -> Option<i128> {
    let x = |i: &Id| match egraph[*i].data.classification {
        AstClassification::Constant { value } => Some(reduce_modulo(value)),
        _ => None,
    };

    Some(match enode {
        Expr::Constant(c) => reduce_modulo(*c),
        Expr::Add([a, b]) => {
            let val = x(a)?.wrapping_add(x(b)?);
            reduce_modulo(val)
        }
        Expr::Mul([a, b]) => {
            let val = x(a)?.wrapping_mul(x(b)?);
            reduce_modulo(val)
        }
        Expr::Pow([a, b]) => {
            let val = x(a)?.wrapping_pow(x(b)?.try_into().unwrap());
            reduce_modulo(val)
        }
        Expr::And([a, b]) => {
            let val = x(a)? & x(b)?;
            reduce_modulo(val)
        }
        Expr::Or([a, b]) => {
            let val = x(a)? | x(b)?;
            reduce_modulo(val)
        }
        Expr::Xor([a, b]) => {
            let val = x(a)? ^ x(b)?;
            reduce_modulo(val)
        }
        Expr::Neg([a]) => {
            let val = !x(a)?;
            reduce_modulo(val)
        }
        Expr::Ashr([a, b]) => {
            let op1 = x(a)?;
            let op2 = x(b)?;
            let ashr = fold_ashr(op1, op2);
            reduce_modulo(ashr)
        }
        Expr::Lshr([a, b]) => {
            let op1 = x(a)?;
            let op2 = x(b)?;
            let ashr = fold_lshr(op1, op2);
            reduce_modulo(ashr)
        }
        Expr::Shl([a, b]) => {
            let op1 = x(a)?;
            let op2 = x(b)?;
            let ashr = fold_shl(op1, op2);
            reduce_modulo(ashr)
        }
        Expr::Symbol(_) => return None,
    })
}

fn fold_ashr(a: i128, b: i128) -> i128 {
    let ashr64 = (a as i64) >> (b as i64);
    return ashr64 as i128;
}

fn fold_lshr(a: i128, b: i128) -> i128 {
    let op1 = (a as u128) as u64;
    let op2 = (b as u128) as u64;
    let lshr64 = op1 >> op2;
    return (lshr64 as u128) as i128;
}

fn fold_shl(a: i128, b: i128) -> i128 {
    let op1 = (a as u128) as u64;
    let op2 = (b as u128) as u64;
    let shl64 = op1 << op2;
    return (shl64 as u128) as i128;
}
