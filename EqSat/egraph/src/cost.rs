use egg::*;

use crate::{
    abstract_interpretation::{
        compute_known_bits, create_constant_known_bits, create_empty_known_bits,
        KnownBitsTransferOpcode, KnownBitsWrapper,
    },
    analysis::{EEGraph, MbaAnalysis},
    classification::{classify, AstClassification},
    expr::Expr,
};

pub type Cost = i64;

pub fn get_cost(egraph: &EEGraph, enode: &Expr) -> Cost {
    let cost = |i: &Id| egraph[*i].data.cost;
    let res = match enode {
        Expr::Add([a, b]) | Expr::Mul([a, b]) => cost(a).saturating_add(cost(b)),
        Expr::Pow([a, b]) | Expr::And([a, b]) | Expr::Or([a, b]) | Expr::Xor([a, b]) => {
            cost(a).saturating_add(cost(b))
        }
        Expr::Neg([a]) => cost(a).saturating_add((1)),
        Expr::Constant(_) | Expr::Symbol(_) => 1,
        Expr::Ashr([a, b]) => cost(a).saturating_add(cost(b)).saturating_add(2),
        Expr::Lshr([a, b]) => cost(a).saturating_add(cost(b)).saturating_add(2),
        Expr::Shl([a, b]) => cost(a).saturating_add(cost(b)).saturating_add(2),
    };

    return res;
}

pub struct EGraphCostFn<'a> {
    pub egraph: &'a EGraph<Expr, MbaAnalysis>,
}

impl<'a> CostFunction<Expr> for EGraphCostFn<'a> {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &Expr, mut _costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let mut op_cost: usize = match enode {
            Expr::Add(_) => 2,
            Expr::Mul(_) => 2,
            Expr::Pow(_) | Expr::And(_) | Expr::Or(_) | Expr::Xor(_) => 2,
            Expr::Neg(_) => 1,
            Expr::Constant(_) | Expr::Symbol(_) => 1,
            Expr::Ashr(_) => 2,
            Expr::Lshr(_) => 2,
            Expr::Shl(_) => 2,
        };

        let class = classify(self.egraph, enode).unwrap();
        op_cost = match class {
            AstClassification::Nonlinear => op_cost + 10,
            AstClassification::Mixed => op_cost + 1,
            _ => op_cost,
        };

        let transfer = |op, a: &Id, b: &Id| -> KnownBitsWrapper {
            let lhs = self.egraph[*a].data.known_bits;
            let rhs = self.egraph[*b].data.known_bits;

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
                self.egraph[*a].data.known_bits,
                None,
            ),
            Expr::Constant(c) => create_constant_known_bits(64, reduce_modulo(*c) as u64),
            _ => create_empty_known_bits(64),
        };

        let popcount = 64 - to.num_known_bits();
        op_cost = op_cost.saturating_add(popcount as usize);

        // Compute the final cost.
        let mut res: usize = enode.fold(op_cost, |sum, id| sum.saturating_add(_costs(id)));

        return res;
    }
}

// Reduce the integer mod 2^64
pub fn reduce_modulo(n: i128) -> i128 {
    return (n as u64) as i128;
}
