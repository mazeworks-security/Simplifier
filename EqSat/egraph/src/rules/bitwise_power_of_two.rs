use egg::*;

use crate::{
    analysis::{EEGraph, MbaAnalysis},
    expr::Expr,
};

use super::read_constant;

#[derive(Debug)]
pub struct BitwisePowerOfTwoFactorApplier {
    pub x_factor: &'static str,
    pub y_factor: &'static str,
}

// Given an AND, XOR, or OR, of `2*x&2*y`, where a power of two can be factored
// out of its children, transform it into `2*(x&y)`.
// TODO: As of right now this transform only works if the constant multiplier is a power of 2,
// but it should work if any power of two can be factored out of the immediate multipliers.
impl Applier<Expr, MbaAnalysis> for BitwisePowerOfTwoFactorApplier {
    fn apply_one(
        &self,
        egraph: &mut EEGraph,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<Expr>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Get the eclass, expression, and of the expressions relating to X.
        let x_id = subst["?x".parse().unwrap()];

        let x_factor_data = &egraph[subst[self.x_factor.parse().unwrap()]].data;
        let x_factor_constant = read_constant(x_factor_data).unwrap();

        // Get the eclass, expression, and of the expressions relating to X.
        let y_id = subst["?y".parse().unwrap()];

        let y_factor_data = &egraph[subst[self.y_factor.parse().unwrap()]].data;
        let y_factor_constant = read_constant(y_factor_data).unwrap();

        let min = x_factor_constant.min(y_factor_constant);
        let min_id = egraph.add(Expr::Constant(min));
        let max = x_factor_constant.max(y_factor_constant);

        // Here we're dealing with expressions like "4*x&4*y" and ""4*x&8*y",
        // where x_factor and y_factor are the constant multipliers.
        // If the constant multipliers are the same, then for example
        // we can factor `4*x&4*y` into `4*(x&y)`.
        let factored: Id = if min == max {
            // Create an egraph node for (x & y).
            let anded = egraph.add(Expr::And([x_id, y_id]));

            // Create an egraph node for factored_out_constant * (x & y);
            egraph.add(Expr::Mul([min_id, anded]))
        }
        // If the factors are not equal(e.g. "4*x&8*y"), then we need to factor
        // out only the minimum factor, giving us something like "4*(x&2*y)".
        else {
            let remaining_factor = egraph.add(Expr::Constant(max / min));

            // If x has the large factor then the RHS becomes ((max/min) * x) & y;
            let rhs: Id = if x_factor_constant == max {
                let x_times_remaining_factor = egraph.add(Expr::Mul([remaining_factor, x_id]));
                egraph.add(Expr::And([x_times_remaining_factor, y_id]))
            // If y has the large factor then the RHS becomes ((max/min) * y) & x;
            } else {
                let y_times_remaining_factor = egraph.add(Expr::Mul([remaining_factor, y_id]));
                egraph.add(Expr::And([y_times_remaining_factor, x_id]))
            };

            // Create the final expression of (min * factored_rhs);
            egraph.add(Expr::Mul([min_id, rhs]))
        };

        if egraph.union(eclass, factored) {
            vec![factored]
        } else {
            vec![]
        }
    }
}

pub fn is_power_of_two(var: &str, var2: &str) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let var2: Var = var2.parse().unwrap();

    move |egraph, _, subst| {
        let v1 = if let Some(c) = read_constant(&egraph[subst[var]].data) {
            c & (c - 1) == 0 && c != 0
        } else {
            false
        };

        let v2 = if let Some(c) = read_constant(&egraph[subst[var2]].data) {
            c & (c - 1) == 0 && c != 0
        } else {
            false
        };

        v1 && v2
    }
}
