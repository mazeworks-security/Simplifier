use egg::*;

use crate::{
    analysis::{EEGraph, MbaAnalysis},
    Expr,
};

use super::read_constant;

#[derive(Debug)]
pub struct FactorIntegerGcdApplier {
    pub x_factor: &'static str,
    pub y_factor: &'static str,
}

// Given (const_1 * x) + (const_2 * y), try to factor out the greatest common constant denominator.
// E.g. (9 * x) + (-9 * y) becomes 9 * (x + -y)
// E.g. (3 * x) + (9 * y) becomes 3 * (x + 9y)
impl Applier<Expr, MbaAnalysis> for FactorIntegerGcdApplier {
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

        // Compute the GCD.
        let gcd = gcd_of_two_numbers(x_factor_constant, y_factor_constant);
        let gcd_id = egraph.add(Expr::Constant(gcd));

        // Compute the factored expression.
        let lhs = without_gcd(egraph, x_id, x_factor_constant, gcd);
        let rhs = without_gcd(egraph, y_id, y_factor_constant, gcd);
        let added = egraph.add(Expr::Add([lhs, rhs]));
        let factored = egraph.add(Expr::Mul([gcd_id, added]));

        if egraph.union(eclass, factored) {
            vec![factored]
        } else {
            vec![]
        }
    }
}

fn without_gcd(egraph: &mut EEGraph, x: Id, x_factor_constant: i128, gcd: i128) -> egg::Id {
    let factor_without_gcd = x_factor_constant / gcd;
    // If we've completely factored out the constant then remove it.
    if factor_without_gcd == 1 {
        return x;
    // Otherwise we couldn't factor out the constant completely.
    } else {
        let without_gcd_id = egraph.add(Expr::Constant(factor_without_gcd));
        return egraph.add(Expr::Mul([x, without_gcd_id]));
    }
}

pub fn has_significant_gcd(var: &str, var2: &str) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let var2: Var = var2.parse().unwrap();

    move |egraph, _, subst| {
        let v1 = read_constant(&egraph[subst[var]].data);
        let v2 = read_constant(&egraph[subst[var2]].data);
        if v1.is_none() || v2.is_none() {
            return false;
        }
        if (v1.unwrap() == 0 || v2.unwrap() == 0) {
            return false;
        }

        let minus_one = 18446744073709551615;
        if (v1.unwrap() == minus_one || v2.unwrap() == minus_one) {
            return false;
        }

        let gcd = gcd_of_two_numbers(v1.unwrap(), v2.unwrap());
        let result = gcd != 0 && gcd != 1 && gcd != minus_one;
        if (gcd == 2) {
            return false;
        }

        return result;
    }
}

/// returns the greatest common divisor of n numbers
pub fn gcd(nums: &[i128]) -> i128 {
    if nums.len() == 1 {
        return nums[0];
    }
    let a = nums[0];
    let b = gcd(&nums[1..]);
    gcd_of_two_numbers(a, b)
}

fn gcd_of_two_numbers(a: i128, b: i128) -> i128 {
    if b == 0 {
        return a;
    }
    gcd_of_two_numbers(b, a % b)
}
