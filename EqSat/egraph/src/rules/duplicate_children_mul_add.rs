use egg::*;

use crate::{
    analysis::{EEGraph, MbaAnalysis},
    expr::Expr,
};

use super::{read_constant, read_known_bits};

#[derive(Debug)]
pub struct DuplicateChildrenMulAddApplier {
    pub const_factor: &'static str,
    pub x_factor: &'static str,
}

impl Applier<Expr, MbaAnalysis> for DuplicateChildrenMulAddApplier {
    fn apply_one(
        &self,
        egraph: &mut EEGraph,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<Expr>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let new_const_expr = &egraph[subst[self.const_factor.parse().unwrap()]].data;

        let const_factor = read_constant(new_const_expr).unwrap();

        let x = subst[self.x_factor.parse().unwrap()];

        let new_const = egraph.add(Expr::Constant(const_factor + 1));
        let new_expr = egraph.add(Expr::Mul([new_const, x]));

        if egraph.union(eclass, new_expr) {
            vec![new_expr]
        } else {
            vec![]
        }
    }
}

pub fn is_const(var: &str) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();

    move |egraph, _, subst| read_constant(&egraph[subst[var]].data).is_some()
}

pub fn are_const(var1: &str, var2: &str) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var1 = var1.parse().unwrap();
    let var2 = var2.parse().unwrap();
    move |egraph, _, subst| {
        read_constant(&egraph[subst[var1]].data).is_some()
            && read_constant(&egraph[subst[var2]].data).is_some()
    }
}

pub fn are_minus_const(var1: &str, var2: &str) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var1 = var1.parse().unwrap();
    let var2 = var2.parse().unwrap();
    move |egraph, _, subst| {
        let c1 = read_constant(&egraph[subst[var1]].data);
        let c2 = read_constant(&egraph[subst[var2]].data);
        if (c1.is_none() || c2.is_none()) {
            return false;
        }

        return c2.unwrap() == -c1.unwrap();
    }
}

pub fn are_disjoint_const(var1: &str, var2: &str) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var1 = var1.parse().unwrap();
    let var2 = var2.parse().unwrap();
    move |egraph, _, subst| {
        let c1 = read_constant(&egraph[subst[var1]].data);
        let c2 = read_constant(&egraph[subst[var2]].data);
        if (c1.is_none() || c2.is_none()) {
            return false;
        }

        return (c1.unwrap() & c2.unwrap()) == 0;
    }
}

pub fn are_disjoint_known_bits(
    var1: &str,
    var2: &str,
) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var1 = var1.parse().unwrap();
    let var2 = var2.parse().unwrap();
    move |egraph, _, subst| {
        let c1 = read_known_bits(&egraph[subst[var1]].data);
        let c2 = read_known_bits(&egraph[subst[var2]].data);

        // Return if c1 and c2 are disjoint
        return c1.no_common_bits_set(c2);
    }
}

pub fn are_subset_known_bits(var1: &str, var2: &str) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var1 = var1.parse().unwrap();
    let var2 = var2.parse().unwrap();
    move |egraph, _, subst| {
        let c1 = read_known_bits(&egraph[subst[var1]].data);
        let c2 = read_known_bits(&egraph[subst[var2]].data);

        // Return if c1 and c2 are disjoint
        return c1.is_subset_of_this(c2);
    }
}

pub fn are_negated_const(var1: &str, var2: &str) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var1 = var1.parse().unwrap();
    let var2 = var2.parse().unwrap();
    move |egraph, _, subst| {
        let c1 = read_constant(&egraph[subst[var1]].data);
        let c2 = read_constant(&egraph[subst[var2]].data);
        if (c1.is_none() || c2.is_none()) {
            return false;
        }

        let c1 = c1.unwrap();
        let c2 = c2.unwrap();
        let negated = (((!c1) as u64) as u128) as i128;
        return c2 == negated;
    }
}

pub fn const_a_contains_b(var1: &str, var2: &str) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var1 = var1.parse().unwrap();
    let var2 = var2.parse().unwrap();
    move |egraph, _, subst| {
        let c1 = read_constant(&egraph[subst[var1]].data);
        let c2 = read_constant(&egraph[subst[var2]].data);
        if (c1.is_none() || c2.is_none()) {
            return false;
        }

        return (c1.unwrap() & c2.unwrap()) == c2.unwrap();
    }
}

pub fn is_negative_const(var: &str) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();

    move |egraph, _, subst| {
        let maybe_const = read_constant(&egraph[subst[var]].data);
        if maybe_const.is_none() {
            return false;
        }

        let constant = maybe_const.unwrap();
        if (constant.is_negative()) {
            return true;
        }

        return false;
    }
}
