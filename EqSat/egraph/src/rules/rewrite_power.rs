use egg::*;

use crate::{
    analysis::{EEGraph, MbaAnalysis},
    Expr,
};

use super::read_constant;

#[derive(Debug)]
pub struct RewritePowerApplier {
    pub a: Var,
    pub b: Var,
    pub exponent: Var,
}

impl Applier<Expr, MbaAnalysis> for RewritePowerApplier {
    fn apply_one(
        &self,
        egraph: &mut EEGraph,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<Expr>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let exponent_id = subst[self.exponent];
        let exponent_data = &egraph[exponent_id].data;
        let exponent_constant = read_constant(exponent_data).unwrap();

        let a_id = subst[self.a];
        let a_data = &egraph[a_id].data;
        let a_constant = read_constant(a_data).unwrap();

        let b_id = subst[self.b];

        let const_value = if let Ok(exponent_constant) = u32::try_from(exponent_constant) {
            a_constant.pow(exponent_constant)
        } else {
            return Vec::new();
        };

        let const_id = egraph.add(Expr::Constant(const_value));
        let id = egraph.add(Expr::Pow([b_id, exponent_id]));
        let new_expr = egraph.add(Expr::Mul([id, const_id]));

        if egraph.union(eclass, new_expr) {
            vec![new_expr]
        } else {
            vec![]
        }
    }
}

pub fn can_rewrite_power(
    a: &'static str,
    exponent: &'static str,
) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let a = a.parse().unwrap();
    let b = "?b".parse().unwrap();
    let exponent = exponent.parse().unwrap();

    move |egraph, _, subst| {
        let a = &egraph[subst[a]].data;
        let b = &egraph[subst[b]].data;
        let exponent = &egraph[subst[exponent]].data;
        read_constant(a).is_some()
            && read_constant(b).is_none()
            && read_constant(exponent).is_some()
    }
}
