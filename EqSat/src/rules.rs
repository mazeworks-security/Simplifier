use egg::{rewrite, Applier, Id, PatternAst, Subst, Symbol, Var};

use crate::simple_ast::{as_constant, AstData, EEGraph, MbaAnalysis, SimpleAst};

pub fn rule_mul_constant_to_left_1_precondition(
    c1: &str,
) -> impl Fn(&mut EEGraph, Id, &Subst) -> bool {
    let c1 = c1.parse().unwrap();
    move |egraph, _, subst| {
        let c1_value = as_constant(&egraph[subst[c1]].data);
        if c1_value.is_none() {
            return false;
        }
        return true;
    }
}

pub struct applier_rule_mul_constant_to_left_1 {
    pub c1: Var,
    pub a: Var,
}
impl Applier<SimpleAst, MbaAnalysis> for applier_rule_mul_constant_to_left_1 {
    fn apply_one(
        &self,
        egraph: &mut EEGraph,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<SimpleAst>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let c1_id = subst[self.c1];
        let a_id = subst[self.a];
        let t2 = egraph.add(SimpleAst::Mul([c1_id, a_id]));

        if egraph.union(eclass, t2) {
            vec![t2]
        } else {
            vec![]
        }
    }
}

fn hello() {
    // mul-constant-to-left-1: (a:i64*Const(c1)) => (Const(c1)*a:i64)
    rewrite!("mul-constant-to-left-1"; "(** ?a ?c1)" => {
    applier_rule_mul_constant_to_left_1 {
        c1 : "?c1".parse().unwrap(),
        a : "?a".parse().unwrap(),
    }
} if (rule_mul_constant_to_left_1_precondition("?c1")));
}
