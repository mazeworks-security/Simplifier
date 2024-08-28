use crate::{
    analysis::MbaAnalysis,
    cost::EGraphCostFn,
    rules::make_simplification_rules,
    time::{Duration, Instant},
};

use egg::*;
use expr::Expr;
use std::time;

mod abstract_interpretation;
mod analysis;
mod classification;
mod cost;
mod expr;
mod ffi_utils;
mod rules;

fn main() {
    let expr = read_expr_from_args();
    println!("Attempting to simplify expression: {}", expr);

    let mut string = expr.as_str().to_owned();
    for i in 0..10 {
        let num = 1000;
        println!("deobfuscating");
        string = simplify_via_eqsat(string.clone().as_ref(), Some(num)).clone();
    }

    println!("Final result: {}", string);
}

fn read_expr_from_args() -> String {
    let mut args = std::env::args().skip(1);

    if let Some(next) = args.next() {
        next
    } else {
        std::fs::read_to_string("test-input.txt").unwrap()
    }
}

/// parse an expression, simplify it using egg, and pretty print it back out
pub fn simplify_via_eqsat(s: &str, milliseconds: Option<u64>) -> String {
    let expr: RecExpr<Expr> = s.parse().unwrap();

    let ms = if milliseconds.is_some() {
        milliseconds.unwrap()
    } else {
        500
    };
    // Create the runner. You can enable explain_equivalence to explain the equivalence,
    // but it comes at a severe performance penalty.
    let explain_equivalence = false;
    let mut runner: Runner<Expr, MbaAnalysis> = Runner::default()
        .with_time_limit(Duration::from_millis(ms))
        .with_scheduler(
            BackoffScheduler::default()
                .with_ban_length(5)
                .with_initial_match_limit(1_000_00),
        )
        .with_node_limit(1000000 * 10)
        .with_iter_limit(500 * 10);

    if explain_equivalence {
        runner = runner.with_explanations_enabled();
    }

    runner = runner.with_expr(&expr);

    let rules = make_simplification_rules();

    let start = Instant::now();
    runner = runner.run(&rules);

    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let (best_cost, best) = if true {
        let mut cost_func = EGraphCostFn {
            egraph: &runner.egraph,
        };

        let extractor = Extractor::new(&runner.egraph, cost_func);

        let res = extractor.find_best(root);

        res
    } else {
        let extractor = Extractor::new(&runner.egraph, AstSize);
        extractor.find_best(root)
    };

    let best = best.to_string();
    let duration = start.elapsed();
    best
}
