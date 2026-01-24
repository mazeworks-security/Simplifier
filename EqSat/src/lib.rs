#![allow(unused)]

use ahash::AHashMap;
use egg::{BackoffScheduler, CostFunction, EGraph, Extractor, Id, Language, RecExpr, Runner};
use rand::Rng;

// use egraph::simplify_via_eqsat;
use libc::c_char;
use std::{
    collections::HashMap,
    ffi::{CStr, CString},
    fs::{self, File},
    io::{BufRead, BufReader},
    path::Path,
    time::{Duration, Instant},
};

use crate::{
    mba::Context as MbaContext,
    rules::get_generated_rules,
    simple_ast::{
        add_to_egraph, from_rec_expr, recursive_simplify, Arena, AstPrinter, Context as Ctx,
        EEGraph, MbaAnalysis, Predicate,
    },
    truth_table_database::TruthTableDatabase,
};

// use egg::*;
use simple_ast::{marshal_string, AstData, AstIdx, Context, Empty, SimpleAst};

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

mod assembler;
mod known_bits;
mod mba;
mod rules;
mod simple_ast;
mod truth_table_database;

#[no_mangle]
pub extern "C" fn SimplifyViaEqsat(s: *const c_char, ms: u64) -> *mut c_char {
    /*
    let str = marshal_string(s).to_owned();

    let res = simplify_via_eqsat(&str, Some(ms));
    unsafe {
        return CString::new(res).unwrap().into_raw();
    }
    */

    panic!("Disabled for now");
}

fn read_expr_from_args() -> String {
    let mut args = std::env::args().skip(1);

    if let Some(next) = args.next() {
        next
    } else {
        std::fs::read_to_string("test-input.txt").unwrap()
    }
}

pub struct EGraphCostFn<'a> {
    pub egraph: &'a EGraph<SimpleAst, MbaAnalysis>,
}

impl<'a> CostFunction<SimpleAst> for EGraphCostFn<'a> {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &SimpleAst, mut _costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            SimpleAst::Add(_) => 1,
            SimpleAst::Mul(_) => 1,
            SimpleAst::Pow(_) => 5,
            SimpleAst::And(_) => 1,
            SimpleAst::Or(_) => 1,
            SimpleAst::Xor(_) => 1,
            SimpleAst::Neg(_) => 1,
            SimpleAst::Lshr(_) => 6,
            SimpleAst::Constant { c, width } => 1,
            SimpleAst::Symbol { id, width } => 1,
            SimpleAst::Zext(_) => 1,
            SimpleAst::Trunc(_) => 5,
            SimpleAst::ICmp {
                predicate,
                children,
            } => 6,
            SimpleAst::Select { children } => 6,
            SimpleAst::Extract(_) => 1,
            SimpleAst::Concat(_) => 1,
            SimpleAst::Carry(_) => 1,
        };
        enode.fold(op_cost, |sum, i| sum + _costs(i))
    }
}

fn main() {
    let parseeee = "(^ (\"icmp ==\" (& ?a1 ?c1) ?mconst0) (\"icmp !=\" (& ?a2 ?c1) ?mconst0))"
        .parse::<egg::Pattern<SimpleAst>>()
        .unwrap();
    dbg!("Parsed {}", parseeee.to_string());

    return;

    let mut arena = Arena::new();

    let mut ctx = Context { arena };

    /*
    let x = ctx.arena.symbol_with_name("x".to_string(), 8);
    let y = ctx.arena.symbol_with_name("y".to_string(), 8);
    let add = ctx.arena.add(x, y);
    */
    let w = 32;
    //let x = SimpleAst::Symbol { id: 0, width: w };
    //let x_id = ctx.arena.insert_node(x);
    let x_id = ctx.arena.symbol_with_name("x".to_string(), w);
    //let y = SimpleAst::Symbol { id: 1, width: w };
    let y = SimpleAst::Constant { c: 1111, width: w };
    let y_id = ctx.arena.insert_node(y);
    let constant_id = ctx.arena.insert_node(SimpleAst::Constant {
        c: 234234432,
        width: w,
    });

    let c2_id = ctx.arena.insert_node(SimpleAst::Constant {
        c: 234243,
        width: w,
    });

    let sum = SimpleAst::Add([x_id, y_id]);
    let mut sum_id = ctx.arena.insert_node(sum.clone());

    //sum_id = ctx.arena.insert_node(SimpleAst::Add([x_id, constant_id]));

    sum_id = ctx.arena.insert_node(SimpleAst::Mul([x_id, constant_id]));

    sum_id = ctx.arena.insert_node(SimpleAst::Mul([sum_id, c2_id]));

    let analysis = MbaAnalysis {};
    let mut egraph = EEGraph::new(analysis);
    let mut idx_to_eclass = AHashMap::new();
    let input_id = add_to_egraph(&ctx, &mut egraph, sum_id, &mut idx_to_eclass);

    /*
    sum_id = egraph.add(SimpleAst::Zext { a: sum_id, to: 64 });

    sum_id = egraph.add(SimpleAst::ICmp {
        predicate: Predicate::Eq,
        children: [x_id, y_id],
    });
    */

    /*
    let cost_func = EGraphCostFn { egraph: &egraph };
    let extractor = Extractor::new(&egraph, cost_func);

    let res = extractor.find_best(sum_id);

    let sum_str = res.1.to_string();
    dbg!("Extracted {}", sum_str.clone());

    let parse: RecExpr<SimpleAst> = sum_str.clone().to_owned().parse().unwrap();
    dbg!("Parsed {}", parse.to_string());
    */

    let ms = 5000;
    let mut runner: Runner<SimpleAst, MbaAnalysis> = Runner::default()
        .with_time_limit(Duration::from_millis(ms))
        .with_scheduler(
            BackoffScheduler::default()
                .with_ban_length(5)
                .with_initial_match_limit(1_000_00),
        )
        .with_node_limit(1000000 * 10)
        .with_iter_limit(500 * 10)
        .with_egraph(egraph);

    let rules = get_generated_rules();
    runner = runner.run(&rules);

    let cost_func = EGraphCostFn {
        egraph: &runner.egraph,
    };
    let extractor = Extractor::new(&runner.egraph, cost_func);

    let res = extractor.find_best(input_id);

    let sum_str = res.1.to_string();
    dbg!("Extracted {}", sum_str.clone());

    let parse: RecExpr<SimpleAst> = sum_str.clone().to_owned().parse().unwrap();
    dbg!("Parsed {}", parse.to_string());

    let from_egraph = from_rec_expr(&mut ctx, &runner.egraph, &mut parse.clone());

    //let printer = AstPrinter { ctx: &ctx };
    let bar = AstPrinter::print(&ctx, ctx.arena.get_node(from_egraph));
    println!("In ctx: {}", bar);
    /*
    dbg!("{}, {}, {}", x_id, y_id, constant_id, sum_id);
    let sum_str = sum.clone().to_string();

    println!("len: {}", );

    println!("{}", sum_str);
    //dbg!("Sum str: {}", sum_str.clone());

    //let x_id = egraph.add(x.clone());
    //dbg!("x {}", x.clone().to_string());

    let parse: RecExpr<SimpleAst> = sum_str.clone().to_owned().parse().unwrap();
    dbg!("Parsed {}", parse.to_string());
    */
}
