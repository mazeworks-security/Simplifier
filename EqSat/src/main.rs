#![allow(unused)]

use egg::{CostFunction, EGraph, Extractor, Id, Language, RecExpr};
use rand::Rng;

// use egraph::simplify_via_eqsat;
use libc::c_char;
use std::{
    collections::HashMap,
    ffi::{CStr, CString},
    fs::{self, File},
    io::{BufRead, BufReader},
    path::Path,
    time::Instant,
};

use crate::{
    mba::Context as MbaContext,
    simple_ast::{
        recursive_simplify, Arena, AstPrinter, Context as Ctx, EEGraph, MbaAnalysis, Predicate,
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
        let op_cost = 1;
        enode.fold(op_cost, |sum, i| sum + _costs(i))
    }
}

fn main() {
    let mut arena = Arena::new();

    let mut ctx = Context { arena };

    /*
    let x = ctx.arena.symbol_with_name("x".to_string(), 8);
    let y = ctx.arena.symbol_with_name("y".to_string(), 8);
    let add = ctx.arena.add(x, y);
    */

    let analysis = MbaAnalysis {};
    let mut egraph = EEGraph::new(analysis);

    let w = 32;
    let x = SimpleAst::Symbol { id: 0, width: w };
    let x_id = egraph.add(x);
    let y = SimpleAst::Symbol { id: 1, width: w };
    let y_id = egraph.add(y);
    let constant_id = egraph.add(SimpleAst::Constant { c: 10000, width: w });

    let sum = SimpleAst::Add([x_id, y_id]);
    let mut sum_id = egraph.add(sum.clone());

    sum_id = egraph.add(SimpleAst::Add([sum_id, constant_id]));

    sum_id = egraph.add(SimpleAst::Zext { a: sum_id, to: 64 });

    sum_id = egraph.add(SimpleAst::ICmp {
        predicate: Predicate::Eq,
        children: [x_id, y_id],
    });

    let cost_func = EGraphCostFn { egraph: &egraph };
    let extractor = Extractor::new(&egraph, cost_func);

    let res = extractor.find_best(sum_id);

    let sum_str = res.1.to_string();
    dbg!("Extracted {}", sum_str.clone());

    let parse: RecExpr<SimpleAst> = sum_str.clone().to_owned().parse().unwrap();
    dbg!("Parsed {}", parse.to_string());

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
