#![feature(generic_const_exprs)]
#![feature(const_convert)]
#![feature(const_index)]
#![allow(incomplete_features)]
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
    isle_rules::Context as MbaContext,
    egraph_rules::get_generated_rules,
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
mod fbgb;


mod known_bits;

mod linalg;
mod simple_ast;
mod truth_table_database;

#[path = "dsl/isle_rules.rs"]
mod isle_rules;
#[path = "dsl/egraph_rules.rs"]
mod egraph_rules;
#[path = "dsl/isle_macros.rs"]
mod isle_macros;



fn main() {}