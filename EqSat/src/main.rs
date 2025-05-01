#![allow(unused)]

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
    simple_ast::{recursive_simplify, Arena, AstPrinter, Context as Ctx},
    truth_table_database::TruthTableDatabase,
};

// use egg::*;
use simple_ast::{marshal_string, AstData, AstIdx, SimpleAst};

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

mod mba;
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

pub fn Pow2(mut base: u64, mut exp: u64) -> u64 {
    let mut res: u64 = 1;
    while exp != 0 {
        if (exp & 1) != 0 {
            res = res.wrapping_mul(base);
        }
        exp >>= 1;
        base = base.wrapping_mul(base);
    }

    return res;
}

fn main() {}
