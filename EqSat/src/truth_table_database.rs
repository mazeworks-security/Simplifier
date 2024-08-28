use core::num;
use std::arch::x86_64::_popcnt64;
use std::ffi::CStr;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, Read};
use std::mem::MaybeUninit;
use std::os::raw::{c_char, c_uint, c_void};
use std::path::Path;

use crate::simple_ast::{AstIdx, AstPrinter, Context, SimpleAst};

pub struct TruthTableDatabase {
    two_var_truth_table: Vec<u8>,
    three_var_truth_table: Vec<u8>,
    four_var_truth_table: Vec<u8>,
}

// Two, three, and four variable boolean truth table utility.
impl TruthTableDatabase {
    pub fn new() -> Self {
        let mut two_var_tt: Vec<u8> = Vec::new();
        Self::load_truth_table_from_bin(2, &mut two_var_tt);

        let mut three_var_tt: Vec<u8> = Vec::new();
        Self::load_truth_table_from_bin(3, &mut three_var_tt);

        let mut four_var_tt: Vec<u8> = Vec::new();
        Self::load_truth_table_from_bin(4, &mut four_var_tt);

        return TruthTableDatabase {
            two_var_truth_table: two_var_tt,
            three_var_truth_table: three_var_tt,
            four_var_truth_table: four_var_tt,
        };
    }

    fn load_truth_table_from_bin(num_vars: u64, output: &mut Vec<u8>) {
        let path = format!(
            "Minimization\\TruthTables\\{}variable_truthtable.bc",
            num_vars
        );
        let bytes = Self::get_file_as_byte_vec(&path, output);
    }

    fn get_file_as_byte_vec(filename: &String, buffer: &mut Vec<u8>) {
        let mut f = File::open(&filename).expect("no file found");
        let metadata = fs::metadata(&filename).expect("unable to read metadata");
        f.read_to_end(buffer).expect("buffer overflow");
    }

    pub fn get_truth_table_entry(
        db: &mut TruthTableDatabase,
        ctx: &mut Context,
        var_count: u32,
        vars: *const AstIdx,
        idx: usize,
    ) -> AstIdx {
        let table = match var_count {
            2 => &db.two_var_truth_table,
            3 => &db.three_var_truth_table,
            4 => &db.four_var_truth_table,
            _ => panic!("truth table database only supports 2, 3, or 4 variables!"),
        };

        // Compute the offset into the table.
        let mut offset_idx = 4 * idx;
        let mut constant: u64 = 0;
        for c in 0..4 {
            let byte = *table.get(offset_idx).unwrap();
            offset_idx += 1;

            constant |= ((byte as u64) << (c * 8));
        }

        let mut i = constant as usize;
        Self::parse_binary_boolean_func(ctx, vars, table, &mut i)
    }

    fn parse_binary_boolean_func(
        ctx: &mut Context,
        vars: *const AstIdx,
        bytes: &Vec<u8>,
        i: &mut usize,
    ) -> AstIdx {
        let this_ctx = ctx;
        let opcode = bytes.get(*i).unwrap();
        *i += 1;

        match opcode {
            2 => {
                let var_index = *bytes.get(*i).unwrap();
                *i += 1;

                unsafe { *vars.add(var_index as usize) }
            }

            4 => {
                let a = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                let b = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                this_ctx.arena.pow(a, b)
            }

            6 => {
                let a = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                let b = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                this_ctx.arena.add(a, b)
            }

            7 => {
                let a = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                let b = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                this_ctx.arena.mul(a, b)
            }

            8 => {
                let a = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                let b = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                this_ctx.arena.and(a, b)
            }

            9 => {
                let a = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                let b = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                this_ctx.arena.or(a, b)
            }

            10 => {
                let a = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                let b = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                this_ctx.arena.xor(a, b)
            }

            11 => {
                let a = Self::parse_binary_boolean_func(this_ctx, vars, bytes, i);
                this_ctx.arena.neg(a)
            }

            _ => panic!("Unrecognized opcode: {}", opcode),
        }
    }
}
