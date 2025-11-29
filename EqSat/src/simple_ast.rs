type Unit = ();

use core::num;
use std::{
    cmp,
    collections::{hash_map::Entry, HashMap, HashSet},
    f32::consts::PI,
    ffi::{CStr, CString},
    ops::Add,
    u16, u64, vec,
};

use ahash::AHashMap;
use iced_x86::{
    code_asm::{st, CodeAssembler},
    Code, Instruction, Register,
};
use libc::{c_char, c_void};
use std::marker::PhantomData;

use crate::{
    assembler::{
        self, amd64_assembler::IAmd64Assembler, fast_amd64_assembler::FastAmd64Assembler, *,
    },
    known_bits::{self, *},
    mba::{self, Context as MbaContext},
    truth_table_database::{TruthTable, TruthTableDatabase},
};

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(C)]
pub struct Empty();

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(C)]
pub struct AstIdx(pub u32);

pub struct Arena {
    pub elements: Vec<(SimpleAst, AstData)>,
    ast_to_idx: AHashMap<SimpleAst, AstIdx>,
    isle_cache: AHashMap<AstIdx, AstIdx>,

    // Map a name to it's corresponds symbol index.
    symbol_ids: Vec<(String, AstIdx)>,
    name_to_symbol: AHashMap<(String, u8), u32>,
}

impl Arena {
    pub fn new() -> Self {
        let elements = Vec::with_capacity(65536);
        let ast_to_idx = AHashMap::with_capacity(65536);
        let isle_cache = AHashMap::with_capacity(65536);

        let symbol_ids = Vec::with_capacity(255);
        let name_to_symbol = AHashMap::with_capacity(255);

        Arena {
            elements: elements,
            ast_to_idx: ast_to_idx,
            isle_cache: isle_cache,

            symbol_ids: symbol_ids,
            name_to_symbol: name_to_symbol,
        }
    }

    pub fn add(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let node = SimpleAst::Add { a, b };
        if let Some(&idx) = self.ast_to_idx.get(&node) {
            return idx;
        }

        let width = self.get_bin_width(a, b);
        let cost = self.get_bin_cost(a, b);
        let has_poly = self.union_contains_poly_part(a, b);

        // Determine the "highest" classification of the two operands, defaulting to linear.
        let d1 = self.get_data(a);
        let d2 = self.get_data(b);

        let mut max = max_class(d1.class, d2.class, AstClass::Linear);

        // If the resulting option is not linear or semilinear, we need to check if one of the operands
        // is a bitwise operation with a constant. If so, the result is semilinear.
        max = try_make_semilinear(max, d1.class, d2.class);

        let known_bits = KnownBits::add(&d1.known_bits, &d2.known_bits);

        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: max,
            known_bits: known_bits,
            imut_data: 0,
        };

        return self.add_ast_node(node, data);
    }

    pub fn mul(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let node = SimpleAst::Mul { a, b };
        if let Some(&idx) = self.ast_to_idx.get(&node) {
            return idx;
        }

        let a_value = self.get_node(a);
        let b_value = self.get_node(b);

        // Apply constant folding for 1*x and 0*x.
        let mut is_one_part_constant = false;
        if let SimpleAst::Constant { c: c1, width } = a_value {
            is_one_part_constant = true;
            if *c1 == 1 {
                return b;
            } else if *c1 == 0 {
                return self.constant(0, self.get_width(a));
            }
        // TODO: If the second part is a constant, swap the operands and apply constant folding.
        } else if let SimpleAst::Constant { c: c1, width } = b_value {
            is_one_part_constant = true;

            if *c1 == 1 {
                return a;
            } else if *c1 == 0 {
                return self.constant(0, self.get_width(a));
            }
        }

        let width = self.get_bin_width(a, b);
        let cost = self.get_bin_cost(a, b);
        // If neither operand is a constant, or either operand contains a polynomial part, the result will contain a polynomial part.
        let has_poly = !is_one_part_constant || self.union_contains_poly_part(a, b);

        // Determine the "highest" classification of the two operands, defaulting to linear.
        let d1 = self.get_data(a);
        let d2 = self.get_data(b);
        let mut max = max_class(
            d1.class,
            d2.class,
            if !is_one_part_constant {
                AstClass::Nonlinear
            } else {
                AstClass::Linear
            },
        );

        max = try_make_semilinear(max, d1.class, d2.class);
        let known_bits = KnownBits::mul(&d1.known_bits, &d2.known_bits);
        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: max,
            known_bits: known_bits,
            imut_data: 0,
        };

        return self.add_ast_node(node, data);
    }

    pub fn pow(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let op1 = self.get_node(a);
        let op2 = self.get_node(b);
        if let SimpleAst::Constant { c: c1, width } = op1 {
            if let SimpleAst::Constant { c: c2, width } = op2 {
                let result = self.constant(Pow(*c1, *c2), self.get_width(a));
                return result;
            }
        }
        let width = self.get_bin_width(a, b);
        let cost = self.get_bin_cost(a, b);
        // TODO: If we have e.g. x**3, computed known bits using repeated squaring.
        // If we have 2**y... compute knownbits for 1 << y..
        // In the multiplication constructor, look for x*(2**y) and use transfer function for x<<y instead
        let known_bits = KnownBits::empty(width);
        let data = AstData {
            width: width,
            cost: cost,
            has_poly: true,
            class: AstClass::Nonlinear,
            known_bits: known_bits,
            imut_data: 0,
        };

        return self.insert_ast_node(SimpleAst::Pow { a, b }, data);
    }

    pub fn and(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let kb = KnownBits::and(&self.get_data(a).known_bits, &self.get_data(b).known_bits);
        let data = self.compute_bitwise_data(a, b, kb);
        return self.insert_ast_node(SimpleAst::And { a, b }, data);
    }

    pub fn or(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let kb = KnownBits::or(&self.get_data(a).known_bits, &self.get_data(b).known_bits);
        let data = self.compute_bitwise_data(a, b, kb);

        return self.insert_ast_node(SimpleAst::Or { a, b }, data);
    }

    pub fn xor(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let kb = KnownBits::xor(&self.get_data(a).known_bits, &self.get_data(b).known_bits);
        let data = self.compute_bitwise_data(a, b, kb);
        return self.insert_ast_node(SimpleAst::Xor { a, b }, data);
    }

    pub fn xor_many(&mut self, nodes: &Vec<AstIdx>) -> AstIdx {
        let mut initial = nodes[0];
        for i in 1..nodes.len() {
            initial = self.xor(initial, nodes[i]);
        }

        return initial;
    }

    pub fn neg(&mut self, a: AstIdx) -> AstIdx {
        let width = self.get_width(a);
        let cost = (1 as u32).saturating_add(self.get_data(a).cost);
        let has_poly = self.get_data(a).has_poly;

        let c1 = self.get_class(a);
        let max = max_class(c1, c1, AstClass::Bitwise);
        let known_bits = KnownBits::neg(&self.get_data(a).known_bits);
        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: max,
            known_bits: known_bits,
            imut_data: 0,
        };
        return self.insert_ast_node(SimpleAst::Neg { a }, data);
    }

    pub fn lshr(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let width = self.get_width(a);
        let cost = (1 as u32).saturating_add(self.get_data(a).cost);
        let has_poly = self.get_data(a).has_poly;
        let class = AstClass::Nonlinear;

        let known_bits =
            KnownBits::lshr(&self.get_data(a).known_bits, &self.get_data(b).known_bits);
        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: class,
            known_bits: known_bits,
            imut_data: 0,
        };
        return self.insert_ast_node(SimpleAst::Lshr { a, b }, data);
    }

    pub fn zext(&mut self, a: AstIdx, width: u8) -> AstIdx {
        if let SimpleAst::Constant { c: c1, .. } = self.get_node(a) {
            let result = self.constant(*c1, width);
            return result;
        }

        let cost = (1 as u32).saturating_add(self.get_data(a).cost);
        let has_poly = self.get_has_poly(a);

        let mask = get_modulo_mask(self.get_width(a));
        let mask_node = self.constant(mask, width);
        let class = self.compute_bitwise_class(a, mask_node);
        let known_bits = KnownBits::zext(&self.get_data(a).known_bits, width as u32);
        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: class,
            known_bits: known_bits,
            imut_data: 0,
        };

        return self.insert_ast_node(SimpleAst::Zext { a, to: width }, data);
    }

    pub fn trunc(&mut self, a: AstIdx, width: u8) -> AstIdx {
        if let SimpleAst::Constant { c: c1, .. } = self.get_node(a) {
            let result = self.constant(*c1, width);
            return result;
        }

        let cost = (1 as u32).saturating_add(self.get_data(a).cost);
        let has_poly = self.get_has_poly(a);

        let mask = get_modulo_mask(width);
        let mask_node = self.constant(mask, width);
        let class = self.compute_bitwise_class(a, mask_node);
        let known_bits = KnownBits::trunc(&self.get_data(a).known_bits, width as u32);
        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: class,
            known_bits: known_bits,
            imut_data: 0,
        };

        return self.insert_ast_node(SimpleAst::Trunc { a, to: width }, data);
    }

    pub fn constant(&mut self, c: u64, width: u8) -> AstIdx {
        // Reduce the constant modulo 2**width
        let constant = get_modulo_mask(width) & c;
        let node = SimpleAst::Constant { c: constant, width };

        if let Some(&idx) = self.ast_to_idx.get(&node) {
            return idx;
        }

        let data = AstData {
            width: width,
            cost: 1,
            has_poly: false,
            class: AstClass::Bitwise,
            known_bits: KnownBits::constant(constant, width),
            imut_data: 0,
        };

        return self.add_ast_node(node, data);
    }

    pub fn symbol(&mut self, id: u32, width: u8) -> AstIdx {
        let data = AstData {
            width: width,
            cost: 1,
            has_poly: false,
            class: AstClass::Bitwise,
            known_bits: KnownBits::empty(width),
            imut_data: 0,
        };

        return self.insert_ast_node(
            SimpleAst::Symbol {
                id: id,
                width: width,
            },
            data,
        );
    }

    pub fn symbol_with_name(&mut self, name: String, width: u8) -> AstIdx {
        if let Some(&id) = self.name_to_symbol.get(&(name.clone(), width)) {
            return self.symbol_ids[id as usize].1;
        }

        // Compute an ID(index into a list of symbol names)
        let symbol_id = self.symbol_ids.len() as u32;
        self.name_to_symbol.insert((name.clone(), width), symbol_id);

        let data = AstData {
            width: width,
            cost: 1,
            has_poly: false,
            class: AstClass::Bitwise,
            known_bits: KnownBits::empty(width),
            imut_data: 0,
        };

        let symbol_ast_idx = self.insert_ast_node(
            SimpleAst::Symbol {
                id: symbol_id,
                width: width,
            },
            data,
        );
        self.symbol_ids.push((name, symbol_ast_idx));
        return symbol_ast_idx;
    }

    pub fn get_symbol_name(&self, symbol_id: u32) -> String {
        return self.symbol_ids[symbol_id as usize].0.clone();
    }

    pub fn insert_ast_node(&mut self, node: SimpleAst, data: AstData) -> AstIdx {
        if let Some(&idx) = self.ast_to_idx.get(&node) {
            return idx;
        }

        let idx = AstIdx(self.elements.len() as u32);
        self.elements.push((node.clone(), data));
        self.ast_to_idx.insert(node, idx);
        idx
    }

    pub fn add_ast_node(&mut self, node: SimpleAst, data: AstData) -> AstIdx {
        let idx = AstIdx(self.elements.len() as u32);
        self.elements.push((node.clone(), data));
        self.ast_to_idx.insert(node, idx);
        idx
    }

    #[inline(always)]
    pub fn get_node(&self, idx: AstIdx) -> &SimpleAst {
        unsafe { &self.elements.get_unchecked(idx.0 as usize).0 }
    }

    pub fn get_width(&self, idx: AstIdx) -> u8 {
        self.get_data(idx).width
    }

    pub fn get_cost(&self, idx: AstIdx) -> u32 {
        self.get_data(idx).cost
    }

    pub fn get_has_poly(&self, idx: AstIdx) -> bool {
        self.get_data(idx).has_poly
    }

    pub fn get_class(&self, a: AstIdx) -> AstClass {
        self.get_data(a).class
    }

    pub fn is_constant(&self, idx: AstIdx) -> bool {
        let ast = self.get_node(idx);
        match ast {
            SimpleAst::Constant { .. } => true,
            _ => false,
        }
    }

    pub fn get_data(&self, idx: AstIdx) -> AstData {
        unsafe { self.elements.get_unchecked(idx.0 as usize).1 }
    }

    pub fn get_data_mut(&mut self, idx: AstIdx) -> &mut AstData {
        unsafe { &mut self.elements.get_unchecked_mut(idx.0 as usize).1 }
    }

    pub fn set_data(&mut self, idx: AstIdx, data: AstData) {
        unsafe { self.elements.get_unchecked_mut(idx.0 as usize).1 = data }
    }

    pub fn get_bin_width(&self, a: AstIdx, b: AstIdx) -> u8 {
        let a_width = self.get_width(a);
        let b_width = self.get_width(b);
        if a_width != b_width {
            panic!("Width mismatch! {} != {}", a_width, b_width);
        }

        return a_width;
    }

    pub fn get_bin_cost(&self, a: AstIdx, b: AstIdx) -> u32 {
        let c1 = self.get_data(a).cost;
        let c2 = self.get_data(b).cost;
        (1 as u32).saturating_add(c1.saturating_add(c2))
    }

    pub fn union_contains_poly_part(&self, a: AstIdx, b: AstIdx) -> bool {
        let a_data = self.get_data(a);
        let b_data = self.get_data(b);
        return a_data.has_poly || b_data.has_poly;
    }

    pub fn compute_bitwise_data(&self, a: AstIdx, b: AstIdx, known_bits: KnownBits) -> AstData {
        let width = self.get_bin_width(a, b);
        let cost = self.get_bin_cost(a, b);
        let has_poly = self.union_contains_poly_part(a, b);

        let max = self.compute_bitwise_class(a, b);
        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: max,
            known_bits: known_bits,
            imut_data: 0,
        };

        return data;
    }

    pub fn compute_bitwise_class(&self, a: AstIdx, b: AstIdx) -> AstClass {
        let c1 = self.get_class(a);
        let c2 = self.get_class(b);

        let has_constant = self.is_constant(a) || self.is_constant(b);

        let mut max = max_class(
            c1,
            c2,
            if has_constant {
                AstClass::BitwiseWithConstants
            } else {
                AstClass::Bitwise
            },
        );

        if max > AstClass::BitwiseWithConstants {
            max = AstClass::Nonlinear;
        }

        return max;
    }

    pub fn clear(&mut self) {
        self.elements.clear();
        self.ast_to_idx.clear();
        self.symbol_ids.clear();
        self.name_to_symbol.clear();
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy, PartialOrd, Ord)]
pub enum AstClass {
    Bitwise = 0,
    BitwiseWithConstants = 1,
    Linear = 2,
    Semilinear = 3,
    Nonlinear = 4,
}

pub fn max_class(a: AstClass, b: AstClass, c: AstClass) -> AstClass {
    return std::cmp::max(a, std::cmp::max(b, c));
}

// Check if a sum or multiplication of two parts would yield a semilinear result.
pub fn try_make_semilinear(max: AstClass, c1: AstClass, c2: AstClass) -> AstClass {
    if max < AstClass::Semilinear {
        let is_sl = c1 == AstClass::BitwiseWithConstants || c2 == AstClass::BitwiseWithConstants;
        return if is_sl { AstClass::Semilinear } else { max };
    }

    return max;
}

#[derive(Clone, Hash, PartialEq, Eq, Copy)]
pub struct AstData {
    // Bit width
    width: u8,

    // Size of the AST(note that this is the AST size rather than DAG size)
    cost: u32,

    // Indicates whether the node contains any nonlinear polynomial parts.
    has_poly: bool,

    // Classification of the ast
    class: AstClass,

    // Known zero or one bits
    known_bits: KnownBits,

    // Internal mutable data for use in different algorithms.
    // Specifically we use this field to avoid unnecessarily storing data in hashmaps.
    //  e.g "how many users does this node have?" can be stored here temporarily.
    imut_data: u64,
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum SimpleAst {
    // Arithmetic operators:
    Add { a: AstIdx, b: AstIdx },
    Mul { a: AstIdx, b: AstIdx },
    Pow { a: AstIdx, b: AstIdx },
    // Bitwise operators:
    And { a: AstIdx, b: AstIdx },
    Or { a: AstIdx, b: AstIdx },
    Xor { a: AstIdx, b: AstIdx },
    Neg { a: AstIdx },
    // Shift operators:
    Lshr { a: AstIdx, b: AstIdx },
    // Literals:
    Constant { c: u64, width: u8 },
    Symbol { id: u32, width: u8 },
    // Special operators
    Zext { a: AstIdx, to: u8 },
    Trunc { a: AstIdx, to: u8 },
}

pub struct Context {
    pub(crate) arena: Arena,
}

impl mba::Context for Context {
    fn add(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, width } = op1 {
            if let SimpleAst::Constant { c: c2, width } = op2 {
                let result = self
                    .arena
                    .constant((c1.wrapping_add(*c2)), self.arena.get_width(arg0));

                return self.arena.get_node(result).clone();
            }
        }

        let add = self.arena.add(arg0, arg1);
        return self.arena.get_node(add).clone();
    }

    fn mul(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, width } = op1 {
            if let SimpleAst::Constant { c: c2, width } = op2 {
                let result = self
                    .arena
                    .constant((c1.wrapping_mul(*c2)), self.arena.get_width(arg0));

                return self.arena.get_node(result).clone();
            }
        }

        let mul = self.arena.mul(arg0, arg1);
        return self.arena.get_node(mul).clone();
    }

    fn pow(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, width } = op1 {
            if let SimpleAst::Constant { c: c2, width } = op2 {
                let result = self
                    .arena
                    .constant(Pow(*c1, *c2), self.arena.get_width(arg0));

                return self.arena.get_node(result).clone();
            }
        }
        let pow = self.arena.pow(arg0, arg1);
        return self.arena.get_node(pow).clone();
    }

    fn and(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, width } = op1 {
            if let SimpleAst::Constant { c: c2, width } = op2 {
                let result = self.arena.constant((*c1 & *c2), self.arena.get_width(arg0));

                return self.arena.get_node(result).clone();
            }
        }

        let and = self.arena.and(arg0, arg1);
        return self.arena.get_node(and).clone();
    }

    fn or(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, width } = op1 {
            if let SimpleAst::Constant { c: c2, width } = op2 {
                let result = self.arena.constant((*c1 | *c2), self.arena.get_width(arg0));
                return self.arena.get_node(result).clone();
            }
        }

        let or = self.arena.or(arg0, arg1);
        return self.arena.get_node(or).clone();
    }

    fn xor(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, width } = op1 {
            if let SimpleAst::Constant { c: c2, width } = op2 {
                let result = self.arena.constant((*c1 ^ *c2), self.arena.get_width(arg0));

                return self.arena.get_node(result).clone();
            }
        }
        let xor = self.arena.xor(arg0, arg1);
        return self.arena.get_node(xor).clone();
    }

    fn neg(&mut self, arg0: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        if let SimpleAst::Constant { c: c1, width } = op1 {
            let result = self.arena.constant((!*c1), self.arena.get_width(arg0));

            return self.arena.get_node(result).clone();
        }

        let neg = self.arena.neg(arg0);
        return self.arena.get_node(neg).clone();
    }

    fn lshr(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, width } = op1 {
            if let SimpleAst::Constant { c: c2, width } = op2 {
                let result = self
                    .arena
                    .constant((*c1 >> *c2), self.arena.get_width(arg0));

                return self.arena.get_node(result).clone();
            }
        }
        let xor = self.arena.lshr(arg0, arg1);
        return self.arena.get_node(xor).clone();
    }

    fn zext(&mut self, arg0: AstIdx, width: u8) -> SimpleAst {
        let zext = self.arena.zext(arg0, width);

        self.arena.get_node(zext).clone()
    }

    fn trunc(&mut self, arg0: AstIdx, width: u8) -> SimpleAst {
        let trunc = self.arena.trunc(arg0, width);

        self.arena.get_node(trunc).clone()
    }

    fn any(&mut self, arg0: AstIdx) -> SimpleAst {
        return self.arena.get_node(arg0).clone();
    }

    fn lookup_value(&mut self, arg0: AstIdx) -> Option<SimpleAst> {
        return Some(self.arena.get_node(arg0).clone());
    }

    fn lookup_id(&mut self, arg0: &SimpleAst) -> AstIdx {
        // TODO: If this element is not present in the map, we need to compute the data and insert it into the arena.
        // This is due to our recent refactor where we separate the `AstData` from the `SimpleAst` struct definition.
        return *self.arena.ast_to_idx.get(arg0).unwrap();
        //return self.arena.insert_ast_node(arg0.clone()); // TODO
    }

    fn constant(&mut self, arg0: u64, width: u8) -> SimpleAst {
        let id = self.arena.constant(arg0, width);
        return self.arena.get_node(id).clone();
    }

    fn symbol(&mut self, arg0: u32, width: u8) -> SimpleAst {
        let id = self.arena.symbol(arg0, width);
        self.arena.get_node(id).clone()
    }

    fn fold_add(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let add = |a: u64, b: u64| return a.wrapping_add(b);
        return fold_constant_binop(self, arg0, arg1, &add);
    }

    fn get_width(&mut self, arg0: AstIdx) -> u8 {
        return self.arena.get_width(arg0);
    }

    fn is_constant_modulo(&mut self, arg0: u64, arg1: u64, arg2: u8) -> Option<Empty> {
        let modulo_mask = get_modulo_mask(arg2);
        let are_equal = (arg0 & modulo_mask) == (arg1 & modulo_mask);
        return if are_equal { Some(Empty()) } else { None };
    }
}

fn fold_constant_binop(
    ctx: &mut Context,
    arg0: AstIdx,
    arg1: AstIdx,
    f: &dyn Fn(u64, u64) -> u64,
) -> SimpleAst {
    let op1 = ctx.arena.get_node(arg0);
    let op2 = ctx.arena.get_node(arg1);
    if let SimpleAst::Constant { c: c1, width } = op1 {
        if let SimpleAst::Constant { c: c2, width } = op2 {
            let result = ctx.arena.constant((f(*c1, *c2)), ctx.arena.get_width(arg0));

            return ctx.arena.get_node(result).clone();
        }
    }

    panic!("Non constant passed to fold_constant_binop!");
}

pub struct AstPrinter {
    output: String,
}

impl AstPrinter {
    pub(crate) fn print(ctx: &Context, ast: &SimpleAst) -> String {
        let mut printer = Self::new();
        printer.print_node(ctx, ast);
        printer.output
    }

    fn new() -> Self {
        Self {
            output: String::new(),
        }
    }

    fn print_node(&mut self, ctx: &Context, ast: &SimpleAst) {
        let operator = match ast {
            SimpleAst::Add { a, b } => "+",
            SimpleAst::Mul { a, b } => "*",
            SimpleAst::Pow { a, b } => "**",
            SimpleAst::And { a, b } => "&",
            SimpleAst::Or { a, b } => "|",
            SimpleAst::Xor { a, b } => "^",
            SimpleAst::Neg { a } => "~",
            SimpleAst::Lshr { a, b } => ">>",
            SimpleAst::Constant { c, width } => "",
            SimpleAst::Symbol { id, width } => "",
            SimpleAst::Zext { a, to } => "zx",
            SimpleAst::Trunc { a, to } => "tr",
        };

        // Don't put parens for constants or symbols
        if operator != "" {
            self.output.push_str("(")
        }

        match ast {
            SimpleAst::Add { a, b }
            | SimpleAst::Mul { a, b }
            | SimpleAst::Pow { a, b }
            | SimpleAst::And { a, b }
            | SimpleAst::Or { a, b }
            | SimpleAst::Xor { a, b }
            | SimpleAst::Lshr { a, b } => {
                self.print_node(ctx, ctx.arena.get_node(*a));
                self.output.push_str(&format!("{}", operator));
                self.print_node(ctx, ctx.arena.get_node(*b));
            }
            SimpleAst::Zext { a, to } => {
                self.print_node(ctx, ctx.arena.get_node(*a));
                self.output.push_str(&format!(" {} i{}", operator, to));
            }
            SimpleAst::Trunc { a, to } => {
                self.print_node(ctx, ctx.arena.get_node(*a));
                self.output.push_str(&format!(" {} i{}", operator, to));
            }
            SimpleAst::Neg { a } => {
                self.output.push('~');
                self.print_node(ctx, ctx.arena.get_node(*a));
            }
            SimpleAst::Constant { c, width } => {
                self.output
                    .push_str(&format!("{}:i{}", (*c as i64).to_string(), width))
            }
            SimpleAst::Symbol { id, width } => self.output.push_str(&format!(
                "{}:i{}",
                ctx.arena.get_symbol_name(*id).clone(),
                width
            )),
        }

        if operator != "" {
            self.output.push_str(")")
        }
    }
}

pub fn get_modulo_mask(width: u8) -> u64 {
    return u64::MAX >> (64 - width);
}

pub fn eval_ast(ctx: &Context, idx: AstIdx, value_mapping: &HashMap<AstIdx, u64>) -> u64 {
    let ast = ctx.arena.get_node(idx);
    let e = |i: &AstIdx| eval_ast(ctx, *i, value_mapping);
    match ast {
        SimpleAst::Add { a, b } => e(a).wrapping_add(e(b)),
        SimpleAst::Mul { a, b } => e(a).wrapping_mul(e(b)),
        SimpleAst::Pow { a, b } => todo!(),
        SimpleAst::And { a, b } => e(a) & e(b),
        SimpleAst::Or { a, b } => e(a) | e(b),
        SimpleAst::Xor { a, b } => e(a) ^ e(b),
        SimpleAst::Lshr { a, b } => e(a) >> e(b),
        SimpleAst::Neg { a } => !e(a),
        SimpleAst::Constant { c, width } => *c,
        SimpleAst::Symbol { id, width } => *value_mapping.get(&idx).unwrap(),
        SimpleAst::Zext { a, to } => get_modulo_mask(ctx.arena.get_width(*a)) & e(a),
        SimpleAst::Trunc { a, to } => get_modulo_mask(*to) & e(a),
    }
}

// Recursively apply ISLE over an AST.
pub fn recursive_simplify(ctx: &mut Context, idx: AstIdx) -> AstIdx {
    if ctx.arena.isle_cache.get(&idx).is_some() {
        return *ctx.arena.isle_cache.get(&idx).unwrap();
    }
    let mut ast = ctx.arena.get_node(idx).clone();

    match ast {
        SimpleAst::Add { a, b }
        | SimpleAst::Mul { a, b }
        | SimpleAst::Pow { a, b }
        | SimpleAst::And { a, b }
        | SimpleAst::Or { a, b }
        | SimpleAst::Xor { a, b }
        | SimpleAst::Lshr { a, b } => {
            let op1 = recursive_simplify(ctx, a);
            let op2 = recursive_simplify(ctx, b);
            ast = match ast {
                SimpleAst::Add { a, b } => ctx.add(op1, op2),
                SimpleAst::Mul { a, b } => ctx.mul(op1, op2),
                SimpleAst::Pow { a, b } => ctx.pow(op1, op2),
                SimpleAst::And { a, b } => ctx.and(op1, op2),
                SimpleAst::Or { a, b } => ctx.or(op1, op2),
                SimpleAst::Xor { a, b } => ctx.xor(op1, op2),
                SimpleAst::Lshr { a, b } => ctx.lshr(op1, op2),
                _ => unreachable!(),
            };
        }
        SimpleAst::Neg { a } => {
            let op1 = recursive_simplify(ctx, a);
            ast = ctx.neg(op1)
        }
        SimpleAst::Zext { a, to } => {
            let op1 = recursive_simplify(ctx, a);
            ast = ctx.zext(op1, to);
        }
        SimpleAst::Trunc { a, to } => {
            let op1 = recursive_simplify(ctx, a);
            ast = ctx.trunc(op1, to)
        }
        SimpleAst::Constant { c, width } => return idx,
        SimpleAst::Symbol { id, width } => return idx,
    }

    // Repeatedly invoke ISLE until a fixed point is reached.
    while true {
        let result = try_simplify_with_isle(ctx, &ast);
        if (result.is_none()) {
            break;
        }

        ast = result.unwrap();
    }

    let result = ctx.arena.ast_to_idx[&ast];
    ctx.arena.isle_cache.insert(idx, result);
    result
}

// Evaluate the current AST for all possible combinations of zeroes and ones as inputs.
// Each entry is then added to the result vector.
pub fn interpret_for_all_truth_values(
    ctx: &mut Context,
    ast_idx: AstIdx,
    var_indices: &Vec<AstIdx>,
    result_vector: &mut Vec<u64>,
    mask: u64,
) {
    // Evaluate the ast for possible combination of input zeroes and ones.
    // This is not the most concise way to do this, but it is easier to read.
    let num_vars = var_indices.len() as usize;
    let num_elements = usize::from(2 as u16).pow(num_vars as u32);
    let mut value_mapping: HashMap<AstIdx, u64> = HashMap::with_capacity(num_vars);
    for i in 0..num_elements {
        // Update the value mapping for this combination of zeroes and ones.
        for v in 0..num_vars {
            // Compute a mask for this variable.
            let var_mask = 1 << v as u16;

            // Compute the value of this specific variable.
            let mut var_value: u64 = (i & var_mask) as u64;

            // Shift the value back down to it's corresponding index.
            var_value = var_value >> v as u16;

            // Lazily use a HashMap to map variables to their input values for this evaluation.
            // TODO: Use an array instead.
            value_mapping.insert(var_indices[v], var_value as u64);
        }

        // Evaluate the AST for this combination of input zeroes and ones.
        let mut res = mask & eval_ast(ctx, ast_idx, &value_mapping);

        // Update the result vector for this combination of zeroes and ones.
        result_vector.push(res);
    }
}

// Try to apply one of the simplification patterns using ISLE.
pub fn try_simplify_with_isle(ctx: &mut Context, ast: &SimpleAst) -> Option<SimpleAst> {
    return mba::constructor_lower(ctx, &ast);
}

pub fn collect_var_indices<'a>(ctx: &Context, idx: AstIdx, out_vars: &mut HashSet<AstIdx>) {
    let mut visited: HashSet<AstIdx> = HashSet::new();
    collect_var_indices_internal(ctx, idx, &mut visited, out_vars);
}

fn collect_var_indices_internal(
    ctx: &Context,
    idx: AstIdx,
    visited: &mut HashSet<AstIdx>,
    out_vars: &mut HashSet<AstIdx>,
) -> () {
    // Only visit each ast once.
    if visited.contains(&idx) {
        return;
    }
    visited.insert(idx);

    let ast = ctx.arena.get_node(idx);
    let mut vbin = |a, b| {
        collect_var_indices_internal(ctx, a, visited, out_vars);
        collect_var_indices_internal(ctx, b, visited, out_vars);
    };
    match ast {
        SimpleAst::Add { a, b }
        | SimpleAst::Mul { a, b }
        | SimpleAst::Pow { a, b }
        | SimpleAst::And { a, b }
        | SimpleAst::Or { a, b }
        | SimpleAst::Xor { a, b }
        | SimpleAst::Lshr { a, b } => vbin(*a, *b),
        SimpleAst::Neg { a } | SimpleAst::Zext { a, .. } | SimpleAst::Trunc { a, .. } => {
            collect_var_indices_internal(ctx, *a, visited, out_vars)
        }
        SimpleAst::Constant { c, width } => return,
        SimpleAst::Symbol { id, width } => {
            out_vars.insert(idx);
            return;
        }
    }

    return;
}

pub fn order_vars_alphabetically(
    ctx: &Context,
    var_indices: &HashSet<AstIdx>,
    out_indices: &mut Vec<AstIdx>,
) {
    let mut sort = |a: &&AstIdx, b: &&AstIdx| {
        let v1 = ctx.arena.get_node(**a);
        let v2 = ctx.arena.get_node(**b);
        if let SimpleAst::Symbol { id, width } = v1 {
            if let SimpleAst::Symbol { id: id2, width } = v2 {
                let s1 = ctx.arena.get_symbol_name(*id);
                let s2 = ctx.arena.get_symbol_name(*id2);
                return s1.cmp(&s2);
            }
        }
        panic!("Expected variable!");
    };
    let mut sorted = Vec::from_iter(var_indices.iter());
    sorted.sort_by(sort);
    for s in sorted {
        out_indices.push(*s);
    }
}

#[no_mangle]
pub extern "C" fn CreateTruthTableDb() -> *mut TruthTableDatabase {
    let db = TruthTableDatabase::new();

    let mut pctx = Box::new(db);

    return Box::into_raw(pctx);
}

#[no_mangle]
pub extern "C" fn GetTruthTableDbEntry(
    db: *mut TruthTableDatabase,
    ctx: *mut Context,
    var_count: u32,
    vars: *const AstIdx,
    idx: usize,
) -> AstIdx {
    unsafe {
        let mut context: &mut Context = &mut (*ctx);
        let mut table: &mut TruthTableDatabase = &mut (*db);

        TruthTableDatabase::get_truth_table_entry(table, context, var_count, vars, idx)
    }
}

#[no_mangle]
pub extern "C" fn GetTruthTableDbEntryCost(
    db: *mut TruthTableDatabase,
    var_count: u32,
    idx: usize,
) -> u32 {
    unsafe {
        let mut table: &mut TruthTableDatabase = &mut (*db);

        TruthTableDatabase::get_boolean_cost(table, var_count, idx)
    }
}

#[no_mangle]
pub extern "C" fn CreateContext() -> *mut Context {
    let mut arena = Arena::new();

    let mut ctx = Context { arena };

    let mut pctx = Box::new(ctx);

    return Box::into_raw(pctx);
}

#[no_mangle]
pub extern "C" fn ContextClear(ctx: *mut Context, a: AstIdx) {
    unsafe {
        (*ctx).arena.clear();
    }
}

#[no_mangle]
pub extern "C" fn ContextAdd(ctx: *mut Context, a: AstIdx, b: AstIdx) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.add(a, b);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextMul(ctx: *mut Context, a: AstIdx, b: AstIdx) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.mul(a, b);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextPow(ctx: *mut Context, a: AstIdx, b: AstIdx) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.pow(a, b);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextAnd(ctx: *mut Context, a: AstIdx, b: AstIdx) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.and(a, b);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextOr(ctx: *mut Context, a: AstIdx, b: AstIdx) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.or(a, b);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextXor(ctx: *mut Context, a: AstIdx, b: AstIdx) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.xor(a, b);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextNeg(ctx: *mut Context, a: AstIdx) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.neg(a);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextLshr(ctx: *mut Context, a: AstIdx, b: AstIdx) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.lshr(a, b);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextZext(ctx: *mut Context, a: AstIdx, width: u8) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.zext(a, width);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextTrunc(ctx: *mut Context, a: AstIdx, width: u8) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.trunc(a, width);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextConstant(ctx: *mut Context, c: u64, width: u8) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.constant(c, width);
        return id;
    }
}

#[no_mangle]
pub extern "C" fn ContextSymbol(ctx: *mut Context, s: *const c_char, width: u8) -> AstIdx {
    let str = marshal_string(s).to_owned();

    unsafe {
        let id = (*ctx).arena.symbol_with_name(str.parse().unwrap(), width);
        return id;
    }
}

pub fn marshal_string(s: *const c_char) -> String {
    let c_str = unsafe {
        assert!(!s.is_null());

        CStr::from_ptr(s)
    };

    return c_str.to_str().unwrap().to_string();
}

#[no_mangle]
pub extern "C" fn ContextGetOpcode(ctx: *const Context, id: AstIdx) -> u8 {
    unsafe {
        return get_opcode(&(*ctx), id);
    }
}

pub fn get_opcode(ctx: &Context, id: AstIdx) -> u8 {
    let ast = ctx.arena.get_node(id);
    return match ast {
        SimpleAst::Add { a, b } => 1,
        SimpleAst::Mul { a, b } => 2,
        SimpleAst::Pow { a, b } => 3,
        SimpleAst::And { a, b } => 4,
        SimpleAst::Or { a, b } => 5,
        SimpleAst::Xor { a, b } => 6,
        SimpleAst::Neg { a } => 7,
        SimpleAst::Lshr { a, b } => 8,
        SimpleAst::Constant { c, width } => 9,
        SimpleAst::Symbol { id, width } => 10,
        SimpleAst::Zext { a, to } => 11,
        SimpleAst::Trunc { a, to } => 12,
    };
}

#[no_mangle]
pub extern "C" fn ContextGetWidth(ctx: *mut Context, id: AstIdx) -> u8 {
    unsafe {
        let width = (*ctx).arena.get_width(id);

        return width;
    }
}

#[no_mangle]
pub extern "C" fn ContextGetCost(ctx: *mut Context, id: AstIdx) -> u32 {
    unsafe {
        let width = (*ctx).arena.get_cost(id);

        return width;
    }
}

#[no_mangle]
pub extern "C" fn ContextGetHasPoly(ctx: *mut Context, id: AstIdx) -> bool {
    unsafe {
        let has = (*ctx).arena.get_has_poly(id);

        return has;
    }
}

#[no_mangle]
pub extern "C" fn ContextGetClass(ctx: *mut Context, id: AstIdx) -> u8 {
    unsafe {
        let class = (*ctx).arena.get_class(id);

        return class as u8;
    }
}

#[no_mangle]
pub extern "C" fn ContextGetKnownBits(ctx: *mut Context, id: AstIdx) -> KnownBits {
    unsafe {
        let kb = (*ctx).arena.get_data(id).known_bits;

        return kb;
    }
}

#[no_mangle]
pub extern "C" fn ContextGetImutData(ctx: *mut Context, id: AstIdx) -> u64 {
    unsafe {
        let kb = (*ctx).arena.get_data(id).imut_data;

        return kb;
    }
}

#[no_mangle]
pub extern "C" fn ContextSetImutData(ctx: *mut Context, id: AstIdx, imut: u64) {
    unsafe {
        let mut data = (*ctx).arena.get_data(id).clone();
        data.imut_data = imut;
        (*ctx).arena.set_data(id, data);
    }
}

#[no_mangle]
pub extern "C" fn ContextGetOp0(ctx: *const Context, id: AstIdx) -> AstIdx {
    unsafe {
        return get_op0(&(*ctx), id);
    }
}

pub fn get_op0(ctx: &Context, id: AstIdx) -> AstIdx {
    let ast = ctx.arena.get_node(id);
    return match ast {
        SimpleAst::Add { a, b } => *a,
        SimpleAst::Mul { a, b } => *a,
        SimpleAst::Pow { a, b } => *a,
        SimpleAst::And { a, b } => *a,
        SimpleAst::Or { a, b } => *a,
        SimpleAst::Xor { a, b } => *a,
        SimpleAst::Neg { a } => *a,
        SimpleAst::Lshr { a, b } => *a,
        SimpleAst::Zext { a, to } => *a,
        SimpleAst::Trunc { a, to } => *a,
        _ => unreachable!("Type has no first operand!"),
    };
}

#[no_mangle]
pub extern "C" fn ContextGetOp1(ctx: *mut Context, id: AstIdx) -> AstIdx {
    unsafe {
        unsafe {
            return get_op1(&(*ctx), id);
        }
    }
}

pub fn get_op1(ctx: &Context, id: AstIdx) -> AstIdx {
    let ast = (*ctx).arena.get_node(id);
    return match ast {
        SimpleAst::Add { a, b } => *b,
        SimpleAst::Mul { a, b } => *b,
        SimpleAst::Pow { a, b } => *b,
        SimpleAst::And { a, b } => *b,
        SimpleAst::Or { a, b } => *b,
        SimpleAst::Xor { a, b } => *b,
        SimpleAst::Lshr { a, b } => *b,
        _ => unreachable!("Type has no second operand!"),
    };
}

#[no_mangle]
pub extern "C" fn ContextGetConstantValue(ctx: *mut Context, id: AstIdx) -> u64 {
    unsafe {
        let ast = (*ctx).arena.get_node(id);
        if let SimpleAst::Constant { c: c2, width } = ast {
            return *c2;
        }
    }

    panic!("ast is not a constant!");
}

#[no_mangle]
pub extern "C" fn ContextGetSymbolName(ctx: *mut Context, id: AstIdx) -> *mut c_char {
    unsafe {
        let ast = (*ctx).arena.get_node(id);
        if let SimpleAst::Symbol { id, width } = ast {
            let s = (*ctx).arena.get_symbol_name(*id);
            return CString::new(s).unwrap().into_raw();
        }
    }
    panic!("ast is not a symbol!");
}

#[no_mangle]
pub extern "C" fn ContextParseAstString(ctx: *mut Context, s: *const c_char) -> AstIdx {
    let str = marshal_string(s).to_owned();

    // Note that the .NET api should be used for parsing strings into ASTs.
    unsafe {
        let mut deref: &mut Context = &mut (*ctx);
        panic!("TODO: Implement parsing in rust");
    }
}

#[no_mangle]
pub extern "C" fn ContextGetAstString(ctx: *mut Context, id: AstIdx) -> *mut c_char {
    unsafe {
        let ast: &SimpleAst = (*ctx).arena.get_node(id);
        let mut deref: &mut Context = &mut (*ctx);
        let str = AstPrinter::print(deref, &ast.clone());
        return CString::new(str).unwrap().into_raw();
    }
}

#[no_mangle]
pub extern "C" fn ContextCollectVariables(
    ctx: *mut Context,
    id: AstIdx,
    out_len: *mut u64,
) -> *mut AstIdx {
    let mut out_vars = HashSet::new();
    unsafe {
        // Collect a unique list of variables.
        let mut deref: &mut Context = &mut (*ctx);
        collect_var_indices(deref, id, &mut out_vars);

        // Order the variables alphabetically.
        let mut ordered_indices = Vec::new();
        order_vars_alphabetically(deref, &out_vars, &mut ordered_indices);

        // Update the length pointer.
        let len = ordered_indices.len();
        *out_len = len as u64;

        // Give C# ownership of the boxed slice.
        let boxed = ordered_indices.into_boxed_slice();
        let released = Box::into_raw(boxed);

        // https://stackoverflow.com/a/57616981/6855629
        return released as *mut _;
    }
}

#[no_mangle]
pub extern "C" fn ContextGetBooleanForIndex(
    ctx: *mut Context,
    vars: *const AstIdx,
    var_count: u32,
    result_vec_idx: u32,
) -> AstIdx {
    let mut ast = None;

    let num_vars = var_count as u16;

    unsafe {
        let mut deref: &mut Context = &mut (*ctx);
        for var_idx in 0..num_vars {
            let vmask: u32 = 1 << var_idx;
            let is_set = (result_vec_idx & vmask) != 0;
            let var = *vars.wrapping_add(var_idx as usize);
            let term = if is_set { var } else { deref.arena.neg(var) };
            if ast.is_none() {
                ast = Some(term);
            } else {
                ast = Some(deref.arena.and(ast.unwrap(), term));
            }
        }
    }

    return ast.unwrap();
}

#[no_mangle]
pub extern "C" fn ContextGetConjunctionFromVarMask(
    ctx: *mut Context,
    vars: *const AstIdx,
    var_mask: u64,
) -> AstIdx {
    unsafe {
        let mut deref: &mut Context = &mut (*ctx);
        return conjunction_from_var_mask(deref, vars, var_mask);
    }
}

fn conjunction_from_var_mask(ctx: &mut Context, vars: *const AstIdx, var_mask: u64) -> AstIdx {
    let mut conj_mask = var_mask;

    let mut conj = None;
    while conj_mask != 0 {
        let lsb = conj_mask.trailing_zeros();

        unsafe {
            let op = *vars.wrapping_add(lsb as usize);
            conj = if conj.is_none() {
                Some(op)
            } else {
                Some(ctx.arena.and(conj.unwrap(), op))
            };
        }

        conj_mask ^= 1 << lsb;
    }

    return conj.unwrap();
}

#[no_mangle]
pub extern "C" fn ContextEvaluateForAllZeroesAndOnes(
    ctx: *mut Context,
    id: AstIdx,
    mask: u64,
    out_len: *mut u64,
) -> *mut u64 {
    let mut out_vars = HashSet::new();
    unsafe {
        // Collect a unique list of variables.
        let mut deref: &mut Context = &mut (*ctx);
        collect_var_indices(deref, id, &mut out_vars);

        // Order the variables alphabetically.
        let mut ordered_indices = Vec::new();
        order_vars_alphabetically(deref, &out_vars, &mut ordered_indices);

        // Evaluate the ast for all possible combinations of zeroes and ones.
        let mut result_vector: Vec<u64> = Vec::new();
        interpret_for_all_truth_values(deref, id, &ordered_indices, &mut result_vector, mask);

        // Update the length pointer.
        let len = result_vector.len();
        *out_len = len as u64;

        // Give C# ownership of the boxed slice.
        let boxed = result_vector.into_boxed_slice();
        let released = Box::into_raw(boxed);

        // https://stackoverflow.com/a/57616981/6855629
        return released as *mut _;
    }
}

const PUSH_RCX: u8 = 0x51;
const PUSH_RDX: u8 = 0x52;
const PUSH_RAX: u8 = 0x50;
const PUSH_RBX: u8 = 0x53;
const PUSH_RSI: u8 = 0x56;
const PUSH_RDI: u8 = 0x57;

const POP_RCX: u8 = 0x59;
const POP_RDX: u8 = 0x5A;

// return value
const POP_RAX: u8 = 0x58;

// rvidx, unused
const POP_RBX: u8 = 0x5B;

// scratch1
const POP_RSI: u8 = 0x5E;

// scratch2
const POP_RDI: u8 = 0x5F;

const RET: u8 = 0xC3;

#[inline(always)]
unsafe fn emit_u8(page: *mut u8, offset: &mut usize, data: u8) {
    *page.add(*offset) = data;
    *offset += 1;
}

#[inline(always)]
unsafe fn emit_u64(page: *mut u8, offset: &mut usize, data: u64) {
    let bytes = data.to_le_bytes();
    for i in bytes {
        *page.add(*offset) = i;
        *offset += 1;
    }
}

#[inline(always)]
unsafe fn emit(page: *mut u8, offset: &mut usize, data: &[u8]) {
    for i in data {
        *page.add(*offset) = *i;
        *offset += 1;
    }
}

// Note that we need to incorporate the ast size into the JIT code.
unsafe fn jit_rec(
    ctx: &Context,
    node: AstIdx,
    node_to_var: &HashMap<AstIdx, u8>,
    page: *mut u8,
    offset: &mut usize,
) {
    let binop = |a: AstIdx, b: AstIdx, data: &[u8], offset: &mut usize| {
        jit_rec(ctx, a, node_to_var, page, offset);
        jit_rec(ctx, b, node_to_var, page, offset);

        emit_u8(page, offset, POP_RDI);
        emit_u8(page, offset, POP_RSI);

        emit(page, offset, data);

        emit_u8(page, offset, PUSH_RSI);
    };

    match ctx.arena.get_node(node) {
        SimpleAst::Constant { c, width } => {
            jit_constant(*c, page, offset);
        }
        SimpleAst::Neg { a } => {
            jit_rec(ctx, *a, node_to_var, page, offset);
            emit_u8(page, offset, POP_RSI);
            emit(page, offset, &[0x48, 0xF7, 0xD6]);
            emit_u8(page, offset, PUSH_RSI);
        }
        SimpleAst::Add { a, b } => binop(*a, *b, &[0x48, 0x01, 0xFE], offset),
        SimpleAst::Mul { a, b } => binop(*a, *b, &[0x48, 0x0F, 0xAF, 0xF7], offset),
        SimpleAst::Pow { a, b } => {
            // Save the value of rcx/rdx on the stack, because these are used throughout the rest of the jitted function.
            emit_u8(page, offset, PUSH_RCX);
            emit_u8(page, offset, PUSH_RDX);

            // Push the base and exponent onto the stack.
            jit_rec(ctx, *a, node_to_var, page, offset);
            jit_rec(ctx, *b, node_to_var, page, offset);

            emit_u8(page, offset, POP_RDX);
            emit_u8(page, offset, POP_RCX);

            // Convert the exponentiation stub to a u64
            let pow_stub_addr = Pow as *const () as u64;
            // Push the address of the pow stub
            jit_constant(pow_stub_addr, page, offset);
            // Mov pow stub addr into rax
            emit_u8(page, offset, POP_RAX);
            // TODO: If the stack is not 16 byte aligned we may need to manually align it. AFAIK it should be aligned already though.
            // Call rax (pow stub)
            emit(page, offset, &[0xFF, 0xD0]);
            // Restore rcx/rdx from the stack
            emit_u8(page, offset, POP_RDX);
            emit_u8(page, offset, POP_RCX);
            // push rax
            emit_u8(page, offset, PUSH_RAX);
        }
        SimpleAst::And { a, b } => binop(*a, *b, &[0x48, 0x21, 0xFE], offset),
        SimpleAst::Or { a, b } => binop(*a, *b, &[0x48, 0x09, 0xFE], offset),
        SimpleAst::Xor { a, b } => binop(*a, *b, &[0x48, 0x31, 0xFE], offset),
        SimpleAst::Symbol { id, width } => {
            let var_idx = node_to_var[&node];

            // varMask = 1 << varIdx
            // mov rsi, 1
            emit(page, offset, &[0x48, 0xC7, 0xC6, 0x01, 0x00, 0x00, 0x00]);

            // shl rsi, varidx
            emit(page, offset, &[0x48, 0xc1, 0xE6, var_idx]);

            // // varValue = i & varMask
            // mov rdi, combIdxRegister (rdx)
            emit(page, offset, &[0x48, 0x89, 0xD7]);
            // and rdi, rsi
            emit(page, offset, &[0x48, 0x21, 0xF7]);

            // Shift the value back down to bit index zero,
            // varValue = varValue >> (ushort)v
            // shr rdi, varIdx
            emit(page, offset, &[0x48, 0xC1, 0xEF, var_idx]);

            // Shift the variable value(which is either zero or one) up to the current bitIndex.
            // varValue <<= bitIndex;
            // shl rdi, bitIdxRegister
            emit(page, offset, &[0x48, 0xD3, 0xE7]);

            // Push the result.
            emit_u8(page, offset, PUSH_RDI);
        }
        SimpleAst::Zext { a, to } => {
            // Zero extend is a no-op in our JIT, since we always AND with a mask after every operation.
            jit_rec(ctx, *a, node_to_var, page, offset);
        }
        SimpleAst::Trunc { a, to } => {
            jit_rec(ctx, *a, node_to_var, page, offset);

            // mov rax, constant
            emit_u8(page, offset, 0x48);
            emit_u8(page, offset, 0xB8);
            // Fill in the constant
            let trunc_mask = get_modulo_mask(*to);
            emit_u64(page, offset, trunc_mask);
            // and [rsp+8], rax
            emit(page, offset, &[0x48, 0x21, 0x04, 0x24]);
        }
        SimpleAst::Lshr { a, b } => todo!(),
    };

    // mov rax, constant
    emit_u8(page, offset, 0x48);
    emit_u8(page, offset, 0xB8);
    // Fill in the constant
    let c = get_modulo_mask(ctx.arena.get_width(node));
    emit_u64(page, offset, c);
    // and [rsp+8], rax
    emit(page, offset, &[0x48, 0x21, 0x04, 0x24]);
}

unsafe fn jit_constant(c: u64, page: *mut u8, offset: &mut usize) {
    // mov rax, constant
    emit_u8(page, offset, 0x48);
    emit_u8(page, offset, 0xB8);
    // Fill in the constant
    emit_u64(page, offset, c);
    // Push rax
    emit_u8(page, offset, PUSH_RAX);
}

#[no_mangle]
pub extern "C" fn GetPowPtr() -> u64 {
    return Pow as *const () as u64;
}

#[no_mangle]
pub extern "C" fn Pow(mut base: u64, mut exp: u64) -> u64 {
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

#[no_mangle]
pub unsafe extern "C" fn ContextCompileLegacy(
    ctx_p: *mut Context,
    node: AstIdx,
    mask: u64,
    variables: *const AstIdx,
    var_count: u64,
    page: *mut u8,
) {
    let mut ctx: &mut Context = &mut (*ctx_p);

    let mut offset: usize = 0;

    // Push all clobbered registers
    emit_u8(page, &mut offset, PUSH_RBX);
    emit_u8(page, &mut offset, PUSH_RSI);
    emit_u8(page, &mut offset, PUSH_RDI);

    // JIT code
    let mut node_to_var: HashMap<AstIdx, u8> = HashMap::with_capacity(var_count as usize);
    for i in 0..var_count {
        node_to_var.insert(*variables.add(i as usize), i as u8);
    }

    jit_rec(ctx, node, &node_to_var, page, &mut offset);

    // Pop the evaluation result
    emit_u8(page, &mut offset, POP_RAX);

    // Mask off bits that we don't care about
    // mov rsi, mask
    emit(page, &mut offset, &[0x48, 0xBE]);
    emit_u64(page, &mut offset, mask);

    // and rax, rsi
    emit(page, &mut offset, &[0x48, 0x21, 0xF0]);

    // Shift the value back down to bit index zero,
    // varValue = varValue >> (ushort)v
    // shr rax, bitIdxRegister
    emit(page, &mut offset, &[0x48, 0xD3, 0xE8]);

    // Restore the clobbered registers.
    emit_u8(page, &mut offset, POP_RDI);
    emit_u8(page, &mut offset, POP_RSI);
    emit_u8(page, &mut offset, POP_RBX);

    emit_u8(page, &mut offset, RET);
}

#[no_mangle]
pub unsafe extern "C" fn ContextCompile(
    ctx_p: *mut Context,
    node: AstIdx,
    mask: u64,
    variables: *const AstIdx,
    var_count: u64,
    page: *mut u8,
) -> u64 {
    let mut ctx: &mut Context = &mut (*ctx_p);

    let mut vars: Vec<AstIdx> = Vec::new();
    // JIT code
    for i in 0..var_count {
        vars.push(*variables.add(i as usize));
    }

    let mut assembler = FastAmd64Assembler::new(page);
    let mut compiler = Amd64OptimizingJit::<FastAmd64Assembler>::new();
    compiler.compile(ctx, &mut assembler, node, &vars, page, false);
    return assembler.offset as u64;
}

#[no_mangle]
pub unsafe extern "C" fn ContextBenchmarkCompile(
    ctx_p: *mut Context,
    node: AstIdx,
    mask: u64,
    variables: *const AstIdx,
    var_count: u64,
    page: *mut u8,
) {
    let mut ctx: &mut Context = &mut (*ctx_p);

    let mut vars: Vec<AstIdx> = Vec::new();
    // JIT code
    for i in 0..var_count {
        vars.push(*variables.add(i as usize));
    }

    let mut assembler = FastAmd64Assembler::new(page);
    let mut compiler = Amd64OptimizingJit::<FastAmd64Assembler>::new();
    //compiler.compile(ctx, &mut assembler, node, &vars, page, false);
    compiler.compile_benchmark(ctx, &mut assembler, node, &vars, page, false);
}

#[no_mangle]
pub unsafe extern "C" fn ContextExecute(
    multi_bit_u: u32,
    bit_width: u32,
    var_count: u64,
    num_combinations: u64,
    page: *mut u8,
    output: *mut u64,
    one_bit_vars: u32,
) {
    let multi_bit = multi_bit_u != 0;
    let num_bit_iterations: u32 = if multi_bit { bit_width } else { 1 };

    if (one_bit_vars != 0) {
        let fptr: unsafe extern "C" fn(u32, u64) -> u64 = std::mem::transmute(page);

        let mut arr_idx: usize = 0;
        for bit_index in 0..num_bit_iterations {
            for i in 0..num_combinations {
                let result = fptr(bit_index, i);
                *output.add(arr_idx) = result;
                arr_idx += 1;
            }
        }

        return;
    }

    let mut var_values = vec![0u64; var_count as usize];
    let vptr = var_values.as_mut_slice();

    let mut arr_idx: usize = 0;
    let fptr: unsafe extern "C" fn(*mut u64) -> u64 = std::mem::transmute(page);
    for bit_index in 0..num_bit_iterations {
        for i in 0..num_combinations {
            for v_idx in 0..var_count {
                vptr[v_idx as usize] = ((i >> v_idx) & 1) << bit_index;
            }

            let result = (fptr(vptr.as_mut_ptr()) & get_modulo_mask(bit_width as u8)) >> bit_index;
            *output.add(arr_idx) = result;
            arr_idx += 1;
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn ContextJit(
    ctx_p: *mut Context,
    node: AstIdx,
    mask: u64,
    multi_bit_u: u32,
    bit_width: u32,
    variables: *const AstIdx,
    var_count: u64,
    num_combinations: u64,
    page: *mut u8,
    output: *mut u64,
) {
    let multi_bit = multi_bit_u != 0;
    let num_bit_iterations: u32 = if multi_bit { bit_width } else { 1 };

    let mut ctx: &mut Context = &mut (*ctx_p);

    let mut offset: usize = 0;

    // Push all clobbered registers
    emit_u8(page, &mut offset, PUSH_RBX);
    emit_u8(page, &mut offset, PUSH_RSI);
    emit_u8(page, &mut offset, PUSH_RDI);

    // JIT code
    let mut node_to_var: HashMap<AstIdx, u8> = HashMap::with_capacity(var_count as usize);
    for i in 0..var_count {
        node_to_var.insert(*variables.add(i as usize), i as u8);
    }

    jit_rec(ctx, node, &node_to_var, page, &mut offset);

    // Pop the evaluation result
    emit_u8(page, &mut offset, POP_RAX);

    // Mask off bits that we don't care about
    // mov rsi, mask
    emit(page, &mut offset, &[0x48, 0xBE]);
    emit_u64(page, &mut offset, mask);

    // and rax, rsi
    emit(page, &mut offset, &[0x48, 0x21, 0xF0]);

    // Shift the value back down to bit index zero,
    // varValue = varValue >> (ushort)v
    // shr rax, bitIdxRegister
    emit(page, &mut offset, &[0x48, 0xD3, 0xE8]);

    // Restore the clobbered registers.
    emit_u8(page, &mut offset, POP_RDI);
    emit_u8(page, &mut offset, POP_RSI);
    emit_u8(page, &mut offset, POP_RBX);

    emit_u8(page, &mut offset, RET);

    let fptr: unsafe extern "C" fn(u32, u64) -> u64 = std::mem::transmute(page);

    let mut arr_idx: usize = 0;
    for bit_index in 0..num_bit_iterations {
        for i in 0..num_combinations {
            let result = fptr(bit_index, i);
            *output.add(arr_idx) = result;
            arr_idx += 1;
        }
    }
}

// Run ISLE until a fixed point is reached, but do not recurse.
#[no_mangle]
pub extern "C" fn ContextSingleSimplify(ctx: *mut Context, idx: AstIdx) -> AstIdx {
    unsafe {
        let mut deref: &mut Context = &mut (*ctx);
        let mut ast = deref.arena.get_node(idx).clone();

        while true {
            let result = try_simplify_with_isle(deref, &ast);
            if (result.is_none()) {
                break;
            }

            ast = result.unwrap();
        }

        return deref.arena.ast_to_idx[&ast];
    }
}

#[no_mangle]
pub extern "C" fn ContextRecursiveSimplify(ctx: *mut Context, id: AstIdx) -> AstIdx {
    unsafe {
        let mut deref: &mut Context = &mut (*ctx);
        return recursive_simplify(deref, id);
    }
}

#[no_mangle]
pub extern "C" fn ContextBenchmark(ctx: *mut Context, seed: u64) {
    let mut deref: &mut Context = unsafe { &mut (*ctx) };

    let mut s = seed;
    for i in 0..50000000 {
        s *= 17;

        let _ = deref.arena.constant(s, 16);
    }
}

#[no_mangle]
pub extern "C" fn SubtractConstantOffset(
    vec: *mut u64,
    len: u64,
    mut num_combinations: u64,
    mut width: u64,
    multi_bit_u: u32,
) -> u64 {
    // Fetch the constant offset. If the offset is zero then there is nothing to subtract.
    let constant = unsafe { *vec.add(0) };
    if constant == 0 {
        return 0;
    }

    // Try to inform the optimizer that the width is at most 64 bits.
    width = cmp::min(width, 64);

    let modulo_mask = get_modulo_mask(width as u8);

    /*
    for bit_index in 0..width {
        let i = bit_index * num_combinations;
        let constant_offset = modulo_mask & (constant >> bit_index);
        let new_coeff = modulo_mask & (unsafe { *vec.add((i) as usize) } - constant_offset);
        unsafe {
            *vec.add((i) as usize) = new_coeff;
            continue;
        };
    }
    */

    let num_bit_iterations = if multi_bit_u != 0 { width } else { 1 };
    /*
    dbg!(
        "SubtractConstantOffset: num_bit_iterations = {}, multi_bit_u = {}",
        num_bit_iterations,
        multi_bit_u
    );
    */
    for bit_index in 0..num_bit_iterations {
        let mask: u64 = 1 << bit_index;
        let i = bit_index * num_combinations;

        let constant_offset = modulo_mask & (constant >> bit_index);
        for comb in 0..num_combinations {
            let new_coeff =
                modulo_mask & (unsafe { *vec.add((comb + i) as usize) } - constant_offset);

            /*
            if comb == 0 {
                unsafe {
                    *vec.add((comb + i) as usize) = new_coeff;
                    continue;
                };
            }
            */

            let new_coeff = (modulo_mask & (new_coeff * (1 << bit_index)) >> bit_index);
            unsafe {
                *vec.add((comb + i) as usize) = new_coeff;
                continue;
            };
        }
    }

    return constant;
}

#[no_mangle]
pub extern "C" fn IsLinearResultVector(
    vec: *const u64,
    len: u64,
    mut num_combinations: u64,
    mut width: u64,
) -> bool {
    let modulo_mask = get_modulo_mask(width as u8);
    for bit_index in 0..width {
        let mask: u64 = 1 << bit_index;
        let i = bit_index * num_combinations;

        let mut nonlinear = false;
        for comb in 0..num_combinations {
            let bit_0_coeff = unsafe { *vec.add(comb as usize) };
            let bit_i_coeff = unsafe { *vec.add((comb + i) as usize) };

            let op0 = modulo_mask & (bit_0_coeff * mask);
            let op1 = modulo_mask & (bit_i_coeff * mask);

            nonlinear |= (op0 != op1);
        }

        if nonlinear {
            return false;
        }
    }

    return true;
}

const VARIABLE_COMBINATIONS_1: &[u16] = &get_variable_combinations::<1, 1>();
const VARIABLE_COMBINATIONS_2: &[u16] = &get_variable_combinations::<3, 2>();
const VARIABLE_COMBINATIONS_3: &[u16] = &get_variable_combinations::<7, 3>();
const VARIABLE_COMBINATIONS_4: &[u16] = &get_variable_combinations::<15, 4>();
const VARIABLE_COMBINATIONS_5: &[u16] = &get_variable_combinations::<31, 5>();
const VARIABLE_COMBINATIONS_6: &[u16] = &get_variable_combinations::<63, 6>();
const VARIABLE_COMBINATIONS_7: &[u16] = &get_variable_combinations::<127, 7>();
const VARIABLE_COMBINATIONS_8: &[u16] = &get_variable_combinations::<255, 8>();
const VARIABLE_COMBINATIONS_9: &[u16] = &get_variable_combinations::<511, 9>();
const VARIABLE_COMBINATIONS_10: &[u16] = &get_variable_combinations::<1023, 10>();
const VARIABLE_COMBINATIONS_11: &[u16] = &get_variable_combinations::<2047, 11>();
const VARIABLE_COMBINATIONS_12: &[u16] = &get_variable_combinations::<4095, 12>();
const VARIABLE_COMBINATIONS_13: &[u16] = &get_variable_combinations::<8191, 13>();
const VARIABLE_COMBINATIONS_14: &[u16] = &get_variable_combinations::<16383, 14>();
const VARIABLE_COMBINATIONS_15: &[u16] = &get_variable_combinations::<32767, 15>();
const VARIABLE_COMBINATIONS_16: &[u16] = &get_variable_combinations::<65535, 16>();

#[inline]
fn get_combs(num_vars: u32) -> &'static [u16] {
    return match num_vars {
        1 => VARIABLE_COMBINATIONS_1,
        2 => VARIABLE_COMBINATIONS_2,
        3 => VARIABLE_COMBINATIONS_3,
        4 => VARIABLE_COMBINATIONS_4,
        5 => VARIABLE_COMBINATIONS_5,
        6 => VARIABLE_COMBINATIONS_6,
        7 => VARIABLE_COMBINATIONS_7,
        8 => VARIABLE_COMBINATIONS_8,
        9 => VARIABLE_COMBINATIONS_9,
        10 => VARIABLE_COMBINATIONS_10,
        11 => VARIABLE_COMBINATIONS_11,
        12 => VARIABLE_COMBINATIONS_12,
        13 => VARIABLE_COMBINATIONS_13,
        14 => VARIABLE_COMBINATIONS_14,
        15 => VARIABLE_COMBINATIONS_15,
        16 => VARIABLE_COMBINATIONS_16,
        _ => panic!(
            "Cannot compute variable combinations for {num_vars}, vector would be too large!"
        ),
    };
}

const fn get_variable_combinations<const ENTRIES: usize, const VARS: usize>() -> [u16; ENTRIES] {
    let mut outputs: [u16; ENTRIES] = [0; ENTRIES];

    let num_entries = ENTRIES as u16;
    let var_count = VARS as u16;

    let mut i: usize = 0;
    while i < var_count as usize {
        outputs[i] = 1 << i;

        i += 1;
    }

    let mut comb_count = var_count;
    let mut _new = var_count;

    let mut count = 1;
    while count < var_count {
        let size = comb_count;
        let mut nnew = 0;
        let mut from = size - _new;

        let mut ei = from;
        while ei < from + (size - from) {
            let e = outputs[ei as usize];
            let last_idx = (16 - e.leading_zeros()) as u16;

            let mut v = last_idx;
            while v < var_count {
                outputs[comb_count as usize] |= (1 << v);
                outputs[comb_count as usize] |= e;
                comb_count += 1;
                nnew += 1;

                v += 1;
            }

            ei += 1;
        }

        _new = nnew;

        count += 1;
    }

    return outputs;
}

#[no_mangle]
pub unsafe extern "C" fn ContextMinimizeAnf(
    ctx: *mut Context,
    db: *mut TruthTableDatabase,
    truth_table: *mut u64,
    vars: *const AstIdx,
    variable_count: u32,
    page: *mut u8,
) -> AstIdx {
    unsafe {
        let mut ctx_deref: &mut Context = &mut (*ctx);
        let table = TruthTable {
            num_vars: variable_count,
            arr: truth_table,
        };

        let mut table_deref: &mut TruthTableDatabase = &mut (*db);

        // If the truth table has a positive constant offset, negate it.
        // This is necessary because the ANF minimization algorithm does not support positive constants.
        let negated = table.get_bit(table.get_mut_arr(), 0) != 0;
        if negated {
            table.negate();
        }

        // Minimize the boolean.
        let result = minimize_anf(ctx_deref, table_deref, &table, vars, variable_count, page);

        // We want to preserve the contents of the truth table, so we need to undo the negation.
        if negated {
            table.negate();
        }

        // If the truth table was negated, we need to negate the whole expression.
        return if negated {
            ctx_deref.arena.neg(result)
        } else {
            result
        };
    }
}

// Compute a minimized algebraic normal form.
pub fn minimize_anf(
    ctx: &mut Context,
    db: &mut TruthTableDatabase,
    table: &TruthTable,
    vars: *const AstIdx,
    variable_count: u32,
    page: *mut u8,
) -> AstIdx {
    let variable_combinations = get_combs(table.num_vars);
    let only_one_var = table.num_vars == 1;
    let width: u32 = if table.num_vars == 1 {
        1
    } else {
        2 << (table.num_vars - 1)
    };

    let mut terms: Vec<u32> =
        Vec::with_capacity(std::cmp::min(32, variable_combinations.len() + 1));

    unsafe {
        let safe_arr = std::slice::from_raw_parts_mut(table.arr, table.get_num_words());

        for i in 0..variable_combinations.len() as u32 {
            let comb = variable_combinations[i as usize];
            let true_mask = variable_combinations[i as usize];
            let index = get_group_size_index(comb as u64);
            let coeff = table.get_bit(safe_arr, index);
            if coeff == 0 {
                continue;
            }

            subtract_coeff_boolean(
                &table,
                safe_arr,
                0,
                coeff,
                index,
                width,
                only_one_var,
                true_mask as u64,
            );
            terms.push(comb.into());
        }
    }

    // For debugging / performance reasons it's useful to be able to terminate here if needbe.
    let only_anf = false;
    if only_anf {
        let mut result: Option<AstIdx> = None;
        for term in terms {
            let conj = conjunction_from_var_mask(ctx, vars, term.into());
            result = if result.is_none() {
                Some(conj)
            } else {
                Some(ctx.arena.xor(result.unwrap(), conj))
            };
        }

        return result.unwrap();
    }

    let mut demanded_vars_map: AHashMap<AstIdx, u32> = AHashMap::new();
    // Set the initial demanded variable masks.
    for i in 0..variable_count {
        let var = unsafe { *vars.add(i as usize) };
        demanded_vars_map.insert(var, 1 << i);
    }

    let factored = factor(
        ctx,
        vars,
        variable_count,
        &mut terms,
        &mut demanded_vars_map,
    );

    let simplified = simplify_rec(
        ctx,
        db,
        factored,
        vars,
        variable_count,
        page,
        &mut demanded_vars_map,
    );

    return simplified;
}

// Recursively factor a boolean function in algebraic normal form
pub fn factor(
    ctx: &mut Context,
    variables: *const AstIdx,
    var_count: u32,
    conjs: &mut Vec<u32>,
    demanded_vars_map: &mut AHashMap<AstIdx, u32>,
) -> AstIdx {
    // Delete -1 if present
    let mut has = false;
    let mut nil_idx = None;
    for i in 0..conjs.len() {
        if conjs[i] == u32::MAX {
            nil_idx = Some(i);
        }
    }
    if nil_idx.is_some() {
        has = true;
        conjs.remove(nil_idx.unwrap());
    }

    // Collect the number of times we encounter each variable.
    let mut variable_counts: Vec<(u32, u32)> = vec![(0, 0); var_count as usize];
    for conj in conjs.iter() {
        for i in 0..var_count {
            let mask = 1 << i;
            if (mask & *conj) != 0 {
                variable_counts[i as usize] = (i, variable_counts[i as usize].1 + 1);
            }
        }
    }

    // Order the variables by the number of times they appear.
    let compare = |a: &(u32, u32), b: &(u32, u32)| {
        return b.1.cmp(&a.1);
    };
    variable_counts.sort_by(compare);

    // For each conjunction, we take out the leading factor.
    let mut groups: AHashMap<u32, Vec<u32>> = AHashMap::new();
    for conj in conjs.iter() {
        for index in 0..var_count {
            let i = variable_counts[index as usize].0;

            let mask = 1 << i;
            if (*conj & mask) == 0 {
                continue;
            }

            let new_conj = conj & !mask;

            let group = groups.entry(i).or_insert(Vec::new());
            if new_conj != 0 {
                group.push(new_conj);
            } else {
                group.push(u32::MAX);
            }

            break;
        }
    }

    let output: &mut Vec<AstIdx> = &mut Vec::new();
    for (var_id, count) in variable_counts.iter() {
        if *count == 0 {
            continue; // Skip variables that don't appear in the function.
        }

        let var_idx = *var_id;

        let mut maybe_elems = groups.get_mut(&var_idx);
        if maybe_elems.is_none() {
            continue;
        }

        let mut elems = maybe_elems.unwrap();

        // Get the variable
        let mut result: AstIdx = AstIdx(0);
        unsafe {
            result = *variables.wrapping_add(var_idx as usize);
        }

        // If we have just 1 a single variable, yield it.
        if elems.len() == 0 || (elems.len() == 1 && elems[0] == u32::MAX) {
            output.push(result);
            continue;
        } else if elems.len() == 1 {
            let mut mask = elems[0];

            let from_mask = conjunction_from_var_mask(ctx, variables, mask as u64);
            let conj = ctx.arena.and(result, from_mask);
            output.push(conj);

            mask |= 1 << var_idx;
            demanded_vars_map.insert(conj, mask);
            continue;
        }

        // Otherwise recursivley factor
        let other = factor(ctx, variables, var_count, &mut elems, demanded_vars_map);
        let and = ctx.arena.and(result, other);
        output.push(and);

        // Update the demanded mask
        let demanded = (1 << var_idx) | demanded_vars_map[&other];
        demanded_vars_map.insert(and, demanded);
    }

    // Compute the union of all demanded variables
    let mut demanded_sum: u32 = 0;
    for id in output.iter() {
        demanded_sum |= demanded_vars_map[id];
    }

    // Compute the XOR of all the terms.
    let mut xored = ctx.arena.xor_many(&output);
    demanded_vars_map.insert(xored, demanded_sum);

    if has {
        let width = ctx.arena.get_width(xored);
        let xor_mask = ctx.arena.constant(get_modulo_mask(width), width);
        xored = ctx.arena.xor(xor_mask, xored);
        demanded_vars_map.insert(xored, demanded_sum);
    }

    return xored;
}

pub fn get_demanded_vars_mask(
    ctx: &Context,
    idx: AstIdx,
    variables: *const AstIdx,
    variable_count: u32,
    demanded_vars_map: &mut AHashMap<AstIdx, u32>,
) -> u32 {
    if let Some(mask) = demanded_vars_map.get(&idx) {
        return *mask;
    }

    let mask: u32 = match ctx.arena.get_node(idx) {
        SimpleAst::Symbol { id, width } => {
            let mut var_idx = u32::MAX;
            for i in 0..variable_count {
                unsafe {
                    if *variables.wrapping_add(i as usize) == idx {
                        var_idx = i;
                        break;
                    }
                }
            }

            if var_idx == u32::MAX {
                panic!("Variable not found!");
            }

            1 << var_idx
        }
        SimpleAst::Neg { a } => {
            get_demanded_vars_mask(ctx, *a, variables, variable_count, demanded_vars_map)
        }
        SimpleAst::And { a, b } | SimpleAst::Xor { a, b } | SimpleAst::And { a, b } => {
            let a_mask =
                get_demanded_vars_mask(ctx, *a, variables, variable_count, demanded_vars_map);
            let b_mask =
                get_demanded_vars_mask(ctx, *b, variables, variable_count, demanded_vars_map);
            a_mask | b_mask
        }
        SimpleAst::Constant { c, width } => 0,

        _ => panic!("Unexpected node type!"),
    };

    demanded_vars_map.insert(idx, mask);
    return mask;
}

pub fn simplify_rec(
    ctx: &mut Context,
    db: &mut TruthTableDatabase,
    idx: AstIdx,
    variables: *const AstIdx,
    variable_count: u32,
    page: *mut u8, // Mutable RWX page for JIT evaluation. TODO: Use parallel boolean jit instead of traditional semi-linear JIT)
    demanded_vars_map: &mut AHashMap<AstIdx, u32>,
) -> AstIdx {
    let ast = ctx.arena.get_node(idx).clone();
    // If the node is a symbol, constant, or negation, we can either return it or recurse onto the only chilld.
    if let SimpleAst::Symbol { id, width } = ast {
        return idx;
    }
    if let SimpleAst::Constant { c, width } = ast {
        return idx;
    }
    if let SimpleAst::Neg { a } = ast {
        let child = simplify_rec(
            ctx,
            db,
            a,
            variables,
            variable_count,
            page,
            demanded_vars_map,
        );

        return ctx.arena.neg(child);
    }

    // If we have four or less variables, pull the optimal representation from the truth table.
    let curr_mask = get_demanded_vars_mask(ctx, idx, variables, variable_count, demanded_vars_map);
    let count = curr_mask.count_ones();
    if count == 1 {
        return idx;
    }
    if count <= 4 {
        return simplify_via_lookup_table(ctx, db, idx, variables, variable_count, curr_mask, page);
    }

    // Otherwise we cannot use a lookup table.
    // In this case we want to check if we can decompose the boolean into terms with disjoint variable sets.
    let mut worklist: Vec<AstIdx> = Vec::new();
    worklist.push(idx);

    // First recursively hoist all associative terms.
    // TODO: Rewrite negations as XORs, then normalize after the fact.
    let mut terms: Vec<AstIdx> = Vec::new();
    let kind = get_opcode(ctx, idx);

    // Hoist children of the same kind.
    let visit = |terms: &mut Vec<AstIdx>, wkl: &mut Vec<AstIdx>, id: AstIdx| {
        let opcode = get_opcode(ctx, id);
        if opcode != kind {
            terms.push(id);
            return;
        }

        wkl.push(get_op0(ctx, id));
        wkl.push(get_op1(ctx, id));
    };

    // Recurisely hoist associative children.
    while true {
        if worklist.len() == 0 {
            break;
        }

        let current = worklist.pop().unwrap();
        if get_opcode(ctx, current) != kind {
            terms.push(current);
            continue;
        }

        let a = get_op0(ctx, current);
        let b = get_op1(ctx, current);
        visit(&mut terms, &mut worklist, a);
        visit(&mut terms, &mut worklist, b);
    }

    // Invariant: All terms must not be of the same kind as the original input id.
    // Do a disjoint variable decomposition. We can start from the least common variables and work our way up.
    let mut decompositions: Vec<(u32, AstIdx)> = Vec::new();
    for term in terms.iter() {
        let demanded_mask =
            get_demanded_vars_mask(ctx, *term, variables, variable_count, demanded_vars_map);

        let mut found = false;
        for i in 0..decompositions.len() {
            let (old_mask, old_id) = decompositions[i];
            let sum = old_mask | demanded_mask;
            if sum.count_ones() <= 4 {
                //let new_id = ctx.arena.or(old_id, *term);
                let new_id = match ast {
                    SimpleAst::And { a, b } => ctx.arena.and(old_id, *term),
                    SimpleAst::Or { a, b } => ctx.arena.or(old_id, *term),
                    SimpleAst::Xor { a, b } => ctx.arena.xor(old_id, *term),
                    _ => panic!("Unexpected node type!"),
                };
                decompositions[i] = (sum, new_id);
                found = true;
                break;
            }
        }

        if found {
            continue;
        }

        decompositions.push((demanded_mask, *term));
    }

    let mut simplified: Option<AstIdx> = None;

    // Recurisvely simplify each term.
    for (_, term) in decompositions.iter() {
        let reduced = simplify_rec(
            ctx,
            db,
            *term,
            variables,
            variable_count,
            page,
            demanded_vars_map,
        );

        if simplified.is_none() {
            simplified = Some(reduced);
        } else {
            simplified = match ast {
                SimpleAst::And { a, b } => Some(ctx.arena.and(simplified.unwrap(), reduced)),
                SimpleAst::Or { a, b } => Some(ctx.arena.or(simplified.unwrap(), reduced)),
                SimpleAst::Xor { a, b } => Some(ctx.arena.xor(simplified.unwrap(), reduced)),
                _ => panic!("Unexpected node type!"),
            };
        }
    }

    return simplified.unwrap();
}

pub fn simplify_via_lookup_table(
    ctx: &mut Context,
    db: &mut TruthTableDatabase,
    idx: AstIdx,
    variables: *const AstIdx,
    variable_count: u32,
    demanded_mask: u32,
    page: *mut u8, // Mutable RWX page for JIT evaluation
) -> AstIdx {
    // Collect the variables that are demanded.
    let var_set: &mut Vec<AstIdx> = &mut Vec::with_capacity(demanded_mask.count_ones() as usize);
    for i in 0..variable_count {
        let mask = 1 << i;
        if (mask & demanded_mask) != 0 {
            let var = unsafe { *variables.wrapping_add(i as usize) };
            var_set.push(var);
        }
    }

    let w = ctx.arena.get_width(idx);
    let num_combinations: u32 = (2 as u32).pow(var_set.len() as u32);

    let rv: &mut Vec<u64> = &mut vec![0; num_combinations as usize];
    let rv_slice = rv.as_mut_ptr();

    // Construct a result vector
    // TODO: Use parallel boolean jit instead of traditional semi-linear JIT
    unsafe {
        ContextJit(
            ctx,
            idx,
            1,
            1,
            1,
            var_set.as_ptr(),
            var_set.len() as u64,
            num_combinations as u64,
            page,
            rv_slice,
        );
    }

    let mut truth_table: u64 = 0;
    for i in 0..num_combinations {
        let result = rv[i as usize];
        truth_table |= (result << i);
    }

    let boolean = TruthTableDatabase::get_truth_table_entry(
        db,
        ctx,
        var_set.len() as u32,
        var_set.as_ptr(),
        truth_table as usize,
    );

    return boolean;
}

#[inline]
pub fn subtract_coeff_boolean(
    table: &TruthTable,
    safe_arr: &mut [u64],
    bit_index: u16,
    coeff: u8,
    first_start: u32,
    width: u32,
    only_one_var: bool,
    true_mask: u64,
) {
    let offset = (bit_index as u32) * width;
    let v0 = true_mask.trailing_zeros();
    let group_size_1: u32 = 1 << v0;
    let period_1 = 2 * group_size_1;

    let mut start = first_start;
    while start < width {
        let mut i = start;
        while i < start + group_size_1 {
            let shares_variables = ((i as u64) & true_mask) == true_mask;
            if (i != first_start) && (only_one_var || shares_variables) {
                let val = 1 & (table.get_bit(safe_arr, i) - coeff);
                table.set_bit(safe_arr, i, val);
            }

            i += 1;
        }

        start += period_1;
    }
}

pub fn get_group_size_index(mask: u64) -> u32 {
    let mut sum: u32 = 0;
    let mut var_mask = mask;
    while var_mask != 0 {
        let lsb = var_mask.trailing_zeros();
        sum += get_group_size(lsb);

        var_mask ^= (1 << lsb);
    }

    return sum;
}

pub fn get_group_size(idx: u32) -> u32 {
    return 1 << idx;
}

#[derive(Copy, Clone)]
struct Location {
    pub register: Register,
}

impl Location {
    pub fn is_register(&self) -> bool {
        return self.register != Register::None;
    }

    pub fn reg(r: Register) -> Location {
        return Location { register: r };
    }

    pub fn stack() -> Location {
        return Location {
            register: Register::None,
        };
    }
}

trait Exists {
    fn exists(&self) -> bool;
}

// Assert that `NodeInfo` is 8 bytes in size
const _: () = [(); 1][(core::mem::size_of::<NodeInfo>() == 8) as usize ^ 1];

#[derive(Copy, Clone)]
struct NodeInfo {
    pub num_uses: u16,
    pub var_idx: u16,
    pub slot_idx: u16,
    pub exists: u16,
}

impl NodeInfo {
    pub fn new(num_instances: u16) -> Self {
        return NodeInfo {
            num_uses: num_instances,
            var_idx: 0,
            slot_idx: u16::MAX,
            exists: 1,
        };
    }
}

impl From<u64> for NodeInfo {
    fn from(value: u64) -> Self {
        unsafe {
            let ptr = (&value) as *const u64 as *const NodeInfo;
            *ptr
        }
    }
}

impl Into<u64> for NodeInfo {
    fn into(self) -> u64 {
        unsafe {
            let ptr = (&self) as *const NodeInfo as *const u64;
            *ptr
        }
    }
}

impl Exists for NodeInfo {
    fn exists(&self) -> bool {
        return self.exists != 0;
    }
}

struct AuxInfoStorage<T: From<u64> + Into<u64> + Exists> {
    _marker: PhantomData<T>,
}

impl<T: From<u64> + Into<u64> + Exists> AuxInfoStorage<T> {
    pub fn contains(ctx: &mut Context, idx: AstIdx) -> bool {
        let value = Self::get(ctx, idx);
        return value.exists();
    }

    pub fn get(ctx: &mut Context, idx: AstIdx) -> T {
        let value = ctx.arena.get_data(idx).imut_data;
        return T::from(value);
    }

    pub fn get_unsafe(ptr: *mut (SimpleAst, AstData), idx: AstIdx) -> T {
        unsafe {
            let value = (*ptr.add(idx.0 as usize)).1.imut_data;
            return T::from(value);
        }
    }

    pub fn get_ptr_unsafe(ptr: *mut (SimpleAst, AstData), idx: AstIdx) -> *mut NodeInfo {
        unsafe {
            //let data = &mut (*ptr.add(idx.0 as usize)).1;
            //return (&mut (*ptr).1.imut_data) as *mut u64 as *mut NodeInfo;
            return (&mut (*ptr.add(idx.0 as usize)).1.imut_data) as *mut u64 as *mut NodeInfo;
        }
    }

    pub fn set(ctx: &mut Context, idx: AstIdx, value: T) {
        ctx.arena.get_data_mut(idx).imut_data = value.into();
    }

    pub fn set_unsafe(ptr: *mut (SimpleAst, AstData), idx: AstIdx, value: T) {
        unsafe {
            let data = &mut (*ptr.add(idx.0 as usize)).1;
            data.imut_data = value.into();
        }
    }

    pub fn try_get(ctx: &mut Context, idx: AstIdx) -> Option<T> {
        let value = Self::get(ctx, idx);
        if value.exists() {
            return Some(value);
        }

        return None;
    }

    pub fn try_get_unsafe(ptr: *mut (SimpleAst, AstData), idx: AstIdx) -> Option<T> {
        let value = Self::get_unsafe(ptr, idx);
        if value.exists() {
            return Some(value);
        }

        return None;
    }
}

const ARGS_REGISTER: Register = Register::RCX;
const LOCALS_REGISTER: Register = Register::RBP;
const SCRATCH1: Register = Register::RSI;
const SCRATCH2: Register = Register::RDI;

static VOLATILE_REGS: &'static [Register] = &[
    Register::RAX,
    Register::RCX,
    Register::RDX,
    Register::R8,
    Register::R9,
    Register::R10,
    Register::R11,
];
static NONVOLATILE_REGS: &'static [Register] = &[
    Register::RBP,
    Register::RBX,
    Register::RDI,
    Register::RSI,
    Register::R12,
    Register::R13,
    Register::R14,
    Register::R15,
];

struct Amd64OptimizingJit<T: IAmd64Assembler> {
    // Available registers for allocation.
    free_registers: Vec<Register>,
    // Post order traversal of the DAG.
    dfs: Vec<AstIdx>,
    // Number of allocated stack slots
    slot_count: u16,
    // Stack of in-use locations.
    stack: Vec<Location>,
    _marker: PhantomData<T>,
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct StTuple {
    owner: AstIdx,
    value: AstIdx,
}

impl StTuple {
    pub fn new(owner: AstIdx, value: AstIdx) -> Self {
        return StTuple { owner, value };
    }
}

impl<T: IAmd64Assembler> Amd64OptimizingJit<T> {
    fn new() -> Self {
        return Amd64OptimizingJit {
            free_registers: vec![
                Register::RAX,
                Register::RDX,
                Register::RBX,
                Register::R8,
                Register::R9,
                Register::R10,
                Register::R11,
                Register::R12,
                Register::R13,
                Register::R14,
                Register::R15,
            ],
            dfs: Vec::with_capacity(64),
            slot_count: 0,
            stack: Vec::with_capacity(16),
            _marker: PhantomData,
        };
    }

    #[inline(never)]
    fn compile(
        &mut self,
        ctx: &mut Context,
        assembler: &mut T,
        idx: AstIdx,
        variables: &Vec<AstIdx>,
        page_ptr: *mut u8,
        use_iced_backend: bool,
    ) -> u64 {
        // Collect necessary information about nodes for JITing (dfs order, how many users a node has).
        //Self::collect_info_fast(ctx, idx, &mut self.dfs);

        unsafe {
            let p = ctx.arena.elements.as_mut_ptr();
            Self::collect_info_unsafe(p, idx, &mut self.dfs);
        }

        // Store each variables argument index
        for i in 0..variables.len() {
            let var_idx = variables[i];
            let mut info = AuxInfoStorage::<NodeInfo>::get(ctx, var_idx);
            info.var_idx = i as u16;
            AuxInfoStorage::<NodeInfo>::set(ctx, var_idx, info);
        }

        // Compile the instructions to x86.
        self.lower_to_x86(ctx, assembler);

        // Clear each node's mutable data.
        for id in self.dfs.iter() {
            let mut info = AuxInfoStorage::<NodeInfo>::get(ctx, *id);
            AuxInfoStorage::<NodeInfo>::set(ctx, *id, NodeInfo::from(0));
        }

        // If using the fast assembler backend, we've already emitted x86.
        // However the stack pointer adjustment needs to fixed up, because it wasn't known during prologue emission.
        if !use_iced_backend {
            Self::fixup_frame_ptr(page_ptr, self.slot_count.into());
            return 0;
        }

        // Otherwise adjust the rsp in iced.
        let mut instructions = assembler.get_instructions();
        Self::fixup_iced_frame_ptr(&mut instructions, self.slot_count.into());

        // Write the instructions to memory.
        // ICED internally emits a list of assembled instructions rather than raw x86 bytes
        // so this must be done after the fact.
        return Self::write_instructions(page_ptr, &instructions);
    }

    #[inline(never)]
    fn compile_benchmark(
        &mut self,
        ctx: &mut Context,
        assembler: &mut T,
        idx: AstIdx,
        variables: &Vec<AstIdx>,
        page_ptr: *mut u8,
        use_iced_backend: bool,
    ) {
        let arr = ctx.arena.elements.as_mut_ptr();
        let mut st: Vec<StTuple> = Vec::with_capacity(1024);

        for i in 0..5000000 {
            st.clear();
            self.dfs.clear();
            //Self::collect_info(ctx, idx, &mut self.dfs);

            unsafe {
                let p = ctx.arena.elements.as_mut_ptr();
                Self::collect_info_unsafe(p, idx, &mut self.dfs);
            }

            /*
            if i % 10000 == 0 || i == 1 {
                for id in self.dfs.iter() {
                    let ast = ctx.arena.get_node(*id);
                    let str = AstPrinter::print(ctx, &ast.clone());
                    println!("DFS[{}]: {} ", id.0, str);
                }
                println!("\n\n\nReceived {} dfs members.", self.dfs.len());
            }
            */

            // Clear each node's mutable data.
            for id in self.dfs.iter() {
                let mut info = AuxInfoStorage::<NodeInfo>::get(ctx, *id);
                AuxInfoStorage::<NodeInfo>::set(ctx, *id, NodeInfo::from(0));
            }
        }

        unsafe {
            *page_ptr = self.dfs.last().unwrap().0 as u8;
        }
    }

    fn collect_info(ctx: &mut Context, idx: AstIdx, dfs: &mut Vec<AstIdx>) {
        let existing = AuxInfoStorage::<NodeInfo>::try_get(ctx, idx);
        if existing.is_some() {
            dfs.push(idx);
            return;
        }

        let node = ctx.arena.get_node(idx).clone();
        match node {
            SimpleAst::Add { a, b }
            | SimpleAst::Mul { a, b }
            | SimpleAst::Pow { a, b }
            | SimpleAst::And { a, b }
            | SimpleAst::Or { a, b }
            | SimpleAst::Xor { a, b }
            | SimpleAst::Lshr { a, b } => {
                Self::collect_info(ctx, a, dfs);
                Self::collect_info(ctx, b, dfs);

                Self::inc_users(ctx, a);
                Self::inc_users(ctx, b);
            }
            SimpleAst::Neg { a } | SimpleAst::Zext { a, .. } | SimpleAst::Trunc { a, .. } => {
                Self::collect_info(ctx, a, dfs);
                Self::inc_users(ctx, a);
            }
            SimpleAst::Constant { .. } | SimpleAst::Symbol { .. } => (),
        }

        dfs.push(idx);
        AuxInfoStorage::<NodeInfo>::set(ctx, idx, NodeInfo::new(0));
    }

    fn collect_info_unsafe(arr: *mut (SimpleAst, AstData), idx: AstIdx, dfs: &mut Vec<AstIdx>) {
        //let existing = AuxInfoStorage::<NodeInfo>::try_get(ctx, idx);
        //let existing = AuxInfoStorage::<NodeInfo>::get_unsafe(arr, idx);
        let p_existing = AuxInfoStorage::<NodeInfo>::get_ptr_unsafe(arr, idx);
        if unsafe { (*p_existing).exists() } {
            Self::inc_users_unsafe(arr, idx);
            dfs.push(idx);
            return;
        }

        //let node = ctx.arena.get_node(idx).clone();
        let ptr = unsafe { arr.add(idx.0 as usize) };
        let node = unsafe { &(*ptr).0 };
        match node {
            SimpleAst::Add { a, b }
            | SimpleAst::Mul { a, b }
            | SimpleAst::Pow { a, b }
            | SimpleAst::And { a, b }
            | SimpleAst::Or { a, b }
            | SimpleAst::Xor { a, b }
            | SimpleAst::Lshr { a, b } => {
                Self::collect_info_unsafe(arr, *a, dfs);
                Self::collect_info_unsafe(arr, *b, dfs);
            }
            SimpleAst::Neg { a } | SimpleAst::Zext { a, .. } | SimpleAst::Trunc { a, .. } => {
                Self::collect_info_unsafe(arr, *a, dfs);
            }
            SimpleAst::Constant { .. } | SimpleAst::Symbol { .. } => (),
        }

        AuxInfoStorage::<NodeInfo>::set_unsafe(arr, idx, NodeInfo::new(1));
        dfs.push(idx);
        //AuxInfoStorage::<NodeInfo>::set(ctx, idx, NodeInfo::new(0));
    }

    /*
    fn collect_info_fast(ctx: &mut Context, idx: AstIdx, dfs: &mut Vec<AstIdx>) {
        let existing = AuxInfoStorage::<NodeInfo>::try_get(ctx, idx);
        if existing.is_some() {
            dfs.push(idx);
            Self::inc_users(ctx, idx);
            return;
        }

        let node = ctx.arena.get_node(idx).clone();
        match node {
            SimpleAst::Add { a, b }
            | SimpleAst::Mul { a, b }
            | SimpleAst::Pow { a, b }
            | SimpleAst::And { a, b }
            | SimpleAst::Or { a, b }
            | SimpleAst::Xor { a, b }
            | SimpleAst::Lshr { a, b } => {
                Self::collect_info_fast(ctx, a, dfs);
                Self::collect_info_fast(ctx, b, dfs);
            }
            SimpleAst::Neg { a } | SimpleAst::Zext { a, .. } | SimpleAst::Trunc { a, .. } => {
                Self::collect_info_fast(ctx, a, dfs);
            }
            SimpleAst::Constant { .. } | SimpleAst::Symbol { .. } => (),
        }

        dfs.push(idx);
        AuxInfoStorage::<NodeInfo>::set(ctx, idx, NodeInfo::new(1));
    }
    */

    fn inc_users(ctx: &mut Context, idx: AstIdx) {
        let mut info = AuxInfoStorage::<NodeInfo>::get(ctx, idx);
        info.num_uses = info.num_uses.add(1);
        AuxInfoStorage::<NodeInfo>::set(ctx, idx, info);
    }

    fn inc_users_unsafe(ptr: *mut (SimpleAst, AstData), idx: AstIdx) {
        let mut info = AuxInfoStorage::<NodeInfo>::get_unsafe(ptr, idx);
        info.num_uses = info.num_uses.add(1);
        AuxInfoStorage::<NodeInfo>::set_unsafe(ptr, idx, info);
    }

    #[inline(never)]
    fn lower_to_x86(&mut self, ctx: &mut Context, assembler: &mut T) {
        // rcx reserved for local variables ptr (or all vars in the case of a semi-linear result vector)
        // RSI, RDI reserved for temporary use

        // Emit the prologue. Initially we reserve space for u32::MAX slots, which we will adjust later.
        Self::emit_prologue(assembler, u32::MAX);

        for i in 0..self.dfs.len() {
            let idx = unsafe { *self.dfs.get_unchecked(i) };
            let node_info = AuxInfoStorage::<NodeInfo>::get(ctx, idx);
            if node_info.num_uses > 1 && node_info.slot_idx != u16::MAX {
                self.load_slot_value(assembler, node_info.slot_idx as u32);
                continue;
            }

            let width = ctx.arena.get_width(idx) as u32;
            let node = ctx.arena.get_node(idx).clone();
            match node {
                SimpleAst::Add { a, b }
                | SimpleAst::Mul { a, b }
                | SimpleAst::Pow { a, b }
                | SimpleAst::And { a, b }
                | SimpleAst::Or { a, b }
                | SimpleAst::Xor { a, b }
                | SimpleAst::Lshr { a, b } => {
                    self.lower_binop(ctx, assembler, idx, node, width, node_info)
                }
                SimpleAst::Constant { c, width } => self.lower_constant(assembler, c),
                SimpleAst::Symbol { .. } => {
                    self.lower_variable(assembler, node_info.var_idx.into(), width)
                }
                SimpleAst::Neg { .. } | SimpleAst::Zext { .. } => self.lower_unary_op(
                    ctx,
                    assembler,
                    idx,
                    width,
                    node_info,
                    matches!(node, SimpleAst::Neg { .. }),
                ),
                SimpleAst::Trunc { a, to } => {
                    let w = ctx.get_width(a);
                    self.lower_zext(ctx, assembler, idx, w.into(), node_info)
                }
            }
        }

        if self.stack.len() != 1 {
            panic!("Unbalanced stack after lowering!");
        }

        let result = self.stack.pop().unwrap();
        if result.is_register() {
            assembler.mov_reg_reg(Register::RAX, result.register);
        } else {
            assembler.pop_reg(Register::RAX);
        }

        // Reduce the result modulo 2**w
        let w = ctx.get_width(*self.dfs.last().unwrap());
        assembler.movabs_reg_imm64(SCRATCH1, get_modulo_mask(w));
        assembler.and_reg_reg(Register::RAX, SCRATCH1);

        Self::emit_epilogue(assembler, self.slot_count as u32);
    }

    fn load_slot_value(&mut self, assembler: &mut T, slot_idx: u32) {
        if !self.free_registers.is_empty() {
            let t = self.free_registers.pop().unwrap();
            assembler.mov_reg_mem64(t, LOCALS_REGISTER, (slot_idx * 8) as i32);
            self.stack.push(Location::reg(t));
            return;
        }

        assembler.push_mem64(LOCALS_REGISTER, 8 * (slot_idx as i32));
        self.stack.push(Location::stack());
    }

    fn lower_binop(
        &mut self,
        ctx: &mut Context,
        assembler: &mut T,
        idx: AstIdx,
        node: SimpleAst,
        width: u32,
        node_info: NodeInfo,
    ) {
        let rhs_loc = self.stack.pop().unwrap();

        // If the rhs is stored in a register, we use it.
        let mut rhs_dest = SCRATCH1;
        if rhs_loc.is_register() {
            rhs_dest = rhs_loc.register;
        }
        // If stored on the stack, pop into scratch register
        else {
            assembler.pop_reg(rhs_dest);
        }

        // Regardless we have the rhs in a register now.
        let lhs_loc = self.stack.pop().unwrap();
        let mut lhs_dest = SCRATCH2;
        if lhs_loc.is_register() {
            lhs_dest = lhs_loc.register;
        } else {
            assembler.pop_reg(lhs_dest);
        }

        match node {
            SimpleAst::Add { a, b } => assembler.add_reg_reg(lhs_dest, rhs_dest),
            SimpleAst::Mul { a, b } => assembler.imul_reg_reg(lhs_dest, rhs_dest),
            SimpleAst::And { a, b } => assembler.and_reg_reg(lhs_dest, rhs_dest),
            SimpleAst::Or { a, b } => assembler.or_reg_reg(lhs_dest, rhs_dest),
            SimpleAst::Xor { a, b } => assembler.xor_reg_reg(lhs_dest, rhs_dest),
            SimpleAst::Lshr { a, b } => {
                if width % 8 != 0 {
                    panic!("Cannot jit lshr with non power of 2 width!");
                }

                // Reduce shift count modulo the bit width of the operation
                // TODO: (a) Handle non power of two bit widths,
                //       (b) shift beyond bounds should yield zero
                assembler.and_reg_imm32(rhs_dest, width - 1);

                assembler.push_reg(Register::RCX);
                assembler.mov_reg_reg(Register::RCX, rhs_dest);
                assembler.shr_reg_cl(lhs_dest);
                assembler.pop_reg(Register::RCX);
            }
            SimpleAst::Pow { a, b } => {
                for r in VOLATILE_REGS.iter() {
                    assembler.push_reg(*r);
                }

                assembler.mov_reg_reg(Register::RCX, lhs_dest);
                assembler.mov_reg_reg(Register::RDX, rhs_dest);

                // TODO: Inline 'pow' function
                assembler.movabs_reg_imm64(Register::R11, Pow as *const () as u64);
                assembler.sub_reg_imm32(Register::RSP, 32);
                assembler.call_reg(Register::R11);
                assembler.add_reg_imm32(Register::RSP, 32);
                assembler.mov_reg_reg(SCRATCH1, Register::RAX);

                // Restore volatile registers
                for &reg in VOLATILE_REGS.iter().rev() {
                    assembler.pop_reg(reg);
                }

                assembler.mov_reg_reg(lhs_dest, SCRATCH1);
            }
            _ => unreachable!("Node is not a binary operator"),
        }

        Self::reduce_register_modulo(assembler, width, lhs_dest, SCRATCH1);

        if rhs_loc.is_register() {
            self.free_registers.push(rhs_loc.register);
        }

        // If there are multiple users of this value, throw it in a stack slot.
        let multiple_users = node_info.num_uses > 1;
        if multiple_users {
            assembler.mov_mem64_reg(LOCALS_REGISTER, 8 * (self.slot_count as i32), lhs_dest);
            self.assign_value_slot(ctx, idx, node_info);
        }

        // If the lhs is already in a register, don't move it!
        if lhs_dest != SCRATCH2 {
            self.stack.push(Location::reg(lhs_dest));
            return;
        }

        // Try to allocate a reg for this value
        if self.free_registers.len() > 0 {
            let dest = self.free_registers.pop().unwrap();
            assembler.mov_reg_reg(dest, lhs_dest);
            self.stack.push(Location::reg(dest));
        }
        // Otherwise this goes on the stack
        else {
            assembler.push_reg(lhs_dest);
            self.stack.push(Location::stack());
        }

        if lhs_loc.is_register() {
            self.free_registers.push(lhs_loc.register);
        }
    }

    fn lower_constant(&mut self, assembler: &mut T, c: u64) {
        if !self.free_registers.is_empty() {
            let dest = self.free_registers.pop().unwrap();
            assembler.movabs_reg_imm64(dest, c);
            self.stack.push(Location::reg(dest));
            return;
        }

        assembler.movabs_reg_imm64(SCRATCH1, c);
        assembler.push_reg(SCRATCH1);
        self.stack.push(Location::stack());
    }

    fn lower_variable(&mut self, assembler: &mut T, var_arr_idx: i32, width: u32) {
        if !self.free_registers.is_empty() {
            let dest = self.free_registers.pop().unwrap();
            assembler.mov_reg_mem64(dest, ARGS_REGISTER, var_arr_idx * 8);
            Self::reduce_register_modulo(assembler, width, dest, SCRATCH1);
            self.stack.push(Location::reg(dest));
            return;
        }

        assembler.push_mem64(ARGS_REGISTER, var_arr_idx * 8);
        self.stack.push(Location::stack());
        Self::reduce_location_modulo(assembler, Location::stack(), width);
    }

    fn lower_unary_op(
        &mut self,
        ctx: &mut Context,
        assembler: &mut T,
        idx: AstIdx,
        width: u32,
        node_info: NodeInfo,
        is_neg: bool,
    ) {
        let curr = self.stack.pop().unwrap();
        let mut dest_reg = SCRATCH1;
        if curr.is_register() {
            dest_reg = curr.register;
        } else {
            assembler.pop_reg(dest_reg);
        }

        if is_neg {
            assembler.not_reg(dest_reg);
            Self::reduce_register_modulo(assembler, width, dest_reg, SCRATCH2);
        } else {
            assembler.movabs_reg_imm64(SCRATCH2, get_modulo_mask(width as u8));
            assembler.and_reg_reg(dest_reg, SCRATCH2);
        }

        // If there are multiple users, store the value in a slot.
        let multiple_users = node_info.num_uses > 1;
        if multiple_users {
            assembler.mov_mem64_reg(LOCALS_REGISTER, 8 * (self.slot_count as i32), dest_reg);
            self.assign_value_slot(ctx, idx, node_info);
        }

        if dest_reg != SCRATCH1 {
            self.stack.push(Location::reg(dest_reg));
            return;
        }

        if !self.free_registers.is_empty() {
            let dest = self.free_registers.pop().unwrap();
            assembler.mov_reg_reg(dest, dest_reg);
            self.stack.push(Location::reg(dest));
            return;
        }

        // Otherwise this goes on the stack
        assembler.push_reg(dest_reg);
        self.stack.push(Location::stack());
    }

    fn lower_zext(
        &mut self,
        ctx: &mut Context,
        assembler: &mut T,
        idx: AstIdx,
        from_width: u32,
        node_info: NodeInfo,
    ) {
        // If we only have one user, this is a no-op. The result we care about is already on the location stack,
        // and the zero-extension is implicit.
        let peek = self.stack.pop().unwrap();
        self.stack.push(peek);

        // Because we are zero extending, we need to reduce the value modulo 2**w
        // In other places we can get away with omitting this step.
        Self::reduce_location_modulo(assembler, peek, from_width);

        if node_info.num_uses <= 1 {
            return;
        }

        if peek.is_register() {
            assembler.mov_mem64_reg(LOCALS_REGISTER, 8 * (self.slot_count as i32), peek.register);
        } else {
            assembler.mov_reg_mem64(SCRATCH1, Register::RSP, 0);
            assembler.mov_mem64_reg(LOCALS_REGISTER, 8 * (self.slot_count as i32), SCRATCH1);
        }

        self.assign_value_slot(ctx, idx, node_info);
    }

    fn reduce_register_modulo(
        assembler: &mut T,
        width: u32,
        dst_reg: Register,
        free_reg: Register,
    ) {
        debug_assert!(dst_reg != free_reg);
        if width == 64 {
            return;
        }

        let mask = get_modulo_mask(width as u8);
        assembler.movabs_reg_imm64(free_reg, mask);
        assembler.and_reg_reg(dst_reg, free_reg);
    }

    fn reduce_location_modulo(assembler: &mut T, loc: Location, width: u32) {
        if width == 64 {
            return;
        }

        let mask = get_modulo_mask(width as u8);
        assembler.movabs_reg_imm64(SCRATCH1, mask);
        if loc.is_register() {
            assembler.and_reg_reg(loc.register, SCRATCH1);
        } else {
            assembler.and_mem64_reg(Register::RSP, 0, SCRATCH1);
        }
    }

    fn assign_value_slot(&mut self, ctx: &mut Context, idx: AstIdx, mut node_info: NodeInfo) {
        node_info.slot_idx = self.slot_count;
        AuxInfoStorage::<NodeInfo>::set(ctx, idx, node_info);
        self.slot_count = self.slot_count.checked_add(1).unwrap();
    }

    fn emit_prologue(assembler: &mut T, num_stack_slots: u32) {
        // Push all nonvolatile registers
        for reg in NONVOLATILE_REGS.iter() {
            assembler.push_reg(*reg);
        }

        // Allocate stack space for local variables
        assembler.sub_reg_imm32(Register::RSP, (num_stack_slots * 8));
        // Point rbp to the local var array
        assembler.mov_reg_reg(LOCALS_REGISTER, Register::RSP);
        // mov rbp, rsp
        assembler.mov_reg_reg(Register::RBP, Register::RSP);
    }

    fn emit_epilogue(assembler: &mut T, num_stack_slots: u32) {
        // Reset rsp
        assembler.add_reg_imm32(Register::RSP, 8 * num_stack_slots);
        // Restore nonvolatile registers (including rbp)
        for i in NONVOLATILE_REGS.iter().rev() {
            assembler.pop_reg(*i);
        }

        assembler.ret();
    }

    fn fixup_frame_ptr(ptr: *mut u8, slot_count: u32) {
        unsafe {
            let sub_rsp_start = ptr.add(12);
            let encoding = (*sub_rsp_start.cast::<u64>()) & 0xFF00FFFFFFFFFFFF;
            if encoding != 0x4800fffff8ec8148 {
                panic!("Rsp fixup position changed!");
            }

            let conv = slot_count * 8;
            *(sub_rsp_start.add(3).cast::<u32>()) = conv;
        }
    }

    fn fixup_iced_frame_ptr(instructions: &mut Vec<Instruction>, slot_count: u32) {
        let sub = instructions[8];
        if sub.code() != Code::Sub_rm64_imm8 && sub.code() != Code::Sub_rm64_imm32 {
            panic!("Rsp fixup position changed!");
        }

        instructions[8] =
            Instruction::with2(Code::Sub_rm64_imm32, Register::RSP, (slot_count * 8) as i32)
                .unwrap();
    }

    fn write_instructions(ptr: *mut u8, instructions: &Vec<Instruction>) -> u64 {
        let mut assembler = CodeAssembler::new(64).unwrap();
        for inst in instructions.iter() {
            assembler.add_instruction(*inst);
        }

        let bytes = assembler.assemble(ptr as u64).unwrap();
        unsafe {
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, bytes.len());
        }

        return bytes.len() as u64;
    }
}
