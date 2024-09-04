use std::{
    collections::{HashMap, HashSet},
    f32::consts::PI,
    ffi::{CStr, CString},
    u64,
};

use ahash::AHashMap;
use libc::{c_char, c_void};

use crate::{
    mba::{self, Context as MbaContext},
    truth_table_database::TruthTableDatabase,
};

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(C)]
pub struct AstIdx(pub u32);

pub struct Arena {
    elements: Vec<SimpleAst>,
    ast_to_idx: AHashMap<SimpleAst, AstIdx>,

    // Map a name to it's corresponds symbol index.
    symbol_ids: Vec<(String, AstIdx)>,
    name_to_symbol: AHashMap<(String, u8), u32>,
}

impl Arena {
    pub fn new() -> Self {
        let elements = Vec::with_capacity(65536);
        let ast_to_idx = AHashMap::with_capacity(65536);

        let symbol_ids = Vec::with_capacity(255);
        let name_to_symbol = AHashMap::with_capacity(255);

        Arena {
            elements: elements,
            ast_to_idx: ast_to_idx,

            symbol_ids: symbol_ids,
            name_to_symbol: name_to_symbol,
        }
    }

    pub fn add(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let width = self.get_bin_width(a, b);
        let cost = self.get_bin_cost(a, b);
        let has_poly = self.union_contains_poly_part(a, b);

        // Determine the "highest" classification of the two operands, defaulting to linear.
        let c1 = self.get_class(a);
        let c2 = self.get_class(b);
        let mut max = max_class(c1, c2, AstClass::Linear);

        // If the resulting option is not linear or semilinear, we need to check if one of the operands
        // is a bitwise operation with a constant. If so, the result is semilinear.
        max = try_make_semilinear(max, c1, c2);

        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: max,
        };

        return self.insert_ast_node(SimpleAst::Add { a, b, data });
    }

    pub fn mul(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let a_value = self.get_node(a);
        let b_value = self.get_node(b);

        // Apply constant folding for 1*x and 0*x.
        let mut is_one_part_constant = false;
        if let SimpleAst::Constant { c: c1, data } = a_value {
            is_one_part_constant = true;
            if *c1 == 1 {
                return b;
            } else if *c1 == 0 {
                return self.constant(0, self.get_width(a));
            }
        // TODO: If the second part is a constant, swap the operands and apply constant folding.
        } else if let SimpleAst::Constant { c: c1, data } = b_value {
            is_one_part_constant = true;
        }

        let width = self.get_bin_width(a, b);
        let cost = self.get_bin_cost(a, b);
        // If neither operand is a constant, or either operand contains a polynomial part, the result will contain a polynomial part.
        let has_poly = !is_one_part_constant || self.union_contains_poly_part(a, b);

        // Determine the "highest" classification of the two operands, defaulting to linear.
        let c1 = self.get_class(a);
        let c2 = self.get_class(b);
        let mut max = max_class(
            c1,
            c2,
            if !is_one_part_constant {
                AstClass::Nonlinear
            } else {
                AstClass::Linear
            },
        );

        max = try_make_semilinear(max, c1, c2);

        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: max,
        };

        return self.insert_ast_node(SimpleAst::Mul { a, b, data });
    }

    pub fn pow(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let width = self.get_bin_width(a, b);
        let cost = self.get_bin_cost(a, b);
        let data = AstData {
            width: width,
            cost: cost,
            has_poly: true,
            class: AstClass::Nonlinear,
        };

        return self.insert_ast_node(SimpleAst::Pow { a, b, data });
    }

    pub fn and(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let data = self.compute_bitwise_data(a, b);
        return self.insert_ast_node(SimpleAst::And { a, b, data });
    }

    pub fn or(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let data = self.compute_bitwise_data(a, b);

        return self.insert_ast_node(SimpleAst::Or { a, b, data });
    }

    pub fn xor(&mut self, a: AstIdx, b: AstIdx) -> AstIdx {
        let data = self.compute_bitwise_data(a, b);
        return self.insert_ast_node(SimpleAst::Xor { a, b, data });
    }

    pub fn neg(&mut self, a: AstIdx) -> AstIdx {
        let width = self.get_width(a);
        let cost = (1 as u32).saturating_add(self.get_data(a).cost);
        let has_poly = self.get_data(a).has_poly;

        let c1 = self.get_class(a);
        let max = max_class(c1, c1, AstClass::Bitwise);

        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: max,
        };
        return self.insert_ast_node(SimpleAst::Neg { a, data });
    }

    pub fn zext(&mut self, a: AstIdx, width: u8) -> AstIdx {
        let cost = (1 as u32).saturating_add(self.get_data(a).cost);
        let has_poly = self.get_has_poly(a);

        let mask = get_modulo_mask(self.get_width(a));
        let mask_node = self.constant(mask, width);
        let class = self.compute_bitwise_class(a, mask_node);
        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: class,
        };

        return self.insert_ast_node(SimpleAst::Zext { a, data });
    }

    pub fn constant(&mut self, c: u64, width: u8) -> AstIdx {
        let data = AstData {
            width: width,
            cost: 1,
            has_poly: false,
            class: AstClass::Bitwise,
        };

        // Reduce the constant modulo 2**width
        let constant = get_modulo_mask(width) & c;

        return self.insert_ast_node(SimpleAst::Constant { c: constant, data });
    }

    pub fn symbol(&mut self, id: u32, width: u8) -> AstIdx {
        let data = AstData {
            width: width,
            cost: 1,
            has_poly: false,
            class: AstClass::Bitwise,
        };

        return self.insert_ast_node(SimpleAst::Symbol { id: id, data });
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
        };

        let symbol_ast_idx = self.insert_ast_node(SimpleAst::Symbol {
            id: symbol_id,
            data,
        });
        self.symbol_ids.push((name, symbol_ast_idx));
        return symbol_ast_idx;
    }

    pub fn get_symbol_name(&self, symbol_id: u32) -> String {
        return self.symbol_ids[symbol_id as usize].0.clone();
    }

    pub fn insert_ast_node(&mut self, node: SimpleAst) -> AstIdx {
        if let Some(&idx) = self.ast_to_idx.get(&node) {
            return idx;
        }

        let idx = AstIdx(self.elements.len() as u32);
        self.elements.push(node.clone());
        self.ast_to_idx.insert(node, idx);
        idx
    }

    #[inline(always)]
    pub fn get_node(&self, idx: AstIdx) -> &SimpleAst {
        unsafe { &self.elements.get_unchecked(idx.0 as usize) }
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
            SimpleAst::Constant { c, data } => true,
            _ => false,
        }
    }

    pub fn get_data(&self, idx: AstIdx) -> AstData {
        let ast = self.get_node(idx);
        match ast {
            SimpleAst::Add { a, b, data }
            | SimpleAst::Mul { a, b, data }
            | SimpleAst::Pow { a, b, data }
            | SimpleAst::And { a, b, data }
            | SimpleAst::Or { a, b, data }
            | SimpleAst::Xor { a, b, data } => *data,
            SimpleAst::Neg { a, data } => *data,
            SimpleAst::Constant { c, data } => *data,
            SimpleAst::Symbol { id, data } => *data,
            SimpleAst::Zext { a, data } => *data,
        }
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
        let c2 = self.get_data(a).cost;
        (1 as u32).saturating_add(c1.saturating_add(c2))
    }

    pub fn union_contains_poly_part(&self, a: AstIdx, b: AstIdx) -> bool {
        let a_data = self.get_data(a);
        let b_data = self.get_data(b);
        return a_data.has_poly || b_data.has_poly;
    }

    pub fn compute_bitwise_data(&self, a: AstIdx, b: AstIdx) -> AstData {
        let width = self.get_bin_width(a, b);
        let cost = self.get_bin_cost(a, b);
        let has_poly = self.union_contains_poly_part(a, b);

        let max = self.compute_bitwise_class(a, b);
        let data = AstData {
            width: width,
            cost: cost,
            has_poly: has_poly,
            class: max,
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
#[repr(packed)]
pub struct AstData {
    // Bit width
    width: u8,

    // Size of the AST(note that this is the AST size rather than DAG size)
    cost: u32,

    // Indicates whether the node contains any nonlinear polynomial parts.
    has_poly: bool,

    // Classification of the ast
    class: AstClass,
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum SimpleAst {
    // Arithmetic operators:
    Add { a: AstIdx, b: AstIdx, data: AstData },
    Mul { a: AstIdx, b: AstIdx, data: AstData },
    Pow { a: AstIdx, b: AstIdx, data: AstData },
    // Bitwise operators:
    And { a: AstIdx, b: AstIdx, data: AstData },
    Or { a: AstIdx, b: AstIdx, data: AstData },
    Xor { a: AstIdx, b: AstIdx, data: AstData },
    Neg { a: AstIdx, data: AstData },
    // Literals:
    Constant { c: u64, data: AstData },
    Symbol { id: u32, data: AstData },
    // Special operators
    Zext { a: AstIdx, data: AstData },
}

pub struct Context {
    pub(crate) arena: Arena,
}

impl mba::Context for Context {
    fn add(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, data } = op1 {
            if let SimpleAst::Constant { c: c2, data } = op2 {
                let result = self.arena.constant((c1.wrapping_add(*c2)), data.width);

                return self.arena.get_node(result).clone();
            }
        }

        let add = self.arena.add(arg0, arg1);
        return self.arena.get_node(add).clone();
    }

    fn mul(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, data } = op1 {
            if let SimpleAst::Constant { c: c2, data } = op2 {
                let result = self.arena.constant((c1.wrapping_mul(*c2)), data.width);

                return self.arena.get_node(result).clone();
            }
        }

        let mul = self.arena.mul(arg0, arg1);
        return self.arena.get_node(mul).clone();
    }

    fn pow(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let pow = self.arena.pow(arg0, arg1);
        return self.arena.get_node(pow).clone();
    }

    fn and(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, data } = op1 {
            if let SimpleAst::Constant { c: c2, data } = op2 {
                let result = self.arena.constant((*c1 & *c2), data.width);

                return self.arena.get_node(result).clone();
            }
        }

        let and = self.arena.and(arg0, arg1);
        return self.arena.get_node(and).clone();
    }

    fn or(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, data } = op1 {
            if let SimpleAst::Constant { c: c2, data } = op2 {
                let result = self.arena.constant((*c1 | *c2), data.width);
                return self.arena.get_node(result).clone();
            }
        }

        let or = self.arena.or(arg0, arg1);
        return self.arena.get_node(or).clone();
    }

    fn xor(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        let op2 = self.arena.get_node(arg1);
        if let SimpleAst::Constant { c: c1, data } = op1 {
            if let SimpleAst::Constant { c: c2, data } = op2 {
                let result = self.arena.constant((*c1 ^ *c2), data.width);

                return self.arena.get_node(result).clone();
            }
        }
        let xor = self.arena.xor(arg0, arg1);
        return self.arena.get_node(xor).clone();
    }

    fn neg(&mut self, arg0: AstIdx) -> SimpleAst {
        let op1 = self.arena.get_node(arg0);
        if let SimpleAst::Constant { c: c1, data } = op1 {
            let result = self.arena.constant((!*c1), data.width);

            return self.arena.get_node(result).clone();
        }

        let neg = self.arena.neg(arg0);
        return self.arena.get_node(neg).clone();
    }

    fn zext(&mut self, arg0: AstIdx, data: AstData) -> SimpleAst {
        let zext = self.arena.zext(arg0, data.width);

        self.arena.get_node(zext).clone()
    }

    fn any(&mut self, arg0: AstIdx) -> SimpleAst {
        return self.arena.get_node(arg0).clone();
    }

    fn lookup_value(&mut self, arg0: AstIdx) -> Option<SimpleAst> {
        return Some(self.arena.get_node(arg0).clone());
    }

    fn lookup_id(&mut self, arg0: &SimpleAst) -> AstIdx {
        return self.arena.insert_ast_node(arg0.clone());
    }

    fn constant(&mut self, arg0: u64, data: AstData) -> SimpleAst {
        let id = self.arena.constant(arg0, data.width);
        return self.arena.get_node(id).clone();
    }

    fn symbol(&mut self, arg0: u32, data: AstData) -> SimpleAst {
        let id = self.arena.symbol(arg0, data.width);
        self.arena.get_node(id).clone()
    }

    fn fold_add(&mut self, arg0: AstIdx, arg1: AstIdx) -> SimpleAst {
        let add = |a: u64, b: u64| return a.wrapping_add(b);
        return fold_constant_binop(self, arg0, arg1, &add);
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
    if let SimpleAst::Constant { c: c1, data } = op1 {
        if let SimpleAst::Constant { c: c2, data } = op2 {
            let result = ctx.arena.constant((f(*c1, *c2)), data.width);

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
            SimpleAst::Add { a, b, data } => "+",
            SimpleAst::Mul { a, b, data } => "*",
            SimpleAst::Pow { a, b, data } => "**",
            SimpleAst::And { a, b, data } => "&",
            SimpleAst::Or { a, b, data } => "|",
            SimpleAst::Xor { a, b, data } => "^",
            SimpleAst::Neg { a, data } => "~",
            SimpleAst::Constant { c, data } => "",
            SimpleAst::Symbol { id, data } => "",
            SimpleAst::Zext { a, data } => "zx",
        };

        // Don't put parens for constants or symbols
        if operator != "" {
            self.output.push_str("(")
        }

        match ast {
            SimpleAst::Add { a, b, data }
            | SimpleAst::Mul { a, b, data }
            | SimpleAst::Pow { a, b, data }
            | SimpleAst::And { a, b, data }
            | SimpleAst::Or { a, b, data }
            | SimpleAst::Xor { a, b, data } => {
                self.print_node(ctx, ctx.arena.get_node(*a));
                self.output.push_str(&format!(" {} ", operator));
                self.print_node(ctx, ctx.arena.get_node(*b));
            }
            SimpleAst::Zext { a, data } => {
                self.print_node(ctx, ctx.arena.get_node(*a));
                self.output.push_str(&format!(" {} ", operator));
                self.output.push_str(&(data.width).to_string());
            }
            SimpleAst::Neg { a, data } => {
                self.output.push('~');
                self.print_node(ctx, ctx.arena.get_node(*a));
            }
            SimpleAst::Constant { c, data } => self.output.push_str(&(*c as i64).to_string()),
            SimpleAst::Symbol { id, data } => self
                .output
                .push_str(&ctx.arena.get_symbol_name(*id).clone()),
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
        SimpleAst::Add { a, b, data } => e(a).wrapping_add(e(b)),
        SimpleAst::Mul { a, b, data } => e(a).wrapping_mul(e(b)),
        SimpleAst::Pow { a, b, data } => todo!(),
        SimpleAst::And { a, b, data } => e(a) & e(b),
        SimpleAst::Or { a, b, data } => e(a) | e(b),
        SimpleAst::Xor { a, b, data } => e(a) ^ e(b),
        SimpleAst::Neg { a, data } => !e(a),
        SimpleAst::Constant { c, data } => *c,
        SimpleAst::Symbol { id, data } => *value_mapping.get(&idx).unwrap(),
        SimpleAst::Zext { a, data } => get_modulo_mask(data.width) & e(a),
    }
}

// Recursively apply ISLE over an AST.
pub fn recursive_simplify(ctx: &mut Context, idx: AstIdx) -> AstIdx {
    let mut ast = ctx.arena.get_node(idx).clone();

    match ast {
        SimpleAst::Add { a, b, data }
        | SimpleAst::Mul { a, b, data }
        | SimpleAst::Pow { a, b, data }
        | SimpleAst::And { a, b, data }
        | SimpleAst::Or { a, b, data }
        | SimpleAst::Xor { a, b, data } => {
            let op1 = recursive_simplify(ctx, a);
            let op2 = recursive_simplify(ctx, b);
            ast = match ast {
                SimpleAst::Add { a, b, data } => ctx.add(op1, op2),
                SimpleAst::Mul { a, b, data } => ctx.mul(op1, op2),
                SimpleAst::Pow { a, b, data } => ctx.pow(op1, op2),
                SimpleAst::And { a, b, data } => ctx.and(op1, op2),
                SimpleAst::Or { a, b, data } => ctx.or(op1, op2),
                SimpleAst::Xor { a, b, data } => ctx.xor(op1, op2),
                _ => unreachable!(),
            };
        }
        SimpleAst::Neg { a, data } => {
            let op1 = recursive_simplify(ctx, a);
            ast = ctx.neg(op1)
        }
        SimpleAst::Zext { a, data } => {
            let op1 = recursive_simplify(ctx, a);
            ast = SimpleAst::Zext { a: op1, data: data }
        }
        SimpleAst::Constant { c, data } => return idx,
        SimpleAst::Symbol { id, data } => return idx,
    }

    // Repeatedly invoke ISLE until a fixed point is reached.
    while true {
        let result = try_simplify_with_isle(ctx, &ast);
        if (result.is_none()) {
            break;
        }

        ast = result.unwrap();
    }

    return ctx.arena.insert_ast_node(ast);
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
        SimpleAst::Add { a, b, data }
        | SimpleAst::Mul { a, b, data }
        | SimpleAst::Pow { a, b, data }
        | SimpleAst::And { a, b, data }
        | SimpleAst::Or { a, b, data }
        | SimpleAst::Xor { a, b, data } => vbin(*a, *b),
        SimpleAst::Neg { a, data } | SimpleAst::Zext { a, data } => {
            collect_var_indices_internal(ctx, *a, visited, out_vars)
        }
        SimpleAst::Constant { c, data } => return,
        SimpleAst::Symbol { id, data } => {
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
        if let SimpleAst::Symbol { id, data } = v1 {
            if let SimpleAst::Symbol { id: id2, data } = v2 {
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
pub extern "C" fn ContextZext(ctx: *mut Context, a: AstIdx, width: u8) -> AstIdx {
    unsafe {
        let id = (*ctx).arena.zext(a, width);
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
pub extern "C" fn ContextGetOpcode(ctx: *mut Context, id: AstIdx) -> u8 {
    unsafe {
        let ast = (*ctx).arena.get_node(id);
        let res: u8 = match ast {
            SimpleAst::Add { a, b, data } => 1,
            SimpleAst::Mul { a, b, data } => 2,
            SimpleAst::Pow { a, b, data } => 3,
            SimpleAst::And { a, b, data } => 4,
            SimpleAst::Or { a, b, data } => 5,
            SimpleAst::Xor { a, b, data } => 6,
            SimpleAst::Neg { a, data } => 7,
            SimpleAst::Constant { c, data } => 8,
            SimpleAst::Symbol { id, data } => 9,
            SimpleAst::Zext { a, data } => 10,
        };
        return res;
    }
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
pub extern "C" fn ContextGetOp0(ctx: *mut Context, id: AstIdx) -> AstIdx {
    unsafe {
        let ast = (*ctx).arena.get_node(id);
        return match ast {
            SimpleAst::Add { a, b, data } => *a,
            SimpleAst::Mul { a, b, data } => *a,
            SimpleAst::Pow { a, b, data } => *a,
            SimpleAst::And { a, b, data } => *a,
            SimpleAst::Or { a, b, data } => *a,
            SimpleAst::Xor { a, b, data } => *a,
            SimpleAst::Neg { a, data } => *a,
            SimpleAst::Zext { a, data } => *a,
            _ => unreachable!("Type has no operand!"),
        };
    }
}

#[no_mangle]
pub extern "C" fn ContextGetOp1(ctx: *mut Context, id: AstIdx) -> AstIdx {
    unsafe {
        let ast = (*ctx).arena.get_node(id);
        return match ast {
            SimpleAst::Add { a, b, data } => *b,
            SimpleAst::Mul { a, b, data } => *b,
            SimpleAst::Pow { a, b, data } => *b,
            SimpleAst::And { a, b, data } => *b,
            SimpleAst::Or { a, b, data } => *b,
            SimpleAst::Xor { a, b, data } => *b,
            _ => unreachable!("Type has no operand!"),
        };
    }
}

#[no_mangle]
pub extern "C" fn ContextGetConstantValue(ctx: *mut Context, id: AstIdx) -> u64 {
    unsafe {
        let ast = (*ctx).arena.get_node(id);
        if let SimpleAst::Constant { c: c2, data } = ast {
            return *c2;
        }
    }

    panic!("ast is not a constant!");
}

#[no_mangle]
pub extern "C" fn ContextGetSymbolName(ctx: *mut Context, id: AstIdx) -> *mut c_char {
    unsafe {
        let ast = (*ctx).arena.get_node(id);
        if let SimpleAst::Symbol { id, data } = ast {
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

const PUSH_RAX: u8 = 0x50;
const PUSH_RBX: u8 = 0x53;
const PUSH_RSI: u8 = 0x56;
const PUSH_RDI: u8 = 0x57;

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
        SimpleAst::Constant { c, data } => {
            // mov rax, constant
            emit_u8(page, offset, 0x48);
            emit_u8(page, offset, 0xB8);
            // Fill in the constant
            emit_u64(page, offset, *c);
            // Push rax
            emit_u8(page, offset, PUSH_RAX);
        }
        SimpleAst::Neg { a, data } => {
            jit_rec(ctx, *a, node_to_var, page, offset);
            emit_u8(page, offset, POP_RSI);
            emit(page, offset, &[0x48, 0xF7, 0xD6]);
            emit_u8(page, offset, PUSH_RSI);
        }
        SimpleAst::Add { a, b, data } => binop(*a, *b, &[0x48, 0x01, 0xFE], offset),
        SimpleAst::Mul { a, b, data } => binop(*a, *b, &[0x48, 0x0F, 0xAF, 0xF7], offset),
        SimpleAst::Pow { a, b, data } => binop(*a, *b, &[0x48, 0x01, 0xFE], offset),
        SimpleAst::And { a, b, data } => binop(*a, *b, &[0x48, 0x21, 0xFE], offset),
        SimpleAst::Or { a, b, data } => binop(*a, *b, &[0x48, 0x09, 0xFE], offset),
        SimpleAst::Xor { a, b, data } => binop(*a, *b, &[0x48, 0x31, 0xFE], offset),
        SimpleAst::Symbol { id, data } => {
            let var_idx = node_to_var[&node];

            // varMask = 1 << varIdx
            // mov rsi, 1
            emit(page, offset, &[0x48, 0xC7, 0xC6, 0x01, 0x00, 0x00, 0x00]);

            // shl rsi, varidx
            emit(page, offset, &[0x48, 0xc1, 0xE6, var_idx]);

            // // varValue = i & varMask
            // mov rdi, combIdxRegister
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
        SimpleAst::Zext { a, data } => {
            jit_rec(ctx, *a, node_to_var, page, offset);
            emit_u8(page, offset, POP_RSI);

            // TODO: AND with mask!
            //emit(page, offset, &[0x48, 0xF7, 0xD6]);
            emit_u8(page, offset, PUSH_RSI);
        }
    };
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

        return deref.arena.insert_ast_node(ast);
    }
}

#[no_mangle]
pub extern "C" fn ContextRecursiveSimplify(ctx: *mut Context, id: AstIdx) -> AstIdx {
    unsafe {
        let mut deref: &mut Context = &mut (*ctx);
        return recursive_simplify(deref, id);
    }
}
