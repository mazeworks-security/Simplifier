use std::{
    collections::{hash_map::Entry, HashMap, HashSet},
    f32::consts::PI,
    ffi::{CStr, CString},
    u64,
};

use ahash::AHashMap;
use libc::{c_char, c_void};

use crate::{
    mba::{self, Context as MbaContext},
    truth_table_database::{TruthTable, TruthTableDatabase},
};

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
#[repr(C)]
pub struct AstIdx(pub u32);

pub struct Arena {
    pub elements: Vec<SimpleAst>,
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
        let c2 = self.get_data(b).cost;
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
                self.output.push_str(&format!("{}", operator));
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
pub extern "C" fn ContextGetOpcode(ctx: *const Context, id: AstIdx) -> u8 {
    unsafe {
        return get_opcode(&(*ctx), id);
    }
}

pub fn get_opcode(ctx: &Context, id: AstIdx) -> u8 {
    let ast = ctx.arena.get_node(id);
    return match ast {
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
pub extern "C" fn ContextGetOp0(ctx: *const Context, id: AstIdx) -> AstIdx {
    unsafe {
        return get_op0(&(*ctx), id);
    }
}

pub fn get_op0(ctx: &Context, id: AstIdx) -> AstIdx {
    let ast = ctx.arena.get_node(id);
    return match ast {
        SimpleAst::Add { a, b, data } => *a,
        SimpleAst::Mul { a, b, data } => *a,
        SimpleAst::Pow { a, b, data } => *a,
        SimpleAst::And { a, b, data } => *a,
        SimpleAst::Or { a, b, data } => *a,
        SimpleAst::Xor { a, b, data } => *a,
        SimpleAst::Neg { a, data } => *a,
        SimpleAst::Zext { a, data } => *a,
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
        SimpleAst::Add { a, b, data } => *b,
        SimpleAst::Mul { a, b, data } => *b,
        SimpleAst::Pow { a, b, data } => *b,
        SimpleAst::And { a, b, data } => *b,
        SimpleAst::Or { a, b, data } => *b,
        SimpleAst::Xor { a, b, data } => *b,
        _ => unreachable!("Type has no second operand!"),
    };
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
            let isSet = (result_vec_idx & vmask) != 0;
            let var = *vars.wrapping_add(var_idx as usize);
            let term = if isSet { var } else { deref.arena.neg(var) };
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
        SimpleAst::Symbol { id, data } => {
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
        SimpleAst::Neg { a, data } => {
            get_demanded_vars_mask(ctx, *a, variables, variable_count, demanded_vars_map)
        }
        SimpleAst::And { a, b, data }
        | SimpleAst::Xor { a, b, data }
        | SimpleAst::And { a, b, data } => {
            let a_mask =
                get_demanded_vars_mask(ctx, *a, variables, variable_count, demanded_vars_map);
            let b_mask =
                get_demanded_vars_mask(ctx, *b, variables, variable_count, demanded_vars_map);
            a_mask | b_mask
        }
        SimpleAst::Constant { c, data } => 0,

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
    if let SimpleAst::Symbol { id, data } = ast {
        return idx;
    }
    if let SimpleAst::Constant { c, data } = ast {
        return idx;
    }
    if let SimpleAst::Neg { a, data } = ast {
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
                    SimpleAst::And { a, b, data } => ctx.arena.and(old_id, *term),
                    SimpleAst::Or { a, b, data } => ctx.arena.or(old_id, *term),
                    SimpleAst::Xor { a, b, data } => ctx.arena.xor(old_id, *term),
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
                SimpleAst::And { a, b, data } => Some(ctx.arena.and(simplified.unwrap(), reduced)),
                SimpleAst::Or { a, b, data } => Some(ctx.arena.or(simplified.unwrap(), reduced)),
                SimpleAst::Xor { a, b, data } => Some(ctx.arena.xor(simplified.unwrap(), reduced)),
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
