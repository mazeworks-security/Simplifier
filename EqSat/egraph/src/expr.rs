use std::ffi::{CStr, CString};

use crate::{
    analysis::{self, MbaAnalysis},
    ffi_utils::marshal_string,
};
use analysis::EEGraph;
use egg::*;
use libc::c_char;

define_language! {
    pub enum Expr {
        // arithmetic operations
        "+" = Add([Id; 2]),        // (+ a b)
        "*" = Mul([Id; 2]),        // (* a b)
        "**" = Pow([Id; 2]),       // (** a b)
        // bitwise operations
        "&" = And([Id; 2]),        // (& a b)
        "|" = Or([Id; 2]),         // (| a b)
        "^" = Xor([Id; 2]),        // (^ a b)
        "~" = Neg([Id; 1]),        // (~ a)

        ">>>" = Ashr([Id; 2]),
        ">>" = Lshr([Id; 2]),
        "<<" = Shl([Id; 2]),

        // Values:
        Constant(i128),             // (int)
        Symbol(Symbol),             // (x)
    }
}

impl Expr {
    pub fn num(&self) -> Option<i128> {
        match self {
            Expr::Constant(n) => Some(*n),
            _ => None,
        }
    }
}

// Below is an FFI interface for egraphs and Expr instances.
#[no_mangle]
pub extern "C" fn CreateEGraph() -> *mut EEGraph {
    let analysis = MbaAnalysis {};
    let egraph = EEGraph::new(analysis);
    let pgraph = Box::new(egraph);
    return Box::into_raw(pgraph);
}

#[no_mangle]
pub extern "C" fn EGraphAddConstant(egraph: *mut EEGraph, constant: u64) -> u32 {
    // We don't want to apply sign extension when upcasting from 64 bits to 128 bits.
    // Instead, we want to zero extend to an i128, *then* cast the unsigned integer to a signed integer.
    let extended = (constant as u128) as i128;

    unsafe {
        let id = (*egraph).add(Expr::Constant(extended));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddSymbol(egraph: *mut EEGraph, s: *const c_char) -> u32 {
    let str = marshal_string(s).to_owned();

    unsafe {
        let id = (*egraph).add(Expr::Symbol(str.parse().unwrap()));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddAdd(egraph: *mut EEGraph, a: u32, b: u32) -> u32 {
    unsafe {
        let op1 = Id::from(a as usize);
        let op2 = Id::from(b as usize);
        let id = (*egraph).add(Expr::Add([op1, op2]));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddMul(egraph: *mut EEGraph, a: u32, b: u32) -> u32 {
    unsafe {
        let op1 = Id::from(a as usize);
        let op2 = Id::from(b as usize);
        let id = (*egraph).add(Expr::Mul([op1, op2]));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddPow(egraph: *mut EEGraph, a: u32, b: u32) -> u32 {
    unsafe {
        let op1 = Id::from(a as usize);
        let op2 = Id::from(b as usize);
        let id = (*egraph).add(Expr::Pow([op1, op2]));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddAnd(egraph: *mut EEGraph, a: u32, b: u32) -> u32 {
    unsafe {
        let op1 = Id::from(a as usize);
        let op2 = Id::from(b as usize);
        let id = (*egraph).add(Expr::And([op1, op2]));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddOr(egraph: *mut EEGraph, a: u32, b: u32) -> u32 {
    unsafe {
        let op1 = Id::from(a as usize);
        let op2 = Id::from(b as usize);
        let id = (*egraph).add(Expr::Or([op1, op2]));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddXor(egraph: *mut EEGraph, a: u32, b: u32) -> u32 {
    unsafe {
        let op1 = Id::from(a as usize);
        let op2 = Id::from(b as usize);
        let id = (*egraph).add(Expr::Xor([op1, op2]));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddNeg(egraph: *mut EEGraph, a: u32) -> u32 {
    unsafe {
        let op1 = Id::from(a as usize);
        let id = (*egraph).add(Expr::Neg([op1]));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddAshr(egraph: *mut EEGraph, a: u32, b: u32) -> u32 {
    unsafe {
        let op1 = Id::from(a as usize);
        let op2 = Id::from(b as usize);
        let id = (*egraph).add(Expr::Ashr([op1, op2]));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddLshr(egraph: *mut EEGraph, a: u32, b: u32) -> u32 {
    unsafe {
        let op1 = Id::from(a as usize);
        let op2 = Id::from(b as usize);
        let id = (*egraph).add(Expr::Lshr([op1, op2]));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn EGraphAddShl(egraph: *mut EEGraph, a: u32, b: u32) -> u32 {
    unsafe {
        let op1 = Id::from(a as usize);
        let op2 = Id::from(b as usize);
        let id = (*egraph).add(Expr::Shl([op1, op2]));
        return get_id_u32(id);
    }
}

#[no_mangle]
pub extern "C" fn RecExprGetChildCount(expr: *const RecExpr<Expr>) -> usize {
    unsafe {
        return (*expr).as_ref().len();
    }
}

#[no_mangle]
pub extern "C" fn RecExprGetChild(expr: *const RecExpr<Expr>, index: usize) -> *const Expr {
    let expr2 = unsafe { &*expr };

    let child = &(expr2.as_ref()[index]);

    return Box::into_raw(Box::new((*child).clone()));
}

#[no_mangle]
pub extern "C" fn RecExprGetIsDag(expr: *const RecExpr<Expr>) -> bool {
    let expr2 = &unsafe { &*expr };

    return expr2.is_dag();
}

#[no_mangle]
pub extern "C" fn ExprGetChildrenCount(expr: *const Expr) -> usize {
    let expr2 = &unsafe { &*expr };

    return expr2.children().len();
}

#[no_mangle]
// The behavior is really strange here, see the rust implementation of "to_sexp_rec".
// The index returned here is actually an index into the parent RecExpr's node list.
pub extern "C" fn ExprGetChildIndex(expr: *const Expr, index: usize) -> usize {
    let expr2 = &unsafe { &*expr };

    return usize::from(expr2.children()[index]);
}

#[no_mangle]
pub extern "C" fn ExprIsAdd(expr: *const Expr) -> bool {
    let expr2 = unsafe { &*expr };

    return match expr2 {
        Expr::Add(_) => true,
        _ => false,
    };
}

#[no_mangle]
pub extern "C" fn ExprIsMul(expr: *const Expr) -> bool {
    let expr2 = unsafe { &*expr };

    return match *expr2 {
        Expr::Mul(_) => true,
        _ => false,
    };
}

#[no_mangle]
pub extern "C" fn ExprIsPow(expr: *const Expr) -> bool {
    let expr2 = unsafe { &*expr };

    return match *expr2 {
        Expr::Pow(_) => true,
        _ => false,
    };
}

#[no_mangle]
pub extern "C" fn ExprIsAnd(expr: *const Expr) -> bool {
    let expr2 = unsafe { &*expr };

    return match expr2 {
        Expr::And(_) => true,
        _ => false,
    };
}

#[no_mangle]
pub extern "C" fn ExprIsOr(expr: *const Expr) -> bool {
    unsafe {
        return matches!(*expr, Expr::Or(_));
    };
}

#[no_mangle]
pub extern "C" fn ExprIsXor(expr: *const Expr) -> bool {
    let expr2 = &unsafe { &*expr };

    match expr2 {
        Expr::Xor(_) => true,
        _ => false,
    }
}

#[no_mangle]
pub extern "C" fn ExprIsNeg(expr: *const Expr) -> bool {
    let expr2 = unsafe { (*(expr)).clone() };

    let is_bool: bool = match expr2 {
        Expr::Neg(_) => true,
        _ => false,
    };

    return is_bool;
}

#[no_mangle]
pub extern "C" fn ExprIsAshr(expr: *const Expr) -> bool {
    let expr2 = &unsafe { &*expr };

    return match expr2 {
        Expr::Ashr(_) => true,
        _ => false,
    };
}

#[no_mangle]
pub extern "C" fn ExprIsLshr(expr: *const Expr) -> bool {
    let expr2 = &unsafe { &*expr };

    return match expr2 {
        Expr::Lshr(_) => true,
        _ => false,
    };
}

#[no_mangle]
pub extern "C" fn ExprIsShl(expr: *const Expr) -> bool {
    let expr2 = &unsafe { &*expr };

    return match expr2 {
        Expr::Shl(_) => true,
        _ => false,
    };
}

#[no_mangle]
pub extern "C" fn ExprIsConstant(expr: *const Expr) -> bool {
    let expr2 = &unsafe { &*expr };

    return match expr2 {
        Expr::Constant(_) => true,
        _ => false,
    };
}

#[no_mangle]
pub extern "C" fn ExprGetConstantValue(expr: *const Expr) -> u64 {
    let expr2 = &unsafe { &*expr };

    return match expr2 {
        Expr::Constant(value) => (*value) as u128 as u64,
        _ => panic!("Not a constant!"),
    };
}

#[no_mangle]
pub extern "C" fn ExprIsSymbol(expr: *const Expr) -> bool {
    let expr2 = &unsafe { &*expr };

    return match expr2 {
        Expr::Symbol(_) => true,
        _ => false,
    };
}

#[no_mangle]
pub extern "C" fn ExprGetSymbolName(expr: *const Expr) -> *mut c_char {
    let expr2 = &unsafe { &*expr };

    return match expr2 {
        Expr::Symbol(value) => CString::new(value.to_string()).unwrap().into_raw(),
        _ => panic!("Not a symbol!"),
    };
}

// Cast an egg 'Id' instance to a u32.
pub fn get_id_u32(id: Id) -> u32 {
    let id: usize = id.into();

    return id as u32;
}
