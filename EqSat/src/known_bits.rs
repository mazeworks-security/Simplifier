use libc::{c_char, c_void};
use std::{ffi::CStr, ptr};

use crate::simple_ast::Predicate;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, Default)]
#[repr(C)]
pub struct KnownBits {
    pub width: u32,

    pub zeroes: u64,

    pub ones: u64,
}

impl KnownBits {
    pub fn new(width: u8, zeroes: u64, ones: u64) -> Self {
        Self {
            width: width as u32,
            zeroes,
            ones,
        }
    }

    pub fn empty(width: u8) -> Self {
        Self {
            width: width as u32,
            zeroes: 0,
            ones: 0,
        }
    }

    pub fn constant(c: u64, width: u8) -> Self {
        let mask = u64::MAX >> (64 - width);
        Self {
            width: width as u32,
            zeroes: !c & mask,
            ones: c & mask,
        }
    }

    pub fn add(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetAddKnownBits(lhs, rhs, &mut out);
        }
        out
    }

    pub fn sub(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetSubKnownBits(lhs, rhs, &mut out);
        }
        out
    }

    pub fn mul(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetMulKnownBits(lhs, rhs, &mut out);
        }
        out
    }

    pub fn and(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetAndKnownBits(lhs, rhs, &mut out);
        }
        out
    }

    pub fn or(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetOrKnownBits(lhs, rhs, &mut out);
        }
        out
    }

    pub fn xor(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetXorKnownBits(lhs, rhs, &mut out);
        }
        out
    }

    pub fn neg(lhs: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetNegKnownBits(lhs, &mut out);
        }
        out
    }

    pub fn shl(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetShlKnownBits(lhs, rhs, &mut out);
        }
        out
    }

    pub fn lshr(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetLshrKnownBits(lhs, rhs, &mut out);
        }
        out
    }

    pub fn zext(lhs: &KnownBits, width: u32) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetZextKnownBits(lhs, width, &mut out);
        }
        out
    }

    pub fn trunc(lhs: &KnownBits, width: u32) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetTruncKnownBits(lhs, width, &mut out);
        }
        out
    }

    pub fn icmp(pred: Predicate, lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetIcmpKnownBits(pred, lhs, rhs, &mut out);
        }
        out
    }

    pub fn select(a: &KnownBits, b: &KnownBits, c: &KnownBits) -> KnownBits {
        let mut out = KnownBits::default();
        unsafe {
            GetSelectKnownBits(a, b, c, &mut out);
        }
        out
    }

    pub fn get_unknown_bits(&self) -> u64 {
        let unknown_bits = (!(self.zeroes | self.ones)) & Self::get_modulo_mask(self.width as u8);
        return unknown_bits;
    }

    pub fn is_constant(&self) -> bool {
        return self.get_unknown_bits() == 0;
    }

    pub fn as_constant(&self) -> Option<u64> {
        if self.is_constant() {
            return Some(self.ones);
        } else {
            return None;
        }
    }

    pub fn union(&self, other: &KnownBits) -> KnownBits {
        let zeroes = self.zeroes | other.zeroes;
        let ones = self.ones | other.ones;
        KnownBits {
            width: self.width,
            zeroes,
            ones,
        }
    }

    fn get_modulo_mask(width: u8) -> u64 {
        return u64::MAX >> (64 - width);
    }
}

#[link(name = "Mba.FFI", kind = "raw-dylib")]
extern "C" {
    fn GetAddKnownBits(
        lhs: *const KnownBits,
        rhs: *const KnownBits,
        out: *mut KnownBits,
    ) -> *const c_void;

    fn GetSubKnownBits(
        lhs: *const KnownBits,
        rhs: *const KnownBits,
        out: *mut KnownBits,
    ) -> *const c_void;

    fn GetMulKnownBits(
        lhs: *const KnownBits,
        rhs: *const KnownBits,
        out: *mut KnownBits,
    ) -> *const c_void;

    fn GetAndKnownBits(
        lhs: *const KnownBits,
        rhs: *const KnownBits,
        out: *mut KnownBits,
    ) -> *const c_void;

    fn GetOrKnownBits(
        lhs: *const KnownBits,
        rhs: *const KnownBits,
        out: *mut KnownBits,
    ) -> *const c_void;

    fn GetXorKnownBits(
        lhs: *const KnownBits,
        rhs: *const KnownBits,
        out: *mut KnownBits,
    ) -> *const c_void;

    fn GetNegKnownBits(lhs: *const KnownBits, out: *mut KnownBits) -> *const c_void;

    fn GetShlKnownBits(
        lhs: *const KnownBits,
        rhs: *const KnownBits,
        out: *mut KnownBits,
    ) -> *const c_void;

    fn GetLshrKnownBits(
        lhs: *const KnownBits,
        rhs: *const KnownBits,
        out: *mut KnownBits,
    ) -> *const c_void;

    fn GetZextKnownBits(lhs: *const KnownBits, width: u32, out: *mut KnownBits) -> *const c_void;

    fn GetTruncKnownBits(lhs: *const KnownBits, width: u32, out: *mut KnownBits) -> *const c_void;

    fn GetIcmpKnownBits(
        pred: Predicate,
        a: *const KnownBits,
        b: *const KnownBits,
        out: *mut KnownBits,
    ) -> *const c_void;

    fn GetSelectKnownBits(
        a: *const KnownBits,
        b: *const KnownBits,
        c: *const KnownBits,
        out: *mut KnownBits,
    ) -> *const c_void;
}
