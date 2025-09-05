use libc::{c_char, c_void};
use std::{ffi::CStr, ptr};

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, Default)]
#[repr(C)]
pub struct KnownBits {
    width: u8,

    zeroes: u64,

    ones: u64,
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
}

pub fn get_add_known_bits(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetAddKnownBits(lhs, rhs, &mut out);
    }
    out
}

pub fn get_sub_known_bits(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetSubKnownBits(lhs, rhs, &mut out);
    }
    out
}

pub fn get_mul_known_bits(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetMulKnownBits(lhs, rhs, &mut out);
    }
    out
}

pub fn get_and_known_bits(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetAndKnownBits(lhs, rhs, &mut out);
    }
    out
}

pub fn get_or_known_bits(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetOrKnownBits(lhs, rhs, &mut out);
    }
    out
}

pub fn get_xor_known_bits(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetXorKnownBits(lhs, rhs, &mut out);
    }
    out
}

pub fn get_neg_known_bits(lhs: &KnownBits) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetNegKnownBits(lhs, &mut out);
    }
    out
}

pub fn get_shl_known_bits(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetShlKnownBits(lhs, rhs, &mut out);
    }
    out
}

pub fn get_lshr_known_bits(lhs: &KnownBits, rhs: &KnownBits) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetLshrKnownBits(lhs, rhs, &mut out);
    }
    out
}

pub fn get_zext_known_bits(lhs: &KnownBits, width: u32) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetZextKnownBits(lhs, width, &mut out);
    }
    out
}

pub fn get_trunc_known_bits(lhs: &KnownBits, width: u32) -> KnownBits {
    let mut out = KnownBits::default();
    unsafe {
        GetTruncKnownBits(lhs, width, &mut out);
    }
    out
}
