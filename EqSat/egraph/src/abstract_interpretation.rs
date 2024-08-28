use libc::{c_char, c_void};
use std::{ffi::CStr, ptr};

use crate::ffi_utils::marshal_string;

#[derive(Copy, Clone)]
pub enum KnownBitsTransferOpcode {
    Add = 0,
    Mul = 1,
    // Note that POW is not supported.
    // If a POW can be represented as a shift left then the shl transfer function should be used.
    // Otherwise you'll need to implement POWs as repeated multiplications.
    Shl = 2,
    And = 3,
    Or = 4,
    Xor = 5,
    Neg = 6,
}

#[derive(Debug, Clone, Copy)]
pub struct KnownBitsWrapper {
    ptr: *const c_void,
}

// Note: For now the KnownBits FFI interface has been replaced with a dummy implementation.
// We rely on LLVM's KnownBits implementation, but do not want to require that users have LLVM installed.
// TODO: Use a macro to conditionally enable the FFI imports for known bits.

/*
// FFI imports.
#[link(name = "LLVMInterop", kind = "raw-dylib")]
extern "C" {
    // Given an integer bit width, create a knownbits object of that bitwidth, with all bits initialized to unknown.
    fn ffi_CreateKnownBits(bitWidth: u32) -> *const c_void;
    // Create a knownbits object for the given constant. Note that only up to 64 bits is supported now.
    pub fn ffi_CreateKnownBitsForConstant(bitWidth: u32, value: u64) -> *const c_void;
    // Compute a new knownbits object given an opcode and a sedt of operands.
    // Note that the opcode is just the 'KnownBitsTransferOpcode` casted to an integer.
    pub fn ffi_ComputeKnownBits(
        opcode: u8,
        lhs: *const c_void,
        rhs: *const c_void,
    ) -> *const c_void;
    pub fn ffi_UnionKnownBits(
        lhs: *const c_void,
        rhs: *const c_void,
        out: *const *mut c_void,
    ) -> bool;
    pub fn ffi_TryConstant(kb: *const c_void, out: *mut u64) -> bool;
    pub fn ffi_KnownBitsToStr(kb: *const c_void) -> *const c_char;
    pub fn ffi_NumKnownBits(kb: *const c_void) -> u64;
    pub fn ffi_AreKnownBitsEqual(lhs: *const c_void, rhs: *const c_void) -> bool;
    pub fn ffi_HaveNoCommonBitsSet(lhs: *const c_void, rhs: *const c_void) -> bool;
    pub fn ffi_IsSubset(lhs: *const c_void, rhs: *const c_void) -> bool;
}
*/

// Given an integer bit width, create a knownbits object of that bitwidth, with all bits initialized to unknown.
fn ffi_CreateKnownBits(bitWidth: u32) -> *const c_void {
    panic!("")
}
// Create a knownbits object for the given constant. Note that only up to 64 bits is supported now.
pub fn ffi_CreateKnownBitsForConstant(bitWidth: u32, value: u64) -> *const c_void {
    panic!("")
}
// Compute a new knownbits object given an opcode and a sedt of operands.
// Note that the opcode is just the 'KnownBitsTransferOpcode` casted to an integer.
pub fn ffi_ComputeKnownBits(opcode: u8, lhs: *const c_void, rhs: *const c_void) -> *const c_void {
    panic!("")
}
pub fn ffi_UnionKnownBits(lhs: *const c_void, rhs: *const c_void, out: *const *mut c_void) -> bool {
    panic!("")
}

pub fn ffi_TryConstant(kb: *const c_void, out: *mut u64) -> bool {
    panic!("")
}
pub fn ffi_KnownBitsToStr(kb: *const c_void) -> *const c_char {
    panic!("")
}
pub fn ffi_NumKnownBits(kb: *const c_void) -> u64 {
    panic!("")
}
pub fn ffi_AreKnownBitsEqual(lhs: *const c_void, rhs: *const c_void) -> bool {
    panic!("")
}
pub fn ffi_HaveNoCommonBitsSet(lhs: *const c_void, rhs: *const c_void) -> bool {
    panic!("")
}
pub fn ffi_IsSubset(lhs: *const c_void, rhs: *const c_void) -> bool {
    panic!("")
}

const DISABLE_KNOWN_BITS: bool = true;

impl KnownBitsWrapper {
    pub fn no_common_bits_set(&self, rhs: KnownBitsWrapper) -> bool {
        if DISABLE_KNOWN_BITS {
            return false;
        }

        unsafe { ffi_HaveNoCommonBitsSet(self.ptr, rhs.ptr) }
    }

    pub fn is_subset_of_this(&self, rhs: KnownBitsWrapper) -> bool {
        if DISABLE_KNOWN_BITS {
            return false;
        }
        unsafe { ffi_IsSubset(self.ptr, rhs.ptr) }
    }

    pub fn num_known_bits(&self) -> u64 {
        if DISABLE_KNOWN_BITS {
            return 0;
        }

        unsafe { ffi_NumKnownBits(self.ptr) }
    }

    pub fn to_str(&self) -> String {
        if DISABLE_KNOWN_BITS {
            return "Disabled".to_string();
        }

        unsafe { marshal_string(ffi_KnownBitsToStr(self.ptr)) }
    }

    pub fn try_as_const(&self) -> Option<u64> {
        if DISABLE_KNOWN_BITS {
            return None;
        }

        let mut out: u64 = 0;
        unsafe {
            if ffi_TryConstant(self.ptr, &mut out) {
                Some(out)
            } else {
                None
            }
        }
    }
}

pub fn are_known_bits_equal(kb1: KnownBitsWrapper, kb2: KnownBitsWrapper) -> bool {
    if DISABLE_KNOWN_BITS {
        return true;
    }

    unsafe { ffi_AreKnownBitsEqual(kb1.ptr, kb2.ptr) }
}

// Wrapper methods around FFI imports.
pub fn create_empty_known_bits(width: u32) -> KnownBitsWrapper {
    if DISABLE_KNOWN_BITS {
        return KnownBitsWrapper {
            ptr: std::ptr::null(),
        };
    }

    unsafe {
        let ptr = ffi_CreateKnownBits(width);
        return KnownBitsWrapper { ptr };
    };
}

pub fn create_constant_known_bits(width: u32, value: u64) -> KnownBitsWrapper {
    if DISABLE_KNOWN_BITS {
        return create_empty_known_bits(width);
    }

    unsafe {
        let ptr = ffi_CreateKnownBitsForConstant(width, value);
        return KnownBitsWrapper { ptr };
    };
}

pub fn compute_known_bits(
    opcode: KnownBitsTransferOpcode,
    lhs: KnownBitsWrapper,
    maybe_rhs: Option<KnownBitsWrapper>,
) -> KnownBitsWrapper {
    if DISABLE_KNOWN_BITS {
        return KnownBitsWrapper {
            ptr: std::ptr::null(),
        };
    }

    unsafe {
        // return CreateEmptyKnownBits(64);
        // If the operand is negation then there is no RHS.
        // In that case we set the RHS to `new KnownBitsWrapper(nullptr)`.
        let nullptr: *const c_void = ptr::null();
        let none = KnownBitsWrapper { ptr: nullptr };
        let rhs = maybe_rhs.unwrap_or(none);

        // Execute and return the result from the known bits transfer function wrapper.
        let ptr = ffi_ComputeKnownBits(opcode as u8, lhs.ptr, rhs.ptr);
        return KnownBitsWrapper { ptr };
    };
}

pub fn union_known_bits(lhs: KnownBitsWrapper, rhs: KnownBitsWrapper) -> Option<KnownBitsWrapper> {
    if DISABLE_KNOWN_BITS {
        return None;
    }

    unsafe {
        let mut new_ptr: *mut c_void = std::ptr::null_mut();
        let res = ffi_UnionKnownBits(lhs.ptr, rhs.ptr, &new_ptr);

        if res {
            Some(KnownBitsWrapper { ptr: new_ptr })
        } else {
            None
        }
    }
}
