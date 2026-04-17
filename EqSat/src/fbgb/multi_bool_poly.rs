use either::Either;

use crate::fbgb::bool_poly::BoolPoly;
use crate::fbgb::transforms::{anf_eliminate_var, anf_filter_by_var, anf_multiply_by_var, anf_negate_many, fast_anf_transform, anf_create_variable_table};
use crate::fbgb::npn::*;
use core::ffi::c_void;
use std::cmp::Ordering;


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct MultiBoolPoly<const N: usize>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    pub bit_width: u8,
    pub value: Box<[BoolPoly<N>]>,
}

impl<const N: usize> MultiBoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    pub fn new(bit_width: u8) -> Self {
        Self {
            value: vec![BoolPoly::new(); bit_width as usize].into_boxed_slice(),
            bit_width,
        }
    }

    pub fn and(&mut self, other: &Self) {
        let count = self.bit_width.min(other.bit_width) as usize;
        for i in 0..count {
            self.value[i] = self.value[i] & other.value[i];
        }
    }

    pub fn or(&mut self, other: &Self) {
        let count = self.bit_width.min(other.bit_width) as usize;
        for i in 0..count {
            self.value[i] = self.value[i] | other.value[i];
        }
    }

     pub fn anf_or(&mut self, other: &Self) {
        let count = self.bit_width.min(other.bit_width) as usize;
        for i in 0..count {
            let or = fast_anf_transform(&self.value[i]) | fast_anf_transform(&other.value[i]);
            self.value[i] = fast_anf_transform(&or);
        }
    }

    pub fn xor(&mut self, other: &Self) {
        let count = self.bit_width.min(other.bit_width) as usize;
        for i in 0..count {
            self.value[i] = self.value[i] + other.value[i];
        }
    }

    pub fn mul(&mut self, other: &Self) {
        let count = self.bit_width.min(other.bit_width) as usize;
        for i in 0..count {
            self.value[i] = self.value[i] * other.value[i];
        }
    }

    pub fn not(&mut self) {
        let last_word = BoolPoly::<N>::WORD_COUNT - 1;
        let last_word_bits = BoolPoly::<N>::BIT_SIZE - last_word * 64;
        let last_mask = if last_word_bits >= 64 {
            !0u64
        } else {
            (1u64 << last_word_bits) - 1
        };

        for i in 0..(self.bit_width as usize) {
            let poly = &mut self.value[i];
            for word in poly.value.iter_mut() {
                *word = !*word;
            }
            poly.value[last_word] &= last_mask;
        }
    }

    pub fn div_rem(&self, other: &Self, div: &mut MultiBoolPoly<N>, rem: &mut MultiBoolPoly<N>)
    {
        let count = self.bit_width.min(other.bit_width) as usize;
        for i in 0..count {
            let (d, r) = self.value[i].div_rem(&other.value[i]);
            div.value[i] = d;
            rem.value[i] = r;
        }
    }

    pub fn get_variable_counts(&self) -> [usize; N] 
    where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
    {
        let seen = self.to_1bit();
        let counts = count_literal_instances(&seen);
        return counts;
    }

    pub fn filter_by_variable(&self, var_index: usize, contains: bool) -> MultiBoolPoly<N>
    where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
     {
        let mut result = MultiBoolPoly::<N>::new(self.bit_width);
        for i in 0..(self.bit_width as usize) {
            result.value[i] = anf_filter_by_var(&self.value[i], var_index, contains);
        }
        result
    }

    pub fn eliminate_variable(&mut self, var_index: usize)
    where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
     {
        for i in 0..(self.bit_width as usize) {
            self.value[i] = anf_eliminate_var(&self.value[i], var_index);
        }
        
    }

    // Multiply every monomial by the selected variables
    pub fn multiply_by_variable(&mut self, var_index: usize)
    where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
    {
        for i in 0..(self.bit_width as usize) {
            self.value[i] = anf_multiply_by_var(&self.value[i], var_index);
        }
    }

    // Compute the set of all monomials across all rows
    pub fn to_1bit(&self) -> BoolPoly<N> {
        let mut result = BoolPoly::<N>::new();
        for i in 0..(self.bit_width as usize) {
            result = result | self.value[i];
        }
        result
    }

    pub fn sift(&mut self) -> (u32, u64)
    {
        // Find a combination of variable negations that minimizes the size of the polynomial
        let mut approx = self.to_1bit();
        approx.set_bit(0, false);
        let canon = fast_anf_negation_canonicalize(approx.clone());

        // Only apply sifting if it's profitable
        let current_literal_count = compute_literal_count(&approx);
        let best_literal_count = compute_literal_count(&canon.table);
        let cmp = anf_compare(&approx, current_literal_count, &canon.table, best_literal_count);
        if cmp != Ordering::Greater {
            return (0, 0);
        }
     
        // Remove constant offset from truth table
        let mut constant_offset : u64 = 0;
        for i in 0..(self.bit_width as usize) {
            self.value[i] = anf_negate_many(&mut self.value[i], canon.negated_vars as u64);
            if self.value[i].has_bit(0) {
                constant_offset |= 1u64 << i;
            }
            self.value[i].set_bit(0, false);
        }

        return (canon.negated_vars as u32, constant_offset);
    }

    #[inline]
    pub fn hash(&self) -> u64 {
        use ahash::RandomState;
        use std::hash::{BuildHasher, Hasher};

        const STATE: RandomState = RandomState::with_seeds(
            0x243f_6a88_85a3_08d3,
            0x1319_8a2e_0370_7344,
            0xa409_3822_299f_31d0,
            0x082e_fa98_ec4e_6c89,
        );

        let rows = &self.value;
        let byte_len = rows.len() * BoolPoly::<N>::WORD_COUNT * 8;
        let bytes = unsafe { std::slice::from_raw_parts(rows.as_ptr() as *const u8, byte_len) };

        let mut h = STATE.build_hasher();
        h.write(bytes);
        h.write_u16(((self.bit_width as u16) << 8) | (N as u16 & 0xFF));
        h.finish()
    }

    pub fn get_constant_offset(&self) -> u64 {
        let mut constant_offset : u64 = 0;
        for i in 0..(self.bit_width as usize) {
            let v = unsafe { self.value.get_unchecked(i).value.get_unchecked(0) };
            constant_offset |= (v & 1) << i;
        }
        return constant_offset;
    }

    pub fn remove_variables<const M: usize>(&self, var_mask: u32) -> MultiBoolPoly<M>
    where
        [(); (1 << M) / 64 + ((1 << M) % 64 != 0) as usize]: Sized,
        [(); (1 << M) as usize]: Sized,
    {
        let mut reduced: Box<[BoolPoly<N>]> = self.value.clone();
        let mut m = var_mask;
        while m != 0 {
            let v = m.trailing_zeros() as usize;
            for row in reduced.iter_mut() {
                *row = anf_eliminate_var(row, v);
            }
            m &= m - 1;
        }

        let mut kept: [u8; 32] = [0; 32];
        let mut kept_count = 0usize;
        for i in 0..N {
            if (var_mask >> i) & 1 == 0 {
                kept[kept_count] = i as u8;
                kept_count += 1;
            }
        }

        let mut out = MultiBoolPoly::<M>::new(self.bit_width);
        let bit_size_m: usize = 1usize << M;
        let bw = self.bit_width as usize;
        
        for j in 0..bit_size_m {
            let mut i: usize = 0;
            for k in 0..M {
                if (j >> k) & 1 == 1 {
                    i |= 1usize << (kept[k] as usize);
                }
            }
            
            for row_idx in 0..bw {
                if reduced[row_idx].has_bit(i) {
                    out.value[row_idx].set_bit(j, true);
                }
            }
        }

        out
    }

    // Try to rewrite the boolean as c1 + c2*(1_bit_table)
    pub fn try_downgrade_to_1bit(&self) -> Option<(BoolPoly<N>, u64, u64)> {
        let constant_offset = self.get_constant_offset();

        let mut table = BoolPoly::<N>::new();
        for i in 0..(self.bit_width as usize) {
            table = table | self.value[i];
        }
        table.set_bit(0, false);

        let mut coefficient: u64 = 0;
        for i in 0..(self.bit_width as usize) {
            let mut row = self.value[i].clone();
            row.set_bit(0, false);

            if row.is_zero() {
                continue;
            }
            if row != table {
                return None;
            }
            coefficient |= 1u64 << i;
        }

        Some((table, constant_offset, coefficient))
    }
}

macro_rules! dispatch_n {
    ($n:expr, |$N:ident| $body:block) => {{
        macro_rules! __arm {
            ($value:literal) => {{
                const $N: usize = $value;
                $body
            }};
        }
        match $n {
            1  => __arm!(1),
            2  => __arm!(2),
            3  => __arm!(3),
            4  => __arm!(4),
            5  => __arm!(5),
            6  => __arm!(6),
            7  => __arm!(7),
            8  => __arm!(8),
            9  => __arm!(9),
            10 => __arm!(10),
            11 => __arm!(11),
            12 => __arm!(12),
            13 => __arm!(13),
            14 => __arm!(14),
            15 => __arm!(15),
            16 => __arm!(16),
            other => panic!(
                "Got truth table with {} variables, expected integer between 1 and 16",
                other
            ),
        }
    }};
}

#[inline]
unsafe fn as_mut<'a, const N: usize>(ptr: *mut c_void) -> &'a mut MultiBoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    &mut *(ptr as *mut MultiBoolPoly<N>)
}

#[inline]
unsafe fn as_ref<'a, const N: usize>(ptr: *const c_void) -> &'a MultiBoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    &*(ptr as *const MultiBoolPoly<N>)
}

#[no_mangle]
pub unsafe extern "C" fn CreateBoolPoly(num_vars: u8, bit_width: u8) -> *mut c_void {
    dispatch_n!(num_vars, |N| {
        Box::into_raw(Box::new(MultiBoolPoly::<N>::new(bit_width))) as *mut c_void
    })
}

#[no_mangle]
pub unsafe extern "C" fn CreateBoolPolyFromVec(num_vars: u8, bit_width: u8, vec_ptr: *const u64) -> *mut c_void {
    dispatch_n!(num_vars, |N| {
        let mut mpb = MultiBoolPoly::<N>::new(bit_width);
        for i in 0..(bit_width as usize) {
            let mut bp = BoolPoly::<N>::new();
            for j in 0..BoolPoly::<N>::WORD_COUNT {
                bp.value[j] = *vec_ptr.add(i * BoolPoly::<N>::WORD_COUNT + j);
            }
            mpb.value[i] = bp;

        }
        Box::into_raw(Box::new(mpb)) as *mut c_void
    })
}

#[no_mangle]
pub unsafe extern "C" fn CreateBoolPolyFromVariable(num_vars: u8, bit_width: u8, var_index: u32) -> *mut c_void {
    dispatch_n!(num_vars, |N| {
        let mut mpb = MultiBoolPoly::<N>::new(bit_width);
        for i in 0..(bit_width as usize) {
            mpb.value[i] = anf_create_variable_table(var_index as usize);

        }
        Box::into_raw(Box::new(mpb)) as *mut c_void
    })
}

#[no_mangle]
pub unsafe extern "C" fn FreeBoolPoly(n: u8, ptr: *mut c_void) {
    dispatch_n!(n, |N| {
        drop(Box::from_raw(ptr as *mut MultiBoolPoly<N>));
    })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyAnd(n: u8, lhs: *mut c_void, rhs: *const c_void) {
    dispatch_n!(n, |N| { as_mut::<N>(lhs).and(as_ref::<N>(rhs)); })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyOr(n: u8, lhs: *mut c_void, rhs: *const c_void) {
    dispatch_n!(n, |N| { as_mut::<N>(lhs).or(as_ref::<N>(rhs)); })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyXor(n: u8, lhs: *mut c_void, rhs: *const c_void) {
    dispatch_n!(n, |N| { as_mut::<N>(lhs).xor(as_ref::<N>(rhs)); })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyMul(n: u8, lhs: *mut c_void, rhs: *const c_void) {
    dispatch_n!(n, |N| { as_mut::<N>(lhs).mul(as_ref::<N>(rhs)); })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyNot(n: u8, target: *mut c_void) {
    dispatch_n!(n, |N| { as_mut::<N>(target).not(); })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyGetConstantOffset(n: u8, ptr: *mut c_void) -> u64 {
    dispatch_n!(n, |N| {
        as_ref::<N>(ptr).get_constant_offset()
    })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyGetRow(n: u8, ptr: *mut c_void, index: u32) -> *mut u64 {
    dispatch_n!(n, |N| {
        as_mut::<N>(ptr).value[index as usize].value.as_mut_ptr()
    })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyChangeBasis(n: u8, target: *mut c_void) {
    dispatch_n!(n, |N| {
        for i in 0..(as_mut::<N>(target).bit_width as usize) {
            as_mut::<N>(target).value[i] = fast_anf_transform(&as_mut::<N>(target).value[i]);
        }

     })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyGetVariableCounts(n: u8, ptr: *mut c_void, arr: *mut u32) {
    dispatch_n!(n, |N| {
        let counts = as_ref::<N>(ptr).get_variable_counts();
        for i in 0..N {
            *arr.add(i) = counts[i] as u32;
        }
    })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyFilterByVar(n: u8, ptr: *mut c_void, var_index: u32, contains: u8) -> *mut c_void  {
    dispatch_n!(n, |N| {
        let r = as_ref::<N>(ptr).filter_by_variable(var_index as usize, contains != 0);
        Box::into_raw(Box::new(r)) as *mut c_void
    })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyEliminateVar(n: u8, ptr: *mut c_void, var_index: u32) -> *mut c_void  {
    dispatch_n!(n, |N| {
        let r = as_mut::<N>(ptr).eliminate_variable(var_index as usize);
        Box::into_raw(Box::new(r)) as *mut c_void
    })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyMultiplyByVar(n: u8, ptr: *mut c_void, var_index: u32) {
    dispatch_n!(n, |N| {
        as_mut::<N>(ptr).multiply_by_variable(var_index as usize);
    })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyRemoveVars(
    num_vars_in: u8,
    ptr: *const c_void,
    var_mask: u32,
) -> *mut c_void {
    dispatch_n!(num_vars_in, |N_IN| {
        let num_vars_out = num_vars_in - var_mask.count_ones() as u8;
        dispatch_n!(num_vars_out, |N_OUT| {
            let reduced = as_ref::<N_IN>(ptr).remove_variables::<N_OUT>(var_mask);
            Box::into_raw(Box::new(reduced)) as *mut c_void
        })
    })
}
// Attempt to change an N-bit boolean polynomial to a 1-bit polynomial by expressing it as c1 + c2*(a + b + ab + ...),
#[no_mangle]
pub unsafe extern "C" fn BoolPolyTryReduceTo1Bit(
    num_vars: u8,
    ptr: *const c_void,
    out_table: *mut *mut c_void,
    out_constant_offset: *mut u64,
    out_coefficient: *mut u64,
) -> u8 {
    dispatch_n!(num_vars, |N| {
        match as_ref::<N>(ptr).try_downgrade_to_1bit() {
            Some((table, constant_offset, coefficient)) => {
                let mut wrapped = MultiBoolPoly::<N>::new(1);
                wrapped.value[0] = table;

                *out_table = Box::into_raw(Box::new(wrapped)) as *mut c_void;
                *out_constant_offset = constant_offset;
                *out_coefficient = coefficient;
                1u8
            }
            None => 0u8,
        }
    })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolySift(n: u8, target: *mut c_void, negated_mask: *mut u32, negated_constant: *mut u64) {
    dispatch_n!(n, |N| {
         let (mask, constant) = as_mut::<N>(target).sift(); 
         *negated_mask = mask;
         *negated_constant = constant;
        })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyClone(n: u8, ptr: *const c_void) -> *mut c_void {
    dispatch_n!(n, |N| {
        let original = as_ref::<N>(ptr);
        let cloned = Box::new(original.clone());
        Box::into_raw(cloned) as *mut c_void
    })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyEquals(n: u8, lhs: *const c_void, rhs: *const c_void) -> u8 {
    dispatch_n!(n, |N| {
        if as_ref::<N>(lhs) == as_ref::<N>(rhs) {
            1
        } else {
            0
        }
    })
}

// Checks whether `(a^b) == (b|c)` == 0 without heap allocating a new polynomial for the result.
#[no_mangle]
pub unsafe extern "C" fn BoolPolyIsOr(n: u8, a: *const c_void, b: *const c_void, c: *const c_void) -> u8 {
    dispatch_n!(n, |N| {

        let mut ground_truth = as_ref::<N>(a).clone();
        ground_truth.xor(as_ref::<N>(b)); 

        let mut combined = as_ref::<N>(b).clone();
        combined.anf_or(as_ref::<N>(c)); 

        if ground_truth == combined {
            1
        } else {
            0
        }
    })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyGetHash(n: u8, ptr: *const c_void) -> u64 {
    dispatch_n!(n, |N| { as_ref::<N>(ptr).hash() })
}

#[no_mangle]
pub unsafe extern "C" fn BoolPolyDivRem(n: u8, a: *const c_void, b: *const c_void, div: *mut c_void, rem: *mut c_void) {
    dispatch_n!(n, |N| {
        let a_ref = as_ref::<N>(a);
        let b_ref = as_ref::<N>(b);

        let div_ref = as_mut::<N>(div);
        let rem_ref = as_mut::<N>(rem);

        a_ref.div_rem(b_ref, div_ref, rem_ref);
    })
}
