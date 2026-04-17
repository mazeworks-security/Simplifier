use crate::fbgb::bool_poly::{BoolPoly, Monomial};

pub(crate) const VAR_MASKS: [u64; 6] = [
    0xAAAAAAAAAAAAAAAA,
    0xCCCCCCCCCCCCCCCC,
    0xF0F0F0F0F0F0F0F0,
    0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000,
    0xFFFFFFFF00000000,
];

// Fast algebraic normal form transformation. Implementation based on:
// "Fast Bitwise Implementation of the Algebraic Normal Form Transform", Bakoev, Valentin
//
// `f` is a classic boolean truth table.
// Yields the algebraic normal form of 'f'.
//
// The implementation of this algorithm differs slightly from the paper.
// `BoolPoly` expects the smallest monomial to be stored in the least significant bit,
// while the paper expects the largest monomial to be stored in the least significant bit.
pub fn fast_anf_transform<const N: usize>(truth_table: &BoolPoly<N>) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut output = truth_table.clone();
    let f = &mut output.value;

    for k in 0..f.len() {
        let mut temp = f[k];
        if N >= 1 {
            temp ^= (temp << 1) & VAR_MASKS[0];
        }
        if N >= 2 {
            temp ^= (temp << 2) & VAR_MASKS[1];
        }
        if N >= 3 {
            temp ^= (temp << 4) & VAR_MASKS[2];
        }
        if N >= 4 {
            temp ^= (temp << 8) & VAR_MASKS[3];
        }
        if N >= 5 {
            temp ^= (temp << 16) & VAR_MASKS[4];
        }
        if N >= 6 {
            temp ^= temp << 32;
        }
        f[k] = temp;
    }

    if N < 6 {
        f[0] &= (1u64 << (1 << N)) - 1;
    }

    let mut blocksize = 1;
    let num_of_steps = (N as i32) - 6;
    for _ in 1..=num_of_steps {
        let mut source = 0;
        while source < f.len() - 1 {
            let target = source + blocksize;
            for i in 0..blocksize {
                f[target + i] ^= f[source + i];
            }
            source += 2 * blocksize;
        }
        blocksize *= 2;
    }

    if N < 6 {
        f[0] &= (1u64 << (1 << N)) - 1;
    }

    output
}

// Inverse of 'fast_anf_transform``
pub fn fast_dnf_transform<const N: usize>(truth_table: &BoolPoly<N>) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    // The inverse of the fast_anf_transform function is itself
    return fast_anf_transform(truth_table);
}

pub fn anf_negate_many<const N: usize>(truth_table: &BoolPoly<N>, var_indices: u64) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut output = truth_table.clone();
    for var_index in 0..N {
        if (var_indices & (1 << var_index)) != 0 {
            output = anf_negate_variable(&output, var_index);
        }
    }
    output
}

// Negate the ith variable of a boolean in algebraic normal form
pub fn anf_negate_variable<const N: usize>(
    truth_table: &BoolPoly<N>,
    var_index: usize,
) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut output = truth_table.clone();

    if var_index >= N {
        return output;
    }

    let f = &mut output.value;

    if var_index < 6 {
        let shift = 1 << var_index;
        let mask = !VAR_MASKS[var_index];
        for word in f.iter_mut() {
            *word ^= (*word >> shift) & mask;
        }

        if N < 6 {
            output.value[0] &= (1u64 << (1 << N)) - 1;
        }
    } else {
        let stride = 1 << (var_index - 6);
        let step = stride << 1;
        let len = f.len();

        for base in (0..len).step_by(step) {
            for i in 0..stride {
                let v = f[base + stride + i];
                f[base + i] ^= v;
            }
        }
    }

    output
}

// Eliminate all monomials containing (or not containing) the selected variable
pub fn anf_filter_by_var<const N: usize>(
    truth_table: &BoolPoly<N>,
    var_index: usize,
    contains: bool,
) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut output = truth_table.clone();

    // No such variable in this basis: no monomial contains it.
    if var_index >= N {
        if contains {
            for word in output.value.iter_mut() {
                *word = 0;
            }
        }
        return output;
    }

    let f = &mut output.value;

    if var_index < 6 {
        let mask = if contains { VAR_MASKS[var_index] } else { !VAR_MASKS[var_index] };
        for word in f.iter_mut() {
            *word &= mask;
        }
    } else {
        let stride = 1usize << (var_index - 6);
        let step = stride << 1;
        let len = f.len();

        let mut base = 0;
        while base < len {
            if contains {
                for i in 0..stride {
                    f[base + i] = 0;
                }
            } else {
                for i in 0..stride {
                    f[base + stride + i] = 0;
                }
            }
            base += step;
        }
    }

    output
}


pub fn anf_create_variable_table<const N: usize>(
    var_index: usize,
) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut output = BoolPoly::<N>::new();
    debug_assert!(var_index < N, "var_index out of range");
    let bit = 1usize << var_index;
    output.value[bit / 64] = 1u64 << (bit % 64);
    output
}

pub fn anf_eliminate_var<const N: usize>(
    truth_table: &BoolPoly<N>,
    var_index: usize,
) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut output = truth_table.clone();

    if var_index >= N {
        return output; 
    }

    let f = &mut output.value;

    if var_index < 6 {
        let absent_mask = !VAR_MASKS[var_index];
        let shift = 1u32 << var_index;
        for word in f.iter_mut() {
            let present = (*word >> shift) & absent_mask;
            let absent = *word & absent_mask;
            *word = present ^ absent;
        }
    } else {
        let stride = 1usize << (var_index - 6);
        let step = stride << 1;
        let len = f.len();

        let mut base = 0;
        while base < len {
            for i in 0..stride {
                f[base + i] ^= f[base + stride + i];
                f[base + stride + i] = 0;
            }
            base += step;
        }
    }

    output
}

pub fn anf_multiply_by_var<const N: usize>(
    truth_table: &BoolPoly<N>,
    var_index: usize,
) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut output = BoolPoly::<N>::new();
    if var_index >= N {
        return output;
    }

    let src = &truth_table.value;
    let dst = &mut output.value;
    let len = src.len();

    if var_index < 6 {
        let present_mask = VAR_MASKS[var_index];
        let shift = 1u32 << var_index;
        for i in 0..len {
            let w = src[i];
            let present = w & present_mask;
            let absent = w & !present_mask;
            dst[i] = present ^ (absent << shift);
        }
    } else {
        let stride = 1usize << (var_index - 6);
        let step = stride << 1;

        let mut base = 0;
        while base < len {
            for i in 0..stride {
                let absent = src[base + i];
                let present = src[base + stride + i];
                dst[base + i] = 0;
                dst[base + stride + i] = present ^ absent;
            }
            base += step;
        }
    }

    output
}


pub fn anf_reorder_variables<const N: usize>(
    truth_table: &BoolPoly<N>,
    permutation: &[u8; N],
) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut output = BoolPoly::new();
    for i in 0..BoolPoly::<N>::BIT_SIZE {
        let m = truth_table.get_bit(i);
        if m.is_zero() {
            continue;
        }

        let mut old = m.m_vars;
        let mut new = 0;
        for j in 0..N {
            if (old & (1 << j)) == 0 {
                continue;
            }
            new |= 1 << permutation[j];
        }

        let new_monomial = Monomial::<N>::from_vars(new);
        output.set_bit(new_monomial.index(), true);
    }

    return output;
}

// Append K variables to a truth table in disjunctive normal form.
// This is equivalent to repeating the original truth table 2^K times.
pub fn dnf_append_variables<const N: usize, const K: usize>(
    truth_table: &BoolPoly<N>,
) -> BoolPoly<{ N + K }>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << (N + K)) / 64 + ((1 << (N + K)) % 64 != 0) as usize]: Sized,
{
    let mut output = BoolPoly::<{ N + K }>::new();

    if N >= 6 {
        let src = &truth_table.value;
        let dst = &mut output.value;
        let src_len = src.len();
        for chunk in dst.chunks_mut(src_len) {
            chunk.copy_from_slice(src);
        }
    } else {
        let pattern_len = 1 << N;
        let mut pattern = truth_table.value[0];

        // Clear high bits
        if pattern_len < 64 {
            pattern &= (1u64 << pattern_len) - 1;
        }

        // Repeat the pattern
        let mut shift = pattern_len;
        while shift < 64 {
            pattern |= pattern << shift;
            shift *= 2;
        }

        if N + K >= 6 {
            output.value.fill(pattern);
        } else {
            let final_mask = (1u64 << (1 << (N + K))) - 1;
            output.value[0] = pattern & final_mask;
        }
    }

    output
}

// Appending K variables to a truth table in algebraic normal form.
// This is equivalent to zero-extending the original truth table from width 2**N to 2**(N+K).
pub fn anf_append_variables<const N: usize, const K: usize>(
    truth_table: &BoolPoly<N>,
) -> BoolPoly<{ N + K }>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << (N + K)) / 64 + ((1 << (N + K)) % 64 != 0) as usize]: Sized,
{
    let mut output = BoolPoly::<{ N + K }>::new();
    for i in 0..truth_table.value.len() {
        output.value[i] = truth_table.value[i];
    }
    return output;
}

// Gets the number of possible unique boolean functions for a given number of variables
pub fn get_num_unique_booleans(num_vars: usize) -> usize {
    1 << (1 << num_vars)
}

// Swaps two adjacent variable in the truth table
// Works for both ANF and DNF
pub fn swap_adjacent_inplace<const N: usize>(truth_table: &mut BoolPoly<N>, k: usize)
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let tt = &mut truth_table.value;

    if k < 5 {
        const MASKS: [u64; 5] = [
            0x2222222222222222,
            0x0C0C0C0C0C0C0C0C,
            0x00F000F000F000F0,
            0x0000FF000000FF00,
            0x00000000FFFF0000,
        ];

        let mask = MASKS[k];
        let shift = 1 << k;

        for word in tt.iter_mut() {
            let val = *word;
            let diff = (val ^ (val >> shift)) & mask;
            *word = val ^ diff ^ (diff << shift);
        }
    } else if k == 5 {
        for chunk in tt.chunks_exact_mut(2) {
            let w_even = chunk[0];
            let w_odd = chunk[1];

            let mask_lo: u64 = 0x00000000FFFFFFFF;

            let even_lo = w_even & mask_lo;
            let odd_hi = w_odd & !mask_lo;

            let even_hi = w_even >> 32;
            let odd_lo = w_odd & mask_lo;

            chunk[0] = even_lo | (odd_lo << 32);
            chunk[1] = odd_hi | even_hi;
        }
    }
    // For high variables we just swap memory blocks
    else {
        let stride = 1 << (k - 6);
        let block_size = stride * 4;

        for chunk in tt.chunks_exact_mut(block_size) {
            let (left, right) = chunk.split_at_mut(stride * 2);

            let block_01 = &mut left[stride..];
            let block_10 = &mut right[..stride];

            block_01.swap_with_slice(block_10);
        }
    }
}

