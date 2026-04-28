// Implements NPN canonicalization algorithms
//
use core::num;
use std::arch::x86_64::*;
use std::cmp;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::format;
use std::hash::Hash;
use std::u64;

use crate::fbgb::bool_poly::*;
use crate::fbgb::hamiltonian_paths::*;
use crate::fbgb::transforms::*;

// Truth table where the output and inputs have been possibly negated
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NNTable<const N: usize>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    pub(crate) table: BoolPoly<N>,
    pub(crate) negated_vars: usize,
    pub(crate) negated_constant: bool,
}

impl<const N: usize> NNTable<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    pub const fn new(table: BoolPoly<N>) -> Self {
        Self {
            table,
            negated_vars: 0,
            negated_constant: false,
        }
    }

    pub fn negate_variable(&mut self, var_index: usize) {
        self.table = anf_negate_variable(&self.table, var_index);
        self.negated_vars ^= 1 << var_index;
        self.canonicalize_constant();
    }

    pub fn canonicalize_constant(&mut self) {
        if self.table.has_bit(0) {
            self.table.set_bit(0, false);
            self.negated_constant = true;
        }
    }
}

// Exact canonicalization of a boolean polynomial modulo negation of variables
//
// The algorithm enumerates through all 2^t combinations of variable negations,
// searching for a polynomial with the smallest size. The size is measured by the number and terms and the sum of the degrees of each term.
// If a tie is found, we save the tied candidate using a bitset and pick the smallest one in disjunctive normal form at the end.
#[inline(never)]
pub fn fast_anf_negation_canonicalize<const N: usize>(truth_table: BoolPoly<N>) -> NNTable<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    // The initial best candidate has no negated variables,
    // and the constant term is cleared.
    let mut best = NNTable::new(truth_table.clone());
    best.canonicalize_constant();
    let mut best_literal_count = compute_literal_count(&best.table);

    let mut current = NNTable::new(truth_table.clone());
    current.canonicalize_constant();

    // Store ties as a bitset
    let mut ties = BoolPoly::<N>::new();
    ties.set_bit(0, false);

    for i in 1..(1 << N) {
        // Use gray codes to only flip one variable at each step
        let bit_to_flip = (i as u32).trailing_zeros() as usize;

        // Negate the selected variable and update state accordingly
        current.negate_variable(bit_to_flip);

        if current.table == best.table {
            continue;
        }

        let current_literal_count = compute_literal_count(&current.table);
        // Compare the two ANF polynomials
        let cmp = anf_compare(&current.table, current_literal_count, &best.table, best_literal_count);
        if cmp == Ordering::Less {
            best = current.clone(); 
            best_literal_count = current_literal_count;
            ties.clear();
            continue;
        }
        if cmp == Ordering::Greater {
            continue;
        }

        ties.set_bit(current.negated_vars, true);
    }

    // Return the canonical element if there are no ties
    if ties.popcount() == 0 {
        return best;
    }

    // Return the element with the smallest truth table
    let mut best_dnf = fast_dnf_transform(&best.table);
    let mut bmask = best.negated_vars;
    let mut bnegated = best.negated_constant;
    for tie in ties.iter() {
        // Negate the variables
        let mut candidate = anf_negate_many(&truth_table, tie.index() as u64);
        // Remove the constant offset.
        let mut cnegated = false;
        if candidate.has_bit(0) {
            candidate.set_bit(0, false);
            cnegated = true;
        }

        // Translate to DNF and pick smallest truth table
        let candidate_dnf = fast_dnf_transform(&candidate);
        if candidate_dnf.ult(&best_dnf) {
            best_dnf = candidate_dnf;
            bmask = tie.index();
            bnegated = cnegated;
        }
    }

    let r = fast_anf_transform(&best_dnf);
    return NNTable {
        table: r,
        negated_vars: bmask as usize,
        negated_constant: bnegated,
    };
}

pub fn anf_compare<const N: usize>(
    a: &BoolPoly<N>,
    a_literal_count: usize,
    b: &BoolPoly<N>,
    b_literal_count: usize,
) -> Ordering
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let op0 = a_literal_count + a.popcount() as usize;
    let op1 = b_literal_count + b.popcount() as usize;

    let cmp = op0.cmp(&op1);
    if cmp != Ordering::Equal {
        return cmp;
    }

    return Ordering::Equal;
}

fn compute_term_degree_counts<const N: usize>(truth_table: &BoolPoly<N>) -> [usize; N]
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut counts = [0; N];
    for m in truth_table.iter() {
        let degree = m.m_vars.count_ones() as usize;
        counts[degree - 1] += 1;
    }

    return counts;
}

pub fn compute_literal_count<const N: usize>(truth_table: &BoolPoly<N>) -> usize
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut count = 0;

    let in_word_vars = if N < 6 { N } else { 6 };

    for i in 0..BoolPoly::<N>::WORD_COUNT {
        let word = unsafe { *truth_table.value.get_unchecked(i) };

        count += (i.count_ones() as usize) * (word.count_ones() as usize);

        for j in 0..in_word_vars {
            let mask = unsafe { *VAR_MASKS.get_unchecked(j) };
            count += (word & mask).count_ones() as usize;
        }
    }
    count
}

#[derive(Debug, Clone, Copy)]
pub struct VariableSignature {
    // Indicates whether the variable is dead (not present in any monomial)
    pub dead: bool,

    // DNF weight
    pub weight: u16,

    // Sum of degrees of every monomial containing the variable
    pub total_degree: u32,

    // The original truth table index of the variable
    pub original_index: u8,
}

impl VariableSignature {
    #[inline(always)]
    fn pack(&self) -> u64 {
        let mut res = (self.dead as u64) << 63;
        res |= (self.weight as u64) << 40;
        res |= (self.total_degree as u64) << 8;
        res |= self.original_index as u64;
        res
    }
}

// Ignore the original index when determining value equality
impl PartialEq for VariableSignature {
    fn eq(&self, other: &Self) -> bool {
        self.dead == other.dead
            && self.weight == other.weight
            && self.total_degree == other.total_degree
    }
}

impl Eq for VariableSignature {}

impl PartialOrd for VariableSignature {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for VariableSignature {
    fn cmp(&self, other: &Self) -> Ordering {
        return self.pack().cmp(&other.pack());
        self.dead
            .cmp(&other.dead)
            .then(self.weight.cmp(&other.weight))
            .then(self.total_degree.cmp(&other.total_degree))
    }
}

impl VariableSignature {
    pub fn new() -> Self {
        Self {
            dead: false,
            weight: 0,
            total_degree: 0,
            original_index: 0,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Block {
    pub start_idx: usize,
    pub size: usize,
}

#[inline(never)]
pub fn anf_compute_signature_vector<const N: usize>(a: &BoolPoly<N>) -> [VariableSignature; N]
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let total_degrees = count_literal_degrees(&a);
    let anf_weights = count_anf_weights(a);

    let mut signatures = [VariableSignature::new(); N];
    for i in 0..N {
        signatures[i].dead = total_degrees[i] == 0;
        signatures[i].weight = anf_weights[i] as u16;
        signatures[i].total_degree = total_degrees[i] as u32;
        signatures[i].original_index = i as u8;
    }

    return signatures;
}

// TODO: Delete variables, reformulate as n-d variable permutation calculation.
#[inline(never)]
pub fn permutation_canonicalize<const N: usize>(
    mut a: BoolPoly<N>,
    signature_map: &mut HashMap<[Block; N], u32>,
) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    // Instead of enumerating n! permutations, we can split the variables into groups based on their properties.
    let anf = fast_anf_transform(&a);
    let mut signatures = anf_compute_signature_vector(&anf);

    if N == 5 {
        unsafe {
            sort5(signatures.as_mut_ptr());
        }
    } else {
        signatures.sort();
    }

    let mut blocks = [Block {
        start_idx: 0,
        size: 0,
    }; N];

    // Group variables with identical signatures.
    let mut block_count = 0;
    let mut i = 0;
    while i < N {
        if signatures[i].dead {
            break;
        }

        let mut j = i + 1;
        while j < N && signatures[j] == signatures[i] {
            j += 1;
        }

        let size = j - i;
        if size > 1 {
            blocks[block_count] = Block { start_idx: i, size };
            block_count += 1;
        }
        i = j;
    }

    // Compute an initial variable ordering based on their signatures
    let mut var_indices = [0; N];
    for i in 0..N {
        var_indices[signatures[i].original_index as usize] = i as u8;
    }

    // Apply the initial variable ordering
    let mut curr = anf.clone();
    unsafe {
        permute_variables(&mut curr, &var_indices);
    }

    // Enumerate through all permutations to find a canonical form
    return solve(curr, &blocks, block_count);
}

#[inline(never)]
pub unsafe fn sort5(arr: *mut VariableSignature) {
    // Pack VariableSignatures into comparable u64s
    let mut packed: [u64; 5] = [
        (*arr.add(0)).pack(),
        (*arr.add(1)).pack(),
        (*arr.add(2)).pack(),
        (*arr.add(3)).pack(),
        (*arr.add(4)).pack(),
    ];

    macro_rules! sort_pair {
        ($a:expr, $b:expr) => {{
            let (min, max) = ($a.min($b), $a.max($b));
            $a = min;
            $b = max;
        }};
    }

    // Sort
    sort_pair!(packed[0], packed[1]);
    sort_pair!(packed[3], packed[4]);
    sort_pair!(packed[2], packed[4]);
    sort_pair!(packed[2], packed[3]);
    sort_pair!(packed[1], packed[4]);
    sort_pair!(packed[0], packed[3]);
    sort_pair!(packed[0], packed[2]);
    sort_pair!(packed[1], packed[3]);
    sort_pair!(packed[1], packed[2]);

    // Compute original indices
    let idx: [usize; 5] = [
        (packed[0] & 0xFF) as usize,
        (packed[1] & 0xFF) as usize,
        (packed[2] & 0xFF) as usize,
        (packed[3] & 0xFF) as usize,
        (packed[4] & 0xFF) as usize,
    ];

    let orig = [
        *arr.add(0),
        *arr.add(1),
        *arr.add(2),
        *arr.add(3),
        *arr.add(4),
    ];

    *arr.add(0) = *orig.get_unchecked(idx[0]);
    *arr.add(1) = *orig.get_unchecked(idx[1]);
    *arr.add(2) = *orig.get_unchecked(idx[2]);
    *arr.add(3) = *orig.get_unchecked(idx[3]);
    *arr.add(4) = *orig.get_unchecked(idx[4]);
}

#[inline(never)]
pub unsafe fn permute_variables<const N: usize>(tt: &mut BoolPoly<N>, var_positions: &[u8])
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let num_vars = N;
    let mut current_layout = [0u8; N];
    for i in 0..num_vars {
        *current_layout.get_unchecked_mut(i) = i as u8;
    }

    let mut target_layout = [0u8; N];
    for (old_idx, &new_pos) in var_positions.iter().enumerate() {
        *target_layout.get_unchecked_mut(new_pos as usize) = old_idx as u8;
    }

    for i in 0..num_vars {
        let target_var = *target_layout.get_unchecked(i);
        let mut curr_pos = 0;
        while *current_layout.get_unchecked(curr_pos) != target_var {
            curr_pos += 1;
        }

        while curr_pos > i {
            swap_adjacent_inplace(tt, curr_pos - 1);
            current_layout.swap(curr_pos, curr_pos - 1);
            curr_pos -= 1;
        }
    }
}

// Enumerate through all permutations of variables to find the canonical form
pub fn solve<const N: usize>(
    mut f: BoolPoly<N>,
    blocks: &[Block; N],
    block_count: usize,
) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    if block_count == 0 {
        return f;
    }

    let mut min_f = f;
    solve_recursive(f.clone(), &blocks[0..block_count], 0, &mut min_f);
    min_f
}

pub fn solve_recursive<const N: usize>(
    mut current_f: BoolPoly<N>,
    blocks: &[Block],
    block_idx: usize,
    min_f: &mut BoolPoly<N>,
) where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    // Return if we've explored this branch
    if block_idx >= blocks.len() {
        if current_f.ult(min_f) {
            *min_f = current_f;
        }
        return;
    }

    // Initially we don't permute any variable in this block
    let b = &blocks[block_idx];
    let path: &[u8] = SJT_PATHS[b.size];
    solve_recursive(current_f, blocks, block_idx + 1, min_f);

    // Enumerate through every possible swap in this block
    for &swap_offset in path {
        let swap_idx = b.start_idx + (swap_offset as usize);
        swap_adjacent_inplace(&mut current_f, swap_idx);
        solve_recursive(current_f, blocks, block_idx + 1, min_f);
    }
}

fn count_anf_weights<const N: usize>(anf: &BoolPoly<N>) -> [usize; N]
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut counts = [0; N];
    for word_idx in 0..BoolPoly::<N>::WORD_COUNT {
        let word = unsafe { *anf.value.get_unchecked(word_idx) };

        for i in 0..N.min(6) {
            counts[i] += (word & VAR_MASKS[i]).count_ones() as usize;
        }

        for i in 6..N {
            if (word_idx >> (i - 6)) & 1 != 0 {
                counts[i] += word.count_ones() as usize;
            }
        }
    }
    counts
}

pub fn count_literal_instances<const N: usize>(truth_table: &BoolPoly<N>) -> [usize; N]
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut counts = [0; N];
    for (i, &word) in truth_table.value.iter().enumerate() {
        if word == 0 {
            continue;
        }

        for bit in 6..N {
            if (i >> (bit - 6)) & 1 != 0 {
                counts[bit] += word.count_ones() as usize;
            }
        }

        for bit in 0..N.min(6) {
            if (word & VAR_MASKS[bit]) != 0 {
                counts[bit] += (word & VAR_MASKS[bit]).count_ones() as usize;
            }
        }
    }

    counts
}

pub fn count_literal_degrees<const N: usize>(truth_table: &BoolPoly<N>) -> [usize; N]
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    let mut counts = [0usize; N];

    for i in 0..BoolPoly::<N>::WORD_COUNT {
        let word = unsafe { *truth_table.value.get_unchecked(i) };

        let d_high = i.count_ones() as usize;
        let pw = word.count_ones() as usize;

        let limit = if N < 6 { N } else { 6 };

        let mut local_weights = [0usize; 6];
        let mut total_local_weight = 0;
        for j in 0..limit {
            let p = (word & VAR_MASKS[j]).count_ones() as usize;
            local_weights[j] = p;
            total_local_weight += p;
        }

        // Compute x0..x5 degrees
        for k in 0..limit {
            let mask_k = word & VAR_MASKS[k];
            let term1 = d_high * local_weights[k];

            let mut term2 = 0;
            for j in 0..limit {
                term2 += (mask_k & VAR_MASKS[j]).count_ones() as usize;
            }

            counts[k] += term1 + term2;
        }

        // Compute x6..xn degrees
        if N >= 6 {
            for k in 6..N {
                if (i >> (k - 6)) & 1 != 0 {
                    counts[k] += d_high * pw + total_local_weight;
                }
            }
        }
    }

    counts
}

#[derive(Clone, Copy)]
#[repr(C, align(32))]
pub struct FaceCosts {
    // Low or cross part
    pub cost_face: [u64; 2],

    // High part
    pub cost_high: [u64; 2],
}

/// Generates a 4 variable ANF cost lookup table
pub fn generate_cost_lut() -> Vec<FaceCosts> {
    let mut lut = Vec::with_capacity(65536);

    for val in 0..65536 {
        let mut row_f = [0u8; 16];
        let mut row_h = [0u8; 16];

        for mask in 0..16 {
            let mut t = val as u16;
            // Apply 4-var negations
            if (mask & 1) != 0 {
                t ^= (t & 0xAAAA) >> 1;
            }
            if (mask & 2) != 0 {
                t ^= (t & 0xCCCC) >> 2;
            }
            if (mask & 4) != 0 {
                t ^= (t & 0xF0F0) >> 4;
            }
            if (mask & 8) != 0 {
                t ^= (t & 0xFF00) >> 8;
            }

            let deg = sum_degrees_u16(t);
            let cnt = t.count_ones() as u8;
            let is_const = (t & 1) as u8;

            // Remove constant term
            row_f[mask] = deg + cnt - is_const;

            // Constant term has double weight in the high part
            row_h[mask] = deg + 2 * cnt;
        }

        lut.push(FaceCosts {
            cost_face: pack_u64(&row_f),
            cost_high: pack_u64(&row_h),
        });
    }
    lut
}

#[inline(always)]
fn sum_degrees_u16(val: u16) -> u8 {
    let mut sum = 0;
    let mut temp = val;
    while temp != 0 {
        let idx = temp.trailing_zeros();
        temp &= temp - 1;
        sum += idx.count_ones() as u8;
    }
    sum
}

fn pack_u64(bytes: &[u8; 16]) -> [u64; 2] {
    [
        u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
        u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
    ]
}

// Fast negation canonicalization of 5-variable booleans
#[target_feature(enable = "avx2")]
pub fn ncanon_5(anf: u32, lut: &[FaceCosts]) -> (u32, u8) {
    let low = (anf & 0xFFFF) as usize;
    let high = (anf >> 16) as usize;
    let cross = low ^ high;

    let m_l = unsafe { lut.get_unchecked(low) };
    let m_h = unsafe { lut.get_unchecked(high) };
    let m_c = unsafe { lut.get_unchecked(cross) };

    let cost_a0 = m_l.cost_face[0] + m_h.cost_high[0];
    let cost_a1 = m_l.cost_face[1] + m_h.cost_high[1];
    let cost_b0 = m_c.cost_face[0] + m_h.cost_high[0];
    let cost_b1 = m_c.cost_face[1] + m_h.cost_high[1];

    // Compute a bitmask containing the tied candidates
    let candidates_mask = unsafe { get_min_byte_mask(&[cost_a0, cost_a1, cost_b0, cost_b1]) };

    let mut best_anf = 0xFFFFFFFFu32;
    let mut best_mask = 0u8;
    let mut min_dnf_val = u32::MAX;
    // Iterate through all ties candidates and pick the one with the smallest DNF value
    let mut iter = candidates_mask;
    while iter != 0 {
        let mask_idx = iter.trailing_zeros() as u8;
        iter &= iter - 1;

        let mut candidate_anf = neg5(anf, mask_idx);

        // Negate the constant offset
        candidate_anf &= 0xFFFFFFFE;

        // Convert the poly to DNF
        let poly = BoolPoly::<5>::from_u64(candidate_anf as u64);
        let dnf_val = fast_dnf_transform(&poly).value[0] as u32;

        // Pick the one with the smallest DNF value
        if dnf_val < min_dnf_val {
            min_dnf_val = dnf_val;
            best_anf = candidate_anf;
            best_mask = mask_idx;
        }
    }

    (best_anf, best_mask)
}

fn neg5(mut anf: u32, mask: u8) -> u32 {
    if (mask & 16) != 0 {
        anf ^= (anf >> 16) & 0xFFFF;
    }
    if (mask & 1) != 0 {
        anf ^= (anf & 0xAAAAAAAA) >> 1;
    }
    if (mask & 2) != 0 {
        anf ^= (anf & 0xCCCCCCCC) >> 2;
    }
    if (mask & 4) != 0 {
        anf ^= (anf & 0xF0F0F0F0) >> 4;
    }
    if (mask & 8) != 0 {
        anf ^= (anf & 0xFF00FF00) >> 8;
    }
    anf
}

// Given 32 bytes represented as 4 u64s,
// return a 32-bit mask indicating which bytes are equal to the minimum byte
#[target_feature(enable = "avx2")]
pub unsafe fn get_min_byte_mask(val: &[u64; 4]) -> u32 {
    let vec = _mm256_loadu_si256(val.as_ptr() as *const __m256i);

    let lo_128 = _mm256_castsi256_si128(vec);
    let hi_128 = _mm256_extracti128_si256(vec, 1);

    let mut min_128 = _mm_min_epu8(lo_128, hi_128);

    min_128 = _mm_min_epu8(min_128, _mm_srli_si128(min_128, 8));
    min_128 = _mm_min_epu8(min_128, _mm_srli_si128(min_128, 4));
    min_128 = _mm_min_epu8(min_128, _mm_srli_si128(min_128, 2));
    min_128 = _mm_min_epu8(min_128, _mm_srli_si128(min_128, 1));

    let broadcasted_min = _mm256_broadcastb_epi8(min_128);
    let cmp_mask = _mm256_cmpeq_epi8(vec, broadcasted_min);
    _mm256_movemask_epi8(cmp_mask) as u32
}
