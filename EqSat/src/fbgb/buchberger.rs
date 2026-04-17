use crate::bool_poly::{BoolPoly, Monomial};
use crate::transforms::fast_dnf_transform;
use bit_set::{self, BitSet};
#[cfg(feature = "enable-m4ri-rust")]
use m4ri_rust::ffi;
#[cfg(feature = "enable-m4ri-rust")]
use m4ri_rust::ffi::*;
#[cfg(feature = "enable-m4ri-rust")]
use m4ri_rust::friendly::BinMatrix;
#[cfg(feature = "enable-m4ri-rust")]
use m4ri_rust::friendly::BinVector;
use std::collections::VecDeque;
use std::ffi::c_int;

// Computes a groebner basis for boolean polynomials
#[inline(never)]
pub fn buchberger<const N: usize>(
    F: &mut Vec<BoolPoly<N>>,
    process_critical_pairs: bool,
) -> Vec<BoolPoly<N>>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    // Auto reduction is at least one order of magnitude faster if we put the system in RREF first.
    // `lower_echelonize` assumes the system is in lower triangular form, which is always true if the system
    // comes from a completely specified boolean truth table.
    lower_echelonize(F);

    let mut g = autoreduce(&mut F.clone());

    // If the system comes from a completely specified boolean truth table,
    // `autoreduce` produces a reduced groebner basis.
    if !process_critical_pairs {
        return g;
    }

    // Matrix M with treated pairs
    let mut k = g.len();
    let mut m: Vec<BitSet> = vec![BitSet::with_capacity(k); k];
    let mut pairs: VecDeque<(i32, usize)> = VecDeque::new();
    for i in -(N as i32)..k as i32 {
        for j in 0..k {
            if i < j as i32 {
                pairs.push_back((i, j));
            }
        }
    }

    // Process critical pairs
    while let Some((i, j)) = pairs.pop_front() {
        let mut s = BoolPoly::<N>::new();

        if i < 0 {
            let gj_lm = g[j].lm();
            let xi = Monomial::<N>::from_vars(1 << (((-i) as u32) - 1));

            if gj_lm.is_relatively_prime(&xi) {
                continue;
            }

            s = &s + &g[j];
        } else {
            let i = i as usize;
            m[i].insert(j);

            let p = &g[i];
            let q = &g[j];

            if criteria(i, j, p, q, &m, &g) {
                continue;
            }

            s = spoly(p, q);
        }

        let h = normal_form(&s, &g, g.len());
        if h.is_zero() {
            continue;
        }

        g.push(h);
        for i in -(N as i32)..k as i32 {
            pairs.push_back((i, k));
        }

        k += 1;
        // Enlarge M for new h entry
        for row in m.iter_mut() {
            row.insert(0);
        }
        m.push(BitSet::with_capacity(k));
    }

    let gb = autoreduce(&mut g);
    return gb;
}

// TODO: Use stack allocated buffer wrapper.
#[inline(never)]
pub fn autoreduce<const N: usize>(mut F: &mut Vec<BoolPoly<N>>) -> Vec<BoolPoly<N>>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    // Stack allocated buffer
    let mut before_p = [BoolPoly::<N>::new(); (1 << N) as usize];
    let mut before_p_index = 0;
    let mut after_p = [BoolPoly::<N>::new(); (1 << N) as usize];
    let mut after_p_index = 0;

    while F.len() > 0 {
        let mut h = F.pop().unwrap();
        h = normal_form(&h, &before_p, before_p_index);
        if h.is_zero() {
            continue;
        }

        // Compute and cache leading monomial since this has not happened before
        h.update_lm();
        let hlm = h.lm();

        for i in 0..before_p_index {
            let itp = &before_p[i];
            if itp.lm().is_divisible(&hlm) {
                F.push(itp.clone());
                continue;
            }

            after_p[after_p_index] = itp.clone();
            after_p_index += 1;
        }

        // Push h
        after_p[after_p_index] = h;
        after_p_index += 1;

        for i in 0..after_p_index {
            before_p[i] = after_p[i].clone();
        }

        before_p_index = after_p_index;
        after_p_index = 0;
    }

    let mut P = Vec::with_capacity(before_p_index);
    for i in 0..before_p_index {
        P.push(before_p[i].clone());
    }

    // TODO: Use VecDeque
    let mut psize = P.len();
    for i in 0..psize {
        let h = P.remove(0);
        let h = normal_form(&h, &P, P.len());
        if h.is_zero() {
            psize = psize - 1;
        } else {
            P.push(h);
        }
    }

    return P;
}

pub fn normal_form<const N: usize>(f: &BoolPoly<N>, F: &[BoolPoly<N>], f_len: usize) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    let mut p = f.clone();
    let mut r = BoolPoly::<N>::new();

    if f_len == 0 {
        return p;
    }

    while !p.is_zero() {
        let mut i = 0;
        let mut divisionoccurred = false;
        let plm = p.lm();

        while i < f_len && !divisionoccurred {
            let film = F[i].lm();
            if plm.is_divisible(&film) {
                let div = plm / film;
                p = p + &F[i] * div;
                p.update_lm();
                divisionoccurred = true;
            } else {
                i += 1;
            }
        }

        if !divisionoccurred {
            r = &r + plm;
            p = &p + plm;
            p.update_lm();
        }
    }

    return r;
}

// Convert a lower triangular gf2 matrix to reduced row echelon form.
pub fn lower_echelonize<const N: usize>(F: &mut Vec<BoolPoly<N>>)
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let rows = F.len();
    for pi in 0..rows {
        let p = F[pi].clone();
        let pivot_col = p.lm();
        let pivot_idx = pivot_col.index();
        if pivot_col.is_zero() {
            continue;
        }

        for ji in pi + 1..rows {
            let j = unsafe { F.get_unchecked_mut(ji) };
            if j.get_bit(pivot_idx).is_zero() {
                continue;
            }

            *j = &*j + &p;
            j.update_lm();
        }
    }
}

// Faster version of lower_echelonize
#[inline(never)]
pub fn fast_lower_echelonize<const N: usize>(F: *mut BoolPoly<N>, rows: usize)
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut zero = BoolPoly::<N>::new();

    let rows = rows;
    for pi in 0..rows {
        let p = unsafe { *F.add(pi) };
        let pivot_col = p.lm();
        let pivot_idx = pivot_col.index();

        if pivot_col.is_zero() {
            continue;
        }

        for ji in pi + 1..rows {
            let j = unsafe { F.add(ji) };

            let bit_set = unsafe { ((*j).value[0] >> (pivot_idx)) & 1 };
            let mask = 0u64.wrapping_sub(bit_set);
            zero.value[0] = mask;
            zero.value[0] &= p.value[0];

            unsafe { *j = &*j + (&zero) };
            unsafe { (*j).update_lm() };
        }
    }
}

// Eliminate polynomials covered by combinations of other polynomials
// This is basically a greedy set cover, where small elements (`a`, `b`, `a&b`) are preferred over larger elements.
#[inline(never)]
pub fn optimize_cover<const N: usize>(F: &Vec<BoolPoly<N>>) -> Vec<BoolPoly<N>>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut output = Vec::new();
    let mut cover = BoolPoly::<N>::new();
    for f in F.iter().rev() {
        let dnf = fast_dnf_transform(f);

        let shared = dnf_and(&cover, &dnf);
        if shared == dnf {
            continue;
        }

        // Otherwise they don't overlap
        cover = dnf_or(&cover, &dnf);
        output.push(f.clone());
    }

    return output;
}

pub fn dnf_or<const N: usize>(a: &BoolPoly<N>, b: &BoolPoly<N>) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut cover = BoolPoly::<N>::new();
    for i in 0..a.value.len() {
        cover.value[i] = a.value[i] | b.value[i];
    }
    cover
}

pub fn dnf_and<const N: usize>(a: &BoolPoly<N>, b: &BoolPoly<N>) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut cover = BoolPoly::<N>::new();
    for i in 0..a.value.len() {
        cover.value[i] = a.value[i] & b.value[i];
    }
    cover
}

pub fn criteria<const N: usize>(
    i: usize,
    j: usize,
    p: &BoolPoly<N>,
    q: &BoolPoly<N>,
    M: &Vec<BitSet>,
    G: &Vec<BoolPoly<N>>,
) -> bool
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    if p.lm().is_relatively_prime(&q.lm()) {
        return true;
    }

    let g_size = G.len();
    let pq_lcm = p.lm() * q.lm();
    for k in 0..g_size {
        if M[i].contains(k) && M[k].contains(j) && G[k].lm().is_divisible(&pq_lcm) {
            return true;
        }
    }

    return false;
}

pub fn spoly<const N: usize>(f: &BoolPoly<N>, g: &BoolPoly<N>) -> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let f_lm = f.lm();
    let g_lm = g.lm();
    let lcm = f_lm * g_lm;

    return &(f * (lcm / f_lm)) + &(g * (lcm / g_lm));
}

// Take a list of boolean polynomials, and print a bitwise OR of their string representations.
pub fn system_to_bool_str<const N: usize>(F: &mut Vec<BoolPoly<N>>) -> String
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    let mut sb = String::new();
    for i in 0..F.len() {
        sb.push_str("(");
        sb.push_str(&F[i].to_string());
        sb.push_str(")");
        if i != F.len() - 1 {
            sb.push_str(" | ");
        }
    }

    return sb;
}

#[cfg(test)]
mod tests {
    use crate::{splitmix64::SplitMix64, system::get_truth_table_system};

    use super::*;

    #[test]
    fn gb_round_trip() {
        let mut rng = SplitMix64::default();
        test_round_trip::<1>(&mut rng);
        test_round_trip::<2>(&mut rng);
        test_round_trip::<3>(&mut rng);
        test_round_trip::<4>(&mut rng);
        test_round_trip::<5>(&mut rng);
        test_round_trip::<6>(&mut rng);
        test_round_trip::<7>(&mut rng);
        test_round_trip::<8>(&mut rng);
    }

    fn test_round_trip<const N: usize>(rng: &mut SplitMix64)
    where
        [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
        [(); (1 << N) as usize]: Sized,
    {
        let mmask = (1u64 << N) - 1;
        for _ in 0..10000 {
            // Get a random boolean polynomial
            let mut poly = BoolPoly::<N>::new();
            for i in 0..poly.value.len() {
                let word = rng.next() & mmask;
                poly.value[i] = word;
            }

            // Reinterpret truth table as a system of nonlinear equatins
            let mut system = get_truth_table_system::<N>(poly);

            let gb = buchberger(&mut system, true);

            let mut result_table = BoolPoly::<N>::new();
            for i in 0..BoolPoly::<N>::BIT_SIZE {
                let mut result = false;
                for f in gb.iter() {
                    result |= f.eval(i as u32);
                }
                result_table.set_bit(i, result);
            }

            assert_eq!(poly, result_table);
        }
    }
}
