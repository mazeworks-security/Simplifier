use std::arch::x86_64::_bzhi_u64;

// Fast modular multiplicative inverse modulo 2^64
pub fn minv(a: u64) -> u64 {
    let x0 = (3 * a) ^ 2;
    let mut y = 1 - a * x0;
    let x1 = x0 * (1 + y);
    y *= y;
    let x2 = x1 * (1 + y);
    y *= y;
    let x3 = x2 * (1 + y);
    y *= y;
    let x4 = x3 * (1 + y);
    return x4;
}

// Solve for `a*x + b*y` = gcd(a, b)`, where `b` is the modulus subtracted by one.
// The modulus must be a power of two.
pub fn ext_gcd_mod(a: u64, mmask: u64) -> (u64, u64) {
    let tzcnt = a.trailing_zeros();
    let gcd = 1u64 << tzcnt;

    let a1 = a >> tzcnt;
    let x = minv(a1) & mmask;
    return (gcd, x);
}

pub struct Lcg {
    pub x0: u64,
    pub coeff: u64,
    pub count: u64,
    pub mmask: u64,
}

// 2**n where the result overflows to zero if n >= 64
// Rust reduces shifts by w, so this is the fastest way to get the expected behavior.
pub fn pow2(n: u32) -> u64 {
    return unsafe { _bzhi_u64(u64::MAX, n) + 1 };
}

pub fn lcg(a: u64, b: u64, mmask: u64) -> Lcg {
    let (d, u) = ext_gcd_mod(a, mmask);

    if (b & (d - 1)) != 0 {
        return Lcg {
            x0: 0,
            coeff: 0,
            count: 0,
            mmask,
        };
    }

    let x0 = (u * (b >> d.trailing_zeros())) & mmask;
    let coeff = pow2(mmask.count_ones() - d.trailing_zeros()) & mmask;

    return Lcg {
        x0,
        coeff: coeff,
        count: d,
        mmask,
    };
}

impl Lcg {
    pub fn nth(&self, i: u64) -> u64 {
        return self.x0 + i * self.coeff;
    }
}
