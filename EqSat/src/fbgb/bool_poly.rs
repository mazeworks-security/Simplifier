use std::{fmt, time::Instant};

// Boolean monomial
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Monomial<const NUM_VARS: usize> {
    pub is_one: bool,

    pub m_vars: u32,
}


impl<const NUM_VARS: usize> Monomial<NUM_VARS> {
    pub fn new(is_one: bool, m_vars: u32) -> Self {
        Self { is_one, m_vars }
    }

    pub fn from_vars(m_vars: u32) -> Self {
        Self {
            is_one: false,
            m_vars,
        }
    }

    pub fn zero() -> Self {
        Self {
            is_one: false,
            m_vars: 0,
        }
    }

    pub fn one() -> Self {
        Self {
            is_one: true,
            m_vars: 0,
        }
    }

    pub fn is_zero(&self) -> bool {
        !self.is_one && self.m_vars == 0
    }

    pub fn is_one(&self) -> bool {
        self.is_one
    }

    // Returns the truth table index of this monomial
    pub fn index(&self) -> usize {
        if self.is_one {
            0
        } else {
            self.m_vars as usize
        }
    }

    pub fn is_divisible(&self, other: &Self) -> bool {
        if other.is_one {
            return true;
        }
        if self.is_one {
            return false;
        }
        self.m_vars == (self.m_vars | other.m_vars)
    }

    pub fn is_relatively_prime(&self, other: &Self) -> bool {
        if self.m_vars == other.m_vars {
            return true;
        }
        if self.is_one {
            return true;
        }
        let lcm = self.m_vars | other.m_vars;
        (lcm ^ self.m_vars) == other.m_vars
    }

    pub fn contains_var(&self, var_index: usize) -> bool {
        (self.m_vars & (1 << var_index)) != 0
    }

    pub fn eval(&self, input: u32) -> bool {
        if self.is_one {
            return true;
        }
        if self.is_zero() {
            return false;
        }
        (input & self.m_vars) == self.m_vars
    }
}

impl<const NUM_VARS: usize> core::ops::Mul<Monomial<NUM_VARS>> for Monomial<NUM_VARS> {
    type Output = Self;

    fn mul(self, rhs: Monomial<NUM_VARS>) -> Self::Output {
        if self == rhs {
            return self;
        }

        if self.is_one {
            return rhs;
        }

        if rhs.is_one {
            return self;
        }

        if self.is_zero() || rhs.is_zero() {
            return Monomial::zero();
        }

        return Monomial::from_vars(self.m_vars | rhs.m_vars);
    }
}

impl<const NUM_VARS: usize> core::ops::Div<Monomial<NUM_VARS>> for Monomial<NUM_VARS> {
    type Output = Self;

    fn div(self, rhs: Monomial<NUM_VARS>) -> Self::Output {
        if rhs.is_one {
            return self;
        }

        if self == rhs {
            return Monomial::one();
        }

        if !self.is_divisible(&rhs) {
            return Monomial::zero();
        }

        return Monomial::from_vars(self.m_vars ^ rhs.m_vars);
    }
}

impl<const NUM_VARS: usize> fmt::Display for Monomial<NUM_VARS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }
        if self.is_one {
            return write!(f, "1");
        }
        let mut first = true;
        for i in 0..NUM_VARS {
            if (self.m_vars & (1 << i)) == 0 {
                continue;
            }
            if !first {
                write!(f, "*")?;
            }
            write!(f, "x{i}")?;
            first = false;
        }
        Ok(())
    }
}


// Represents a boolean polynomial in lexicographic order
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoolPoly<const N: usize>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    pub value: [u64; (1 << N) / 64 + ((1 << N) % 64 != 0) as usize],
}

impl<const N: usize> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    pub const BIT_SIZE: usize = 1 << N;
    pub const WORD_COUNT: usize = (1 << N) / 64 + ((1 << N) % 64 != 0) as usize;

    /// Creates a new truth table with all zeros.
    pub const fn new() -> Self
    where
        [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
    {
        Self {
            value: [0u64; (1 << N) / 64 + ((1 << N) % 64 != 0) as usize],
            //cached_lm: Monomial::zero(),
        }
    }

    pub fn from_u64(value: u64) -> Self {
        let mut poly = Self::new();
        poly.value[0] = value;
        poly
    }

    pub fn get_bit_size(&self) -> usize {
        Self::BIT_SIZE
    }

    pub fn get_word_count(&self) -> usize {
        Self::WORD_COUNT
    }

    pub fn update_lm(&mut self) {
        //self.cached_lm = self.calc_lm();
    }

    fn calc_lm(&self) -> Monomial<N> {
        let mut lzc = self.leading_zero_count();

        let bit_size = Self::BIT_SIZE as u32;
        if bit_size < 64 {
            lzc = lzc.saturating_sub(64 - bit_size);
        }

        if lzc >= bit_size {
            return Monomial::zero();
        }

        let lm_index = (bit_size - 1) - lzc;

        if lm_index == 0 {
            return Monomial::one();
        }

        Monomial::from_vars(lm_index)
    }

    pub fn lm(&self) -> Monomial<N> {
        //self.cached_lm
        self.calc_lm()
    }

    pub fn leading_zero_count(&self) -> u32 {
        let mut count = 0;
        for word in self.value.iter().rev() {
            if *word == 0 {
                count += 64;
            } else {
                count += word.leading_zeros();
                break;
            }
        }
        count
    }

    pub fn trailing_zero_count(&self) -> u32 {
        let mut count = 0;
        for word in self.value.iter() {
            if *word == 0 {
                count += 64;
            } else {
                count += word.trailing_zeros();
                break;
            }
        }
        count
    }

    pub fn popcount(&self) -> u32 {
        self.value.iter().map(|word| word.count_ones()).sum()
    }

    pub fn is_zero(&self) -> bool {
        for word in self.value.iter() {
            if *word != 0 {
                return false;
            }
        }
        true
    }

    pub fn get_bit(&self, index: usize) -> Monomial<{ N }> {
        let word_index = index / 64;
        let bit_index = index % 64;
        let v = unsafe { *self.value.get_unchecked(word_index) };
        if (v & (1 << bit_index)) == 0 {
            return Monomial::zero();
        }

        if index == 0 {
            return Monomial::one();
        }

        return Monomial::from_vars(index as u32);
    }

    pub fn has_bit(&self, index: usize) -> bool {
        let m = self.get_bit(index);
        !m.is_zero()
    }

    pub fn set_bit(&mut self, index: usize, value: bool) {
        let word_index = index / 64;
        let bit_index = index % 64;
        let word = unsafe { self.value.get_unchecked_mut(word_index) };
        if value {
            *word |= 1 << bit_index;
        } else {
            *word &= !(1 << bit_index);
        }
    }

    pub fn xor_bit(&mut self, index: usize, value: bool) {
        let word_index = index / 64;
        let bit_index = index % 64;
        let word = unsafe { self.value.get_unchecked_mut(word_index) };
        *word ^= (value as u64) << bit_index;
    }

    pub fn bitreverse(&mut self) {
        let bit_size = Self::BIT_SIZE;

        // Reverse the order of words
        self.value.reverse();

        // Reverse bits within each word
        for word in self.value.iter_mut() {
            *word = word.reverse_bits();
        }

        let remainder = bit_size % 64;
        if remainder != 0 {
            let shift = 64 - remainder;
            let mut carry = 0u64;
            for word in self.value.iter_mut().rev() {
                let new_carry = *word << (64 - shift);
                *word = (*word >> shift) | carry;
                carry = new_carry;
            }
        }
    }

    pub fn ult(&self, other: &Self) -> bool {
        return !self.ugt(other) && self != other;
    }

    pub fn ule(&self, other: &Self) -> bool {
        return !self.ugt(other);
    }

    pub fn ugt(&self, other: &Self) -> bool {
        for (w1, w2) in self.value.iter().rev().zip(other.value.iter().rev()) {
            if *w1 > *w2 {
                return true;
            }
            if *w1 < *w2 {
                return false;
            }
        }
        false
    }

    pub fn eval(&self, input: u32) -> bool {
        let mut result = false;
        for i in 0..Self::BIT_SIZE {
            let m = self.get_bit(i);
            result ^= m.eval(input);
        }

        return result;
    }

    pub fn clear(&mut self) {
        self.value.fill(0);
    }

    pub const fn const_clone(&self) -> Self {
        let mut r = BoolPoly::new();
        r.value = self.value;
        return r;
    }

    #[inline]
    pub fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        let lm = divisor.lm();

        if lm.is_zero() {
            return (BoolPoly::new(), self.clone());
        }

        if lm.is_one() {
            return (self.clone(), BoolPoly::new());
        }

        let l_mask = lm.m_vars as usize;
        let l_word = l_mask / 64;
        let l_bit = l_mask % 64;

        let mut tail_words = divisor.value;
        tail_words[l_word] &= !(1u64 << l_bit);

        let mut active_tail_words = 0;
        let mut tail_word_indices = BoolPoly::<N>::new().value;
        for (i, &w) in tail_words.iter().enumerate() {
            if w != 0 {
                tail_word_indices[active_tail_words] = i as u64;
                active_tail_words += 1;
            }
        }

        let mut f = self.clone();
        let mut q = BoolPoly::<N>::new();
        let mut r = BoolPoly::<N>::new();

        let mut wi = Self::WORD_COUNT;
        while wi > 0 {
            wi -= 1;
            while unsafe { *f.value.get_unchecked(wi) } != 0 {
                let word = unsafe { *f.value.get_unchecked(wi) };
                let b = 63 - word.leading_zeros() as usize;
                let i = wi * 64 + b;

                if (i & l_mask) == l_mask {
                    let j = i ^ l_mask;
                    unsafe {
                        *q.value.get_unchecked_mut(j >> 6) |= 1u64 << (j & 63);
                        *f.value.get_unchecked_mut(wi) ^= 1u64 << b;
                        
                        for idx in 0..active_tail_words {
                            let tw = *tail_word_indices.get_unchecked(idx) as usize;
                            let mut bits = *tail_words.get_unchecked(tw);
                            while bits != 0 {
                                let c = bits.trailing_zeros() as usize;
                                bits &= bits - 1;
                                let t = j | (tw * 64 + c);
                                *f.value.get_unchecked_mut(t >> 6) ^= 1u64 << (t & 63);
                            }
                        }
                    }
                } else {
                    unsafe {
                        *r.value.get_unchecked_mut(wi) |= 1u64 << b;
                        *f.value.get_unchecked_mut(wi) ^= 1u64 << b;
                    }
                }
            }
        }

        (q, r)
    }
}

impl<const N: usize> fmt::Display for BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for i in 0..Self::BIT_SIZE {
            let word_index = i / 64;
            let bit_index = i % 64;
            if (self.value[word_index] & (1u64 << bit_index)) != 0 {
                if !first {
                    write!(f, " + ")?;
                }
                if i == 0 {
                    write!(f, "1")?;
                } else {
                    let monomial = Monomial::<N>::from_vars(i as u32);
                    write!(f, "{}", monomial)?;
                }
                first = false;
            }
        }
        if first {
            write!(f, "0")?;
        }
        Ok(())
    }
}

impl<const N: usize> core::ops::BitAnd for &BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn bitand(self, rhs: Self) -> Self::Output {
        let mut result = BoolPoly::<N>::new();
        for i in 0..Self::Output::WORD_COUNT {
            result.value[i] = self.value[i] & rhs.value[i];
        }
        result
    }
}

impl<const N: usize> core::ops::BitAnd for BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn bitand(self, rhs: Self) -> Self::Output {
        &self &  &rhs
    }
}

impl<const N: usize> core::ops::BitAnd<BoolPoly<N>> for &BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn bitand(self, rhs: BoolPoly<N>) -> Self::Output {
        self & &rhs
    }
}

impl<const N: usize> core::ops::BitOr for &BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn bitor(self, rhs: Self) -> Self::Output {
        let mut result = BoolPoly::<N>::new();
        for i in 0..Self::Output::WORD_COUNT {
            result.value[i] = self.value[i] | rhs.value[i];
        }
        result
    }
}

impl<const N: usize> core::ops::BitOr for BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn bitor(self, rhs: Self) -> Self::Output {
        &self | &rhs
    }
}

impl<const N: usize> core::ops::BitOr<BoolPoly<N>> for &BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn bitor(self, rhs: BoolPoly<N>) -> Self::Output {
        self | &rhs
    }
}

impl<const N: usize> core::ops::Add for &BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn add(self, rhs: Self) -> Self::Output {
        let mut result = BoolPoly::<N>::new();
        for i in 0..Self::Output::WORD_COUNT {
            result.value[i] = self.value[i] ^ rhs.value[i];
        }
        result
    }
}

impl<const N: usize> core::ops::Add for BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn add(self, rhs: Self) -> Self::Output {
        &self + &rhs
    }
}

impl<const N: usize> core::ops::Add<BoolPoly<N>> for &BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn add(self, rhs: BoolPoly<N>) -> Self::Output {
        self + &rhs
    }
}

impl<const N: usize> core::ops::Mul<Monomial<N>> for &BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn mul(self, rhs: Monomial<N>) -> Self::Output {
        return self.mul_monomial(rhs);
        if self.is_zero() || rhs.is_zero() {
            return BoolPoly::<N>::new();
        }

        let mut result = BoolPoly::<N>::new();
        let mut a = self.clone();

        while !a.is_zero() {
            // Get and clear lowest set bit
            let i = a.trailing_zero_count() as usize;
            a.set_bit(i, false);

            // Multiply the monomials by OR-ing their indices,
            // then add the product to the result.
            let j = rhs.index();
            result.xor_bit(i | j, true);
        }
        result
    }
}

impl<const N: usize> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    // Multiply a boolean polynomial by a monomial
    pub fn mul_monomial(mut self, rhs: Monomial<N>) -> BoolPoly<N> {
        if self.is_zero() || rhs.is_zero() {
            return BoolPoly::new();
        }
        if rhs.is_one() {
            return self;
        }

        let vars = rhs.m_vars;
        for k in 0..N {
            if (vars >> k) & 1 == 0 {
                continue;
            }

            if k < 6 {
                let mask = match k {
                    0 => 0x5555555555555555,
                    1 => 0x3333333333333333,
                    2 => 0x0F0F0F0F0F0F0F0F,
                    3 => 0x00FF00FF00FF00FF,
                    4 => 0x0000FFFF0000FFFF,
                    5 => 0x00000000FFFFFFFF,
                    _ => unreachable!(),
                };
                let shift = 1 << k;
                for w in self.value.iter_mut() {
                    let val = *w;
                    *w = (val & !mask) ^ ((val & mask) << shift);
                }
            } else {
                let stride = 1 << (k - 6);
                let step = stride << 1;
                let len = self.value.len();

                for i in (0..len).step_by(step) {
                    let j = i + stride;
                    for offset in 0..stride {
                        let v = self.value[i + offset];
                        self.value[j + offset] ^= v;
                        self.value[i + offset] = 0;
                    }
                }
            }
        }
        self
    }
}

impl<const N: usize> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    pub fn mul_poly(&self, rhs: &Self) -> Self {
        if self.is_zero() || rhs.is_zero() {
            return BoolPoly::<N>::new();
        }

        let lhs_tt = crate::fbgb::transforms::fast_anf_transform(self);
        let rhs_tt = crate::fbgb::transforms::fast_anf_transform(rhs);
        let product_tt = &lhs_tt & &rhs_tt;
        crate::fbgb::transforms::fast_anf_transform(&product_tt)
    }
}

impl<const N: usize> core::ops::Mul<&BoolPoly<N>> for &BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    type Output = BoolPoly<N>;

    fn mul(self, rhs: &BoolPoly<N>) -> Self::Output {
        self.mul_poly(rhs)
    }
}

impl<const N: usize> core::ops::Mul for BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    type Output = BoolPoly<N>;

    fn mul(self, rhs: Self) -> Self::Output {
        (&self).mul_poly(&rhs)
    }
}

impl<const N: usize> core::ops::Mul<BoolPoly<N>> for &BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
    [(); (1 << N) as usize]: Sized,
{
    type Output = BoolPoly<N>;

    fn mul(self, rhs: BoolPoly<N>) -> Self::Output {
        self.mul_poly(&rhs)
    }
}

impl<const N: usize> core::ops::Add<Monomial<N>> for &BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]:,
{
    type Output = BoolPoly<N>;

    fn add(self, rhs: Monomial<N>) -> Self::Output {
        let mut left = self.clone();

        // Fetch the nth bit containing the 'right' monomial
        let idx = rhs.index();
        let a = left.get_bit(idx);

        // XOR the bits coefficient by 1
        let value = !a.is_zero() ^ true;
        left.set_bit(idx, value);
        left
    }
}

impl<const N: usize> BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    pub fn iter(&self) -> MonomialIter<N> {
        MonomialIter::new(self)
    }
}

impl<'a, const N: usize> IntoIterator for &'a BoolPoly<N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    type Item = Monomial<N>;
    type IntoIter = MonomialIter<'a, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct MonomialIter<'a, const N: usize>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    poly: &'a BoolPoly<N>,
    current_word_idx: usize,
    current_word: u64,
}

impl<'a, const N: usize> MonomialIter<'a, N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    fn new(poly: &'a BoolPoly<N>) -> Self {
        let current_word = if !poly.value.is_empty() {
            unsafe { *poly.value.get_unchecked(0) }
        } else {
            0
        };
        Self {
            poly,
            current_word_idx: 0,
            current_word,
        }
    }
}

impl<'a, const N: usize> Iterator for MonomialIter<'a, N>
where
    [(); (1 << N) / 64 + ((1 << N) % 64 != 0) as usize]: Sized,
{
    type Item = Monomial<N>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.current_word != 0 {
                let bit_index = self.current_word.trailing_zeros();
                // Clear the lowest set bit
                self.current_word &= self.current_word - 1;

                let global_index = (self.current_word_idx * 64) + (bit_index as usize);

                if global_index == 0 {
                    return Some(Monomial::one());
                } else {
                    return Some(Monomial::from_vars(global_index as u32));
                }
            }

            self.current_word_idx += 1;
            if self.current_word_idx >= self.poly.value.len() {
                return None;
            }

            self.current_word = unsafe { *self.poly.value.get_unchecked(self.current_word_idx) };
        }
    }
}
