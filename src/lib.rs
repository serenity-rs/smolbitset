#![allow(dead_code)]

use core::{panic, slice};
use std::alloc::{self, Layout, handle_alloc_error};
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};
use std::ops::{Shl, ShlAssign, Shr, ShrAssign};
use std::ptr;
use std::str::FromStr;

type BitSliceType = u32;
const BST_BITS: usize = BitSliceType::BITS as usize;
const INLINE_SLICE_PARTS: usize = usize::BITS as usize / BST_BITS;

pub struct SmolBitSet {
    ptr: *mut BitSliceType,
}

impl SmolBitSet {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            ptr: 1 as _, //ptr::without_provenance_mut(1),
        }
    }

    #[inline]
    fn is_inline(&self) -> bool {
        self.ptr.addr() & 0b1 == 1
    }

    #[inline]
    unsafe fn get_inline_data_unchecked(&self) -> usize {
        self.ptr.addr() >> 1
    }

    #[inline]
    const unsafe fn write_inline_data_unchecked(&mut self, data: usize) {
        self.ptr = ptr::without_provenance_mut((data << 1) | 0b1);
    }

    fn len(&self) -> BitSliceType {
        if self.is_inline() {
            return 0;
        }

        unsafe { self.len_unchecked() }
    }

    #[inline]
    const unsafe fn len_unchecked(&self) -> BitSliceType {
        unsafe { *self.ptr }
    }

    fn as_slice(&self) -> &[BitSliceType] {
        if self.is_inline() {
            return &[];
        }

        unsafe { self.as_slice_unchecked() }
    }

    #[inline]
    const unsafe fn as_slice_unchecked(&self) -> &[BitSliceType] {
        unsafe { slice::from_raw_parts(self.ptr.add(1), self.len_unchecked() as usize) }
    }

    fn as_slice_mut(&mut self) -> &mut [BitSliceType] {
        if self.is_inline() {
            return &mut [];
        }

        unsafe { self.as_slice_mut_unchecked() }
    }

    #[inline]
    const unsafe fn as_slice_mut_unchecked(&mut self) -> &mut [BitSliceType] {
        unsafe { slice::from_raw_parts_mut(self.ptr.add(1), self.len_unchecked() as usize) }
    }

    fn spill(&mut self, highest_bit: usize) {
        if !self.is_inline() {
            return;
        }

        let len = (highest_bit).div_ceil(BST_BITS);
        let len = len.max(INLINE_SLICE_PARTS);

        let layout = slice_layout::<BitSliceType>(len);
        let ptr = unsafe { alloc::alloc_zeroed(layout).cast::<BitSliceType>() };
        if ptr.is_null() {
            handle_alloc_error(layout)
        }

        let new = unsafe {
            *ptr = len as BitSliceType; // store the length in the first element
            slice::from_raw_parts_mut(ptr.add(1), len)
        };

        let old = self.ptr.addr() >> 1;

        new.iter_mut()
            .enumerate()
            .take(INLINE_SLICE_PARTS)
            .for_each(|(i, elem)| {
                *elem = (old >> (i * BST_BITS)) as BitSliceType;
            });

        self.ptr = ptr;
    }

    fn ensure_capacity(&mut self, highest_bit: usize) {
        if self.is_inline() {
            if highest_bit >= (usize::BITS as usize) {
                self.spill(highest_bit);
            }

            return;
        }

        let len = unsafe { self.len_unchecked() } as usize;
        if highest_bit < (BST_BITS * len) {
            return;
        }

        // we need to grow our slice allocation
        let new_len = (highest_bit).div_ceil(BST_BITS);
        debug_assert!(new_len >= len);

        let layout = slice_layout::<BitSliceType>(len);
        let new_layout = slice_layout::<BitSliceType>(new_len);
        let new_ptr = unsafe {
            #[allow(clippy::cast_ptr_alignment)]
            alloc::realloc(self.ptr.cast::<u8>(), layout, new_layout.size()).cast::<BitSliceType>()
        };
        if new_ptr.is_null() {
            handle_alloc_error(new_layout)
        }

        unsafe {
            // initializing newly allocated memory to zero
            // slice::from_raw_parts_mut(new_ptr.add(1 + len), new_len - len).fill(0);

            // update the new length in the first element
            *new_ptr = new_len as BitSliceType;
        }
        self.ptr = new_ptr;
    }

    fn highest_set_bit(&self) -> usize {
        if self.is_inline() {
            let data = self.ptr.addr() >> 1;
            return highest_set_bit_usize(data);
        }

        let data = unsafe { self.as_slice_unchecked() };
        let mut highest = 0;
        for (idx, &data) in data.iter().enumerate().rev() {
            let h = highest_set_bit(data);
            if h == 0 {
                continue;
            }

            highest = (idx * BST_BITS) + h;
            break;
        }

        highest
    }
}

impl Drop for SmolBitSet {
    fn drop(&mut self) {
        if self.is_inline() {
            return;
        }

        unsafe {
            let layout = slice_layout::<BitSliceType>(self.len_unchecked() as usize);
            alloc::dealloc(self.ptr.cast::<u8>(), layout);
        }
    }
}

impl Default for SmolBitSet {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for SmolBitSet {
    fn clone(&self) -> Self {
        if self.is_inline() {
            return Self { ptr: self.ptr };
        }

        let src = unsafe { self.as_slice_unchecked() };
        let len = src.len();
        let layout = slice_layout::<BitSliceType>(len);
        let ptr = unsafe {
            #[allow(clippy::cast_ptr_alignment)]
            alloc::alloc_zeroed(layout).cast::<BitSliceType>()
        };
        if ptr.is_null() {
            handle_alloc_error(layout)
        }

        let new_data = unsafe {
            *ptr = len as BitSliceType; // store the length in the first element
            slice::from_raw_parts_mut(ptr.add(1), len)
        };
        new_data.copy_from_slice(src);

        Self { ptr }
    }
}

fn slice_layout<T>(len: usize) -> Layout {
    let len = len + 1; // +1 for the length since we store the length in the first element
    let single = Layout::new::<T>().pad_to_align();
    if let Some(size) = single.size().checked_mul(len) {
        Layout::from_size_align(size, single.align()).expect("Layout error in SmolBitSet slice")
    } else {
        panic!("Overflow in SmolBitSet slice layout");
    }
}

fn highest_set_bit(data: BitSliceType) -> usize {
    if data == 0 {
        return 0;
    }

    for i in (0..BST_BITS).rev() {
        if data & (1 << i) != 0 {
            return i + 1;
        }
    }

    0
}

fn highest_set_bit_usize(data: usize) -> usize {
    if data == 0 {
        return 0;
    }

    for i in (0..usize::BITS as usize).rev() {
        if data & (1 << i) != 0 {
            return i + 1;
        }
    }

    0
}

fn sbs_shl(sbs: &mut SmolBitSet, rhs: usize) {
    if rhs == 0 {
        return;
    }

    let hb: usize = sbs.highest_set_bit();
    sbs.ensure_capacity(hb + rhs);

    if sbs.is_inline() {
        unsafe {
            sbs.write_inline_data_unchecked(
                sbs.get_inline_data_unchecked()
                    .checked_shl(rhs as u32)
                    .unwrap_or(0),
            );
        }
    } else {
        let data = unsafe { sbs.as_slice_mut_unchecked() };

        // shifting further than one slice member?
        let offset = rhs / BST_BITS;
        if offset > 0 {
            for i in (0..data.len()).rev() {
                data[i] = if let Some(src_idx) = i.checked_sub(offset) {
                    data[src_idx]
                } else {
                    0
                };
            }
        }

        let shift = rhs % BST_BITS;
        if shift == 0 {
            // offset shifting was enough
            return;
        }

        let carry_shift = BST_BITS - shift;
        let mut carry = 0;
        for d in data.iter_mut() {
            let new = (*d << shift) | carry;
            carry = *d >> carry_shift;
            *d = new;
        }
    }
}

fn sbs_shr(sbs: &mut SmolBitSet, rhs: usize) {
    if rhs == 0 {
        return;
    }

    if sbs.is_inline() {
        unsafe {
            sbs.write_inline_data_unchecked(
                sbs.get_inline_data_unchecked()
                    .checked_shr(rhs as u32)
                    .unwrap_or(0),
            );
        }
    } else {
        let data = unsafe { sbs.as_slice_mut_unchecked() };

        // shifting further than one slice member?
        let offset = rhs / BST_BITS;
        if offset > 0 {
            let len = data.len();
            for i in 0..len {
                data[i] = if (i + offset) < len {
                    data[i + offset]
                } else {
                    0
                };
            }
        }

        let shift = rhs % BST_BITS;
        if shift == 0 {
            // offset shifting was enough
            return;
        }

        let carry_shift = BST_BITS - shift;
        let mut carry = 0;
        for d in data.iter_mut().rev() {
            let new = (*d >> shift) | carry;
            carry = *d << carry_shift;
            *d = new;
        }
    }
}

macro_rules! impl_shifts {
    ($($t:ty),+) => {$(
        impl Shl<$t> for SmolBitSet {
            type Output = Self;

            fn shl(mut self, rhs: $t) -> Self {
                sbs_shl(&mut self, rhs as usize);
                self
            }
        }

        impl ShlAssign<$t> for SmolBitSet {
            fn shl_assign(&mut self, rhs: $t) {
                sbs_shl(self, rhs as usize);
            }
        }

        impl Shr<$t> for SmolBitSet {
            type Output = Self;

            fn shr(mut self, rhs: $t) -> Self {
                sbs_shr(&mut self, rhs as usize);
                self
            }
        }

        impl ShrAssign<$t> for SmolBitSet {
            fn shr_assign(&mut self, rhs: $t) {
                sbs_shr(self, rhs as usize);
            }
        }

        impl_shifts!(@ref $t);
    )*};
    (@ref $t:ty) => {
        impl Shl<&$t> for SmolBitSet {
            type Output = Self;

            fn shl(self, rhs: &$t) -> Self {
                self.shl(*rhs)
            }
        }

        impl ShlAssign<&$t> for SmolBitSet {
            fn shl_assign(&mut self, rhs: &$t) {
                self.shl_assign(*rhs)
            }
        }

        impl Shr<&$t> for SmolBitSet {
            type Output = Self;

            fn shr(self, rhs: &$t) -> Self {
                self.shr(*rhs)
            }
        }

        impl ShrAssign<&$t> for SmolBitSet {
            fn shr_assign(&mut self, rhs: &$t) {
                self.shr_assign(*rhs)
            }
        }
    }
}

impl_shifts!(u8, u16, u32, u64, usize);

macro_rules! impl_bitop {
    ($($OP:ident :: $op:ident, $OPA:ident :: $opa:ident),+) => {$(
        impl $OP<Self> for SmolBitSet {
            type Output = Self;

            fn $op(self, rhs: Self) -> Self {
                let mut lhs = self;
                lhs.$opa(rhs);
                lhs
            }
        }

        impl $OPA<Self> for SmolBitSet {
            fn $opa(&mut self, rhs: Self) {
                self.$opa(&rhs);
            }
        }

        impl_bitop!(@ref $OP :: $op, $OPA :: $opa);
    )*};
    (@ref $OP:ident :: $op:ident, $OPA:ident :: $opa:ident) => {
        impl $OP<&Self> for SmolBitSet {
            type Output = Self;

            fn $op(self, rhs: &Self) -> Self {
                let mut lhs = self;
                lhs.$opa(rhs);
                lhs
            }
        }

        impl $OPA<&Self> for SmolBitSet {
            fn $opa(&mut self, rhs: &Self) {
                match (self.is_inline(), rhs.is_inline()) {
                    (true, true) => unsafe {
                        let lhs = self.get_inline_data_unchecked();
                        let rhs = rhs.get_inline_data_unchecked();
                        self.write_inline_data_unchecked(lhs.$op(rhs));
                    },
                    (_, false) => {
                        let rhs_hb = rhs.highest_set_bit();
                        if rhs_hb > self.highest_set_bit() {
                            self.ensure_capacity(rhs_hb);
                        }

                        let lhs = unsafe { self.as_slice_mut_unchecked() };
                        let rhs = unsafe { rhs.as_slice_unchecked() };

                        assert!(lhs.len() >= rhs.len());

                        // in case lhs > rhs we need to have extra elements
                        let rhs_iter = rhs.iter().chain(std::iter::repeat(&0));

                        for (lhs, rhs) in lhs.iter_mut().zip(rhs_iter) {
                            (*lhs).$opa(*rhs);
                        }
                    }
                    (false, true) => {
                        let lhs = unsafe { self.as_slice_mut_unchecked() };
                        let rhs = unsafe { rhs.get_inline_data_unchecked() };

                        lhs.iter_mut()
                            .enumerate()
                            .take(INLINE_SLICE_PARTS)
                            .for_each(|(idx, lhs)| {
                                (*lhs).$opa((rhs >> (idx * BST_BITS)) as BitSliceType);
                            });
                    }
                }
            }
        }
    };
}

impl_bitop! {
    BitOr::bitor, BitOrAssign::bitor_assign,
    BitAnd::bitand, BitAndAssign::bitand_assign,
    BitXor::bitxor, BitXorAssign::bitxor_assign
}

macro_rules! impl_binop_prim {
    ($($OP:ident :: $op:ident, $OPA:ident :: $opa:ident, $t:ty),+) => {$(
        impl $OP<$t> for SmolBitSet {
            type Output = Self;

            fn $op(self, rhs: $t) -> Self {
                let mut lhs = self;
                lhs.$opa(rhs);
                lhs
            }
        }

        impl $OPA<$t> for SmolBitSet {
            fn $opa(&mut self, rhs: $t) {
                self.$opa(Self::from(rhs))
            }
        }

        impl_binop_prim!(@ref $OP :: $op, $OPA :: $opa, $t);
    )*};
    (@ref $OP:ident :: $op:ident, $OPA:ident :: $opa:ident, $t:ty) => {
        impl $OP<&$t> for SmolBitSet {
            type Output = Self;

            fn $op(self, rhs: &$t) -> Self {
                self.$op(*rhs)
            }
        }

        impl $OPA<&$t> for SmolBitSet {
            fn $opa(&mut self, rhs: &$t) {
                self.$opa(*rhs)
            }
        }
    };
    ($($t:ty),+) => {$(
        impl_binop_prim!{
            BitOr::bitor, BitOrAssign::bitor_assign, $t,
            BitAnd::bitand, BitAndAssign::bitand_assign, $t,
            BitXor::bitxor, BitXorAssign::bitxor_assign, $t
        }
    )*};
}

impl_binop_prim!(u8, u16, u32, u64, usize);

macro_rules! impl_from {
    ($($t:ty),+) => {$(
        impl From<$t> for SmolBitSet {
            fn from(value: $t) -> Self {
                let mut sbs = SmolBitSet::new();
                let value = value as usize;
                sbs.ensure_capacity(highest_set_bit_usize(value));

                if sbs.is_inline() {
                    unsafe { sbs.write_inline_data_unchecked(value) };
                } else {
                    let data = unsafe { sbs.as_slice_mut_unchecked() };
                    assert_eq!(data.len(), 2);

                    data[0] = value as BitSliceType;
                    data[1] = (value >> BST_BITS) as BitSliceType;
                }

                sbs
            }
        }

        impl_from!(@ref $t);
    )*};
    (@ref $t:ty) => {
        impl From<&$t> for SmolBitSet {
            fn from(value: &$t) -> Self {
                Self::from(*value)
            }
        }
    }
}

impl_from!(u8, u16, u32, u64, usize);

impl std::fmt::Display for SmolBitSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_inline() {
            return write!(f, "{}", unsafe { self.get_inline_data_unchecked() });
        }

        let tmp = num_bigint::BigUint::from_slice(unsafe { self.as_slice_unchecked() });
        write!(f, "{tmp}")
    }
}

impl TryFrom<String> for SmolBitSet {
    type Error = ();

    fn try_from(value: String) -> Result<Self, Self::Error> {
        Self::from_str(value.as_str())
    }
}

impl FromStr for SmolBitSet {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let tmp = num_bigint::BigUint::from_str(s).map_err(|_| ())?;

        let mut sbs = Self::new();
        sbs.ensure_capacity(tmp.bits() as usize);

        let digits = tmp.to_u32_digits();
        let digit_count = digits.len();
        if sbs.is_inline() {
            match digit_count {
                0 => {}
                1 => unsafe { sbs.write_inline_data_unchecked(digits[0] as usize) },
                2 => unsafe {
                    sbs.write_inline_data_unchecked(
                        (digits[0] as usize) | ((digits[1] as usize) << u32::BITS),
                    );
                },
                _ => unreachable!("Too many digits for inline data"),
            }
        } else {
            assert!(sbs.len() as usize >= digit_count);

            let data = unsafe { sbs.as_slice_mut_unchecked() };
            data[0..digit_count].copy_from_slice(&digits);
        }

        Ok(sbs)
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;

    #[test]
    fn check_highest_set_bit() {
        let t = 0;
        assert_eq!(highest_set_bit_usize(t), 0);

        let t = 1;
        assert_eq!(highest_set_bit_usize(t), 1);

        let t = 1 << 3;
        assert_eq!(highest_set_bit_usize(t), 4);

        let t = 1 << 31;
        assert_eq!(highest_set_bit_usize(t), 32);

        let t = 0b10101;
        assert_eq!(highest_set_bit_usize(t), 5);

        let t = 1 << 22;
        assert_eq!(highest_set_bit(t), 23);

        let t = u64::MAX;
        assert_eq!(highest_set_bit_usize(t as usize), 64);
    }

    #[test]
    fn ensure_capacity() {
        let mut t = SmolBitSet::new();
        assert!(t.is_inline());

        t.ensure_capacity(0);
        assert!(t.is_inline());

        t.ensure_capacity(32);
        assert!(t.is_inline());

        t.ensure_capacity(63);
        assert!(t.is_inline());

        t.ensure_capacity(64);
        assert!(!t.is_inline());
        assert_eq!(t.len(), 2);

        t.ensure_capacity(65);
        assert!(!t.is_inline());
        assert_eq!(t.len(), 3);

        t.ensure_capacity(32 * 40);
        assert!(!t.is_inline());
        assert_eq!(t.len(), 40);
    }

    #[test]
    fn set_get_inline() {
        let mut sbs = SmolBitSet::new();
        assert!(sbs.is_inline());

        unsafe {
            let d = sbs.get_inline_data_unchecked();
            assert_eq!(d, 0);

            sbs.write_inline_data_unchecked(0b1010);
            assert!(sbs.is_inline());

            let d = sbs.get_inline_data_unchecked();
            assert_eq!(d, 0b1010);
        }
    }

    #[test]
    fn set_get_slice() {
        let a = SmolBitSet::from(0xC5C5_BEEF_0000_1234u64);
        assert!(!a.is_inline());
        assert_eq!(a.len(), 2);

        let d1 = a.as_slice();
        assert_eq!(d1.len(), 2);
        assert_eq!(d1, [0x_0000_1234, 0xC5C5_BEEF]);

        let mut b = a.clone();
        let d2 = b.as_slice_mut();
        assert_eq!(d2.len(), 2);
        assert_eq!(d2, d1);

        d2[0] = 0xDEAD_BEEF;
        d2[1] = 0xC0FF_EE00;

        let d3 = b.as_slice();
        assert_eq!(d3.len(), 2);
        assert_eq!(d3, [0xDEAD_BEEF, 0xC0FF_EE00]);
    }

    #[test]
    fn spill() {
        let mut sbs = SmolBitSet::new();
        assert!(sbs.is_inline());

        sbs.spill(30);
        assert!(!sbs.is_inline());
        // expecting 2 since the inline data can hold 63 bits already
        // and spill will always allocate to at least store the inline data
        assert_eq!(sbs.len(), 2);

        let mut sbs = SmolBitSet::new();
        assert!(sbs.is_inline());

        sbs.spill(55);
        assert!(!sbs.is_inline());
        assert_eq!(sbs.len(), 2);

        let mut sbs = SmolBitSet::new();
        assert!(sbs.is_inline());

        sbs.spill(64);
        assert!(!sbs.is_inline());
        assert_eq!(sbs.len(), 2);

        let mut sbs = SmolBitSet::new();
        assert!(sbs.is_inline());

        sbs.spill(65);
        assert!(!sbs.is_inline());
        assert_eq!(sbs.len(), 3);
    }

    #[test]
    fn deserialize() {
        let sbs = SmolBitSet::try_from(String::from("1337")).unwrap();
        assert!(sbs.is_inline());
        assert_eq!(unsafe { sbs.get_inline_data_unchecked() }, 1337);

        // A5A5 1337 0000 C0FF EE00 BEEF 0000 A5A5
        let sbs =
            SmolBitSet::try_from(String::from("220179738009501684669546686565819917733")).unwrap();
        assert!(!sbs.is_inline());
        assert_eq!(
            sbs.as_slice(),
            [0x0000_A5A5, 0xEE00_BEEF, 0x0000_C0FF, 0xA5A5_1337]
        );
    }

    #[test]
    fn serialize() {
        let sbs = SmolBitSet::from(1337u32);
        assert_eq!(sbs.to_string(), "1337");

        // A5A5 1337 0000 C0FF EE00 BEEF 0000 A5A5
        let mut sbs = SmolBitSet::from(0xA5A5_1337_0000_C0FFu64);
        sbs <<= 64u8;
        sbs |= 0xEE00_BEEF_0000_A5A5u64;
        assert_eq!(sbs.to_string(), "220179738009501684669546686565819917733");
    }

    mod from {
        use super::*;

        macro_rules! test_from {
            ($($name:ident, $val:expr),+) => {$(
                #[test]
                fn $name() {
                    let t = SmolBitSet::from($val);
                    assert!(t.is_inline());

                    let d = unsafe { t.get_inline_data_unchecked() };
                    assert_eq!(d, $val as usize);
                }
            )*}
        }

        test_from! {
            u8, 0b1110_1010u8,
            u8_max, u8::MAX,
            u16, 0xBEAFu16,
            u16_max, u16::MAX,
            u32, 0xF0BA_B0BBu32,
            u32_max, u32::MAX,
            u64, 0x7550_1337_0000_F00Fu64
        }

        #[test]
        fn u64_hb_64() {
            let t = SmolBitSet::from(0xC5C5_BEEF_0000_1234u64);
            assert!(!t.is_inline());
            assert_eq!(t.len(), 2);

            let d = t.as_slice();
            assert_eq!(d.len(), 2);
            assert_eq!(d, [0x0000_1234, 0xC5C5_BEEF]);
        }

        #[test]
        fn u64_max() {
            let t = SmolBitSet::from(u64::MAX);
            assert_eq!(t.len(), 2);

            let d = t.as_slice();
            assert_eq!(d.len(), 2);
            assert_eq!(d, &[u32::MAX; 2]);
        }
    }

    mod clone {
        use super::*;

        #[test]
        fn inline() {
            let val = 0xC0FE_FE00u32;
            let a = SmolBitSet::from(val);
            #[allow(clippy::redundant_clone)]
            let b = a.clone();

            assert!(a.is_inline());
            assert!(b.is_inline());

            let a_data = unsafe { a.get_inline_data_unchecked() };
            let b_data = unsafe { b.get_inline_data_unchecked() };
            assert_eq!(a_data, b_data);
        }

        #[test]
        fn slice() {
            let val = 0xFFEE_00AA_1337_0420u64;
            let a = SmolBitSet::from(val);
            #[allow(clippy::redundant_clone)]
            let b = a.clone();

            assert!(!a.is_inline());
            assert!(!b.is_inline());

            let a_data = a.as_slice();
            let b_data = b.as_slice();
            assert_eq!(a_data.len(), b_data.len());
            assert_eq!(a_data, b_data);
            assert_eq!(a_data, [0x1337_0420, 0xFFEE_00AA]);
        }
    }

    mod shifts {
        use super::*;

        mod shl {
            use super::*;

            #[test]
            fn inline() {
                let val = 0xABCD_0042u32;
                let mut a = SmolBitSet::from(val);
                assert!(a.is_inline());

                a <<= 6u8;
                assert!(a.is_inline());
                assert_eq!(
                    unsafe { a.get_inline_data_unchecked() },
                    (val as usize) << 6
                );

                let b = a << 4u8;
                assert!(b.is_inline());
                assert_eq!(
                    unsafe { b.get_inline_data_unchecked() },
                    (val as usize) << (6 + 4)
                );
            }

            #[test]
            fn grow_to_slice() {
                let val = 0x00AB_CD55_1337_BEEFu64;
                let mut a = SmolBitSet::from(val);
                assert!(a.is_inline());

                a <<= 8u8;
                assert_eq!(a.len(), 2);
                assert_eq!(a.as_slice(), [0x37BE_EF00u32, 0xABCD_5513u32]);

                let b = a << 24u8;
                assert_eq!(b.len(), 3);
                assert_eq!(
                    b.as_slice(),
                    [0x0000_0000u32, 0x1337_BEEFu32, 0x00AB_CD55u32]
                );
            }

            #[test]
            fn by_multiple_of_32() {
                let val = 0xFFEE_00AA_AFFE_BEEFu64;
                let mut a = SmolBitSet::from(val);
                assert!(!a.is_inline());

                a <<= 32u8;
                assert_eq!(a.len(), 3);
                assert_eq!(a.as_slice(), [0, 0xAFFE_BEEFu32, 0xFFEE_00AAu32]);

                a <<= 64u8;
                assert_eq!(a.len(), 5);
                assert_eq!(a.as_slice(), [0, 0, 0, 0xAFFE_BEEFu32, 0xFFEE_00AAu32]);
            }
        }

        mod shr {
            use super::*;

            #[test]
            fn inline() {
                let val = 0xF00D_BEEFu32;
                let mut a = SmolBitSet::from(val);
                assert!(a.is_inline());

                a >>= 10u8;
                assert!(a.is_inline());
                assert_eq!(
                    unsafe { a.get_inline_data_unchecked() },
                    (val >> 10) as usize
                );

                let b = a >> 10u8;
                assert!(b.is_inline());
                assert_eq!(
                    unsafe { b.get_inline_data_unchecked() },
                    (val >> (10 + 10)) as usize
                );
            }

            #[test]
            fn slice() {
                let val = 0xF420_1337_FEFE_BEEFu64;
                let mut a = SmolBitSet::from(val);
                assert!(!a.is_inline());
                assert_eq!(a.len(), 2);

                a >>= 8u8;
                assert!(!a.is_inline());
                assert_eq!(a.as_slice(), [0x37FE_FEBEu32, 0x00F4_2013u32]);

                let b = a >> 24u8;
                assert!(!b.is_inline());
                assert_eq!(b.as_slice(), [0xF420_1337u32, 0x0000_0000u32]);
            }

            #[test]
            fn by_multiple_of_32() {
                let val = 0xFFEE_00AA_AFFE_BEEFu64;
                let mut a = SmolBitSet::from(val);
                assert!(!a.is_inline());

                a >>= 32u8;
                assert_eq!(a.len(), 2);
                assert_eq!(a.as_slice(), [0xFFEE_00AAu32, 0]);

                let mut a = SmolBitSet::from(val);
                a >>= 64u8;
                assert_eq!(a.len(), 2);
                assert_eq!(a.as_slice(), [0, 0]);
            }
        }

        #[test]
        fn with_offsets() {
            let val = 0xA5A5_BEEF_1337_A5A5u64;
            let mut a = SmolBitSet::from(val);
            assert!(!a.is_inline());
            assert_eq!(a.len(), 2);

            a <<= 64u16 + 24u16;
            assert!(!a.is_inline());
            assert_eq!(a.len(), 2 + 2 + 1);
            assert_eq!(a.as_slice(), [0, 0, 0xA500_0000, 0xEF13_37A5, 0x00A5_A5BE]);

            a >>= 32u32 + 16u32;
            assert!(!a.is_inline());
            assert_eq!(a.len(), 2 + 2 + 1); // still same size, does not auto shrink
            assert_eq!(a.as_slice(), [0, 0x37A5_A500, 0xA5BE_EF13, 0x0000_00A5, 0],);
        }
    }

    mod binops {
        use super::*;

        mod inline {
            use super::*;

            macro_rules! test_inline_binops {
                ($($name:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let a = SmolBitSet::from($a);
                        let b = SmolBitSet::from($b);
                        assert!(a.is_inline());
                        assert!(b.is_inline());

                        let res = a.$name(b);
                        assert!(res.is_inline());

                        let d = unsafe { res.get_inline_data_unchecked() };
                        assert_eq!(d, ($a as usize).$name($b as usize));
                    }
                )*}
            }

            test_inline_binops! {
                bitor, 0xF0F0u16, 0x0F0Fu16,
                bitand, 0xFEFEu16, 0xAFFEu16,
                bitxor, 0x3A52u16, 0xAAE8u16
            }
        }

        mod slice {
            use super::*;

            macro_rules! test_slice_binops {
                ($($name:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let a = SmolBitSet::from($a);
                        let b = SmolBitSet::from($b);
                        assert_eq!(a.len(), 2);
                        assert_eq!(b.len(), 2);

                        let res = a.$name(b);
                        assert_eq!(res.len(), 2);
                        assert_eq!(
                            res.as_slice(),
                            [
                                (($a as BitSliceType).$name($b as BitSliceType)),
                                ((($a >> 32) as BitSliceType).$name(($b >> 32) as BitSliceType))
                            ]
                        );
                    }
                )*}
            }

            test_slice_binops! {
                bitor, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }

        mod mixed {
            use super::*;

            macro_rules! test_mixed_binops {
                ($($name:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let a = SmolBitSet::from($a);
                        let b = SmolBitSet::from($b);
                        assert!(a.is_inline());
                        assert_eq!(b.len(), 2);

                        let res1 = a.clone().$name(b.clone());
                        assert_eq!(res1.len(), 2);
                        assert_eq!(
                            res1.as_slice(),
                            [
                                (($a as BitSliceType).$name($b as BitSliceType)),
                                ((($a >> 32) as BitSliceType).$name(($b >> 32) as BitSliceType))
                            ]
                        );

                        let res2 = b.$name(a);
                        assert_eq!(res2.len(), 2);
                        assert_eq!(res2.as_slice(), res1.as_slice());
                    }
                )*}
            }

            test_mixed_binops! {
                bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }

        mod rhs_smaller {
            use super::*;

            macro_rules! test_rhs_smaller_binops {
                ($($name:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let mut lhs = SmolBitSet::from($a);
                        let rhs = SmolBitSet::from($b);
                        lhs <<= 32u8;
                        let lhs_len = lhs.len();
                        assert!(lhs_len > rhs.len());

                        let res = lhs.$name(rhs);
                        assert_eq!(res.len(), lhs_len);
                        assert_eq!(
                            res.as_slice(),
                            [
                                ((0 as BitSliceType).$name($b as BitSliceType)),
                                ((($a) as BitSliceType).$name(($b >> 32) as BitSliceType)),
                                ((($a >> 32) as BitSliceType).$name((0 as BitSliceType)))
                            ]
                        );
                    }
                )*};
            }

            test_rhs_smaller_binops! {
                bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }

        mod rhs_larger {
            use super::*;

            macro_rules! test_rhs_larger_binops {
                ($($name:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let lhs = SmolBitSet::from($a);
                        let mut rhs = SmolBitSet::from($b);
                        rhs <<= 32u8;
                        let rhs_len = rhs.len();
                        assert!(rhs_len > lhs.len());

                        let res = lhs.$name(rhs);
                        assert_eq!(res.len(), rhs_len);
                        assert_eq!(
                            res.as_slice(),
                            [
                                (($a as BitSliceType).$name((0 as BitSliceType))),
                                ((($a >> 32) as BitSliceType).$name($b as BitSliceType)),
                                ((0 as BitSliceType).$name((($b >> 32) as BitSliceType)))
                            ]
                        );
                    }
                )*};
            }

            test_rhs_larger_binops! {
                bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }
    }
}
