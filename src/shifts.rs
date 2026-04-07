use crate::{BST_BITS, SmolBitSet};

use core::ops::{Shl, ShlAssign, Shr, ShrAssign};

fn sbs_shl(sbs: &mut SmolBitSet, rhs: usize) {
    if rhs == 0 {
        return;
    }

    if sbs.is_sparse() {
        let flag = unsafe { sbs.get_inline_sparse_data_unchecked() };
        let rhs = rhs
            .try_into()
            .expect("Cannot shift left by an amount larger than u32::MAX");
        let new_flag = flag
            .checked_add(rhs)
            .expect("Cannot shift left by an amount that causes overflow");

        unsafe {
            sbs.write_inline_sparse_data_unchecked(new_flag);
        }

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

    if sbs.is_sparse() {
        let flag = unsafe { sbs.get_inline_sparse_data_unchecked() };
        let rhs = rhs.try_into().unwrap_or(u32::MAX);
        let new_flag = flag.checked_sub(rhs);

        match new_flag {
            Some(f) => unsafe {
                sbs.write_inline_sparse_data_unchecked(f);
            },
            None => {
                // bitset is now empty, switching to non-sparse inline representation
                *sbs = SmolBitSet::new();
            }
        }

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
    ($($t:ty),+) => {
        impl_shifts!(false, $($t),*);
    };
    (@signed $($t:ty),+) => {
        impl_shifts!(true, $($t),*);
    };
    ($signed:literal, $($t:ty),+) => {$(
        impl Shl<$t> for SmolBitSet {
            type Output = Self;

            #[inline]
            fn shl(mut self, rhs: $t) -> Self {
                #[allow(unused_comparisons)]
                if $signed && rhs < 0 {
                    panic!("Cannot shift left by a negative amount");
                }

                sbs_shl(&mut self, rhs as usize);
                self
            }
        }

        impl ShlAssign<$t> for SmolBitSet {
            #[inline]
            fn shl_assign(&mut self, rhs: $t) {
                #[allow(unused_comparisons)]
                if $signed && rhs < 0 {
                    panic!("Cannot shift left by a negative amount");
                }

                sbs_shl(self, rhs as usize);
            }
        }

        impl Shr<$t> for SmolBitSet {
            type Output = Self;

            #[inline]
            fn shr(mut self, rhs: $t) -> Self {
                #[allow(unused_comparisons)]
                if $signed && rhs < 0 {
                    panic!("Cannot shift right by a negative amount");
                }

                sbs_shr(&mut self, rhs as usize);
                self
            }
        }

        impl ShrAssign<$t> for SmolBitSet {
            #[inline]
            fn shr_assign(&mut self, rhs: $t) {
                #[allow(unused_comparisons)]
                if $signed && rhs < 0 {
                    panic!("Cannot shift right by a negative amount");
                }

                sbs_shr(self, rhs as usize);
            }
        }

        impl_shifts!(@ref $t);
    )*};
    (@ref $t:ty) => {
        impl Shl<&$t> for SmolBitSet {
            type Output = Self;

            #[inline]
            fn shl(self, rhs: &$t) -> Self {
                self.shl(*rhs)
            }
        }

        impl ShlAssign<&$t> for SmolBitSet {
            #[inline]
            fn shl_assign(&mut self, rhs: &$t) {
                self.shl_assign(*rhs)
            }
        }

        impl Shr<&$t> for SmolBitSet {
            type Output = Self;

            #[inline]
            fn shr(self, rhs: &$t) -> Self {
                self.shr(*rhs)
            }
        }

        impl ShrAssign<&$t> for SmolBitSet {
            #[inline]
            fn shr_assign(&mut self, rhs: &$t) {
                self.shr_assign(*rhs)
            }
        }
    };
}

impl_shifts!(u8, u16, u32, u64, usize);
impl_shifts!(@signed i8, i16, i32, i64, isize);

#[cfg(test)]
mod tests {
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

        #[test]
        fn sparse_inline() {
            let flag = 0;
            let mut a = SmolBitSet::new_flag(flag);
            assert!(a.is_inline());
            assert!(a.is_sparse());

            a <<= 6u8;
            assert!(a.is_inline());
            assert!(a.is_sparse());
            assert_eq!(unsafe { a.get_inline_sparse_data_unchecked() }, flag + 6);

            let b = a << u16::MAX;
            assert!(b.is_inline());
            assert!(b.is_sparse());
            assert_eq!(
                unsafe { b.get_inline_sparse_data_unchecked() },
                flag + 6 + u16::MAX as u32
            );
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

        #[test]
        fn sparse_inline() {
            let flag = u16::MAX as u32;
            let mut a = SmolBitSet::new_flag(flag);
            assert!(a.is_inline());
            assert!(a.is_sparse());

            a >>= 10u8;
            assert!(a.is_inline());
            assert!(a.is_sparse());
            assert_eq!(
                unsafe { a.get_inline_sparse_data_unchecked() },
                flag.saturating_sub(10)
            );

            let b = a >> 420u16;
            assert!(b.is_inline());
            assert!(b.is_sparse());
            assert_eq!(
                unsafe { b.get_inline_sparse_data_unchecked() },
                flag.saturating_sub(10 + 420)
            );

            let c = b >> u16::MAX;
            assert!(c.is_inline());
            assert!(!c.is_sparse());
            assert_eq!(unsafe { c.get_inline_data_unchecked() }, 0);
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
