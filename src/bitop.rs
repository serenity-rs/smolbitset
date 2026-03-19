use crate::{BST_BITS, BitSliceType, INLINE_SLICE_PARTS, SmolBitSet};

use core::iter;
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

macro_rules! shortening_bitop_fn_body {
    ($lhs:ident, $rhs:ident, $opa:path) => {
        match ($lhs.is_inline(), $rhs.is_inline()) {
            (true, _) => unsafe {
                let mut lhs = $lhs.get_inline_data_unchecked();
                let rhs = $rhs.get_inlineable_start();
                $opa(&mut lhs, rhs);
                $lhs.write_inline_data_unchecked(lhs);
            },
            (false, false) => {
                let lhs = unsafe { $lhs.as_slice_mut_unchecked() };
                let rhs = unsafe { $rhs.as_slice_unchecked() };

                // in case lhs > rhs we need to have extra elements
                let rhs_iter = rhs.iter().chain(iter::repeat(&0));

                for (lhs, rhs) in lhs.iter_mut().zip(rhs_iter) {
                    $opa(lhs, *rhs);
                }
            }
            (false, true) => {
                let lhs = unsafe { $lhs.as_slice_mut_unchecked() };
                let rhs = unsafe { $rhs.get_inline_data_unchecked() };

                lhs.iter_mut().enumerate().for_each(|(idx, lhs)| {
                    $opa(
                        lhs,
                        rhs.checked_shr((idx * BST_BITS) as u32).unwrap_or(0) as BitSliceType,
                    );
                });
            }
        }
    };
}

macro_rules! extending_bitop_fn_body {
    ($lhs:ident, $rhs:ident, $opa:path) => {
        match ($lhs.is_inline(), $rhs.is_inline()) {
            (true, true) => unsafe {
                let mut lhs = $lhs.get_inline_data_unchecked();
                let rhs = $rhs.get_inline_data_unchecked();
                $opa(&mut lhs, rhs);
                $lhs.write_inline_data_unchecked(lhs);
            },
            (_, false) => {
                let rhs_hb = $rhs.highest_set_bit();
                if rhs_hb > $lhs.highest_set_bit() {
                    $lhs.ensure_capacity(rhs_hb);
                }

                let lhs = unsafe { $lhs.as_slice_mut_unchecked() };
                let rhs = unsafe { $rhs.as_slice_unchecked() };

                assert!(lhs.len() >= rhs.len());

                // in case lhs > rhs we need to have extra elements
                let rhs_iter = rhs.iter().chain(iter::repeat(&0));

                for (lhs, rhs) in lhs.iter_mut().zip(rhs_iter) {
                    $opa(lhs, *rhs);
                }
            }
            (false, true) => {
                let lhs = unsafe { $lhs.as_slice_mut_unchecked() };
                let rhs = unsafe { $rhs.get_inline_data_unchecked() };

                lhs.iter_mut()
                    .enumerate()
                    .take(INLINE_SLICE_PARTS)
                    .for_each(|(idx, lhs)| {
                        $opa(lhs, (rhs >> (idx * BST_BITS)) as BitSliceType);
                    });
            }
        }
    };
}

macro_rules! impl_bitop {
    ($($OP:ident :: $op:ident, $OPA:ident :: $opa:ident, $body_macro:path;)+) => {$(
        impl $OP<Self> for SmolBitSet {
            type Output = Self;

            #[inline]
            fn $op(self, rhs: Self) -> Self {
                let mut lhs = self;
                lhs.$opa(rhs);
                lhs
            }
        }

        impl $OPA<Self> for SmolBitSet {
            #[inline]
            fn $opa(&mut self, rhs: Self) {
                self.$opa(&rhs);
            }
        }

        impl $OP<&Self> for SmolBitSet {
            type Output = Self;

            #[inline]
            fn $op(self, rhs: &Self) -> Self {
                let mut lhs = self;
                lhs.$opa(rhs);
                lhs
            }
        }

        impl $OPA<&Self> for SmolBitSet {
            fn $opa(&mut self, rhs: &Self) {
                fn op<T>(lhs: &mut T, rhs: T)
                where
                    T: $OPA<T>
                {
                    (*lhs).$opa(rhs);
                }

                $body_macro!(self, rhs, op);
            }
        }
    )*};
}

impl_bitop! {
    BitOr::bitor, BitOrAssign::bitor_assign, extending_bitop_fn_body;
    BitAnd::bitand, BitAndAssign::bitand_assign, shortening_bitop_fn_body;
    BitXor::bitxor, BitXorAssign::bitxor_assign, extending_bitop_fn_body;
}

macro_rules! impl_bitop_prim {
    ($($OP:ident :: $op:ident, $OPA:ident :: $opa:ident, $t:ty;)+) => {$(
        impl $OP<$t> for SmolBitSet {
            type Output = Self;

            #[inline]
            fn $op(self, rhs: $t) -> Self {
                let mut lhs = self;
                lhs.$opa(rhs);
                lhs
            }
        }

        impl $OPA<$t> for SmolBitSet {
            #[inline]
            fn $opa(&mut self, rhs: $t) {
                self.$opa(Self::from(rhs))
            }
        }

        impl $OP<&$t> for SmolBitSet {
            type Output = Self;

            #[inline]
            fn $op(self, rhs: &$t) -> Self {
                self.$op(*rhs)
            }
        }

        impl $OPA<&$t> for SmolBitSet {
            #[inline]
            fn $opa(&mut self, rhs: &$t) {
                self.$opa(*rhs)
            }
        }
    )*};
    ($($t:ty),+) => {$(
        impl_bitop_prim!{
            BitOr::bitor, BitOrAssign::bitor_assign, $t;
            BitAnd::bitand, BitAndAssign::bitand_assign, $t;
            BitXor::bitxor, BitXorAssign::bitxor_assign, $t;
        }
    )*};
}

impl_bitop_prim!(u8, u16, u32, u64, u128, usize);

impl SmolBitSet {
    /// Unsets all bits set on the `rhs` [`SmolBitSet`].
    ///
    /// This is equivalent to `self & !rhs` with integers.
    #[must_use]
    pub fn and_not(mut self, rhs: &Self) -> Self {
        self.and_not_assign(rhs);
        self
    }

    /// Unsets all bits set on the `rhs` [`SmolBitSet`].
    ///
    /// This is equivalent to `*self &= !rhs` with integers.
    pub fn and_not_assign(&mut self, rhs: &Self) {
        fn op<T>(lhs: &mut T, rhs: T)
        where
            T: BitAndAssign + Not<Output = T>,
        {
            *lhs &= !rhs;
        }

        shortening_bitop_fn_body!(self, rhs, op);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bst_slice::BstSlice;

    #[cfg(not(feature = "std"))]
    use extern_alloc::vec::Vec;

    /// Helper extension trait to simplify some tests.
    trait AndNot {
        fn and_not(self, rhs: Self) -> Self;
    }

    impl AndNot for BitSliceType {
        fn and_not(self, rhs: Self) -> Self {
            self & !rhs
        }
    }

    impl AndNot for usize {
        fn and_not(self, rhs: Self) -> Self {
            self & !rhs
        }
    }

    fn to_bst_vec(sbs: &SmolBitSet) -> Vec<BitSliceType> {
        BstSlice::new(sbs).slice().to_vec()
    }

    fn zero_pad_to(mut vec: Vec<BitSliceType>, len: usize) -> Vec<BitSliceType> {
        while vec.len() < len {
            vec.push(0);
        }
        vec
    }

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

                        let res = a.$name(&b);
                        assert!(res.is_inline());

                        let d = unsafe { res.get_inline_data_unchecked() };
                        assert_eq!(d, ($a as usize).$name($b as usize));
                    }
                )*}
            }

        test_inline_binops! {
            bitor, 0xF0F0u16, 0x0F0Fu16,
            bitand, 0xFEFEu16, 0xAFFEu16,
            bitxor, 0x3A52u16, 0xAAE8u16,
            and_not, 0xFEFEu16, 0xAFFEu16
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

                        let res = a.$name(&b);
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
            bitxor, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
            and_not, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
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

                        let res1 = a.clone().$name(&b);
                        assert_eq!(
                            to_bst_vec(&res1),
                            [
                                (($a as BitSliceType).$name($b as BitSliceType)),
                                ((($a >> 32) as BitSliceType).$name(($b >> 32) as BitSliceType))
                            ]
                        );

                        let res2 = b.$name(&a);
                        assert_eq!(res2, res1);
                    }
                )*}
            }

        test_mixed_binops! {
            bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
            bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
            bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
        }

        // `a.and_not(b) != b.and_not(a)`
        #[test]
        fn and_not() {
            const A: u64 = 0x0ABC_EE00_1337_BEEFu64;
            const B: u64 = 0xF00D_BEEF_0420_BEEFu64;

            let a = SmolBitSet::from(A);
            let b = SmolBitSet::from(B);
            assert!(a.is_inline());
            assert_eq!(b.len(), 2);

            let res1 = a.and_not(&b);
            assert_eq!(
                to_bst_vec(&res1),
                [
                    ((A as BitSliceType).and_not(B as BitSliceType)),
                    (((A >> 32) as BitSliceType).and_not((B >> 32) as BitSliceType))
                ]
            );
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

                        let res = lhs.$name(&rhs);
                        assert_eq!(
                            to_bst_vec(&res),
                            [
                                ((0 as BitSliceType).$name($b as BitSliceType)),
                                ((($a) as BitSliceType).$name(($b >> 32) as BitSliceType)),
                                ((($a >> 32) as BitSliceType).$name(0 as BitSliceType))
                            ]
                        );
                    }
                )*};
            }

        test_rhs_smaller_binops! {
            bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
            bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
            bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
            and_not, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
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

                        let res = lhs.$name(&rhs);
                        assert_eq!(
                            zero_pad_to(to_bst_vec(&res), 3),
                            [
                                (($a as BitSliceType).$name(0 as BitSliceType)),
                                ((($a >> 32) as BitSliceType).$name($b as BitSliceType)),
                                ((0 as BitSliceType).$name(($b >> 32) as BitSliceType))
                            ]
                        );
                    }
                )*};
            }

        test_rhs_larger_binops! {
            bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
            bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
            bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
            and_not, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
        }
    }
}
