use crate::bst_slice::BstSlice;
use crate::{BST_BITS, BitSliceType, INLINE_SLICE_PARTS, Representation, SmolBitSet};

use core::iter;
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

macro_rules! shortening_bitop_fn_body {
    ($lhs:ident, $rhs:ident, $opa:path, $sparse_cond:path, $self_op:ident) => {
        match ($lhs.representation(), $rhs.representation()) {
            (Representation::SparseInline, Representation::SparseInline) => unsafe {
                let lhs_flag = $lhs.get_inline_sparse_data_unchecked();
                let rhs_flag = $rhs.get_inline_sparse_data_unchecked();

                if $sparse_cond(lhs_flag, rhs_flag) {
                    // result is still sparse and lhs already has the correct flag set
                } else {
                    // result is an empty set
                    *$lhs = Self::new();
                }
            },
            (
                Representation::SparseInline,
                Representation::NormalInline | Representation::NormalHeap,
            ) => {
                let lhs_flag = unsafe { $lhs.get_inline_sparse_data_unchecked() };
                let target_elem = lhs_flag / BST_BITS as u32;
                let target_shift = lhs_flag.rem_euclid(BST_BITS as u32);

                let rhs_bst = BstSlice::new($rhs);
                let rhs_slice = rhs_bst.slice();
                let rhs_elem = rhs_slice.iter().nth(target_elem as usize).unwrap_or(&0);
                let rhs_flag = ((rhs_elem >> target_shift) & 1) as u32 * lhs_flag;

                if $sparse_cond(lhs_flag, rhs_flag) {
                    // result is still sparse and lhs already has the correct flag set
                } else {
                    // result is an empty set
                    *$lhs = Self::new();
                }
            }
            (
                Representation::NormalInline | Representation::NormalHeap,
                Representation::SparseInline,
            ) => {
                let rhs_flag = unsafe { $rhs.get_inline_sparse_data_unchecked() };
                let target_elem = rhs_flag / BST_BITS as u32;
                let target_shift = rhs_flag.rem_euclid(BST_BITS as u32);

                let lhs_bst = BstSlice::new($lhs);
                let lhs_slice = lhs_bst.slice();
                let lhs_elem = lhs_slice.iter().nth(target_elem as usize).unwrap_or(&0);
                let lhs_flag = ((lhs_elem >> target_shift) & 1) as u32 * rhs_flag;

                // TODO: clean up the duplication & possibly simplify conditions
                if $sparse_cond(lhs_flag, rhs_flag) {
                    if lhs_flag == rhs_flag {
                        // result is sparse and lhs needs to be updated
                        *$lhs = Self::new_flag(rhs_flag);
                    } else {
                        // result is not sparse, rhs_flag bit needs to be unset in lhs
                        $lhs.and_not_assign(&(Self::new_small(1) << rhs_flag));
                    }
                } else {
                    if lhs_flag != rhs_flag {
                        // result is an empty set
                        *$lhs = Self::new();
                    } else {
                        // result is not sparse, rhs_flag bit needs to be unsed in lhs
                        $lhs.and_not_assign(&(Self::new_small(1) << rhs_flag));
                    }
                }
            }
            (
                Representation::NormalInline,
                Representation::NormalInline | Representation::NormalHeap,
            ) => unsafe {
                let mut lhs = $lhs.get_inline_data_unchecked();
                let rhs = $rhs.get_inlineable_start();
                $opa(&mut lhs, rhs);
                $lhs.write_inline_data_unchecked(lhs);
            },
            (Representation::NormalHeap, Representation::NormalHeap) => {
                let lhs = unsafe { $lhs.as_slice_mut_unchecked() };
                let rhs = unsafe { $rhs.as_slice_unchecked() };

                // in case lhs > rhs we need to have extra elements
                let rhs_iter = rhs.iter().chain(iter::repeat(&0));

                for (lhs, rhs) in lhs.iter_mut().zip(rhs_iter) {
                    $opa(lhs, *rhs);
                }
            }
            (Representation::NormalHeap, Representation::NormalInline) => {
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
    ($lhs:ident, $rhs:ident, $opa:path, $sparse_cond:path, $self_op:ident) => {
        match ($lhs.representation(), $rhs.representation()) {
            (Representation::SparseInline, Representation::SparseInline) => unsafe {
                let lhs_flag = $lhs.get_inline_sparse_data_unchecked();
                let rhs_flag = $rhs.get_inline_sparse_data_unchecked();

                if $sparse_cond(lhs_flag, rhs_flag) {
                    if lhs_flag == rhs_flag {
                        // result is still sparse and lhs is already correct
                    } else {
                        // result is not sparse, must contain both flags
                        let mut res = $lhs.as_normal();
                        $opa(&mut res, $rhs.as_normal());
                        *$lhs = res;
                    }
                } else {
                    // result is an empty set
                    *$lhs = Self::new();
                }
            },
            (
                Representation::SparseInline,
                Representation::NormalInline | Representation::NormalHeap,
            ) => {
                let mut lhs_normalized = $lhs.as_normal();
                Self::$self_op(&mut lhs_normalized, $rhs);
                *$lhs = lhs_normalized;
            }
            (
                Representation::NormalInline | Representation::NormalHeap,
                Representation::SparseInline,
            ) => {
                Self::$self_op($lhs, $rhs.as_normal());
            }
            (Representation::NormalInline, Representation::NormalInline) => unsafe {
                let mut lhs = $lhs.get_inline_data_unchecked();
                let rhs = $rhs.get_inline_data_unchecked();
                $opa(&mut lhs, rhs);
                $lhs.write_inline_data_unchecked(lhs);
            },
            (
                Representation::NormalInline | Representation::NormalHeap,
                Representation::NormalHeap,
            ) => {
                let rhs_hb = $rhs.highest_set_bit();
                if rhs_hb > $lhs.highest_set_bit() {
                    $lhs.ensure_capacity(rhs_hb);
                }

                let lhs = unsafe { $lhs.as_slice_mut_unchecked() };
                let rhs = unsafe { $rhs.as_slice_unchecked() };

                // in case lhs > rhs we need to have extra elements
                let rhs_iter = rhs.iter().chain(iter::repeat(&0));

                for (lhs, rhs) in lhs.iter_mut().zip(rhs_iter) {
                    $opa(lhs, *rhs);
                }
            }
            (Representation::NormalHeap, Representation::NormalInline) => {
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
    ($($OP:ident :: $op:ident, $OPA:ident :: $opa:ident, $sparse_comp_closure:expr, $body_macro:path;)+) => {$(
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

                fn sparse_cond(lhs: u32, rhs: u32) -> bool {
                    $sparse_comp_closure(lhs, rhs)
                }

                $body_macro!(self, rhs, op, sparse_cond, $opa);
            }
        }
    )*};
}

impl_bitop! {
    BitOr::bitor, BitOrAssign::bitor_assign, |_, _| true, extending_bitop_fn_body;
    BitAnd::bitand, BitAndAssign::bitand_assign, |lhs, rhs| lhs == rhs, shortening_bitop_fn_body;
    BitXor::bitxor, BitXorAssign::bitxor_assign, |lhs, rhs| lhs != rhs, extending_bitop_fn_body;
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

        const fn sparse_cond(lhs_flag: u32, rhs_flag: u32) -> bool {
            lhs_flag != rhs_flag
        }

        shortening_bitop_fn_body!(self, rhs, op, sparse_cond, and_not_assign);
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

    mod normal {
        use super::*;

        mod inline {
            use super::*;

            macro_rules! test_inline_bitops {
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

            test_inline_bitops! {
                bitor, 0xF0F0u16, 0x0F0Fu16,
                bitand, 0xFEFEu16, 0xAFFEu16,
                bitxor, 0x3A52u16, 0xAAE8u16,
                and_not, 0xFEFEu16, 0xAFFEu16
            }
        }

        mod slice {
            use super::*;

            macro_rules! test_slice_bitops {
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

            test_slice_bitops! {
                bitor, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                and_not, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }

        mod mixed {
            use super::*;

            macro_rules! test_mixed_bitops {
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

            test_mixed_bitops! {
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

            macro_rules! test_rhs_smaller_bitops {
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

            test_rhs_smaller_bitops! {
                bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                and_not, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }

        mod rhs_larger {
            use super::*;

            macro_rules! test_rhs_larger_bitops {
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

            test_rhs_larger_bitops! {
                bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                and_not, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }
    }

    mod sparse {
        use super::*;

        mod inline {
            use super::*;

            macro_rules! test_sparse_inline_bitops {
                ($($name:ident, $op:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let a = SmolBitSet::new_flag($a);
                        let b = SmolBitSet::new_flag($b);
                        assert!(a.is_inline());
                        assert!(b.is_inline());
                        assert!(a.is_sparse());
                        assert!(b.is_sparse());

                        let res = a.$op(&b);
                        assert!(res.is_inline());

                        let normal_res = (1usize << $a as usize).$op(1usize << $b as usize);
                        if res.is_sparse() {
                            let res_flag = unsafe { res.get_inline_sparse_data_unchecked() };
                            assert_eq!(res_flag, normal_res.trailing_zeros());
                        } else {
                            let d = unsafe { res.get_inline_data_unchecked() };
                            assert_eq!(d, normal_res);
                        }
                    }
                )*}
            }

            test_sparse_inline_bitops! {
                bitor_eq, bitor, 10, 10,
                bitor_ne, bitor, 14, 18,

                bitand_eq, bitand, 22, 22,
                bitand_ne, bitand, 12, 22,

                bitxor_eq, bitxor, 5, 5,
                bitxor_ne, bitxor, 7, 24,

                and_not_eq, and_not, 13, 13,
                and_not_ne, and_not, 17, 19
            }
        }
    }

    mod mixed {
        use super::*;

        mod inline {
            use super::*;

            macro_rules! test_mixed_inline_bitops {
                ($($name:ident, $op:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        fn inner(a: SmolBitSet, b: SmolBitSet, a_u: usize, b_u: usize) {
                            let res = a.$op(&b);
                            assert!(res.is_inline());

                            let normal_res = a_u.$op(b_u);

                            if res.is_sparse() {
                                let res_flag = unsafe { res.get_inline_sparse_data_unchecked() };
                                assert_eq!(normal_res.count_ones(), 1);
                                assert_eq!(res_flag, normal_res.trailing_zeros());
                            } else {
                                let d = unsafe { res.get_inline_data_unchecked() };
                                assert_eq!(d, normal_res);
                            }
                        }

                        let a = SmolBitSet::new_flag($a);
                        let b = SmolBitSet::from($b);
                        assert!(a.is_inline());
                        assert!(a.is_sparse());
                        assert!(b.is_inline());
                        assert!(!b.is_sparse());

                        let a_u = 1usize << $a as usize;
                        let b_u = $b as usize;

                        inner(a.clone(), b.clone(), a_u, b_u);
                        inner(b, a, b_u, a_u);
                    }
                )*}
            }

            test_mixed_inline_bitops! {
                bitor_eq, bitor, 10, 0xBEEFu16,
                bitor_ne, bitor, 10, 0xF00Du16,

                bitand_eq, bitand, 10, 0xBEEFu16,
                bitand_ne, bitand, 10, 0xF00Du16,

                bitxor_eq, bitxor, 10, 0xBEEFu16,
                bitxor_ne, bitxor, 10, 0xF00Du16,

                and_not_eq, and_not, 10, 0xBEEFu16,
                and_not_ne, and_not, 10, 0xF00Du16
            }
        }

        mod sparse_inline_normal_heap {
            use super::*;

            macro_rules! test_mixed_sparse_inline_normal_heap_bitops {
                ($($name:ident, $op:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        fn inner(a: SmolBitSet, b: SmolBitSet, a_u: usize, b_u: usize, shift: usize) {
                            let res = a.$op(&b);

                            let normal_res = a_u.$op(b_u);
                            let shifted_res = SmolBitSet::from(normal_res) << shift;
                            assert_eq!(res, shifted_res);
                        }

                        let shift = 120;
                        let a: SmolBitSet = SmolBitSet::new_flag($a) << shift;
                        let b: SmolBitSet = SmolBitSet::from($b) << shift;
                        assert!(a.is_inline());
                        assert!(a.is_sparse());
                        assert!(!b.is_inline());
                        assert!(!b.is_sparse());

                        let a_u = 1usize << $a as usize;
                        let b_u = $b as usize;

                        inner(a.clone(), b.clone(), a_u, b_u, shift);
                        inner(b, a, b_u, a_u, shift);
                    }
                )*}
            }

            test_mixed_sparse_inline_normal_heap_bitops! {
                bitor_eq, bitor, 10, 0xBEEFu16,
                bitor_ne, bitor, 10, 0xF00Du16,

                bitand_eq, bitand, 10, 0xBEEFu16,
                bitand_ne, bitand, 10, 0xF00Du16,

                bitxor_eq, bitxor, 10, 0xBEEFu16,
                bitxor_ne, bitxor, 10, 0xF00Du16,

                and_not_eq, and_not, 10, 0xBEEFu16,
                and_not_ne, and_not, 10, 0xF00Du16
            }
        }
    }
}
