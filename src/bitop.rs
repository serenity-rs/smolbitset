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
