use crate::{BST_BITS, BitSliceType, INLINE_SLICE_PARTS, SmolBitSet};

use core::iter;
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};

macro_rules! impl_bitop {
    ($($OP:ident :: $op:ident, $OPA:ident :: $opa:ident),+) => {$(
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

        impl_bitop!(@ref $OP :: $op, $OPA :: $opa);
    )*};
    (@ref $OP:ident :: $op:ident, $OPA:ident :: $opa:ident) => {
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
                        let rhs_iter = rhs.iter().chain(iter::repeat(&0));

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

macro_rules! impl_bitop_prim {
    ($($OP:ident :: $op:ident, $OPA:ident :: $opa:ident, $t:ty),+) => {$(
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

        impl_bitop_prim!(@ref $OP :: $op, $OPA :: $opa, $t);
    )*};
    (@ref $OP:ident :: $op:ident, $OPA:ident :: $opa:ident, $t:ty) => {
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
    };
    ($($t:ty),+) => {$(
        impl_bitop_prim!{
            BitOr::bitor, BitOrAssign::bitor_assign, $t,
            BitAnd::bitand, BitAndAssign::bitand_assign, $t,
            BitXor::bitxor, BitXorAssign::bitxor_assign, $t
        }
    )*};
}

impl_bitop_prim!(u8, u16, u32, u64, u128, usize);
