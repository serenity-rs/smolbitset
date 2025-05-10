use crate::{BST_BITS, SmolBitSet};

use core::ops::{Shl, ShlAssign, Shr, ShrAssign};

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
