use crate::{BST_BITS, BitSliceType, SmolBitSet};

use core::str::FromStr;

#[cfg(not(feature = "std"))]
use extern_alloc::string::String;

macro_rules! impl_from {
    ($($t:ty),+) => {$(
        impl From<$t> for SmolBitSet {
            fn from(value: $t) -> Self {
                let mut sbs = SmolBitSet::new();
                sbs.ensure_capacity(highest_set_bit!($t, value));

                if sbs.is_inline() {
                    unsafe { sbs.write_inline_data_unchecked(value as usize) };
                } else {
                    const T_BITS: usize = <$t>::BITS as usize;
                    const STEPS: usize = T_BITS.div_ceil(BST_BITS);

                    let data = unsafe { sbs.as_slice_mut_unchecked() };

                    for i in 0..STEPS {
                        data[i] = (value >> (i * BST_BITS)) as BitSliceType;
                    }
                }

                sbs
            }
        }

        impl_from!(@ref $t);
    )*};
    (@ref $t:ty) => {
        impl From<&$t> for SmolBitSet {
            #[inline]
            fn from(value: &$t) -> Self {
                Self::from(*value)
            }
        }
    }
}

impl_from!(u8, u16, u32, u64, u128, usize);

impl TryFrom<String> for SmolBitSet {
    type Error = ();

    #[inline]
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
                        (digits[0] as usize) | ((digits[1] as usize) << BST_BITS),
                    );
                },
                _ => unreachable!("Too many digits for inline data"),
            }
        } else {
            assert!(sbs.len() >= digit_count);

            let data = unsafe { sbs.as_slice_mut_unchecked() };
            data[0..digit_count].copy_from_slice(&digits);
        }

        Ok(sbs)
    }
}
