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

#[cfg(test)]
mod tests {
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
        u64, 0x3550_1337_0000_F00Fu64
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
