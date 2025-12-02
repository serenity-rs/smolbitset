use crate::bst_slice::BstSlice;
use crate::{BST_BITS, SmolBitSet};

#[cfg(feature = "std")]
use std::fmt;

#[cfg(not(feature = "std"))]
use core::fmt;

use fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, Result, UpperHex};

impl Debug for SmolBitSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_list().entries(BstSlice::new(self).slice()).finish()
    }
}

impl Display for SmolBitSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.is_inline() {
            return write!(f, "{}", unsafe { self.get_inline_data_unchecked() });
        }

        let tmp = num_bigint::BigUint::from_slice(unsafe { self.as_slice_unchecked() });
        write!(f, "{tmp}")
    }
}

macro_rules! impl_format {
    ($($kind:ident $format:literal $variants:literal),+) => {$(
        impl $kind for SmolBitSet {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result {
                if self.is_inline() {
                    return $kind::fmt(&unsafe { self.get_inline_data_unchecked() }, f);
                }

                let data = unsafe { self.as_slice_unchecked() };
                let highest = self.highest_set_bit().saturating_sub(1).div_ceil(BST_BITS);

                let mut full_width = false;
                for idx in (0..highest).rev() {
                    const PADDING: usize = BST_BITS / ($variants as u8).ilog2() as usize;

                    let d = data[idx];

                    if full_width {
                        write!(f, concat!("{d:0PADDING$", $format, "}"), d = d, PADDING = PADDING)?;
                    } else {
                        full_width = true;
                        $kind::fmt(&d, f)?;
                    }
                }

                Ok(())
            }
        }
    )*};
}

impl_format!(
    Binary 'b' 2,
    Octal 'o' 8,
    LowerHex 'x' 16,
    UpperHex 'X' 16
);
