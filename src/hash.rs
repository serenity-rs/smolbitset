use crate::{BST_BITS, SmolBitSet};

#[cfg(not(feature = "std"))]
use core::hash;
#[cfg(feature = "std")]
use std::hash;

impl hash::Hash for SmolBitSet {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        if self.is_inline() {
            unsafe { self.get_inline_data_unchecked() }.hash(state);
            return;
        }

        let hb = self.highest_set_bit();
        let data = unsafe { self.as_slice_unchecked() };
        for d in data.iter().take(hb.div_ceil(BST_BITS)) {
            d.hash(state);
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;

    #[test]
    #[cfg(feature = "std")]
    fn hash() {
        // core does not have a default hasher
        use hash::{DefaultHasher, Hash, Hasher};

        let a = SmolBitSet::from(0xC5C5_F00Du32);
        let b = SmolBitSet::from(0xC5C5_F00Du32);
        let mut hasher_a = DefaultHasher::new();
        let mut hasher_b = DefaultHasher::new();
        a.hash(&mut hasher_a);
        b.hash(&mut hasher_b);
        assert_eq!(hasher_a.finish(), hasher_b.finish());

        let mut a = SmolBitSet::from(0xFFC5_C0FF_EE00_BEEF_u64);
        let mut b = SmolBitSet::from(0xFFC5_C0FF_EE00_BEEF_u64);
        a <<= 128u8;
        a >>= 66u8;
        b <<= 128u8 - 66u8;
        let mut hasher_a = DefaultHasher::new();
        let mut hasher_b = DefaultHasher::new();
        a.hash(&mut hasher_a);
        b.hash(&mut hasher_b);
        assert_eq!(hasher_a.finish(), hasher_b.finish());
    }
}
