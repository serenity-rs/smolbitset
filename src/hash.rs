use crate::{BST_BITS, MAX_INLINE_BITS, SmolBitSet};

#[cfg(not(feature = "std"))]
use core::hash;
#[cfg(feature = "std")]
use std::hash;

impl hash::Hash for SmolBitSet {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        if self.is_sparse() {
            self.as_normal().hash(state);
            return;
        }

        if self.is_inline() {
            unsafe { self.get_inline_data_unchecked() }.hash(state);
            return;
        }

        let hb = self.highest_set_bit();
        let data = unsafe { self.as_slice_unchecked() };

        if hb <= MAX_INLINE_BITS {
            #[cfg(target_pointer_width = "32")]
            let val = data[0] as usize;
            #[cfg(target_pointer_width = "64")]
            let val = (data[1] as usize) << 32 | data[0] as usize;

            val.hash(state);
        } else {
            for d in data.iter().take(hb.div_ceil(BST_BITS)) {
                d.hash(state);
            }
        }
    }
}

// core does not have a default hasher
#[cfg(all(test, feature = "std"))]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;

    fn hash_helper(a: &SmolBitSet) -> u64 {
        use hash::{DefaultHasher, Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        a.hash(&mut hasher);
        hasher.finish()
    }

    fn assert_hash_eq(a: &SmolBitSet, b: &SmolBitSet) {
        assert_eq!(hash_helper(a), hash_helper(b));
    }

    fn assert_hash_ne(a: &SmolBitSet, b: &SmolBitSet) {
        assert_ne!(hash_helper(a), hash_helper(b));
    }

    #[test]
    fn normal_inline() {
        let val = 0xC5C5_F00D;
        let mut a = SmolBitSet::new_small(val);
        let mut b = SmolBitSet::new_small(val);
        assert_hash_eq(&a, &b);

        a >>= 1u8;
        b >>= 4u8;
        assert_hash_ne(&a, &b);

        a >>= 3u8;
        assert_hash_eq(&a, &b);
    }

    #[test]
    fn sparse_inline() {
        let flag = 1337;
        let mut a = SmolBitSet::new_flag(flag);
        let mut b = SmolBitSet::new_flag(flag);
        assert_hash_eq(&a, &b);

        a <<= 42u8;
        b <<= 66u8;
        assert_hash_ne(&a, &b);

        a <<= 24u8;
        assert_hash_eq(&a, &b);
    }

    #[test]
    fn mixed_inline() {
        let mut a = SmolBitSet::new_small(1 << 15);
        let mut b = SmolBitSet::new_flag(15);
        assert_hash_eq(&a, &b);

        b <<= 420u16;
        a >>= 5u8;
        assert_hash_ne(&a, &b);

        b >>= 425u16;
        assert_hash_eq(&a, &b);
    }

    #[test]
    fn normal_heap() {
        let val = 0xFFC5_C0FF_EE00_BEEF_u64;
        let mut a = SmolBitSet::from(val);
        let mut b = SmolBitSet::from(val);
        assert!(!a.is_inline());
        assert!(!b.is_inline());
        assert_hash_eq(&a, &b);

        a <<= 128u8;
        a >>= 66u8;
        assert_hash_ne(&a, &b);

        b <<= 128u8 - 66u8;
        assert_hash_eq(&a, &b);
    }

    #[test]
    fn normal_mixed() {
        let val = 0xBEEF_F00D;
        let mut a = SmolBitSet::new_small(val);
        let mut b = SmolBitSet::new_small(val);
        b.spill(70);
        assert!(a.is_inline());
        assert!(!b.is_inline());
        assert_hash_eq(&a, &b);

        a >>= 5u8;
        assert_hash_ne(&a, &b);

        b >>= 5u8;
        assert_hash_eq(&a, &b);
    }
}
