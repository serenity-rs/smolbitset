use crate::bst_slice::BstSlice;
use crate::{BitSliceType, SmolBitSet};

use core::{cmp, iter};

impl cmp::PartialEq for SmolBitSet {
    fn eq(&self, other: &Self) -> bool {
        let this = BstSlice::new(self);
        let other = BstSlice::new(other);

        let this = this.slice();
        let other = other.slice();

        let (long, short) = if this.len() >= other.len() {
            (this, other)
        } else {
            (other, this)
        };

        let (prefix, suffix) = long.split_at(short.len());
        prefix == short && suffix.iter().all(|&x| x == 0)
    }
}

impl cmp::Eq for SmolBitSet {}

impl cmp::PartialOrd for SmolBitSet {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl cmp::Ord for SmolBitSet {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        fn inner(long: &[BitSliceType], short: &[BitSliceType]) -> cmp::Ordering {
            let (prefix, suffix) = long.split_at(short.len());
            if suffix.iter().any(|&x| x != 0) {
                return cmp::Ordering::Greater;
            }

            for (a, b) in iter::zip(prefix, short).rev() {
                let cmp = a.cmp(b);
                if cmp != cmp::Ordering::Equal {
                    return cmp;
                }
            }

            cmp::Ordering::Equal
        }

        let this = BstSlice::new(self);
        let other = BstSlice::new(other);

        let this = this.slice();
        let other = other.slice();

        if this.len() >= other.len() {
            inner(this, other)
        } else {
            inner(other, this).reverse()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eq() {
        let mut a = SmolBitSet::from(u16::MAX);
        let mut b = SmolBitSet::from(0xFFFFu16);
        assert_eq!(a, b);

        a <<= 55;
        assert_ne!(a, b);

        b <<= 55;
        assert_eq!(a, b);
    }

    #[test]
    fn ord() {
        let mut a = SmolBitSet::from(0xBEEFu16);
        let mut b = SmolBitSet::from(0x00C5_F00Du32);
        assert!(a < b);

        a <<= 72;
        assert!(a > b);
        assert!(b < a);

        b <<= 72;
        assert!(a < b);
    }

    #[test]
    fn eq_but_not_physical_same() {
        let mut a = SmolBitSet::from(u16::MAX);
        let mut b = SmolBitSet::from(0xFFFFu16);

        // ensure a is larger than b in memory
        a.spill(256);

        assert_eq!(a, b);
        assert_eq!(b, a);

        a <<= 55;
        assert_ne!(a, b);
        assert_ne!(b, a);

        b <<= 55;
        assert_eq!(a, b);
        assert_eq!(b, a);
    }

    #[test]
    fn ord_but_not_physical_same() {
        let mut a = SmolBitSet::from(0xBEEFu16);
        let mut b = SmolBitSet::from(0x00C5_F00Du32);

        // ensure a is larger than b in memory
        a.spill(256);

        assert!(a < b);
        assert!(b > a);

        a <<= 18;
        assert!(a > b);
        assert!(b < a);

        a <<= 54;
        assert!(a > b);
        assert!(b < a);

        b <<= 72;
        assert!(a < b);
        assert!(b > a);
    }
}
