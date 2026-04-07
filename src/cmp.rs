use crate::bst_slice::BstSlice;
use crate::{BitSliceType, Representation, SmolBitSet};

use core::{cmp, iter};

impl cmp::PartialEq for SmolBitSet {
    fn eq(&self, other: &Self) -> bool {
        fn inner(this: &BstSlice<'_>, other: &BstSlice<'_>) -> bool {
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

        match (self.representation(), other.representation()) {
            (Representation::SparseInline, Representation::SparseInline) => {
                let this = unsafe { self.get_inline_sparse_data_unchecked() };
                let other = unsafe { other.get_inline_sparse_data_unchecked() };
                this == other
            }
            (
                Representation::SparseInline,
                Representation::NormalInline | Representation::NormalHeap,
            ) => {
                let normalized_self = self.as_normal();
                let this = BstSlice::new(&normalized_self);
                let other = BstSlice::new(other);
                inner(&this, &other)
            }
            (
                Representation::NormalInline | Representation::NormalHeap,
                Representation::SparseInline,
            ) => {
                let normalized_other = other.as_normal();
                let this = BstSlice::new(self);
                let other = BstSlice::new(&normalized_other);
                inner(&this, &other)
            }
            (
                Representation::NormalHeap | Representation::NormalInline,
                Representation::NormalHeap | Representation::NormalInline,
            ) => inner(&BstSlice::new(self), &BstSlice::new(other)),
        }
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
        fn slice_cmp(long: &[BitSliceType], short: &[BitSliceType]) -> cmp::Ordering {
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

        fn inner(this: &BstSlice<'_>, other: &BstSlice<'_>) -> cmp::Ordering {
            let this = this.slice();
            let other = other.slice();

            if this.len() >= other.len() {
                slice_cmp(this, other)
            } else {
                slice_cmp(other, this).reverse()
            }
        }

        match (self.representation(), other.representation()) {
            (Representation::SparseInline, Representation::SparseInline) => {
                let this = unsafe { self.get_inline_sparse_data_unchecked() };
                let other = unsafe { other.get_inline_sparse_data_unchecked() };
                this.cmp(&other)
            }
            (
                Representation::SparseInline,
                Representation::NormalInline | Representation::NormalHeap,
            ) => {
                let normalized_self = self.as_normal();
                let this = BstSlice::new(&normalized_self);
                let other = BstSlice::new(other);
                inner(&this, &other)
            }
            (
                Representation::NormalInline | Representation::NormalHeap,
                Representation::SparseInline,
            ) => {
                let normalized_other = other.as_normal();
                let this = BstSlice::new(self);
                let other = BstSlice::new(&normalized_other);
                inner(&this, &other)
            }
            (
                Representation::NormalHeap | Representation::NormalInline,
                Representation::NormalHeap | Representation::NormalInline,
            ) => inner(&BstSlice::new(self), &BstSlice::new(other)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod normal {
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

    mod sparse {
        use super::*;

        #[test]
        fn eq() {
            let mut a = SmolBitSet::new_flag(12345);
            let mut b = SmolBitSet::new_flag(12345);
            assert_eq!(a, b);

            a <<= 550;
            assert_ne!(a, b);

            b <<= 550;
            assert_eq!(a, b);
        }

        #[test]
        fn ord() {
            let mut a = SmolBitSet::new_flag(12345);
            let mut b = SmolBitSet::new_flag(54321);
            assert!(a < b);

            a <<= 100_000;
            assert!(a > b);
            assert!(b < a);

            b <<= 100_000;
            assert!(a < b);
        }
    }

    mod mixed {
        use super::*;

        #[test]
        fn eq() {
            let mut a = SmolBitSet::new_small(1 << 22);
            let mut b = SmolBitSet::new_flag(22);
            assert_eq!(a, b);

            a <<= 32;
            assert_ne!(a, b);

            b <<= 32;
            assert_eq!(a, b);
        }

        #[test]
        fn ord() {
            let mut a = SmolBitSet::new_small(1);
            let mut b = SmolBitSet::new_flag(22);
            assert!(a < b);

            a <<= 80;
            assert!(a > b);
            assert!(b < a);

            b <<= 80;
            assert!(a < b);
        }
    }
}
