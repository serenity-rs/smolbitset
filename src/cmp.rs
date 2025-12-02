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
