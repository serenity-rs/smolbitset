use crate::SmolBitSet;

use core::cmp;

impl cmp::PartialEq for SmolBitSet {
    fn eq(&self, other: &Self) -> bool {
        match (self.len(), other.len()) {
            (0, 0) => unsafe {
                self.get_inline_data_unchecked() == other.get_inline_data_unchecked()
            },
            (a, b) if a == b => {
                let a = unsafe { self.as_slice_unchecked() };
                let b = unsafe { other.as_slice_unchecked() };

                a == b
            }
            _ => false,
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
        match (self.len(), other.len()) {
            (0, 0) => unsafe {
                self.get_inline_data_unchecked()
                    .cmp(&other.get_inline_data_unchecked())
            },
            (0, _) => cmp::Ordering::Less,
            (_, 0) => cmp::Ordering::Greater,
            (a, b) if a == b => unsafe {
                let a = self.as_slice_unchecked();
                let b = other.as_slice_unchecked();

                for (a, b) in a.iter().zip(b.iter()).rev() {
                    let cmp = a.cmp(b);
                    if cmp != cmp::Ordering::Equal {
                        return cmp;
                    }
                }

                cmp::Ordering::Equal
            },
            (a, b) => a.cmp(&b),
        }
    }
}
