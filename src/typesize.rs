use crate::{BitSliceType, SmolBitSet};

impl typesize::TypeSize for SmolBitSet {
    fn extra_size(&self) -> usize {
        const ELEM_SIZE: usize = core::mem::size_of::<BitSliceType>();

        if self.is_inline() {
            return 0;
        }

        let len = unsafe { self.len_unchecked() } + 1;
        ELEM_SIZE * len
    }
}
