#[cfg(target_pointer_width = "64")]
use crate::BST_BITS;
use crate::{BitSliceType, INLINE_SLICE_PARTS, SmolBitSet};

pub enum BstSlice<'a> {
    Inline([BitSliceType; INLINE_SLICE_PARTS]),
    Heap(&'a [BitSliceType]),
}

impl<'a> BstSlice<'a> {
    pub fn new(sbs: &'a SmolBitSet) -> Self {
        if sbs.is_inline() {
            let data = unsafe { sbs.get_inline_data_unchecked() };
            #[cfg(target_pointer_width = "32")]
            let data = [data as BitSliceType];
            #[cfg(target_pointer_width = "64")]
            let data = [(data as BitSliceType), ((data >> BST_BITS) as BitSliceType)];

            Self::Inline(data)
        } else {
            let slice = unsafe { sbs.as_slice_unchecked() };

            Self::Heap(slice)
        }
    }

    pub const fn slice(&self) -> &[BitSliceType] {
        match self {
            Self::Inline(items) => items,
            Self::Heap(items) => items,
        }
    }
}
