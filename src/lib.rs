//! A library for dynamically sized bitsets with memory usage optimizations.
//!
//! The first <code>[usize::BITS] - 1</code> bits are stored without incurring any heap allocations.\
//! Any larger values dynamically allocate an appropriately sized [`u32`] slice on the heap.\
//! Furthermore [`SmolBitSet`] has a niche optimization so [`Option<SmolBitSet>`] has the same size of 1 [`usize`].
//!
//! # Example
//!
//! ```
//! use smolbitset::SmolBitSet;
//!
//! let mut sbs = SmolBitSet::new();
//!
//! sbs |= 1u32 << 5;
//! sbs >>= 5u8;
//! assert_eq!(sbs, SmolBitSet::from(1u64));
//!
//! sbs |= !1u64;
//! assert_eq!(sbs, SmolBitSet::from(u64::MAX));
//!
//! sbs <<= 64u16;
//! assert_eq!(sbs, SmolBitSet::from_bits(&(64..128).collect::<Box<[_]>>()))
//! ```
//!
//! # Minimum Supported Rust Version
//!
//! This is currently `1.89`, and is considered a breaking change to increase.
//!

#![doc(html_root_url = "https://docs.rs/smolbitset/*")]
#![allow(dead_code)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc as extern_alloc;
#[cfg(not(feature = "std"))]
use {
    core::slice,
    extern_alloc::alloc::{self, Layout, handle_alloc_error},
};

#[cfg(feature = "std")]
use {
    std::alloc::{self, Layout, handle_alloc_error},
    std::slice,
};

use core::convert::Infallible;
use core::mem::MaybeUninit;
use core::num::NonZero;
use core::ptr::NonNull;

/// Returns the index of the most significant bit set to 1 in the given data.
///
/// The least significant bit is at index 1!
macro_rules! highest_set_bit {
    ($t:ty, $val:expr) => {
        (<$t>::BITS - $val.leading_zeros()) as usize
    };
}

mod bitop;
mod bst_slice;
mod cmp;
mod fmt;
mod from;
mod hash;
mod shifts;

#[cfg(feature = "serde")]
mod serde;

#[cfg(feature = "typesize")]
mod typesize;

type BitSliceType = u32;

/// How many bits are used for other purposes in the pointer which also determines
/// the required alignment since we use the least significant bits for this header information.
/// Bit 0: inline(1) / heap(0) flag
const HEADER_SIZE: u32 = 1;
const BST_BITS: usize = BitSliceType::BITS as usize;
const INLINE_SLICE_PARTS: usize = usize::BITS as usize / BST_BITS;
const MAX_INLINE_BITS: usize = (usize::BITS - HEADER_SIZE) as usize;

/// A dynamically sized bitset with memory usage optimizations.
///
/// The first <code>[usize::BITS] - 1</code> bits are stored without incurring any heap allocations.
#[repr(transparent)]
pub struct SmolBitSet {
    ptr: NonNull<BitSliceType>,
}

impl SmolBitSet {
    /// Constructs a new, empty [`SmolBitSet`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use smolbitset::SmolBitSet;
    /// let mut sbs = SmolBitSet::new();
    /// ```
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        let ptr = NonNull::without_provenance(core::num::NonZero::<usize>::MIN);

        Self { ptr }
    }

    /// Constructs a new [`SmolBitSet`] from the provided `val` without any heap allocations.
    ///
    /// # Panics
    ///
    /// Panics if the most significant bit in `val` is 1.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smolbitset::SmolBitSet;
    /// const sbs: SmolBitSet = SmolBitSet::new_small(1234);
    /// assert_eq!(sbs, SmolBitSet::from(1234u16));
    /// ```
    #[must_use]
    pub const fn new_small(val: usize) -> Self {
        assert!(
            val.leading_zeros() >= HEADER_SIZE,
            "the highest bit in val must be 0 for a non allocating SmolBitSet"
        );

        let mut res = Self::new();
        unsafe {
            res.write_inline_data_unchecked(val);
        }

        res
    }

    /// Constructs a new [`SmolBitSet`] from the provided array of bit indices without any heap allocations.
    ///
    /// # Panics
    ///
    /// Panics if any bit index in `bits` is larger than or equal to [`usize::BITS`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use smolbitset::SmolBitSet;
    /// const sbs: SmolBitSet = SmolBitSet::from_bits_small([0, 4, 1, 6]);
    /// assert_eq!(sbs, SmolBitSet::from(0b0101_0011u8));
    /// ```
    ///
    /// ```should_panic
    /// # use smolbitset::SmolBitSet;
    /// // this panics since 63 is outside of the range
    /// // a SmolBitSet can hold without incurring a heap allocation
    /// let sbs = SmolBitSet::from_bits_small([63]);
    /// ```
    ///
    /// ```compile_fail
    /// # use smolbitset::SmolBitSet;
    /// // this fails to compile since the const evaluation
    /// // panics for the same reason as above
    /// const sbs: SmolBitSet = SmolBitSet::from_bits_small([63]);
    /// ```
    #[must_use]
    pub const fn from_bits_small<const N: usize>(bits: [usize; N]) -> Self {
        let mut res = 0;
        let mut i = 0;

        while i < N {
            let b = bits[i];
            assert!(
                b < (usize::BITS - HEADER_SIZE) as usize,
                "bit index out of range for a non allocating SmolBitSet"
            );

            res |= 1 << b;
            i += 1;
        }

        Self::new_small(res)
    }

    /// Creates a new [`SmolBitSet`] from the provided slice of bit indices.
    ///
    /// # Examples
    ///
    /// ```
    /// # use smolbitset::SmolBitSet;
    /// // bit indices can be in any order
    /// let sbs = SmolBitSet::from_bits(&[0, 6, 4, 3]);
    /// assert_eq!(sbs, SmolBitSet::from(0b0101_1001u8));
    ///
    /// let sbs = SmolBitSet::from_bits(&[63]);
    /// assert_eq!(sbs, SmolBitSet::from(1u64 << 63));
    /// ```
    #[must_use]
    pub fn from_bits(bits: &[usize]) -> Self {
        let Some(hb) = bits.iter().copied().max() else {
            return Self::new();
        };

        let mut res = Self::new();
        res.ensure_capacity(hb + 1);

        if res.is_inline() {
            let mut data = 0;

            for &bit in bits {
                data |= 1 << bit;
            }

            unsafe { res.write_inline_data_unchecked(data) }
        } else {
            let data = unsafe { res.as_slice_mut_unchecked() };

            for &bit in bits {
                let s = bit % BST_BITS;
                let b = bit / BST_BITS;
                data[b] |= 1 << s;
            }
        }

        res
    }

    #[inline]
    fn is_inline(&self) -> bool {
        self.ptr.addr().get() & 0b1 == 1
    }

    #[inline]
    unsafe fn get_inline_data_unchecked(&self) -> usize {
        self.ptr.addr().get() >> HEADER_SIZE
    }

    #[inline]
    const unsafe fn write_inline_data_unchecked(&mut self, data: usize) {
        let addr = unsafe { NonZero::new_unchecked((data << HEADER_SIZE) | 0b1) };
        self.ptr = NonNull::without_provenance(addr);
    }

    #[inline]
    fn len(&self) -> usize {
        if self.is_inline() {
            return 0;
        }

        unsafe { self.len_unchecked() }
    }

    #[inline]
    const unsafe fn len_unchecked(&self) -> usize {
        unsafe { *self.ptr.as_ptr() as usize }
    }

    #[inline]
    const unsafe fn data_ptr_unchecked(&self) -> *mut BitSliceType {
        unsafe { self.ptr.as_ptr().add(1) }
    }

    #[inline]
    fn as_slice(&self) -> &[BitSliceType] {
        if self.is_inline() {
            return &[];
        }

        unsafe { self.as_slice_unchecked() }
    }

    #[inline]
    const unsafe fn as_slice_unchecked(&self) -> &[BitSliceType] {
        unsafe { slice::from_raw_parts(self.data_ptr_unchecked(), self.len_unchecked()) }
    }

    #[inline]
    fn as_slice_mut(&mut self) -> &mut [BitSliceType] {
        if self.is_inline() {
            return &mut [];
        }

        unsafe { self.as_slice_mut_unchecked() }
    }

    #[inline]
    const unsafe fn as_slice_mut_unchecked(&mut self) -> &mut [BitSliceType] {
        unsafe { slice::from_raw_parts_mut(self.data_ptr_unchecked(), self.len_unchecked()) }
    }

    /// # Warning
    /// `highest_bit` is 1 indexed, so the least significant bit is 1, not 0!
    #[inline]
    fn spill(&mut self, highest_bit: usize) {
        if !self.is_inline() {
            return;
        }

        unsafe {
            self.do_spill(highest_bit);
        }
    }

    /// # Warning
    /// `highest_bit` is 1 indexed, so the least significant bit is 1, not 0!
    unsafe fn do_spill(&mut self, highest_bit: usize) {
        let len = highest_bit.div_ceil(BST_BITS);
        let len = core::cmp::max(len, INLINE_SLICE_PARTS);

        let layout = slice_layout(len);
        let ptr = unsafe {
            #[allow(clippy::cast_ptr_alignment)]
            alloc::alloc(layout).cast::<MaybeUninit<BitSliceType>>()
        };
        if ptr.is_null() {
            handle_alloc_error(layout)
        }

        unsafe {
            (*ptr).write(len as BitSliceType); // store the length in the first element
            let old = self.get_inline_data_unchecked();

            for i in 0..INLINE_SLICE_PARTS {
                let data = (old >> (i * BST_BITS)) as BitSliceType;
                (*ptr.add(1 + i)).write(data);
            }

            for i in INLINE_SLICE_PARTS..len {
                (*ptr.add(1 + i)).write(0);
            }
        };

        self.ptr = unsafe { NonNull::new_unchecked(ptr.cast()) };
    }

    /// # Warning
    /// `highest_bit` is 1 indexed, so the least significant bit is 1, not 0!
    #[inline]
    fn ensure_capacity(&mut self, highest_bit: usize) {
        if self.is_inline() {
            if highest_bit > (usize::BITS - HEADER_SIZE) as usize {
                unsafe { self.do_spill(highest_bit) }
            }

            return;
        }

        let len = unsafe { self.len_unchecked() };
        if highest_bit < (BST_BITS * len) {
            return;
        }

        unsafe {
            self.do_grow(len, highest_bit);
        }
    }

    /// # Warning
    /// `highest_bit` is 1 indexed, so the least significant bit is 1, not 0!
    unsafe fn do_grow(&mut self, len: usize, highest_bit: usize) {
        // we need to grow our slice allocation
        let new_len = highest_bit.div_ceil(BST_BITS);
        debug_assert!(new_len >= len);

        let layout = slice_layout(len);
        let new_layout = slice_layout(new_len);
        let new_ptr = unsafe {
            #[allow(clippy::cast_ptr_alignment)]
            alloc::realloc(self.ptr.cast::<u8>().as_ptr(), layout, new_layout.size())
                .cast::<BitSliceType>()
        };
        if new_ptr.is_null() {
            handle_alloc_error(new_layout)
        }

        unsafe {
            // initializing newly allocated memory to zero
            slice::from_raw_parts_mut(new_ptr.add(1 + len), new_len - len).fill(0);

            // update the new length in the first element
            *new_ptr = new_len as BitSliceType;
        }
        self.ptr = unsafe { NonNull::new_unchecked(new_ptr) };
    }

    /// Returns the index of the most significant bit set to 1.
    ///
    /// # Warning
    /// The least significant bit is at index 1!
    #[inline]
    fn highest_set_bit(&self) -> usize {
        if self.is_inline() {
            let data = unsafe { self.get_inline_data_unchecked() };
            return highest_set_bit!(usize, data);
        }

        let data = unsafe { self.as_slice_unchecked() };
        for (idx, &data) in data.iter().enumerate().rev() {
            let h = highest_set_bit!(BitSliceType, data);
            if h != 0 {
                return (idx * BST_BITS) + h;
            }
        }

        0
    }

    /// Gets the starting bits that could be stored inlined.
    fn get_inlineable_start(&self) -> usize {
        if self.is_inline() {
            let data = unsafe { self.get_inline_data_unchecked() };
            return data;
        }

        let data = unsafe { self.as_slice_unchecked() };
        let mut start = 0usize;
        for (idx, &chunk) in data.iter().enumerate().take(INLINE_SLICE_PARTS) {
            start |= (chunk as usize) << (idx * BST_BITS);
        }

        start & (usize::MAX >> HEADER_SIZE)
    }
}

impl Drop for SmolBitSet {
    #[inline]
    fn drop(&mut self) {
        if self.is_inline() {
            return;
        }

        unsafe {
            let layout = slice_layout(self.len_unchecked());
            alloc::dealloc(self.ptr.cast::<u8>().as_ptr(), layout);
        }
    }
}

unsafe impl Send for SmolBitSet {}
unsafe impl Sync for SmolBitSet {}

impl Default for SmolBitSet {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for SmolBitSet {
    fn clone(&self) -> Self {
        if self.is_inline() {
            return Self { ptr: self.ptr };
        }

        let src = unsafe { self.as_slice_unchecked() };
        let len = src.len();
        let layout = slice_layout(len);
        let ptr = unsafe {
            #[allow(clippy::cast_ptr_alignment)]
            alloc::alloc_zeroed(layout).cast::<BitSliceType>()
        };
        if ptr.is_null() {
            handle_alloc_error(layout)
        }

        let new_data = unsafe {
            *ptr = len as BitSliceType; // store the length in the first element
            slice::from_raw_parts_mut(ptr.add(1), len)
        };
        new_data.copy_from_slice(src);

        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        Self { ptr }
    }
}

#[inline]
fn slice_layout(len: usize) -> Layout {
    #[cold]
    #[inline(never)]
    fn layout_err() -> Infallible {
        panic!("layout error in SmolBitSet slice")
    }

    #[cold]
    #[inline(never)]
    fn overflow_err() -> Infallible {
        panic!("overflow error in SmolBitSet slice")
    }

    const BST_SIZE: usize = size_of::<BitSliceType>();
    const BST_ALIGN: usize = align_of::<BitSliceType>();
    const HEADER_ALIGN: usize = 2usize.pow(HEADER_SIZE);
    const REQUIRED_ALIGN: usize = [BST_ALIGN, HEADER_ALIGN][(BST_ALIGN < HEADER_ALIGN) as usize];
    // core::cmp::max is not const yet :/

    let len = len + 1; // +1 for the length since we store the length in the first element
    let Some(size) = BST_SIZE.checked_mul(len) else {
        #[allow(unreachable_code)]
        match overflow_err() {}
    };

    let Ok(layout) = Layout::from_size_align(size, REQUIRED_ALIGN) else {
        #[allow(unreachable_code)]
        match layout_err() {}
    };

    layout
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;

    #[cfg(not(feature = "std"))]
    use extern_alloc::string::{String, ToString};

    #[test]
    fn send() {
        fn assert_send<T: Send>() {}
        assert_send::<SmolBitSet>();
    }

    #[test]
    fn sync() {
        fn assert_sync<T: Sync>() {}
        assert_sync::<SmolBitSet>();
    }

    #[test]
    fn check_highest_set_bit() {
        let mut t: u64 = 0;
        assert_eq!(highest_set_bit!(u64, t), 0);

        t = 1;
        assert_eq!(highest_set_bit!(u64, t), 1);

        t = 1 << 3;
        assert_eq!(highest_set_bit!(u64, t), 4);

        t = 1 << 31;
        assert_eq!(highest_set_bit!(u64, t), 32);

        t = 0b10101;
        assert_eq!(highest_set_bit!(u64, t), 5);

        t = u64::MAX;
        assert_eq!(highest_set_bit!(u64, t), 64);
    }

    #[test]
    fn ensure_capacity() {
        let mut t = SmolBitSet::new();
        assert!(t.is_inline());

        t.ensure_capacity(0);
        assert!(t.is_inline());

        t.ensure_capacity(32);
        assert!(t.is_inline());

        let max_inline = (usize::BITS - HEADER_SIZE) as usize;
        t.ensure_capacity(max_inline);
        assert!(t.is_inline());

        t.ensure_capacity(max_inline + 1);
        assert!(!t.is_inline());
        assert_eq!(t.len(), 2);

        t.ensure_capacity(65);
        assert!(!t.is_inline());
        assert_eq!(t.len(), 3);

        t.ensure_capacity(32 * 40);
        assert!(!t.is_inline());
        assert_eq!(t.len(), 40);
    }

    #[test]
    fn set_get_inline() {
        let mut sbs = SmolBitSet::new();
        assert!(sbs.is_inline());

        unsafe {
            let d = sbs.get_inline_data_unchecked();
            assert_eq!(d, 0);

            sbs.write_inline_data_unchecked(0b1010);
            assert!(sbs.is_inline());

            let d = sbs.get_inline_data_unchecked();
            assert_eq!(d, 0b1010);
        }
    }

    #[test]
    fn set_get_slice() {
        let a = SmolBitSet::from(0xC5C5_BEEF_0000_1234u64);
        assert!(!a.is_inline());
        assert_eq!(a.len(), 2);

        let d1 = a.as_slice();
        assert_eq!(d1.len(), 2);
        assert_eq!(d1, [0x_0000_1234, 0xC5C5_BEEF]);

        let mut b = a.clone();
        let d2 = b.as_slice_mut();
        assert_eq!(d2.len(), 2);
        assert_eq!(d2, d1);

        d2[0] = 0xDEAD_BEEF;
        d2[1] = 0xC0FF_EE00;

        let d3 = b.as_slice();
        assert_eq!(d3.len(), 2);
        assert_eq!(d3, [0xDEAD_BEEF, 0xC0FF_EE00]);
    }

    #[test]
    fn spill() {
        let mut sbs = SmolBitSet::new();
        assert!(sbs.is_inline());

        sbs.spill(30);
        assert!(!sbs.is_inline());
        // expecting 2 since the inline data can hold 63 bits already
        // and spill will always allocate to at least store the inline data
        assert_eq!(sbs.len(), 2);

        let mut sbs = SmolBitSet::new();
        assert!(sbs.is_inline());

        sbs.spill(55);
        assert!(!sbs.is_inline());
        assert_eq!(sbs.len(), 2);

        let mut sbs = SmolBitSet::new();
        assert!(sbs.is_inline());

        sbs.spill(64);
        assert!(!sbs.is_inline());
        assert_eq!(sbs.len(), 2);

        let mut sbs = SmolBitSet::new();
        assert!(sbs.is_inline());

        sbs.spill(65);
        assert!(!sbs.is_inline());
        assert_eq!(sbs.len(), 3);
    }

    #[test]
    fn deserialize() {
        let sbs = SmolBitSet::try_from(String::from("1337")).unwrap();
        assert!(sbs.is_inline());
        assert_eq!(unsafe { sbs.get_inline_data_unchecked() }, 1337);

        // A5A5 1337 0000 C0FF EE00 BEEF 0000 A5A5
        let sbs =
            SmolBitSet::try_from(String::from("220179738009501684669546686565819917733")).unwrap();
        assert!(!sbs.is_inline());
        assert_eq!(
            sbs.as_slice(),
            [0x0000_A5A5, 0xEE00_BEEF, 0x0000_C0FF, 0xA5A5_1337]
        );
    }

    #[test]
    fn serialize() {
        let sbs = SmolBitSet::from(1337u32);
        assert_eq!(sbs.to_string(), "1337");

        // A5A5 1337 0000 C0FF EE00 BEEF 0000 A5A5
        let mut sbs = SmolBitSet::from(0xA5A5_1337_0000_C0FFu64);
        sbs <<= 64u8;
        sbs |= 0xEE00_BEEF_0000_A5A5u64;
        assert_eq!(sbs.to_string(), "220179738009501684669546686565819917733");
    }

    mod clone {
        use super::*;

        #[test]
        fn inline() {
            let val = 0xC0FE_FE00u32;
            let a = SmolBitSet::from(val);
            #[allow(clippy::redundant_clone)]
            let b = a.clone();

            assert!(a.is_inline());
            assert!(b.is_inline());

            let a_data = unsafe { a.get_inline_data_unchecked() };
            let b_data = unsafe { b.get_inline_data_unchecked() };
            assert_eq!(a_data, b_data);
        }

        #[test]
        fn slice() {
            let val = 0xFFEE_00AA_1337_0420u64;
            let a = SmolBitSet::from(val);
            #[allow(clippy::redundant_clone)]
            let b = a.clone();

            assert!(!a.is_inline());
            assert!(!b.is_inline());

            let a_data = a.as_slice();
            let b_data = b.as_slice();
            assert_eq!(a_data.len(), b_data.len());
            assert_eq!(a_data, b_data);
            assert_eq!(a_data, [0x1337_0420, 0xFFEE_00AA]);
        }
    }
}
