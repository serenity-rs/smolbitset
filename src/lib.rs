//! A library for dynamically sized bitsets with small storage optimization.
//!
//! All values up to `usize::MAX >> 1` are stored without incurring any heap allocations.\
//! Any larger values dynamically allocate an appropriately sized `u32` slice on the heap.\
//! [`SmolBitSet`] also has a niche optimization so [`Option<SmolBitSet>`] and [`SmolBitSet`] have the same size of 1 [`usize`].

#![doc(html_root_url = "https://docs.rs/smolbitset/*")]
#![allow(dead_code)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc as extern_alloc;
#[cfg(not(feature = "std"))]
use {
    core::hash,
    core::slice,
    extern_alloc::alloc::{self, Layout, handle_alloc_error},
};

#[cfg(feature = "std")]
use {
    std::alloc::{self, Layout, handle_alloc_error},
    std::hash,
    std::slice,
};

use core::convert::Infallible;
use core::mem::MaybeUninit;
use core::ptr::{self, NonNull};

/// Returns the index of the most significant bit set to 1 in the given data.
///
/// The least significant bit is at index 1!
macro_rules! highest_set_bit {
    ($t:ty, $val:expr) => {
        (<$t>::BITS - $val.leading_zeros()) as usize
    };
}

mod bitop;
mod cmp;
mod fmt;
mod from;
mod shifts;

#[cfg(feature = "serde")]
mod serde;

type BitSliceType = u32;
const BST_BITS: usize = BitSliceType::BITS as usize;
const INLINE_SLICE_PARTS: usize = usize::BITS as usize / BST_BITS;

#[repr(transparent)]
pub struct SmolBitSet {
    ptr: NonNull<BitSliceType>,
}

impl SmolBitSet {
    /// Creates a new empty [`SmolBitSet`].
    ///
    /// # Examples
    ///
    /// ```
    /// use smolbitset::SmolBitSet;
    ///
    /// # #[allow(unused_mut)]
    /// let mut sbs = SmolBitSet::new();
    /// ```
    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        let ptr = unsafe { NonNull::new_unchecked(ptr::without_provenance_mut(0b1)) };

        // #![feature(nonnull_provenance)] -> https://github.com/rust-lang/rust/issues/135243
        // let ptr = NonNull::without_provenance(core::num::NonZero::<usize>::MIN);

        Self { ptr }
    }

    /// Creates a new [`SmolBitSet`] from the provided `val` without any heap allocation.
    ///
    /// # Panics
    ///
    /// Panics if the most significant bit in `val` is set to 1.
    ///
    /// # Examples
    ///
    /// ```
    /// use smolbitset::SmolBitSet;
    ///
    /// const sbs: SmolBitSet = SmolBitSet::new_small(1234);
    /// assert_eq!(sbs, SmolBitSet::from(1234u16));
    /// ```
    #[must_use]
    pub const fn new_small(val: usize) -> Self {
        assert!(val.leading_zeros() >= 1, "the highest bit in val must be 0");

        let mut res = Self::new();
        unsafe {
            res.write_inline_data_unchecked(val);
        }

        res
    }

    /// Creates a new [`SmolBitSet`] from the provided slice of `bits`.
    ///
    /// # Examples
    ///
    /// ```
    /// use smolbitset::SmolBitSet;
    ///
    /// let sbs = SmolBitSet::from_bits(&[0, 4, 3, 6]);
    /// assert_eq!(sbs, SmolBitSet::from(0b0101_1001u8));
    /// # let sbs = SmolBitSet::from_bits(&[63]);
    /// # assert_eq!(sbs, SmolBitSet::from(1u64 << 63));
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
        self.ptr.addr().get() >> 1
    }

    #[inline]
    const unsafe fn write_inline_data_unchecked(&mut self, data: usize) {
        self.ptr =
            unsafe { NonNull::new_unchecked(ptr::without_provenance_mut((data << 1) | 0b1)) };
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

        let layout = slice_layout::<BitSliceType>(len);
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
            if highest_bit >= (usize::BITS as usize) {
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

        let layout = slice_layout::<BitSliceType>(len);
        let new_layout = slice_layout::<BitSliceType>(new_len);
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
}

impl Drop for SmolBitSet {
    #[inline]
    fn drop(&mut self) {
        if self.is_inline() {
            return;
        }

        unsafe {
            let layout = slice_layout::<BitSliceType>(self.len_unchecked());
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
        let layout = slice_layout::<BitSliceType>(len);
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
fn slice_layout<T>(len: usize) -> Layout {
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

    let len = len + 1; // +1 for the length since we store the length in the first element
    let single = Layout::new::<T>().pad_to_align();
    let Some(size) = single.size().checked_mul(len) else {
        #[allow(unreachable_code)]
        match overflow_err() {}
    };

    let Ok(layout) = Layout::from_size_align(size, single.align()) else {
        #[allow(unreachable_code)]
        match layout_err() {}
    };

    layout
}

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

#[cfg(feature = "typesize")]
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

        t.ensure_capacity(63);
        assert!(t.is_inline());

        t.ensure_capacity(64);
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

    mod from {
        use super::*;

        macro_rules! test_from {
            ($($name:ident, $val:expr),+) => {$(
                #[test]
                fn $name() {
                    let t = SmolBitSet::from($val);
                    assert!(t.is_inline());

                    let d = unsafe { t.get_inline_data_unchecked() };
                    assert_eq!(d, $val as usize);
                }
            )*}
        }

        test_from! {
            u8, 0b1110_1010u8,
            u8_max, u8::MAX,
            u16, 0xBEAFu16,
            u16_max, u16::MAX,
            u32, 0xF0BA_B0BBu32,
            u32_max, u32::MAX,
            u64, 0x7550_1337_0000_F00Fu64
        }

        #[test]
        fn u64_hb_64() {
            let t = SmolBitSet::from(0xC5C5_BEEF_0000_1234u64);
            assert!(!t.is_inline());
            assert_eq!(t.len(), 2);

            let d = t.as_slice();
            assert_eq!(d.len(), 2);
            assert_eq!(d, [0x0000_1234, 0xC5C5_BEEF]);
        }

        #[test]
        fn u64_max() {
            let t = SmolBitSet::from(u64::MAX);
            assert_eq!(t.len(), 2);

            let d = t.as_slice();
            assert_eq!(d.len(), 2);
            assert_eq!(d, &[u32::MAX; 2]);
        }
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

    mod shifts {
        use super::*;

        mod shl {
            use super::*;

            #[test]
            fn inline() {
                let val = 0xABCD_0042u32;
                let mut a = SmolBitSet::from(val);
                assert!(a.is_inline());

                a <<= 6u8;
                assert!(a.is_inline());
                assert_eq!(
                    unsafe { a.get_inline_data_unchecked() },
                    (val as usize) << 6
                );

                let b = a << 4u8;
                assert!(b.is_inline());
                assert_eq!(
                    unsafe { b.get_inline_data_unchecked() },
                    (val as usize) << (6 + 4)
                );
            }

            #[test]
            fn grow_to_slice() {
                let val = 0x00AB_CD55_1337_BEEFu64;
                let mut a = SmolBitSet::from(val);
                assert!(a.is_inline());

                a <<= 8u8;
                assert_eq!(a.len(), 2);
                assert_eq!(a.as_slice(), [0x37BE_EF00u32, 0xABCD_5513u32]);

                let b = a << 24u8;
                assert_eq!(b.len(), 3);
                assert_eq!(
                    b.as_slice(),
                    [0x0000_0000u32, 0x1337_BEEFu32, 0x00AB_CD55u32]
                );
            }

            #[test]
            fn by_multiple_of_32() {
                let val = 0xFFEE_00AA_AFFE_BEEFu64;
                let mut a = SmolBitSet::from(val);
                assert!(!a.is_inline());

                a <<= 32u8;
                assert_eq!(a.len(), 3);
                assert_eq!(a.as_slice(), [0, 0xAFFE_BEEFu32, 0xFFEE_00AAu32]);

                a <<= 64u8;
                assert_eq!(a.len(), 5);
                assert_eq!(a.as_slice(), [0, 0, 0, 0xAFFE_BEEFu32, 0xFFEE_00AAu32]);
            }
        }

        mod shr {
            use super::*;

            #[test]
            fn inline() {
                let val = 0xF00D_BEEFu32;
                let mut a = SmolBitSet::from(val);
                assert!(a.is_inline());

                a >>= 10u8;
                assert!(a.is_inline());
                assert_eq!(
                    unsafe { a.get_inline_data_unchecked() },
                    (val >> 10) as usize
                );

                let b = a >> 10u8;
                assert!(b.is_inline());
                assert_eq!(
                    unsafe { b.get_inline_data_unchecked() },
                    (val >> (10 + 10)) as usize
                );
            }

            #[test]
            fn slice() {
                let val = 0xF420_1337_FEFE_BEEFu64;
                let mut a = SmolBitSet::from(val);
                assert!(!a.is_inline());
                assert_eq!(a.len(), 2);

                a >>= 8u8;
                assert!(!a.is_inline());
                assert_eq!(a.as_slice(), [0x37FE_FEBEu32, 0x00F4_2013u32]);

                let b = a >> 24u8;
                assert!(!b.is_inline());
                assert_eq!(b.as_slice(), [0xF420_1337u32, 0x0000_0000u32]);
            }

            #[test]
            fn by_multiple_of_32() {
                let val = 0xFFEE_00AA_AFFE_BEEFu64;
                let mut a = SmolBitSet::from(val);
                assert!(!a.is_inline());

                a >>= 32u8;
                assert_eq!(a.len(), 2);
                assert_eq!(a.as_slice(), [0xFFEE_00AAu32, 0]);

                let mut a = SmolBitSet::from(val);
                a >>= 64u8;
                assert_eq!(a.len(), 2);
                assert_eq!(a.as_slice(), [0, 0]);
            }
        }

        #[test]
        fn with_offsets() {
            let val = 0xA5A5_BEEF_1337_A5A5u64;
            let mut a = SmolBitSet::from(val);
            assert!(!a.is_inline());
            assert_eq!(a.len(), 2);

            a <<= 64u16 + 24u16;
            assert!(!a.is_inline());
            assert_eq!(a.len(), 2 + 2 + 1);
            assert_eq!(a.as_slice(), [0, 0, 0xA500_0000, 0xEF13_37A5, 0x00A5_A5BE]);

            a >>= 32u32 + 16u32;
            assert!(!a.is_inline());
            assert_eq!(a.len(), 2 + 2 + 1); // still same size, does not auto shrink
            assert_eq!(a.as_slice(), [0, 0x37A5_A500, 0xA5BE_EF13, 0x0000_00A5, 0],);
        }
    }

    mod binops {
        use super::*;

        use core::ops::{BitAnd, BitOr, BitXor};

        mod inline {
            use super::*;

            macro_rules! test_inline_binops {
                ($($name:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let a = SmolBitSet::from($a);
                        let b = SmolBitSet::from($b);
                        assert!(a.is_inline());
                        assert!(b.is_inline());

                        let res = a.$name(b);
                        assert!(res.is_inline());

                        let d = unsafe { res.get_inline_data_unchecked() };
                        assert_eq!(d, ($a as usize).$name($b as usize));
                    }
                )*}
            }

            test_inline_binops! {
                bitor, 0xF0F0u16, 0x0F0Fu16,
                bitand, 0xFEFEu16, 0xAFFEu16,
                bitxor, 0x3A52u16, 0xAAE8u16
            }
        }

        mod slice {
            use super::*;

            macro_rules! test_slice_binops {
                ($($name:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let a = SmolBitSet::from($a);
                        let b = SmolBitSet::from($b);
                        assert_eq!(a.len(), 2);
                        assert_eq!(b.len(), 2);

                        let res = a.$name(b);
                        assert_eq!(res.len(), 2);
                        assert_eq!(
                            res.as_slice(),
                            [
                                (($a as BitSliceType).$name($b as BitSliceType)),
                                ((($a >> 32) as BitSliceType).$name(($b >> 32) as BitSliceType))
                            ]
                        );
                    }
                )*}
            }

            test_slice_binops! {
                bitor, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0xC0FF_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }

        mod mixed {
            use super::*;

            macro_rules! test_mixed_binops {
                ($($name:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let a = SmolBitSet::from($a);
                        let b = SmolBitSet::from($b);
                        assert!(a.is_inline());
                        assert_eq!(b.len(), 2);

                        let res1 = a.clone().$name(b.clone());
                        assert_eq!(res1.len(), 2);
                        assert_eq!(
                            res1.as_slice(),
                            [
                                (($a as BitSliceType).$name($b as BitSliceType)),
                                ((($a >> 32) as BitSliceType).$name(($b >> 32) as BitSliceType))
                            ]
                        );

                        let res2 = b.$name(a);
                        assert_eq!(res2.len(), 2);
                        assert_eq!(res2.as_slice(), res1.as_slice());
                    }
                )*}
            }

            test_mixed_binops! {
                bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }

        mod rhs_smaller {
            use super::*;

            macro_rules! test_rhs_smaller_binops {
                ($($name:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let mut lhs = SmolBitSet::from($a);
                        let rhs = SmolBitSet::from($b);
                        lhs <<= 32u8;
                        let lhs_len = lhs.len();
                        assert!(lhs_len > rhs.len());

                        let res = lhs.$name(rhs);
                        assert_eq!(res.len(), lhs_len);
                        assert_eq!(
                            res.as_slice(),
                            [
                                ((0 as BitSliceType).$name($b as BitSliceType)),
                                ((($a) as BitSliceType).$name(($b >> 32) as BitSliceType)),
                                ((($a >> 32) as BitSliceType).$name((0 as BitSliceType)))
                            ]
                        );
                    }
                )*};
            }

            test_rhs_smaller_binops! {
                bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }

        mod rhs_larger {
            use super::*;

            macro_rules! test_rhs_larger_binops {
                ($($name:ident, $a:expr, $b:expr),+) => {$(
                    #[test]
                    fn $name() {
                        let lhs = SmolBitSet::from($a);
                        let mut rhs = SmolBitSet::from($b);
                        rhs <<= 32u8;
                        let rhs_len = rhs.len();
                        assert!(rhs_len > lhs.len());

                        let res = lhs.$name(rhs);
                        assert_eq!(res.len(), rhs_len);
                        assert_eq!(
                            res.as_slice(),
                            [
                                (($a as BitSliceType).$name((0 as BitSliceType))),
                                ((($a >> 32) as BitSliceType).$name($b as BitSliceType)),
                                ((0 as BitSliceType).$name((($b >> 32) as BitSliceType)))
                            ]
                        );
                    }
                )*};
            }

            test_rhs_larger_binops! {
                bitor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitand, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64,
                bitxor, 0x0ABC_EE00_1337_BEEFu64, 0xF00D_BEEF_0420_BEEFu64
            }
        }
    }

    mod cmp {
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
    }
}
