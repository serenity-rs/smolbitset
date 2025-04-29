#![allow(dead_code)]

use core::{panic, slice};
use std::alloc::{self, Layout, handle_alloc_error};
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};
use std::ops::{Shl, ShlAssign, Shr, ShrAssign};

type BitSliceType = u32;
const BST_BITS: usize = BitSliceType::BITS as usize;
const INLINE_SLICE_PARTS: usize = usize::BITS as usize / BST_BITS;

pub struct SmolBitSet {
    ptr: *const BitSliceType,
}

impl SmolBitSet {
    const fn new() -> Self {
        Self {
            ptr: 1 as *const BitSliceType,
        }
    }

    #[inline]
    fn is_inline(&self) -> bool {
        self.ptr.addr() & 0b1 == 1
    }

    unsafe fn get_inline_data_unchecked(&self) -> usize {
        self.ptr.addr() >> 1
    }

    const unsafe fn write_inline_data_unchecked(&mut self, data: usize) {
        self.ptr = ((data << 1) & 0b1) as *const BitSliceType;
    }

    fn len(&self) -> BitSliceType {
        if self.is_inline() {
            return 0;
        }

        unsafe { self.len_unchecked() }
    }

    #[inline]
    const unsafe fn len_unchecked(&self) -> BitSliceType {
        unsafe { *self.ptr }
    }

    fn as_slice(&self) -> &[BitSliceType] {
        if self.is_inline() {
            return &[];
        }

        unsafe { self.as_slice_unchecked() }
    }

    const unsafe fn as_slice_unchecked(&self) -> &[BitSliceType] {
        unsafe { slice::from_raw_parts(self.ptr, self.len_unchecked() as usize) }
    }

    fn as_slice_mut(&mut self) -> &mut [BitSliceType] {
        if self.is_inline() {
            return &mut [];
        }

        unsafe { self.as_slice_mut_unchecked() }
    }

    const unsafe fn as_slice_mut_unchecked(&mut self) -> &mut [BitSliceType] {
        unsafe { slice::from_raw_parts_mut(self.ptr.cast_mut(), self.len_unchecked() as usize) }
    }

    fn spill(&mut self, highest_bit: usize) {
        if !self.is_inline() {
            return;
        }

        let len = (highest_bit).div_ceil(BST_BITS);
        let len = len.max(INLINE_SLICE_PARTS);

        let layout = slice_layout::<BitSliceType>(len);
        let ptr = unsafe { alloc::alloc_zeroed(layout).cast::<BitSliceType>() };
        if ptr.is_null() {
            handle_alloc_error(layout)
        }

        let new = unsafe {
            *ptr = len as BitSliceType; // store the length in the first element
            slice::from_raw_parts_mut(ptr.add(1), len)
        };

        let old = self.ptr.addr() >> 1;

        new.iter_mut()
            .enumerate()
            .take(INLINE_SLICE_PARTS)
            .for_each(|(i, elem)| {
                *elem = (old >> (i * BST_BITS)) as BitSliceType;
            });

        self.ptr = ptr;
    }

    fn ensure_capacity(&mut self, highest_bit: usize) {
        if self.is_inline() {
            if highest_bit >= (usize::BITS as usize) {
                self.spill(highest_bit);
            }

            return;
        }

        let len = unsafe { self.len_unchecked() } as usize;
        if highest_bit <= (BST_BITS * len) {
            return;
        }

        // we need to grow our slice allocation
        let new_len = (highest_bit).div_ceil(BST_BITS);
        debug_assert!(new_len >= len);

        let new_layout = slice_layout::<BitSliceType>(new_len);
        let new_ptr = unsafe {
            alloc::realloc(self.ptr as *mut u8, new_layout, new_layout.size())
                .cast::<BitSliceType>()
        };
        if new_ptr.is_null() {
            handle_alloc_error(new_layout)
        }

        unsafe { *new_ptr = new_len as BitSliceType }; // update the new length in the first element
        self.ptr = new_ptr;
    }

    fn highest_set_bit(&self) -> usize {
        if self.is_inline() {
            let data = self.ptr.addr() >> 1;
            return highest_set_bit_usize(data);
        }

        let data = unsafe { self.as_slice_unchecked() };
        let mut highest = 0;
        for (idx, &data) in data.iter().enumerate().rev() {
            let h = highest_set_bit(data);
            if h == 0 {
                continue;
            }

            highest = (idx * BST_BITS) + h;
            break;
        }

        highest
    }
}

impl Drop for SmolBitSet {
    fn drop(&mut self) {
        if self.is_inline() {
            return;
        }

        unsafe {
            let layout = slice_layout::<BitSliceType>(self.len_unchecked() as usize);
            alloc::dealloc(self.ptr as *mut u8, layout);
        }
    }
}

impl Default for SmolBitSet {
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
        let ptr = unsafe { alloc::alloc_zeroed(layout).cast::<BitSliceType>() };
        if ptr.is_null() {
            handle_alloc_error(layout)
        }

        let new_data = unsafe {
            *ptr = len as BitSliceType; // store the length in the first element
            slice::from_raw_parts_mut(ptr.add(1), len)
        };
        new_data.copy_from_slice(src);

        Self { ptr }
    }
}

fn slice_layout<T>(len: usize) -> Layout {
    let len = len + 1; // +1 for the length since we store the length in the first element
    let single = Layout::new::<T>().pad_to_align();
    if let Some(size) = single.size().checked_mul(len) {
        Layout::from_size_align(size, single.align()).expect("Layout error in SmolBitSet slice")
    } else {
        panic!("Overflow in SmolBitSet slice layout");
    }
}

fn highest_set_bit(data: BitSliceType) -> usize {
    if data == 0 {
        return 0;
    }

    for i in (0..BST_BITS).rev() {
        if data & (1 << i) != 0 {
            return i;
        }
    }

    0
}

fn highest_set_bit_usize(data: usize) -> usize {
    if data == 0 {
        return 0;
    }

    for i in (0..usize::BITS as usize).rev() {
        if data & (1 << i) != 0 {
            return i;
        }
    }

    0
}

fn sbs_shl(sbs: &mut SmolBitSet, rhs: usize) {
    if rhs == 0 {
        return;
    }

    let hb: usize = sbs.highest_set_bit();
    sbs.ensure_capacity(hb + rhs);

    if sbs.is_inline() {
        unsafe {
            sbs.write_inline_data_unchecked(sbs.get_inline_data_unchecked() << rhs);
        }
    } else {
        let data = unsafe { sbs.as_slice_mut_unchecked() };

        // shifting further than one slice member?
        let offset = rhs / BST_BITS;
        if offset > 0 {
            for i in (0..data.len()).rev() {
                data[i] = if let Some(src_idx) = i.checked_sub(offset) {
                    data[src_idx]
                } else {
                    0
                };
            }
        }

        let shift = rhs % BST_BITS;
        let carry_shift = BST_BITS - shift;
        let mut carry = 0;
        for d in data.iter_mut() {
            let new = (*d << shift) | carry;
            carry = *d >> carry_shift;
            *d = new;
        }
    }
}

fn sbs_shr(sbs: &mut SmolBitSet, rhs: usize) {
    if rhs == 0 {
        return;
    }

    if sbs.is_inline() {
        unsafe {
            sbs.write_inline_data_unchecked(
                sbs.get_inline_data_unchecked()
                    .checked_shr(rhs as u32)
                    .unwrap_or(0),
            );
        }
    } else {
        let data = unsafe { sbs.as_slice_mut_unchecked() };

        // shifting further than one slice member?
        let offset = rhs / BST_BITS;
        if offset > 0 {
            for i in 0..data.len() {
                data[i] = if let Some(src_idx) = i.checked_add(offset) {
                    data[src_idx]
                } else {
                    0
                };
            }
        }

        let shift = rhs % BST_BITS;
        let carry_shift = BST_BITS - shift;
        let mut carry = 0;
        for d in data.iter_mut().rev() {
            let new = (*d >> shift) | carry;
            carry = *d << carry_shift;
            *d = new;
        }
    }
}

macro_rules! impl_shifts {
    ($($t:ty),+) => {$(
        impl Shl<$t> for SmolBitSet {
            type Output = Self;

            fn shl(mut self, rhs: $t) -> Self {
                sbs_shl(&mut self, rhs as usize);
                self
            }
        }

        impl ShlAssign<$t> for SmolBitSet {
            fn shl_assign(&mut self, rhs: $t) {
                sbs_shl(self, rhs as usize);
            }
        }

        impl Shr<$t> for SmolBitSet {
            type Output = Self;

            fn shr(mut self, rhs: $t) -> Self {
                sbs_shr(&mut self, rhs as usize);
                self
            }
        }

        impl ShrAssign<$t> for SmolBitSet {
            fn shr_assign(&mut self, rhs: $t) {
                sbs_shr(self, rhs as usize);
            }
        }

        impl_shifts!(@ref $t);
    )*};
    (@ref $t:ty) => {
        impl Shl<&$t> for SmolBitSet {
            type Output = Self;

            fn shl(self, rhs: &$t) -> Self {
                self.shl(*rhs)
            }
        }

        impl ShlAssign<&$t> for SmolBitSet {
            fn shl_assign(&mut self, rhs: &$t) {
                self.shl_assign(*rhs)
            }
        }

        impl Shr<&$t> for SmolBitSet {
            type Output = Self;

            fn shr(self, rhs: &$t) -> Self {
                self.shr(*rhs)
            }
        }

        impl ShrAssign<&$t> for SmolBitSet {
            fn shr_assign(&mut self, rhs: &$t) {
                self.shr_assign(*rhs)
            }
        }
    }
}

impl_shifts!(u8, u16, u32, u64, usize);

macro_rules! impl_binop {
    ($($OP:ident :: $op:ident, $OPA:ident :: $opa:ident),+) => {$(
        impl $OP<Self> for SmolBitSet {
            type Output = Self;

            fn $op(self, rhs: Self) -> Self {
                let mut lhs = self;
                lhs.$opa(rhs);
                lhs
            }
        }

        impl $OPA<Self> for SmolBitSet {
            fn $opa(&mut self, rhs: Self) {
                self.$opa(&rhs);
            }
        }

        impl_binop!(@ref $OP :: $op, $OPA :: $opa);
    )*};
    (@ref $OP:ident :: $op:ident, $OPA:ident :: $opa:ident) => {
        impl $OP<&Self> for SmolBitSet {
            type Output = Self;

            fn $op(self, rhs: &Self) -> Self {
                let mut lhs = self;
                lhs.$opa(rhs);
                lhs
            }
        }

        impl $OPA<&Self> for SmolBitSet {
            fn $opa(&mut self, rhs: &Self) {
                match (self.is_inline(), rhs.is_inline()) {
                    (true, true) => unsafe {
                        let lhs = self.get_inline_data_unchecked();
                        let rhs = rhs.get_inline_data_unchecked();
                        self.write_inline_data_unchecked(lhs.$op(rhs));
                    },
                    (_, false) => {
                        let rhs_hb = rhs.highest_set_bit();
                        if rhs_hb > self.highest_set_bit() {
                            self.ensure_capacity(rhs_hb);
                        }

                        let lhs = unsafe { self.as_slice_mut_unchecked() };
                        let rhs = unsafe { rhs.as_slice_unchecked() };

                        assert_eq!(lhs.len(), rhs.len());

                        for (lhs, rhs) in lhs.iter_mut().zip(rhs.iter()) {
                            (*lhs).$opa(*rhs);
                        }
                    }
                    (false, true) => {
                        let lhs = unsafe { self.as_slice_mut_unchecked() };
                        let rhs = unsafe { rhs.get_inline_data_unchecked() };

                        lhs.iter_mut()
                            .enumerate()
                            .take(INLINE_SLICE_PARTS)
                            .for_each(|(idx, lhs)| {
                                (*lhs).$opa((rhs >> (idx * BST_BITS)) as BitSliceType);
                            });
                    }
                }
            }
        }
    };
}

impl_binop! {
    BitOr::bitor, BitOrAssign::bitor_assign,
    BitAnd::bitand, BitAndAssign::bitand_assign,
    BitXor::bitxor, BitXorAssign::bitxor_assign
}

macro_rules! impl_from {
    ($($t:ty),+) => {$(
        impl From<$t> for SmolBitSet {
            fn from(value: $t) -> Self {
                let mut sbs = SmolBitSet::new();
                let value = value as usize;
                sbs.ensure_capacity(highest_set_bit_usize(value));

                if sbs.is_inline() {
                    unsafe { sbs.write_inline_data_unchecked(value) };
                } else {
                    let data = unsafe { sbs.as_slice_mut_unchecked() };
                    assert_eq!(data.len(), 2);

                    data[0] = value as BitSliceType;
                    data[1] = (value >> BST_BITS) as BitSliceType;
                }

                sbs
            }
        }

        impl_from!(@ref $t);
    )*};
    (@ref $t:ty) => {
        impl From<&$t> for SmolBitSet {
            fn from(value: &$t) -> Self {
                Self::from(*value)
            }
        }
    }
}

impl_from!(u8, u16, u32, u64, usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn addr_sanity_check() {
        for i in 0..usize::BITS {
            let t: *const BitSliceType = (1usize << i) as _;
            assert_eq!(t as usize, t.addr());
        }
    }
}
