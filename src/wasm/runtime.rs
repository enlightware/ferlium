// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Raw storage services. Destruction of live values is the caller's responsibility.

use std::{
    alloc::{Layout, alloc, dealloc, handle_alloc_error},
    ptr,
};

use crate::std::string::{StaticStr, String as NativeString};

#[derive(Clone, Copy)]
struct Header {
    size: usize,
    align: usize,
}

impl Header {
    fn allocation(&self) -> (Layout, usize) {
        let value = Layout::from_size_align(self.size.max(1), self.align)
            .expect("invalid allocation layout");
        let (layout, offset) = Layout::new::<Self>()
            .extend(value)
            .expect("allocation layout overflow");
        (layout.pad_to_align(), offset)
    }
}

/// Recover the payload layout recorded by the temporary pointer-only allocation contract.
///
/// # Safety
/// `data` must be a live allocation returned by [`allocate`].
pub(super) unsafe fn payload_layout(data: *const u8) -> Layout {
    // SAFETY: the allocation contract places a live Header immediately before every payload.
    let header = unsafe { data.sub(size_of::<Header>()).cast::<Header>().read() };
    Layout::from_size_align(header.size.max(1), header.align).expect("invalid allocation layout")
}

/// Allocate aligned, uninitialized storage, including a distinct reclaimable zero-sized block.
pub(super) extern "C" fn allocate(size: usize, align: usize) -> *mut u8 {
    let header = Header { size, align };
    let (layout, offset) = header.allocation();
    // SAFETY: layout is nonzero and valid. The prefix fits Header; offset and Header's size are
    // multiples of its alignment, so placing Header immediately before the payload is aligned.
    unsafe {
        let base = alloc(layout);
        if base.is_null() {
            handle_alloc_error(layout);
        }
        let data = base.add(offset);
        data.sub(size_of::<Header>()).cast::<Header>().write(header);
        data
    }
}

/// Allocate/copy/free supports alignment changes; in-place growth is not implemented.
///
/// # Safety
/// `data` must be a live allocation from these services with no outstanding borrows. Any removed
/// values must already be destroyed; preserved bytes transfer ownership to the returned block.
pub(super) unsafe extern "C" fn reallocate(data: *mut u8, size: usize, align: usize) -> *mut u8 {
    // Allocate first: growth or alignment changes never invalidate the source before copying.
    let replacement = allocate(size, align);
    // SAFETY: the caller owns data; the new allocation is disjoint and large enough for the copy.
    unsafe {
        let header = data.sub(size_of::<Header>()).cast::<Header>().read();
        ptr::copy_nonoverlapping(data, replacement, header.size.min(size));
        release(data);
    }
    replacement
}

/// # Safety
/// `data` must be a live allocation from these services, with no live values or outstanding borrows.
pub(super) unsafe extern "C" fn release(data: *mut u8) {
    // SAFETY: the original size/alignment reconstruct the exact allocation layout and base offset.
    unsafe {
        let header = data.sub(size_of::<Header>()).cast::<Header>().read();
        let (layout, offset) = header.allocation();
        dealloc(data.sub(offset), layout);
    }
}

/// Hide guest storage from optimization without changing its bytes.
pub(super) extern "C" fn black_box(data: *const u8, size: usize) {
    // Observing the pair is sufficient: it keeps the place address and its dynamic extent opaque
    // without constructing a Rust reference (in particular, for a zero-sized value at address 0).
    std::hint::black_box((data, size));
}

/// Compare an owned run-time string with immutable compiler pattern data.
///
/// # Safety
/// Both pointers must address initialized values of their respective Rust types for the duration
/// of this call. Generated code satisfies that contract.
pub(super) unsafe extern "C" fn string_matches(
    actual: *const NativeString,
    expected: *const StaticStr,
) -> u32 {
    // SAFETY: upheld by the generated-code contract above.
    u32::from(unsafe { &*actual }.as_ref() == unsafe { &*expected }.as_str())
}
