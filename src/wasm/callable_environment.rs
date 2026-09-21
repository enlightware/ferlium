// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Raw callable environment storage. Generated code owns capture construction and destruction.

#[cfg(test)]
use std::cell::Cell;
use std::{alloc::Layout, ptr};

#[cfg(test)]
use wasm_bindgen_test::wasm_bindgen_test;

use super::{evidence, runtime};
use crate::mir::physical::DictionaryReference;

/// Prefix followed by hidden evidence, capture offsets, then the aligned capture tuple.
/// Storage flags occupy the low byte of a zero-padded evidence slot, with no environment owner.
#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct Environment {
    pub(super) values_offset: u32,
    pub(super) values_size: u32,
    pub(super) values_align: u32,
    pub(super) hidden_count: u32,
    pub(super) capture_count: u32,
    pub(super) dictionary: DictionaryReference,
}

impl Environment {
    pub(super) fn hidden_offset(index: usize) -> u32 {
        (size_of::<Self>() + index * size_of::<DictionaryReference>()) as u32
    }

    pub(super) fn capture_offset(hidden: usize, index: usize) -> u32 {
        Self::hidden_offset(hidden) + index as u32 * 4
    }
}

/// Reserve an environment; generated code fills the captures and retains its evidence.
pub(super) extern "C" fn allocate(
    size: usize,
    align: usize,
    hidden: u32,
    captures: u32,
) -> *mut Environment {
    let prefix = Environment::capture_offset(hidden as usize, captures as usize) as usize;
    let (layout, offset) = Layout::from_size_align(prefix, align_of::<Environment>())
        .unwrap()
        .extend(Layout::from_size_align(size, align).expect("callable capture layout"))
        .expect("callable environment layout overflow");
    let environment = runtime::allocate(layout.size(), layout.align()).cast::<Environment>();
    // SAFETY: the prefix fits and contains only integer fields and evidence references.
    unsafe {
        ptr::write_bytes(environment.cast::<u8>(), 0, offset);
        environment.write(Environment {
            values_offset: offset as u32,
            values_size: size as u32,
            values_align: align as u32,
            hidden_count: hidden,
            capture_count: captures,
            dictionary: DictionaryReference {
                descriptor: 0,
                environment: 0,
            },
        });
    }
    #[cfg(test)]
    LIVE_ENVIRONMENTS.set(LIVE_ENVIRONMENTS.get() + 1);
    environment
}

/// Clone metadata and retain evidence, leaving the new source-value tuple uninitialized.
///
/// # Safety
/// The source environment is complete and remains borrowed throughout the call.
pub(super) unsafe extern "C" fn copy_shell(source: *const Environment) -> *mut Environment {
    // SAFETY: both metadata prefixes have the same layout; tuple bytes are deliberately not copied.
    unsafe {
        let header = source.read();
        let result = allocate(
            header.values_size as usize,
            header.values_align as usize,
            header.hidden_count,
            header.capture_count,
        );
        ptr::copy_nonoverlapping(
            source.cast::<u8>(),
            result.cast::<u8>(),
            header.values_offset as usize,
        );
        evidence::retain(&raw const (*result).dictionary);
        for index in 0..header.hidden_count as usize {
            evidence::retain(
                result
                    .byte_add(Environment::hidden_offset(index) as usize)
                    .cast(),
            );
        }
        result
    }
}

/// Copy a closed subscript's evidence captures into its owned callable environment.
///
/// # Safety
/// `data` is the live immutable image and `source` is a valid subscript evidence reference.
pub(super) unsafe extern "C" fn materialize_subscript(
    data: *const u8,
    source: *const DictionaryReference,
) -> *mut Environment {
    // SAFETY: the descriptor fixes every source capture offset and representation.
    unsafe {
        let source = source.read();
        let descriptor = evidence::descriptor(data, source.descriptor);
        if descriptor.captures == 0 {
            return ptr::null_mut();
        }
        let result = allocate(0, 1, descriptor.captures, 0);
        let fields = ptr::from_ref(descriptor)
            .byte_add(size_of::<evidence::DictionaryDescriptor>())
            .cast::<u32>();
        for index in 0..descriptor.captures as usize {
            let field = fields.add(index).read();
            let target = result
                .byte_add(Environment::hidden_offset(index) as usize)
                .cast::<u8>();
            if field & (1 << 31) != 0 {
                target.write(
                    (source.environment as *const u8)
                        .add((field & !(1 << 31)) as usize)
                        .read(),
                );
            } else {
                let source = (source.environment as *const u8)
                    .add(field as usize)
                    .cast::<DictionaryReference>();
                target.cast::<DictionaryReference>().write(source.read());
                evidence::retain(target.cast());
            }
        }
        result
    }
}

/// Release evidence and storage after the capture tuple has been destroyed.
///
/// # Safety
/// The environment is uniquely owned and contains no live source values.
pub(super) unsafe extern "C" fn release(data: *const u8, environment: *mut Environment) {
    // SAFETY: generated clone/drop entries manage source values and transfer the remaining owner.
    unsafe {
        evidence::release(data, &raw const (*environment).dictionary);
        for index in 0..(*environment).hidden_count as usize {
            evidence::release(
                data,
                environment
                    .byte_add(Environment::hidden_offset(index) as usize)
                    .cast(),
            );
        }
        runtime::release(environment.cast());
    }
    #[cfg(test)]
    LIVE_ENVIRONMENTS.set(LIVE_ENVIRONMENTS.get() - 1);
}

#[cfg(test)]
thread_local! {
    pub(super) static LIVE_ENVIRONMENTS: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
#[wasm_bindgen_test]
fn wasm_codegen_materialized_subscript_copies_storage_flag_captures() {
    let before = LIVE_ENVIRONMENTS.get();
    let data = [
        4_u32, // Descriptor zero starts after this prefix entry.
        8,     // Environment size.
        8,     // Environment alignment.
        1,     // Capture count.
        0,     // Entry table (unused by materialization).
        1 << 31,
    ];
    let flag = 1_u8;
    let source = DictionaryReference {
        descriptor: 0,
        environment: ptr::from_ref(&flag) as usize,
    };
    // SAFETY: the local image describes one flag byte at offset zero and remains live throughout.
    let environment = unsafe { materialize_subscript(data.as_ptr().cast(), &source) };
    // SAFETY: materialization allocated the descriptor's one zero-padded hidden slot.
    assert_eq!(
        unsafe {
            environment
                .byte_add(Environment::hidden_offset(0) as usize)
                .cast::<u8>()
                .read()
        },
        1
    );
    // SAFETY: no source values exist and this transfers the environment's sole owner.
    unsafe { release(data.as_ptr().cast(), environment) };
    assert_eq!(LIVE_ENVIRONMENTS.get(), before);
}
