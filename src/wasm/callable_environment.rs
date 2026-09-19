// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Raw callable environment storage. Generated code owns capture construction and destruction.

#[cfg(test)]
use std::cell::Cell;
use std::{alloc::Layout, ptr};

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
