// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Invocation-owned diagnostics. Generated frames retain opaque handles while running cleanup.
//!
//! Trusted native entries must supply a diagnostic on failure, and generated code must use live
//! handles. Violating these contracts can abort: these C ABI callbacks must not unwind.

use crate::{eval::RuntimeError, hir::native_functions::NativeFailureState};

#[derive(Default)]
pub(super) struct Failures {
    pub native: NativeFailureState,
    propagated: Option<RuntimeError>,
    pending: Vec<Option<RuntimeError>>,
}

impl Failures {
    pub fn finish(&mut self, error: Option<RuntimeError>) -> Option<RuntimeError> {
        let mut error = error.or_else(|| self.propagated.take());
        for initial in self.pending.iter_mut().rev().filter_map(Option::take) {
            error = Some(match error {
                Some(error) => initial.interrupted_by(error),
                None => initial,
            });
        }
        error
    }
}

/// Detach the latest diagnostic so cleanup can use the native failure cell again.
pub(super) extern "C" fn capture(state: &mut Failures, pending: u32) -> u32 {
    let error = state
        .propagated
        .take()
        .or_else(|| state.native.take().map(RuntimeError::new_native))
        .expect("failed Wasm call must supply a diagnostic");
    if pending != 0 {
        let slot = &mut state.pending[pending as usize - 1];
        *slot = Some(
            slot.take()
                .expect("live pending failure")
                .interrupted_by(error),
        );
        pending
    } else {
        state.pending.push(Some(error));
        state.pending.len() as u32
    }
}

/// Transfer a frame's retained diagnostic back to its caller.
pub(super) extern "C" fn propagate(state: &mut Failures, pending: u32) -> u32 {
    assert!(state.propagated.is_none());
    state.propagated = Some(
        state.pending[pending as usize - 1]
            .take()
            .expect("live pending failure"),
    );
    // Handles follow nested cleanup order. Reclaim trailing holes without reordering live causes.
    while state.pending.last().is_some_and(Option::is_none) {
        state.pending.pop();
    }
    u32::from(state.propagated.as_ref().unwrap().is_poisoning())
}
