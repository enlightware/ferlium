// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Invocation-owned diagnostics. Generated frames retain opaque handles while running cleanup.
//! Propagation with handle zero forwards the current diagnostic; a nonzero handle transfers a
//! retained diagnostic and requires the current failure cells to be empty. Capture alone chains
//! failures raised during cleanup.
//!
//! Trusted native entries must supply a diagnostic on failure, and nonzero handles must be live. Violating these contracts can abort: these C ABI callbacks must not unwind.

use crate::{
    compiler::error::SourceFailureKind, eval::RuntimeError,
    hir::native_functions::NativeFailureState,
};

/// Supply the same diagnostic and status as the native division entries.
pub(super) extern "C" fn division_by_zero(state: &mut NativeFailureState) -> u32 {
    state.fail(SourceFailureKind::DivisionByZero)
}

/// Supply the same diagnostic and status as the native remainder entries.
pub(super) extern "C" fn remainder_by_zero(state: &mut NativeFailureState) -> u32 {
    state.fail(SourceFailureKind::RemainderByZero)
}

#[derive(Default)]
pub(super) struct Failures {
    pub native: NativeFailureState,
    propagated: Option<RuntimeError>,
    pending: Vec<Option<RuntimeError>>,
}

impl Failures {
    fn take_current(&mut self) -> Option<RuntimeError> {
        self.propagated
            .take()
            .or_else(|| self.native.take().map(RuntimeError::new_native))
    }

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
        .take_current()
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

/// Transfer the current or retained diagnostic back to the caller. Immediate propagation needs
/// no pending handle; cleanup paths retain one so subsequent failures can be chained with it.
pub(super) extern "C" fn propagate(state: &mut Failures, pending: u32) -> u32 {
    let error = if pending == 0 {
        state
            .take_current()
            .expect("failed Wasm call must supply a diagnostic")
    } else {
        assert!(
            state.take_current().is_none(),
            "retained failure must have no current diagnostic"
        );
        state.pending[pending as usize - 1]
            .take()
            .expect("live pending failure")
    };
    state.propagated = Some(error);
    // Handles follow nested cleanup order. Reclaim trailing holes without reordering live causes.
    while state.pending.last().is_some_and(Option::is_none) {
        state.pending.pop();
    }
    u32::from(state.propagated.as_ref().unwrap().is_poisoning())
}

#[cfg(test)]
mod tests {
    use wasm_bindgen_test::wasm_bindgen_test;

    use super::*;
    use crate::compiler::error::RuntimeErrorKind;

    #[wasm_bindgen_test]
    fn propagation_preserves_current_and_retained_diagnostics() {
        let mut state = Failures::default();
        state.native.fail(SourceFailureKind::DivisionByZero);
        assert_eq!(propagate(&mut state, 0), 0);
        // A generated caller can forward an already propagated diagnostic without capturing it.
        assert_eq!(propagate(&mut state, 0), 0);
        assert_eq!(
            state.finish(None).unwrap().kind(),
            RuntimeErrorKind::SourceFailure(SourceFailureKind::DivisionByZero)
        );

        state.native.fail(SourceFailureKind::DivisionByZero);
        let pending = capture(&mut state, 0);
        assert_eq!(propagate(&mut state, pending), 0);
        assert_eq!(
            state.finish(None).unwrap().kind(),
            RuntimeErrorKind::SourceFailure(SourceFailureKind::DivisionByZero)
        );

        state.native.fail(SourceFailureKind::DivisionByZero);
        let pending = capture(&mut state, 0);
        state.native.fail(SourceFailureKind::RemainderByZero);
        assert_eq!(capture(&mut state, pending), pending);
        assert_eq!(propagate(&mut state, pending), 1);
        // Direct forwarding must preserve poisoning as well as ordinary source failures.
        assert_eq!(propagate(&mut state, 0), 1);
        let error = state.finish(None).unwrap();
        let chain = error.failure_during_cleanup().unwrap();
        assert_eq!(chain.initial().kind(), SourceFailureKind::DivisionByZero);
        assert_eq!(
            chain.during_cleanup().kind(),
            SourceFailureKind::RemainderByZero
        );
    }
}
