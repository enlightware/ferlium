#![no_main]
// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Soundness fuzzing of trait output effects: generated programs combining traits with output
//! effects, concrete and blanket impls, generic callers and fallible callbacks must never let a
//! source failure escape code typed as unable to fail, and must behave alike on every backend and
//! under renaming and reordering. See `ferlium_fuzz::effects`.

use arbitrary::Unstructured;
use ferlium_fuzz::{effect_oracle::check_program, effects::EffectProgram};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(data);
    let Ok(program) = EffectProgram::generate(&mut u) else {
        return;
    };
    check_program(&program);
});
