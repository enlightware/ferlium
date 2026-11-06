#![no_main]
// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Fuzzing of the rule that effects never select an impl. See `ferlium_fuzz::selection`.

use arbitrary::Unstructured;
use ferlium_fuzz::effect_selection::{SelectionProgram, check_selection};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(data);
    let Ok(program) = SelectionProgram::generate(&mut u) else {
        return;
    };
    check_selection(&program);
});
