#![no_main]
// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Fuzzing of the compiler's limits on deep and large types. See `ferlium_fuzz::deep_types`.

use arbitrary::Unstructured;
use ferlium_fuzz::deep_types::{DeepProgram, check_deep_types};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(data);
    let Ok(program) = DeepProgram::generate(&mut u) else {
        return;
    };
    check_deep_types(&program);
});
