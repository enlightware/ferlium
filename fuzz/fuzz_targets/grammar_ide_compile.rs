#![no_main]
// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use libfuzzer_sys::fuzz_target;

fuzz_target!(|tape: &[u8]| {
    let Some(source) = ferlium_fuzz::source_from_tape(tape) else {
        return;
    };

    let mut compiler = ferlium::Compiler::new();
    let _ = compiler.compile(&source);
});
