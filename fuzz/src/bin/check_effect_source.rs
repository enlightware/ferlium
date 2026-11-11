// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Runs the `effect_soundness` checks on a Ferlium source file, for triage and minimization:
//! panics on a finding, otherwise prints the report.
//!
//! Usage: `cargo run --release --manifest-path fuzz/Cargo.toml --bin check_effect_source --
//! [--trusted] <file.fer>`
//!
//! `--trusted` compiles the source as trusted code, which allows custom `Value` impls.

use ferlium_fuzz::effect_oracle::check_source_with_trust;

fn main() {
    let mut args: Vec<_> = std::env::args().skip(1).collect();
    let trusted = args.first().is_some_and(|arg| arg == "--trusted");
    if trusted {
        args.remove(0);
    }
    let path = args
        .first()
        .expect("usage: check_effect_source [--trusted] <file.fer>");
    let source = std::fs::read_to_string(path).expect("readable source");
    println!("{:?}", check_source_with_trust(&source, trusted));
}
