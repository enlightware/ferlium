// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Runs the `effect_soundness` checks on a Ferlium source file, for triage and minimization:
//! panics on a finding, otherwise prints the report.
//!
//! Usage: `cargo run --release --manifest-path fuzz/Cargo.toml --bin check_effect_source --
//! <file.fer>`

use ferlium_fuzz::effect_oracle::check_source;

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: check_effect_source <file.fer>");
    let source = std::fs::read_to_string(&path).expect("readable source");
    println!("{:?}", check_source(&source));
}
