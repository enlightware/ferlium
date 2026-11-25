// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Prints the Ferlium program a `deep_types` input generates.
//!
//! Usage: `cargo run --manifest-path fuzz/Cargo.toml --bin decode_deep_types_program -- <input>`

use arbitrary::Unstructured;
use ferlium_fuzz::deep_types::DeepProgram;

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: decode_deep_types_program <input>");
    let data = std::fs::read(path).expect("readable input");
    let program = DeepProgram::generate(&mut Unstructured::new(&data))
        .expect("the input generates a program");
    print!("{}", program.render());
}
