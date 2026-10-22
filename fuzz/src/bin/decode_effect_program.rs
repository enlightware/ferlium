// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Prints the Ferlium program an `effect_soundness` input generates.
//!
//! Usage: `cargo run --manifest-path fuzz/Cargo.toml --bin decode_effect_program -- <input>`

use arbitrary::Unstructured;
use ferlium_fuzz::effects::{EffectProgram, Variant};

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: decode_effect_program <input>");
    let data = std::fs::read(&path).expect("readable input");
    let program = EffectProgram::generate(&mut Unstructured::new(&data))
        .expect("the input generates a program");
    print!("{}", program.render(Variant::default()));
}
