// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Prints the Ferlium program an `effect_soundness` input generates, or with `--web ORDER` its
//! web of impls, a program of its own, in that order: `written`, `reversed` or `rotated`.
//!
//! Usage: `cargo run --manifest-path fuzz/Cargo.toml --bin decode_effect_soundness_program --
//! [--web ORDER] <input>`

use arbitrary::Unstructured;
use ferlium_fuzz::{
    effect_soundness::{EffectProgram, Variant},
    impl_web::WebOrder,
};

fn main() {
    let usage = "usage: decode_effect_soundness_program [--web written|reversed|rotated] <input>";
    let mut args = std::env::args().skip(1);
    let mut web = None;
    let mut path = None;
    while let Some(arg) = args.next() {
        if arg == "--web" {
            let name = args.next().expect(usage);
            web = Some(WebOrder::from_name(&name).expect(usage));
        } else {
            path = Some(arg);
        }
    }
    let data = std::fs::read(path.expect(usage)).expect("readable input");
    let program = EffectProgram::generate(&mut Unstructured::new(&data))
        .expect("the input generates a program");
    match web {
        None => print!("{}", program.render(Variant::default())),
        Some(order) => print!(
            "{}",
            program
                .impl_web
                .as_ref()
                .expect("the input generates a web of impls")
                .render(order)
        ),
    }
}
