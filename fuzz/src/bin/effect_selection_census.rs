// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Checks programs of the `effect_selection` generator from pseudo-random inputs and reports how
//! many run, fail or are rejected, by rejection kind, with crashes recorded instead of stopping.
//!
//! Usage: `cargo run --release --manifest-path fuzz/Cargo.toml --bin effect_selection_census --
//! [count] [seed]`

use arbitrary::Unstructured;
use ferlium_fuzz::{
    effect_oracle::{Outcome, Report},
    effect_selection::{SelectionProgram, check_selection},
};
use std::collections::BTreeMap;
use std::panic::{self, AssertUnwindSafe};

fn main() {
    let mut args = std::env::args().skip(1);
    let count: usize = args.next().map_or(1000, |n| n.parse().expect("a count"));
    let mut state: u64 = args
        .next()
        .map_or(0x9e37_79b9_7f4a_7c15, |n| n.parse().expect("a seed"));
    let (mut ran, mut failed, mut crashes) = (0, 0, 0);
    let mut rejected: BTreeMap<String, (usize, String)> = BTreeMap::new();
    for _ in 0..count {
        let data: Vec<u8> = (0..64)
            .map(|_| {
                // xorshift64*
                state ^= state >> 12;
                state ^= state << 25;
                state ^= state >> 27;
                (state.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 56) as u8
            })
            .collect();
        let Ok(program) = SelectionProgram::generate(&mut Unstructured::new(&data)) else {
            continue;
        };
        match panic::catch_unwind(AssertUnwindSafe(|| check_selection(&program))) {
            Err(_) => {
                println!("\n== CRASH {program:?}\n{}", program.render());
                crashes += 1;
            }
            Ok(Report::Ran { outcome, .. }) => {
                ran += 1;
                failed += usize::from(matches!(outcome, Outcome::Failure { .. }));
            }
            Ok(Report::Rejected { category, message }) => {
                rejected
                    .entry(category)
                    .or_insert_with(|| (0, format!("{message}\n{}", program.render())))
                    .0 += 1;
            }
        }
    }
    println!("{count} inputs: {ran} ran ({failed} failed), {crashes} crashed");
    for (category, (occurrences, sample)) in rejected {
        println!("\n== {occurrences} rejected: {category}\n{sample}");
    }
}
