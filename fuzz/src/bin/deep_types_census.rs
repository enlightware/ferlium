// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Checks programs of the `deep_types` generator from pseudo-random inputs and reports how many
//! run, stop at a sandbox limit or are rejected, by limit, and the slowest, with crashes recorded
//! instead of stopping. Before checking a program, it writes its input to
//! `deep_types_census.PID.input` in the working directory, PID being its process id and the path
//! printed at start, so that a hang or a crash that ends the process leaves the input for
//! `decode_deep_types_program`, even with several censuses running.
//!
//! Usage: `cargo run --release --manifest-path fuzz/Cargo.toml --bin deep_types_census --
//! [count] [seed]`

use arbitrary::Unstructured;
use ferlium_fuzz::{
    deep_types::{DeepProgram, check_deep_types},
    effect_oracle::{Outcome, Report},
};
use std::collections::BTreeMap;
use std::panic::{self, AssertUnwindSafe};
use std::time::{Duration, Instant};

fn main() {
    let mut args = std::env::args().skip(1);
    let count: usize = args.next().map_or(1000, |n| n.parse().expect("a count"));
    let mut state: u64 = args
        .next()
        .map_or(0x9e37_79b9_7f4a_7c15, |n| n.parse().expect("a seed"));
    let (mut ran, mut limited, mut crashes) = (0, 0, 0);
    let mut rejected: BTreeMap<String, usize> = BTreeMap::new();
    let mut slowest = (Duration::ZERO, String::new());
    // The input of the program being checked.
    let current_input = format!("deep_types_census.{}.input", std::process::id());
    println!("current input: {current_input}");
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
        let Ok(program) = DeepProgram::generate(&mut Unstructured::new(&data)) else {
            continue;
        };
        std::fs::write(&current_input, &data).expect("a writable working directory");
        let start = Instant::now();
        let report = panic::catch_unwind(AssertUnwindSafe(|| check_deep_types(&program)));
        let elapsed = start.elapsed();
        if elapsed > slowest.0 {
            slowest = (elapsed, program.render());
        }
        match report {
            Err(_) => {
                println!("\n== CRASH {program:?}\n{}", program.render());
                crashes += 1;
            }
            Ok(Report::Ran {
                outcome: Outcome::Limit,
                ..
            }) => limited += 1,
            Ok(Report::Ran { .. }) => ran += 1,
            Ok(Report::Rejected { category, message }) => {
                // The kind of limit, when the error names one.
                let kind = message
                    .split_once("kind: ")
                    .and_then(|(_, rest)| rest.split([',', ' ', '}']).next())
                    .unwrap_or_default();
                *rejected.entry(format!("{category} {kind}")).or_default() += 1;
            }
        }
    }
    println!("{count} inputs: {ran} ran, {limited} stopped at a sandbox limit, {crashes} crashed");
    for (kind, occurrences) in rejected {
        println!("{occurrences} rejected: {kind}");
    }
    println!(
        "\n== slowest, {:.2} s:\n{}",
        slowest.0.as_secs_f64(),
        slowest.1
    );
}
