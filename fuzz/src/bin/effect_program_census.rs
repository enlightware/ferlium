// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Generates programs from pseudo-random inputs and reports how many compile, run, fail and are
//! rejected, by rejection kind: measures how much the `effect_soundness` generator reaches.
//! Rejections are not findings by themselves; their samples are for inspection.
//!
//! Usage: `cargo run --release --manifest-path fuzz/Cargo.toml --bin effect_program_census --
//! [count] [seed]`

use arbitrary::Unstructured;
use ferlium_fuzz::{
    effect_oracle::{Outcome, Report, check_program},
    effects::{EffectProgram, Variant},
};
use std::collections::BTreeMap;
use std::panic::{self, AssertUnwindSafe};

fn main() {
    let mut args = std::env::args().skip(1);
    let count: usize = args.next().map_or(1000, |n| n.parse().expect("a count"));
    let mut state: u64 = args
        .next()
        .map_or(0x9e37_79b9_7f4a_7c15, |n| n.parse().expect("a seed"));
    let mut ran = 0;
    let mut failed = 0;
    let mut typed_fallible = 0;
    let mut crashes = 0;
    let mut rejected: BTreeMap<String, (usize, String)> = BTreeMap::new();
    for _ in 0..count {
        let data: Vec<u8> = (0..256)
            .map(|_| {
                // xorshift64*
                state ^= state >> 12;
                state ^= state << 25;
                state ^= state >> 27;
                (state.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 56) as u8
            })
            .collect();
        let Ok(program) = EffectProgram::generate(&mut Unstructured::new(&data)) else {
            continue;
        };
        let checked = panic::catch_unwind(AssertUnwindSafe(|| check_program(&program)));
        let Ok(report) = checked else {
            let source = program.render(Variant::default());
            println!("\n== CRASH\n{source}");
            crashes += 1;
            continue;
        };
        match report {
            Report::Ran { outcome, may_fail } => {
                ran += 1;
                failed += usize::from(matches!(outcome, Outcome::Failure { .. }));
                typed_fallible += usize::from(may_fail);
            }
            Report::Rejected { category, message } => {
                let source = program.render(Variant::default());
                let category = format!("{category} at `{}`", pointed_line(&message, &source));
                let entry = rejected.entry(category).or_insert_with(|| {
                    (
                        0,
                        format!("{message}\n{}", program.render(Variant::default())),
                    )
                });
                entry.0 += 1;
            }
        }
    }
    println!(
        "{count} inputs: {ran} ran ({failed} failed, {typed_fallible} typed fallible), {crashes} crashed"
    );
    for (category, (n, sample)) in &rejected {
        println!("\n== {n} rejected: {category}\n{sample}");
    }
}

/// The start of the source line the first non-empty span of `message` points at, up to its first
/// brace: enough to tell rejections apart by the construct they blame.
fn pointed_line(message: &str, source: &str) -> String {
    let mut rest = message;
    while let Some(index) = rest.find("span: Span { start: ") {
        rest = &rest[index + "span: Span { start: ".len()..];
        let number = |text: &str| -> Option<usize> {
            text.split(|c: char| !c.is_ascii_digit())
                .next()?
                .parse()
                .ok()
        };
        let Some(start) = number(rest) else { continue };
        let Some(end) = rest.find("end: ").and_then(|i| number(&rest[i + 5..])) else {
            continue;
        };
        if end > start && end <= source.len() {
            let line_start = source[..start].rfind('\n').map_or(0, |i| i + 1);
            let line = source[line_start..]
                .lines()
                .next()
                .unwrap_or_default()
                .trim();
            return line
                .split('{')
                .next()
                .unwrap_or_default()
                .trim()
                .to_string();
        }
    }
    String::new()
}
