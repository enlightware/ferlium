// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Compilation profiling of one runtime workload under Callgrind.
//!
//! The workload is compiled to physical MIR once outside measurement, which also builds the
//! standard library, then `REPEATS` more times inside `measured`. Restricting Callgrind to that
//! function attributes the instructions of user compilation alone to the compiler's functions,
//! where the Wasm Callgrind runner reports only a total per phase. `make profile-compile` builds
//! with debug information and runs it; see `doc/benchmarks.md`.
//!
//! Usage: `compile_profile WORKLOAD [REPEATS]`, with `REPEATS` defaulting to 1.

#[path = "../benches/runtime_workloads.rs"]
mod runtime_workloads;

use std::hint::black_box;

use runtime_workloads::{BenchTarget, RuntimeWorkload};

fn compile(workload: RuntimeWorkload) {
    let prepared = workload.prepare(BenchTarget::PhysicalMir);
    black_box(
        prepared
            .session
            .physical_mir_operation_count(prepared.module_id)
            .unwrap(),
    );
}

/// The only function Callgrind collects.
#[inline(never)]
fn measured(workload: RuntimeWorkload, repeats: usize) {
    for _ in 0..repeats {
        compile(workload);
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let usage = "usage: compile_profile WORKLOAD [REPEATS]";
    let name = args.next().expect(usage);
    let workload = RuntimeWorkload::from_name(&name)
        .unwrap_or_else(|| panic!("unknown workload {name:?}; {usage}"));
    let repeats = args
        .next()
        .map_or(1, |repeats| repeats.parse().expect(usage));
    compile(workload);
    measured(workload, repeats);
}
