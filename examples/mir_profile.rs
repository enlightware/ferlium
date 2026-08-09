// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Fast raw-versus-optimized MIR instruction profiling over the runtime benchmark suite.
//!
//! This deliberately does not use Gungraun or Valgrind. It executes each workload once with the
//! optional counters in the MIR reference interpreter, using the same workload definitions and
//! inputs as `benches/benches.rs`.

#[path = "../benches/runtime_workloads.rs"]
mod runtime_workloads;

use std::{collections::BTreeSet, env};

use ferlium::mir::profile::{
    MirExecutionProfile, MirInstructionCostClass, MirInstructionCounts, MirInstructionKind,
};

use runtime_workloads::{BenchTarget, RuntimeWorkload};

fn selected_workloads() -> Vec<RuntimeWorkload> {
    let names = env::args().skip(1).collect::<Vec<_>>();
    if names.iter().any(|name| name == "--list") {
        for workload in RuntimeWorkload::ALL {
            println!("{}", workload.name());
        }
        std::process::exit(0);
    }
    if names.is_empty() {
        return RuntimeWorkload::ALL.to_vec();
    }
    names
        .iter()
        .map(|name| {
            RuntimeWorkload::from_name(name).unwrap_or_else(|| {
                eprintln!("unknown workload `{name}`; use --list to show valid names");
                std::process::exit(2)
            })
        })
        .collect()
}

fn profile(workload: RuntimeWorkload, target: BenchTarget) -> MirExecutionProfile {
    let mut prepared = workload.prepare(target);
    let (result, profile) = prepared.run_profiled();
    result.discard_storage();
    profile
}

fn kinds_in(
    raw: &MirInstructionCounts,
    optimized: &MirInstructionCounts,
    class: MirInstructionCostClass,
) -> BTreeSet<MirInstructionKind> {
    raw.nonzero()
        .chain(optimized.nonzero())
        .map(|(kind, _)| kind)
        .filter(|kind| kind.cost_class() == class)
        .collect()
}

fn print_comparison(name: &str, raw: &MirInstructionCounts, optimized: &MirInstructionCounts) {
    println!("\n{name}");
    println!(
        "{:<32} {:>14} {:>14} {:>14}",
        "instruction", "raw", "optimized", "delta"
    );
    for class in MirInstructionCostClass::ALL {
        let kinds = kinds_in(raw, optimized, class);
        if kinds.is_empty() {
            continue;
        }
        println!("  [{}]", class.label());
        for kind in kinds {
            let before = raw.get(kind);
            let after = optimized.get(kind);
            let delta = i128::from(after) - i128::from(before);
            println!(
                "  {:<30} {:>14} {:>14} {:>+14}",
                kind.label(),
                before,
                after,
                delta
            );
        }
    }
    let before = raw.total();
    let after = optimized.total();
    let delta = i128::from(after) - i128::from(before);
    println!(
        "  {:<30} {:>14} {:>14} {:>+14}",
        "TOTAL", before, after, delta
    );
}

fn main() {
    let workloads = selected_workloads();
    let mut raw_total = MirInstructionCounts::default();
    let mut optimized_total = MirInstructionCounts::default();

    for workload in &workloads {
        eprintln!("profiling {}...", workload.name());
        let raw = profile(*workload, BenchTarget::Mir);
        let optimized = profile(*workload, BenchTarget::OptimizedMir);
        print_comparison(workload.name(), raw.total(), optimized.total());
        raw_total.merge(raw.total());
        optimized_total.merge(optimized.total());
    }

    if workloads.len() > 1 {
        print_comparison("TOTAL", &raw_total, &optimized_total);
    }
}
