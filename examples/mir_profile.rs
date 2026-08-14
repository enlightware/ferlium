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

fn formatted_delta(before: u64, after: u64) -> String {
    let delta = i128::from(after) - i128::from(before);
    if delta == 0 {
        "0".to_owned()
    } else {
        format!("{delta:+}")
    }
}

fn formatted_percentage(before: u64, after: u64) -> String {
    if before == 0 {
        return if after == 0 {
            "0.00%".to_owned()
        } else {
            "new".to_owned()
        };
    }
    let percentage = (after as f64 / before as f64 - 1.0) * 100.0;
    if percentage == 0.0 {
        "0.00%".to_owned()
    } else if percentage.abs() < 0.01 {
        if percentage.is_sign_positive() {
            "+<0.01%".to_owned()
        } else {
            "-<0.01%".to_owned()
        }
    } else {
        format!("{percentage:+.2}%")
    }
}

fn print_row(label: &str, before: u64, after: u64) {
    println!(
        "  {label:<30} {before:>14} {after:>14} {:>14} {:>10}",
        formatted_delta(before, after),
        formatted_percentage(before, after),
    );
}

fn print_comparison(name: &str, raw: &MirInstructionCounts, optimized: &MirInstructionCounts) {
    println!("\n{name}");
    println!(
        "{:<32} {:>14} {:>14} {:>14} {:>10}",
        "instruction", "raw", "optimized", "delta", "change"
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
            print_row(&kind.label(), before, after);
        }
    }
    let before = raw.total();
    let after = optimized.total();
    print_row("TOTAL", before, after);
}

/// Peak cells is a high-water mark within one workload. At corpus level we sum those paired peaks
/// as a comparison score; it is deliberately not a claim about simultaneous memory use.
fn print_peak_cells(label: &str, raw: usize, optimized: usize) {
    print_row(label, raw as u64, optimized as u64);
}

fn main() {
    let workloads = selected_workloads();
    let mut raw_total = MirInstructionCounts::default();
    let mut optimized_total = MirInstructionCounts::default();
    let (mut raw_peak_sum, mut optimized_peak_sum) = (0, 0);

    for workload in &workloads {
        eprintln!("profiling {}...", workload.name());
        let raw = profile(*workload, BenchTarget::Mir);
        let optimized = profile(*workload, BenchTarget::OptimizedMir);
        print_comparison(workload.name(), raw.total(), optimized.total());
        print_peak_cells("peak cells", raw.peak_cells(), optimized.peak_cells());
        raw_total.merge(raw.total());
        optimized_total.merge(optimized.total());
        raw_peak_sum += raw.peak_cells();
        optimized_peak_sum += optimized.peak_cells();
    }

    if workloads.len() > 1 {
        print_comparison("TOTAL", &raw_total, &optimized_total);
        print_peak_cells(
            "peak cells (workload sum)",
            raw_peak_sum,
            optimized_peak_sum,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{formatted_delta, formatted_percentage};

    #[test]
    fn zero_change_has_no_positive_sign() {
        assert_eq!(formatted_delta(10, 10), "0");
        assert_eq!(formatted_percentage(10, 10), "0.00%");
    }

    #[test]
    fn nonzero_changes_keep_their_direction() {
        assert_eq!(formatted_delta(10, 12), "+2");
        assert_eq!(formatted_delta(10, 8), "-2");
        assert_eq!(formatted_percentage(10, 12), "+20.00%");
        assert_eq!(formatted_percentage(10, 8), "-20.00%");
        assert_eq!(formatted_percentage(100_000, 100_001), "+<0.01%");
        assert_eq!(formatted_percentage(100_000, 99_999), "-<0.01%");
    }

    #[test]
    fn a_new_nonzero_row_has_no_finite_percentage() {
        assert_eq!(formatted_percentage(0, 1), "new");
    }
}
