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

use std::{
    collections::BTreeSet,
    env,
    io::{self, IsTerminal},
};

use ferlium::mir::profile::{
    MirExecutionProfile, MirInstructionCostClass, MirInstructionCounts, MirInstructionKind,
};

use runtime_workloads::{BenchTarget, RuntimeWorkload};

const ANSI_RESET: &str = "\x1b[0m";

#[derive(Clone, Copy)]
struct OutputStyle {
    color: bool,
}

impl OutputStyle {
    fn for_stdout() -> Self {
        Self {
            color: colors_enabled(
                io::stdout().is_terminal(),
                env::var_os("NO_COLOR").is_some(),
            ),
        }
    }

    fn paint(self, codes: &str, text: String) -> String {
        if self.color {
            format!("\x1b[{codes}m{text}{ANSI_RESET}")
        } else {
            text
        }
    }

    fn heading(self, text: String) -> String {
        self.paint("1;36", text)
    }

    fn section(self, text: String) -> String {
        self.paint("36", text)
    }

    fn bold(self, text: String) -> String {
        self.paint("1", text)
    }

    fn change(self, text: String, before: u64, after: u64) -> String {
        let codes = match after.cmp(&before) {
            std::cmp::Ordering::Less => "32",
            std::cmp::Ordering::Equal => "2",
            std::cmp::Ordering::Greater => "31",
        };
        self.paint(codes, text)
    }
}

fn colors_enabled(stdout_is_terminal: bool, no_color_is_set: bool) -> bool {
    stdout_is_terminal && !no_color_is_set
}

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

fn print_row(style: OutputStyle, label: &str, before: u64, after: u64, bold: bool) {
    let mut label = format!("  {label:<30}");
    let mut before_cell = format!("{before:>14}");
    let mut after_cell = format!("{after:>14}");
    let delta_cell = format!("{:>14}", formatted_delta(before, after));
    let percentage_cell = format!("{:>10}", formatted_percentage(before, after));
    if bold {
        label = style.bold(label);
        before_cell = style.bold(before_cell);
        after_cell = style.bold(after_cell);
    }
    let delta_cell = style.change(delta_cell, before, after);
    let percentage_cell = style.change(percentage_cell, before, after);
    println!("{label} {before_cell} {after_cell} {delta_cell} {percentage_cell}");
}

fn print_comparison(
    style: OutputStyle,
    name: &str,
    raw: &MirInstructionCounts,
    optimized: &MirInstructionCounts,
) {
    println!("\n{}", style.heading(name.to_owned()));
    println!(
        "{}",
        style.bold(format!(
            "{:<32} {:>14} {:>14} {:>14} {:>10}",
            "instruction", "raw", "optimized", "delta", "change"
        ))
    );
    for class in MirInstructionCostClass::ALL {
        let kinds = kinds_in(raw, optimized, class);
        if kinds.is_empty() {
            continue;
        }
        println!("{}", style.section(format!("  [{}]", class.label())));
        for kind in kinds {
            let before = raw.get(kind);
            let after = optimized.get(kind);
            print_row(style, &kind.label(), before, after, false);
        }
    }
    let before = raw.total();
    let after = optimized.total();
    print_row(style, "TOTAL", before, after, true);
}

/// Peak cells is a high-water mark within one workload. At corpus level we sum those paired peaks
/// as a comparison score; it is deliberately not a claim about simultaneous memory use.
fn print_peak_cells(style: OutputStyle, label: &str, raw: usize, optimized: usize) {
    print_row(style, label, raw as u64, optimized as u64, false);
}

fn main() {
    let style = OutputStyle::for_stdout();
    let workloads = selected_workloads();
    let mut raw_total = MirInstructionCounts::default();
    let mut optimized_total = MirInstructionCounts::default();
    let (mut raw_peak_sum, mut optimized_peak_sum) = (0, 0);

    for workload in &workloads {
        eprintln!("profiling {}...", workload.name());
        let raw = profile(*workload, BenchTarget::Mir);
        let optimized = profile(*workload, BenchTarget::OptimizedMir);
        print_comparison(style, workload.name(), raw.total(), optimized.total());
        print_peak_cells(
            style,
            "peak cells",
            raw.peak_cells(),
            optimized.peak_cells(),
        );
        raw_total.merge(raw.total());
        optimized_total.merge(optimized.total());
        raw_peak_sum += raw.peak_cells();
        optimized_peak_sum += optimized.peak_cells();
    }

    if workloads.len() > 1 {
        print_comparison(style, "TOTAL", &raw_total, &optimized_total);
        print_peak_cells(
            style,
            "peak cells (workload sum)",
            raw_peak_sum,
            optimized_peak_sum,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{OutputStyle, colors_enabled, formatted_delta, formatted_percentage};

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

    #[test]
    fn color_requires_a_terminal_and_no_override() {
        assert!(colors_enabled(true, false));
        assert!(!colors_enabled(false, false));
        assert!(!colors_enabled(true, true));
    }

    #[test]
    fn changes_use_directional_colors() {
        let style = OutputStyle { color: true };
        assert_eq!(style.change("-2".to_owned(), 10, 8), "\x1b[32m-2\x1b[0m");
        assert_eq!(style.change("+2".to_owned(), 10, 12), "\x1b[31m+2\x1b[0m");
        assert_eq!(style.change("0".to_owned(), 10, 10), "\x1b[2m0\x1b[0m");
    }
}
