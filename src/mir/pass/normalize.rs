// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Normalization: the shrinking rewrites, run to a fixpoint between expansions.
//!
//! The driver separates two kinds of rewrite. *Expanding* ones (specialization, inlining) grow
//! code and are bounded by budgets. *Normalizing* ones shrink or canonicalize a body, and the
//! driver runs them until none applies, so that every expansion prices and copies settled bodies.
//!
//! Each pass stays a pure function of its input, returning a rewritten body or `None`. The passes
//! run in a fixed order, which also settles the rewrites that compete for the same code, such as
//! CSE before and after the passes that substitute places. One sweep in that order reaches the
//! fixpoint except where a pass enables an earlier one, or itself. The earlier ones are listed
//! explicitly ([`Pass::enables`]), measured over std and the benchmark corpus; a pass that may
//! enable itself says so with each rewrite ([`Rewrite::enables_itself`]), since only it knows
//! whether its rewrite produced something it consumes. A change marks every later pass and the
//! change's back edges as pending, and the lowest pending pass runs next.
//!
//! A missing back edge costs an optimization, never correctness: any prefix of normalizing
//! rewrites is a valid body. The same holds for the cap on pass runs, which only guards against a
//! defect that would make two rewrites undo each other. Debug builds check both: reaching the cap
//! is reported, and once the worklist empties every pass runs once more and must find nothing.

use crate::mir::Function;

/// One normalizing pass, as the driver sees it.
pub(super) struct Pass<'a> {
    pub(super) name: &'static str,
    pub(super) run: &'a dyn Fn(&Function) -> Option<Rewrite>,
    /// The earlier passes a change by this one can enable, by name.
    pub(super) enables: &'static [&'static str],
}

/// A body a pass rewrote.
pub(super) struct Rewrite {
    pub(super) body: Function,
    /// Whether running the same pass again may find more.
    pub(super) enables_itself: bool,
}

impl Rewrite {
    /// A rewrite after which the pass itself has nothing left to do.
    pub(super) fn settled(body: Function) -> Self {
        Self {
            body,
            enables_itself: false,
        }
    }
}

/// Pass runs per pass in one normalization, beyond which it stops.
///
/// Over std and the benchmark corpus a body settles within three changing sweeps; the cap only
/// bounds a defect.
const RUNS_PER_PASS: usize = 8;

/// Runs `passes` over `function` to a fixpoint, returning the rewritten body if any pass changed it.
pub(super) fn normalize(function: &Function, passes: &[Pass<'_>]) -> Option<Function> {
    let back_edges: Vec<Vec<usize>> = passes
        .iter()
        .enumerate()
        .map(|(index, pass)| {
            pass.enables
                .iter()
                .map(|name| {
                    let target = passes
                        .iter()
                        .position(|pass| pass.name == *name)
                        .unwrap_or_else(|| panic!("unknown normalizing pass `{name}`"));
                    debug_assert!(target < index, "`{name}` must run before `{}`", pass.name);
                    target
                })
                .collect()
        })
        .collect();
    let mut pending = vec![true; passes.len()];
    let mut current: Option<Function> = None;
    let mut runs = 0;
    while let Some(index) = pending.iter().position(|&pending| pending) {
        if runs == RUNS_PER_PASS * passes.len() {
            debug_assert!(
                false,
                "normalizing `{}` reached its cap of {RUNS_PER_PASS} runs per pass with `{}` pending",
                function.name, passes[index].name
            );
            return current;
        }
        runs += 1;
        let Some(rewrite) = (passes[index].run)(current.as_ref().unwrap_or(function)) else {
            pending[index] = false;
            continue;
        };
        current = Some(rewrite.body);
        pending[index] = rewrite.enables_itself;
        pending[index + 1..].fill(true);
        for &target in &back_edges[index] {
            pending[target] = true;
        }
    }
    #[cfg(debug_assertions)]
    {
        let settled = current.as_ref().unwrap_or(function);
        for pass in passes {
            assert!(
                (pass.run)(settled).is_none(),
                "normalizing `{}` left work for `{}`: a back edge is missing",
                function.name,
                pass.name
            );
        }
    }
    current
}
