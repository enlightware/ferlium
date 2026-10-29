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

/// Every normalizing pass, across both stages; each stage lists the ones it runs, in its order.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum NormalizingPass {
    CommonLoads,
    StaticDictionaries,
    Fold,
    CommonCalls,
    RedundantStorage,
    StoredValues,
    CommonSubexpressions,
    CloneBorrowing,
    TerminalMoves,
    ManagedSplit,
    BooleanBranches,
    BooleanResults,
    OverwrittenStores,
    DiscardedResults,
    DeadCalls,
    DeadStorage,
    StackMarkers,
    DeadTrivialResults,
    Tails,
}

impl NormalizingPass {
    const COUNT: usize = Self::Tails as usize + 1;
}

/// One normalizing pass, as the driver sees it.
pub(super) struct Pass<'a> {
    pub(super) id: NormalizingPass,
    pub(super) run: &'a dyn Fn(&Function) -> Option<Rewrite>,
    /// The earlier passes a change by this one can enable.
    pub(super) enables: &'static [NormalizingPass],
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

/// Sets of passes, as bits indexed by position in a stage's list.
type Positions = u32;

const _: () = assert!(NormalizingPass::COUNT <= Positions::BITS as usize);

/// Runs `passes` over `function` to a fixpoint, returning the rewritten body if any pass changed it.
pub(super) fn normalize(function: &Function, passes: &[Pass<'_>]) -> Option<Function> {
    let mut position = [None; NormalizingPass::COUNT];
    for (index, pass) in passes.iter().enumerate() {
        let slot = &mut position[pass.id as usize];
        assert!(slot.is_none(), "{:?} is listed twice", pass.id);
        *slot = Some(index);
    }
    let mut back_edges = [0 as Positions; NormalizingPass::COUNT];
    for (index, pass) in passes.iter().enumerate() {
        for &target in pass.enables {
            let target_index = position[target as usize]
                .unwrap_or_else(|| panic!("{target:?}, enabled by {:?}, is not run", pass.id));
            debug_assert!(
                target_index < index,
                "{target:?} must run before {:?}",
                pass.id
            );
            back_edges[index] |= 1 << target_index;
        }
    }
    let all: Positions = (1 << passes.len()) - 1;
    let mut pending = all;
    let mut current: Option<Function> = None;
    let mut runs = 0;
    while pending != 0 {
        let index = pending.trailing_zeros() as usize;
        if runs == RUNS_PER_PASS * passes.len() {
            debug_assert!(
                false,
                "normalizing `{}` reached its cap of {RUNS_PER_PASS} runs per pass with {:?} pending",
                function.name, passes[index].id
            );
            return current;
        }
        runs += 1;
        let bit = 1 << index;
        let Some(rewrite) = (passes[index].run)(current.as_ref().unwrap_or(function)) else {
            pending &= !bit;
            continue;
        };
        current = Some(rewrite.body);
        let later = all & !(bit | (bit - 1));
        let itself = if rewrite.enables_itself { bit } else { 0 };
        pending = (pending & !bit) | itself | later | back_edges[index];
    }
    #[cfg(debug_assertions)]
    {
        let settled = current.as_ref().unwrap_or(function);
        for pass in passes {
            assert!(
                (pass.run)(settled).is_none(),
                "normalizing `{}` left work for {:?}: a back edge is missing",
                function.name,
                pass.id
            );
        }
    }
    current
}
