// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Counts, rather than checks: what an optimization that does not exist yet would find to do.
//!
//! A proposed pass is worth its complexity only if there is something for it to remove, and the
//! cheapest way to learn that is to walk the optimized MIR of std and the corpus and count. These
//! are `#[ignore]`d, print their numbers, and assert nothing about them — a census that failed CI
//! when the standard library changed would be deleted within the month. Run one with
//!
//! ```text
//! cargo test --lib mir::pass::census -- --ignored --nocapture
//! ```
//!
//! **A census must be validated against the code it is counting before its number is believed.**
//! The dead-call census below returned 283, 11 and finally 0 as two false-positive classes were
//! found by reading the MIR it had flagged; the first two numbers were nonsense and would have
//! justified building the pass. See `doc/plans/partial-evaluation.md`.
#![cfg(test)]

use std::collections::HashSet;

use crate::{
    CompilerSession, ExecutionTarget, MirOptimization,
    format::FormatWith,
    mir::{Function, Operation, OperationKind, Value, value::ValueId},
    module,
    module::{ModuleEnv, ModuleId},
    std::STD_MODULE_ID,
    types::{
        effects::{Effect, PrimitiveEffect},
        r#type::{CallResultConvention, Type},
    },
};

/// Whether a call could be removed if nothing read its result.
///
/// Deliberately the *permissive* reading, so the count is an upper bound: pure (no `Read`, no
/// `Write`), not fallible, no effect variables, `Value` convention, and a non-unit result. Unit
/// results are excluded for the reason `fold.rs` gives — a host may instrument a pure unit call.
fn removable_if_unread(op: &Operation) -> bool {
    let OperationKind::Call { ty, .. } = &op.kind else {
        return false;
    };
    let effects = ty.effects();
    !effects.has_variables()
        && !effects.contains(Effect::Primitive(PrimitiveEffect::Read))
        && !effects.contains(Effect::Primitive(PrimitiveEffect::Write))
        && !effects.contains(Effect::Primitive(PrimitiveEffect::Fallible))
        && ty.result_convention == CallResultConvention::Value
        && ty.ret() != Type::unit()
}

/// Every register an operation reads, excluding a call's trailing out-pointer — which the call
/// writes, not reads.
fn reads_of(op: &Operation) -> Vec<ValueId> {
    let operands: &[Value] = &op.operands;
    let read_range = match &op.kind {
        OperationKind::Call { .. } => &operands[..operands.len() - 1],
        _ => operands,
    };
    read_range
        .iter()
        .filter_map(|v| match v {
            Value::Register(id) => Some(*id),
            _ => None,
        })
        .collect()
}

/// The local `alloca` a place is rooted in, if any.
///
/// A call that writes through a place derived from a parameter — the return out-pointer above all —
/// initializes storage the caller owns, and is not dead however locally unread it looks. This is
/// the census's crude version of what `provenance.rs` does properly.
fn local_root(ops: &[&Operation], place: ValueId) -> Option<ValueId> {
    let mut current = place;
    loop {
        let def = ops.iter().find(|op| op.result_id() == Some(current))?;
        match &def.kind {
            OperationKind::Alloca { .. } | OperationKind::AllocaPlace { .. } => {
                return Some(current);
            }
            OperationKind::Subfield { .. }
            | OperationKind::DictEntry { .. }
            | OperationKind::SubscriptMember { .. }
            | OperationKind::Project { .. } => match def.operands.first() {
                Some(Value::Register(base)) => current = *base,
                _ => return None,
            },
            _ => return None,
        }
    }
}

/// Whether an operation reading a place register is *observing* the value stored there.
///
/// Deriving a sub-place from it is not an observation, and neither is releasing it: dropping and
/// stack bookkeeping are what gap 2 names as the ownership obligations a real pass has to carry
/// along, not evidence that something read the result.
fn is_observation(op: &Operation) -> bool {
    !matches!(
        op.kind,
        OperationKind::Subfield { .. }
            | OperationKind::DictEntry { .. }
            | OperationKind::SubscriptMember { .. }
            | OperationKind::Drop { .. }
            | OperationKind::DropClosureEnv
            | OperationKind::Clear
            | OperationKind::StackSave
            | OperationKind::StackRestore
    )
}

struct Census {
    /// Calls that are removable and whose result storage nothing reads.
    dead_calls: usize,
    /// Operations that would go with them, the calls themselves included.
    dead_operations: usize,
    /// Total calls examined, for scale.
    total_calls: usize,
    total_operations: usize,
    /// One line per dead call: the function it sits in and the call itself.
    sites: Vec<String>,
}

impl Census {
    fn new() -> Self {
        Self {
            dead_calls: 0,
            dead_operations: 0,
            total_calls: 0,
            total_operations: 0,
            sites: Vec::new(),
        }
    }

    /// Counts the removable calls in one function whose result storage nothing observes.
    ///
    /// The unit of deadness is the **place family**: the local `alloca` the call's out-pointer is
    /// rooted in, together with every place projected out of it. Judging the out-pointer register
    /// alone says a call is dead whenever it writes into a field of an aggregate that is read
    /// through a *different* projection register, which is how the first version of this census
    /// reported 283 dead calls instead of the real figure.
    ///
    /// This stays a census and not the pass: liveness is whole-function rather than per path, and
    /// drops are assumed to come along rather than being proved safe to move.
    fn visit(&mut self, func: &Function, label: &str, env: &ModuleEnv<'_>) {
        let ops: Vec<&Operation> = func
            .blocks()
            .flat_map(|b| func.block(b).operations())
            .collect();
        self.total_operations += ops.len();
        self.total_calls += ops
            .iter()
            .filter(|op| matches!(op.kind, OperationKind::Call { .. }))
            .count();

        let mut pinned: HashSet<ValueId> = HashSet::new();
        for block in func.blocks() {
            for value in func.block(block).terminator().operands() {
                if let Value::Register(id) = value {
                    pinned.insert(*id);
                }
            }
        }

        // Which family each register belongs to, and the members of each family.
        let mut family_of: Vec<(ValueId, ValueId)> = Vec::new();
        for op in &ops {
            if let Some(result) = op.result_id()
                && let Some(root) = local_root(&ops, result)
            {
                family_of.push((result, root));
            }
        }
        let family = |root: ValueId| -> Vec<ValueId> {
            family_of
                .iter()
                .filter(|(_, r)| *r == root)
                .map(|(m, _)| *m)
                .collect()
        };

        for (i, op) in ops.iter().enumerate() {
            if !removable_if_unread(op) {
                continue;
            }
            let Some(Value::Register(out)) = op.operands.last() else {
                continue;
            };
            let Some(root) = local_root(&ops, *out) else {
                continue;
            };
            let members = family(root);
            if members.iter().any(|m| pinned.contains(m)) {
                continue;
            }
            // Anything that observes a member of the family keeps the call.
            let observed = ops.iter().enumerate().any(|(j, other)| {
                j != i
                    && is_observation(other)
                    && reads_of(other).iter().any(|r| members.contains(r))
            });
            if observed {
                continue;
            }
            self.dead_calls += 1;
            self.sites
                .push(format!("{label}\n      {}", op.format_with(env)));
            // What goes with it: the call, the family's own place operations, and everything whose
            // only purpose was to feed one of them.
            self.dead_operations += 1 + ops
                .iter()
                .enumerate()
                .filter(|(j, other)| {
                    *j != i
                        && (other.result_id().is_some_and(|r| members.contains(&r))
                            || reads_of(other).iter().any(|r| members.contains(r)))
                })
                .count();
        }
    }

    fn visit_module(&mut self, session: &CompilerSession, module_id: ModuleId, name: &str) {
        let Some(artifacts) = session.mir_artifacts_for(module_id, MirOptimization::Enabled) else {
            return;
        };
        let module = session.modules().get(module_id).unwrap();
        let env = session.modules().env_for(module);
        for body in artifacts.bodies().iter().flatten() {
            self.visit(body, &format!("{name}::{}", body.name), &env);
        }
    }
}

#[test]
#[ignore = "measurement, not a check: run with --ignored --nocapture"]
/// Prints one corpus module's optimized MIR, for reading a census result back against the code.
/// `DUMP=quicksort cargo test --lib census::dump -- --ignored --nocapture`.
fn dump_one_module() {
    let name = std::env::var("DUMP").unwrap_or_else(|_| "sieve".to_string());
    let src = std::fs::read_to_string(format!("tests/modules/{name}.fer")).unwrap();
    let mut session = CompilerSession::new();
    session.set_mir_optimization(MirOptimization::Enabled);
    let path = module::Path::single_str(&name);
    let module_id = session
        .compile_for(ExecutionTarget::Mir, &src, &name, path)
        .unwrap()
        .module_id;
    println!("{}", session.emit_mir_module(module_id));
}

/// How many pure calls the optimized MIR of std and the corpus computes and then throws away.
///
/// Measured 2026-08-07 at `338fe8b`: **one** candidate of 3334 calls in 21005 operations, and that
/// one is a false positive — `buffer_take` in `Value<[A]>::drop`, where letting the result die *is*
/// the drop, which is exactly the ownership hazard the gap description names. The real answer is
/// zero.
///
/// The rule is deliberately an upper bound, so a zero here is a strong statement: there is nothing
/// for a call-level DCE to remove on the code we compile today. See gap 2 of the plan.
#[test]
#[ignore = "measurement, not a check: run with --ignored --nocapture"]
fn dead_pure_call_census() {
    const CORPUS: &[&str] = &[
        "quicksort",
        "sudoku",
        "sieve",
        "fibonacci",
        "factorial",
        "bank_account",
        "rle_encode",
        "calculator",
        "csv",
    ];

    let mut census = Census::new();
    for name in CORPUS {
        let src = std::fs::read_to_string(format!("tests/modules/{name}.fer")).unwrap();
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let path = module::Path::single_str(name);
        let module_id = session
            .compile_for(ExecutionTarget::Mir, &src, name, path)
            .unwrap()
            .module_id;
        session.prepare_execution_target(ExecutionTarget::Mir, module_id);
        let before = census.dead_calls;
        census.visit_module(&session, module_id, name);
        println!("{name}: {} dead calls", census.dead_calls - before);
    }

    // std once, on its own session.
    let mut session = CompilerSession::new();
    session.set_mir_optimization(MirOptimization::Enabled);
    session.prepare_execution_target(ExecutionTarget::Mir, STD_MODULE_ID);
    let before = census.dead_calls;
    census.visit_module(&session, STD_MODULE_ID, "std");
    println!("std: {} dead calls", census.dead_calls - before);

    println!(
        "\nTOTAL: {} dead pure calls of {} calls; {} operations of {} would go with them",
        census.dead_calls, census.total_calls, census.dead_operations, census.total_operations
    );
    let mut sites = census.sites.clone();
    sites.sort();
    sites.dedup_by(|a, b| a == b);
    for site in sites {
        println!("  {site}");
    }
}
