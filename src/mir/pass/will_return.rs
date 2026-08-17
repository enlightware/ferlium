// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Conservative proofs that a call cannot diverge.
//!
//! This is a theorem about a function's source semantics, derived once from raw MIR and retained
//! across optimization. A semantics-preserving rewrite cannot invalidate a proof; it can only make
//! an `Unknown` body easier to prove. Keeping that distinction avoids analysis invalidation inside
//! the per-function optimization loop while still giving speculation a generic, checkable gate.
//!
//! The initial proof deliberately recognizes only finite call DAGs: a script body must have an
//! acyclic reachable CFG, and every operation it may invoke must name a callee already proved to
//! return. Recursive call components, indirect calls, scoped projections and closure-environment
//! clone/drop remain unknown. Native functions have no MIR and are proved by Ferlium's host-function
//! contract, which requires them to terminate for every valid input.

use std::collections::VecDeque;

use crate::{
    mir::{Function, Operation, OperationKind, terminator::TerminatorKind},
    module::{FunctionId, LocalFunctionId, ModuleId, id::Id},
};

use super::call_graph::CallGraph;

/// Whether termination has been proved for every valid invocation of a function.
///
/// `Unknown` is not a proof of divergence. Keeping a two-point lattice makes the conservative
/// direction explicit: clients may speculate only `Proven` callees.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum WillReturn {
    Unknown,
    Proven,
}

impl WillReturn {
    pub(crate) fn is_proven(self) -> bool {
        self == Self::Proven
    }
}

/// One module's cached termination proofs, indexed like its raw function table.
#[derive(Clone, Default)]
pub(crate) struct WillReturnSummaries {
    of: Vec<WillReturn>,
}

impl WillReturnSummaries {
    /// Proves the finite call DAG rooted at each raw MIR body.
    ///
    /// Components are visited callees-first. Starting every script function at `Unknown` prevents
    /// recursion from proving itself; mutually dependent non-call references may still settle to
    /// `Proven` through the monotone fixed point. A bodyless local function is native and therefore
    /// inherits the host termination contract.
    pub(crate) fn of_module(
        bodies: &[Option<Function>],
        module: ModuleId,
        external: &dyn Fn(FunctionId) -> WillReturn,
    ) -> Self {
        let graph = CallGraph::of_module(bodies, module);
        let mut of = vec![WillReturn::Unknown; bodies.len()];

        for component in graph.components_callees_first() {
            loop {
                let mut changed = false;
                for &id in &component {
                    if of[id.as_index()] == WillReturn::Proven {
                        continue;
                    }
                    let derived = match &bodies[id.as_index()] {
                        Some(body) => derive(body, module, &of, external),
                        None => WillReturn::Proven,
                    };
                    if derived == WillReturn::Proven {
                        of[id.as_index()] = WillReturn::Proven;
                        changed = true;
                    }
                }
                if !changed || component.len() == 1 {
                    break;
                }
            }
        }
        Self { of }
    }

    pub(crate) fn summary(&self, id: LocalFunctionId) -> WillReturn {
        self.of
            .get(id.as_index())
            .copied()
            .unwrap_or(WillReturn::Unknown)
    }
}

fn derive(
    body: &Function,
    module: ModuleId,
    known: &[WillReturn],
    external: &dyn Fn(FunctionId) -> WillReturn,
) -> WillReturn {
    let reachable = reachable_blocks(body);
    if has_cycle(body, &reachable) {
        return WillReturn::Unknown;
    }

    let callee_returns = |callee: FunctionId| {
        (if callee.module == module {
            known
                .get(callee.function.as_index())
                .copied()
                .unwrap_or(WillReturn::Unknown)
        } else {
            external(callee)
        }) == WillReturn::Proven
    };

    for block in body.blocks().filter(|block| reachable[block.as_index()]) {
        let basic = body.block(block);
        if basic
            .operations()
            .iter()
            .any(|operation| !operation_returns(operation, &callee_returns))
        {
            return WillReturn::Unknown;
        }
        match &basic.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => {
                if !operation_returns(operation, &callee_returns) {
                    return WillReturn::Unknown;
                }
            }
            // Yield suspends rather than completing the invocation. Proving that a scoped accessor
            // reaches its yield and later finishes needs a separate summary.
            TerminatorKind::Yield { .. } => return WillReturn::Unknown,
            TerminatorKind::Goto { .. }
            | TerminatorKind::CondBr { .. }
            | TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup => {}
        }
    }
    WillReturn::Proven
}

/// Whether an operation is intrinsically finite or invokes only a proved callee.
fn operation_returns(operation: &Operation, callee_returns: &impl Fn(FunctionId) -> bool) -> bool {
    let direct = |operand: Option<&crate::mir::Value>| matches!(operand, Some(crate::mir::Value::Function(callee)) if callee_returns(*callee));
    match &operation.kind {
        OperationKind::Call { .. } => direct(operation.operands.first()),
        OperationKind::Clone { .. } => direct(operation.operands.get(2)),
        OperationKind::Drop { .. } => direct(operation.operands.get(1)),
        // `Project` runs an accessor until its yield; `EndProject` resumes the suspended body.
        // Closure-environment clone/drop recursively invoke functions stored in runtime values.
        OperationKind::Project { .. }
        | OperationKind::EndProject
        | OperationKind::CloneClosureEnv { .. }
        | OperationKind::DropClosureEnv => false,
        OperationKind::Alloca { .. }
        | OperationKind::AllocaPlace { .. }
        | OperationKind::CompareEqual
        | OperationKind::Load
        | OperationKind::Subfield { .. }
        | OperationKind::DictEntry { .. }
        | OperationKind::SubscriptMember { .. }
        | OperationKind::BuildSubscript { .. }
        | OperationKind::Variant { .. }
        | OperationKind::BuildArray { .. }
        | OperationKind::ExtractTag
        | OperationKind::Store
        | OperationKind::Clear
        | OperationKind::Memcpy
        | OperationKind::Move
        | OperationKind::StackSave
        | OperationKind::StackRestore
        | OperationKind::CheckCallDepth
        | OperationKind::CheckFuel
        | OperationKind::BuildClosure { .. } => true,
    }
}

fn reachable_blocks(body: &Function) -> Vec<bool> {
    let mut reachable = vec![false; body.blocks().count()];
    let mut pending = vec![body.entry()];
    while let Some(block) = pending.pop() {
        if std::mem::replace(&mut reachable[block.as_index()], true) {
            continue;
        }
        pending.extend(body.block(block).terminator().successors());
    }
    reachable
}

/// Kahn's algorithm over the reachable CFG. Anything left after removing indegree-zero blocks is
/// on or downstream of a directed cycle; only the count matters here.
fn has_cycle(body: &Function, reachable: &[bool]) -> bool {
    let mut indegree = vec![0usize; reachable.len()];
    let reachable_count = reachable
        .iter()
        .filter(|&&is_reachable| is_reachable)
        .count();
    for block in body.blocks().filter(|block| reachable[block.as_index()]) {
        for successor in body.block(block).terminator().successors() {
            if reachable[successor.as_index()] {
                indegree[successor.as_index()] += 1;
            }
        }
    }
    let mut pending: VecDeque<_> = body
        .blocks()
        .filter(|block| reachable[block.as_index()] && indegree[block.as_index()] == 0)
        .collect();
    let mut removed = 0;
    while let Some(block) = pending.pop_front() {
        removed += 1;
        for successor in body.block(block).terminator().successors() {
            if !reachable[successor.as_index()] {
                continue;
            }
            indegree[successor.as_index()] -= 1;
            if indegree[successor.as_index()] == 0 {
                pending.push_back(successor);
            }
        }
    }
    removed != reachable_count
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, ExecutionTarget, MirOptimization, module::Path};
    use ustr::ustr;

    fn summaries_of(src: &str) -> (WillReturnSummaries, impl Fn(&str) -> LocalFunctionId) {
        let mut session = CompilerSession::new();
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                src,
                "test",
                Path::single_str("will_return"),
            )
            .expect("the test source must compile")
            .module_id;
        let summaries = {
            let artifacts = session
                .mir_artifacts_for(module_id, MirOptimization::Disabled)
                .expect("raw MIR must be prepared");
            WillReturnSummaries::of_module(artifacts.bodies(), module_id, &|callee| {
                session
                    .mir_artifacts_for(callee.module, MirOptimization::Disabled)
                    .map_or(WillReturn::Unknown, |artifacts| {
                        artifacts.will_return(callee.module, callee.function)
                    })
            })
        };
        let lookup = move |name: &str| {
            session
                .expect_fresh_module(module_id)
                .get_local_function_id(ustr(name))
                .unwrap_or_else(|| panic!("no function named {name}"))
        };
        (summaries, lookup)
    }

    #[test]
    fn proves_an_acyclic_direct_call_dag() {
        let (summaries, id) = summaries_of(
            "fn leaf(x: int) -> int { x + 1 }\n\
             fn caller(x: int) -> int { leaf(x) }",
        );
        assert_eq!(summaries.summary(id("leaf")), WillReturn::Proven);
        assert_eq!(summaries.summary(id("caller")), WillReturn::Proven);
    }

    #[test]
    fn a_reachable_cfg_cycle_is_unknown() {
        let (summaries, id) = summaries_of("fn spin() -> int { loop {} }");
        assert_eq!(summaries.summary(id("spin")), WillReturn::Unknown);
    }

    #[test]
    fn recursion_cannot_prove_itself() {
        let (summaries, id) = summaries_of(
            "fn even(n: int) -> bool { if n == 0 { true } else { odd(n - 1) } }\n\
             fn odd(n: int) -> bool { if n == 0 { false } else { even(n - 1) } }",
        );
        assert_eq!(summaries.summary(id("even")), WillReturn::Unknown);
        assert_eq!(summaries.summary(id("odd")), WillReturn::Unknown);
    }

    #[test]
    fn an_indirect_call_is_unknown() {
        let (summaries, id) = summaries_of("fn apply(f: (int) -> int, x: int) -> int { f(x) }");
        assert_eq!(summaries.summary(id("apply")), WillReturn::Unknown);
    }
}
