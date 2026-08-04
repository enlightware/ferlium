// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Inlining: replacing a call with the callee's own operations.
//!
//! Inlining matters here less for the call overhead it removes than for what it hands to folding.
//! A callee's parameters are opaque to the analysis; once its body sits in the caller with the
//! caller's operands substituted in, the arguments become known and the body folds. It is also what
//! makes devirtualization possible: a dictionary parameter bound to a constant dictionary turns the
//! callee's `dict_entry`s into known functions, and its indirect calls into direct ones.
//!
//! **This handles the shape that needs no control-flow surgery**: a callee of a single block ending
//! in `return`, called by an ordinary `call` operation. Such a callee is necessarily infallible — a
//! source-fallible operation needs an `invoke` terminator, and so a second block — which means no
//! error edge has to be rewired and no block has to be split. The callee's operations are spliced
//! in place of the call, with:
//!
//! - **parameters substituted by the caller's operands.** A call's operands are exactly the
//!   callee's parameters in signature order (`@extra`, `@arg`, `@ret`), so the substitution is
//!   positional. It is also why inlining hands folding known arguments: what was `%pN` becomes the
//!   caller's place.
//! - **registers renumbered** into the caller, and **constants merged** into its pool.
//! - **the body bracketed by `stack_save`/`stack_restore`**, because the callee's `alloca`s now
//!   live in the caller's frame and nothing else would reclaim them at the point its frame used to
//!   end.
//!
//! Multi-block callees — everything with a branch, a loop, or an error edge — need block splitting
//! and `propagate_error` rewiring, and are left alone for now.
//!
//! See `doc/plans/partial-evaluation.md`.
#![allow(dead_code)]

use rustc_hash::FxHashMap;

use crate::{
    CompilerSession,
    compiler::MirOptimization,
    mir::{
        self, Function, Operation, OperationKind, OperationResult, edit::FunctionEdit,
        terminator::TerminatorKind,
    },
    module::{FunctionId, ModuleEnv, ModuleId, id::Id},
    types::{r#type::CallResultConvention, type_like::TypeLike},
};

use super::budget;

/// A call site to replace with its callee's body.
struct Inlining {
    block: mir::BlockId,
    /// Index of the call within its block.
    index: usize,
    callee: FunctionId,
}

/// Inlines what can be inlined in `func`, returning a rewritten function if anything was.
pub(crate) fn inline_function(
    func: &Function,
    original_size: usize,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
) -> Option<Function> {
    let _ = module_id;
    let sites = plan_inlinings(func, original_size, session);
    if sites.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    // Later indices first, so splicing one call does not move the ones still to be done.
    for site in sites.into_iter().rev() {
        let Some(body) = callee_body(session, site.callee) else {
            continue;
        };
        let spliced = splice(&mut edit, &body, site.block, site.index, env);
        let block = edit.block_mut(site.block);
        block.operations.splice(site.index..=site.index, spliced);
    }
    Some(edit.finish(env))
}

/// Chooses the call sites to inline.
///
/// `original_size` is the function's size before *any* round ran, so the growth budget bounds the
/// whole of optimization rather than each round — otherwise a function could grow by the budget
/// again on every round, and the cap would only bound growth per round.
fn plan_inlinings(
    func: &Function,
    original_size: usize,
    session: &CompilerSession,
) -> Vec<Inlining> {
    let mut sites = Vec::new();
    let mut size = function_size(func);

    for block in func.blocks() {
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let OperationKind::Call { ty } = &operation.kind else {
                continue;
            };
            if ty.result_convention != CallResultConvention::Value {
                continue;
            }
            let mir::Value::Function(callee) = &operation.operands[0] else {
                continue;
            };
            let Some(body) = callee_body(session, *callee) else {
                continue;
            };
            if !is_inlinable(&body) {
                continue;
            }
            let callee_size = function_size(&body);
            // The call goes, the callee's operations and a `stack_save`/`stack_restore` pair
            // arrive.
            let cost = callee_size + 1;
            if callee_size > budget::INLINE_CALLEE_OPERATIONS
                || size + cost > original_size + budget::INLINE_FUNCTION_GROWTH
            {
                continue;
            }
            size += cost;
            sites.push(Inlining {
                block,
                index,
                callee: *callee,
            });
        }
    }
    sites
}

/// The callee's body, read from the raw stage.
///
/// Deliberately raw rather than optimized: the driver reads raw bodies everywhere so that a result
/// never depends on the order functions are optimized in. Folding runs over the inlined body
/// afterwards, which recovers most of what an already-simplified callee would have given.
fn callee_body(session: &CompilerSession, callee: FunctionId) -> Option<Function> {
    session
        .mir_artifacts_for(callee.module, MirOptimization::Disabled)?
        .get(callee.function)
        .cloned()
}

/// Whether this callee is one of the shapes that needs no control-flow surgery, *and* whose body
/// means the same thing in the caller as it did at home.
///
/// The second half is the subtle one. An operation carries types — `clone_closure_env { ty }`,
/// `alloca { ty }`, a call's `CallImplType` — and those are written in the *callee's* type
/// environment. Copying them into a caller with a different instantiation silently reinterprets
/// them: inlining a generic `Value<A>::clone` into a concrete caller makes its `A` mean whatever
/// `A` happens to be there. Making that sound requires substituting the call site's instantiation
/// through the body, which is what specialization does — so until then, only callees that carry no
/// type variables at all are inlined.
fn is_inlinable(body: &Function) -> bool {
    if body.parameters().iter().any(|parameter| {
        matches!(parameter.kind, mir::ParameterKind::Dictionary) || !parameter.ty.is_constant()
    }) {
        return false;
    }
    has_inlinable_shape(body)
}

/// Whether the body needs no control-flow surgery to splice.
fn has_inlinable_shape(body: &Function) -> bool {
    let mut blocks = body.blocks();
    let Some(entry) = blocks.next() else {
        return false;
    };
    if blocks.next().is_some() {
        return false;
    }
    let block = body.block(entry);
    if !matches!(block.terminator().kind, TerminatorKind::Return) {
        return false;
    }
    // A recursive callee carries a call-depth guard; the plan's restriction is to assert its
    // absence rather than handle it, and a single-block body cannot contain a `yield` either.
    block.operations().iter().all(|operation| {
        !matches!(
            operation.kind,
            OperationKind::CheckCallDepth | OperationKind::Project { .. }
        )
    })
}

fn function_size(func: &Function) -> usize {
    func.blocks()
        .map(|block| func.block(block).operations().len())
        .sum()
}

/// Builds the operations that replace the call: the callee's body, remapped into the caller and
/// bracketed so its storage is reclaimed.
fn splice(
    edit: &mut FunctionEdit,
    body: &Function,
    block: mir::BlockId,
    index: usize,
    env: ModuleEnv<'_>,
) -> Vec<Operation> {
    let call = edit.block(block).operations[index].clone();
    let span = call.span;

    // A call's operands are its callee followed by the callee's parameters in signature order, so
    // parameter `i` is operand `i + 1`.
    let arguments: Vec<mir::Value> = call.operands[1..].to_vec();
    let mut constants: FxHashMap<usize, mir::Value> = FxHashMap::default();
    let mut registers: FxHashMap<mir::ValueId, mir::ValueId> = FxHashMap::default();

    let mut spliced = Vec::with_capacity(function_size(body) + 2);
    let mut marker = Operation::stack_save(span);
    let marker_id = edit.new_value();
    marker.assign_result_id(Some(marker_id));
    spliced.push(marker);

    for operation in body.block(body.entry()).operations() {
        let operands = operation
            .operands
            .iter()
            .map(|operand| match operand {
                mir::Value::Parameter(id) => arguments[id.as_index()].clone(),
                mir::Value::Register(id) => mir::Value::Register(registers[id]),
                mir::Value::Constant(id) => constants
                    .entry(id.as_index())
                    .or_insert_with(|| {
                        let constant = body.constant(*id);
                        mir::Value::Constant(edit.add_constant(
                            constant.ty,
                            constant.representation.clone(),
                            &env,
                        ))
                    })
                    .clone(),
                other => other.clone(),
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let mut inlined = Operation::from_parts(operation.span, operands, operation.kind.clone());
        if inlined.result() != OperationResult::Nothing
            && let Some(source) = operation.result_id()
        {
            let fresh = edit.new_value();
            registers.insert(source, fresh);
            inlined.assign_result_id(Some(fresh));
        }
        spliced.push(inlined);
    }

    spliced.push(Operation::stack_restore(
        span,
        mir::Value::Register(marker_id),
    ));
    spliced
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("inline", src)
    }

    /// What inlining is for: the callee's body arrives with the caller's operands substituted in,
    /// so its argument becomes known and folding finishes the job.
    #[test]
    fn inlining_a_callee_makes_its_argument_known() {
        let module = optimized(
            "fn double(x: int) -> int { x + x }\nfn main() -> int { let n = 21; double(n) }",
        );
        let main = module.split("fn main").nth(1).expect("main");
        assert!(
            !main.contains("call "),
            "the call must be inlined and then folded away:\n{main}"
        );
        assert!(
            main.contains("= 42"),
            "the result must be constant:\n{main}"
        );
    }

    /// A generic callee is not inlined: its operations carry types written in its own type
    /// environment, which would mean something else in the caller. Substituting them through the
    /// call site's instantiation is specialization, a later phase.
    ///
    /// The argument is deliberately unknown — with a constant argument the call folds outright and
    /// never reaches the inliner.
    #[test]
    fn a_generic_callee_is_not_inlined() {
        let module = optimized("fn identity(x) { x }\nfn use_it(n: int) -> int { identity(n) }");
        let caller = module.split("fn use_it").nth(1).expect("use_it");
        assert!(
            caller.contains("call "),
            "a generic callee must be left alone:\n{caller}"
        );
    }
}
