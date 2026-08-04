// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Constant folding of calls: run a call at compile time and store its result instead.
//!
//! A call folds when all of the following hold. Each is a refusal reason the fold report will name.
//!
//! - the callee is a direct [`mir::Value::Function`] — an indirect call needs devirtualization first;
//! - every visible argument arrives by [`ArgConvention::Let`], so nothing is written back;
//! - every argument place holds a known literal, and every hidden evidence operand is a constant
//!   dictionary;
//! - the call's effects and result convention permit compile-time evaluation ([`const_eval`]);
//! - the evaluation succeeds, and its result can be expressed as MIR ([`reify`]).
//!
//! The rewrite is then local: `call f(a, b, ret)` becomes `store @cN to ret`. Both forms initialize
//! the same slot and neither takes ownership of anything the caller held — argument conventions
//! leave ownership with the caller — so the surrounding `alloca`/`store`/`drop` scaffolding stays
//! correct while becoming dead. Removing it is a separate cleanup pass.
//!
//! Folding runs against an immutable function and returns a rewritten one, so the analysis it reads
//! is never stale with respect to the edits it makes. Within a block, a fold updates the local state
//! immediately, so a chain of calls in straight-line code folds in one pass; a chain that crosses
//! blocks folds over the driver's rounds.
//!
//! See `doc/plans/partial-evaluation.md`.
#![allow(dead_code)]

use crate::{
    CompilerSession,
    hir::function::ArgConvention,
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        const_eval::{ConstArgument, ConstEvaluator, NotFoldable},
        edit::FunctionEdit,
        reify::{Reification, reify},
        value::Constant,
    },
    module::{ModuleEnv, ModuleId},
    types::r#type::CallImplType,
};

use super::dataflow::{self, Const, Fact, State};

/// A call site the pass decided to replace, and what to replace it with.
struct Fold {
    block: BlockId,
    /// Index of the operation within its block.
    index: usize,
    /// The place the folded call would have written its result into.
    destination: mir::Value,
    constant: Constant,
}

/// Folds every call in `func` that can be folded, returning a rewritten function if any was.
pub(crate) fn fold_function(
    func: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
) -> Option<Function> {
    let folds = plan_folds(func, env, session, module_id);
    if folds.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for fold in folds {
        let constant = edit.add_constant(fold.constant.ty, fold.constant.representation, &env);
        let span = edit.block(fold.block).operations[fold.index].span;
        edit.block_mut(fold.block).replace_operation(
            fold.index,
            Operation::store(span, mir::Value::Constant(constant), fold.destination),
        );
    }
    Some(edit.finish(env))
}

/// Decides which calls to fold, without touching the function.
fn plan_folds(
    func: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
) -> Vec<Fold> {
    let analysis = dataflow::analyze(func);
    let evaluator = ConstEvaluator::new(module_id, session);
    let mut folds = Vec::new();

    for block in func.blocks() {
        // Replaying a block yields the state before each operation; a fold discovered inside the
        // block updates that state as it goes, so `2 + 3` then `* 7` folds in a single walk.
        let mut folded_here: Vec<(usize, Constant, mir::Value)> = Vec::new();
        let mut local: Option<State> = None;
        // A source-fallible call lives in the block's `Invoke` terminator rather than its operation
        // list, and replacing it means rewriting control flow — the terminator becomes a `goto` and
        // the error edge dies. Until that rewrite exists, such a call is left alone.
        let operation_count = func.block(block).operations().len();
        analysis.replay(func, block, |index, operation, state| {
            let state = local.as_ref().unwrap_or(state);
            if index >= operation_count {
                return;
            }
            let OperationKind::Call { ty } = &operation.kind else {
                return;
            };
            let Ok(constant) = try_fold_call(func, operation, ty, state, &evaluator, &env) else {
                return;
            };
            let Some(call) = dataflow::call_operands(&operation.operands, ty) else {
                return;
            };
            let destination = call.result.clone();
            // Teach the rest of the walk what this call now produces.
            let mut updated = state.clone();
            if let Some(key) = updated.place_of(&destination) {
                updated.set_place_known(
                    key,
                    Fact::Known(Const::Literal(constant.representation.clone())),
                );
            }
            local = Some(updated);
            folded_here.push((index, constant, destination));
        });
        for (index, constant, destination) in folded_here {
            folds.push(Fold {
                block,
                index,
                destination,
                constant,
            });
        }
    }
    folds
}

/// Evaluates one call site at compile time and expresses the result as a constant, or explains why
/// it cannot be.
fn try_fold_call(
    func: &Function,
    operation: &Operation,
    ty: &CallImplType,
    state: &State,
    evaluator: &ConstEvaluator<'_>,
    env: &ModuleEnv<'_>,
) -> Result<Constant, NotFoldable> {
    let Some(call) = dataflow::call_operands(&operation.operands, ty) else {
        return Err(NotFoldable::UnsupportedConvention);
    };
    let mir::Value::Function(callee) = call.callee else {
        // An indirect callee: devirtualization has not (or cannot) resolve it.
        return Err(NotFoldable::NoBody);
    };

    let mut arguments = Vec::with_capacity(call.extras.len() + call.arguments.len());
    for extra in call.extras {
        match extra {
            mir::Value::Dictionary(id) => arguments.push(ConstArgument::Dictionary(*id)),
            // A forwarded dictionary parameter is not known here; specialization is a later phase.
            _ => return discard(arguments, NotFoldable::Effectful),
        }
    }
    for (operand, convention) in &call.arguments {
        // Write-back of a `MutableRef` argument is out of scope: the callee's writes would have to
        // be reified too.
        if !matches!(convention, ArgConvention::Let) {
            return discard(arguments, NotFoldable::UnsupportedConvention);
        }
        let known = state
            .place_of(operand)
            .map(|key| state.place(&key))
            .and_then(|fact| match fact {
                Fact::Known(Const::Literal(literal)) => Some(literal),
                _ => None,
            });
        match known {
            Some(literal) => arguments.push(ConstArgument::Value(literal.into_value())),
            None => return discard(arguments, NotFoldable::Failed),
        }
    }

    let _ = func;
    let value = evaluator.try_call(
        *callee,
        ty.effects(),
        ty.result_convention,
        ty.ret(),
        arguments,
        operation.span,
    )?;
    let reified = reify(&value, ty.ret(), env);
    value.discard_storage();
    match reified? {
        Reification::Constant(constant) => Ok(constant),
        // A function operand needs no constant, but replacing a call with one is a different
        // rewrite than storing a literal; leave it to the devirtualization work.
        Reification::Operand(_) => Err(NotFoldable::NotReifiable),
    }
}

/// Releases arguments prepared for a call that is not made after all.
fn discard(arguments: Vec<ConstArgument>, reason: NotFoldable) -> Result<Constant, NotFoldable> {
    ConstArgument::discard_all(arguments);
    Err(reason)
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization, module::Path, ustr,
    };

    /// The gate example: constant arithmetic collapses into a single store into `@ret`.
    #[test]
    fn constant_arithmetic_folds_to_a_store() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let optimized = session.emit_mir("fold", "fn main() -> int { let x = 2 + 3; x * 7 }");

        let main = optimized
            .split("fn main")
            .nth(1)
            .expect("the module defines main");
        assert!(
            !main.contains("call "),
            "every call of a constant expression must fold:\n{main}"
        );
        assert!(
            main.contains("store @c") && main.contains("to %p0"),
            "the result must be stored into the return place:\n{main}"
        );
        let _ = ustr("");
        let _ = ExecutionTarget::Mir;
        let _ = Path::single_str("x");
    }
}
