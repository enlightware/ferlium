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
        terminator::{Terminator, TerminatorKind},
        value::Constant,
    },
    module::{ModuleEnv, ModuleId},
    types::r#type::{CallImplType, Type},
};

use super::dataflow::{self, Const, Fact, RegisterFact, State};

/// A call site the pass decided to replace, and what to replace it with.
struct Fold {
    block: BlockId,
    /// Index of the operation within its block.
    index: usize,
    /// The place the folded call would have written its result into.
    destination: mir::Value,
    constant: Constant,
}

/// What one pass over a function decided to rewrite.
#[derive(Default)]
struct Plan {
    calls: Vec<Fold>,
    /// Conditional branches whose condition is known, and the successor they always take.
    branches: Vec<(BlockId, BlockId)>,
}

impl Plan {
    fn is_empty(&self) -> bool {
        self.calls.is_empty() && self.branches.is_empty()
    }
}

/// Folds what can be folded in `func`, returning a rewritten function if anything was.
pub(crate) fn fold_function(
    func: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
) -> Option<Function> {
    let plan = plan_folds(func, env, session, module_id);
    if plan.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for fold in plan.calls {
        let constant = edit.add_constant(fold.constant.ty, fold.constant.representation, &env);
        let span = edit.block(fold.block).operations[fold.index].span;
        edit.block_mut(fold.block).replace_operation(
            fold.index,
            Operation::store(span, mir::Value::Constant(constant), fold.destination),
        );
    }
    for (block, target) in plan.branches {
        let span = edit.block(block).terminator.span;
        edit.block_mut(block).terminator = Terminator::goto(span, target);
    }
    // Folding a branch is what strands blocks, so the pass prunes once its edits have settled.
    edit.remove_unreachable_blocks();
    Some(edit.finish(env))
}

/// Decides what to rewrite, without touching the function.
fn plan_folds(
    func: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
) -> Plan {
    let analysis = dataflow::analyze(func);
    let evaluator = ConstEvaluator::new(module_id, session);
    let mut plan = Plan::default();

    for block in func.blocks() {
        // Stepping from the block's entry state, rather than only reading it, lets a fold teach the
        // rest of the walk what it produced: `2 + 3` then `* 7` folds in one pass.
        let mut state = analysis.entry_state(block);
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            if let OperationKind::Call { ty } = &operation.kind
                && let Ok(constant) = try_fold_call(operation, ty, &state, &evaluator, &env)
                && let Some(call) = dataflow::call_operands(&operation.operands, ty)
            {
                let destination = call.result.clone();
                if let Some(key) = state.place_of(&destination) {
                    state.set_place_known(
                        key,
                        Fact::Known(Const::Literal(constant.representation.clone())),
                    );
                }
                plan.calls.push(Fold {
                    block,
                    index,
                    destination,
                    constant,
                });
                continue;
            }
            analysis.step(func, operation, &mut state);
        }

        // A source-fallible call lives in the terminator rather than the operation list, and
        // folding it means rewriting control flow — the error edge dies. That rewrite is not done
        // yet, so such a call is left alone; only a decided branch is rewritten here.
        if let TerminatorKind::CondBr {
            condition,
            then_target,
            else_target,
        } = &basic_block.terminator().kind
            && let Some(taken) = known_condition(condition, &state)
        {
            plan.branches
                .push((block, if taken { *then_target } else { *else_target }));
        }
    }
    plan
}

/// The value of a branch condition, when the analysis knows it.
fn known_condition(condition: &mir::Value, state: &State) -> Option<bool> {
    let mir::Value::Register(id) = condition else {
        return None;
    };
    match state.register(*id)? {
        RegisterFact::Value(Fact::Known(Const::Literal(literal))) => {
            literal.as_primitive_ty::<bool>().copied()
        }
        _ => None,
    }
}

/// Evaluates one call site at compile time and expresses the result as a constant, or explains why
/// it cannot be.
fn try_fold_call(
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

    // A unit result carries no information, so replacing such a call with a store of `()` gains
    // nothing — and it would delete a call the host may be relying on. `Value::drop` is declared
    // effect-free by its trait, so a host that instruments drops *must* declare that instrumentation
    // pure; folding pure unit-returning calls would silently remove it for no benefit.
    if ty.ret() == Type::unit() {
        return discard(arguments, NotFoldable::UnsupportedConvention);
    }

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
    use crate::{CompilerSession, MirOptimization};

    fn optimized_main(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir("fold", src);
        module
            .split("fn main")
            .nth(1)
            .expect("the module defines main")
            .to_string()
    }

    /// A branch whose condition is known becomes a jump, and the arm not taken disappears — with
    /// the constants only it named.
    #[test]
    fn a_known_condition_drops_the_arm_not_taken() {
        let main = optimized_main("fn main() -> int { if true { 1 } else { 2 } }");
        assert!(
            !main.contains("condbr"),
            "the branch must be decided:\n{main}"
        );
        assert!(
            !main.contains("= 2"),
            "the untaken arm's constant must be pruned:\n{main}"
        );
        assert!(main.contains("= 1"), "{main}");
    }

    /// The gate example: constant arithmetic collapses into a single store into `@ret`.
    #[test]
    fn constant_arithmetic_folds_to_a_store() {
        let main = optimized_main("fn main() -> int { let x = 2 + 3; x * 7 }");
        assert!(
            !main.contains("call "),
            "every call of a constant expression must fold:\n{main}"
        );
        assert!(
            main.contains("store @c") && main.contains("to %p0"),
            "the result must be stored into the return place:\n{main}"
        );
    }
}
