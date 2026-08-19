// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Constant and semantic folding of calls.
//!
//! A call folds when all of the following hold. Each is a refusal reason the fold report will name.
//!
//! - the callee is a direct [`mir::Value::Function`] — an indirect call needs devirtualization first;
//! - every visible argument arrives by [`ArgConvention::Let`], so nothing is written back;
//! - every argument place holds a known literal or constructive array, and every hidden evidence
//!   operand is a constant dictionary;
//! - the call's effects and result convention permit compile-time evaluation ([`const_eval`]);
//! - the evaluation succeeds, and its result can be expressed as MIR ([`reify`]).
//!
//! A second path needs only the callee identity and the arguments mentioned by a documented
//! identity. It simplifies concrete integer and float std calls such as `x * 1`, `x - 0` and
//! `cmp(x, x)` even when `x` is unknown. Float identities are representation-preserving: signed
//! zero deliberately excludes `x + 0.0` and `x * 0.0`.
//!
//! The rewrite is then local: `call f(a, b, ret)` becomes either `store @cN to ret` or a
//! `build_array` into `ret`. Both forms initialize the same slot and neither takes ownership of
//! anything the caller held — argument conventions leave ownership with the caller — so the
//! surrounding construction/drop scaffolding stays correct while becoming dead. Removing it is a
//! separate cleanup pass.
//!
//! Folding runs against an immutable function and returns a rewritten one, so the analysis it reads
//! is never stale with respect to the edits it makes. Within a block, a fold updates the local state
//! immediately, so a chain of calls in straight-line code folds in one pass; a chain that crosses
//! blocks folds over the driver's rounds.

#![allow(dead_code)]

use rustc_hash::FxHashSet;
use ustr::ustr;

use crate::{
    CompilerSession, Location,
    containers::b,
    hir::{
        function::ArgConvention,
        value::{LiteralValue, VariantPayloadStorage},
    },
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        const_eval::{ConstArgument, ConstEvaluator, NotFoldable},
        edit::FunctionEdit,
        reify::{Reification, reify},
        terminator::{Terminator, TerminatorKind},
    },
    module::{FunctionId, ModuleEnv, ModuleId, id::Id},
    std::{
        array::{array_type, array_value_from_vec},
        math::Float,
        ordering::{ORDERING_EQUAL, ordering_type},
    },
    types::r#type::{CallImplType, CallResultConvention, Type},
};

use super::{
    dataflow::{self, Analysis, Const, Fact, Root, State},
    known_callee::{KnownCallee, KnownCallees},
    site::OperationIndex,
};

/// A call result the optimizer can materialize without knowing every argument.
#[derive(Debug)]
enum CallRewrite {
    /// Ordinary full constant evaluation.
    Reification(Reification),
    /// A known identity says the result is one of the call's input places.
    Copy(mir::Value),
    /// A reflexive comparison returns the payload-free `Equal` case.
    EqualOrdering,
    /// A boolean negation, expressed as the comparison MIR already has.
    Negate(mir::Value),
}

/// The two inputs needed to recognize a known call, kept together at folding entry points.
#[derive(Clone, Copy)]
pub(crate) struct KnownCallSemantics<'a> {
    callees: &'a KnownCallees,
    original_of: &'a dyn Fn(FunctionId) -> Option<FunctionId>,
}

impl<'a> KnownCallSemantics<'a> {
    pub(crate) fn new(
        callees: &'a KnownCallees,
        original_of: &'a dyn Fn(FunctionId) -> Option<FunctionId>,
    ) -> Self {
        Self {
            callees,
            original_of,
        }
    }

    fn resolve(self, callee: FunctionId) -> Option<KnownCallee> {
        self.callees.resolve(callee, self.original_of)
    }
}

/// A call site the pass decided to replace, and what to replace it with.
struct Fold {
    block: BlockId,
    /// Index of the operation within its block.
    index: OperationIndex,
    /// The place the folded call would have written its result into.
    destination: mir::Value,
    result: CallRewrite,
}

/// A source-fallible call the pass decided to replace, in its block's `Invoke` terminator.
struct InvokeFold {
    block: BlockId,
    destination: mir::Value,
    result: Reification,
    /// The successor the call would have taken on success — where control goes now that it cannot
    /// fail.
    normal: BlockId,
}

/// An indirect dispatch whose callee the analysis resolved, and the function to name directly
/// instead. `operand` is the callee's index, which differs per operation kind.
struct Devirtualization {
    site: Site,
    operand: usize,
    callee: FunctionId,
}

/// Where a dispatch sits in its block: an ordinary operation, or the `Invoke` terminator.
#[derive(Clone, Copy)]
enum Site {
    Operation {
        block: BlockId,
        index: OperationIndex,
    },
    Terminator {
        block: BlockId,
    },
}

impl Site {
    fn block(self) -> BlockId {
        match self {
            Site::Operation { block, .. } | Site::Terminator { block } => block,
        }
    }
}

/// What one pass over a function decided to rewrite.
#[derive(Default)]
pub(crate) struct Plan {
    calls: Vec<Fold>,
    invokes: Vec<InvokeFold>,
    /// Conditional branches whose condition is known, and the successor they always take.
    branches: Vec<(BlockId, BlockId)>,
    /// Whether anything planned here can enable a further rewrite. See
    /// [`Folded::warrants_another_round`].
    warrants_another_round: bool,
}

impl Plan {
    /// How many call sites this plan would fold — what the report calls round-exhausted when it
    /// finds any in an already-optimized body.
    pub(crate) fn foldable_calls(&self) -> usize {
        self.calls.len() + self.invokes.len()
    }

    fn is_empty(&self) -> bool {
        self.calls.is_empty() && self.invokes.is_empty() && self.branches.is_empty()
    }
}

/// Everything a call site is judged against, gathered once per function.
///
/// The evaluator, environment, and dataflow analysis decide whether a call folds. Refusal-only
/// provenance is absent from normal optimization and constructed only for an optimization report.
struct FoldContext<'a> {
    evaluator: ConstEvaluator<'a>,
    env: ModuleEnv<'a>,
    analysis: Analysis,
    known_calls: KnownCallSemantics<'a>,
    refusal: Option<RefusalContext>,
}

struct RefusalContext {
    /// The `alloca`s a call writes its result into. See [`call_destinations`].
    call_destinations: FxHashSet<mir::ValueId>,
}

/// Why one call site was not folded, and where it is.
pub(crate) struct Refusal {
    pub site: Location,
    pub callee: Option<FunctionId>,
    pub reason: NotFoldable,
}

/// The result of one folding pass over a function.
pub(crate) struct Folded {
    pub body: Function,
    /// Whether this rewrite may enable further folding or inlining, and so warrants another round.
    ///
    /// A round is expensive — a full fold-specialize-CSE-inline cycle — so one is bought only by a
    /// rewrite that hands the *next* round something it did not have. A fold that produces a
    /// constant does, and so does a decided branch, which deletes an arm.
    ///
    /// **A rewrite whose result stays unknown does not.** Replacing a call with a copy of an
    /// unknown argument, or with a comparison of one, is a smaller body computing the same unknown
    /// value: the next round's analysis learns nothing from it. Measured on std, granting rounds
    /// for those cost 0.14% of MIR optimization time and changed no optimized body.
    ///
    /// **Devirtualization does not either.** Naming a callee directly is progress, but the callees
    /// a dictionary entry resolves to are overwhelmingly natives, which cannot be inlined and only
    /// fold with known arguments — so granting a round for one buys a cycle that almost never
    /// finds anything. Measured, that was +19.2% of compile time for half a percent of run time.
    pub warrants_another_round: bool,
}

/// Folds what can be folded in `func`, returning a rewritten function if anything was.
pub(crate) fn fold_function(
    func: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    known_calls: KnownCallSemantics<'_>,
) -> Option<Folded> {
    let (plan, devirtualizations) =
        plan_folds_and_devirtualizations(func, env, session, module_id, known_calls);
    if plan.is_empty() && devirtualizations.is_empty() {
        return None;
    }
    let warrants_another_round = plan.warrants_another_round;

    let mut edit = FunctionEdit::new(func.clone());
    // Devirtualization first: it only rewrites a callee operand in place, while a fold below may
    // splice one call into two operations and shift every later index of its block. Both were
    // planned against the same body, and no operation is in both plans.
    apply_devirtualizations(&mut edit, devirtualizations);
    // A reflexive comparison expands one call into `variant Equal; store`, so apply sites in
    // reverse order and splice without invalidating a later index planned in the same block.
    for fold in plan.calls.into_iter().rev() {
        let index = fold.index.as_index();
        let span = edit.block(fold.block).operations[index].span;
        let replacements =
            materialize_call_rewrite(&mut edit, span, fold.result, fold.destination, env);
        edit.block_mut(fold.block)
            .operations
            .splice(index..=index, replacements);
    }
    for invoke in plan.invokes {
        let span = edit.block(invoke.block).terminator.span;
        // The call becomes an ordinary store at the end of the block, and the terminator loses its
        // error edge: an evaluated call cannot fail. Appending keeps the indices the operation
        // folds above were planned against.
        let replacement =
            materialize_reification(&mut edit, span, invoke.result, invoke.destination, env);
        let block = edit.block_mut(invoke.block);
        block.operations.push(replacement);
        block.terminator = Terminator::goto(span, invoke.normal);
    }
    for (block, target) in plan.branches {
        let span = edit.block(block).terminator.span;
        edit.block_mut(block).terminator = Terminator::goto(span, target);
    }
    // Folding a branch or an invoke is what strands blocks — an error edge that dies leaves its
    // cleanup pad unreachable — so the pass prunes once its edits have settled. Resolving a
    // `condbr` also leaves its surviving target with a single predecessor, so merging follows the
    // prune, in this pass's own edit: a separate open-and-verify cycle for it costs more
    // than the merge saves.
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some(Folded {
        body: edit.finish_unverified(),
        warrants_another_round,
    })
}

/// Turns either full evaluation or a partial known-call identity into MIR operations.
fn materialize_call_rewrite(
    edit: &mut FunctionEdit,
    span: Location,
    rewrite: CallRewrite,
    destination: mir::Value,
    env: ModuleEnv<'_>,
) -> Vec<Operation> {
    match rewrite {
        CallRewrite::Reification(reification) => {
            vec![materialize_reification(
                edit,
                span,
                reification,
                destination,
                env,
            )]
        }
        CallRewrite::Copy(source) => vec![Operation::memcpy(span, source, destination)],
        CallRewrite::Negate(source) => {
            let mut comparison = Operation::compare_eq(
                span,
                source,
                mir::Value::Pattern(b(LiteralValue::new_native(false))),
            );
            let value = edit.new_value();
            comparison.assign_result_id(Some(value));
            vec![
                comparison,
                Operation::store(span, mir::Value::Register(value), destination),
            ]
        }
        CallRewrite::EqualOrdering => {
            let mut variant = Operation::variant(
                span,
                ustr(ORDERING_EQUAL),
                ordering_type(),
                Some(VariantPayloadStorage::Inline),
                None,
            );
            let value = edit.new_value();
            variant.assign_result_id(Some(value));
            vec![
                variant,
                Operation::store(span, mir::Value::Register(value), destination),
            ]
        }
    }
}

/// Turns a compile-time result into the one MIR operation that initializes its destination.
fn materialize_reification(
    edit: &mut FunctionEdit,
    span: Location,
    reification: Reification,
    destination: mir::Value,
    env: ModuleEnv<'_>,
) -> Operation {
    match reification {
        Reification::Constant(constant) => {
            let id = edit.add_constant(constant.ty, constant.representation, &env);
            Operation::store(span, mir::Value::Constant(id), destination)
        }
        Reification::Array {
            element_ty,
            elements,
        } => {
            let elements = elements.into_vec().into_iter().map(|representation| {
                let id = edit.add_constant(element_ty, representation, &env);
                mir::Value::Constant(id)
            });
            Operation::build_array(span, element_ty, elements, destination)
        }
        Reification::Operand(_) => {
            unreachable!("call folding admits only destination-initializing reifications")
        }
    }
}

/// Names callees resolved through constant dictionary entries after the optimization round budget
/// was exhausted.
///
/// Folding normally performs this rewrite while it already owns the dataflow analysis. Inlining can
/// expose one last `dict_entry`/dispatch pair in the last permitted round, however, and DCE can
/// remove the entry only after this has made the dispatch direct. The driver does not call this
/// after genuine convergence: the final no-change fold already saw the settled body.
pub(crate) fn devirtualize_known_callees(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    if !may_have_devirtualization(func) {
        return None;
    }
    let devirtualizations = plan_devirtualizations(func, env);
    if devirtualizations.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    apply_devirtualizations(&mut edit, devirtualizations);
    Some(edit.finish_unverified())
}

/// Decides what to rewrite, without touching the function.
///
/// `refusals`, when present, collects why each call site was left alone — the optimization report
/// runs this over an already-optimized body precisely so its answers cannot drift from the pass's.
pub(crate) fn plan_folds(
    func: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    known_calls: KnownCallSemantics<'_>,
    refusals: &mut Option<&mut Vec<Refusal>>,
) -> Plan {
    plan_folds_with(
        func,
        env,
        session,
        module_id,
        known_calls,
        refusals,
        &mut None,
    )
}

/// Plans folds and devirtualizations in one walk.
///
/// **Devirtualization rides along with folding rather than running as a pass of its own**, and the
/// reason is entirely the dataflow analysis: resolving a callee needs exactly the analysis folding
/// has already built, and that analysis *is* the cost. Riding along is therefore the main path. The
/// final devirtualization sweep below exists only for dictionary-entry callees exposed in an
/// exhausted last round, behind a cheap syntactic pre-filter and before DCE removes the stranded
/// entry.
///
/// What it must not do is claim a *round*: see [`Folded::warrants_another_round`].
fn plan_folds_and_devirtualizations(
    func: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    known_calls: KnownCallSemantics<'_>,
) -> (Plan, Vec<Devirtualization>) {
    let mut devirtualizations = Vec::new();
    let plan = plan_folds_with(
        func,
        env,
        session,
        module_id,
        known_calls,
        &mut None,
        &mut Some(&mut devirtualizations),
    );
    (plan, devirtualizations)
}

fn plan_devirtualizations(func: &Function, env: ModuleEnv<'_>) -> Vec<Devirtualization> {
    let analysis = dataflow::analyze(func, env);
    let mut devirtualizations = Vec::new();
    for block in func.blocks() {
        let mut state = analysis.entry_state(block);
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            if let Some((operand, callee)) = resolved_callee(operation, &state, &analysis) {
                devirtualizations.push(Devirtualization {
                    site: Site::Operation {
                        block,
                        index: OperationIndex::from_index(index),
                    },
                    operand,
                    callee,
                });
            }
            analysis.step(func, env, operation, &mut state);
        }
        if let TerminatorKind::Invoke { operation, .. } = &basic_block.terminator().kind
            && let Some((operand, callee)) = resolved_callee(operation, &state, &analysis)
        {
            devirtualizations.push(Devirtualization {
                site: Site::Terminator { block },
                operand,
                callee,
            });
        }
    }
    devirtualizations
}

fn may_have_devirtualization(func: &Function) -> bool {
    let mut has_dict_entry = false;
    let mut has_indirect_dispatch = false;
    for block in func.blocks() {
        let basic_block = func.block(block);
        for operation in basic_block.operations() {
            has_dict_entry |= matches!(operation.kind, OperationKind::DictEntry { .. });
            has_indirect_dispatch |= dispatch_callee(operation).is_some_and(is_indirect_callee);
            if has_dict_entry && has_indirect_dispatch {
                return true;
            }
        }
        if let TerminatorKind::Invoke { operation, .. } = &basic_block.terminator().kind {
            has_indirect_dispatch |= dispatch_callee(operation).is_some_and(is_indirect_callee);
            if has_dict_entry && has_indirect_dispatch {
                return true;
            }
        }
    }
    false
}

fn dispatch_callee(operation: &Operation) -> Option<&mir::Value> {
    operation.operands.get(callee_operand_index(operation)?)
}

fn is_indirect_callee(callee: &mir::Value) -> bool {
    !matches!(callee, mir::Value::Function(_))
}

// Naming a resolved callee directly. The operand shape is unchanged — the verifier accepts a
// function or a function place in a callee position — so this touches nothing but that one operand.
// The `dict_entry` that produced the place is usually left unread by the rewrite, and `dce.rs`
// removes it.
fn apply_devirtualizations(edit: &mut FunctionEdit, devirtualizations: Vec<Devirtualization>) {
    for devirtualized in devirtualizations {
        let callee = mir::Value::Function(devirtualized.callee);
        let block = edit.block_mut(devirtualized.site.block());
        let operation = match devirtualized.site {
            Site::Operation { index, .. } => &mut block.operations[index.as_index()],
            Site::Terminator { .. } => match &mut block.terminator.kind {
                TerminatorKind::Invoke { operation, .. } => operation,
                _ => unreachable!("planned against this block's invoke terminator"),
            },
        };
        operation.operands[devirtualized.operand] = callee;
    }
}

fn plan_folds_with(
    func: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    known_calls: KnownCallSemantics<'_>,
    refusals: &mut Option<&mut Vec<Refusal>>,
    devirtualizations: &mut Option<&mut Vec<Devirtualization>>,
) -> Plan {
    // A report pays one scan for detailed classification; normal optimization carries none of this
    // provenance and does not classify unknown arguments it will not report.
    let refusal = refusals.is_some().then(|| RefusalContext {
        call_destinations: call_destinations(func),
    });
    let context = FoldContext {
        evaluator: ConstEvaluator::new(module_id, session),
        env,
        analysis: dataflow::analyze(func, env),
        known_calls,
        refusal,
    };
    let analysis = &context.analysis;
    let mut plan = Plan::default();

    for block in func.blocks() {
        // Stepping from the block's entry state, rather than only reading it, lets a fold teach the
        // rest of the walk what it produced: `2 + 3` then `* 7` folds in one pass.
        let mut state = analysis.entry_state(block);
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            if let OperationKind::Call { ty, .. } = &operation.kind
                && let Some(call) = dataflow::call_operands(&operation.operands, ty)
                && let Some(result) =
                    partial_call_outcome(operation, ty, &state, &context).or_else(|| {
                        fold_outcome(operation, ty, &state, &context, refusals)
                            .map(CallRewrite::Reification)
                    })
            {
                let destination = call.result.clone();
                // Only a rewrite that produced a value the next round can reason about buys one.
                plan.warrants_another_round |= yields_known_value(&result, &state, analysis);
                if let Some(place) = analysis.tracked_place_of(&destination) {
                    let fact = fact_for_call_rewrite(&result, &state, analysis);
                    analysis.set_place_known(&mut state, place, fact);
                }
                plan.calls.push(Fold {
                    block,
                    index: OperationIndex::from_index(index),
                    destination,
                    result,
                });
                continue;
            }
            if let Some(devirtualizations) = devirtualizations.as_mut()
                && let Some((operand, callee)) = resolved_callee(operation, &state, analysis)
            {
                devirtualizations.push(Devirtualization {
                    site: Site::Operation {
                        block,
                        index: OperationIndex::from_index(index),
                    },
                    operand,
                    callee,
                });
            }
            analysis.step(func, env, operation, &mut state);
        }

        match &basic_block.terminator().kind {
            // A source-fallible call lives in the terminator rather than the operation list.
            // Folding it rewrites control flow: the call cannot fail once it has been evaluated, so
            // the terminator becomes a jump to the normal successor and the error edge dies. An
            // evaluation that *does* fail is refused by `try_fold_call`, which is what keeps a
            // failure the program is entitled to observe.
            TerminatorKind::Invoke {
                operation, normal, ..
            } => {
                if let OperationKind::Call { ty, .. } = &operation.kind
                    && let Some(result) = fold_outcome(operation, ty, &state, &context, refusals)
                    && let Some(call) = dataflow::call_operands(&operation.operands, ty)
                {
                    // An evaluated fallible call yields a constant and removes an error edge.
                    plan.warrants_another_round = true;
                    plan.invokes.push(InvokeFold {
                        block,
                        destination: call.result.clone(),
                        result,
                        normal: *normal,
                    });
                } else if let Some(devirtualizations) = devirtualizations.as_mut()
                    && let Some((operand, callee)) = resolved_callee(operation, &state, analysis)
                {
                    devirtualizations.push(Devirtualization {
                        site: Site::Terminator { block },
                        operand,
                        callee,
                    });
                }
            }
            TerminatorKind::CondBr {
                condition,
                then_target,
                else_target,
            } => {
                if let Some(taken) = known_condition(condition, &state) {
                    // Deciding a branch deletes an arm, which is new for every later pass.
                    plan.warrants_another_round = true;
                    plan.branches
                        .push((block, if taken { *then_target } else { *else_target }));
                }
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup => {}
        }
    }
    plan
}

/// Whether a rewrite leaves behind a value the next round's analysis can reason about.
///
/// Deliberately answers without building the fact: a fact carries a cloned literal or array
/// recipe, and this is asked about every planned fold rather than only those writing a place the
/// analysis tracks.
fn yields_known_value(rewrite: &CallRewrite, state: &State, analysis: &Analysis) -> bool {
    match rewrite {
        CallRewrite::Reification(Reification::Constant(_) | Reification::Array { .. })
        | CallRewrite::EqualOrdering => true,
        // An operand reification names a place rather than a value, and both of the rewrites below
        // reproduce an argument the analysis already did not know.
        CallRewrite::Reification(Reification::Operand(_)) | CallRewrite::Negate(_) => false,
        CallRewrite::Copy(source) => analysis
            .tracked_place_of(source)
            .is_some_and(|place| state.place_is_known(place)),
    }
}

fn fact_for_call_rewrite(rewrite: &CallRewrite, state: &State, analysis: &Analysis) -> Fact {
    match rewrite {
        CallRewrite::Reification(reification) => fact_for_reification(reification),
        CallRewrite::Copy(source) => analysis
            .tracked_place_of(source)
            .map(|place| state.place(place))
            .unwrap_or_default(),
        CallRewrite::EqualOrdering => Fact::Known(Const::VariantTag(ustr(ORDERING_EQUAL))),
        // Only an unknown argument reaches the negation rewrite; a known one folds outright.
        CallRewrite::Negate(_) => Fact::Unknown,
    }
}

/// Applies known-callee rewrites that need less than the whole of the arguments.
///
/// Most are identities: the result is one of the inputs, or a constant, even though an argument is
/// unknown. [`BoolNot`](KnownCallee::BoolNot) is the exception, and is here for the same reason —
/// its meaning is a MIR operation rather than a call, so naming the callee is all it takes to stop
/// calling it.
///
/// The callee identity is the contract. Effects and convention are checked independently so adding
/// an entry from [`KnownCallees`] here never silently grants permission to discard an effect or
/// scoped result. Float rules intentionally differ from integer rules: Ferlium excludes NaN and infinity,
/// but retains signed zero, so `x + 0` and `x * 0` are not representation-preserving float
/// identities while `x - +0`, `x * 1`, `x - x` and reflexive comparison are sound.
fn partial_call_outcome(
    operation: &Operation,
    ty: &CallImplType,
    state: &State,
    context: &FoldContext<'_>,
) -> Option<CallRewrite> {
    if !ty.effects().is_empty() || ty.result_convention != CallResultConvention::Value {
        return None;
    }
    let call = dataflow::call_operands(&operation.operands, ty)?;
    if call
        .arguments
        .iter()
        .any(|(_, convention)| !matches!(convention, ArgConvention::Let))
    {
        return None;
    }
    let callee = match call.callee {
        mir::Value::Function(callee) => *callee,
        operand => match context
            .analysis
            .place_of(operand)
            .map(|place| state.place(place))
        {
            Some(Fact::Known(Const::Function(callee))) => callee,
            _ => return None,
        },
    };
    let known = context.known_calls.resolve(callee)?;
    let argument = |index: usize| call.arguments.get(index).map(|(operand, _)| *operand);
    let literal = |index: usize| -> Option<LiteralValue> {
        let place = context.analysis.tracked_place_of(argument(index)?)?;
        match state.place(place) {
            Fact::Known(Const::Literal(literal)) => Some(literal),
            _ => None,
        }
    };
    // Deliberately not `literal(index).is_some()`: reading a fact clones what it holds, and the
    // callees below that ask only whether an argument is known are the most common calls in a body.
    let is_known = |index: usize| {
        context
            .analysis
            .tracked_place_of(match argument(index) {
                Some(argument) => argument,
                None => return false,
            })
            .is_some_and(|place| state.place_is_known(place))
    };
    let same_argument = |left: usize, right: usize| {
        let (Some(left), Some(right)) = (argument(left), argument(right)) else {
            return false;
        };
        left == right
            || context
                .analysis
                .place_of(left)
                .is_some_and(|left_place| context.analysis.place_of(right) == Some(left_place))
    };
    let copy = |index| argument(index).cloned().map(CallRewrite::Copy);
    let int_is = |index, expected| {
        literal(index).and_then(|literal| literal.as_primitive_ty::<isize>().copied())
            == Some(expected)
    };
    let float_is = |index, expected: f64| {
        literal(index)
            .and_then(|literal| literal.as_primitive_ty::<Float>().copied())
            .is_some_and(|value| value.into_inner().to_bits() == expected.to_bits())
    };
    let zero = || {
        let representation = match known {
            KnownCallee::IntSub | KnownCallee::IntMul => LiteralValue::new_native(0isize),
            KnownCallee::FloatSub | KnownCallee::FloatMul => {
                LiteralValue::new_native(Float::new(0.0).expect("zero is a finite float"))
            }
            _ => return None,
        };
        Some(CallRewrite::Reification(Reification::Constant(
            mir::value::Constant {
                ty: ty.ret(),
                representation,
            },
        )))
    };

    match known {
        KnownCallee::IntAdd if int_is(0, 0) => copy(1),
        KnownCallee::IntAdd if int_is(1, 0) => copy(0),
        KnownCallee::IntSub if same_argument(0, 1) => zero(),
        KnownCallee::IntSub if int_is(1, 0) => copy(0),
        KnownCallee::IntMul if int_is(0, 0) || int_is(1, 0) => zero(),
        KnownCallee::IntMul if int_is(0, 1) => copy(1),
        KnownCallee::IntMul if int_is(1, 1) => copy(0),
        KnownCallee::IntCmp if same_argument(0, 1) => Some(CallRewrite::EqualOrdering),
        // The two rewrites below name their whole argument rather than a literal one, so both step
        // aside for a *known* argument: evaluating the call outright produces a constant, which is
        // better than copying the cell that held it or comparing it at run time.
        KnownCallee::IntFromInt if !is_known(0) => copy(0),
        // Negation is not an identity but a rewrite: the call becomes the one comparison MIR uses
        // to test a boolean, which every later pass reads.
        KnownCallee::BoolNot if !is_known(0) => argument(0).cloned().map(CallRewrite::Negate),

        // `+0.0` is not an identity for `-0.0`, and multiplying an unknown negative value by
        // `+0.0` produces `-0.0`. Both signs are observable through formatting and hashing.
        KnownCallee::FloatSub if same_argument(0, 1) => zero(),
        KnownCallee::FloatSub if float_is(1, 0.0) => copy(0),
        KnownCallee::FloatMul if float_is(0, 1.0) => copy(1),
        KnownCallee::FloatMul if float_is(1, 1.0) => copy(0),
        KnownCallee::FloatCmp if same_argument(0, 1) => Some(CallRewrite::EqualOrdering),
        KnownCallee::IntAdd
        | KnownCallee::IntSub
        | KnownCallee::IntMul
        | KnownCallee::IntNeg
        | KnownCallee::IntFromInt
        | KnownCallee::IntCmp
        | KnownCallee::FloatAdd
        | KnownCallee::FloatSub
        | KnownCallee::FloatMul
        | KnownCallee::FloatNeg
        | KnownCallee::FloatCmp
        | KnownCallee::BoolNot
        | KnownCallee::ArrayLen
        | KnownCallee::ArrayResolveIndex
        | KnownCallee::ArrayIndex
        | KnownCallee::ArrayOffsetUnchecked
        | KnownCallee::ArrayWrapIndex
        | KnownCallee::RangeNext
        | KnownCallee::RangeInclusiveNext => None,
    }
}

/// Where an operation carries its callee, for the three kinds that dispatch through one.
///
/// `drop` and `clone` name a `Value` method exactly as a call names a function — the interpreter
/// resolves all three through the same contract, a constant reference or the place of a function
/// value read by reference — so all three are devirtualizable at the same price.
fn callee_operand_index(operation: &Operation) -> Option<usize> {
    match operation.kind {
        OperationKind::Call { .. } => Some(0),
        OperationKind::Drop { .. } => Some(1),
        OperationKind::Clone { .. } => Some(2),
        _ => None,
    }
}

/// The function an indirect dispatch's callee place is known to hold, when naming it directly is
/// safe, paired with the operand index to write it into.
///
/// Returns `None` for a dispatch that is already direct, and for one whose callee the analysis
/// cannot resolve. The payoff is that a direct call costs no place read and no dynamic dispatch,
/// and is a candidate for folding and inlining on a later round; the population is dispatches
/// through a `dict_entry`, which specialization and inlining put in front of the analysis.
///
/// **Restricted to a callee read from a [`Root::DictEntry`]**, and the restriction is load-bearing
/// rather than cautious. Any other place may hold a *closure* — a function together with its
/// captured environment — and a bare `Value::Function` operand names the function alone, silently
/// dropping the captures. An earlier version without this restriction was caught by a test
/// divergence, "expected native value, got function value". A dictionary entry holds a plain
/// function by construction, which is what makes this rewrite information-preserving there.
fn resolved_callee(
    operation: &Operation,
    state: &State,
    analysis: &Analysis,
) -> Option<(usize, FunctionId)> {
    let index = callee_operand_index(operation)?;
    let callee = operation.operands.get(index)?;
    if matches!(callee, mir::Value::Function(_)) {
        return None;
    }
    let place = analysis.place_of(callee)?;
    if !matches!(analysis.root_of_place(place), Root::DictEntry(_)) {
        return None;
    }
    match state.place(place) {
        Fact::Known(Const::Function(id)) => Some((index, id)),
        _ => None,
    }
}

/// Evaluates a call site, recording the refusal if one was asked for.
fn fold_outcome(
    operation: &Operation,
    ty: &CallImplType,
    state: &State,
    context: &FoldContext<'_>,
    refusals: &mut Option<&mut Vec<Refusal>>,
) -> Option<Reification> {
    match try_fold_call(operation, ty, state, context) {
        Ok(constant) => Some(constant),
        Err(reason) => {
            if let Some(refusals) = refusals {
                refusals.push(Refusal {
                    site: operation.span,
                    callee: match &operation.operands[0] {
                        mir::Value::Function(id) => Some(*id),
                        _ => None,
                    },
                    reason,
                });
            }
            None
        }
    }
}

fn fact_for_reification(reification: &Reification) -> Fact {
    match reification {
        Reification::Constant(constant) => {
            Fact::Known(Const::Literal(constant.representation.clone()))
        }
        Reification::Array {
            element_ty,
            elements,
        } => Fact::Known(Const::Array {
            element_ty: *element_ty,
            elements: elements.clone(),
        }),
        Reification::Operand(_) => Fact::Unknown,
    }
}

/// Why an argument's value is not known, in the terms that say what would fix it.
///
/// "Argument not known" is by far the largest refusal bucket, and undivided it says nothing: it
/// cannot distinguish a case specialization would lift from one that is merely downstream of
/// another refusal. Each answer here names a different remedy, which is the point.
fn why_argument_unknown(
    operand: &mir::Value,
    state: &State,
    analysis: &Analysis,
    refusal: &RefusalContext,
) -> NotFoldable {
    let Some(place) = analysis.place_of(operand) else {
        return why_operand_names_no_place(operand, state, analysis);
    };
    let root = analysis.root_of_place(place);
    if analysis.is_escaped(root) {
        return NotFoldable::ArgumentStorageEscaped;
    }
    match state.place(place) {
        // Known, but not in a form compile-time evaluation accepts.
        Fact::Known(_) => NotFoldable::ArgumentNotLiteral,
        // An uninitialized slot is not an analysis gap; it is a slot with nothing in it.
        Fact::Uninit => NotFoldable::ArgumentStorageNotModelled,
        Fact::Unknown => match root {
            Root::Parameter(_) => NotFoldable::ArgumentIsParameter,
            Root::DictEntry(_) => NotFoldable::ArgumentNotLiteral,
            Root::Alloca(id) if refusal.call_destinations.contains(&id) => {
                NotFoldable::ArgumentFromCall
            }
            Root::Alloca(_) => NotFoldable::ArgumentFromOperation,
        },
    }
}

/// Why an operand names no slot the analysis tracks — the three causes have three remedies.
///
/// Structural place bindings are checked before reaching here, so a register here holds a
/// materialized value or names no modelled storage.
fn why_operand_names_no_place(
    operand: &mir::Value,
    state: &State,
    analysis: &Analysis,
) -> NotFoldable {
    let mir::Value::Register(id) = operand else {
        return NotFoldable::ArgumentStorageNotModelled;
    };
    match state.register(*id) {
        // Bound, but to a value rather than a slot. Folding reads arguments only through places,
        // so a *known* value here is a gap rather than a missing analysis — worth separating,
        // because the two have completely different costs to close.
        Some(Fact::Known(Const::Literal(_))) => NotFoldable::ArgumentValueKnownButUnread,
        Some(_) => NotFoldable::ArgumentIsUnknownValue,
        None => match analysis.root_of_register(*id) {
            Some(root) if analysis.is_escaped(root) => NotFoldable::ArgumentStorageEscaped,
            _ => NotFoldable::ArgumentStorageNotModelled,
        },
    }
}

/// The `alloca`s that some call in this function writes its result into.
///
/// Used to separate "this argument is unknown because the call producing it did not fold" — which
/// needs no new machinery, only the other refusal lifted — from "unknown because the analysis does
/// not model what wrote it", which does.
///
/// Deliberately approximate: it matches a call's result operand by register identity, so it sees
/// the `%r = alloca; call f(.., %r)` shape that lowering actually emits and not a write through a
/// `subfield`. It reads call layout through [`dataflow::call_operands`] rather than restating it.
/// This feeds a report, not a rewrite, so an approximation that is honest about its edges is the
/// right trade — a precise answer would mean recording a cause alongside every `Unknown` the
/// dataflow produces.
fn call_destinations(func: &Function) -> FxHashSet<mir::ValueId> {
    let mut destinations = FxHashSet::default();
    let mut record = |operation: &Operation| {
        if let OperationKind::Call { ty, .. } = &operation.kind
            && let Some(call) = dataflow::call_operands(&operation.operands, ty)
            && let mir::Value::Register(id) = call.result
        {
            destinations.insert(*id);
        }
    };
    for block in func.blocks() {
        let block = func.block(block);
        block.operations().iter().for_each(&mut record);
        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
            record(operation);
        }
    }
    destinations
}

/// The value of a branch condition, when the analysis knows it.
fn known_condition(condition: &mir::Value, state: &State) -> Option<bool> {
    let mir::Value::Register(id) = condition else {
        return None;
    };
    match state.register(*id)? {
        Fact::Known(Const::Literal(literal)) => literal.as_primitive_ty::<bool>().copied(),
        _ => None,
    }
}

/// Evaluates one call site at compile time and expresses the result as a constant, or explains why
/// it cannot be.
fn try_fold_call(
    operation: &Operation,
    ty: &CallImplType,
    state: &State,
    context: &FoldContext<'_>,
) -> Result<Reification, NotFoldable> {
    let Some(call) = dataflow::call_operands(&operation.operands, ty) else {
        return Err(NotFoldable::UnsupportedConvention);
    };
    // A callee is either named directly, or read from a place the analysis knows holds a function
    // — which is what an entry of a constant dictionary resolves to.
    let callee = match call.callee {
        mir::Value::Function(id) => *id,
        operand => match context
            .analysis
            .place_of(operand)
            .map(|place| state.place(place))
        {
            Some(Fact::Known(Const::Function(id))) => id,
            _ => return Err(NotFoldable::CalleeNotDirect),
        },
    };

    let mut arguments = Vec::with_capacity(call.extras.len() + call.arguments.len());
    for extra in call.extras {
        match extra {
            mir::Value::Dictionary(id) => arguments.push(ConstArgument::Dictionary(*id)),
            // A forwarded dictionary parameter is not known here; specialization is a later phase.
            _ => return discard(arguments, NotFoldable::EvidenceNotKnown),
        }
    }
    for ((operand, convention), parameter) in call.arguments.iter().zip(&ty.fn_ty.args) {
        // Write-back of a `MutableRef` argument is out of scope: the callee's writes would have to
        // be reified too.
        if !matches!(convention, ArgConvention::Let) {
            return discard(arguments, NotFoldable::MutableArgument);
        }
        let known = context
            .analysis
            .tracked_place_of(operand)
            .map(|place| state.place(place));
        match known {
            Some(Fact::Known(Const::Literal(literal)))
                if literal.has_representation_type_in(parameter.ty, &context.env) =>
            {
                arguments.push(ConstArgument::Value(literal.into_value()))
            }
            Some(Fact::Known(Const::Array {
                element_ty,
                elements,
            })) if parameter.ty == array_type(element_ty) => {
                arguments.push(ConstArgument::Value(array_value_from_vec(
                    elements
                        .into_vec()
                        .into_iter()
                        .map(LiteralValue::into_value)
                        .collect(),
                )))
            }
            Some(Fact::Known(Const::Function(function))) if parameter.ty.is_function() => arguments
                .push(ConstArgument::Value(crate::hir::value::Value::function(
                    function,
                ))),
            Some(Fact::Known(_)) => return discard(arguments, NotFoldable::ArgumentNotLiteral),
            _ => {
                // The reason is irrelevant to the rewrite. Detailed provenance is computed only
                // when a report will consume it; the broad fallback is never externally observed.
                let reason = context
                    .refusal
                    .as_ref()
                    .map_or(NotFoldable::ArgumentStorageNotModelled, |refusal| {
                        why_argument_unknown(operand, state, &context.analysis, refusal)
                    });
                return discard(arguments, reason);
            }
        }
    }

    // A unit result carries no information, so replacing such a call with a store of `()` gains
    // nothing — and it would delete a call the host may be relying on. `Value::drop` is declared
    // effect-free by its trait, so a host that instruments drops *must* declare that instrumentation
    // pure; folding pure unit-returning calls would silently remove it for no benefit.
    if ty.ret() == Type::unit() {
        return discard(arguments, NotFoldable::UnitResult);
    }

    let value = context.evaluator.try_call(
        callee,
        ty.effects(),
        ty.result_convention,
        ty.ret(),
        arguments,
        operation.span,
    )?;
    let reified = reify(&value, ty.ret(), &context.env);
    value.discard_storage();
    match reified? {
        result @ (Reification::Constant(_) | Reification::Array { .. }) => Ok(result),
        // A function operand needs no constant, but replacing a call with one is a different
        // rewrite than storing a literal; leave it to the devirtualization work.
        Reification::Operand(_) => Err(NotFoldable::NotReifiable),
    }
}

/// Releases arguments prepared for a call that is not made after all.
fn discard(arguments: Vec<ConstArgument>, reason: NotFoldable) -> Result<Reification, NotFoldable> {
    ConstArgument::discard_all(arguments);
    Err(reason)
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized_function<'a>(module: &'a str, name: &str) -> &'a str {
        module
            .split(&format!("fn {name}"))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
            .split("\nfn ")
            .next()
            .expect("a function has a body")
    }

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

    /// An indirect call whose callee the analysis resolved is rewritten to name that callee
    /// directly. The whole chain is what produces the shape: specialization binds the dictionary to
    /// a constant, inlining brings the body into the caller, folding resolves the `dict_entry` to a
    /// known function, and this names it.
    ///
    /// The argument is deliberately unknown, so the call itself cannot fold and what remains to
    /// observe is the callee operand.
    #[test]
    fn a_call_through_a_resolved_dictionary_entry_becomes_direct() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "fold",
            "fn twice_it(x) { x + x }\n\
             fn use_it(n: int) -> int { twice_it(n) }",
        );
        let caller = module
            .split("fn use_it")
            .nth(1)
            .expect("the module defines use_it")
            .split("\nfn ")
            .next()
            .expect("use_it has a body");
        assert!(
            caller.contains("call std::Num<std::int>::add"),
            "the call must name the concrete impl rather than a place:\n{caller}"
        );
        assert!(
            !caller.contains("call %r"),
            "no indirect call may remain:\n{caller}"
        );
    }

    /// `drop` and `clone` name their `Value` method the same way a call names a function, and are
    /// devirtualized on the same evidence. They are the majority of the resolvable dispatches in
    /// generic code: an iterator pipeline drops its `Option` once per element through a dictionary
    /// entry that specialization has already made constant.
    ///
    /// Asserted over the whole module rather than one function because the sites are spread across
    /// the specializations the pipeline creates, none of which is named in the source.
    #[test]
    fn a_drop_or_clone_through_a_resolved_dictionary_entry_becomes_direct() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir("fold", "fn main() { [1, 2] |> map(|x| x * x); }");
        let indirect: Vec<&str> = module
            .lines()
            .map(str::trim)
            .filter(|line| {
                (line.starts_with("drop ") || line.starts_with("clone "))
                    && line.contains(" via %r")
            })
            .collect();
        assert!(
            indirect.is_empty(),
            "every resolvable drop/clone callee must be named directly, found:\n{}",
            indirect.join("\n")
        );
    }

    #[test]
    fn a_late_dictionary_entry_callee_is_devirtualized_after_round_exhaustion() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir("fold", "[1, 2] |> concat([3, 4]) |> map(|x| x * x)");
        let lines: Vec<_> = module.lines().map(str::trim).collect();
        let late_indirect: Vec<_> = lines
            .windows(2)
            .filter_map(|pair| {
                let [entry, call] = pair else {
                    return None;
                };
                if entry.contains("= dict_entry ") && call.starts_with("call %r") {
                    Some(format!("{entry}\n{call}"))
                } else {
                    None
                }
            })
            .collect();

        assert!(
            late_indirect.is_empty(),
            "dictionary-entry callees should be direct after final devirtualization, found:\n{}",
            late_indirect.join("\n\n")
        );
    }

    /// Reading a field of a struct built from constants folds. This is the capability field
    /// tracking exists for, and it was unreachable until `field_index` learned to resolve a
    /// constant-pool index: every `subfield` produced an unknown value, so no field of any
    /// aggregate was ever known.
    #[test]
    fn a_field_of_a_constant_struct_folds() {
        let module = optimized_main(
            "struct S { a: int, b: int }\n\
             fn main() -> int { let s = S { a: 20, b: 22 }; s.a + s.b }",
        );
        // `optimized_main` returns everything after `fn main`, which includes the derived `Value`
        // impls; only main's own body is the subject here.
        let main = module.split("\nfn ").next().expect("main has a body");
        assert!(
            !main.contains("call "),
            "the addition must fold through the fields:\n{main}"
        );
        assert!(main.contains("= 42"), "and yield the sum:\n{main}");
    }

    /// The structural place map retains escaped roots for diagnostics, but folding must never
    /// inject a constant into one. A scoped projection can mutate its arguments while it is open
    /// and again when `end_project` resumes its epilogue, so their initial constants are stale.
    #[test]
    fn an_escaped_structural_place_does_not_retain_a_folded_constant() {
        let mut session = CompilerSession::new();
        session.set_allow_experimental(true);
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "fold",
            "subscript cell(slot: &mut int, log: &mut int) -> int {\n\
                 mut {\n\
                     log = log + 1;\n\
                     let mut local = slot;\n\
                     yield local;\n\
                     slot = local;\n\
                     log = log * 10\n\
                 }\n\
             }\n\
             fn main() -> int {\n\
                 let cell_slot = cell;\n\
                 let mut slot = 5;\n\
                 let mut log = 0;\n\
                 slot->[cell_slot](log) += 7;\n\
                 slot + log\n\
             }",
        );
        let main = module
            .split("fn main")
            .nth(1)
            .expect("the module defines main")
            .split("\nfn ")
            .next()
            .expect("main has a body");
        assert!(
            main.contains("end_project"),
            "the scoped call must remain:\n{main}"
        );
        assert!(
            main.contains("call std::Num<std::int>::add"),
            "the final addition must read the values mutated by the projection:\n{main}"
        );
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

    /// A source-fallible call whose evaluation succeeds folds too: the terminator loses its error
    /// edge and the cleanup pad it reached becomes unreachable.
    #[test]
    fn a_fallible_call_that_succeeds_folds_away_its_error_edge() {
        let main = optimized_main("fn main() -> int { idiv(6, 3) }");
        assert!(!main.contains("invoke"), "the call must fold:\n{main}");
        assert!(
            !main.contains("propagate_error"),
            "the error path must be unreachable and pruned:\n{main}"
        );
        assert!(
            main.contains("= 2"),
            "the result must be a constant:\n{main}"
        );
    }

    /// A call that raises must not fold: the program is entitled to observe the failure, so the
    /// `invoke` and its error edge stay exactly as lowered.
    #[test]
    fn a_fallible_call_that_fails_is_left_alone() {
        let main = optimized_main("fn main() -> int { idiv(6, 0) }");
        assert!(
            main.contains("invoke"),
            "a failing call must stay a runtime call:\n{main}"
        );
        assert!(main.contains("propagate_error"), "{main}");
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

    #[test]
    fn partially_known_integer_identities_are_simplified() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "fold",
            "fn identities(x: int) {\n\
                 { add_left: 0 + x, add_right: x + 0, sub_zero: x - 0,\n\
                   sub_self: x - x, mul_left_zero: 0 * x, mul_right_zero: x * 0,\n\
                   mul_left_one: 1 * x, mul_right_one: x * 1, reflexive: x < x }\n\
             }",
        );
        let body = optimized_function(&module, "identities");
        assert!(
            !body.contains("call std::Num<std::int>") && !body.contains("call std::Ord<std::int>"),
            "all documented integer identities must become copies or constants:\n{body}"
        );
    }

    /// The conversion every integer literal is desugared into is the identity at `int`. A literal
    /// argument folds outright, so what this must show is the call whose argument is unknown —
    /// which is what a generic body specialized at `int` leaves.
    #[test]
    fn an_integer_conversion_of_an_unknown_value_is_elided() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "fold",
            "fn convert(n) { from_int(n) }\n\
             fn use_it(x: int) -> int { convert(x) }",
        );
        let body = optimized_function(&module, "use_it");
        assert!(
            !body.contains("from_int"),
            "converting an int to an int must become a copy:\n{body}"
        );
        assert!(body.contains("memcpy %p0 to %p1"), "{body}");
    }

    /// `not` has no MIR operation of its own, but `comp_eq value false` is exactly it, so naming
    /// the callee is enough to stop calling it.
    #[test]
    fn a_logical_negation_becomes_a_comparison() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir("fold", "fn negate(a: bool) -> bool { not a }");
        let body = optimized_function(&module, "negate");
        assert!(
            !body.contains("call std::not"),
            "the negation call must become a comparison:\n{body}"
        );
        assert!(body.contains("comp_eq %p0 false"), "{body}");
    }

    /// A *known* argument must reach full evaluation instead: a constant beats both a copy of the
    /// cell that held it and a comparison performed at run time.
    #[test]
    fn a_known_argument_folds_rather_than_being_rewritten() {
        let main = optimized_main("fn main() -> bool { not (from_int(1) == 1) }");
        assert!(!main.contains("comp_eq"), "{main}");
        assert!(
            main.contains("store @c") && main.contains("to %p0"),
            "the whole expression must fold to a constant:\n{main}"
        );
    }

    #[test]
    fn sound_partially_known_float_identities_are_simplified() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "fold",
            "fn identities(x: float) {\n\
                 { sub_zero: x - 0.0, sub_self: x - x,\n\
                   mul_left_one: 1.0 * x, mul_right_one: x * 1.0, reflexive: x < x }\n\
             }",
        );
        let body = optimized_function(&module, "identities");
        assert!(
            !body.contains("call std::Num<std::float>")
                && !body.contains("call std::Ord<std::float>"),
            "the signed-zero-safe float identities must become copies or constants:\n{body}"
        );
    }

    /// Signed zero is a Ferlium float value and is observable through formatting and hashing.
    /// Consequently the familiar real-number identities below are not valid representation-level
    /// rewrites for an unknown float.
    #[test]
    fn float_signed_zero_prevents_unsound_add_and_multiply_by_zero_rewrites() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "fold",
            "fn retain(x: float) { { add: x + 0.0, mul: x * 0.0 } }",
        );
        let body = optimized_function(&module, "retain");
        assert!(body.contains("call std::Num<std::float>::add"), "{body}");
        assert!(body.contains("call std::Num<std::float>::mul"), "{body}");
    }
}
