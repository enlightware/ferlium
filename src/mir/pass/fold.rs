// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

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
//! zero deliberately excludes `x + +0.0` and `x * 0.0`.
//!
//! The rewrite is then local: `call f(a, b, ret)` becomes a store of a constant or captureless
//! function, a `build_array`, or a bounded `StaticStr` plus `string_from_static` construction into
//! `ret`. All forms initialize the same slot and none takes ownership of anything the caller held —
//! argument conventions leave ownership with the caller — so the surrounding construction/drop
//! scaffolding stays correct while becoming dead. Removing it is a separate cleanup pass.
//!
//! Folding runs against an immutable function and returns a rewritten one, so the analysis it reads
//! is never stale with respect to the edits it makes. Within a block, a fold updates the local state
//! immediately, so a chain of calls in straight-line code folds in one pass; a chain that crosses
//! blocks folds over the driver's rounds.

#![allow(dead_code)]

use std::{cell::OnceCell, rc::Rc};

use rustc_hash::{FxHashMap, FxHashSet};
use ustr::{Ustr, ustr};

use super::{
    OptimizationStage,
    cost::{Growth, GrowthBase},
    dataflow::{self, Analysis, Const, Fact, PlaceId, Root, State},
    known_callee::{KnownCallee, KnownCallees},
    scalar_arguments,
    site::OperationIndex,
};
use crate::{
    CompilerSession, Location,
    containers::b,
    hir::{
        function::ArgConvention,
        value::{
            ClosedTraitDictionary, HiddenEvidenceArgValue, LiteralValue, Value,
            VariantPayloadStorage,
        },
    },
    mir::{
        self, BlockId, DebugLocation, Function, Operation, OperationKind, ValueId,
        const_eval::{ConstArgument, ConstEvaluator, NotFoldable},
        edit::FunctionEdit,
        interpreter::static_evidence_value,
        reify::{Reification, reify},
        role::{MirType, ValueRole, ValueRoles},
        terminator::{Terminator, TerminatorKind},
        value::{Constant, StaticEvidence},
    },
    module::{FunctionId, ModuleEnv, ModuleId, id::Id},
    std::{
        array::{array_type, array_value_from_vec},
        math::Float,
        ordering::{ORDERING_EQUAL, ordering_type},
        string::{static_str_type, string_type},
        value::is_tag_scalar,
    },
    types::r#type::{CallImplType, CallResultConvention, Type},
};

/// A call result the optimizer can materialize without knowing every argument.
#[derive(Debug)]
enum CallRewrite {
    /// Ordinary full constant evaluation.
    Reification(Reification),
    /// A known identity says the result is one of the call's input places.
    Copy(mir::Value),
    /// A known identity says the result is one of the call's inputs passed as a value.
    Store(mir::Value),
    /// A reflexive comparison returns the payload-free `Equal` case.
    EqualOrdering,
    /// A boolean negation, expressed as the comparison MIR already has.
    Negate(mir::Value),
    /// Arithmetic negation uses the declared concrete std native.
    ArithmeticNegation {
        source: mir::Value,
        callee: FunctionId,
        ty: CallImplType,
    },
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
    destination: FoldDestination,
    result: CallRewrite,
}

/// Where a folded call would have left its result.
enum FoldDestination {
    /// The place the call would have written its result into.
    Place(mir::Value),
    /// The register the call would have defined.
    Register(ValueId),
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

/// A `build_array` whose element slots the analysis can replace with the constants they hold, and
/// which of them — as operand index and the constant's representation.
struct ArrayElements {
    block: BlockId,
    /// Index of the operation within its block.
    index: OperationIndex,
    element_ty: Type,
    known: Vec<(usize, LiteralValue)>,
}

/// An indirect dispatch whose callee the analysis resolved, and the function to name directly
/// instead. `operand` is the callee's index, which differs per operation kind.
struct Devirtualization {
    site: Site,
    operand: usize,
    callee: FunctionId,
    hidden_evidence: Rc<[StaticEvidence]>,
}

struct ResolvedCallee {
    operand: usize,
    callee: FunctionId,
    hidden_evidence: Rc<[StaticEvidence]>,
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
    /// Runtime calls proved unable to take their source-error edge.
    nonzero_invokes: Vec<(BlockId, FunctionId, CallImplType)>,
    /// Conditional branches whose condition is known, and the successor they always take.
    branches: Vec<(BlockId, BlockId)>,
    /// `build_array` element slots to replace with the constants they hold.
    arrays: Vec<ArrayElements>,
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
        self.calls.is_empty()
            && self.invokes.is_empty()
            && self.nonzero_invokes.is_empty()
            && self.branches.is_empty()
            && self.arrays.is_empty()
    }
}

/// Everything a call site is judged against, gathered once per function.
///
/// The evaluator, environment, and dataflow analysis decide whether a call folds. Refusal-only
/// provenance is absent from normal optimization and constructed only for an optimization report.
struct FoldContext<'a> {
    func: &'a Function,
    /// Derived only when a rewrite must tell a value argument from a place.
    roles: OnceCell<ValueRoles>,
    evaluator: Option<ConstEvaluator<'a>>,
    env: ModuleEnv<'a>,
    analysis: Analysis,
    known_calls: KnownCallSemantics<'a>,
    string_from_static: FunctionId,
    refusal: Option<RefusalContext>,
}

/// The declared std constructor used by constructive string reification.
///
/// Keeping its call type beside its identity makes synthesized calls follow the declaration rather
/// than duplicating that declaration in the optimizer.
#[derive(Clone)]
pub(crate) struct StringMaterializer {
    function: FunctionId,
    ty: CallImplType,
}

impl StringMaterializer {
    pub(crate) fn resolve(env: ModuleEnv<'_>, function_id: FunctionId) -> Self {
        let module = env
            .module_by_id(function_id.module)
            .expect("the std module is registered before MIR optimization");
        let function = module
            .get_function_by_id(function_id.function)
            .expect("std::string_from_static has a callable definition");
        let fn_ty = function.definition.ty_scheme.ty.clone();
        debug_assert!(function.definition.ty_scheme.ty_quantifiers.is_empty());
        debug_assert!(function.definition.ty_scheme.eff_quantifiers.is_empty());
        debug_assert!(function.definition.ty_scheme.constraints.is_empty());
        debug_assert_eq!(function.parameter_passing.as_slice(), [ArgConvention::Let]);
        debug_assert_eq!(fn_ty.args.len(), 1);
        debug_assert_eq!(fn_ty.args[0].ty, static_str_type());
        debug_assert_eq!(fn_ty.ret, string_type());
        debug_assert_eq!(
            function.definition.result_convention,
            CallResultConvention::Value
        );
        Self {
            function: function_id,
            ty: CallImplType::new(fn_ty, function.definition.result_convention),
        }
    }
}

/// Module-local inputs shared by fold planning and materialization.
#[derive(Clone, Copy)]
pub(crate) struct FoldResources<'m, 's> {
    growth_base: GrowthBase,
    env: ModuleEnv<'m>,
    module_id: ModuleId,
    string_materializer: &'s StringMaterializer,
}

impl<'m, 's> FoldResources<'m, 's> {
    pub(crate) fn new(
        growth_base: GrowthBase,
        env: ModuleEnv<'m>,
        module_id: ModuleId,
        string_materializer: &'s StringMaterializer,
    ) -> Self {
        Self {
            growth_base,
            env,
            module_id,
            string_materializer,
        }
    }
}

struct RefusalContext {
    /// The `alloca`s a call writes its result into, and the registers it defines. See
    /// [`call_destinations`].
    call_destinations: FxHashSet<ValueId>,
    /// The place each `load` read, so that a value argument is explained by its place.
    loaded_from: FxHashMap<ValueId, mir::Value>,
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
    /// value: the next round's analysis learns nothing from it. Rewriting binary arithmetic to
    /// negation is an exception: it may expose a double negation. Measured on std, granting rounds
    /// for those cost 0.14% of MIR optimization time and changed no optimized body.
    ///
    /// **Devirtualization does.** Closed-dictionary lowering deliberately makes even concrete trait
    /// dispatch uniform. Naming the selected entry exposes script callees, their hidden static
    /// evidence, and known natives to the rest of the optimizer.
    pub warrants_another_round: bool,
    /// The places this rewrite initialized with a compile-time result.
    ///
    /// A call reading one may have become foldable as a whole, which the next round's analysis
    /// decides; inlining it first would replace that evaluation with a body to fold piecemeal.
    pub reified_places: FxHashSet<ValueId>,
}

/// Folds what can be folded in `func`, returning a rewritten function if anything was.
pub(crate) fn fold_function(
    func: &Function,
    growth_base: GrowthBase,
    env: ModuleEnv<'_>,
    stage: OptimizationStage<'_>,
    known_calls: KnownCallSemantics<'_>,
    string_materializer: &StringMaterializer,
) -> Option<Folded> {
    // Physical folding uses shared algebraic/CFG rules, never the boxed script evaluator or
    // semantic dictionary-entry adaptation.
    let session = match stage {
        OptimizationStage::Semantic(callees) => Some(callees.session()),
        OptimizationStage::Physical { .. } => None,
    };
    let resources = FoldResources::new(
        growth_base,
        env,
        env.current.module_id(),
        string_materializer,
    );
    let (plan, devirtualizations) =
        plan_folds_and_devirtualizations(func, resources, session, known_calls);
    if plan.is_empty() && devirtualizations.is_empty() {
        return None;
    }
    let warrants_another_round = plan.warrants_another_round || !devirtualizations.is_empty();

    let mut edit = FunctionEdit::new(func.clone());
    // Devirtualization first: it only rewrites a callee operand in place, while a fold below may
    // splice one call into two operations and shift every later index of its block. Both were
    // planned against the same body, and no operation is in both plans.
    apply_devirtualizations(&mut edit, devirtualizations);
    // For the same reason: naming a constant replaces one element operand and leaves every index
    // where it was.
    apply_array_elements(&mut edit, plan.arrays, env);
    // A reflexive comparison expands one call into `variant Equal; store`, so apply sites in
    // reverse order and splice without invalidating a later index planned in the same block.
    let mut renamed = FxHashMap::default();
    let mut reified_places = FxHashSet::default();
    for fold in plan.calls.into_iter().rev() {
        let index = fold.index.as_index();
        let span = edit.block(fold.block).operations[index].span;
        let replacements = match fold.destination {
            FoldDestination::Place(destination) => {
                if let (CallRewrite::Reification(_), mir::Value::Register(place)) =
                    (&fold.result, &destination)
                {
                    reified_places.insert(*place);
                }
                materialize_call_rewrite(
                    &mut edit,
                    span,
                    fold.result,
                    destination,
                    env,
                    string_materializer,
                )
            }
            FoldDestination::Register(register) => {
                define_call_rewrite(&mut edit, span, fold.result, register, &mut renamed, env)
            }
        };
        edit.block_mut(fold.block)
            .operations
            .splice(index..=index, replacements);
    }
    rename_registers(&mut edit, &renamed);
    for invoke in plan.invokes {
        let span = edit.block(invoke.block).terminator.span;
        if let mir::Value::Register(place) = &invoke.destination {
            reified_places.insert(*place);
        }
        // The call becomes an ordinary store at the end of the block, and the terminator loses its
        // error edge: an evaluated call cannot fail. Appending keeps the indices the operation
        // folds above were planned against.
        let replacements = materialize_reification(
            &mut edit,
            span,
            invoke.result,
            invoke.destination,
            env,
            string_materializer,
        );
        let block = edit.block_mut(invoke.block);
        block.operations.extend(replacements);
        block.terminator = Terminator::goto(span, invoke.normal);
    }
    for (block_id, callee, ty) in plan.nonzero_invokes {
        // Retargetable declarations have identical instantiation and ownership conventions.
        demote_invoke(&mut edit, block_id, callee, ty, env);
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
        reified_places,
    })
}

/// Names the constants a `build_array`'s element slots hold instead of reading them back out.
///
/// An element operand may be a materialized value as readily as a place — verification admits
/// either, and the reification path already emits the constant form. What reaches here is the
/// lowering of a source array literal, which stores each element into a fresh slot only for the
/// construction to read it straight back; naming the constants leaves those slots unread, and DCE
/// removes them.
///
/// This buys no round. The array's own fact is derived from these same element facts, so the
/// substitution hands the next round's analysis nothing it did not already have.
fn known_array_elements(
    operation: &Operation,
    state: &State,
    analysis: &Analysis,
) -> Vec<(usize, LiteralValue)> {
    let Some((_, elements)) = operation.operands.split_last() else {
        return Vec::new();
    };
    elements
        .iter()
        .enumerate()
        .filter_map(|(index, operand)| {
            let place = analysis.tracked_place_of(operand)?;
            match state.place(place) {
                Fact::Known(Const::Literal(literal)) => Some((index, Rc::unwrap_or_clone(literal))),
                _ => None,
            }
        })
        .collect()
}

fn apply_array_elements(edit: &mut FunctionEdit, arrays: Vec<ArrayElements>, env: ModuleEnv<'_>) {
    for array in arrays {
        for (operand, representation) in array.known {
            let constant = edit.add_constant(array.element_ty, representation, &env);
            edit.block_mut(array.block).operations[array.index.as_index()].operands[operand] =
                mir::Value::Constant(constant);
        }
    }
}

/// Turns either full evaluation or a partial known-call identity into MIR operations defining the
/// call's result `register`, or into an entry of `renamed`, when the register is to be replaced by
/// a constant or by a value already available.
fn define_call_rewrite(
    edit: &mut FunctionEdit,
    span: DebugLocation,
    rewrite: CallRewrite,
    register: ValueId,
    renamed: &mut FxHashMap<ValueId, mir::Value>,
    env: ModuleEnv<'_>,
) -> Vec<Operation> {
    let defined = |mut operation: Operation| {
        operation.assign_result_id(Some(register));
        vec![operation]
    };
    match rewrite {
        CallRewrite::Reification(Reification::Constant(constant)) => {
            let id = edit.add_constant(constant.ty, constant.representation, &env);
            renamed.insert(register, mir::Value::Constant(id));
            Vec::new()
        }
        CallRewrite::Store(source) => {
            renamed.insert(register, source);
            Vec::new()
        }
        CallRewrite::Copy(source) => defined(Operation::load(span, source)),
        CallRewrite::ArithmeticNegation { source, callee, ty } => defined(
            Operation::call(span, mir::Value::Function(callee), [source], ty).with_value_result(),
        ),
        CallRewrite::Negate(source) => defined(Operation::compare_eq(
            span,
            source,
            mir::Value::Pattern(b(LiteralValue::new_native(false))),
        )),
        CallRewrite::Reification(Reification::Tag { tag, ty }) => defined(tag_shell(span, tag, ty)),
        CallRewrite::EqualOrdering => {
            defined(tag_shell(span, ustr(ORDERING_EQUAL), ordering_type()))
        }
        CallRewrite::Reification(_) => unreachable!("a scalar result reifies as a constant"),
    }
}

/// The complete shell that is the whole value of `tag`, of the unit-only variant type `ty`.
fn tag_shell(span: DebugLocation, tag: Ustr, ty: Type) -> Operation {
    Operation::variant(
        span,
        tag,
        ty,
        Type::unit(),
        Some(VariantPayloadStorage::Inline),
        None,
        None,
    )
}

/// Replaces each use of a register `renamed` maps by what it maps to, following chains: a folded
/// call's result may be the result of another.
fn rename_registers(edit: &mut FunctionEdit, renamed: &FxHashMap<ValueId, mir::Value>) {
    if renamed.is_empty() {
        return;
    }
    let resolve = |value: &mir::Value| {
        let mut value = value.clone();
        while let mir::Value::Register(id) = &value
            && let Some(next) = renamed.get(id)
        {
            value = next.clone();
        }
        value
    };
    edit.visit_operands_mut(|operand| {
        if matches!(operand, mir::Value::Register(id) if renamed.contains_key(id)) {
            *operand = resolve(operand);
        }
    });
}

/// Turns either full evaluation or a partial known-call identity into MIR operations.
fn materialize_call_rewrite(
    edit: &mut FunctionEdit,
    span: DebugLocation,
    rewrite: CallRewrite,
    destination: mir::Value,
    env: ModuleEnv<'_>,
    string_materializer: &StringMaterializer,
) -> Vec<Operation> {
    match rewrite {
        CallRewrite::Reification(reification) => materialize_reification(
            edit,
            span,
            reification,
            destination,
            env,
            string_materializer,
        ),
        CallRewrite::Copy(source) => vec![Operation::memcpy(span, source, destination)],
        CallRewrite::Store(source) => vec![Operation::store(span, source, destination)],
        CallRewrite::ArithmeticNegation { source, callee, ty } => vec![Operation::call(
            span,
            mir::Value::Function(callee),
            [source, destination],
            ty,
        )],
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
            let mut variant = tag_shell(span, ustr(ORDERING_EQUAL), ordering_type());
            let value = edit.new_value();
            variant.assign_result_id(Some(value));
            vec![
                variant,
                Operation::store(span, mir::Value::Register(value), destination),
            ]
        }
    }
}

/// Turns a compile-time result into the MIR operations that initialize its destination.
fn materialize_reification(
    edit: &mut FunctionEdit,
    span: DebugLocation,
    reification: Reification,
    destination: mir::Value,
    env: ModuleEnv<'_>,
    string_materializer: &StringMaterializer,
) -> Vec<Operation> {
    match reification {
        Reification::Constant(constant) => {
            let id = edit.add_constant(constant.ty, constant.representation, &env);
            vec![Operation::store(
                span,
                mir::Value::Constant(id),
                destination,
            )]
        }
        Reification::Array {
            element_ty,
            elements,
        } => {
            let elements = elements.into_vec().into_iter().map(|representation| {
                let id = edit.add_constant(element_ty, representation, &env);
                mir::Value::Constant(id)
            });
            vec![Operation::build_array(
                span,
                element_ty,
                elements,
                destination,
            )]
        }
        Reification::BareFunction(function) => {
            vec![Operation::store(
                span,
                mir::Value::Function(function),
                destination,
            )]
        }
        Reification::Tag { tag, ty } => {
            let mut shell = tag_shell(span, tag, ty);
            let value = edit.new_value();
            shell.assign_result_id(Some(value));
            vec![
                shell,
                Operation::store(span, mir::Value::Register(value), destination),
            ]
        }
        Reification::String(text) => {
            let constant =
                edit.add_constant(static_str_type(), LiteralValue::new_native(text), &env);
            let text_place = edit.new_value();
            let mut alloca = Operation::alloca(span, static_str_type());
            alloca.assign_result_id(Some(text_place));
            vec![
                alloca,
                Operation::store(
                    span,
                    mir::Value::Constant(constant),
                    mir::Value::Register(text_place),
                ),
                Operation::call(
                    span,
                    mir::Value::Function(string_materializer.function),
                    [mir::Value::Register(text_place), destination],
                    string_materializer.ty.clone(),
                ),
            ]
        }
    }
}

fn reification_operation_count(reification: &Reification) -> usize {
    match reification {
        Reification::Constant(_) | Reification::Array { .. } | Reification::BareFunction(_) => 1,
        Reification::Tag { .. } => 2,
        Reification::String(_) => 3,
    }
}

fn call_rewrite_operation_count(rewrite: &CallRewrite) -> usize {
    match rewrite {
        CallRewrite::Reification(reification) => reification_operation_count(reification),
        CallRewrite::Copy(_) | CallRewrite::Store(_) | CallRewrite::ArithmeticNegation { .. } => 1,
        CallRewrite::EqualOrdering | CallRewrite::Negate(_) => 2,
    }
}

/// Decides what to rewrite, without touching the function.
///
/// `refusals`, when present, collects why each call site was left alone — the optimization report
/// runs this over an already-optimized body precisely so its answers cannot drift from the pass's.
pub(crate) fn plan_folds(
    func: &Function,
    resources: FoldResources<'_, '_>,
    session: &CompilerSession,
    known_calls: KnownCallSemantics<'_>,
    refusals: &mut Option<&mut Vec<Refusal>>,
) -> Plan {
    plan_folds_with(
        func,
        resources,
        Some(session),
        known_calls,
        refusals,
        &mut None,
    )
}

/// Plans folds and devirtualizations in one walk.
///
/// **Devirtualization rides along with folding rather than running as a pass of its own**, and the
/// reason is entirely the dataflow analysis: resolving a callee needs exactly the analysis folding
/// has already built, and that analysis *is* the cost.
fn plan_folds_and_devirtualizations(
    func: &Function,
    resources: FoldResources<'_, '_>,
    session: Option<&CompilerSession>,
    known_calls: KnownCallSemantics<'_>,
) -> (Plan, Vec<Devirtualization>) {
    let mut devirtualizations = Vec::new();
    let plan = plan_folds_with(
        func,
        resources,
        session,
        known_calls,
        &mut None,
        &mut session.map(|_| &mut devirtualizations),
    );
    (plan, devirtualizations)
}

fn dispatch_callee(operation: &Operation) -> Option<&mir::Value> {
    operation.operands.get(operation.dispatch_callee_index()?)
}

fn is_indirect_callee(callee: &mir::Value) -> bool {
    !matches!(callee, mir::Value::Function(_))
}

/// Replaces `block`'s invoke by a call to `callee` typed `ty`, which cannot fail, followed by a
/// jump to the invoke's normal successor. The call keeps its metadata.
fn demote_invoke(
    edit: &mut FunctionEdit,
    block_id: BlockId,
    callee: FunctionId,
    ty: CallImplType,
    env: ModuleEnv<'_>,
) {
    let block = edit.block_mut(block_id);
    let TerminatorKind::Invoke {
        operation, normal, ..
    } = &block.terminator.kind
    else {
        unreachable!("planned against an Invoke");
    };
    let normal = *normal;
    let mut operation = operation.clone();
    operation.operands[0] = mir::Value::Function(callee);
    let OperationKind::Call { ty: call_ty, .. } = &mut operation.kind else {
        unreachable!("only calls are demoted");
    };
    *call_ty = b(ty);
    let span = block.terminator.span;
    block.terminator = Terminator::goto(span, normal);
    // An infallible call carries a scalar result as a value.
    let store = scalar_arguments::normalize_call_result(edit, &mut operation, env);
    let block = edit.block_mut(block_id);
    block.operations.push(operation);
    block.operations.extend(store);
}

/// Demotes each invoke whose direct callee cannot fail to a call typed with the callee's effects.
///
/// A call keeps the type of the site that wrote it. Once inlining or devirtualization names its
/// callee, that type may be wider than the callee's own, as for a callback parameter typed
/// `! fallible` bound to a pure function. A direct call reaches the callee's own entry, whose
/// conventions follow the callee's type; effects that cannot fail have no variables, so they need
/// no instantiation.
pub(crate) fn narrow_infallible_direct_invokes(
    func: &Function,
    env: ModuleEnv<'_>,
    original_of: impl Fn(FunctionId) -> FunctionId,
) -> Option<Function> {
    let narrowed: Vec<_> = func
        .blocks()
        .filter_map(|block| {
            let TerminatorKind::Invoke { operation, .. } = &func.block(block).terminator().kind
            else {
                return None;
            };
            let (mir::Value::Function(callee), OperationKind::Call { ty, .. }) =
                (&operation.operands[0], &operation.kind)
            else {
                return None;
            };
            let original = original_of(*callee);
            let effects = &env
                .module_by_id(original.module)?
                .get_function_by_id(original.function)?
                .definition
                .ty_scheme
                .ty
                .effects;
            if !effects.cannot_fail() {
                return None;
            }
            let mut ty = (**ty).clone();
            ty.fn_ty.effects = effects.clone();
            Some((block, *callee, ty))
        })
        .collect();
    if narrowed.is_empty() {
        return None;
    }
    let mut edit = FunctionEdit::new(func.clone());
    for (block, callee, ty) in narrowed {
        demote_invoke(&mut edit, block, callee, ty, env);
    }
    // The error edges died with their invokes.
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some(edit.finish_unverified())
}

// Naming a resolved callee directly. A closed dictionary entry's captured evidence is inserted
// immediately after the callee, which is the hidden-evidence prefix used by calls, clones, and
// drops. The `dict_entry` that produced the place is usually left unread by the rewrite, and
// `dce.rs` removes it.
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
        if !devirtualized.hidden_evidence.is_empty() {
            let mut operands = operation.operands.to_vec();
            operands.splice(
                devirtualized.operand + 1..devirtualized.operand + 1,
                devirtualized
                    .hidden_evidence
                    .iter()
                    .map(|evidence| mir::Value::Evidence(Box::new(evidence.clone()))),
            );
            operation.operands = operands.into_boxed_slice();
        }
    }
}

/// Every consumer of the planner's dataflow facts must be represented here. Stop at the first
/// possible consumer; bodies without one need neither analysis nor a replay of their operations.
fn may_have_fold_consumer(func: &Function, devirtualize: bool) -> bool {
    let consumes = |operation: &Operation| {
        matches!(
            operation.kind,
            OperationKind::Call { .. } | OperationKind::BuildArray { .. }
        ) || (devirtualize && dispatch_callee(operation).is_some_and(is_indirect_callee))
    };
    func.blocks().any(|block| {
        let block = func.block(block);
        block.operations().iter().any(consumes)
            || match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => consumes(operation),
                TerminatorKind::CondBr { .. } | TerminatorKind::SwitchVariant { .. } => true,
                TerminatorKind::Goto { .. }
                | TerminatorKind::Yield { .. }
                | TerminatorKind::Return { .. }
                | TerminatorKind::PropagateError
                | TerminatorKind::EffectViolation
                | TerminatorKind::FailureDuringCleanup
                | TerminatorKind::InvariantFailure { .. } => false,
            }
    })
}

fn plan_folds_with(
    func: &Function,
    resources: FoldResources<'_, '_>,
    session: Option<&CompilerSession>,
    known_calls: KnownCallSemantics<'_>,
    refusals: &mut Option<&mut Vec<Refusal>>,
    devirtualizations: &mut Option<&mut Vec<Devirtualization>>,
) -> Plan {
    // Keep the detailed-report path unchanged, though it could also skip consumer-free bodies.
    let skip_analysis =
        refusals.is_none() && !may_have_fold_consumer(func, devirtualizations.is_some());
    if skip_analysis && !cfg!(debug_assertions) {
        return Plan::default();
    }
    // Debug builds run the full planner to catch consumers missing from the structural filter.
    #[cfg(debug_assertions)]
    let initial_devirtualizations = devirtualizations.as_ref().map_or(0, |items| items.len());
    let FoldResources {
        growth_base,
        env,
        module_id,
        string_materializer,
    } = resources;
    // A report pays one scan for detailed classification; normal optimization carries none of this
    // provenance and does not classify unknown arguments it will not report.
    let refusal = refusals.is_some().then(|| RefusalContext {
        call_destinations: call_destinations(func),
        loaded_from: loaded_from(func),
    });
    let context = FoldContext {
        func,
        roles: OnceCell::new(),
        evaluator: session.map(|session| ConstEvaluator::new(module_id, session)),
        env,
        analysis: dataflow::analyze(func, env),
        known_calls,
        string_from_static: string_materializer.function,
        refusal,
    };
    let analysis = &context.analysis;
    let mut plan = Plan::default();
    // Constructive folds reserve their growth against the same budgets as inlining, measured
    // only once a call has a rewrite to reserve.
    let mut growth = None;

    for block in func.blocks() {
        // Stepping from the block's entry state, rather than only reading it, lets a fold teach the
        // rest of the walk what it produced: `2 + 3` then `* 7` folds in one pass.
        let mut state = analysis.entry_state(block);
        let basic_block = func.block(block);
        let mut negations = ArithmeticNegations::default();
        for (index, operation) in basic_block.operations().iter().enumerate() {
            let double_negation = negations.double_negation(operation, &state, &context);
            negations.step(operation, &state, &context);
            if let OperationKind::Call { ty, .. } = &operation.kind
                && let Some(destination) = dataflow::call_result_operand(operation)
                    .map(|place| FoldDestination::Place(place.clone()))
                    .or_else(|| operation.result_id().map(FoldDestination::Register))
                && let Some(result) = double_negation
                    .or_else(|| partial_call_outcome(operation, ty, &state, &context))
                    .filter(|rewrite| {
                        context.evaluator.is_some()
                            || !matches!(rewrite, CallRewrite::EqualOrdering)
                    })
                    .or_else(|| {
                        fold_outcome(operation, ty, &state, &context, refusals)
                            .map(CallRewrite::Reification)
                    })
            {
                if growth
                    .get_or_insert_with(|| Growth::new(growth_base, func))
                    .reserve(block, 1, call_rewrite_operation_count(&result))
                {
                    // Known results and newly exposed arithmetic negations can enable another fold.
                    plan.warrants_another_round |=
                        warrants_another_fold_round(&result, &state, analysis);
                    match &destination {
                        FoldDestination::Place(place) => {
                            if let Some(place) = analysis.tracked_place_of(place) {
                                let fact = fact_for_call_rewrite(
                                    &result,
                                    &state,
                                    analysis,
                                    func.constants(),
                                );
                                analysis.set_place_known(&mut state, place, fact);
                            }
                        }
                        FoldDestination::Register(register) => {
                            let fact =
                                fact_for_call_rewrite(&result, &state, analysis, func.constants());
                            analysis.set_register_known(&mut state, *register, fact);
                        }
                    }
                    plan.calls.push(Fold {
                        block,
                        index: OperationIndex::from_index(index),
                        destination,
                        result,
                    });
                    continue;
                }
                record_refusal(
                    operation,
                    NotFoldable::FunctionGrowthBudgetExceeded,
                    refusals,
                );
            }
            if let Some(devirtualizations) = devirtualizations.as_mut()
                && let Some(resolved) = resolved_callee(operation, &state, analysis)
            {
                devirtualizations.push(Devirtualization {
                    site: Site::Operation {
                        block,
                        index: OperationIndex::from_index(index),
                    },
                    operand: resolved.operand,
                    callee: resolved.callee,
                    hidden_evidence: resolved.hidden_evidence,
                });
            }
            if let OperationKind::BuildArray { element_ty } = &operation.kind {
                let known = known_array_elements(operation, &state, analysis);
                if !known.is_empty() {
                    plan.arrays.push(ArrayElements {
                        block,
                        index: OperationIndex::from_index(index),
                        element_ty: *element_ty,
                        known,
                    });
                }
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
                    && let Some(destination) = dataflow::call_result_operand(operation)
                {
                    if growth
                        .get_or_insert_with(|| Growth::new(growth_base, func))
                        .reserve(block, 1, reification_operation_count(&result))
                    {
                        // An evaluated fallible call yields a constant and removes an error edge.
                        plan.warrants_another_round = true;
                        plan.invokes.push(InvokeFold {
                            block,
                            destination: destination.clone(),
                            result,
                            normal: *normal,
                        });
                        continue;
                    }
                    record_refusal(
                        operation,
                        NotFoldable::FunctionGrowthBudgetExceeded,
                        refusals,
                    );
                }
                if let Some((callee, ty)) = proven_nonzero_arithmetic(operation, &state, &context) {
                    plan.nonzero_invokes.push((block, callee, ty));
                    plan.warrants_another_round = true;
                    continue;
                }
                if let Some(devirtualizations) = devirtualizations.as_mut()
                    && let Some(resolved) = resolved_callee(operation, &state, analysis)
                {
                    devirtualizations.push(Devirtualization {
                        site: Site::Terminator { block },
                        operand: resolved.operand,
                        callee: resolved.callee,
                        hidden_evidence: resolved.hidden_evidence,
                    });
                }
            }
            TerminatorKind::CondBr {
                condition,
                then_target,
                else_target,
            } => {
                if let Some(taken) = known_condition(condition, &state, func) {
                    // Deciding a branch deletes an arm, which is new for every later pass.
                    plan.warrants_another_round = true;
                    plan.branches
                        .push((block, if taken { *then_target } else { *else_target }));
                }
            }
            TerminatorKind::SwitchVariant {
                tag,
                cases,
                default,
            } => {
                if let Some(target) = known_variant_target(tag, cases, *default, &state) {
                    plan.warrants_another_round = true;
                    plan.branches.push((block, target));
                }
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::Return { .. }
            | TerminatorKind::PropagateError
            | TerminatorKind::EffectViolation
            | TerminatorKind::FailureDuringCleanup
            | TerminatorKind::InvariantFailure { .. } => {}
        }
    }
    #[cfg(debug_assertions)]
    if skip_analysis {
        debug_assert!(plan.is_empty() && !plan.warrants_another_round);
        debug_assert_eq!(
            devirtualizations.as_ref().map_or(0, |items| items.len()),
            initial_devirtualizations,
        );
    }
    plan
}

/// Whether a rewrite exposes a known value or arithmetic negation to the next folding round.
///
/// Deliberately answers without building the fact: literal and array facts require cloning their
/// representation, and this is asked about every planned fold rather than only those writing a
/// place the analysis tracks.
fn warrants_another_fold_round(rewrite: &CallRewrite, state: &State, analysis: &Analysis) -> bool {
    match rewrite {
        CallRewrite::Reification(
            Reification::Constant(_)
            | Reification::BareFunction(_)
            | Reification::Array { .. }
            | Reification::Tag { .. },
        )
        | CallRewrite::EqualOrdering => true,
        // A constructed string is deliberately unknown to the literal dataflow. Its constructor
        // is terminal, and the final string pass can fuse it directly into a static append.
        CallRewrite::Reification(Reification::String(_)) => false,
        // Negation reproduces an argument the analysis already did not know.
        CallRewrite::Negate(_) => false,
        // A binary operation rewritten to negation can expose a double negation next round.
        CallRewrite::ArithmeticNegation { .. } => true,
        CallRewrite::Copy(source) | CallRewrite::Store(source) => {
            analysis.read_is_known(source, state)
        }
    }
}

fn fact_for_call_rewrite(
    rewrite: &CallRewrite,
    state: &State,
    analysis: &Analysis,
    constants: &[Constant],
) -> Fact {
    match rewrite {
        CallRewrite::Reification(reification) => fact_for_reification(reification),
        CallRewrite::Copy(source) | CallRewrite::Store(source) => {
            analysis.read_fact(source, constants, state)
        }
        CallRewrite::EqualOrdering => Fact::Known(Const::VariantTag(ustr(ORDERING_EQUAL))),
        // Negation does not establish a literal fact here; the next fold can evaluate the native.
        CallRewrite::Negate(_) | CallRewrite::ArithmeticNegation { .. } => Fact::Unknown,
    }
}

/// A block-local negation result and its operand: an unchanged place, or a value.
#[derive(Clone)]
struct ArithmeticNegation {
    kind: KnownCallee,
    source: mir::Value,
    /// The place `source` names, `None` for a value, which nothing can change.
    source_place: Option<PlaceId>,
}

/// Available negations over non-escaping storage, and in the values loaded from it. Copying a
/// result preserves its origin, and so does loading it, but any write to the original operand
/// invalidates the relation; a write to the result's root invalidates only the stored result.
/// Unknown operations clear the table. Starting empty in each block avoids moving reads across
/// joins or loop iterations; the normal fold rounds and block merging expose further local
/// opportunities.
#[derive(Default)]
struct ArithmeticNegations {
    places: FxHashMap<PlaceId, ArithmeticNegation>,
    values: FxHashMap<ValueId, ArithmeticNegation>,
}

impl ArithmeticNegations {
    fn call<'a>(
        operation: &'a Operation,
        state: &State,
        context: &FoldContext<'_>,
    ) -> Option<(KnownCallee, &'a mir::Value)> {
        let OperationKind::Call { ty, .. } = &operation.kind else {
            return None;
        };
        if !ty.effects().is_empty() || ty.result_convention != CallResultConvention::Value {
            return None;
        }
        let call = dataflow::call_operands(operation)?;
        let [(source, ArgConvention::Let)] = call.arguments.as_slice() else {
            return None;
        };
        let callee = match call.callee {
            mir::Value::Function(callee) => *callee,
            operand => match state.place(context.analysis.tracked_place_of(operand)?) {
                Fact::Known(Const::Function(callee)) => callee,
                _ => return None,
            },
        };
        let known = context.known_calls.resolve(callee)?;
        matches!(known, KnownCallee::IntNeg | KnownCallee::FloatNeg).then_some((known, *source))
    }

    fn double_negation(
        &self,
        operation: &Operation,
        state: &State,
        context: &FoldContext<'_>,
    ) -> Option<CallRewrite> {
        let (kind, source) = Self::call(operation, state, context)?;
        let first = match source {
            mir::Value::Register(id) if self.values.contains_key(id) => &self.values[id],
            _ => self
                .places
                .get(&context.analysis.tracked_place_of(source)?)?,
        };
        (first.kind == kind).then(|| context.copy_of(first.source.clone()))
    }

    fn forget_write(&mut self, destination: &mir::Value, analysis: &Analysis) {
        let Some(place) = analysis.place_of(destination) else {
            self.places.clear();
            self.values.clear();
            return;
        };
        let root = analysis.root_of_place(place);
        let source_unchanged = |negation: &ArithmeticNegation| {
            negation
                .source_place
                .is_none_or(|source| analysis.root_of_place(source) != root)
        };
        self.places.retain(|place, negation| {
            analysis.root_of_place(*place) != root && source_unchanged(negation)
        });
        self.values.retain(|_, negation| source_unchanged(negation));
    }

    /// The operand of a negation: a tracked place, or a value.
    fn source_place(source: &mir::Value, context: &FoldContext<'_>) -> Option<Option<PlaceId>> {
        if let Some(place) = context.analysis.tracked_place_of(source) {
            return Some(Some(place));
        }
        context.is_value(source).then_some(None)
    }

    fn clear(&mut self) {
        self.places.clear();
        self.values.clear();
    }

    fn step(&mut self, operation: &Operation, state: &State, context: &FoldContext<'_>) {
        let analysis = &context.analysis;
        match &operation.kind {
            OperationKind::Call { ty, .. } => {
                let Some(call) = dataflow::call_operands(operation) else {
                    self.clear();
                    return;
                };
                if !ty.effects().is_empty()
                    || ty.result_convention != CallResultConvention::Value
                    || call
                        .arguments
                        .iter()
                        .any(|(_, convention)| *convention != ArgConvention::Let)
                {
                    self.clear();
                    return;
                }
                // A call writes its result slot, or defines its result register, which nothing else
                // names yet.
                if let Some(result) = operation.result_id() {
                    if let Some((kind, source)) = Self::call(operation, state, context)
                        && let Some(source_place) = Self::source_place(source, context)
                    {
                        self.values.insert(
                            result,
                            ArithmeticNegation {
                                kind,
                                source: source.clone(),
                                source_place,
                            },
                        );
                    }
                    return;
                }
                let Some(destination) = dataflow::call_result_operand(operation) else {
                    self.clear();
                    return;
                };
                self.forget_write(destination, analysis);
                if let Some((kind, source)) = Self::call(operation, state, context)
                    && let Some(source_place) = Self::source_place(source, context)
                    && let Some(place) = analysis.tracked_place_of(destination)
                    && source_place.is_none_or(|source_place| {
                        analysis.root_of_place(place) != analysis.root_of_place(source_place)
                    })
                {
                    self.places.insert(
                        place,
                        ArithmeticNegation {
                            kind,
                            source: source.clone(),
                            source_place,
                        },
                    );
                }
            }
            OperationKind::Memcpy => {
                let [source, destination] = operation.operands.as_ref() else {
                    self.clear();
                    return;
                };
                let origin = analysis
                    .tracked_place_of(source)
                    .and_then(|place| self.places.get(&place))
                    .cloned();
                self.forget_write(destination, analysis);
                if let Some(origin) = origin
                    && let Some(place) = analysis.tracked_place_of(destination)
                    && origin.source_place.is_none_or(|source_place| {
                        analysis.root_of_place(place) != analysis.root_of_place(source_place)
                    })
                {
                    self.places.insert(place, origin);
                }
            }
            OperationKind::Load => {
                if let Some(id) = operation.result_id()
                    && let Some(origin) = analysis
                        .tracked_place_of(&operation.operands[0])
                        .and_then(|place| self.places.get(&place))
                {
                    self.values.insert(id, origin.clone());
                }
            }
            OperationKind::Store => {
                // Storing a negation's result register gives the slot that negation.
                let origin = match &operation.operands[0] {
                    mir::Value::Register(id) => self.values.get(id).cloned(),
                    _ => None,
                };
                self.forget_write(&operation.operands[1], analysis);
                if let Some(origin) = origin
                    && let Some(place) = analysis.tracked_place_of(&operation.operands[1])
                    && origin.source_place.is_none_or(|source_place| {
                        analysis.root_of_place(place) != analysis.root_of_place(source_place)
                    })
                {
                    self.places.insert(place, origin);
                }
            }
            OperationKind::Alloca { .. }
            | OperationKind::DictEntry { .. }
            | OperationKind::Subfield { .. }
            | OperationKind::StackSave => {}
            _ => self.clear(),
        }
    }
}

/// Retarget only a concrete std call whose divisor facts exclude both zero representations.
fn proven_nonzero_arithmetic(
    operation: &Operation,
    state: &State,
    context: &FoldContext<'_>,
) -> Option<(FunctionId, CallImplType)> {
    let OperationKind::Call { .. } = &operation.kind else {
        return None;
    };
    let mir::Value::Function(callee) = operation.operands.first()? else {
        return None;
    };
    let known = context.known_calls.resolve(*callee)?;
    let (replacement, replacement_ty) = context.known_calls.callees.nonzero_arithmetic(known)?;
    let call = dataflow::call_operands(operation)?;
    // These concrete primitives have no hidden evidence or ownership transfer.
    if !call.extras.is_empty() || !call.captures.is_empty() || call.arguments.len() != 2 {
        return None;
    }
    let (divisor, _) = call.arguments.get(1)?;
    let fact = context.argument_fact(divisor, state);
    let nonzero = match fact {
        Fact::Known(Const::Literal(value)) if known == KnownCallee::FloatDiv => value
            .as_primitive_ty::<Float>()
            .is_some_and(|value| value.into_inner() != 0.0),
        Fact::Known(Const::Literal(value)) => value
            .as_primitive_ty::<isize>()
            .is_some_and(|value| *value != 0),
        Fact::Outcomes(values) if known != KnownCallee::FloatDiv => values
            .iter()
            .all(|value| matches!(value, dataflow::Outcome::Int(value) if *value != 0)),
        _ => false,
    };
    nonzero.then(|| (replacement, replacement_ty.clone()))
}

/// Applies known-callee rewrites that need less than the whole of the arguments.
///
/// Most are identities: the result is one of the inputs, or a constant, even though an argument is
/// unknown. Other rules replace binary arithmetic with the declared unary negation, or replace
/// [`BoolNot`](KnownCallee::BoolNot) with the comparison MIR already has.
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
    let call = dataflow::call_operands(operation)?;
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
        match context.argument_fact(argument(index)?, state) {
            Fact::Known(Const::Literal(literal)) => Some(Rc::unwrap_or_clone(literal)),
            _ => None,
        }
    };
    // Deliberately not `literal(index).is_some()`: reading a fact clones what it holds, and the
    // callees below that ask only whether an argument is known are the most common calls in a body.
    let is_known = |index: usize| {
        argument(index).is_some_and(|argument| context.argument_is_known(argument, state))
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
    let copy = |index| {
        argument(index)
            .cloned()
            .map(|source| context.copy_of(source))
    };
    let negate = |index, float| {
        let (callee, ty) = if float {
            context.known_calls.callees.float_neg()
        } else {
            context.known_calls.callees.int_neg()
        };
        argument(index)
            .cloned()
            .map(|source| CallRewrite::ArithmeticNegation {
                source,
                callee,
                ty: ty.clone(),
            })
    };
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
        Some(CallRewrite::Reification(Reification::Constant(Constant {
            ty: ty.ret(),
            representation,
        })))
    };

    // Layout expansion exposes constant integer offset arithmetic. These are the same wrapping
    // operations as the registered natives, and need no interpreter or constructive reification.
    let integer = |index| literal(index)?.as_primitive_ty::<isize>().copied();
    let constant = match known {
        KnownCallee::IntAdd => integer(0).zip(integer(1)).map(|(a, b)| a.wrapping_add(b)),
        KnownCallee::IntSub => integer(0).zip(integer(1)).map(|(a, b)| a.wrapping_sub(b)),
        KnownCallee::IntMul => integer(0).zip(integer(1)).map(|(a, b)| a.wrapping_mul(b)),
        KnownCallee::IntNeg => integer(0).map(isize::wrapping_neg),
        _ => None,
    };
    if let Some(value) = constant {
        return Some(CallRewrite::Reification(Reification::Constant(Constant {
            ty: ty.ret(),
            representation: LiteralValue::new_native(value),
        })));
    }

    // Physical folding has no native evaluator: materialize the unsigned range predicate here,
    // giving the same results as its native body and Wasm lowering for target-range values.
    if known == KnownCallee::ArrayOffsetInBounds
        && let Some((offset, length)) = integer(0).zip(integer(1))
    {
        return Some(CallRewrite::Reification(Reification::Constant(Constant {
            ty: ty.ret(),
            representation: LiteralValue::new_native(
                offset.cast_unsigned() < length.cast_unsigned(),
            ),
        })));
    }

    // Float excludes NaN, so reflexive comparisons obey the same laws as integers.
    if same_argument(0, 1) {
        let predicate = match known {
            KnownCallee::IntLt
            | KnownCallee::IntGt
            | KnownCallee::ArrayOffsetInBounds
            | KnownCallee::FloatLt
            | KnownCallee::FloatGt => Some(false),
            KnownCallee::IntLe
            | KnownCallee::IntGe
            | KnownCallee::FloatLe
            | KnownCallee::FloatGe
            | KnownCallee::IntEq
            | KnownCallee::FloatEq
            | KnownCallee::BoolEq => Some(true),
            _ => None,
        };
        if let Some(value) = predicate {
            return Some(CallRewrite::Reification(Reification::Constant(Constant {
                ty: ty.ret(),
                representation: LiteralValue::new_native(value),
            })));
        }
    }

    match known {
        KnownCallee::IntAdd if int_is(0, 0) => copy(1),
        KnownCallee::IntAdd if int_is(1, 0) => copy(0),
        KnownCallee::IntSub if same_argument(0, 1) => zero(),
        KnownCallee::IntSub if int_is(1, 0) => copy(0),
        KnownCallee::IntSub if int_is(0, 0) => negate(1, false),
        KnownCallee::IntMul if int_is(0, 0) || int_is(1, 0) => zero(),
        KnownCallee::IntMul if int_is(0, 1) => copy(1),
        KnownCallee::IntMul if int_is(1, 1) => copy(0),
        KnownCallee::IntMul if int_is(0, -1) => negate(1, false),
        KnownCallee::IntMul if int_is(1, -1) => negate(0, false),
        KnownCallee::IntCmp | KnownCallee::FloatCmp if same_argument(0, 1) => {
            Some(CallRewrite::EqualOrdering)
        }
        // The two rewrites below name their whole argument rather than a literal one, so both step
        // aside for a *known* argument: evaluating the call outright produces a constant, which is
        // better than copying the cell that held it or comparing it at run time.
        KnownCallee::IntFromInt if !is_known(0) => copy(0),
        // Negation is not an identity but a rewrite: the call becomes the one comparison MIR uses
        // to test a boolean, which every later pass reads.
        KnownCallee::BoolNot if !is_known(0) => argument(0).cloned().map(CallRewrite::Negate),

        // `+0.0` is not an identity for `-0.0`, and multiplying an unknown negative value by
        // `+0.0` produces `-0.0`. Both signs are observable through formatting and hashing.
        KnownCallee::FloatAdd if float_is(0, -0.0) => copy(1),
        KnownCallee::FloatAdd if float_is(1, -0.0) => copy(0),
        KnownCallee::FloatSub if same_argument(0, 1) => zero(),
        KnownCallee::FloatSub if float_is(1, 0.0) => copy(0),
        KnownCallee::FloatSub if float_is(0, -0.0) => negate(1, true),
        KnownCallee::FloatMul if float_is(0, 1.0) => copy(1),
        KnownCallee::FloatMul if float_is(1, 1.0) => copy(0),
        KnownCallee::FloatMul if float_is(0, -1.0) => negate(1, true),
        KnownCallee::FloatMul if float_is(1, -1.0) => negate(0, true),
        KnownCallee::FloatCmp if same_argument(0, 1) => Some(CallRewrite::EqualOrdering),
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
/// Closed dictionary entries may carry hidden evidence just like closures. Known-callee facts keep
/// that evidence beside the function identity so devirtualization can expose the complete direct
/// callable, rather than silently dropping its environment.
fn resolved_callee(
    operation: &Operation,
    state: &State,
    analysis: &Analysis,
) -> Option<ResolvedCallee> {
    let operand = operation.dispatch_callee_index()?;
    let callee = operation.operands.get(operand)?;
    if matches!(callee, mir::Value::Function(_)) {
        return None;
    }
    let place = analysis.place_of(callee)?;
    if !matches!(analysis.root_of_place(place), Root::DictEntry(_)) {
        return None;
    }
    let (callee, hidden_evidence) = match state.place(place) {
        Fact::Known(Const::Function(id)) => (id, Rc::default()),
        Fact::Known(Const::ClosedFunction {
            function,
            hidden_evidence,
        }) => (function, hidden_evidence),
        _ => return None,
    };
    Some(ResolvedCallee {
        operand,
        callee,
        hidden_evidence,
    })
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
            record_refusal(operation, reason, refusals);
            None
        }
    }
}

fn record_refusal(
    operation: &Operation,
    reason: NotFoldable,
    refusals: &mut Option<&mut Vec<Refusal>>,
) {
    if let Some(refusals) = refusals {
        refusals.push(Refusal {
            site: operation.span.location,
            callee: match &operation.operands[0] {
                mir::Value::Function(id) => Some(*id),
                _ => None,
            },
            reason,
        });
    }
}

fn fact_for_reification(reification: &Reification) -> Fact {
    match reification {
        Reification::Constant(constant) => {
            Fact::Known(Const::literal(constant.representation.clone()))
        }
        Reification::Array {
            element_ty,
            elements,
        } => Fact::Known(Const::Array {
            element_ty: *element_ty,
            elements: Rc::from(&elements[..]),
        }),
        Reification::BareFunction(function) => Fact::Known(Const::Function(*function)),
        Reification::Tag { tag, .. } => Fact::Known(Const::VariantTag(*tag)),
        // Owned strings are not constants: the recipe constructs a fresh value at run time.
        Reification::String(_) => Fact::Unknown,
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
    if let mir::Value::Register(id) = operand
        && let Some(source) = refusal.loaded_from.get(id)
    {
        return why_argument_unknown(source, state, analysis, refusal);
    }
    let Some(place) = analysis.place_of(operand) else {
        return why_operand_names_no_place(operand, state, analysis, refusal);
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
        Fact::Unknown | Fact::Outcomes(_) => match root {
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
    refusal: &RefusalContext,
) -> NotFoldable {
    let mir::Value::Register(id) = operand else {
        return NotFoldable::ArgumentStorageNotModelled;
    };
    match state.register(*id) {
        // A call's result register is unknown because that call did not fold.
        Some(Fact::Unknown) if refusal.call_destinations.contains(id) => {
            NotFoldable::ArgumentFromCall
        }
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

/// The `alloca`s that some call in this function writes its result into, and the registers that
/// some call defines as its result.
///
/// Used to separate "this argument is unknown because the call producing it did not fold" — which
/// needs no new machinery, only the other refusal lifted — from "unknown because the analysis does
/// not model what wrote it", which does.
///
/// Deliberately approximate: it matches a call's result operand by register identity, so it sees
/// the `%r = alloca; call f(.., %r)` shape that lowering actually emits and not a write through a
/// `subfield`. It reads call layout through [`dataflow::call_result_operand`]
/// rather than restating it.
/// This feeds a report, not a rewrite, so an approximation that is honest about its edges is the
/// right trade — a precise answer would mean recording a cause alongside every `Unknown` the
/// dataflow produces.
fn call_destinations(func: &Function) -> FxHashSet<ValueId> {
    let mut destinations = FxHashSet::default();
    let mut record = |operation: &Operation| {
        if let OperationKind::Call { .. } = &operation.kind
            && let Some(id) = match dataflow::call_result_operand(operation) {
                Some(mir::Value::Register(id)) => Some(*id),
                Some(_) => None,
                None => operation.result_id(),
            }
        {
            destinations.insert(id);
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

/// The place each `load` of the function read.
fn loaded_from(func: &Function) -> FxHashMap<ValueId, mir::Value> {
    func.blocks()
        .flat_map(|block| func.block(block).operations())
        .filter(|operation| matches!(operation.kind, OperationKind::Load))
        .filter_map(|operation| Some((operation.result_id()?, operation.operands[0].clone())))
        .collect()
}

/// The value of a branch condition, when the analysis knows it.
fn known_condition(condition: &mir::Value, state: &State, func: &Function) -> Option<bool> {
    let literal = match condition {
        mir::Value::Constant(id) => &func.constant(*id).representation,
        mir::Value::Register(id) => match state.register(*id)? {
            Fact::Known(Const::Literal(literal)) => literal,
            _ => return None,
        },
        _ => return None,
    };
    literal.as_primitive_ty::<bool>().copied()
}

/// A switch is decided when every possible semantic tag selects the same successor.
fn known_variant_target(
    tag: &mir::Value,
    cases: &[(Ustr, BlockId)],
    default: BlockId,
    state: &State,
) -> Option<BlockId> {
    let mir::Value::Register(id) = tag else {
        return None;
    };
    let tags = state.register(*id)?.variant_tags()?;
    let mut targets = tags.map(|tag| {
        cases
            .iter()
            .find_map(|(case, target)| (*case == tag).then_some(*target))
            .unwrap_or(default)
    });
    let first = targets.next()?;
    targets.all(|target| target == first).then_some(first)
}

impl FoldContext<'_> {
    /// What the analysis knows of a call argument, whether it is a place or a value.
    fn argument_fact(&self, operand: &mir::Value, state: &State) -> Fact {
        self.analysis
            .read_fact(operand, self.func.constants(), state)
    }

    /// Whether [`Self::argument_fact`] is known, without materializing it.
    fn argument_is_known(&self, operand: &mir::Value, state: &State) -> bool {
        self.analysis.read_is_known(operand, state)
    }

    /// Whether `operand` is a value rather than a place.
    fn is_value(&self, operand: &mir::Value) -> bool {
        match operand {
            mir::Value::Constant(_) => true,
            mir::Value::Parameter(_) => self
                .roles
                .get_or_init(|| ValueRoles::derive(self.func))
                .get(operand, self.func.constants())
                .is_some_and(|role| matches!(*role, ValueRole::Materialized(MirType::Lowered(_)))),
            mir::Value::Register(_) if self.analysis.place_of(operand).is_none() => self
                .roles
                .get_or_init(|| ValueRoles::derive(self.func))
                .get(operand, self.func.constants())
                .is_some_and(|role| matches!(*role, ValueRole::Materialized(MirType::Lowered(_)))),
            _ => false,
        }
    }

    /// The rewrite making a call's result a copy of its argument `source`.
    fn copy_of(&self, source: mir::Value) -> CallRewrite {
        if self.is_value(&source) {
            CallRewrite::Store(source)
        } else {
            CallRewrite::Copy(source)
        }
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
    let evaluator = context.evaluator.as_ref().ok_or(NotFoldable::NoBody)?;
    let Some(call) = dataflow::call_operands(operation) else {
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
    if context
        .known_calls
        .resolve(callee)
        .is_some_and(KnownCallee::is_optimization_barrier)
    {
        return Err(NotFoldable::OptimizationBarrier);
    }

    // Constructive string reification ends in this call. Evaluating it would produce the same
    // `StaticStr` plus `string_from_static` sequence again, so it is the fixed point rather than a
    // fold candidate.
    if callee == context.string_from_static {
        return Err(NotFoldable::ConstructiveMaterializer);
    }

    if !call.captures.is_empty() {
        return Err(NotFoldable::ClosureCaptures);
    }
    let mut arguments = Vec::with_capacity(call.extras.len() + call.arguments.len());
    for extra in call.extras {
        match extra {
            mir::Value::Dictionary(id) => {
                arguments.push(ConstArgument::Dictionary(ClosedTraitDictionary::bare(*id)))
            }
            mir::Value::Evidence(evidence) => {
                let HiddenEvidenceArgValue::TraitDictionary(dictionary) =
                    static_evidence_value(evidence)
                else {
                    return discard(arguments, NotFoldable::EvidenceNotKnown);
                };
                arguments.push(ConstArgument::Dictionary(dictionary));
            }
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
        // Unit has exactly one initialized value. A projection from an otherwise unknown
        // parameter therefore carries all the information compile-time evaluation needs, even
        // though the place dataflow quite correctly knows nothing about its containing aggregate.
        if parameter.ty == Type::unit() {
            arguments.push(ConstArgument::Value(Value::unit()));
            continue;
        }
        let known = Some(context.argument_fact(operand, state));
        match known {
            Some(Fact::Known(Const::Literal(literal)))
                if literal.has_representation_type_in(parameter.ty, &context.env) =>
            {
                arguments.push(ConstArgument::Value(
                    Rc::unwrap_or_clone(literal).into_value(),
                ))
            }
            Some(Fact::Known(Const::Array {
                element_ty,
                elements,
            })) if parameter.ty == array_type(element_ty) => {
                arguments.push(ConstArgument::Value(array_value_from_vec(
                    elements
                        .iter()
                        .cloned()
                        .map(LiteralValue::into_value)
                        .collect(),
                )))
            }
            Some(Fact::Known(Const::Function(function))) if parameter.ty.is_function() => {
                arguments.push(ConstArgument::Value(Value::function(function)))
            }
            Some(Fact::Known(Const::VariantTag(tag)))
                if is_tag_scalar(parameter.ty, &context.env) =>
            {
                arguments.push(ConstArgument::Value(Value::unit_variant(tag)))
            }
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

    let value = evaluator.try_call(
        callee,
        ty.effects(),
        ty.result_convention,
        ty.ret(),
        arguments,
        operation.span.location,
    )?;
    let reified = reify(&value, ty.ret(), &context.env);
    value.discard_storage();
    reified
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

    #[test]
    fn proven_nonzero_divisors_remove_only_impossible_error_edges() {
        for (expression, helper) in [
            ("idiv(x, 3)", "idiv_nonzero"),
            ("idiv(x, -1)", "idiv_nonzero"),
            ("rem(x, 3)", "rem_nonzero"),
            ("mod(x, -3)", "mod_nonzero"),
            ("idiv(x, if x < 0 { -3 } else { 3 })", "idiv_nonzero"),
        ] {
            let body = optimized_main(&format!("fn main(x: int) -> int {{ {expression} }}"));
            assert!(body.contains(helper), "{expression}: {body}");
            assert!(!body.contains("invoke "), "{expression}: {body}");
        }
        let body = optimized_main("fn main(x: float) -> float { x / 3.0 }");
        assert!(body.contains("div_float_nonzero"), "{body}");
        assert!(!body.contains("invoke "), "{body}");
        for expression in [
            "idiv(x, 0)",
            "rem(x, 0)",
            "mod(x, 0)",
            "idiv(x, if x < 0 { 0 } else { 3 })",
            "idiv(3, x)",
        ] {
            let body = optimized_main(&format!("fn main(x: int) -> int {{ {expression} }}"));
            assert!(body.contains("invoke "), "{expression}: {body}");
            assert!(!body.contains("_nonzero"), "{expression}: {body}");
        }
        for divisor in ["0.0", "-0.0", "x"] {
            let body = optimized_main(&format!("fn main(x: float) -> float {{ x / {divisor} }}"));
            assert!(body.contains("invoke "), "{divisor}: {body}");
            assert!(!body.contains("div_float_nonzero"), "{divisor}: {body}");
        }
    }

    /// An array literal stores each element into a fresh slot only for the construction to read it
    /// straight back. Every slot whose contents the analysis knows is replaced by the constant
    /// itself, and DCE then removes the slot. The middle element is deliberately unknown: it must
    /// keep its slot, which is what shows the substitution is per-operand rather than all-or-nothing.
    #[test]
    fn known_array_element_slots_become_constants() {
        let body = optimized_main("fn main(n: int) -> [int] { [1, n, 3] }");
        let (_, operands) = body
            .split_once("build_array<int> [")
            .expect("the array is still built");
        let operands: Vec<_> = operands.split(']').next().unwrap().split(", ").collect();
        assert!(
            matches!(operands[..], ["@c0", slot, "@c1"] if slot.starts_with("%r")),
            "the known elements must be named directly:\n{body}"
        );
        assert_eq!(
            body.matches("store @").count(),
            0,
            "no element literal should be stored into a slot first:\n{body}"
        );
        assert_eq!(
            body.matches("alloca").count(),
            1,
            "only the unknown element keeps a slot:\n{body}"
        );
    }

    /// An evaluated comparison is a tag, which folds to its shell; a comparison of a value with
    /// itself is `Equal` even when the value is unknown. A known tag is an argument evaluation
    /// accepts, even for a callee kept out of line.
    #[test]
    fn evaluated_tags_fold_to_their_shells() {
        let flip = "#[inline(never)] fn flip(o: Ordering) -> Ordering {
            match o { Less => Greater, Equal => Equal, Greater => Less }
        }";
        for (source, tag) in [
            ("fn main() -> Ordering { cmp(1, 2) }", "Less"),
            ("fn main(x: int) -> Ordering { cmp(x, x) }", "Equal"),
            (
                &format!("{flip}\nfn main() -> Ordering {{ flip(Less) }}"),
                "Greater",
            ),
        ] {
            let body = optimized_main(source);
            assert!(
                body.contains(&format!("variant {tag}")) && !body.contains("call "),
                "{source}:\n{body}"
            );
        }
    }

    /// A locally constructed variant has a symbolic tag fact, so its semantic switch reduces to
    /// the selected edge without turning that tag into a session-local integer constant.
    #[test]
    fn a_known_switch_variant_becomes_a_jump() {
        let body =
            optimized_main("fn main() -> int { match Some(3) { Some(value) => value, _ => 0 } }");
        assert!(
            !body.contains("switch_variant"),
            "the known constructor must select its arm:\n{body}"
        );
        assert!(
            !body.contains("comp_eq"),
            "selecting a known switch case needs no tag comparison:\n{body}"
        );
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
    /// Asserted over every closed function in the module because the sites are spread across the
    /// specializations the pipeline creates, none of which is named in the source. Open generated
    /// thunks deliberately retain dispatch through their evidence parameters.
    #[test]
    fn a_drop_or_clone_through_a_resolved_dictionary_entry_becomes_direct() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir("fold", "fn main() { [1, 2] |> map(|x| x * x); }");
        let mut function = "";
        let mut has_evidence_parameters = false;
        let mut indirect = Vec::new();
        for line in module.lines().map(str::trim) {
            if let Some(name) = line.strip_prefix("fn ") {
                function = name.split('(').next().unwrap_or(name);
                has_evidence_parameters = line.contains("@extra");
            }
            if !has_evidence_parameters
                && (line.starts_with("drop ") || line.starts_with("clone "))
                && line.contains(" via %r")
            {
                indirect.push(format!("{function}: {line}"));
            }
        }
        assert!(
            indirect.is_empty(),
            "every resolvable drop/clone callee must be named directly, found:\n{}",
            indirect.join("\n")
        );
    }

    #[test]
    fn a_concrete_drop_in_an_open_function_is_still_devirtualized() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "fold",
            "fn open<T>(value: T, n: int) -> T where T: Value {\
                 let mut concrete = [1, 2]; concrete[n] = 3; value\
             }",
        );
        let function = module
            .split("fn open")
            .nth(1)
            .expect("the module defines open")
            .split("\nfn ")
            .next()
            .expect("open has a body");
        assert!(
            function
                .lines()
                .next()
                .is_some_and(|header| header.contains("@extra")),
            "the test must inspect an open function:\n{function}"
        );
        let concrete_drops: Vec<_> = function
            .lines()
            .filter(|line| line.contains("drop [int]"))
            .collect();
        assert!(
            !concrete_drops.is_empty(),
            "the test must retain the concrete local's drop:\n{function}"
        );
        assert!(
            concrete_drops.iter().all(|line| !line.contains(" via %r")),
            "the concrete local's drops must be direct even in an open function:\n{function}"
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
                // An entry of a parameter's dictionary stays indirect; only a constant one resolves.
                if entry.contains("= dict_entry ")
                    && entry.contains(" from dict(")
                    && call.starts_with("call %r")
                {
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
    fn constant_arithmetic_folds_to_a_returned_constant() {
        let main = optimized_main("fn main() -> int { let x = 2 + 3; x * 7 }");
        assert!(
            !main.contains("call "),
            "every call of a constant expression must fold:\n{main}"
        );
        assert!(
            main.contains("= 35") && main.contains("ret @c"),
            "the result must be returned:\n{main}"
        );
    }

    /// Exercise the physical fallback directly, without the native evaluator or whole-std
    /// optimization. The out-of-range cases must fold to false, not become runtime calls.
    #[test]
    fn physical_unsigned_bounds_constants_fold_without_an_evaluator() {
        use super::*;
        use crate::{
            mir::{builder::FunctionBuilder, terminator::Terminator},
            std::{
                STD_MODULE_ID, logic::bool_type, math::int_type,
                string::STRING_FROM_STATIC_FUNCTION_NAME,
            },
        };

        let session = CompilerSession::new();
        let env = session.module_env();
        let std = session.expect_fresh_module(STD_MODULE_ID);
        let local = std
            .get_local_function_id(ustr("array_offset_in_bounds"))
            .unwrap();
        let callee = FunctionId::new(STD_MODULE_ID, local);
        let ty = CallImplType::value(
            std.get_function_by_id(local)
                .unwrap()
                .definition
                .ty_scheme
                .ty
                .clone(),
        );
        let string_from_static = FunctionId::new(
            STD_MODULE_ID,
            std.get_local_function_id(ustr(STRING_FROM_STATIC_FUNCTION_NAME))
                .unwrap(),
        );
        let span = Location::new_synthesized();
        for (offset, length, expected) in [
            (2isize, 3isize, true),
            (3, 3, false),
            (-1, 3, false),
            (0, 0, false),
            (isize::MIN, isize::MAX, false),
            (isize::MAX - 1, isize::MAX, true),
        ] {
            let mut builder = FunctionBuilder::new("bounds".into(), Default::default());
            let block = builder.add_block();
            let arguments = [offset, length].map(|value| {
                let place = builder
                    .append_operation(block, Operation::alloca(span, int_type()))
                    .unwrap();
                let literal =
                    builder.add_constant(int_type(), LiteralValue::new_native(value), &env);
                builder.append_operation(
                    block,
                    Operation::store(span, mir::Value::Constant(literal), place.clone()),
                );
                place
            });
            let result = builder
                .append_operation(block, Operation::alloca(span, bool_type()))
                .unwrap();
            builder.append_operation(
                block,
                Operation::call(
                    span,
                    mir::Value::Function(callee),
                    arguments.into_iter().chain([result]),
                    ty.clone(),
                ),
            );
            builder.set_terminator(block, Terminator::ret(span));
            let body = builder.finish_physical(env);
            let context = FoldContext {
                func: &body,
                roles: OnceCell::new(),
                evaluator: None,
                env,
                analysis: dataflow::analyze(&body, env),
                known_calls: KnownCallSemantics::new(session.known_callees(), &|_| None),
                string_from_static,
                refusal: None,
            };
            let operations = body.block(block).operations();
            let mut state = context.analysis.entry_state(block);
            for operation in &operations[..operations.len() - 1] {
                context.analysis.step(&body, env, operation, &mut state);
            }
            let outcome = partial_call_outcome(operations.last().unwrap(), &ty, &state, &context);
            let Some(CallRewrite::Reification(Reification::Constant(constant))) = outcome else {
                panic!("bounds({offset}, {length}) must fold without an evaluator");
            };
            assert_eq!(
                constant.representation.as_primitive_ty::<bool>(),
                Some(&expected),
                "bounds({offset}, {length})"
            );
        }
    }

    /// A captureless function returned by a folded call is a bare MIR function operand. Keeping it
    /// known lets the same fold walk evaluate the immediately following call; the generic
    /// identity's clone/drop scaffolding then becomes dead together with both function slots.
    #[test]
    fn a_folded_bare_function_result_stays_known() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "fold",
            "fn id(x) { x }\n\
             id(|x, y| (y, x))(1, 1.3)",
        );
        let expression = optimized_function(&module, "<expr>");

        // Folded to a constant tuple, or called directly through the single-store cell and inlined,
        // leaving each field stored from a constant.
        assert!(
            expression.contains("= (1.3, 1)")
                || (expression.contains("store @c1 to") && expression.contains("store @c0 to")),
            "the call through the folded function must itself fold:\n{expression}"
        );
        for spelling in ["alloca", "clone ", "drop ", "call "] {
            assert!(
                !expression.contains(spelling),
                "the bare function's runtime lifetime must be gone:\n{expression}"
            );
        }
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
        assert!(body.contains("ret %p0"), "{body}");
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
            main.contains("ret @c"),
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

    #[test]
    fn arithmetic_identities_become_negations() {
        for (ty, expressions) in [
            ("int", ["0 - x", "-1 * x", "x * -1"]),
            ("float", ["-0.0 - x", "-1.0 * x", "x * -1.0"]),
        ] {
            for expression in expressions {
                let body = optimized_main(&format!("fn main(x: {ty}) -> {ty} {{ {expression} }}"));
                assert_eq!(body.matches("call ").count(), 1, "{expression}: {body}");
                assert!(
                    body.contains(&format!("call std::Num<std::{ty}>::neg")),
                    "{expression}: {body}"
                );
            }
        }
    }

    #[test]
    fn negative_zero_addition_is_elided() {
        for expression in ["x + -0.0", "-0.0 + x"] {
            let body = optimized_main(&format!("fn main(x: float) -> float {{ {expression} }}"));
            assert!(!body.contains("call "), "{expression}: {body}");
        }
    }

    #[test]
    fn double_arithmetic_negation_is_elided() {
        for (ty, expressions) in [
            ("int", ["-(-x)", "-1 * (0 - x)", "let y = -x; -y"]),
            ("float", ["-(-x)", "-1.0 * (-0.0 - x)", "let y = -x; -y"]),
        ] {
            for expression in expressions {
                let body = optimized_main(&format!("fn main(x: {ty}) -> {ty} {{ {expression} }}"));
                assert!(!body.contains("call "), "{expression}: {body}");
            }
        }
    }

    #[test]
    fn double_negation_does_not_forward_across_mutation() {
        for ty in ["int", "float"] {
            let one = if ty == "int" { "1" } else { "1.0" };
            for expression in [
                format!("let mut y = -x; keep(y); y = {one}; -y"),
                format!("let mut y = x; keep(y); let z = -y; y = {one}; -z + y"),
            ] {
                let body = optimized_main(&format!(
                    "fn keep(y: &mut {ty}) {{}} fn main(x: {ty}) -> {ty} {{ {expression} }}"
                ));
                // The second expression negates the value `y` held before the write, read before
                // it; the first folds its overwritten value to a constant rather than copying x.
                if expression.contains("let z") {
                    let write = body.find("store @c").expect(&body);
                    let negated = body
                        .split(&format!("Num<std::{ty}>::add"))
                        .nth(1)
                        .and_then(|call| call.split(['(', ',']).nth(1))
                        .expect(&body);
                    let read = body.find(&format!("{negated}: {ty} = load")).expect(&body);
                    assert!(read < write, "{body}");
                } else {
                    assert!(body.contains("ret @c"), "{body}");
                }
            }
        }
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
