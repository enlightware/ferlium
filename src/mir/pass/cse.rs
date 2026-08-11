// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Common-subexpression elimination over the calls and address computations a body repeats.
//!
//! Two complementary passes run at different points. Before inlining, available-expression
//! analysis merges repeatable calls, copying the first result into the duplicate's out-slot. This
//! covers both caller-rooted `AddressorPlace` calls and environment-independent `Value` calls whose
//! result is `TrivialCopy`. That is the economical point: `swap#spec:[int]` has four calls to
//! `array_index::ref_mut` but only two distinct `(array, index)` pairs, so only two accessor bodies
//! are subsequently copied; `(x - y) * (x - y)` similarly computes the subtraction once. After
//! inlining, dominator-based value numbering merges repeated `subfield` chains which the remaining
//! accessor copies expose.
//!
//! **Addressor availability.** A call is eligible only when its effects permit reevaluation, its
//! callee's summary proves it repeatable, and provenance names the visible argument containing the
//! returned place. The expression key excludes only the out-slot. Calls which receive that storage
//! root mutably invalidate its available addresses; structural writes and stack restoration do too,
//! while writing a value through an addressor-produced leaf does not reallocate its containing
//! object. An `invoke` generates the expression only on its normal edge. Joins intersect available
//! expressions, so a reused pointer always comes from a call which succeeded on every path.
//!
//! **Value availability.** A value call is eligible only when it is statically known, its effects
//! permit compile-time evaluation, all visible arguments use `Let`, and its concrete result is
//! `TrivialCopy`. Its cached result depends on the contents of every argument root and on the first
//! result slot remaining live. Any write to one of those roots invalidates it. Restricting the
//! result to `TrivialCopy` makes the replacement an ordinary `memcpy`; owned results would require
//! explicit clone/drop accounting.
//!
//! **Dominator-based value numbering.** Each operation is keyed by its kind, its type metadata and
//! the *canonical* identity of each operand, so comparing two arbitrarily deep expressions is one
//! key comparison rather than a tree walk: operands are already canonicalized when an operation is
//! reached, which is what keeps this linear. The table is scoped to the dominator tree — entered on
//! the way down and undone on the way up — so a match is available exactly when its definition
//! dominates the use. That misses a value available on some paths only; catching those needs
//! available-expressions and lazy code motion, a much larger machine and not what these bodies want.
//!
//! **The numbering merges two place-producing operations, which differ in what keeps them valid.**
//! A `subfield` *derives* a place from its operand: the base's root and path with one index
//! appended, holding no storage of its own. It is valid exactly where its base is, and the base is
//! valid at the duplicate — that is what the duplicate reads too. Registers are single-assignment,
//! so no intervening write invalidates it; there is no kill for it at all. A `dict_entry` instead
//! *materializes* the function value into a freshly allocated cell, so what it yields lives in the
//! current stack region: a `stack_restore` between two occurrences pops it, and a merged register
//! would name storage that is gone. That is not hypothetical — it is what `bank_account` did before
//! the kill existed. Popping a region therefore forgets every materialized place, and a scoped
//! accessor counts as one.
//!
//! Two classes remain out, each for its own reason:
//!
//! - **A memory reader** — `load`, `comp_eq`, `extract_tag` — needs an aliasing argument about the
//!   writes in between, which is what provenance is for.
//! - **An owned materialized value**, `build_subscript` among them, cannot be merged at all: such a
//!   register must have exactly one consuming use, and merging is precisely what gives it two.
//!   `subscript_member` is place-producing like `dict_entry` but is left out until its redundancy
//!   is measured rather than assumed.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    hir::function::ArgConvention,
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        const_eval::effects_allow_const_eval,
        dominance::Dominance,
        edit::{FunctionEdit, successors},
        operation::Instantiation,
        terminator::{Terminator, TerminatorKind},
        value::ValueId,
    },
    module::{FunctionId, ModuleEnv, id::Id},
    types::{
        r#trait::TraitDictionaryEntryIndex,
        r#type::{CallImplType, CallResultConvention, Type},
        type_properties::concrete_type_is_trivial_copy,
    },
};

use super::{
    dataflow::{Root, call_operands},
    provenance::{AddressorSummary, ResultProvenance},
};

/// A call identity without its out-parameter. The out-parameter is only where the result is stored,
/// not an input to the computation.
#[derive(Clone, PartialEq, Eq, Hash)]
struct CallExpression {
    ty: CallImplType,
    instantiation: Option<Instantiation>,
    operands: Box<[mir::Value]>,
}

#[derive(Clone, PartialEq, Eq)]
enum AvailableCall {
    Addressor {
        output: mir::Value,
        root: Root,
    },
    Value {
        output: mir::Value,
        dependencies: Box<[Root]>,
        output_root: Root,
    },
}

impl AvailableCall {
    fn output(&self) -> &mir::Value {
        match self {
            AvailableCall::Addressor { output, .. } | AvailableCall::Value { output, .. } => output,
        }
    }
}

type AvailableCalls = FxHashMap<CallExpression, AvailableCall>;

/// Where a place points, and whether writing through it may replace storage containing addressor
/// metadata. A place loaded from an addressor's out-slot is a leaf projection: writing its pointee
/// changes the selected value, not the allocation which contains it.
#[derive(Clone, Copy, PartialEq, Eq)]
struct PlaceOrigin {
    root: Root,
    structural: bool,
}

#[derive(Default)]
struct PlaceOrigins {
    registers: FxHashMap<ValueId, PlaceOrigin>,
    /// Out-slots an addressor call filled, before the following `load` materializes the place.
    returned: FxHashMap<ValueId, PlaceOrigin>,
}

impl PlaceOrigins {
    fn of(func: &Function, summary_of: &dyn Fn(FunctionId) -> AddressorSummary) -> PlaceOrigins {
        let mut origins = PlaceOrigins::default();
        // Canonical block order normally defines every operand before it is seen. Iterating to a
        // fixpoint also covers a place flowing through an unusual loop-shaped body without making
        // that ordering an analysis contract.
        let mut changed = true;
        while changed {
            changed = false;
            for block_id in func.blocks() {
                let block = func.block(block_id);
                for operation in block
                    .operations()
                    .iter()
                    .chain(match &block.terminator().kind {
                        TerminatorKind::Invoke { operation, .. } => Some(operation),
                        _ => None,
                    })
                {
                    changed |= origins.learn(operation, summary_of);
                }
            }
        }
        origins
    }

    fn origin_of(&self, value: &mir::Value) -> Option<PlaceOrigin> {
        match value {
            mir::Value::Parameter(id) => Some(PlaceOrigin {
                root: Root::Parameter(*id),
                structural: true,
            }),
            mir::Value::Register(id) => self.registers.get(id).copied(),
            _ => None,
        }
    }

    fn learn(
        &mut self,
        operation: &Operation,
        summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
    ) -> bool {
        let Some(result) = operation.result_id() else {
            return self.learn_call_result(operation, summary_of);
        };
        let origin = match &operation.kind {
            OperationKind::Alloca { .. }
            | OperationKind::AllocaPlace { .. }
            | OperationKind::DictEntry { .. }
            | OperationKind::SubscriptMember { .. } => Some(PlaceOrigin {
                root: Root::Alloca(result),
                structural: true,
            }),
            OperationKind::Subfield { .. } => self.origin_of(&operation.operands[0]),
            OperationKind::Load => match &operation.operands[0] {
                mir::Value::Register(slot) => {
                    self.returned.get(slot).copied().map(|origin| PlaceOrigin {
                        root: origin.root,
                        structural: false,
                    })
                }
                _ => None,
            },
            _ => None,
        };
        let mut changed = origin
            .is_some_and(|origin| self.registers.insert(result, origin).as_ref() != Some(&origin));
        changed |= self.learn_call_result(operation, summary_of);
        changed
    }

    fn learn_call_result(
        &mut self,
        operation: &Operation,
        summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
    ) -> bool {
        let OperationKind::Call { ty, .. } = &operation.kind else {
            return false;
        };
        if ty.result_convention != CallResultConvention::ADDRESSOR_PLACE {
            return false;
        }
        let Some(call) = call_operands(&operation.operands, ty) else {
            return false;
        };
        let mir::Value::Function(callee) = call.callee else {
            return false;
        };
        let ResultProvenance::Argument(index) = summary_of(*callee).provenance else {
            return false;
        };
        let Some((argument, _)) = call.arguments.get(index as usize) else {
            return false;
        };
        let Some(origin) = self.origin_of(argument) else {
            return false;
        };
        let mir::Value::Register(output) = call.result else {
            return false;
        };
        self.returned.insert(*output, origin).as_ref() != Some(&origin)
    }
}

#[derive(Clone)]
enum ReplacementSite {
    Operation { block: BlockId, index: usize },
    Invoke { block: BlockId, normal: BlockId },
}

#[derive(Clone)]
struct CallReplacement {
    site: ReplacementSite,
    source: mir::Value,
    destination: mir::Value,
    span: crate::Location,
}

/// Eliminates repeated, statically known addressor and trivially-copyable value calls before the
/// inliner expands them.
///
/// The analysis is an available-expression intersection over CFG edges. A fallible call becomes
/// available only on its normal edge: replacing a later identical invoke is then both an address
/// reuse and proof that its failure edge is unreachable, because the first call already succeeded.
pub(crate) fn eliminate_common_calls(
    func: &Function,
    env: ModuleEnv<'_>,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
) -> Option<Function> {
    let origins = PlaceOrigins::of(func, summary_of);
    let entry_states = available_call_states(func, env, &origins, summary_of);
    let mut replacements = Vec::new();

    for block_id in func.blocks() {
        let Some(mut state) = entry_states.get(&block_id).cloned() else {
            continue;
        };
        let block = func.block(block_id);
        for (index, operation) in block.operations().iter().enumerate() {
            if let Some((source, destination)) =
                transfer(operation, env, &origins, summary_of, &mut state)
            {
                replacements.push(CallReplacement {
                    site: ReplacementSite::Operation {
                        block: block_id,
                        index,
                    },
                    source,
                    destination,
                    span: operation.span,
                });
            }
        }
        if let TerminatorKind::Invoke {
            operation, normal, ..
        } = &block.terminator().kind
            && let Some((source, destination)) =
                transfer(operation, env, &origins, summary_of, &mut state)
        {
            replacements.push(CallReplacement {
                site: ReplacementSite::Invoke {
                    block: block_id,
                    normal: *normal,
                },
                source,
                destination,
                span: operation.span,
            });
        }
    }
    if replacements.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for replacement in replacements {
        let copy = Operation::memcpy(
            replacement.span,
            replacement.source,
            replacement.destination,
        );
        match replacement.site {
            ReplacementSite::Operation { block, index } => {
                edit.block_mut(block).replace_operation(index, copy);
            }
            ReplacementSite::Invoke { block, normal } => {
                let block = edit.block_mut(block);
                block.operations.push(copy);
                block.terminator = Terminator::goto(replacement.span, normal);
            }
        }
    }
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some(edit.finish_unverified())
}

fn available_call_states(
    func: &Function,
    env: ModuleEnv<'_>,
    origins: &PlaceOrigins,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
) -> FxHashMap<BlockId, AvailableCalls> {
    let mut entries = FxHashMap::default();
    entries.insert(func.entry(), AvailableCalls::default());
    let mut changed = true;
    while changed {
        changed = false;
        for block_id in func.blocks() {
            let Some(mut state) = entries.get(&block_id).cloned() else {
                continue;
            };
            let block = func.block(block_id);
            for operation in block.operations() {
                transfer(operation, env, origins, summary_of, &mut state);
            }
            match &block.terminator().kind {
                TerminatorKind::Invoke {
                    operation,
                    normal,
                    error,
                } => {
                    transfer(operation, env, origins, summary_of, &mut state);
                    changed |= join_available(&mut entries, *normal, &state);
                    // No call result is available on failure. Empty is deliberately more
                    // conservative than preserving expressions from before the invoke.
                    changed |= join_available(&mut entries, *error, &AvailableCalls::default());
                }
                _ => {
                    for successor in successors(block.terminator()) {
                        changed |= join_available(&mut entries, successor, &state);
                    }
                }
            }
        }
    }
    entries
}

fn join_available(
    entries: &mut FxHashMap<BlockId, AvailableCalls>,
    block: BlockId,
    incoming: &AvailableCalls,
) -> bool {
    match entries.get_mut(&block) {
        None => {
            entries.insert(block, incoming.clone());
            true
        }
        Some(existing) => {
            let previous_len = existing.len();
            existing.retain(|expression, available| incoming.get(expression) == Some(available));
            existing.len() != previous_len
        }
    }
}

/// Applies one operation and returns the result copy which replaces it when it is redundant.
fn transfer(
    operation: &Operation,
    env: ModuleEnv<'_>,
    origins: &PlaceOrigins,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
    state: &mut AvailableCalls,
) -> Option<(mir::Value, mir::Value)> {
    if let Some((expression, available)) = call_expression(operation, origins, summary_of, env) {
        // Every call writes its out-slot. This can invalidate another value expression whose input
        // or cached result occupies the same root, and overwrites an addressor pointer cached in
        // exactly that slot.
        forget_write(state, origins, available.output());
        state.retain(|_, cached| cached.output() != available.output());
        if let Some(previous) = state.get(&expression) {
            return Some((previous.output().clone(), available.output().clone()));
        }
        state.insert(expression, available);
        return None;
    }

    match &operation.kind {
        OperationKind::Call { ty, .. } => {
            let Some(call) = call_operands(&operation.operands, ty) else {
                state.clear();
                return None;
            };
            forget_write(state, origins, call.result);
            state.retain(|_, cached| cached.output() != call.result);
            // An address computation declared repeatable is independent of environmental state,
            // so effects alone do not kill it. Mutable access to its storage root does.
            for (argument, convention) in call.arguments {
                if matches!(convention, ArgConvention::MutableRef) {
                    match origins.origin_of(argument) {
                        Some(origin) => forget_root(state, origin.root),
                        None => state.clear(),
                    }
                }
            }
        }
        OperationKind::Store => forget_write(state, origins, &operation.operands[1]),
        OperationKind::Clear => forget_write(state, origins, &operation.operands[0]),
        OperationKind::Memcpy | OperationKind::Move | OperationKind::Clone { .. } => {
            if matches!(operation.kind, OperationKind::Move) {
                forget_write(state, origins, &operation.operands[0]);
            }
            forget_write(state, origins, &operation.operands[1]);
        }
        OperationKind::Drop { .. }
        | OperationKind::DropClosureEnv
        | OperationKind::CloneClosureEnv { .. } => {
            forget_write(state, origins, &operation.operands[0]);
        }
        // Restoring can pop the out-slot holding the cached pointer. Scoped projections can run
        // arbitrary setup/cleanup code and are outside the AddressorPlace contract.
        OperationKind::StackRestore | OperationKind::Project { .. } | OperationKind::EndProject => {
            state.clear()
        }
        _ => {}
    }
    None
}

fn call_expression(
    operation: &Operation,
    origins: &PlaceOrigins,
    summary_of: &dyn Fn(FunctionId) -> AddressorSummary,
    env: ModuleEnv<'_>,
) -> Option<(CallExpression, AvailableCall)> {
    let OperationKind::Call { ty, metadata } = &operation.kind else {
        return None;
    };
    if metadata
        .as_deref()
        .is_some_and(|metadata| !metadata.owned_arguments.is_empty())
    {
        return None;
    }
    if !effects_allow_const_eval(ty.effects()) {
        return None;
    }
    let call = call_operands(&operation.operands, ty)?;
    let mir::Value::Function(callee) = call.callee else {
        return None;
    };
    let available = match ty.result_convention {
        CallResultConvention::ADDRESSOR_PLACE => {
            let summary = summary_of(*callee);
            if !summary.repeatable {
                return None;
            }
            let ResultProvenance::Argument(index) = summary.provenance else {
                return None;
            };
            let (base, _) = call.arguments.get(index as usize)?;
            AvailableCall::Addressor {
                output: call.result.clone(),
                root: origins.origin_of(base)?.root,
            }
        }
        CallResultConvention::Value => {
            if !concrete_type_is_trivial_copy(ty.ret(), &env)
                || call
                    .arguments
                    .iter()
                    .any(|(_, convention)| *convention != ArgConvention::Let)
            {
                return None;
            }
            let dependencies: Box<[Root]> = call
                .arguments
                .iter()
                .map(|(argument, _)| origins.origin_of(argument).map(|origin| origin.root))
                .collect::<Option<Vec<_>>>()?
                .into_boxed_slice();
            let output_root = origins.origin_of(call.result)?.root;
            // The call reads its arguments before writing its result. Keeping those roots distinct
            // lets transfer invalidate the destination before looking up the old expression and is
            // also the ordinary MIR lowering shape.
            if dependencies.contains(&output_root) {
                return None;
            }
            AvailableCall::Value {
                output: call.result.clone(),
                dependencies,
                output_root,
            }
        }
        _ => return None,
    };
    Some((
        CallExpression {
            ty: ty.as_ref().clone(),
            instantiation: metadata
                .as_deref()
                .and_then(|metadata| metadata.instantiation.clone()),
            operands: operation.operands[..operation.operands.len() - 1]
                .to_vec()
                .into_boxed_slice(),
        },
        available,
    ))
}

fn forget_write(state: &mut AvailableCalls, origins: &PlaceOrigins, destination: &mir::Value) {
    let Some(origin) = origins.origin_of(destination) else {
        // An unknown destination may alias a value input. Repeatable addressors remain independent
        // of leaf writes, and structural operations with unknown provenance clear the whole state
        // separately.
        state.retain(|_, available| matches!(available, AvailableCall::Addressor { .. }));
        return;
    };
    state.retain(|_, available| match available {
        AvailableCall::Addressor { root, .. } => !origin.structural || *root != origin.root,
        AvailableCall::Value {
            dependencies,
            output_root,
            ..
        } => *output_root != origin.root && !dependencies.contains(&origin.root),
    });
}

fn forget_root(state: &mut AvailableCalls, root: Root) {
    state.retain(|_, available| match available {
        AvailableCall::Addressor {
            root: available_root,
            ..
        } => *available_root != root,
        AvailableCall::Value {
            dependencies,
            output_root,
            ..
        } => *output_root != root && !dependencies.contains(&root),
    });
}

/// What a place-producing operation computes, beside its operands.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Computation {
    /// A field address *derived* from its operand: the base's root and path with an index appended.
    Subfield { ty: Type },
    /// A function place *materialized* from evidence into a freshly allocated cell.
    DictEntry {
        entry_index: TraitDictionaryEntryIndex,
        ty: Type,
    },
}

impl Computation {
    fn of(kind: &OperationKind) -> Option<Self> {
        match kind {
            OperationKind::Subfield { ty } => Some(Self::Subfield { ty: *ty }),
            OperationKind::DictEntry { entry_index, ty } => Some(Self::DictEntry {
                entry_index: *entry_index,
                ty: *ty,
            }),
            _ => None,
        }
    }

    /// Whether the result lives in the current stack region rather than deriving from an operand's
    /// storage, and so dies when that region is popped.
    fn is_materialized(&self) -> bool {
        match self {
            Self::Subfield { .. } => false,
            Self::DictEntry { .. } => true,
        }
    }
}

/// The identity of a place-producing operation: what it computes, and its canonical operands. Two
/// operations sharing one yield the same place.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Expression {
    computation: Computation,
    operands: Box<[mir::Value]>,
}

/// The operation an expression was first computed by, and where.
#[derive(Clone, Copy)]
struct Available {
    result: ValueId,
    block: BlockId,
}

/// Replaces repeated address computations by their dominating first occurrence, returning a
/// rewritten function if anything was merged.
pub(crate) fn eliminate_common_subexpressions(func: &Function) -> Option<Function> {
    let successors: Vec<Vec<usize>> = func
        .blocks()
        .map(|block| {
            successors(func.block(block).terminator())
                .into_iter()
                .map(|target| target.as_index())
                .collect()
        })
        .collect();
    let dominance = Dominance::of(&successors, func.entry().as_index());

    let mut numbering = Numbering {
        func,
        dominance: &dominance,
        available: FxHashMap::default(),
        merged: FxHashMap::default(),
        removed: FxHashMap::default(),
    };
    numbering.walk(func.entry());
    let Numbering {
        merged, removed, ..
    } = numbering;
    if merged.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for (block, indices) in &removed {
        let mut index = 0;
        edit.block_mut(*block).operations.retain(|_| {
            let keep = !indices.contains(&index);
            index += 1;
            keep
        });
    }
    edit.visit_operands_mut(|operand| {
        if let mir::Value::Register(id) = operand
            && let Some(representative) = merged.get(id)
        {
            *id = *representative;
        }
    });
    // A merged operation is usually the last reference to the field index it named.
    edit.prune_constants();
    Some(edit.finish_unverified())
}

struct Numbering<'a> {
    func: &'a Function,
    dominance: &'a Dominance,
    /// The expressions computed by a dominator of the block being walked.
    available: FxHashMap<Expression, Available>,
    /// The result each merged operation is replaced by. A representative is never itself merged —
    /// an expression is looked up under already-canonical operands — so this needs no chasing.
    merged: FxHashMap<ValueId, ValueId>,
    removed: FxHashMap<BlockId, FxHashSet<usize>>,
}

impl Numbering<'_> {
    /// Numbers `block`, then the subtree it dominates, undoing its own entries on the way back up.
    ///
    /// Iterative rather than recursive, for the same reason the dominator computation is: a body's
    /// block count must not be bounded by the host thread's stack.
    fn walk(&mut self, entry: BlockId) {
        // What each entry displaced, so leaving a subtree restores exactly what entering it found.
        let mut undo: Vec<(Expression, Option<Available>)> = Vec::new();
        let mut stack = vec![(entry, Enter::Down)];
        while let Some((block, direction)) = stack.pop() {
            match direction {
                Enter::Up { undo_depth } => {
                    while undo.len() > undo_depth {
                        let (expression, previous) =
                            undo.pop().expect("the log is longer than the depth");
                        match previous {
                            Some(available) => self.available.insert(expression, available),
                            None => self.available.remove(&expression),
                        };
                    }
                }
                Enter::Down => {
                    let depth = undo.len();
                    self.number_block(block, &mut undo);
                    stack.push((block, Enter::Up { undo_depth: depth }));
                    for &child in self.dominance.children(block.as_index()) {
                        stack.push((BlockId::from_index(child), Enter::Down));
                    }
                }
            }
        }
    }

    fn number_block(&mut self, block: BlockId, undo: &mut Vec<(Expression, Option<Available>)>) {
        for (index, operation) in self.func.block(block).operations().iter().enumerate() {
            // Popping a stack region frees every cell allocated inside it, so a materialized place
            // does not survive one. A scoped accessor is opaque enough to count as one too.
            if matches!(
                operation.kind,
                OperationKind::StackRestore
                    | OperationKind::Project { .. }
                    | OperationKind::EndProject
            ) {
                self.forget_materialized(undo);
                continue;
            }
            let Some(computation) = Computation::of(&operation.kind) else {
                continue;
            };
            let result = operation
                .result_id()
                .expect("a place-producing operation defines a result");
            let operands = operation
                .operands
                .iter()
                .map(|operand| match operand {
                    mir::Value::Register(id) => match self.merged.get(id) {
                        Some(representative) => mir::Value::Register(*representative),
                        None => operand.clone(),
                    },
                    _ => operand.clone(),
                })
                .collect();
            let expression = Expression {
                computation,
                operands,
            };
            match self.available.get(&expression) {
                // Dominance makes the merge *correct*; block order is what the verifier walks in
                // when it resolves an operand's role, so a representative must also precede its new
                // use there. Canonical MIR is ordered so that a dominator comes first, which makes
                // this a guard rather than a restriction.
                Some(&available) if available.block.as_index() <= block.as_index() => {
                    self.merged.insert(result, available.result);
                    self.removed.entry(block).or_default().insert(index);
                }
                _ => {
                    let key = expression.clone();
                    let previous = self
                        .available
                        .insert(expression, Available { result, block });
                    undo.push((key, previous));
                }
            }
        }
    }

    /// Drops every materialized place from the scope, through the undo log so that a sibling
    /// subtree — which did not pop the region — still sees them.
    fn forget_materialized(&mut self, undo: &mut Vec<(Expression, Option<Available>)>) {
        self.available.retain(|expression, available| {
            if expression.computation.is_materialized() {
                undo.push((expression.clone(), Some(*available)));
                false
            } else {
                true
            }
        });
    }
}

#[derive(Clone, Copy)]
enum Enter {
    Down,
    Up { undo_depth: usize },
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.emit_mir("cse", src)
    }

    /// The body of `name`, up to the next function.
    fn body_of(src: &str, name: &str) -> String {
        let module = optimized(&format!("struct Pair {{ a: int, b: int }}\n{src}"));
        module
            .split(&format!("fn {name}("))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
            .split("\nfn ")
            .next()
            .expect("a split always yields a first piece")
            .to_string()
    }

    fn subfields(body: &str) -> usize {
        body.matches("= subfield").count()
    }

    fn calls(body: &str, callee_fragment: &str) -> usize {
        body.lines()
            .filter(|line| line.contains("call ") && line.contains(callee_fragment))
            .count()
    }

    #[test]
    fn repeated_integer_value_call_is_computed_once() {
        let body = body_of(
            "fn repeated_int(x: int, y: int) -> int { (x - y) * (x - y) }",
            "repeated_int",
        );
        assert_eq!(
            calls(&body, "Num<std::int>::sub"),
            1,
            "the repeated subtraction should be copied from its first result:\n{body}"
        );
    }

    #[test]
    fn repeated_float_value_call_is_computed_once() {
        let body = body_of(
            "fn repeated_float(x: float, y: float) -> float { (x - y) * (x - y) }",
            "repeated_float",
        );
        assert_eq!(
            calls(&body, "Num<std::float>::sub"),
            1,
            "the repeated subtraction should be copied from its first result:\n{body}"
        );
    }

    #[test]
    fn repeated_boolean_value_call_is_computed_once() {
        let body = body_of(
            "fn repeated_bool(x: bool, y: bool) -> bool {\n\
                 bit_or(bit_and(x, y), bit_and(x, y))\n\
             }",
            "repeated_bool",
        );
        assert_eq!(
            calls(&body, "Bits<std::bool>::bit_and"),
            1,
            "the repeated boolean computation should be copied from its first result:\n{body}"
        );
    }

    #[test]
    fn changing_a_value_argument_invalidates_the_cached_call() {
        let body = body_of(
            "fn changed(mut x: int, y: int) -> int {\n\
                 let before = x - y;\n\
                 x = x + 1;\n\
                 before * (x - y)\n\
             }",
            "changed",
        );
        assert_eq!(
            calls(&body, "Num<std::int>::sub"),
            2,
            "the subtraction after changing x must be recomputed:\n{body}"
        );
    }

    #[test]
    fn repeated_subscripts_are_merged_before_inlining_swap() {
        let body = body_of(
            "fn swap(a, i, j) { let temp = a[i]; a[i] = a[j]; a[j] = temp }\n\
             fn use_it(mut a: [int]) -> [int] { swap(a, 0, 1); a }",
            "swap#spec:[int]",
        );
        assert_eq!(
            body.matches("call std::array_resolve_index").count(),
            2,
            "one bounds/index computation per distinct subscript:\n{body}"
        );
        assert_eq!(
            body.matches("call std::buffer_slot::ref_mut").count(),
            2,
            "one address computation per distinct subscript:\n{body}"
        );
    }

    #[test]
    fn a_mutating_call_invalidates_an_available_subscript() {
        let body = body_of(
            "fn around_append(a: &mut [int]) -> int {\n\
                 let before = a[0];\n\
                 array_append(a, 1);\n\
                 before + a[0]\n\
             }",
            "around_append",
        );
        assert_eq!(
            body.matches("call std::array_resolve_index").count(),
            2,
            "append may reallocate the array, so the second address must be recomputed:\n{body}"
        );
    }

    /// A generic body reads the same dictionary entry once per use of the trait method; merging
    /// them is what makes this worth running before the inliner prices the body.
    #[test]
    fn a_repeated_dictionary_entry_is_read_once() {
        let body = body_of(
            "fn twice_clone(x) { let a = x; let b = x; (a, b) }\n\
             fn use_it(v: int) -> (int, int) { twice_clone(v) }",
            "twice_clone",
        );
        assert_eq!(
            body.matches("= dict_entry").count(),
            1,
            "one entry read, reused by both clones:\n{body}"
        );
    }

    /// The same scoping rule as for field addresses: neither arm dominates the other, so neither
    /// may name the other's cell.
    #[test]
    fn a_dictionary_entry_is_not_shared_between_branch_arms() {
        let body = body_of(
            "fn arms(x, c: bool) { if c { let a = x; a } else { let b = x; b } }\n\
             fn use_it(v: int, c: bool) -> int { arms(v, c) }",
            "arms",
        );
        assert_eq!(
            body.matches("= dict_entry").count(),
            2,
            "each arm reads its own entry:\n{body}"
        );
    }

    #[test]
    fn a_repeated_field_address_is_computed_once() {
        let body = body_of("fn twice(p: Pair) -> int { p.a + p.a }", "twice");
        assert_eq!(subfields(&body), 1, "one address, computed once:\n{body}");
    }

    #[test]
    fn addresses_of_different_fields_stay_distinct() {
        let body = body_of("fn both(p: Pair) -> int { p.a + p.b }", "both");
        assert_eq!(subfields(&body), 2, "two fields are two addresses:\n{body}");
    }

    /// The scope must be undone on the way back up the dominator tree: neither arm dominates the
    /// other, so neither may reuse the other's address. Merging them would not merely be
    /// unprofitable — the verifier rejects a use its definition does not dominate.
    #[test]
    fn a_field_address_is_not_shared_between_branch_arms() {
        let body = body_of(
            "fn arms(p: Pair, c: bool) -> int { if c { p.a } else { p.a } }",
            "arms",
        );
        assert_eq!(
            subfields(&body),
            2,
            "each arm computes its own address:\n{body}"
        );
    }

    /// A dominating definition is reused across blocks, which is the case the whole dominator walk
    /// exists for — a redundancy inside one block would not need it.
    #[test]
    fn a_dominating_field_address_is_reused_in_a_later_block() {
        let body = body_of(
            "fn guarded(p: Pair, c: bool) -> int { let x = p.a; if c { x + p.a } else { x } }",
            "guarded",
        );
        assert_eq!(
            subfields(&body),
            1,
            "the entry's address dominates the arm's:\n{body}"
        );
    }
}
