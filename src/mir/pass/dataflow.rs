// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! What the folding pass knows at each point of a function: which storage slots hold which
//! compile-time constants.
//!
//! Analysis only — nothing here rewrites MIR. It answers one question for the folding pass: at this
//! call site, is every argument place fully known?
//!
//! The model has two layers, because MIR is storage-explicit:
//!
//! - **Places.** A [`Root`] is an `alloca` result or a parameter; a [`PlaceKey`] is a root plus a
//!   field path. Facts are attached to place keys, so `store 5 to %r1.0` is known independently of
//!   `%r1.1`.
//! - **Registers.** Immutable register-to-place bindings (`alloca`, `subfield`) live once in the
//!   [`Analysis`]; only flow-dependent materialized values (`load`) live in each [`State`].
//!
//! **Escape is computed once, flow-insensitively, before the dataflow runs.** A root whose place
//! reaches any context this analysis does not model — a call argument, a `store` of the pointer
//! itself, an operation with no transfer function — is marked escaped, and escaped roots are never
//! tracked anywhere in the function. That is coarser than a flow-sensitive escape analysis and
//! deliberately so: the cost of being wrong here is unsound folding, while the cost of being coarse
//! is an unfolded call. The set of *modelled* operations is the whitelist; everything else escapes
//! its place operands.
//!
//! The folding pass that consumes this is the next deliverable, so the items here are exercised
//! only by the tests below.
#![allow(dead_code)]

use std::{cmp::Reverse, collections::BinaryHeap};

use rustc_hash::{FxHashMap, FxHashSet};
use ustr::Ustr;

use crate::{
    hir::{
        function::{ArgConvention, arg_conventions_for_args},
        value::LiteralValue,
    },
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        terminator::TerminatorKind,
        value::{ParameterId, ValueId},
    },
    module::{
        FunctionId, ModuleEnv, ProjectionIndex, TraitDictionaryEntry, TraitDictionaryId, id::Id,
    },
    types::r#trait::TraitDictionaryEntryIndex,
    types::r#type::{CallImplType, Type},
};

/// A root of addressable storage the analysis can track.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Root {
    /// Storage allocated by an `alloca` in this function.
    Alloca(ValueId),
    /// Storage owned by the caller and named by a parameter.
    Parameter(ParameterId),
    /// The cell a `dict_entry` materializes its entry into. Not storage the function allocated, but
    /// a place all the same, and the one devirtualization reads: an entry of a constant dictionary
    /// is a known function.
    DictEntry(ValueId),
}

/// A storage slot: a root plus the field path reaching it.
///
/// A path entry is the position of a field in the aggregate above it, which is what a `subfield`
/// selects. It is a [`ProjectionIndex`] rather than a bare integer because that is what it is:
/// lowering builds the `subfield`'s index operand from one, and reading it back as an untyped
/// number loses that.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct PlaceKey {
    pub root: Root,
    pub path: Vec<ProjectionIndex>,
}

impl PlaceKey {
    pub(crate) fn root(root: Root) -> Self {
        Self {
            root,
            path: Vec::new(),
        }
    }

    pub(crate) fn field(&self, index: ProjectionIndex) -> Self {
        let mut path = self.path.clone();
        path.push(index);
        Self {
            root: self.root,
            path,
        }
    }

    /// Whether `self` is `other` or lies inside it.
    pub(crate) fn is_within(&self, other: &PlaceKey) -> bool {
        self.root == other.root
            && self.path.len() >= other.path.len()
            && self.path[..other.path.len()] == other.path[..]
    }
}

/// Immutable register-to-storage structure.
///
/// A dynamic `subfield` still has a known root, which escape analysis and diagnostics need, but no
/// exact [`PlaceKey`] the folding analysis may safely read.
#[derive(Clone, PartialEq, Eq, Debug)]
enum PlaceBinding {
    Exact(PlaceKey),
    Root(Root),
}

#[derive(Default)]
pub(crate) struct PlaceBindings {
    registers: FxHashMap<ValueId, PlaceBinding>,
}

impl PlaceBindings {
    fn place_of(&self, operand: &mir::Value) -> Option<PlaceKey> {
        match operand {
            mir::Value::Register(id) => match self.registers.get(id)? {
                PlaceBinding::Exact(key) => Some(key.clone()),
                PlaceBinding::Root(_) => None,
            },
            mir::Value::Parameter(id) => Some(PlaceKey::root(Root::Parameter(*id))),
            _ => None,
        }
    }

    fn root_of(&self, operand: &mir::Value) -> Option<Root> {
        match operand {
            mir::Value::Register(id) => self.root_of_register(*id),
            mir::Value::Parameter(id) => Some(Root::Parameter(*id)),
            _ => None,
        }
    }

    pub(crate) fn root_of_register(&self, id: ValueId) -> Option<Root> {
        match self.registers.get(&id)? {
            PlaceBinding::Exact(key) => Some(key.root),
            PlaceBinding::Root(root) => Some(*root),
        }
    }
}

/// A compile-time constant the analysis can carry.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum Const {
    /// A trivially-copyable value, in the form a MIR constant pool holds.
    Literal(LiteralValue),
    /// A known function, as a `dict_entry` on a constant dictionary resolves to.
    Function(FunctionId),
    /// A known trait dictionary.
    Dictionary(TraitDictionaryId),
    /// A symbolic discriminant, kept independent of compilation-session numeric tag ids.
    VariantTag(Ustr),
    /// A fresh array construction whose statically `TrivialCopy` elements are all known.
    Array {
        element_ty: Type,
        elements: Box<[LiteralValue]>,
    },
}

/// What is known about one storage slot, or about a materialized value.
///
/// The lattice is `Uninit` and `Known(_)` below `Unknown`: joining two disagreeing facts yields
/// `Unknown`, which is the safe answer everywhere.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub(crate) enum Fact {
    /// Nothing is known; the slot may hold anything.
    #[default]
    Unknown,
    /// The slot holds no value (never initialized, cleared, or moved out).
    Uninit,
    /// The slot holds this constant.
    Known(Const),
}

impl Fact {
    fn join(&self, other: &Fact) -> Fact {
        if self == other {
            self.clone()
        } else {
            Fact::Unknown
        }
    }

    pub(crate) fn known(&self) -> Option<&Const> {
        match self {
            Fact::Known(value) => Some(value),
            _ => None,
        }
    }
}

/// The analysis state at one program point.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub(crate) struct State {
    places: FxHashMap<PlaceKey, Fact>,
    /// Flow-dependent facts for registers that hold materialized values. Registers that name
    /// places are structural and live once in [`Analysis::register_places`].
    registers: FxHashMap<ValueId, Fact>,
}

impl State {
    /// The fact for a slot. Absent means `Unknown`: an untracked slot is one nothing is known about.
    pub(crate) fn place(&self, key: &PlaceKey) -> Fact {
        self.places.get(key).cloned().unwrap_or_default()
    }

    pub(crate) fn register(&self, id: ValueId) -> Option<&Fact> {
        self.registers.get(&id)
    }

    /// Records a fact the folding pass established by rewriting an operation.
    pub(crate) fn set_place_known(&mut self, key: PlaceKey, fact: Fact) {
        self.set_place(key, fact);
    }

    fn set_place(&mut self, key: PlaceKey, fact: Fact) {
        // Writing a slot says nothing about the slots inside it, which the write replaced.
        self.forget_within(&key);
        self.places.insert(key, fact);
    }

    fn forget_within(&mut self, key: &PlaceKey) {
        self.places.retain(|tracked, _| !tracked.is_within(key));
    }

    fn forget_root(&mut self, root: Root) {
        self.places.retain(|tracked, _| tracked.root != root);
    }

    fn join(&self, other: &State) -> State {
        let mut places = FxHashMap::default();
        for (key, fact) in &self.places {
            // A slot tracked on one edge and absent on the other is Unknown on that edge, so it
            // joins to Unknown and is simply dropped.
            if let Some(theirs) = other.places.get(key) {
                let joined = fact.join(theirs);
                if joined != Fact::Unknown {
                    places.insert(key.clone(), joined);
                }
            }
        }
        let mut registers = FxHashMap::default();
        for (id, fact) in &self.registers {
            if let Some(theirs) = other.registers.get(id) {
                registers.insert(*id, fact.join(theirs));
            }
        }
        State { places, registers }
    }
}

/// The result of analysing a function: the state on entry to each block.
pub(crate) struct Analysis {
    entry_states: Vec<Option<State>>,
    escaped: FxHashSet<Root>,
    /// Immutable structural bindings, discovered once before the fixpoint rather than copied into
    /// every flow state.
    register_places: PlaceBindings,
}

impl Analysis {
    /// Whether `root` is tracked at all. An escaped root is `Unknown` everywhere.
    pub(crate) fn is_escaped(&self, root: Root) -> bool {
        self.escaped.contains(&root)
    }

    /// The root a register names, if this function's structure gives it one.
    pub(crate) fn root_of_register(&self, id: ValueId) -> Option<Root> {
        self.register_places.root_of_register(id)
    }

    /// The slot an operand names, independent of flow state.
    pub(crate) fn place_of(&self, operand: &mir::Value) -> Option<PlaceKey> {
        self.register_places.place_of(operand)
    }

    /// The slot an operand names when its contents remain within the analysis model.
    ///
    /// Structural bindings deliberately include escaped places so diagnostics can explain why a
    /// fact is unavailable. Consumers must use this narrower lookup before reading or injecting a
    /// fact: an escaped place can be mutated by an operation the transfer function does not model.
    pub(crate) fn tracked_place_of(&self, operand: &mir::Value) -> Option<PlaceKey> {
        let key = self.place_of(operand)?;
        (!self.is_escaped(key.root)).then_some(key)
    }
    /// The state on entry to `block`.
    pub(crate) fn entry_state(&self, block: BlockId) -> State {
        self.entry_states
            .get(block.as_index())
            .and_then(Option::as_ref)
            .cloned()
            .unwrap_or_default()
    }

    /// Applies one operation's transfer function to `state`.
    ///
    /// The per-block entry states are the fixpoint; everything inside a block is recomputed by
    /// stepping from its entry state. The folding pass walks blocks this way rather than through a
    /// callback, because it also needs to *inject* facts — a call it decides to fold makes its
    /// result place known for the rest of the walk.
    pub(crate) fn step(
        &self,
        func: &Function,
        env: ModuleEnv<'_>,
        operation: &Operation,
        state: &mut State,
    ) {
        transfer(
            operation,
            func,
            env,
            &self.escaped,
            &self.register_places,
            state,
        );
    }
}

/// Runs the analysis to fixpoint over `func`.
pub(crate) fn analyze(func: &Function, env: ModuleEnv<'_>) -> Analysis {
    let (escaped, register_places) = escaping_roots(func, &|_| false);

    let block_count = func.blocks().count();
    // The consumer replays operations from each settled entry. A one-block function's only entry
    // is always the empty function-entry state, even when its terminator loops back to itself: the
    // external entry contributes Unknown and therefore absorbs every back-edge fact at the join.
    // There is no successor state for the solver to discover, so avoid duplicating that replay.
    if block_count == 1 {
        return Analysis {
            entry_states: vec![Some(State::default())],
            escaped,
            register_places,
        };
    }
    let successor_lists: Vec<Vec<usize>> = func
        .blocks()
        .map(|block| {
            func.block(block)
                .terminator()
                .successors()
                .map(|successor| successor.as_index())
                .collect()
        })
        .collect();

    // Forward dataflow converges fastest when definitions precede their uses and loop back edges
    // come last. Block ids are only construction order after edits, so derive the priority from the
    // actual CFG rather than relying on their current numbering.
    let entry = func.entry().as_index();
    let mut reverse_postorder = vec![usize::MAX; block_count];
    for (priority, block) in crate::graph::reverse_postorder(&successor_lists, entry)
        .into_iter()
        .enumerate()
    {
        reverse_postorder[block] = priority;
    }

    let mut entry_states = vec![None; block_count];
    entry_states[entry] = Some(State::default());
    let mut queued = vec![false; block_count];
    queued[entry] = true;
    let mut worklist = BinaryHeap::from([Reverse((reverse_postorder[entry], entry))]);

    // Only a changed entry can change a block's exit. Priority keeps forward edges ahead of loop
    // back edges; `queued` coalesces several changed predecessors into one transfer.
    while let Some(Reverse((_, block_index))) = worklist.pop() {
        queued[block_index] = false;
        let block_id = BlockId::from_index(block_index);
        let mut state = entry_states[block_index]
            .clone()
            .expect("only a reachable block is queued");
        let block = func.block(block_id);
        for operation in block.operations() {
            transfer(operation, func, env, &escaped, &register_places, &mut state);
        }
        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
            transfer(operation, func, env, &escaped, &register_places, &mut state);
        }
        for successor in block.terminator().successors() {
            let successor = successor.as_index();
            let updated = match &entry_states[successor] {
                Some(existing) => existing.join(&state),
                None => state.clone(),
            };
            if entry_states[successor].as_ref() == Some(&updated) {
                continue;
            }
            entry_states[successor] = Some(updated);
            if !queued[successor] {
                queued[successor] = true;
                worklist.push(Reverse((reverse_postorder[successor], successor)));
            }
        }
    }

    Analysis {
        entry_states,
        escaped,
        register_places,
    }
}

/// The transfer function for one operation.
///
/// Only the operations listed here are modelled; anything else has already caused its place
/// operands to escape (see [`escaping_roots`]), so it needs no case.
fn transfer(
    operation: &Operation,
    func: &Function,
    env: ModuleEnv<'_>,
    escaped: &FxHashSet<Root>,
    register_places: &PlaceBindings,
    state: &mut State,
) {
    let place_of = |operand| register_places.place_of(operand);
    let tracked = |key: &PlaceKey| !escaped.contains(&key.root);
    match &operation.kind {
        OperationKind::Alloca { .. } => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let root = Root::Alloca(result);
            if escaped.contains(&root) {
                return;
            }
            let key = PlaceKey::root(root);
            state.forget_root(root);
            state.places.insert(key, Fact::Uninit);
        }
        OperationKind::Store => {
            let Some(key) = place_of(&operation.operands[1]) else {
                return;
            };
            if !tracked(&key) {
                return;
            }
            let fact = value_operand_fact(&operation.operands[0], func, state);
            state.set_place(key, fact);
        }
        OperationKind::BuildArray { element_ty } => {
            let Some((destination, elements)) = operation.operands.split_last() else {
                return;
            };
            let Some(key) = place_of(destination) else {
                return;
            };
            if !tracked(&key) {
                return;
            }
            let elements = elements
                .iter()
                .map(|operand| {
                    let fact = match place_of(operand) {
                        Some(key) if tracked(&key) => state.place(&key),
                        Some(_) => Fact::Unknown,
                        None => value_operand_fact(operand, func, state),
                    };
                    match fact {
                        Fact::Known(Const::Literal(literal)) => Some(literal),
                        _ => None,
                    }
                })
                .collect::<Option<Vec<_>>>();
            let fact = elements.map_or(Fact::Unknown, |elements| {
                Fact::Known(Const::Array {
                    element_ty: *element_ty,
                    elements: elements.into_boxed_slice(),
                })
            });
            state.set_place(key, fact);
        }
        OperationKind::Clear => {
            if let Some(key) = place_of(&operation.operands[0])
                && tracked(&key)
            {
                state.set_place(key, Fact::Uninit);
            }
        }
        OperationKind::Load => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let fact = match place_of(&operation.operands[0]) {
                Some(key) if tracked(&key) => state.place(&key),
                _ => Fact::Unknown,
            };
            state.registers.insert(result, fact);
        }
        OperationKind::Variant { tag, .. } => {
            let Some(result) = operation.result_id() else {
                return;
            };
            state
                .registers
                .insert(result, Fact::Known(Const::VariantTag(*tag)));
        }
        OperationKind::ExtractTag => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let fact = match place_of(&operation.operands[0]) {
                Some(key) if tracked(&key) => match state.place(&key) {
                    Fact::Known(Const::VariantTag(tag)) => Fact::Known(Const::VariantTag(tag)),
                    _ => Fact::Unknown,
                },
                _ => Fact::Unknown,
            };
            state.registers.insert(result, fact);
        }
        // A subfield's immutable register-to-place binding was discovered before the fixpoint.
        OperationKind::Subfield { .. } => {}
        OperationKind::Memcpy | OperationKind::Move => {
            let source = place_of(&operation.operands[0]);
            let destination = place_of(&operation.operands[1]);
            let fact = match &source {
                Some(key) if tracked(key) => state.place(key),
                _ => Fact::Unknown,
            };
            if let Some(key) = destination
                && tracked(&key)
            {
                state.set_place(key, fact);
            }
            // A move leaves its source moved-out; a memcpy preserves it.
            if matches!(operation.kind, OperationKind::Move)
                && let Some(key) = source
                && tracked(&key)
            {
                state.set_place(key, Fact::Uninit);
            }
        }
        OperationKind::CompareEqual => {
            let Some(result) = operation.result_id() else {
                return;
            };
            // Operands are `[scrutinee, pattern]`, the scrutinee read non-consumingly — as a value,
            // or as the pointee of a place.
            let scrutinee = match place_of(&operation.operands[0]) {
                Some(key) if tracked(&key) => state.place(&key),
                Some(_) => Fact::Unknown,
                None => value_operand_fact(&operation.operands[0], func, state),
            };
            let fact = match (scrutinee.known(), &operation.operands[1]) {
                (Some(Const::VariantTag(actual)), mir::Value::Pattern(pattern))
                    if pattern.as_variant_tag().is_some() =>
                {
                    Fact::Known(Const::Literal(LiteralValue::new_native(
                        pattern.as_variant_tag() == Some(actual),
                    )))
                }
                (Some(Const::Literal(literal)), mir::Value::Pattern(pattern)) => {
                    // Compared exactly as the interpreter does, rather than by comparing literal
                    // trees: pattern matching has representation rules of its own (a `StaticStr`
                    // pattern matches a `String` value), and this must not disagree with them.
                    let value = literal.clone().into_value();
                    let equal = pattern.try_matches_runtime_value(&value);
                    value.discard_storage();
                    match equal {
                        Ok(equal) => Fact::Known(Const::Literal(LiteralValue::new_native(equal))),
                        Err(_) => Fact::Unknown,
                    }
                }
                _ => Fact::Unknown,
            };
            state.registers.insert(result, fact);
        }
        OperationKind::DictEntry { entry_index, .. } => {
            let Some(result) = operation.result_id() else {
                return;
            };
            // The entry of a *constant* dictionary is a statically known function — this is what
            // makes devirtualization fall out of inlining, once inlining has bound a callee's
            // dictionary parameter to a constant.
            let fact = match &operation.operands[0] {
                mir::Value::Dictionary(id) => dictionary_entry(*id, *entry_index, env)
                    .map(|function| Fact::Known(Const::Function(function)))
                    .unwrap_or_default(),
                _ => Fact::Unknown,
            };
            let key = PlaceKey::root(Root::DictEntry(result));
            state.forget_root(key.root);
            state.places.insert(key, fact);
        }
        OperationKind::Call { ty, .. } => {
            // The callee writes its result through the trailing out-pointer, so whatever was known
            // about that slot no longer holds. The folding pass is what replaces a call with a
            // store of a known constant; until it does, the result is unknown.
            if let Some(call) = call_operands(&operation.operands, ty)
                && let Some(key) = place_of(call.result)
                && tracked(&key)
            {
                state.set_place(key, Fact::Unknown);
            }
        }
        // A clone writes its destination through the callee, so that slot is unknown afterwards —
        // the same reasoning as a call's result place, which is what a clone was until it became an
        // operation of its own.
        OperationKind::Clone { .. } => {
            if let Some(key) = place_of(&operation.operands[1])
                && tracked(&key)
            {
                state.set_place(key, Fact::Unknown);
            }
        }
        OperationKind::Drop { .. } => {
            if let Some(key) = place_of(&operation.operands[0])
                && tracked(&key)
            {
                state.set_place(key, Fact::Uninit);
            }
        }
        _ => {
            // Not modelled: the escape scan has escaped every place this operation touches, so
            // there is nothing left to invalidate. A result register, if any, is an unknown value.
            if let Some(result) = operation.result_id() {
                state.registers.insert(result, Fact::Unknown);
            }
        }
    }
}

/// Resolves one entry of a dictionary, from module metadata alone — exactly as the interpreter
/// does when it executes a `dict_entry`.
fn dictionary_entry(
    dictionary: TraitDictionaryId,
    entry: TraitDictionaryEntryIndex,
    env: ModuleEnv<'_>,
) -> Option<FunctionId> {
    let module = env.module_by_id(dictionary.module_id)?;
    let TraitDictionaryEntry::Function(function) = module
        .get_impl_data(dictionary.impl_id)?
        .dictionary_value
        .entry(entry);
    Some(FunctionId {
        module: dictionary.module_id,
        function,
    })
}

/// The fact for an operand used as a materialized value.
fn value_operand_fact(operand: &mir::Value, func: &Function, state: &State) -> Fact {
    match operand {
        mir::Value::Register(id) => state.registers.get(id).cloned().unwrap_or_default(),
        // A pool constant is the base case of the whole analysis: `let x = 5` lowers to a store of
        // one, and everything folding knows grows from there.
        mir::Value::Constant(id) => {
            Fact::Known(Const::Literal(func.constant(*id).representation.clone()))
        }
        mir::Value::Function(id) => Fact::Known(Const::Function(*id)),
        mir::Value::Dictionary(id) => Fact::Known(Const::Dictionary(*id)),
        // Compile-time pattern data belongs to `comp_eq`, and a subscript is evidence rather than
        // data; a parameter naming a materialized value cannot occur, parameters being places.
        mir::Value::Subscript(_) | mir::Value::Pattern(_) | mir::Value::Parameter(_) => {
            Fact::Unknown
        }
    }
}

/// The constant field index a `subfield` selects, if it is one.
///
/// Both forms have to be accepted. Lowering emits the index as a **constant-pool reference**
/// (`subfield @c0 from %r0`), while hand-built MIR and patterns carry it inline. Recognizing only
/// the inline form silently disabled every field-sensitive answer this analysis can give: the
/// transfer function fell back to an unknown value for *every* `subfield`, and the escape scan read
/// the same `None` as "dynamic index" and escaped the base root.
pub(crate) fn field_index(operand: &mir::Value, func: &Function) -> Option<ProjectionIndex> {
    let literal = match operand {
        mir::Value::Pattern(literal) => literal,
        mir::Value::Constant(id) => &func.constant(*id).representation,
        _ => return None,
    };
    literal
        .as_primitive_ty::<isize>()
        .and_then(|index| u32::try_from(*index).ok())
        .and_then(|index| ProjectionIndex::try_from(index as usize).ok())
}

/// Roots that reach a context the analysis does not model, and are therefore never tracked.
///
/// Conservative by construction: the modelled operations below are a whitelist, and every other use
/// of a place escapes its root. A root also escapes if it is reached other than through an `alloca`
/// result or a parameter — an operand this scan cannot resolve to a root escapes nothing precisely
/// because nothing was tracked for it in the first place.
///
/// `mutations_modelled` names the operations whose writes through a place the *caller's* transfer
/// function describes, so that the place stays tracked instead of escaping. Answering true is a
/// claim about the callee on two counts — its writes are accounted for, and it captures no pointer
/// it was given — and folding makes it for nothing, because knowing which slots a callee wrote does
/// not make their new contents known. [`relations`](super::relations) makes it for the std
/// functions whose semantics the optimizer resolves, and for `drop`, which ends a value's life
/// without writing another one anywhere the caller cannot see.
pub(crate) fn escaping_roots(
    func: &Function,
    mutations_modelled: &dyn Fn(&Operation) -> bool,
) -> (FxHashSet<Root>, PlaceBindings) {
    // Register-to-place bindings are immutable MIR structure. Discover the complete paths once so
    // neither escape analysis nor the flow solver has to reconstruct and copy them.
    let mut register_places = PlaceBindings::default();
    for block_id in func.blocks() {
        for operation in func.block(block_id).operations() {
            match (&operation.kind, operation.result_id()) {
                (OperationKind::Alloca { .. }, Some(result)) => {
                    register_places.registers.insert(
                        result,
                        PlaceBinding::Exact(PlaceKey::root(Root::Alloca(result))),
                    );
                }
                (OperationKind::DictEntry { .. }, Some(result)) => {
                    register_places.registers.insert(
                        result,
                        PlaceBinding::Exact(PlaceKey::root(Root::DictEntry(result))),
                    );
                }
                (OperationKind::Subfield { .. }, Some(result)) => {
                    if let Some(root) = register_places.root_of(&operation.operands[0]) {
                        let binding = match (
                            register_places.place_of(&operation.operands[0]),
                            field_index(&operation.operands[1], func),
                        ) {
                            (Some(base), Some(index)) => PlaceBinding::Exact(base.field(index)),
                            _ => PlaceBinding::Root(root),
                        };
                        register_places.registers.insert(result, binding);
                    }
                }
                _ => {}
            }
        }
    }

    // A `BuildArray` destination and a slot initialized with a bare function are compiler-known,
    // self-contained values. Their later semantic drop ends the lifetime but does not make earlier
    // contents escape, so keep precisely these roots trackable through that drop. The array plus
    // mapper pair is the resource-valued fold consumer; applying the same relaxation to every
    // dropped root was measured before one existed and added 25.6% analysis work for no folds.
    let mut self_contained_roots = FxHashSet::default();
    for block_id in func.blocks() {
        for operation in func.block(block_id).operations() {
            let destination = match operation.kind {
                OperationKind::BuildArray { .. } => operation.operands.last(),
                OperationKind::Store
                    if matches!(operation.operands[0], mir::Value::Function(_)) =>
                {
                    operation.operands.get(1)
                }
                _ => None,
            };
            if let Some(destination) = destination
                && let Some(root) = register_places.root_of(destination)
            {
                self_contained_roots.insert(root);
            }
        }
    }

    let mut escaped = FxHashSet::default();
    let escape_operand = |operand: &mir::Value, escaped: &mut FxHashSet<Root>| {
        if let Some(root) = register_places.root_of(operand) {
            escaped.insert(root);
        }
    };

    let scan = |operation: &Operation, escaped: &mut FxHashSet<Root>| {
        match &operation.kind {
            // Modelled: these consume places in ways the transfer functions describe exactly.
            OperationKind::Alloca { .. } => {}
            // `comp_eq` borrows its scrutinee for a literal snapshot and never moves it, so the
            // place stays tracked; its second operand is compile-time pattern data.
            OperationKind::Load
            | OperationKind::Clear
            | OperationKind::CompareEqual
            | OperationKind::ExtractTag => {}
            // Optional storage evidence is read without escaping its place.
            OperationKind::Variant { .. } => {}
            // Elements are borrowed and the trailing destination is modelled exactly.
            OperationKind::BuildArray { .. } => {}
            // Its operand is evidence rather than storage, and its result is a place this analysis
            // roots itself.
            OperationKind::DictEntry { .. } => {}
            OperationKind::Subfield { .. } => {
                // A dynamic field index would name a slot the analysis cannot distinguish.
                if field_index(&operation.operands[1], func).is_none() {
                    escape_operand(&operation.operands[0], escaped);
                }
            }
            OperationKind::Store => {
                // The destination is modelled, but storing a *pointer* lets it reach anywhere.
                escape_operand(&operation.operands[0], escaped);
            }
            OperationKind::Memcpy | OperationKind::Move => {
                // Both places are modelled; a dynamic move additionally reads a witness place.
                for operand in operation.operands.iter().skip(2) {
                    escape_operand(operand, escaped);
                }
            }
            OperationKind::Call { ty, .. } => match call_operands(&operation.operands, ty) {
                // A `Let` argument is immutable and non-escaping by the language's own convention,
                // and the callee reads its function value and evidence by reference. What a call
                // does change is its result place, which the transfer function kills. Anything the
                // callee may write through — a `MutableRef` argument — escapes.
                Some(call) => {
                    for (operand, convention) in &call.arguments {
                        if matches!(convention, ArgConvention::MutableRef)
                            && !mutations_modelled(operation)
                        {
                            escape_operand(operand, escaped);
                        }
                    }
                }
                None => {
                    for operand in operation.operands.iter() {
                        escape_operand(operand, escaped);
                    }
                }
            },
            // The source is read the way a `Let` argument is and the destination written the way a
            // call's result place is, so neither escapes — exactly as when a clone was spelled as a
            // call. The callee is read by reference.
            OperationKind::Clone { .. } => {}
            OperationKind::Drop { .. } => {
                let target = &operation.operands[0];
                if !mutations_modelled(operation)
                    && register_places
                        .root_of(target)
                        .is_none_or(|root| !self_contained_roots.contains(&root))
                {
                    escape_operand(target, escaped);
                }
                for operand in operation.operands.iter().skip(1) {
                    escape_operand(operand, escaped);
                }
            }
            // Everything else — projections, drops, closure building, comparisons — takes its
            // places outside what this analysis models.
            _ => {
                for operand in operation.operands.iter() {
                    escape_operand(operand, escaped);
                }
            }
        }
    };

    for block_id in func.blocks() {
        let block = func.block(block_id);
        for operation in block.operations() {
            scan(operation, &mut escaped);
        }
        match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => scan(operation, &mut escaped),
            TerminatorKind::CondBr { condition, .. } => {
                escape_operand(condition, &mut escaped);
            }
            TerminatorKind::Yield { place, .. } => escape_operand(place, &mut escaped),
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup => {}
        }
    }
    (escaped, register_places)
}

/// How a `call` operation uses each of its operands.
///
/// The layout is `[callee, extras.., args.., ret]`, matching the callee's parameter order
/// (`@extra`, `@arg`, `@ret`); the number of hidden evidence operands follows from the visible
/// argument count in the call's type.
pub(crate) struct CallOperands<'a> {
    pub callee: &'a mir::Value,
    pub extras: &'a [mir::Value],
    /// Visible arguments, paired with the convention the callee receives them under.
    pub arguments: Vec<(&'a mir::Value, ArgConvention)>,
    pub result: &'a mir::Value,
}

pub(crate) fn call_operands<'a>(
    operands: &'a [mir::Value],
    ty: &CallImplType,
) -> Option<CallOperands<'a>> {
    let visible = ty.fn_ty.args.len();
    // callee + extras + args + ret
    let extras = operands.len().checked_sub(visible + 2)?;
    let conventions = arg_conventions_for_args(&ty.fn_ty.args);
    Some(CallOperands {
        callee: &operands[0],
        extras: &operands[1..1 + extras],
        arguments: operands[1 + extras..1 + extras + visible]
            .iter()
            .zip(conventions)
            .collect(),
        result: operands.last()?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, ExecutionTarget, Location,
        compiler::MirOptimization,
        containers::b,
        hir::value::VariantPayloadStorage,
        mir::{Operation, builder::FunctionBuilder, terminator::Terminator},
        module::Path,
        std::math::int_type,
        types::r#type::Type,
        ustr,
    };

    fn compile(session: &mut CompilerSession, src: &str) -> crate::module::ModuleId {
        session
            .compile_for(ExecutionTarget::Mir, src, "test", Path::single_str("test"))
            .expect("test source must compile")
            .module_id
    }

    fn body<'a>(
        session: &'a CompilerSession,
        module: crate::module::ModuleId,
        name: &str,
    ) -> &'a Function {
        let id = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr(name))
            .unwrap_or_else(|| panic!("no function named {name}"));
        session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .expect("MIR must be prepared")
            .get(id)
            .expect("function must have a MIR body")
    }

    fn allocas(func: &Function) -> impl Iterator<Item = ValueId> + '_ {
        func.blocks()
            .flat_map(|block| func.block(block).operations().iter())
            .filter_map(|operation| match operation.kind {
                OperationKind::Alloca { .. } => operation.result_id(),
                _ => None,
            })
    }

    /// Every fact the analysis holds at the end of the entry block, for a single-block function.
    fn entry_block_exit(func: &Function, env: ModuleEnv<'_>) -> (Analysis, State) {
        let analysis = analyze(func, env);
        let mut state = analysis.entry_state(func.entry());
        for operation in func.block(func.entry()).operations() {
            analysis.step(func, env, operation, &mut state);
        }
        (analysis, state)
    }

    /// A literal stored into a local is known; the place holding a call result is not, because
    /// nothing folds calls yet.
    #[test]
    fn a_stored_literal_is_known() {
        let session = CompilerSession::new();
        let span = Location::new_synthesized();
        let env = session.module_env();

        let mut builder = FunctionBuilder::new("known".into(), Default::default());
        let block = builder.add_block();
        let slot = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        let constant = builder.add_constant(int_type(), LiteralValue::new_native(5isize), &env);
        builder.append_operation(
            block,
            Operation::store(span, mir::Value::Constant(constant), slot.clone()),
        );
        let loaded = builder
            .append_operation(block, Operation::load(span, slot.clone()))
            .unwrap();
        builder.set_terminator(block, Terminator::ret(span));
        let func = builder.finish(env);

        let (analysis, state) = entry_block_exit(&func, env);
        let key = analysis.place_of(&slot).expect("the alloca names a place");
        let expected = Fact::Known(Const::Literal(LiteralValue::new_native(5isize)));
        assert_eq!(state.place(&key), expected);
        let mir::Value::Register(slot) = slot else {
            panic!("`alloca` defines a register");
        };
        assert_eq!(
            state.register(slot),
            None,
            "structural place bindings must not be copied into flow states"
        );
        // And loading it carries the same fact into a register.
        let mir::Value::Register(loaded) = loaded else {
            panic!("`load` defines a register");
        };
        assert_eq!(state.register(loaded), Some(&expected));
    }

    #[test]
    fn a_constructed_variant_tag_compares_symbolically() {
        let session = CompilerSession::new();
        let span = Location::new_synthesized();
        let env = session.module_env();
        let tag = ustr("Some");
        let variant_ty = Type::variant([(tag, Type::unit())]);

        let mut builder = FunctionBuilder::new("known_variant_tag".into(), Default::default());
        let block = builder.add_block();
        let slot = builder
            .append_operation(block, Operation::alloca(span, variant_ty))
            .unwrap();
        let shell = builder
            .append_operation(
                block,
                Operation::variant(
                    span,
                    tag,
                    variant_ty,
                    Some(VariantPayloadStorage::Inline),
                    None,
                ),
            )
            .unwrap();
        builder.append_operation(block, Operation::store(span, shell, slot.clone()));
        let extracted = builder
            .append_operation(block, Operation::extract_tag(span, slot))
            .unwrap();
        let equal = builder
            .append_operation(
                block,
                Operation::compare_eq(
                    span,
                    extracted,
                    mir::Value::Pattern(b(LiteralValue::new_variant_tag(tag))),
                ),
            )
            .unwrap();
        builder.set_terminator(block, Terminator::ret(span));
        let func = builder.finish(env);

        let (_, state) = entry_block_exit(&func, env);
        let mir::Value::Register(equal) = equal else {
            panic!("compare_eq defines a register")
        };
        assert_eq!(
            state.register(equal),
            Some(&Fact::Known(Const::Literal(LiteralValue::new_native(true))))
        );
    }

    /// A `Let` argument place does not escape: the convention is immutable and non-escaping, and
    /// keeping those places tracked is precisely what lets a call fold.
    #[test]
    fn a_let_argument_place_does_not_escape() {
        let mut session = CompilerSession::new();
        let module = compile(&mut session, "fn f() -> int { 2 + 3 }");
        let func = body(&session, module, "f");

        let analysis = analyze(func, session.module_env());
        let escaped = allocas(func)
            .filter(|id| analysis.is_escaped(Root::Alloca(*id)))
            .count();
        assert_eq!(
            escaped, 0,
            "`2 + 3` passes every place by `Let`, so none of them may escape"
        );
    }

    /// A place reaching an operation with no transfer function escapes, and stays untracked for the
    /// whole function. `drop` is one: it hands the place to a `Value::drop` implementation.
    #[test]
    fn a_place_reaching_an_unmodelled_operation_escapes() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn f() -> string { string_concat(\"ab\", \"cd\") }",
        );
        let func = body(&session, module, "f");

        let analysis = analyze(func, session.module_env());
        let escaped = allocas(func)
            .filter(|id| analysis.is_escaped(Root::Alloca(*id)))
            .count();
        assert!(
            escaped > 0,
            "the string temporaries are dropped, which this analysis does not model"
        );
    }

    /// Lowering emits a `subfield`'s index as a constant-pool reference, not an inline literal, so
    /// the analysis has to resolve the pool to track fields at all. Reading only the inline form
    /// silently disabled every field-sensitive answer — and, through the escape scan, escaped the
    /// base of every `subfield` as though its index were dynamic.
    #[test]
    fn a_field_index_from_the_constant_pool_is_resolved() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "struct S { a: int, b: int }\nfn f() -> int { let s = S { a: 1, b: 2 }; s.a }",
        );
        let func = body(&session, module, "f");

        let analysis = analyze(func, session.module_env());
        let escaped = allocas(func)
            .filter(|id| analysis.is_escaped(Root::Alloca(*id)))
            .count();
        assert_eq!(
            escaped, 0,
            "a constant field index is not a dynamic one, so nothing may escape"
        );

        let (block, field) = func
            .blocks()
            .find_map(|block| {
                func.block(block)
                    .operations()
                    .iter()
                    .find_map(|operation| match operation.kind {
                        OperationKind::Subfield { .. } => operation.result_id(),
                        _ => None,
                    })
                    .map(|field| (block, field))
            })
            .expect("field access must contain a subfield");
        let key = analysis
            .place_of(&mir::Value::Register(field))
            .expect("the structural scan resolves the subfield");
        assert!(!key.path.is_empty());

        let mut state = analysis.entry_state(block);
        for operation in func.block(block).operations() {
            analysis.step(func, session.module_env(), operation, &mut state);
        }
        assert_eq!(
            state.register(field),
            None,
            "subfield bindings must not be copied into flow states"
        );
    }

    /// A move leaves its source moved-out, which the folding pass must not mistake for a value.
    #[test]
    fn a_move_leaves_its_source_uninitialized() {
        let session = CompilerSession::new();
        let span = Location::new_synthesized();
        let env = session.module_env();

        let mut builder = FunctionBuilder::new("moved".into(), Default::default());
        let block = builder.add_block();
        let source = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        let destination = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        // A move reads its source, so it must be initialized first — the verifier enforces it.
        let constant = builder.add_constant(int_type(), LiteralValue::new_native(1isize), &env);
        builder.append_operation(
            block,
            Operation::store(span, mir::Value::Constant(constant), source.clone()),
        );
        builder.append_operation(
            block,
            Operation::move_value(span, source.clone(), destination.clone()),
        );
        builder.set_terminator(block, Terminator::ret(span));
        let func = builder.finish(env);

        let (analysis, state) = entry_block_exit(&func, env);
        let source_key = analysis.place_of(&source).expect("a tracked source place");
        assert_eq!(state.place(&source_key), Fact::Uninit);
    }

    /// An entry of a *constant* dictionary is a known function — the fact devirtualization reads.
    ///
    /// Constant dictionary operands do not appear in emitted MIR: a `dict_entry` reads a
    /// dictionary *parameter*, which only becomes constant once inlining substitutes the caller's
    /// operand for it. So this is exercised on a hand-built function until inlining lands.
    #[test]
    fn an_entry_of_a_constant_dictionary_is_a_known_function() {
        let mut session = CompilerSession::new();
        // Harvest a real dictionary from lowered MIR rather than fabricating one.
        let module = compile(
            &mut session,
            "fn addg(a, b) { a + b }\nfn main() -> int { addg(1, 2) }",
        );
        let dictionary = body(&session, module, "main")
            .blocks()
            .flat_map(|block| {
                body(&session, module, "main")
                    .block(block)
                    .operations()
                    .to_vec()
            })
            .find_map(|operation| {
                operation.operands.iter().find_map(|operand| match operand {
                    mir::Value::Dictionary(id) => Some(*id),
                    _ => None,
                })
            })
            .expect("the generic call passes a constant dictionary");

        let span = Location::new_synthesized();
        let env = session.module_env();
        let mut builder = FunctionBuilder::new("entry".into(), Default::default());
        let block = builder.add_block();
        let entry = builder
            .append_operation(
                block,
                Operation::dict_entry(
                    span,
                    mir::Value::Dictionary(dictionary),
                    crate::types::r#trait::TraitDictionaryEntryIndex::new(0),
                    int_type(),
                ),
            )
            .unwrap();
        builder.set_terminator(block, Terminator::ret(span));
        let func = builder.finish(env);

        let (analysis, state) = entry_block_exit(&func, env);
        let key = analysis.place_of(&entry).expect("the entry names a place");
        assert!(
            matches!(state.place(&key), Fact::Known(Const::Function(_))),
            "an entry of a constant dictionary must resolve: {:?}",
            state.place(&key)
        );
    }

    /// Facts that disagree on two paths join to `Unknown`.
    #[test]
    fn disagreeing_paths_join_to_unknown() {
        assert_eq!(
            Fact::Known(Const::Function(FunctionId {
                module: crate::module::ModuleId::new(0),
                function: crate::module::LocalFunctionId::new(0),
            }))
            .join(&Fact::Uninit),
            Fact::Unknown
        );
        assert_eq!(Fact::Uninit.join(&Fact::Uninit), Fact::Uninit);
    }

    /// A back edge can invalidate the fact first propagated from the entry. The worklist must then
    /// revisit the header and its successors rather than treating their first states as settled.
    #[test]
    fn a_loop_back_edge_revisits_changed_entries() {
        let session = CompilerSession::new();
        let span = Location::new_synthesized();
        let env = session.module_env();

        let mut builder = FunctionBuilder::new("loop_join".into(), Default::default());
        let entry = builder.add_block();
        let header = builder.add_block();
        let body = builder.add_block();
        let exit = builder.add_block();
        let slot = builder
            .append_operation(entry, Operation::alloca(span, int_type()))
            .unwrap();
        let one = builder.add_constant(int_type(), LiteralValue::new_native(1isize), &env);
        let two = builder.add_constant(int_type(), LiteralValue::new_native(2isize), &env);
        let condition = builder.add_constant(
            crate::std::logic::bool_type(),
            LiteralValue::new_native(true),
            &env,
        );
        builder.append_operation(
            entry,
            Operation::store(span, mir::Value::Constant(one), slot.clone()),
        );
        builder.set_terminator(entry, Terminator::goto(span, header));
        builder.set_terminator(
            header,
            Terminator::cond_br(span, mir::Value::Constant(condition), body, exit),
        );
        builder.append_operation(
            body,
            Operation::store(span, mir::Value::Constant(two), slot.clone()),
        );
        builder.set_terminator(body, Terminator::goto(span, header));
        builder.set_terminator(exit, Terminator::ret(span));
        let func = builder.finish(env);

        let analysis = analyze(&func, env);
        let state = analysis.entry_state(header);
        let key = analysis.place_of(&slot).expect("the alloca names a place");
        assert_eq!(state.place(&key), Fact::Unknown);
    }
}
