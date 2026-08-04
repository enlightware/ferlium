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
//! - **Registers.** A register either *names* a place (`alloca`, `subfield`) or holds a
//!   materialized value (`load`). [`RegisterFact`] distinguishes the two, so an operand can be
//!   followed to the storage it refers to.
//!
//! **Escape is computed once, flow-insensitively, before the dataflow runs.** A root whose place
//! reaches any context this analysis does not model — a call argument, a `store` of the pointer
//! itself, an operation with no transfer function — is marked escaped, and escaped roots are never
//! tracked anywhere in the function. That is coarser than a flow-sensitive escape analysis and
//! deliberately so: the cost of being wrong here is unsound folding, while the cost of being coarse
//! is an unfolded call. The set of *modelled* operations is the whitelist; everything else escapes
//! its place operands.
//!
//! See `doc/plans/partial-evaluation.md`.
//!
//! The folding pass that consumes this is the next deliverable, so the items here are exercised
//! only by the tests below.
#![allow(dead_code)]

use rustc_hash::{FxHashMap, FxHashSet};

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
    module::{FunctionId, ModuleEnv, TraitDictionaryEntry, TraitDictionaryId},
    types::r#trait::TraitDictionaryEntryIndex,
    types::r#type::CallImplType,
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
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct PlaceKey {
    pub root: Root,
    pub path: Vec<usize>,
}

impl PlaceKey {
    fn root(root: Root) -> Self {
        Self {
            root,
            path: Vec::new(),
        }
    }

    fn field(&self, index: usize) -> Self {
        let mut path = self.path.clone();
        path.push(index);
        Self {
            root: self.root,
            path,
        }
    }

    /// Whether `self` is `other` or lies inside it.
    fn is_within(&self, other: &PlaceKey) -> bool {
        self.root == other.root
            && self.path.len() >= other.path.len()
            && self.path[..other.path.len()] == other.path[..]
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

/// What a register denotes.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum RegisterFact {
    /// The register is a pointer to this storage slot.
    Place(PlaceKey),
    /// The register holds a materialized value.
    Value(Fact),
}

/// The analysis state at one program point.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub(crate) struct State {
    places: FxHashMap<PlaceKey, Fact>,
    registers: FxHashMap<ValueId, RegisterFact>,
}

impl State {
    /// The fact for a slot. Absent means `Unknown`: an untracked slot is one nothing is known about.
    pub(crate) fn place(&self, key: &PlaceKey) -> Fact {
        self.places.get(key).cloned().unwrap_or_default()
    }

    pub(crate) fn register(&self, id: ValueId) -> Option<&RegisterFact> {
        self.registers.get(&id)
    }

    /// The slot an operand names, if it names one this analysis tracks.
    pub(crate) fn place_of(&self, operand: &mir::Value) -> Option<PlaceKey> {
        match operand {
            mir::Value::Register(id) => match self.registers.get(id)? {
                RegisterFact::Place(key) => Some(key.clone()),
                RegisterFact::Value(_) => None,
            },
            mir::Value::Parameter(id) => Some(PlaceKey::root(Root::Parameter(*id))),
            _ => None,
        }
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
                let joined = match (fact, theirs) {
                    (RegisterFact::Place(ours), RegisterFact::Place(theirs)) if ours == theirs => {
                        RegisterFact::Place(ours.clone())
                    }
                    (RegisterFact::Value(ours), RegisterFact::Value(theirs)) => {
                        RegisterFact::Value(ours.join(theirs))
                    }
                    _ => RegisterFact::Value(Fact::Unknown),
                };
                registers.insert(*id, joined);
            }
        }
        State { places, registers }
    }
}

/// The result of analysing a function: the state on entry to each block.
pub(crate) struct Analysis {
    entry_states: FxHashMap<BlockId, State>,
    escaped: FxHashSet<Root>,
}

impl Analysis {
    /// Whether `root` is tracked at all. An escaped root is `Unknown` everywhere.
    pub(crate) fn is_escaped(&self, root: Root) -> bool {
        self.escaped.contains(&root)
    }

    /// The state on entry to `block`.
    pub(crate) fn entry_state(&self, block: BlockId) -> State {
        self.entry_states.get(&block).cloned().unwrap_or_default()
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
        transfer(operation, func, env, &self.escaped, state);
    }
}

/// Runs the analysis to fixpoint over `func`.
pub(crate) fn analyze(func: &Function, env: ModuleEnv<'_>) -> Analysis {
    let escaped = escaping_roots(func);

    let mut entry_states: FxHashMap<BlockId, State> = FxHashMap::default();
    entry_states.insert(func.entry(), State::default());

    // Blocks are visited in index order until nothing changes. Bodies are small and the lattice is
    // finite in the facts it can hold, so this settles quickly; a worklist can come later if a
    // profile asks for one.
    let mut changed = true;
    while changed {
        changed = false;
        for block_id in func.blocks() {
            let Some(entry) = entry_states.get(&block_id).cloned() else {
                continue;
            };
            let mut state = entry;
            let block = func.block(block_id);
            for operation in block.operations() {
                transfer(operation, func, env, &escaped, &mut state);
            }
            if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
                transfer(operation, func, env, &escaped, &mut state);
            }
            for successor in successors(&block.terminator().kind) {
                let updated = match entry_states.get(&successor) {
                    Some(existing) => existing.join(&state),
                    None => state.clone(),
                };
                if entry_states.get(&successor) != Some(&updated) {
                    entry_states.insert(successor, updated);
                    changed = true;
                }
            }
        }
    }

    Analysis {
        entry_states,
        escaped,
    }
}

fn successors(kind: &TerminatorKind) -> Vec<BlockId> {
    match kind {
        TerminatorKind::Goto { target } => vec![*target],
        TerminatorKind::CondBr {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        TerminatorKind::Invoke { normal, error, .. } => vec![*normal, *error],
        TerminatorKind::Yield { resume, .. } => vec![*resume],
        TerminatorKind::Return
        | TerminatorKind::PropagateError
        | TerminatorKind::FailureDuringCleanup => Vec::new(),
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
    state: &mut State,
) {
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
            state.places.insert(key.clone(), Fact::Uninit);
            state.registers.insert(result, RegisterFact::Place(key));
        }
        OperationKind::Store => {
            let Some(key) = state.place_of(&operation.operands[1]) else {
                return;
            };
            if !tracked(&key) {
                return;
            }
            let fact = value_operand_fact(&operation.operands[0], func, state);
            state.set_place(key, fact);
        }
        OperationKind::Clear => {
            if let Some(key) = state.place_of(&operation.operands[0])
                && tracked(&key)
            {
                state.set_place(key, Fact::Uninit);
            }
        }
        OperationKind::Load => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let fact = match state.place_of(&operation.operands[0]) {
                Some(key) if tracked(&key) => state.place(&key),
                _ => Fact::Unknown,
            };
            state.registers.insert(result, RegisterFact::Value(fact));
        }
        OperationKind::Subfield { .. } => {
            let Some(result) = operation.result_id() else {
                return;
            };
            // The field index is a literal `int` operand; a non-constant index means an unknown
            // slot, which the escape scan has already accounted for by escaping the root.
            let binding = match (
                state.place_of(&operation.operands[0]),
                field_index(&operation.operands[1]),
            ) {
                (Some(base), Some(index)) if tracked(&base) => {
                    RegisterFact::Place(base.field(index))
                }
                _ => RegisterFact::Value(Fact::Unknown),
            };
            state.registers.insert(result, binding);
        }
        OperationKind::Memcpy | OperationKind::Move => {
            let source = state.place_of(&operation.operands[0]);
            let destination = state.place_of(&operation.operands[1]);
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
            let scrutinee = match state.place_of(&operation.operands[0]) {
                Some(key) if tracked(&key) => state.place(&key),
                Some(_) => Fact::Unknown,
                None => value_operand_fact(&operation.operands[0], func, state),
            };
            let fact = match (scrutinee.known(), &operation.operands[1]) {
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
            state.registers.insert(result, RegisterFact::Value(fact));
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
            state.places.insert(key.clone(), fact);
            state.registers.insert(result, RegisterFact::Place(key));
        }
        OperationKind::Call { ty } => {
            // The callee writes its result through the trailing out-pointer, so whatever was known
            // about that slot no longer holds. The folding pass is what replaces a call with a
            // store of a known constant; until it does, the result is unknown.
            if let Some(call) = call_operands(&operation.operands, ty)
                && let Some(key) = state.place_of(call.result)
                && tracked(&key)
            {
                state.set_place(key, Fact::Unknown);
            }
        }
        _ => {
            // Not modelled: the escape scan has escaped every place this operation touches, so
            // there is nothing left to invalidate. A result register, if any, is an unknown value.
            if let Some(result) = operation.result_id() {
                state
                    .registers
                    .insert(result, RegisterFact::Value(Fact::Unknown));
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
        mir::Value::Register(id) => match state.registers.get(id) {
            Some(RegisterFact::Value(fact)) => fact.clone(),
            _ => Fact::Unknown,
        },
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

fn field_index(operand: &mir::Value) -> Option<usize> {
    match operand {
        mir::Value::Pattern(literal) => literal
            .as_primitive_ty::<isize>()
            .and_then(|index| usize::try_from(*index).ok()),
        _ => None,
    }
}

/// Roots that reach a context the analysis does not model, and are therefore never tracked.
///
/// Conservative by construction: the modelled operations below are a whitelist, and every other use
/// of a place escapes its root. A root also escapes if it is reached other than through an `alloca`
/// result or a parameter — an operand this scan cannot resolve to a root escapes nothing precisely
/// because nothing was tracked for it in the first place.
fn escaping_roots(func: &Function) -> FxHashSet<Root> {
    // Registers that name a root, discovered structurally rather than by dataflow: an `alloca`
    // defines one, and a `subfield` of a rooted place stays in the same root.
    let mut register_roots: FxHashMap<ValueId, Root> = FxHashMap::default();
    for block_id in func.blocks() {
        for operation in func.block(block_id).operations() {
            match (&operation.kind, operation.result_id()) {
                (OperationKind::Alloca { .. }, Some(result)) => {
                    register_roots.insert(result, Root::Alloca(result));
                }
                (OperationKind::DictEntry { .. }, Some(result)) => {
                    register_roots.insert(result, Root::DictEntry(result));
                }
                (OperationKind::Subfield { .. }, Some(result)) => {
                    if let Some(root) = operand_root(&operation.operands[0], &register_roots) {
                        register_roots.insert(result, root);
                    }
                }
                _ => {}
            }
        }
    }

    let mut escaped = FxHashSet::default();
    let escape_operand = |operand: &mir::Value, escaped: &mut FxHashSet<Root>| {
        if let Some(root) = operand_root(operand, &register_roots) {
            escaped.insert(root);
        }
    };

    let scan = |operation: &Operation, escaped: &mut FxHashSet<Root>| {
        match &operation.kind {
            // Modelled: these consume places in ways the transfer functions describe exactly.
            OperationKind::Alloca { .. } => {}
            // `comp_eq` borrows its scrutinee for a literal snapshot and never moves it, so the
            // place stays tracked; its second operand is compile-time pattern data.
            OperationKind::Load | OperationKind::Clear | OperationKind::CompareEqual => {}
            // Its operand is evidence rather than storage, and its result is a place this analysis
            // roots itself.
            OperationKind::DictEntry { .. } => {}
            OperationKind::Subfield { .. } => {
                // A dynamic field index would name a slot the analysis cannot distinguish.
                if field_index(&operation.operands[1]).is_none() {
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
            OperationKind::Call { ty } => match call_operands(&operation.operands, ty) {
                // A `Let` argument is immutable and non-escaping by the language's own convention,
                // and the callee reads its function value and evidence by reference. What a call
                // does change is its result place, which the transfer function kills. Anything the
                // callee may write through — a `MutableRef` argument — escapes.
                Some(call) => {
                    for (operand, convention) in &call.arguments {
                        if matches!(convention, ArgConvention::MutableRef) {
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
    escaped
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

fn operand_root(operand: &mir::Value, roots: &FxHashMap<ValueId, Root>) -> Option<Root> {
    match operand {
        mir::Value::Register(id) => roots.get(id).copied(),
        mir::Value::Parameter(id) => Some(Root::Parameter(*id)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, ExecutionTarget, Location,
        compiler::MirOptimization,
        mir::{Operation, builder::FunctionBuilder, terminator::Terminator},
        module::Path,
        std::math::int_type,
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
    fn entry_block_exit(func: &Function, env: ModuleEnv<'_>) -> State {
        let analysis = analyze(func, env);
        let mut state = analysis.entry_state(func.entry());
        for operation in func.block(func.entry()).operations() {
            analysis.step(func, env, operation, &mut state);
        }
        state
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

        let state = entry_block_exit(&func, env);
        let key = state.place_of(&slot).expect("the alloca names a place");
        let expected = Fact::Known(Const::Literal(LiteralValue::new_native(5isize)));
        assert_eq!(state.place(&key), expected);
        // And loading it carries the same fact into a register.
        let mir::Value::Register(loaded) = loaded else {
            panic!("`load` defines a register");
        };
        assert_eq!(state.register(loaded), Some(&RegisterFact::Value(expected)));
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

        let state = entry_block_exit(&func, env);
        let source_key = state.place_of(&source).expect("a tracked source place");
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

        let state = entry_block_exit(&func, env);
        let key = state.place_of(&entry).expect("the entry names a place");
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
}
