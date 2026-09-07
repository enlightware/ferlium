// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! What the folding pass knows at each point of a function: which storage slots hold which
//! compile-time constants or bounded sets of possible outcomes.
//!
//! Analysis only — nothing here rewrites MIR. It answers one question for the folding pass: at this
//! call site, is every argument place fully known? Finite outcome domains also let it answer
//! which branches remain possible without evaluating opaque native functions.
//!
//! The model has two layers, because MIR is storage-explicit:
//!
//! - **Places.** A [`Root`] is an `alloca` result or a parameter. Root and field paths are interned
//!   as compact [`PlaceId`]s, so `store 5 to %r1.0` is known independently of `%r1.1` without
//!   cloning or hashing projection vectors in every flow state.
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

use std::{borrow::Cow, cmp::Reverse, collections::BinaryHeap};

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use ustr::Ustr;

use crate::{
    hir::{
        function::{ArgConvention, arg_conventions_for_args},
        native_functions::NativeResultKnowledge,
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
    std::math::Int,
    types::r#trait::TraitDictionaryEntryIndex,
    types::r#type::{CallImplType, Type, TypeKind},
};

/// A root of addressable storage the analysis can track.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Root {
    /// Storage allocated by an `alloca` or `runtime_alloc` in this function.
    Alloca(ValueId),
    /// Storage owned by the caller and named by a parameter.
    Parameter(ParameterId),
    /// The cell a `dict_entry` materializes its entry into. Not storage the function allocated, but
    /// a place all the same, and the one devirtualization reads: an entry of a constant dictionary
    /// is a known function.
    DictEntry(ValueId),
}

crate::define_id_type!(
    /// An interned storage path within one dataflow analysis.
    PlaceId
);

struct Place {
    root: Root,
    children: Vec<PlaceId>,
    depth: usize,
}

/// Immutable register-to-storage structure.
///
/// A dynamic `subfield` still has a known root, which escape analysis and diagnostics need, but no
/// exact [`PlaceId`] the folding analysis may safely read.
#[derive(Clone, PartialEq, Eq, Debug)]
enum PlaceBinding {
    Exact(PlaceId),
    Root(Root),
}

#[derive(Default)]
pub(crate) struct PlaceBindings {
    registers: FxHashMap<ValueId, PlaceBinding>,
    parameters: Vec<PlaceId>,
    places: Vec<Place>,
}

struct PlaceBuilder {
    bindings: PlaceBindings,
    roots: FxHashMap<Root, PlaceId>,
    fields: FxHashMap<(PlaceId, ProjectionIndex), PlaceId>,
}

impl PlaceBuilder {
    fn new(func: &Function) -> Self {
        let mut builder = Self {
            bindings: PlaceBindings::default(),
            roots: FxHashMap::default(),
            fields: FxHashMap::default(),
        };
        for index in 0..func.parameters().len() {
            let parameter = builder.intern_root(Root::Parameter(ParameterId::from_index(index)));
            builder.bindings.parameters.push(parameter);
        }
        builder
    }

    fn intern_root(&mut self, root: Root) -> PlaceId {
        if let Some(place) = self.roots.get(&root) {
            return *place;
        }
        let place = PlaceId::from_index(self.bindings.places.len());
        self.bindings.places.push(Place {
            root,
            children: Vec::new(),
            depth: 0,
        });
        self.roots.insert(root, place);
        place
    }

    fn intern_field(&mut self, parent: PlaceId, index: ProjectionIndex) -> PlaceId {
        if let Some(place) = self.fields.get(&(parent, index)) {
            return *place;
        }
        let place = PlaceId::from_index(self.bindings.places.len());
        self.bindings.places.push(Place {
            root: self.bindings.places[parent.as_index()].root,
            children: Vec::new(),
            depth: self.bindings.places[parent.as_index()].depth + 1,
        });
        self.bindings.places[parent.as_index()].children.push(place);
        self.fields.insert((parent, index), place);
        place
    }

    fn finish(self) -> PlaceBindings {
        self.bindings
    }
}

impl PlaceBindings {
    fn place_of(&self, operand: &mir::Value) -> Option<PlaceId> {
        match operand {
            mir::Value::Register(id) => match self.registers.get(id)? {
                PlaceBinding::Exact(place) => Some(*place),
                PlaceBinding::Root(_) => None,
            },
            mir::Value::Parameter(id) => self.parameters.get(id.as_index()).copied(),
            _ => None,
        }
    }

    pub(crate) fn root_of(&self, operand: &mir::Value) -> Option<Root> {
        match operand {
            mir::Value::Register(id) => self.root_of_register(*id),
            mir::Value::Parameter(id) => Some(Root::Parameter(*id)),
            _ => None,
        }
    }

    pub(crate) fn depth_of(&self, operand: &mir::Value) -> Option<usize> {
        match operand {
            mir::Value::Register(id) => match self.registers.get(id)? {
                PlaceBinding::Exact(place) => Some(self.places[place.as_index()].depth),
                PlaceBinding::Root(_) => None,
            },
            mir::Value::Parameter(id) => self
                .parameters
                .get(id.as_index())
                .map(|place| self.places[place.as_index()].depth),
            _ => None,
        }
    }

    pub(crate) fn root_of_register(&self, id: ValueId) -> Option<Root> {
        match self.registers.get(&id)? {
            PlaceBinding::Exact(place) => Some(self.root_of_place(*place)),
            PlaceBinding::Root(root) => Some(*root),
        }
    }

    fn root_of_place(&self, place: PlaceId) -> Root {
        self.places[place.as_index()].root
    }

    fn children(&self, place: PlaceId) -> &[PlaceId] {
        &self.places[place.as_index()].children
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
    /// Recursively static hidden evidence.
    Evidence(mir::value::StaticEvidence),
    /// A dictionary entry function together with its closed hidden evidence.
    ClosedFunction {
        function: FunctionId,
        hidden_evidence: Vec<mir::value::StaticEvidence>,
    },
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
/// Known integer values and variant tags may join into bounded sets of outcomes; exceeding the
/// bound yields `Unknown`. Other disagreeing facts, including `Uninit`, join to `Unknown`.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub(crate) enum Fact {
    /// Nothing is known; the slot may hold anything.
    #[default]
    Unknown,
    /// The slot holds no value (never initialized, cleared, or moved out).
    Uninit,
    /// The slot holds this constant.
    Known(Const),
    /// A bounded set of possible integer values or semantic variant tags.
    Outcomes(std::rc::Rc<[Outcome]>),
}

impl Fact {
    fn join(&self, other: &Fact) -> Fact {
        if self == other {
            self.clone()
        } else if let (Some(ours), Some(theirs)) = (self.outcomes(), other.outcomes()) {
            Self::from_outcomes(ours.chain(theirs))
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
    places: FxHashMap<PlaceId, Fact>,
    /// Flow-dependent facts for registers that hold materialized values. Registers that name
    /// places are structural and live once in [`Analysis::register_places`].
    registers: FxHashMap<ValueId, Fact>,
    tests: FxHashMap<ValueId, EqualityTest>,
    origins: FxHashMap<ValueId, Subject>,
}

impl State {
    /// The fact for a slot. Absent means `Unknown`: an untracked slot is one nothing is known about.
    pub(crate) fn place(&self, place: PlaceId) -> Fact {
        self.places.get(&place).cloned().unwrap_or_default()
    }

    /// Whether a slot's contents are known, without materializing the fact.
    ///
    /// A fact carries a cloned literal or array recipe, which is wasted when the question is only
    /// whether there is one. Asked at every call site of the most common calls in a body.
    pub(crate) fn place_is_known(&self, place: PlaceId) -> bool {
        self.places
            .get(&place)
            .is_some_and(|fact| fact.known().is_some())
    }

    pub(crate) fn register(&self, id: ValueId) -> Option<&Fact> {
        self.registers.get(&id)
    }

    fn set_place(&mut self, place: PlaceId, fact: Fact, bindings: &PlaceBindings) {
        // Writing a slot says nothing about the slots inside it, which the write replaced.
        self.forget_within(place, bindings);
        self.places.insert(place, fact);
    }

    fn forget_within(&mut self, place: PlaceId, bindings: &PlaceBindings) {
        // Conservatively invalidate all predicates/reads rooted in this storage. A materialized
        // value keeps its own domain, but must no longer refine the overwritten place.
        let root = bindings.root_of_place(place);
        self.invalidate_subjects(|subject| matches!(subject, Subject::Place(place) if bindings.root_of_place(place) == root));
        fn remove_subtree(
            facts: &mut FxHashMap<PlaceId, Fact>,
            bindings: &PlaceBindings,
            place: PlaceId,
        ) {
            facts.remove(&place);
            for child in bindings.children(place) {
                remove_subtree(facts, bindings, *child);
            }
        }
        remove_subtree(&mut self.places, bindings, place);
    }

    fn join(&self, other: &State) -> State {
        let mut places = FxHashMap::default();
        for (key, fact) in &self.places {
            // A slot tracked on one edge and absent on the other is Unknown on that edge, so it
            // joins to Unknown and is simply dropped.
            if let Some(theirs) = other.places.get(key) {
                let joined = fact.join(theirs);
                if joined != Fact::Unknown {
                    places.insert(*key, joined);
                }
            }
        }
        let mut registers = FxHashMap::default();
        for (id, fact) in &self.registers {
            if let Some(theirs) = other.registers.get(id) {
                registers.insert(*id, fact.join(theirs));
            }
        }
        let tests = self
            .tests
            .iter()
            .filter(|(id, test)| other.tests.get(id) == Some(test))
            .map(|(id, test)| (*id, test.clone()))
            .collect();
        let origins = self
            .origins
            .iter()
            .filter(|(id, subject)| other.origins.get(id) == Some(subject))
            .map(|(id, subject)| (*id, *subject))
            .collect();
        State {
            places,
            registers,
            tests,
            origins,
        }
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
    pub(crate) fn place_of(&self, operand: &mir::Value) -> Option<PlaceId> {
        self.register_places.place_of(operand)
    }

    /// The slot an operand names when its contents remain within the analysis model.
    ///
    /// Structural bindings deliberately include escaped places so diagnostics can explain why a
    /// fact is unavailable. Consumers must use this narrower lookup before reading or injecting a
    /// fact: an escaped place can be mutated by an operation the transfer function does not model.
    pub(crate) fn tracked_place_of(&self, operand: &mir::Value) -> Option<PlaceId> {
        let place = self.place_of(operand)?;
        (!self.is_escaped(self.root_of_place(place))).then_some(place)
    }

    pub(crate) fn root_of_place(&self, place: PlaceId) -> Root {
        self.register_places.root_of_place(place)
    }

    /// Records a fact the folding pass established by rewriting an operation.
    pub(crate) fn set_place_known(&self, state: &mut State, place: PlaceId, fact: Fact) {
        debug_assert!(
            !self.is_escaped(self.root_of_place(place)),
            "folding must not inject facts for escaped places"
        );
        state.set_place(place, fact, &self.register_places);
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

// --- Finite outcome domains ---

// Native adapters seed domains, not comparison laws. Branches restrict domains, copies retain
// them, and joins take their union. Predicates refer only to unmodified storage or materialized
// registers; writes invalidate their provenance, including across loop iterations.

const MAX_OUTCOMES: usize = 8;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) enum Outcome {
    Int(Int),
    Tag(Ustr),
}

impl Outcome {
    fn from_const(value: &Const) -> Option<Self> {
        match value {
            Const::Literal(value) => value.as_primitive_ty::<Int>().copied().map(Self::Int),
            Const::VariantTag(tag) => Some(Self::Tag(*tag)),
            _ => None,
        }
    }

    fn pattern(value: &LiteralValue) -> Option<Self> {
        value
            .as_variant_tag()
            .copied()
            .map(Self::Tag)
            .or_else(|| value.as_primitive_ty::<Int>().copied().map(Self::Int))
    }

    fn constant(&self) -> Const {
        match self {
            Self::Int(value) => Const::Literal(LiteralValue::new_native(*value)),
            Self::Tag(tag) => Const::VariantTag(*tag),
        }
    }
}

impl Fact {
    pub(crate) fn variant_tags(&self) -> Option<impl Iterator<Item = Ustr> + '_> {
        let values = self.outcomes()?;
        if !values.clone().all(|value| matches!(value, Outcome::Tag(_))) {
            return None;
        }
        Some(values.map(|value| match value {
            Outcome::Tag(tag) => tag,
            _ => unreachable!("the domain contains only tags"),
        }))
    }
    /// Read a domain without allocating, including the singleton represented by `Known`.
    fn outcomes(&self) -> Option<impl Iterator<Item = Outcome> + Clone + '_> {
        let (one, many) = match self {
            Self::Known(value) => (Some(Outcome::from_const(value)?), &[][..]),
            Self::Outcomes(values) => (None, values.as_ref()),
            _ => return None,
        };
        Some(one.into_iter().chain(many.iter().copied()))
    }

    fn from_outcomes(values: impl IntoIterator<Item = Outcome>) -> Self {
        // Temporary inline storage does not enlarge Fact. Immutable shared domains make the
        // much more frequent state copies and place reads independent of the set's size.
        let mut values: SmallVec<[Outcome; MAX_OUTCOMES]> = values.into_iter().collect();
        values.sort_unstable();
        values.dedup();
        match values.as_slice() {
            [value] => Self::Known(value.constant()),
            [] => Self::Unknown, // No domain supplied; restrictions handle impossible edges first.
            _ if values.len() <= MAX_OUTCOMES => Self::Outcomes(values.as_slice().into()),
            _ => Self::Unknown,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Subject {
    Place(PlaceId),
    Register(ValueId),
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct EqualityTest {
    subject: Subject,
    pattern: Outcome,
}

impl State {
    fn subject(&self, value: &mir::Value, bindings: &PlaceBindings) -> Option<Subject> {
        if let Some(place) = bindings.place_of(value) {
            return Some(Subject::Place(place));
        }
        let mir::Value::Register(id) = value else {
            return None;
        };
        Some(
            self.origins
                .get(id)
                .copied()
                .unwrap_or(Subject::Register(*id)),
        )
    }

    fn invalidate_subjects(&mut self, invalid: impl Fn(Subject) -> bool) {
        self.tests.retain(|_, test| !invalid(test.subject));
        self.origins.retain(|_, subject| !invalid(*subject));
    }

    fn remember_read(&mut self, result: ValueId, source: &mir::Value, bindings: &PlaceBindings) {
        if let Some(subject) = self.subject(source, bindings) {
            self.origins.insert(result, subject);
        }
    }

    fn compare_outcomes(
        &mut self,
        result: ValueId,
        operation: &Operation,
        scrutinee: &Fact,
        bindings: &PlaceBindings,
    ) -> Option<Fact> {
        let mir::Value::Pattern(pattern) = &operation.operands[1] else {
            return None;
        };
        let pattern = Outcome::pattern(pattern)?;
        let values = scrutinee.outcomes()?;
        let contains = values.clone().any(|value| value == pattern);
        if !contains || values.clone().count() == 1 {
            return Some(Fact::Known(Const::Literal(LiteralValue::new_native(
                contains,
            ))));
        }
        if let Some(subject) = self.subject(&operation.operands[0], bindings) {
            self.tests.insert(result, EqualityTest { subject, pattern });
        }
        None
    }

    fn restrict(&mut self, subject: Subject, keep: impl Fn(&Outcome) -> bool) {
        let fact = match subject {
            Subject::Place(place) => self.places.get_mut(&place),
            Subject::Register(id) => self.registers.get_mut(&id),
        };
        let Some(fact) = fact else { return };
        let Some(values) = fact.outcomes() else {
            return;
        };
        let count = values.clone().count();
        let restricted: SmallVec<[Outcome; MAX_OUTCOMES]> = values.filter(keep).collect();
        // Empty means the edge is impossible, not that the value became unknown. This analysis
        // conservatively still visits that edge, but must not weaken any of its existing facts.
        if restricted.is_empty() || restricted.len() == count {
            return;
        }
        *fact = Fact::from_outcomes(restricted);
        let fact = fact.clone();
        // Materialized copies of this still-current value carry the same restriction.
        for (id, origin) in &self.origins {
            if *origin == subject {
                self.registers.insert(*id, fact.clone());
            }
        }
    }

    fn on_edge<'a>(
        &'a self,
        terminator: &TerminatorKind,
        successor: BlockId,
        bindings: &PlaceBindings,
    ) -> Cow<'a, Self> {
        let mut state = Cow::Borrowed(self);
        match terminator {
            TerminatorKind::CondBr {
                condition: mir::Value::Register(id),
                then_target,
                else_target,
            } if then_target != else_target => {
                if let Some(test) = self.tests.get(id) {
                    state.to_mut().restrict(test.subject, |value| {
                        (value == &test.pattern) == (successor == *then_target)
                    });
                }
            }
            TerminatorKind::SwitchVariant {
                tag,
                cases,
                default,
            } => {
                if let Some(subject) = self.subject(tag, bindings) {
                    state.to_mut().restrict(subject, |value| {
                        let Outcome::Tag(tag) = value else {
                            return true;
                        };
                        cases
                            .iter()
                            .find_map(|(case, target)| (case == tag).then_some(*target))
                            .unwrap_or(*default)
                            == successor
                    });
                }
            }
            TerminatorKind::Invoke {
                operation, error, ..
            } if successor == *error => {
                if let OperationKind::Call { ty, .. } = &operation.kind
                    && let Some(call) = call_operands(&operation.operands, ty)
                    && let Some(place) = bindings.place_of(call.result)
                {
                    state.to_mut().set_place(place, Fact::Unknown, bindings);
                }
            }
            _ => {}
        }
        state
    }
}

/// A variant's closed case set is guaranteed by its type, regardless of who produces it.
fn type_fact(mut ty: Type, env: ModuleEnv<'_>) -> Fact {
    let mut visited = FxHashSet::default();
    loop {
        let named = {
            let kind = ty.data();
            match &*kind {
                TypeKind::Named(named) => named.clone(),
                TypeKind::Variant(cases) if cases.len() <= MAX_OUTCOMES => {
                    return Fact::from_outcomes(cases.iter().map(|(tag, _)| Outcome::Tag(*tag)));
                }
                _ => return Fact::Unknown,
            }
        };
        if !visited.insert(ty) {
            break;
        }
        ty = named.instantiated_shape(&env);
    }
    Fact::Unknown
}

/// Seed only unconditional parameter-type invariants, never facts specific to the first visit.
/// `analyze` also uses this state directly for a one-block function with a self back-edge.
fn entry_state(
    func: &Function,
    env: ModuleEnv<'_>,
    bindings: &PlaceBindings,
    escaped: &FxHashSet<Root>,
) -> State {
    let mut state = State::default();
    for (index, parameter) in func.parameters().iter().enumerate() {
        if matches!(
            parameter.kind,
            crate::mir::function::ParameterKind::Parameter(_)
                | crate::mir::function::ParameterKind::Owned
        ) {
            let place = bindings.parameters[index];
            if !escaped.contains(&bindings.root_of_place(place)) {
                let fact = type_fact(parameter.ty, env);
                if fact != Fact::Unknown {
                    state.places.insert(place, fact);
                }
            }
        }
    }
    state
}

/// Metadata is resolved from the actual module function, not a list of std identities.
fn native_result_fact(callee: &mir::Value, env: ModuleEnv<'_>) -> Fact {
    let mir::Value::Function(callee) = callee else {
        return Fact::Unknown;
    };
    let knowledge = env
        .module_by_id(callee.module)
        .and_then(|module| module.get_function_by_id(callee.function))
        .and_then(|function| {
            // Descriptions can be cloned or replaced by host code. Only trust a guarantee
            // still backed by the actual typed entry, not metadata copied from another callable.
            let declared = function.definition.native_result_knowledge();
            if declared == NativeResultKnowledge::Unknown {
                // The common case needs no virtual entry lookup to confirm absence of a proof.
                return None;
            }
            (function.code.native_entry()?.result_knowledge() == declared).then_some(declared)
        });
    match knowledge {
        Some(NativeResultKnowledge::OrderingCode) => {
            Fact::from_outcomes([Outcome::Int(-1), Outcome::Int(0), Outcome::Int(1)])
        }
        _ => Fact::Unknown,
    }
}

// --- Dataflow solver ---

/// Runs the analysis to fixpoint over `func`.
pub(crate) fn analyze(func: &Function, env: ModuleEnv<'_>) -> Analysis {
    let (escaped, register_places) = escaping_roots(func, &|_| false);
    let initial = entry_state(func, env, &register_places, &escaped);

    let block_count = func.blocks().count();
    // The consumer replays operations from each settled entry. A one-block function's only entry
    // contains only parameter-type guarantees, even when its terminator loops back to itself:
    // no back-edge fact can strengthen those unconditional entry guarantees.
    // There is no successor state for the solver to discover, so avoid duplicating that replay.
    if block_count == 1 {
        return Analysis {
            entry_states: vec![Some(initial)],
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
    entry_states[entry] = Some(initial);
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
            let edge = state.on_edge(&block.terminator().kind, successor, &register_places);
            let successor = successor.as_index();
            let updated = match &entry_states[successor] {
                Some(existing) => existing.join(&edge),
                None => edge.into_owned(),
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
    let tracked = |place| !escaped.contains(&register_places.root_of_place(place));
    if let Some(result) = operation.result_id() {
        state.invalidate_subjects(|subject| subject == Subject::Register(result));
        state.tests.remove(&result);
        state.origins.remove(&result);
    }
    match &operation.kind {
        OperationKind::Alloca { .. } | OperationKind::RuntimeAlloc { .. } => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let root = Root::Alloca(result);
            if escaped.contains(&root) {
                return;
            }
            let place = place_of(&mir::Value::Register(result))
                .expect("the structural scan interns every allocation");
            state.forget_within(place, register_places);
            state.places.insert(place, Fact::Uninit);
        }
        OperationKind::RuntimeDealloc => {
            if let Some(place) = place_of(&operation.operands[0]) {
                state.forget_within(place, register_places);
            }
        }
        OperationKind::Store => {
            let Some(place) = place_of(&operation.operands[1]) else {
                return;
            };
            if !tracked(place) {
                return;
            }
            let fact = value_operand_fact(&operation.operands[0], func, state);
            state.set_place(place, fact, register_places);
        }
        OperationKind::BuildArray { element_ty } => {
            let Some((destination, elements)) = operation.operands.split_last() else {
                return;
            };
            let Some(place) = place_of(destination) else {
                return;
            };
            if !tracked(place) {
                return;
            }
            let elements = elements
                .iter()
                .map(|operand| {
                    let fact = match place_of(operand) {
                        Some(place) if tracked(place) => state.place(place),
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
            state.set_place(place, fact, register_places);
        }
        OperationKind::Clear => {
            if let Some(place) = place_of(&operation.operands[0])
                && tracked(place)
            {
                state.set_place(place, Fact::Uninit, register_places);
            }
        }
        OperationKind::Load => {
            let Some(result) = operation.result_id() else {
                return;
            };
            let fact = match place_of(&operation.operands[0]) {
                Some(place) if tracked(place) => state.place(place),
                _ => Fact::Unknown,
            };
            state.registers.insert(result, fact);
            state.remember_read(result, &operation.operands[0], register_places);
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
                Some(place) if tracked(place) => match state.place(place) {
                    fact @ Fact::Known(Const::VariantTag(_)) => fact,
                    fact @ Fact::Outcomes(_) => fact,
                    _ => Fact::Unknown,
                },
                _ => Fact::Unknown,
            };
            state.registers.insert(result, fact);
            state.remember_read(result, &operation.operands[0], register_places);
        }
        OperationKind::ExtractPayloadIndirection | OperationKind::IsInitialized => {
            let Some(result) = operation.result_id() else {
                return;
            };
            state.registers.insert(result, Fact::Unknown);
        }
        // Derived immutable register-to-place bindings were discovered before the fixpoint.
        OperationKind::Subfield { .. }
        | OperationKind::AddressOffset { .. }
        | OperationKind::AddressOffsetPlace { .. } => {}
        OperationKind::Memcpy | OperationKind::Move | OperationKind::MoveBytes { .. } => {
            let source = place_of(&operation.operands[0]);
            let destination = place_of(&operation.operands[1]);
            let fact = match &source {
                Some(place) if tracked(*place) => state.place(*place),
                _ => Fact::Unknown,
            };
            if let Some(place) = destination
                && tracked(place)
            {
                state.set_place(place, fact, register_places);
            }
            // A move leaves its source moved-out; a memcpy preserves it.
            if matches!(
                operation.kind,
                OperationKind::Move | OperationKind::MoveBytes { .. }
            ) && let Some(place) = source
                && tracked(place)
            {
                state.set_place(place, Fact::Uninit, register_places);
            }
        }
        OperationKind::CompareEqual => {
            let Some(result) = operation.result_id() else {
                return;
            };
            // Operands are `[scrutinee, pattern]`, the scrutinee read non-consumingly — as a value,
            // or as the pointee of a place.
            let scrutinee = match place_of(&operation.operands[0]) {
                Some(place) if tracked(place) => state.place(place),
                Some(_) => Fact::Unknown,
                None => value_operand_fact(&operation.operands[0], func, state),
            };
            let outcomes = state.compare_outcomes(result, operation, &scrutinee, register_places);
            let fact =
                outcomes.unwrap_or_else(|| match (scrutinee.known(), &operation.operands[1]) {
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
                            Ok(equal) => {
                                Fact::Known(Const::Literal(LiteralValue::new_native(equal)))
                            }
                            Err(_) => Fact::Unknown,
                        }
                    }
                    _ => Fact::Unknown,
                });
            state.registers.insert(result, fact);
        }
        OperationKind::DictEntry { entry_index, .. } => {
            let Some(result) = operation.result_id() else {
                return;
            };
            // The entry of a *constant* dictionary is a statically known function — this is what
            // makes devirtualization fall out of inlining, once inlining has bound a callee's
            // dictionary parameter to a constant.
            let fact = static_evidence_operand(&operation.operands[0])
                .and_then(|evidence| dictionary_entry(&evidence, *entry_index, env))
                .map(|(function, hidden_evidence)| {
                    if hidden_evidence.is_empty() {
                        Fact::Known(Const::Function(function))
                    } else {
                        Fact::Known(Const::ClosedFunction {
                            function,
                            hidden_evidence,
                        })
                    }
                })
                .unwrap_or_default();
            let place = place_of(&mir::Value::Register(result))
                .expect("the structural scan interns every dictionary entry");
            state.forget_within(place, register_places);
            state.places.insert(place, fact);
        }
        OperationKind::Call { ty, .. } => {
            // The callee replaces its result slot. Only the type or adapter's result-domain
            // contract is known without evaluating it; no effects or operand laws follow.
            if let Some(call) = call_operands(&operation.operands, ty)
                && let Some(place) = place_of(call.result)
                && tracked(place)
            {
                let fact = match native_result_fact(&operation.operands[0], env) {
                    Fact::Unknown => type_fact(ty.ret(), env),
                    fact => fact,
                };
                state.set_place(place, fact, register_places);
            }
        }
        // A clone writes its destination through the callee, so that slot is unknown afterwards —
        // the same reasoning as a call's result place, which is what a clone was until it became an
        // operation of its own.
        OperationKind::Clone { .. } => {
            if let Some(place) = place_of(&operation.operands[1])
                && tracked(place)
            {
                state.set_place(place, Fact::Unknown, register_places);
            }
        }
        OperationKind::Drop { .. } => {
            if let Some(place) = place_of(&operation.operands[0])
                && tracked(place)
            {
                state.set_place(place, Fact::Uninit, register_places);
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
    dictionary: &mir::value::StaticEvidence,
    entry: TraitDictionaryEntryIndex,
    env: ModuleEnv<'_>,
) -> Option<(FunctionId, Vec<mir::value::StaticEvidence>)> {
    let mir::value::StaticEvidence::Dictionary {
        definition,
        captures,
    } = dictionary
    else {
        return None;
    };
    let module = env.module_by_id(definition.module_id)?;
    let dictionary_definition = &module.get_impl_data(definition.impl_id)?.dictionary_value;
    let TraitDictionaryEntry::Function(function) = dictionary_definition.entry(entry);
    let hidden_evidence =
        dictionary_definition.project_entry_captures(entry, captures, || dictionary.clone())?;
    Some((
        FunctionId {
            module: definition.module_id,
            function,
        },
        hidden_evidence,
    ))
}

fn static_evidence_operand(value: &mir::Value) -> Option<mir::value::StaticEvidence> {
    match value {
        mir::Value::Dictionary(definition) => {
            Some(mir::value::StaticEvidence::bare_dictionary(*definition))
        }
        mir::Value::Subscript(definition) => {
            Some(mir::value::StaticEvidence::bare_subscript(*definition))
        }
        mir::Value::Evidence(evidence) => Some((**evidence).clone()),
        _ => None,
    }
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
        mir::Value::Evidence(evidence) => Fact::Known(Const::Evidence((**evidence).clone())),
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
/// of a place escapes its root. A root also escapes if it is reached other than through an `alloca`,
/// a `runtime_alloc`, or a parameter — an operand this scan cannot resolve to a root escapes nothing
/// precisely because nothing was tracked for it in the first place.
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
    let mut place_builder = PlaceBuilder::new(func);
    for block_id in func.blocks() {
        for operation in func.block(block_id).operations() {
            match (&operation.kind, operation.result_id()) {
                (
                    OperationKind::Alloca { .. } | OperationKind::RuntimeAlloc { .. },
                    Some(result),
                ) => {
                    let place = place_builder.intern_root(Root::Alloca(result));
                    place_builder
                        .bindings
                        .registers
                        .insert(result, PlaceBinding::Exact(place));
                }
                (OperationKind::DictEntry { .. }, Some(result)) => {
                    let place = place_builder.intern_root(Root::DictEntry(result));
                    place_builder
                        .bindings
                        .registers
                        .insert(result, PlaceBinding::Exact(place));
                }
                (OperationKind::Subfield { .. }, Some(result)) => {
                    if let Some(root) = place_builder.bindings.root_of(&operation.operands[0]) {
                        let binding = match (
                            place_builder.bindings.place_of(&operation.operands[0]),
                            field_index(&operation.operands[1], func),
                        ) {
                            (Some(base), Some(index)) => {
                                PlaceBinding::Exact(place_builder.intern_field(base, index))
                            }
                            _ => PlaceBinding::Root(root),
                        };
                        place_builder.bindings.registers.insert(result, binding);
                    }
                }
                (
                    OperationKind::AddressOffset { .. } | OperationKind::AddressOffsetPlace { .. },
                    Some(result),
                ) => {
                    if let Some(root) = place_builder.bindings.root_of(&operation.operands[0]) {
                        place_builder
                            .bindings
                            .registers
                            .insert(result, PlaceBinding::Root(root));
                    }
                }
                _ => {}
            }
        }
    }
    let register_places = place_builder.finish();

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
            OperationKind::Alloca { .. } | OperationKind::RuntimeAlloc { .. } => {}
            // The operation consumes the address without exposing it elsewhere.
            OperationKind::RuntimeDealloc => {}
            // `comp_eq` borrows its scrutinee for a literal snapshot and never moves it, so the
            // place stays tracked; its second operand is compile-time pattern data.
            OperationKind::Load
            | OperationKind::Clear
            | OperationKind::CompareEqual
            | OperationKind::ExtractTag
            | OperationKind::ExtractPayloadIndirection
            | OperationKind::IsInitialized => {}
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
            // A byte offset has no semantic field identity. Stop tracking the complete allocation
            // rather than treating writes through the derived address as writes to an unrelated
            // logical field.
            OperationKind::AddressOffset { .. } | OperationKind::AddressOffsetPlace { .. } => {
                escape_operand(&operation.operands[0], escaped);
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
            // Source and destination ownership are modelled above; the remaining operand is a
            // materialized integer extent, not evidence or a place that can escape.
            OperationKind::MoveBytes { .. } => {}
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
            TerminatorKind::SwitchVariant { tag, .. } => escape_operand(tag, &mut escaped),
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

/// Returns the caller-provided result-place operand's index.
///
/// This is the allocation-free part of [`call_operands`]. Consumers that only classify the result
/// place should use it rather than constructing visible argument/convention pairs.
pub(crate) fn call_result_operand_index(
    operands: &[mir::Value],
    ty: &CallImplType,
) -> Option<usize> {
    let visible = ty.fn_ty.args.len();
    // callee + extras + args + ret
    let extras = operands.len().checked_sub(visible + 2)?;
    Some(1 + extras + visible)
}

pub(crate) fn call_operands<'a>(
    operands: &'a [mir::Value],
    ty: &CallImplType,
) -> Option<CallOperands<'a>> {
    let visible = ty.fn_ty.args.len();
    let result_index = call_result_operand_index(operands, ty)?;
    let extras = operands.len().checked_sub(visible + 2)?;
    let conventions = arg_conventions_for_args(&ty.fn_ty.args);
    Some(CallOperands {
        callee: &operands[0],
        extras: &operands[1..1 + extras],
        arguments: operands[1 + extras..1 + extras + visible]
            .iter()
            .zip(conventions)
            .collect(),
        result: &operands[result_index],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, ExecutionTarget, Location,
        compiler::MirOptimization,
        containers::b,
        hir::{native_functions::NativeFnNN, value::VariantPayloadStorage},
        mir::{Operation, builder::FunctionBuilder, terminator::Terminator},
        module::{Module, Path},
        std::math::int_type,
        types::{effects::no_effects, r#type::Type},
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
        assert_eq!(state.place(key), expected);
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
                    Type::unit(),
                    Some(VariantPayloadStorage::Inline),
                    None,
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
        assert!(
            analysis
                .register_places
                .places
                .iter()
                .any(|place| place.children.contains(&key)),
            "the subfield must be interned below its base place"
        );

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
        assert_eq!(state.place(source_key), Fact::Uninit);
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
            matches!(state.place(key), Fact::Known(Const::Function(_))),
            "an entry of a constant dictionary must resolve: {:?}",
            state.place(key)
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

    #[test]
    fn interned_places_share_paths_and_invalidate_only_the_written_subtree() {
        let mut builder = PlaceBuilder {
            bindings: PlaceBindings::default(),
            roots: FxHashMap::default(),
            fields: FxHashMap::default(),
        };
        let root = builder.intern_root(Root::Alloca(ValueId::from_index(0)));
        let field = builder.intern_field(root, ProjectionIndex::from_index(0));
        let same_field = builder.intern_field(root, ProjectionIndex::from_index(0));
        let nested = builder.intern_field(field, ProjectionIndex::from_index(0));
        let sibling = builder.intern_field(root, ProjectionIndex::from_index(1));
        assert_eq!(field, same_field, "identical paths must share one place id");
        let bindings = builder.finish();

        let known = |value| Fact::Known(Const::Literal(LiteralValue::new_native(value)));
        let mut state = State::default();
        state.places.insert(root, known(1isize));
        state.places.insert(field, known(2isize));
        state.places.insert(nested, known(3isize));
        state.places.insert(sibling, known(4isize));

        state.set_place(field, Fact::Uninit, &bindings);
        assert_eq!(state.place(root), known(1isize));
        assert_eq!(state.place(field), Fact::Uninit);
        assert!(!state.places.contains_key(&nested));
        assert_eq!(state.place(sibling), known(4isize));

        state.set_place(root, known(5isize), &bindings);
        assert_eq!(state.places.len(), 1);
        assert_eq!(state.place(root), known(5isize));
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
        assert_eq!(
            state.place(key),
            Fact::Outcomes([Outcome::Int(1), Outcome::Int(2)].into())
        );
    }

    // --- Finite outcome domains ---

    fn codes() -> Fact {
        Fact::from_outcomes(vec![Outcome::Int(-1), Outcome::Int(0), Outcome::Int(1)])
    }

    #[test]
    fn outcome_joins_are_bounded_unions() {
        let one = Fact::from_outcomes(vec![Outcome::Int(1)]);
        let zero = Fact::from_outcomes(vec![Outcome::Int(0)]);
        assert_eq!(
            one.join(&zero),
            Fact::Outcomes([Outcome::Int(0), Outcome::Int(1)].into())
        );
        assert_eq!(codes().join(&Fact::Unknown), Fact::Unknown);
        assert_eq!(codes().join(&Fact::Uninit), Fact::Unknown);
        let wide = (0..MAX_OUTCOMES as isize).map(Outcome::Int);
        assert_eq!(
            Fact::from_outcomes(wide).join(&Fact::from_outcomes(vec![Outcome::Int(99)])),
            Fact::Unknown
        );
    }

    #[test]
    fn outcome_predicates_do_not_follow_overwritten_storage() {
        let place = PlaceId::from_index(0);
        let slot = ValueId::from_index(0);
        let read = ValueId::from_index(1);
        let test = ValueId::from_index(2);
        let mut bindings = PlaceBindings::default();
        bindings.places.push(Place {
            root: Root::Alloca(slot),
            children: vec![],
            depth: 0,
        });
        bindings.registers.insert(slot, PlaceBinding::Exact(place));
        let mut state = State::default();
        state.places.insert(place, codes());
        state.registers.insert(read, codes());
        state.remember_read(read, &mir::Value::Register(slot), &bindings);
        state.tests.insert(
            test,
            EqualityTest {
                subject: Subject::Place(place),
                pattern: Outcome::Int(-1),
            },
        );
        let yes = BlockId::from_index(1);
        let no = BlockId::from_index(2);
        let branch = TerminatorKind::CondBr {
            condition: mir::Value::Register(test),
            then_target: yes,
            else_target: no,
        };
        assert_eq!(
            state.on_edge(&branch, no, &bindings).place(place),
            Fact::Outcomes([Outcome::Int(0), Outcome::Int(1)].into())
        );
        state.set_place(place, Fact::from_outcomes(vec![Outcome::Int(2)]), &bindings);
        assert!(state.tests.is_empty());
        assert!(state.origins.is_empty());
        assert_eq!(
            state.on_edge(&branch, yes, &bindings).place(place),
            Fact::from_outcomes(vec![Outcome::Int(2)])
        );
        // The old loaded value remains usable, but a test of it only refines that snapshot.
        state.tests.insert(
            test,
            EqualityTest {
                subject: Subject::Register(read),
                pattern: Outcome::Int(-1),
            },
        );
        let edge = state.on_edge(&branch, yes, &bindings);
        assert_eq!(
            edge.registers[&read],
            Fact::from_outcomes(vec![Outcome::Int(-1)])
        );
        assert_eq!(
            edge.place(place),
            Fact::from_outcomes(vec![Outcome::Int(2)])
        );
        // Re-executing a register definition in a loop invalidates tests of its previous value.
        state.invalidate_subjects(|subject| subject == Subject::Register(read));
        assert!(state.tests.is_empty());
    }

    #[test]
    fn impossible_restrictions_preserve_facts_at_joins() {
        let place = PlaceId::from_index(0);
        let read = ValueId::from_index(1);
        let less = Outcome::Tag(ustr::ustr("Less"));
        let fact = Fact::from_outcomes([less]);
        let mut state = State::default();
        state.places.insert(place, fact.clone());
        state.registers.insert(read, fact.clone());
        state.origins.insert(read, Subject::Place(place));
        let mut impossible = state.clone();
        impossible.restrict(Subject::Place(place), |value| *value != less);
        assert_eq!(impossible, state);
        assert_eq!(state.join(&impossible).place(place), fact);
        assert_eq!(state.join(&impossible).register(read), Some(&fact));
    }

    #[test]
    fn untracked_subjects_do_not_clobber_materialized_facts() {
        let place = PlaceId::from_index(0);
        let read = ValueId::from_index(1);
        let mut state = State::default();
        state.registers.insert(read, codes());
        state.origins.insert(read, Subject::Place(place));
        let original = state.clone();
        state.restrict(Subject::Place(place), |_| true);
        assert_eq!(state, original);
        state.places.insert(place, Fact::Unknown);
        state.restrict(Subject::Place(place), |_| true);
        assert_eq!(state.register(read), Some(&codes()));
    }

    fn host_session() -> CompilerSession {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let path = Path::single_str("host_ordering");
        let mut host = Module::new(session.modules().next_id(), path.clone());
        // Deliberately not a std identity, and ordered in the opposite direction.
        let compare = host.add_function(
            ustr::ustr("compare"),
            NativeFnNN::from_rust_ordering_code(|a: isize, b: isize| b.cmp(&a)).description(
                ["a", "b"],
                "Host comparison",
                no_effects(),
            ),
        );
        host.add_function(
            ustr::ustr("ordinary"),
            NativeFnNN::from_rust(isize::wrapping_sub).description(
                ["a", "b"],
                "Unrestricted result",
                no_effects(),
            ),
        );
        let mut copied_description = NativeFnNN::from_rust(isize::wrapping_sub).description(
            ["a", "b"],
            "Copied description",
            no_effects(),
        );
        copied_description.definition =
            host.get_function_by_id(compare).unwrap().definition.clone();
        host.add_function(ustr::ustr("copied_description"), copied_description);
        host.add_function(
            ustr::ustr("not_reflexive"),
            NativeFnNN::from_rust_ordering_code(|_: isize, _: isize| std::cmp::Ordering::Less)
                .description(["a", "b"], "No ordering laws", no_effects()),
        );
        let id = session.register_module(path, host);
        assert!(
            session
                .known_callees()
                .resolve(
                    FunctionId {
                        module: id,
                        function: compare
                    },
                    |_| None
                )
                .is_none()
        );
        session
    }

    fn optimized(session: &mut CompilerSession, source: &str) -> String {
        let id = session
            .compile_for(
                ExecutionTarget::Mir,
                source,
                "outcomes",
                Path::single_str("outcomes"),
            )
            .expect("comparison fixture compiles")
            .module_id;
        session.emit_mir_module(id)
    }

    #[test]
    fn host_ordering_metadata_eliminates_impossible_code_cases() {
        let mut session = host_session();
        let body = optimized(
            &mut session,
            "fn classify(a: int, b: int) -> int {
            match host_ordering::compare(a, b) { -1 => 10, 0 => 20, 1 => 30, _ => 987654 }
        }",
        );
        assert!(
            body.contains("call host_ordering::compare"),
            "the opaque call remains:\n{body}"
        );
        assert!(
            !body.contains("987654"),
            "only the impossible result arm disappears:\n{body}"
        );

        let body = optimized(
            &mut session,
            "fn classify(a: int, b: int) -> int {
            match host_ordering::ordinary(a, b) { -1 => 10, 0 => 20, 1 => 30, _ => 987654 }
        }",
        );
        assert!(
            body.contains("987654"),
            "ordinary integer results remain unrestricted:\n{body}"
        );
        let body = optimized(&mut session, "fn classify(a: int, b: int) -> int {
            match host_ordering::copied_description(a, b) { -1 => 10, 0 => 20, 1 => 30, _ => 987654 }
        }");
        assert!(
            body.contains("987654"),
            "a copied description cannot confer the adapter's guarantee:\n{body}"
        );
    }

    #[test]
    fn semantic_ordering_outcomes_do_not_depend_on_the_producer() {
        let mut session = host_session();
        let body = optimized(
            &mut session,
            "fn classify(value: Ordering) -> int {
            match value { Less => 10, _ => match value { Less => 987654, _ => 20 } }
        }",
        );
        assert!(
            !body.contains("987654"),
            "an excluded variant remains excluded:\n{body}"
        );
    }

    #[test]
    fn host_ordering_wrappers_inline_without_assuming_ordering_laws() {
        let mut session = host_session();
        let source = "fn ordering(code: int) -> Ordering {
            match code { -1 => Less, 0 => Equal, _ => Greater }
        }
        fn compare(a: int, b: int) -> Ordering { ordering(host_ordering::compare(a, b)) }
        fn below(a: int, b: int) -> bool { match compare(a, b) { Less => true, _ => false } }
        fn reflexive(a: int) -> Ordering { ordering(host_ordering::not_reflexive(a, a)) }
        fn main() { (below(9, 2), below(2, 9), below(3, 3), reflexive(5)) }";
        let body = optimized(&mut session, source);
        let below = body
            .split("fn below(")
            .nth(1)
            .unwrap()
            .split("\nfn ")
            .next()
            .unwrap();
        assert!(below.contains("call host_ordering::compare"), "{below}");
        assert!(
            !below.contains("extract_tag") && !below.contains("variant "),
            "no temporary Ordering is needed:\n{below}"
        );
        let optimized = session.eval_mir("run_optimized_outcomes", source);
        session.set_mir_optimization(MirOptimization::Disabled);
        let raw = session.eval_mir("run_raw_outcomes", source);
        assert_eq!(optimized, raw);
        assert_eq!(optimized, "(true, false, false, Less)");
    }
}
