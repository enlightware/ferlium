// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Specializing a generic MIR body at one call site's instantiation.
//!
//! A generic function is compiled once, its type parameters left as quantified variables and its
//! trait constraints turned into hidden dictionary parameters. Generated impl thunks can likewise
//! be type-monomorphic while still abstract over captured dictionaries. Specializing either form
//! has two halves — substituting the types and binding the dictionaries — and **they must be applied
//! together**. A
//! body with only its dictionaries bound says `int` in its evidence and `A` in its types; that is
//! latent while nothing acts on it, but the moment folding uses the now-resolved `dict_entry` it
//! evaluates a call at the concrete instantiation and has nowhere type-correct to put the result.
//!
//! [`specialize`] therefore applies both, inside a single edit: the incoherent intermediate is
//! never a `Function` at all, so no caller can be handed one and nothing verifies one.
//!
//! Substitution composes down the call graph without anything reasoning about nesting, because a
//! call's recorded instantiation is written in the *containing* function's type environment.
//! Substituting `forwarding<U>` at `U := int` rewrites its inner call's recorded `[U]` into
//! `[int]`, so a call that was generic becomes concrete. See `doc/generic-instantiation.md`.
//!
//! Binding a dictionary parameter replaces its *uses* and leaves the parameter itself in place, so
//! **a specialization has no live evidence parameter by construction** — a property this file's
//! tests assert. The dead parameters survive this phase and are removed from the finished module by
//! [`dead_evidence`](super::dead_evidence), after every optimization decision has been taken
//! against the signatures the optimizer has always seen.
//!
//! What the specialization keeps unchanged is its original's *visible* signature, which is what
//! every HIR-table lookup the interpreter makes on a call — `code.as_script()`,
//! `return_convention()`, `parameter_passing` — is answered from.
//!
//! Exercised only by its own tests until the specialization pass consumes it; remove the allow
//! below then, as `const_eval.rs` did when folding started calling it.
#![allow(dead_code)]

use std::{
    borrow::Cow,
    cell::{Cell, Ref, RefCell},
    hash::{Hash, Hasher},
    mem,
};

use rustc_hash::{FxHashMap, FxHashSet, FxHasher};
use ustr::{Ustr, ustr};

use super::{
    OptimizationStats, budget, cost,
    dataflow::{self, Analysis, Const, State},
    site::{OperationIndex, OperationSite},
    stage::SemanticCallees,
};
use crate::{
    CompilerSession,
    compiler::Specialization,
    format::FormatWith,
    hir::function::ArgConvention,
    mir::{
        self, Function, Instantiation, Operation, OperationKind, ParameterId, ParameterKind,
        ValueId,
        debug_location::InlineRebase,
        edit::FunctionEdit,
        operation::SourceFallibility,
        role::MirType,
        terminator::{Terminator, TerminatorKind, TerminatorKindDiscriminant},
        value::StaticEvidence,
    },
    module::{
        FunctionId, LocalFunctionId, ModuleEnv, ModuleId, id::Id, stable_generated_name_hash,
        unique_generated_name,
    },
    std::value::{dynamic_product_member_layouts, type_has_static_layout},
    types::{
        effects::{EffType, Effect, PrimitiveEffect},
        r#type::Type,
        type_like::TypeLike,
        type_mapper::{BitmapInstantiationMapper, TypeMapper},
        type_properties::concrete_type_is_trivial_copy,
        type_scheme::TypeScheme,
    },
};

// Sharing one residual body between the keys that produce it.
//
// Specialization keys are finer than the bodies they produce. Type arguments, effect arguments and
// evidence all enter the key, but only what survives substitution enters the *body*: effects are
// erased from MIR unless they changed a control-flow form, and a dictionary appears only where it
// was used. Two call sites that instantiate a generic callee differently can therefore ask for
// residual MIR that is the same function, and `iter_pipeline` is full of them — ten copies of
// `MapIterator::next` separated by nothing but caller-local effect variables.
//
// Comparing the residual body itself is what keeps a distinction exactly when it makes a
// difference. It needs no rule about which parts of a key may be ignored, and it cannot be wrong
// about one: a distinction that reaches the MIR keeps the copies apart by construction.
//
// Everything a caller can observe takes part — the calling convention, the parameters, the constant
// pool and the code — and only two things do not:
//
// - the generated *name*, which is derived from the key and so differs whenever the key does;
// - the body's own *function id*, which a recursive specialization names in its self-calls.
//
// Both are properties of which copy this is rather than of what it computes, which is precisely
// what must not distinguish two copies. The original takes part because a specialization's HIR
// metadata is answered through `Specialization::original` rather than held by the copy: two
// originals with identical residual MIR can still declare different parameter passing or return
// conventions, so bodies are shared within one original and never across two.
//
// Neither function below copies or rewrites anything: both walk the bodies as they stand and
// substitute a self-reference as they go, `structure_digest` while hashing one and
// `structurally_identical` while comparing two.

/// The identity a self-reference is normalized to.
///
/// Far past any dense function table: `LocalFunctionId` is a `u32` index into one, and `u32::MAX`
/// itself is reserved as `Option`'s niche.
const SELF_REFERENCE: LocalFunctionId = LocalFunctionId::new(u32::MAX - 1);

/// How a body's function references are read while deciding what body it is.
///
/// A copy names *itself* by its own id, which is the one thing that must not distinguish it from
/// another copy, so `own` maps to [`SELF_REFERENCE`]. Sharing bodies after they are optimized adds
/// the only other reason to canonicalize — a reference to a copy already merged away has to read as
/// the copy it was merged into — so [`share_specializations`](super::share_specializations)
/// composes that mapping with this one.
pub(super) fn self_reference(own: FunctionId) -> impl Fn(FunctionId) -> FunctionId {
    move |id| {
        if id == own {
            FunctionId {
                module: own.module,
                function: SELF_REFERENCE,
            }
        } else {
            id
        }
    }
}

/// Hashes what makes `body` — a specialization of `original` — the function it is, rather than the
/// copy it is.
///
/// Everything is hashed through its derived implementation except the operands, which are the one
/// place `canonical` has anything to say: [`resolve_recursion`] writes a self-reference into call
/// callee operands and nowhere else. So only calls are decomposed, and a block's other terminator
/// forms hash whole.
///
/// A function named by an operation *kind* rather than an operand — `build_closure` alone — is
/// hashed raw, so two copies naming two merged-away callees there simply fail to be recognized.
/// That is the safe direction, and today an unreachable one: nothing ever writes a specialization
/// into a `build_closure`.
///
/// This is a filter and never the decision — [`structurally_identical`] decides — so an imprecise
/// hash costs a sharing rather than merging two bodies that differ.
pub(super) fn structure_digest(
    body: &Function,
    original: FunctionId,
    canonical: &impl Fn(FunctionId) -> FunctionId,
) -> u64 {
    let mut state = FxHasher::default();
    original.hash(&mut state);
    body.result_convention().hash(&mut state);
    body.parameters().hash(&mut state);
    body.constants().hash(&mut state);
    // Lengths are hashed alongside the sequences they precede, as a derived slice hash would do:
    // without them two bodies whose operations merely start alike collide, and a collision here
    // costs a sharing.
    body.blocks().count().hash(&mut state);
    for block_id in body.blocks() {
        let block = body.block(block_id);
        block.operations().len().hash(&mut state);
        for operation in block.operations() {
            hash_operation(operation, canonical, &mut state);
        }
        let terminator = block.terminator();
        terminator.span.hash(&mut state);
        TerminatorKindDiscriminant::from(&terminator.kind).hash(&mut state);
        match &terminator.kind {
            TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } => {
                hash_operation(operation, canonical, &mut state);
                normal.hash(&mut state);
                error.hash(&mut state);
            }
            // Derived, because no other form carries a function operand to normalize: a condition
            // is a boolean and a yielded place is a place. One that later did would hash its raw
            // operand and fail to recognize a sharing, never invent one.
            kind => kind.hash(&mut state),
        }
    }
    state.finish()
}

/// Hashes one operation with its function references read through `canonical`.
fn hash_operation(
    operation: &Operation,
    canonical: &impl Fn(FunctionId) -> FunctionId,
    state: &mut impl Hasher,
) {
    operation.result_id().hash(state);
    operation.span.hash(state);
    operation.kind.hash(state);
    operation.operands.len().hash(state);
    for operand in &operation.operands {
        normalize_function(operand, canonical).hash(state);
    }
}

/// `operand` with any function it names read through `canonical`.
fn normalize_function(
    operand: &mir::Value,
    canonical: &impl Fn(FunctionId) -> FunctionId,
) -> mir::Value {
    match operand {
        mir::Value::Function(id) => mir::Value::Function(canonical(*id)),
        operand => operand.clone(),
    }
}

/// Whether `body`, read through `canonical`, is the same function as `existing` read through
/// `existing_canonical`.
///
/// The two mappings are separate because each body names itself by its own id. Everything outside
/// the operands is compared by the derived equality — including the code, which
/// [`Operation::eq_by_operands`] destructures exhaustively so that a field added to MIR later
/// cannot silently drop out of a decision that two bodies are interchangeable.
///
/// The name is excluded, because two copies of one function are generated under different names by
/// construction: that is exactly what the name records.
pub(super) fn structurally_identical(
    body: &Function,
    canonical: &impl Fn(FunctionId) -> FunctionId,
    existing: &Function,
    existing_canonical: &impl Fn(FunctionId) -> FunctionId,
) -> bool {
    let operand_eq = |operand: &mir::Value, other: &mir::Value| {
        normalize_function(operand, canonical) == normalize_function(other, existing_canonical)
    };
    body.result_convention() == existing.result_convention()
        && body.parameters() == existing.parameters()
        && body.constants() == existing.constants()
        && body.blocks().count() == existing.blocks().count()
        && body.blocks().zip(existing.blocks()).all(|(own, other)| {
            let own = body.block(own);
            let other = existing.block(other);
            own.operations().len() == other.operations().len()
                && own
                    .operations()
                    .iter()
                    .zip(other.operations())
                    .all(|(operation, other)| operation.eq_by_operands(other, &operand_eq))
                && own
                    .terminator()
                    .eq_by_operands(other.terminator(), &operand_eq)
        })
}

/// Where a specialization's optimization stands.
///
/// A specialization is a callee found while optimizing its caller. Like a declared callee, it is
/// optimized before its callers read it whenever its inputs allow: created from a final body — a
/// dependency's or a finished component's — it is optimized as soon as a caller is about to read
/// it, and callers then read the optimized body. Its result must not depend on when it was
/// computed, so it is kept only if every body its optimization read was final too: a dependency's,
/// a finished one, the raw body of a specialization that will never be optimized ahead, or an
/// optimized one. Reading anything else — a declared function still being optimized, reached
/// through a dictionary, or a specialization being optimized, which is a cycle discovered while
/// optimizing — leaves the specialization to the worklist, as a recursive component reads its own
/// members raw.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Progress {
    /// Created from a body that was not final; read raw, optimized by the worklist.
    Deferred,
    /// Created from a final body; to be optimized before a caller reads it.
    Ready,
    /// Being optimized ahead of the worklist.
    Optimizing,
    /// Optimized ahead of the worklist; callers read the optimized body.
    Optimized,
    /// Its optimization ahead of the worklist read a body that was not final, so it was
    /// discarded; read raw, optimized by the worklist.
    Unsettled,
}

/// What [`Specializations::begin_ahead`] saved of an enclosing optimization ahead of the worklist.
pub(crate) struct AheadFrame {
    ahead: Option<LocalFunctionId>,
    read_unsettled: bool,
}

/// How one call site instantiates a generic callee: both halves of the instantiation, together.
///
/// This is the specialization cache's key, and pairing the two here is the same discipline
/// [`specialize`] enforces — a key naming only the dictionaries would give two call sites that bind
/// the same evidence at different types the same specialization, which is precisely the incoherence
/// this phase exists to avoid.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct SpecializationKey {
    pub(crate) callee: FunctionId,
    pub(crate) instantiation: Instantiation,
    pub(crate) dictionaries: Vec<StaticEvidence>,
    /// Immutable visible parameters bound to bare function values.
    pub(crate) callbacks: Vec<(ParameterId, FunctionId)>,
}

/// Cumulative callback-copy cost for one type/evidence family. Neither publication nor
/// generated output changes the allowance established from its first source body.
#[derive(Default)]
struct CallbackGrowth {
    allowance: usize,
    spent: usize,
    last_admitted: Option<usize>,
}

/// The specializations one module's optimization has created, and the caches that keep them shared.
///
/// Two call sites that instantiate a generic function the same way get the same body rather than a
/// copy each. Without that, a generic function called `n` times would be copied `n` times, which is
/// how naive specialization explodes.
///
/// Sharing is decided twice, because a key is finer than the body it produces. The key cache
/// answers a repeated call site outright; [`BodyStructure`] then catches a *new* key whose residual
/// MIR turns out to be a function already created — the copies that keying alone cannot see,
/// because recognizing them means substituting first.
#[derive(Default)]
pub(crate) struct Specializations {
    /// The module whose optimized artifacts will hold these, which is not in general the module a
    /// specialized callee came from: the identities below index *this* module's table.
    module: ModuleId,
    /// This module's declared functions whose component has been optimized, callees first.
    ///
    /// A component is published only once all its members are done, so a body read here never
    /// depends on the order within a recursive component, which reads its own members raw.
    finished: Vec<Option<Function>>,
    created: Vec<Specialization>,
    /// Each specialization as it was created, before it was optimized.
    ///
    /// This is a specialization's *raw* stage, and it exists for the same reason the raw stage does:
    /// a pass that consults a callee's body must get the same answer whatever order functions are
    /// optimized in. `created` is mutated in place as the worklist reaches each entry, so reading it
    /// would make an inlining decision depend on whether that had happened yet; only a body
    /// optimized ahead of the worklist is read from it (see [`Progress`]).
    raw: Vec<Function>,
    cache: FxHashMap<SpecializationKey, LocalFunctionId>,
    /// Digests of the residual bodies already created, so that keys whose distinctions vanish under
    /// substitution share one copy.
    ///
    /// Indexed by digest rather than by the structure itself so that the table stores no second
    /// copy of every specialized body — the bodies are already in `raw`, which is what a candidate
    /// is confirmed against. See [`BodyStructure`].
    structures: FxHashMap<u64, LocalFunctionId>,
    /// Keys whose callee bodies expose none of the payoffs specialization can currently realize.
    ///
    /// A rejected key can occur at many call sites. Remembering it keeps the admission scan linear
    /// in the number of distinct candidates rather than in candidate call sites times body size.
    rejected: FxHashSet<SpecializationKey>,
    /// Callback descriptors for the callee body currently visible to this table. Publication
    /// invalidates raw-body entries along with the other admission and substitution caches.
    callback_parameters: RefCell<FxHashMap<FunctionId, FxHashSet<ParameterId>>>,
    /// Bodies produced by substituting a generic callee at a call site's instantiation, memoized
    /// for the duration of one module's optimization.
    ///
    /// Unlike `cache`, this keeps no function: an inlined body is spliced and then discarded, so
    /// the entry exists only so that the same `(callee, instantiation)` pair is not substituted —
    /// and re-verified — once per call site, per round, per caller. `array_index` at `[int]`
    /// produces one body however many array accesses a module has.
    ///
    /// Interior mutability because the inliner's planner holds this by shared reference, and a memo
    /// that changes no answer is exactly what that is for.
    substituted: RefCell<FxHashMap<(FunctionId, Instantiation), Function>>,
    /// Where each specialization stands, aligned with `created`.
    progress: Vec<Progress>,
    /// How many specializations are [`Progress::Ready`], so a caller with none to optimize pays
    /// no scan.
    ready: usize,
    /// The specialization being optimized ahead of the worklist, if any.
    ahead: Option<LocalFunctionId>,
    /// Whether that optimization has read a body that is not final yet; see [`Progress`].
    read_unsettled: Cell<bool>,
    /// What the specializations optimized ahead of the worklist and kept counted.
    kept_ahead_stats: OptimizationStats,
    /// Where the module's HIR-declared functions end; specializations are numbered from here.
    first_index: usize,
    /// Fixed from the module's declared MIR-body population before any output is generated.
    limit: usize,
    /// Unique callback-bound bodies created, including work later pruned or published.
    callback_created: usize,
    callback_limit: usize,
    callback_growth: FxHashMap<SpecializationKey, CallbackGrowth>,
}

impl Specializations {
    /// Starts an empty table for `module`, whose HIR function table has `function_count` entries
    /// and `declared_body_count` script bodies.
    pub(crate) fn new(module: ModuleId, function_count: usize, declared_body_count: usize) -> Self {
        Self {
            module,
            finished: vec![None; function_count],
            created: Vec::new(),
            raw: Vec::new(),
            cache: FxHashMap::default(),
            structures: FxHashMap::default(),
            rejected: FxHashSet::default(),
            callback_parameters: RefCell::new(FxHashMap::default()),
            substituted: RefCell::new(FxHashMap::default()),
            progress: Vec::new(),
            ready: 0,
            ahead: None,
            read_unsettled: Cell::new(false),
            kept_ahead_stats: OptimizationStats::default(),
            first_index: function_count,
            limit: budget::specialization_limit(declared_body_count),
            callback_created: 0,
            callback_limit: budget::callback_specialization_limit(declared_body_count),
            callback_growth: FxHashMap::default(),
        }
    }

    /// The module being optimized, whose table this is.
    pub(crate) fn module(&self) -> ModuleId {
        self.module
    }

    /// The optimized body of a declared function of this module, once its component is finished.
    pub(crate) fn finished_body(&self, id: LocalFunctionId) -> Option<&Function> {
        self.finished.get(id.as_index())?.as_ref()
    }

    /// Publishes the optimized bodies of one component of the call graph.
    pub(crate) fn finish(&mut self, bodies: Vec<(LocalFunctionId, Function)>) {
        // What was decided or copied from a member's raw body must not outlive its publication.
        // Specializations already created stay; later call sites copy the optimized body.
        let module = self.module;
        let raw = |callee: &FunctionId| {
            callee.module == module && bodies.iter().any(|(id, _)| *id == callee.function)
        };
        self.substituted
            .get_mut()
            .retain(|(callee, _), _| !raw(callee));
        self.cache.retain(|key, _| !raw(&key.callee));
        self.rejected.retain(|key| !raw(&key.callee));
        self.callback_parameters
            .get_mut()
            .retain(|callee, _| !raw(callee));
        for (id, body) in bodies {
            self.finished[id.as_index()] = Some(body);
        }
    }

    /// The optimized declared bodies, aligned with the module's function table.
    pub(crate) fn take_finished(&mut self) -> Vec<Option<Function>> {
        mem::take(&mut self.finished)
    }

    /// Inspect each visible callee body once, shared across callers and optimization rounds.
    fn invoked_callbacks(
        &self,
        callee: FunctionId,
        session: &CompilerSession,
    ) -> Option<Ref<'_, FxHashSet<ParameterId>>> {
        // A cached raw summary is still a dependency on an unfinished callee, even when it
        // finds no opportunity. Publication can expose an invocation through inlining.
        if callee.module == self.module && self.finished_body(callee.function).is_none() {
            self.note_unsettled();
        }
        if !self.callback_parameters.borrow().contains_key(&callee) {
            let body = SemanticCallees::new(session, Some(self)).body(callee)?;
            self.callback_parameters
                .borrow_mut()
                .insert(callee, repeated_callback_parameters(body, callee));
        }
        Some(Ref::map(self.callback_parameters.borrow(), |parameters| {
            &parameters[&callee]
        }))
    }

    pub(crate) fn into_created(self) -> Vec<Specialization> {
        self.created
    }

    pub(crate) fn len(&self) -> usize {
        self.created.len()
    }

    /// Whether this module has consumed its input-relative specialization allowance.
    pub(crate) fn is_full(&self) -> bool {
        self.created.len() >= self.limit
    }

    fn callbacks_full(&self) -> bool {
        self.callback_created >= self.callback_limit
    }

    /// Whether `id` names a specialization this table created.
    ///
    /// Takes a whole [`FunctionId`], because the local index alone is meaningless: it addresses
    /// *this* module's table, and another module's ordinary function can share it.
    pub(crate) fn is_specialization(&self, id: FunctionId) -> bool {
        id.module == self.module && id.function.as_index() >= self.first_index
    }

    /// The source function whose body `id` specializes.
    pub(crate) fn original(&self, id: FunctionId) -> Option<FunctionId> {
        self.is_specialization(id)
            .then(|| self.created.get(id.function.as_index() - self.first_index))
            .flatten()
            .map(|specialization| specialization.original)
    }

    /// The body of a specialization this table created.
    pub(crate) fn body(&self, id: LocalFunctionId) -> Option<&Function> {
        Some(&self.created.get(id.as_index() - self.first_index)?.body)
    }

    /// The body of a specialization that a pass consulting it as a callee reads.
    ///
    /// Optimized once it was optimized ahead of the worklist, and raw otherwise, so that a
    /// decision never depends on how far the worklist has got. Reading a raw body that will later
    /// be optimized ahead, or one being optimized, is recorded against the specialization being
    /// optimized ahead, whose result then depends on when it was computed.
    pub(crate) fn callee_body(&self, id: LocalFunctionId) -> Option<&Function> {
        let index = id.as_index().checked_sub(self.first_index)?;
        match self.progress.get(index)? {
            Progress::Optimized => return Some(&self.created[index].body),
            Progress::Deferred => {}
            // Its own body, which a recursive specialization reads to refuse inlining itself, is
            // the same raw body whenever it is read.
            Progress::Optimizing if self.ahead == Some(id) => {}
            Progress::Ready | Progress::Optimizing | Progress::Unsettled => self.note_unsettled(),
        }
        self.raw.get(index)
    }

    /// Records that the specialization being optimized ahead, if any, read a body that is not
    /// final yet.
    pub(crate) fn note_unsettled(&self) {
        self.read_unsettled.set(true);
    }

    /// Whether the specialization being optimized ahead of the worklist has read a body that is
    /// not final, so that its result will be discarded.
    pub(crate) fn abandons_ahead(&self) -> bool {
        self.ahead.is_some() && self.read_unsettled.get()
    }

    /// Whether some specialization waits to be optimized before its first caller reads it.
    pub(crate) fn has_ready(&self) -> bool {
        self.ready > 0
    }

    /// Whether `id` is a specialization waiting to be optimized before its first caller reads it.
    pub(crate) fn is_ready(&self, id: FunctionId) -> bool {
        self.is_specialization(id)
            && self.progress.get(id.function.as_index() - self.first_index)
                == Some(&Progress::Ready)
    }

    /// Starts optimizing the ready specialization `id` ahead of the worklist, returning its raw
    /// body and what [`Self::end_ahead`] restores.
    pub(crate) fn begin_ahead(&mut self, id: LocalFunctionId) -> (Function, AheadFrame) {
        let index = id.as_index() - self.first_index;
        debug_assert_eq!(self.progress[index], Progress::Ready);
        self.progress[index] = Progress::Optimizing;
        self.ready -= 1;
        let frame = AheadFrame {
            ahead: self.ahead.replace(id),
            read_unsettled: self.read_unsettled.replace(false),
        };
        (self.raw[index].clone(), frame)
    }

    /// Ends optimizing `id` ahead of the worklist, which counted `stats`. The result is kept only
    /// when every body the optimization read was final, and returns whether it was.
    pub(crate) fn end_ahead(
        &mut self,
        id: LocalFunctionId,
        optimized: Function,
        frame: AheadFrame,
        stats: OptimizationStats,
    ) -> bool {
        let index = id.as_index() - self.first_index;
        let settled = !self.read_unsettled.get();
        if settled {
            self.created[index].body = optimized;
            self.progress[index] = Progress::Optimized;
            self.kept_ahead_stats.add(stats);
        } else {
            self.progress[index] = Progress::Unsettled;
        }
        self.ahead = frame.ahead;
        self.read_unsettled.set(frame.read_unsettled);
        settled
    }

    /// What the specializations optimized ahead of the worklist and kept counted; the worklist
    /// counts the others.
    pub(crate) fn kept_ahead_stats(&self) -> OptimizationStats {
        self.kept_ahead_stats
    }

    /// Whether the worklist still has to optimize `id`.
    pub(crate) fn needs_worklist(&self, id: LocalFunctionId) -> bool {
        self.progress[id.as_index() - self.first_index] != Progress::Optimized
    }

    /// Replaces the body of a specialization this table created, after optimizing it.
    pub(crate) fn set_body(&mut self, id: LocalFunctionId, body: Function) {
        let index = id.as_index() - self.first_index;
        self.created[index].body = body;
    }

    /// A specialization already admitted for `key`, so another call site needs no scan or budget.
    ///
    /// Never a deferred specialization of a callee now finished: [`Self::finish`] drops the keys
    /// of the callees it publishes, so a later call site creates one from the optimized body.
    pub(crate) fn cached(&self, key: &SpecializationKey) -> Option<LocalFunctionId> {
        let id = self.cache.get(key).copied()?;
        debug_assert!(
            !(self.progress[id.as_index() - self.first_index] == Progress::Deferred
                && (key.callee.module != self.module
                    || self.finished_body(key.callee.function).is_some())),
            "a cached key names a deferred specialization of a finished callee"
        );
        Some(id)
    }

    /// Whether the admission scan already found no specialization payoff for `key`.
    pub(crate) fn is_rejected(&self, key: &SpecializationKey) -> bool {
        self.rejected.contains(key)
    }

    /// Records that `key` exposes no specialization payoff in its callee body.
    pub(crate) fn reject(&mut self, key: SpecializationKey) {
        self.rejected.insert(key);
    }

    /// The local id of the specialization for `key`, creating it if this is the first call site to
    /// ask for a body like the one it produces.
    ///
    /// Two lookups, because a key is finer than the body it produces. The key cache answers a call
    /// site that has been seen before without substituting anything; the structural digest answers a
    /// *new* key whose residual MIR turns out to be one already created, which needs the body built
    /// to be recognized. Both lookups map to the retained copy, so later call sites take the cheap
    /// path. Ordinary type/evidence construction cannot be refused.
    pub(crate) fn get_or_create<Ty: TypeLike>(
        &mut self,
        key: SpecializationKey,
        scheme: &TypeScheme<Ty>,
        body: &Function,
        env: ModuleEnv<'_>,
    ) -> LocalFunctionId {
        debug_assert!(key.callbacks.is_empty());
        self.create(key, scheme, body, env)
            .expect("type/evidence copies do not spend callback growth")
    }

    /// A conservative preflight for novel callback keys. A different binding or published body
    /// can be cheaper than the last admitted copy; declining it only misses an optimization.
    fn callback_growth_allows(&self, key: &SpecializationKey) -> bool {
        let mut family = key.clone();
        family.callbacks.clear();
        self.callback_growth.get(&family).is_none_or(|growth| {
            growth
                .last_admitted
                .is_none_or(|cost| cost <= growth.allowance.saturating_sub(growth.spent))
        })
    }

    /// Callback-only admission retains an exact check after conservative preflight.
    fn get_or_create_callback<Ty: TypeLike>(
        &mut self,
        key: SpecializationKey,
        scheme: &TypeScheme<Ty>,
        body: &Function,
        env: ModuleEnv<'_>,
    ) -> Option<LocalFunctionId> {
        debug_assert!(!key.callbacks.is_empty());
        if let Some(existing) = self.cached(&key) {
            return Some(existing);
        }
        if !self.callback_growth_allows(&key) {
            self.reject(key);
            return None;
        }
        self.create(key, scheme, body, env)
    }

    fn create<Ty: TypeLike>(
        &mut self,
        key: SpecializationKey,
        scheme: &TypeScheme<Ty>,
        body: &Function,
        env: ModuleEnv<'_>,
    ) -> Option<LocalFunctionId> {
        if let Some(existing) = self.cache.get(&key) {
            return Some(*existing);
        }
        // Allocated before the body is built, because a recursive callee has to be able to name
        // itself: see `resolve_recursion`. Nothing consumes it until the body proves to be new, so
        // a duplicate leaves the id to whichever specialization is created next.
        let id = LocalFunctionId::from_index(self.first_index + self.created.len());
        let own = FunctionId {
            module: self.module,
            function: id,
        };
        let specialized = specialize(body, scheme, &key, own, env);
        // Source locations participate in structural identity; candidates and retained copies
        // must use the same inline-site table before comparing. Interning deduplicates moves.
        let specialized = move_inline_sites(specialized, key.callee.module, self.module, env);

        // Final exactly when the body read to create it was: a dependency's or a finished one.
        let from_final =
            key.callee.module != self.module || self.finished_body(key.callee.function).is_some();
        let digest = structure_digest(&specialized, key.callee, &self_reference(own));
        if let Some(existing) = self.identical_to(&specialized, key.callee, own, digest, from_final)
        {
            self.cache.insert(key, existing);
            return Some(existing);
        }

        // Charge the complete residual body, including cold paths and callback materialization,
        // before it enters the optimization worklist. Equivalent bodies above consume no growth.
        let callback_charge = if key.callbacks.is_empty() {
            None
        } else {
            let mut family = key.clone();
            family.callbacks.clear();
            let growth = self
                .callback_growth
                .entry(family.clone())
                .or_insert_with(|| CallbackGrowth {
                    allowance: budget::callback_growth_limit(cost::cost(body)),
                    spent: 0,
                    last_admitted: None,
                });
            let copied = cost::cost(&specialized);
            if copied > growth.allowance.saturating_sub(growth.spent) {
                self.reject(key);
                return None;
            }
            Some((family, copied))
        };

        // Named only now that there is a copy to name. `name_for` scans every name created so far
        // to keep generated names unique, which is work a duplicate should not pay for — and a name
        // it never uses would push the next specialization's own name onto a `-1` suffix.
        let name = self.name_for(&key, body, env);
        let mut specialized = FunctionEdit::new(specialized);
        // The body carries its original's name until renamed, which would print two functions under
        // one header in a MIR dump.
        specialized.set_name(name);
        let specialized = specialized.finish(env);
        self.raw.push(specialized.clone());
        self.progress.push(if from_final {
            self.ready += 1;
            Progress::Ready
        } else {
            Progress::Deferred
        });
        self.created.push(Specialization {
            original: key.callee,
            name,
            body: specialized,
        });
        if let Some((family, copied)) = callback_charge {
            self.callback_created += 1;
            let growth = self.callback_growth.get_mut(&family).unwrap();
            growth.spent += copied;
            growth.last_admitted = Some(copied);
        }
        self.structures.insert(digest, id);
        self.cache.insert(key, id);
        Some(id)
    }

    /// The specialization already created that `specialized` duplicates, if there is one.
    ///
    /// The digest selects at most one candidate and the bodies then decide, which is why a candidate
    /// that fails to match is simply not shared with: the entry it occupies stays put, costing the
    /// colliding pair their sharing and nothing else.
    ///
    /// A copy of a final body is not shared with a deferred one, which callers read raw until the
    /// worklist reaches it: they would price it at its raw size instead of its optimized one.
    ///
    /// Compared against the *raw* stage, the body as created — `created` is rewritten in place as
    /// the worklist reaches each entry, so comparing against it would make sharing depend on how far
    /// optimization had got.
    fn identical_to(
        &self,
        specialized: &Function,
        original: FunctionId,
        own: FunctionId,
        digest: u64,
        from_final: bool,
    ) -> Option<LocalFunctionId> {
        let candidate = *self.structures.get(&digest)?;
        let index = candidate.as_index().checked_sub(self.first_index)?;
        if self.created.get(index)?.original != original
            || (from_final && self.progress[index] == Progress::Deferred)
        {
            return None;
        }
        let candidate_own = FunctionId {
            module: self.module,
            function: candidate,
        };
        structurally_identical(
            specialized,
            &self_reference(own),
            self.raw.get(index)?,
            &self_reference(candidate_own),
        )
        .then_some(candidate)
    }

    /// `body` substituted at `instantiation`, computed once per distinct pair.
    ///
    /// The substitution is deterministic in its inputs, so the memo changes no decision — it only
    /// stops the inliner from rebuilding and re-verifying an identical body at every call site that
    /// asks for it.
    pub(crate) fn substituted_body<Ty: TypeLike>(
        &self,
        callee: FunctionId,
        instantiation: &Instantiation,
        scheme: &TypeScheme<Ty>,
        body: &Function,
        env: ModuleEnv<'_>,
    ) -> Function {
        let key = (callee, instantiation.clone());
        if let Some(existing) = self.substituted.borrow().get(&key) {
            return existing.clone();
        }
        let substituted = substitute_body(body, scheme, instantiation, env);
        self.substituted
            .borrow_mut()
            .insert(key, substituted.clone());
        substituted
    }

    /// A specialization's generated name.
    ///
    /// Follows the `#impl:` convention the compiler already uses for generated impl functions: a
    /// readable part naming what it came from, a `#spec:` marker saying it is compiler-generated,
    /// and a discriminator. The instantiation is rendered where it is short enough to read, because
    /// `sort#spec:[std::int]` tells a user in a backtrace far more than a hash does; a long or
    /// unrenderable key falls back to a stable hash, as impl names do.
    fn name_for(&self, key: &SpecializationKey, original: &Function, env: ModuleEnv<'_>) -> Ustr {
        const READABLE_LIMIT: usize = 48;

        // The *readable* part is the callee's local name, because this name is stored in a module's
        // function table and every renderer prepends that module — a qualified name here would come
        // out doubled. The *canonical* part below stays fully qualified, which is what has to be
        // unique: two callees of the same local name in different modules would otherwise hash
        // alike, and this table will hold callees from more than one module once cross-module
        // specialization arrives.
        let qualified = mir::Value::Function(key.callee)
            .format_with(&env)
            .to_string();
        let callee_name = original.name;
        let types = key
            .instantiation
            .ty_args
            .iter()
            .map(|ty| ty.format_with(&env).to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let dictionaries = key
            .dictionaries
            .iter()
            .map(|evidence| {
                mir::Value::Evidence(Box::new(evidence.clone()))
                    .format_with(&env)
                    .to_string()
                    // `dict(std::Num<std::int>)` -> `std::Num<std::int>`: the wrapper is noise
                    // inside a `#spec:` list, but the qualification inside it is not.
                    .trim_start_matches("dict(")
                    .trim_end_matches(')')
                    .to_string()
            })
            .collect::<Vec<_>>()
            .join(", ");

        // The canonical identity covers *every* part of the cache key. Hashing less than the key
        // would give two distinct specializations the same name.
        let callbacks = key
            .callbacks
            .iter()
            .map(|(parameter, function)| {
                format!(
                    "{}={}",
                    parameter.as_index(),
                    mir::Value::Function(*function).format_with(&env)
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        let canonical = format!(
            "callee={qualified}; types=[{types}]; dictionaries=[{dictionaries}]; callbacks=[{callbacks}]"
        );
        // `m0:i` is what `Display` falls back to when a dictionary cannot be rendered through the
        // module env; such a name would depend on id allocation order, so it is not readable.
        let readable = types.len() <= READABLE_LIMIT && !types.contains("m0:i");
        let base = if readable {
            format!("{callee_name}#spec:[{types}]")
        } else {
            format!(
                "{callee_name}#spec:{:08x}",
                stable_generated_name_hash(&canonical)
            )
        };

        // Last line of defence, mirroring `unique_generated_name`: distinct keys must never share a
        // name, whichever branch produced it.
        unique_generated_name(ustr(&base), |candidate| {
            self.created
                .iter()
                .any(|existing| existing.name == candidate)
        })
    }
}

/// Specializes `body` — the MIR of the function `scheme` declares — at one call site: its types are
/// substituted by `instantiation`, and its `@extra` dictionary parameters bound to `dictionaries`,
/// the constant evidence that call site passes.
///
/// Both halves in one edit, which is the whole point of the signature: there is no way to ask for
/// one, and the body between them is never a `Function`. `dictionaries` is positional against the
/// body's dictionary parameters, exactly as a call's `@extra` operands are.
///
/// The result is verified by [`FunctionEdit::finish`]. That is a real check rather than a formality:
/// the verifier requires that instantiating a callee's declared signature by a call's recorded
/// arguments reproduces that call's own type, which is precisely the agreement between evidence and
/// types that binding dictionaries alone destroyed.
pub(crate) fn specialize<Ty: TypeLike>(
    body: &Function,
    scheme: &TypeScheme<Ty>,
    key: &SpecializationKey,
    own: FunctionId,
    env: ModuleEnv<'_>,
) -> Function {
    let subst = key.instantiation.substitution(scheme);
    // Bitmap rather than simple: one mapper is reused across every type in the body, which is what
    // makes its `affects_type` constant-time construction cost pay for itself.
    let mut mapper = BitmapInstantiationMapper::new(&subst);

    let mut edit = FunctionEdit::new(body.clone());
    map_types(&mut edit, &mut mapper);
    bind_dictionaries(&mut edit, &key.dictionaries);
    // Check callback forwarding while operands still name the original parameters.
    resolve_recursion(&mut edit, key, own);
    bind_callbacks(&mut edit, &key.callbacks);
    simplify_after_substitution(&mut edit, env);
    edit.finish(env)
}

/// Materialize bound callable values in private places, preserving the visible call ABI.
fn bind_callbacks(edit: &mut FunctionEdit, callbacks: &[(ParameterId, FunctionId)]) {
    if callbacks.is_empty() {
        return;
    }
    let mut setup = Vec::new();
    let mut replacements = FxHashMap::default();
    let span = edit.block(edit.entry()).terminator.span;
    for &(parameter, function) in callbacks {
        let mut alloca = Operation::alloca(span, edit.parameters()[parameter.as_index()].ty);
        let place = edit.assign_new_result(&mut alloca).unwrap();
        setup.push(alloca);
        setup.push(Operation::store(
            span,
            mir::Value::Function(function),
            place.clone(),
        ));
        replacements.insert(parameter, place);
    }
    // Passing the same callable place as an argument can prevent ordinary store forwarding.
    // Its direct invocations are nevertheless known by the immutable parameter binding itself.
    let bound: FxHashMap<_, _> = callbacks.iter().copied().collect();
    let mut loaded = FxHashMap::default();
    for block in edit.blocks() {
        for operation in edit.block(block).operations.iter() {
            if matches!(operation.kind, OperationKind::Load)
                && let mir::Value::Parameter(parameter) = operation.operands[0]
            {
                loaded.insert(operation.result_id().unwrap(), parameter);
            }
        }
    }
    for block in edit.blocks().collect::<Vec<_>>() {
        let block = edit.block_mut(block);
        for operation in block
            .operations
            .iter_mut()
            .chain(match &mut block.terminator.kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            })
        {
            if matches!(operation.kind, OperationKind::Call { .. }) {
                let parameter = callback_parameter(&operation.operands[0], &loaded);
                if let Some(function) = parameter.and_then(|parameter| bound.get(&parameter)) {
                    operation.operands[0] = mir::Value::Function(*function);
                }
            }
        }
    }
    edit.visit_operands_mut(|operand| {
        if let mir::Value::Parameter(parameter) = operand
            && let Some(place) = replacements.get(parameter)
        {
            *operand = place.clone();
        }
    });
    edit.block_mut(edit.entry()).operations.splice(0..0, setup);
}

/// A generic body rewritten at one call site's instantiation, for a consumer that splices it rather
/// than keeping it.
///
/// The same type substitution [`specialize`] applies, and deliberately none of the rest. There are
/// no dictionaries to bind, because an inliner substitutes the caller's own evidence operands
/// positionally like any other parameter; and no recursion to redirect, because no new function is
/// created for a self-call to name — a recursive callee is refused by the inliner anyway.
pub(crate) fn substitute_body<Ty: TypeLike>(
    body: &Function,
    scheme: &TypeScheme<Ty>,
    instantiation: &Instantiation,
    env: ModuleEnv<'_>,
) -> Function {
    let subst = instantiation.substitution(scheme);
    let mut mapper = BitmapInstantiationMapper::new(&subst);

    let mut edit = FunctionEdit::new(body.clone());
    map_types(&mut edit, &mut mapper);
    simplify_after_substitution(&mut edit, env);
    edit.finish(env)
}

/// The rewrites that knowing the concrete types makes possible, shared by both substituting paths.
///
/// Each is a consequence of substitution rather than an optimization in its own right: an effect
/// variable resolved to a concrete effect can make a conservatively-fallible call infallible, a
/// concrete type can have a static layout, and a concrete type can own nothing.
fn simplify_after_substitution(edit: &mut FunctionEdit, env: ModuleEnv<'_>) {
    demote_infallible_invokes(edit);
    drop_redundant_layout_witnesses(edit, env);
    elide_trivial_ownership_operations(edit, env);
}

/// Points a specialized body's recursive calls at the specialization rather than the original.
///
/// **A recursive call records no instantiation**, so nothing else can redirect it: type inference
/// types a call within the defining group monomorphically, against the function's own variables,
/// rather than instantiating its scheme — there is no `FnInstData` to carry down. Left alone, a
/// specialization recurses into the generic original and every level below the first runs
/// unspecialized, which for a recursive algorithm is nearly all of them.
///
/// The redirection is sound for the same reason the instantiation is missing: Hindley-Milner cannot
/// infer polymorphic recursion, so a self-call is necessarily at the caller's own instantiation —
/// the one this body was specialized at. Only calls carrying *no* instantiation are redirected; one
/// that carries an explicit instantiation is an ordinary call site, and
/// [`specialize_call_sites`] resolves it through the cache like any other.
///
/// A bound callback is an additional condition: only self-calls forwarding every bound parameter
/// unchanged reuse `own`. Other self-calls record the containing body's monomorphic instantiation,
/// allowing ordinary call-site specialization to retain types while selecting another callback.
///
/// The specialization still carries its original's signature at this point, so the operands need no
/// adjustment; [`dead_evidence`](super::dead_evidence) narrows this call with every other.
fn resolve_recursion(edit: &mut FunctionEdit, key: &SpecializationKey, own: FunctionId) {
    let own = mir::Value::Function(own);
    let parameters = visible_parameters(edit.parameters());
    for block_id in edit.blocks().collect::<Vec<_>>() {
        let block = edit.block_mut(block_id);
        let operations = block
            .operations
            .iter_mut()
            .chain(match &mut block.terminator.kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            });
        for operation in operations {
            if let OperationKind::Call { metadata, .. } = &operation.kind
                && metadata
                    .as_deref()
                    .and_then(|metadata| metadata.instantiation.as_ref())
                    .is_none()
                && operation.operands[0] == mir::Value::Function(key.callee)
            {
                if key.callbacks.iter().all(|(parameter, _)| {
                    visible_operand(operation, &parameters, *parameter)
                        == Some(&mir::Value::Parameter(*parameter))
                }) {
                    operation.operands[0] = own.clone();
                } else {
                    // HM self-calls have the containing body's instantiation even when the
                    // callback changes. Preserve that proof for type-only or new callback copies.
                    let OperationKind::Call { metadata, .. } = &mut operation.kind else {
                        unreachable!()
                    };
                    metadata.get_or_insert_with(Default::default).instantiation =
                        Some(key.instantiation.clone());
                }
            }
        }
    }
}

/// Rewrites the semantic ownership operations that substitution made unnecessary.
///
/// A generic body copies and releases through `Value::clone` and `Value::drop` because it cannot
/// know whether its type owns anything. Substituting a concrete instantiation answers that, and when
/// the answer is "nothing", the semantic forms have representation-level equivalents: a `clone`
/// becomes a `memcpy`, and a `drop` becomes nothing at all. That is the same decision
/// `resolve_local_drop` and `resolve_local_clone` make during elaboration, taken again now that the
/// type is known — which is why a non-generic function never carries these in the first place.
///
/// The two are independent. The verifier's obligation model is type-based
/// (`live_state_for_type` consults the same trivial-copy predicate), so a destination of a
/// trivially-copyable type never carried an obligation, and removing its drop strands nothing.
fn elide_trivial_ownership_operations(edit: &mut FunctionEdit, env: ModuleEnv<'_>) {
    let mut trivial_temporaries = FxHashSet::default();
    let mut has_replace = false;
    for block_id in edit.blocks().collect::<Vec<_>>() {
        let block = edit.block_mut(block_id);
        let mut dead_drops = Vec::new();
        for (index, operation) in block.operations.iter_mut().enumerate() {
            match &operation.kind {
                OperationKind::Alloca { ty } if concrete_type_is_trivial_copy(*ty, &env) => {
                    trivial_temporaries.insert(operation.result_id().expect("alloca has a result"));
                }
                OperationKind::Replace => has_replace = true,
                OperationKind::Clone { ty } if concrete_type_is_trivial_copy(*ty, &env) => {
                    let source = operation.operands[0].clone();
                    let destination = operation.operands[1].clone();
                    *operation = Operation::memcpy(operation.span, source, destination);
                }
                OperationKind::Drop { ty } | OperationKind::DropInitialized { ty }
                    if concrete_type_is_trivial_copy(*ty, &env) =>
                {
                    dead_drops.push(index);
                }
                _ => {}
            }
        }
        // Descending, so an earlier removal cannot move a later one.
        for index in dead_drops.into_iter().rev() {
            block.operations.remove(index);
        }
    }
    if !has_replace || trivial_temporaries.is_empty() {
        return;
    }

    // A trivial drop is gone, but replacement still preserves the displaced value. Turn it into
    // a move only when that value (including its initialization state) is never observed: the
    // source must be an unaliased local used solely for initialization (by a store, copy, move or
    // call result) and one replacement.
    // Existing copy forwarding can then eliminate the temporary altogether.
    let mut replacements = FxHashSet::default();
    for block_id in edit.blocks() {
        let block = edit.block(block_id);
        for operation in &block.operations {
            for (position, operand) in operation.operands.iter().enumerate() {
                let mir::Value::Register(root) = operand else {
                    continue;
                };
                if !trivial_temporaries.contains(root) {
                    continue;
                }
                let allowed = match &operation.kind {
                    OperationKind::Store | OperationKind::Memcpy | OperationKind::Move => {
                        position == 1
                    }
                    // A result place is written by the call; its inputs are separate operands.
                    OperationKind::Call { ty, .. } => {
                        ty.result_convention.has_result_place()
                            && position + 1 == operation.operands.len()
                    }
                    OperationKind::Replace => position == 0 && replacements.insert(*root),
                    _ => false,
                };
                if !allowed {
                    trivial_temporaries.remove(root);
                }
            }
        }
        for operand in block.terminator.operands() {
            if let mir::Value::Register(root) = operand {
                trivial_temporaries.remove(root);
            }
        }
    }
    for block_id in edit.blocks().collect::<Vec<_>>() {
        for operation in &mut edit.block_mut(block_id).operations {
            if matches!(operation.kind, OperationKind::Replace)
                && let mir::Value::Register(root) = &operation.operands[0]
                && trivial_temporaries.contains(root)
            {
                operation.kind = OperationKind::Move;
            }
        }
    }
}

/// Drops `Value` dictionary layout witnesses that substitution made redundant.
///
/// `alloca`, `move`, `replace`, variant construction, and variant/product projection carry
/// them when the relevant layout is only known at run time. Substitution can make all or only some
/// of those layouts static. A witness the generic body needed is then dead weight: for this type the
/// emitter would have chosen the static form. Left in place it is a live use of the dictionary, and
/// a backend would honour it and emit dynamic layout code for a value whose layout it knows. The
/// MIR interpreter ignores it, so this changes no behaviour today.
pub(crate) fn drop_redundant_layout_witnesses(edit: &mut FunctionEdit, env: ModuleEnv<'_>) {
    let moved_types = moved_place_types(edit, env);
    for block_id in edit.blocks().collect::<Vec<_>>() {
        let block = edit.block_mut(block_id);
        let operations = block
            .operations
            .iter_mut()
            .chain(match &mut block.terminator.kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            });
        for operation in operations {
            let span = operation.span;
            match &mut operation.kind {
                // The operand is present exactly in the dynamic form; the type it describes is the
                // operation's own.
                OperationKind::Alloca { ty } => {
                    if operation.operands.len() == 1
                        && type_has_static_layout(*ty, span.location, &env)
                    {
                        operation.operands = Box::new([]);
                    }
                }
                // `move` records no type, so the moved type is read back from the witnessing
                // `Value<T>` dictionary, or else from the places it connects.
                OperationKind::Move | OperationKind::Replace => {
                    if operation.operands.len() == 3
                        && let Some(ty) = witnessed_type(&operation.operands[2], env)
                            .or_else(|| moved_types.get(&operation.operands[0]).copied())
                        && type_has_static_layout(ty, span.location, &env)
                    {
                        let source = operation.operands[0].clone();
                        let destination = operation.operands[1].clone();
                        operation.operands = Box::new([source, destination]);
                    }
                }
                OperationKind::Subfield {
                    variant_payload: false,
                    product: Some(product),
                    ..
                } => {
                    debug_assert_eq!(
                        operation.operands.len(),
                        2 + product.layout_witness_tys.len()
                    );
                    if product.layout_witness_tys.is_empty() {
                        continue;
                    }
                    let required =
                        dynamic_product_member_layouts(product.aggregate_ty, span.location, &env);
                    if required.as_slice() == product.layout_witness_tys.as_ref() {
                        continue;
                    }
                    let mut operands = operation.operands[..2].to_vec();
                    let mut witness_tys = Vec::with_capacity(required.len());
                    assert!(
                        visit_product_witness_retention(
                            &product.layout_witness_tys,
                            &required,
                            |index, keep| {
                                if keep {
                                    witness_tys.push(product.layout_witness_tys[index]);
                                    operands.push(operation.operands[index + 2].clone());
                                }
                            },
                        ),
                        "recomputed product layout witnesses must be an ordered subset of the original schema"
                    );
                    operation.operands = operands.into_boxed_slice();
                    product.layout_witness_tys = witness_tys.into_boxed_slice();
                }
                OperationKind::Subfield {
                    ty,
                    variant_payload: true,
                    has_layout_witness,
                    ..
                } => {
                    if *has_layout_witness && type_has_static_layout(*ty, span.location, &env) {
                        debug_assert_eq!(operation.operands.len(), 3);
                        operation.operands = operation.operands[..2].into();
                        *has_layout_witness = false;
                    }
                }
                OperationKind::Variant {
                    metadata,
                    has_layout_witness,
                    ..
                } if *has_layout_witness
                    && type_has_static_layout(metadata.payload_ty, span.location, &env) =>
                {
                    let new_len = operation.operands.len() - 1;
                    operation.operands = operation.operands[..new_len].into();
                    *has_layout_witness = false;
                }
                _ => {}
            }
        }
    }
}

/// The pointee types of the places a witnessed `move` or `replace` reads, when its witness does not
/// name the moved type itself.
///
/// A dictionary built at run time, or of a generic impl, witnesses a type its impl key alone does
/// not say. Substitution has made the places' own types concrete, so they answer
/// instead. Roles are derived only for a body that has such a witness, which is rare.
fn moved_place_types(edit: &FunctionEdit, env: ModuleEnv<'_>) -> FxHashMap<mir::Value, Type> {
    let unresolved = |operation: &Operation| {
        matches!(operation.kind, OperationKind::Move | OperationKind::Replace)
            && operation.operands.len() == 3
            && witnessed_type(&operation.operands[2], env).is_none()
    };
    let sources: Vec<mir::Value> = edit
        .blocks()
        .flat_map(|block| {
            let block = edit.block(block);
            block.operations.iter().chain(match &block.terminator.kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            })
        })
        .filter(|operation| unresolved(operation))
        .map(|operation| operation.operands[0].clone())
        .collect();
    if sources.is_empty() {
        return FxHashMap::default();
    }
    let roles = edit.value_roles();
    sources
        .into_iter()
        .filter_map(|source| {
            let role = roles.get(&source, edit.constants())?;
            let MirType::Lowered(ty) = role.place_pointee_type()? else {
                return None;
            };
            Some((source, ty))
        })
        .collect()
}

/// Visits the members of an existing product-witness schema and identifies the ordered subset
/// retained by layout recomputation.
fn visit_product_witness_retention(
    current: &[Type],
    required: &[Type],
    mut visit: impl FnMut(usize, bool),
) -> bool {
    let mut required_index = 0;
    for (index, ty) in current.iter().enumerate() {
        let keep = required.get(required_index) == Some(ty);
        if keep {
            required_index += 1;
        }
        visit(index, keep);
    }
    required_index == required.len()
}

/// The type a `Value<T>` dictionary operand witnesses the layout of, when its impl names it.
///
/// A generic impl's key is its own generic type, such as `(A, A)`; its captures would say what `A`
/// is, so the key alone names no concrete type.
fn witnessed_type(witness: &mir::Value, env: ModuleEnv<'_>) -> Option<Type> {
    let id = match witness {
        mir::Value::Dictionary(id) => *id,
        mir::Value::Evidence(evidence) => match &**evidence {
            StaticEvidence::Dictionary { definition, .. } => *definition,
            _ => return None,
        },
        _ => return None,
    };
    let module = env.module_by_id(id.module_id)?;
    let key = module.get_impl_trait_key_by_id(id.impl_id)?;
    key.input_tys().first().copied().filter(Type::is_constant)
}

fn static_evidence_operand(value: &mir::Value) -> Option<StaticEvidence> {
    match value {
        mir::Value::Dictionary(definition) => Some(StaticEvidence::bare_dictionary(*definition)),
        mir::Value::Subscript(definition) => Some(StaticEvidence::bare_subscript(*definition)),
        mir::Value::Evidence(evidence) => Some((**evidence).clone()),
        _ => None,
    }
}

/// Turns an `invoke` whose operation substitution made source-infallible back into an ordinary
/// operation, jumping to the normal successor.
///
/// **Substituting types changes control flow, not only annotations**, which is the one place this
/// transform is more than a rewrite of metadata. A call whose effects are a *variable* is
/// conservatively fallible, so lowering gives it an `invoke` and an error edge — `fn ho(f, x) {
/// match f(x) { .. } }` is the shape. Instantiating that variable at a concrete effect set can make
/// the call infallible, and MIR requires the form to agree with the fallibility: the verifier says
/// so directly.
///
/// Only this direction is possible. A plain `call` has no effect variables to instantiate — it
/// would have been an `invoke` if it had — so substitution can never make one fallible, which is
/// what keeps this a local rewrite rather than a CFG restructuring. It is the same shape folding
/// applies to an `invoke` it evaluated away: the operation moves into the block, the terminator
/// becomes a jump, and the dead error edge leaves its cleanup pad for
/// [`FunctionEdit::remove_unreachable_blocks`].
fn demote_infallible_invokes(edit: &mut FunctionEdit) {
    let projections = open_projection_fallibility(edit);
    let mut demoted = false;
    for block_id in edit.blocks().collect::<Vec<_>>() {
        let block = edit.block_mut(block_id);
        let TerminatorKind::Invoke {
            operation, normal, ..
        } = &block.terminator.kind
        else {
            continue;
        };
        if operation_is_source_fallible(operation, &projections) {
            continue;
        }
        let span = block.terminator.span;
        let normal = *normal;
        let TerminatorKind::Invoke { operation, .. } =
            mem::replace(&mut block.terminator, Terminator::goto(span, normal)).kind
        else {
            unreachable!("the terminator was just matched as an invoke");
        };
        block.operations.push(operation);
        demoted = true;
    }
    if demoted {
        edit.remove_unreachable_blocks();
        edit.merge_blocks_into_predecessors();
    }
}

/// Whether an operation can still raise a source failure, judged the way the verifier judges it.
///
/// A call whose effects mention a variable counts as fallible: the instantiated effects are unknown,
/// so the conservative answer is the only sound one.
///
/// An `end_project` states no fallibility of its own — it carries whatever the projection it closes
/// carries — so it is resolved through `projections`, keyed by the projection's result. Judging it
/// conservatively fallible instead is *not* safe here: a projection and its `end_project` must
/// agree, so demoting the one while leaving the other an `invoke` produces a body the verifier
/// rejects.
fn operation_is_source_fallible(
    operation: &Operation,
    projections: &FxHashMap<ValueId, bool>,
) -> bool {
    match operation.source_fallibility() {
        SourceFallibility::Infallible => false,
        SourceFallibility::Fallible => true,
        SourceFallibility::FromOpenProjection => match operation.operands.first() {
            Some(mir::Value::Register(id)) => projections.get(id).copied().unwrap_or(false),
            _ => false,
        },
    }
}

/// Whether each open projection in the body can raise a source failure, keyed by its result.
///
/// The accessor contract lives on the defining `project`, so this is the substituting pass's
/// equivalent of the operand role the verifier derives.
fn open_projection_fallibility(edit: &FunctionEdit) -> FxHashMap<ValueId, bool> {
    let mut fallibility = FxHashMap::default();
    let mut record = |operation: &Operation| {
        if let OperationKind::Project { ty, .. } = &operation.kind
            && let Some(result) = operation.result_id()
        {
            fallibility.insert(
                result,
                ty.effects()
                    .contains(Effect::Primitive(PrimitiveEffect::Fallible))
                    || ty.effects().has_variables(),
            );
        }
    };
    for block_id in edit.blocks() {
        let block = edit.block(block_id);
        block.operations.iter().for_each(&mut record);
        if let TerminatorKind::Invoke { operation, .. } = &block.terminator.kind {
            record(operation);
        }
    }
    fallibility
}

/// Rewrites every type the body carries through `mapper`.
///
/// Takes the mapper rather than building one so that the tests can supply a recording mapper and
/// enumerate a body's per-operation types through this same traversal. They deliberately do *not*
/// do that for the signature and the constant pool, which they read directly — a check sharing the
/// traversal it checks cannot see what the traversal skips.
pub(crate) fn map_types(edit: &mut FunctionEdit, mapper: &mut impl TypeMapper) {
    for parameter in edit.parameters_mut() {
        parameter.ty = parameter.ty.map(mapper);
    }
    for constant in edit.constants_mut() {
        constant.ty = constant.ty.map(mapper);
    }
    for block in edit.blocks().collect::<Vec<_>>() {
        let block = edit.block_mut(block);
        for operation in &mut block.operations {
            substitute_in_operation(operation, mapper);
        }
        if let TerminatorKind::Invoke { operation, .. } = &mut block.terminator.kind {
            substitute_in_operation(operation, mapper);
        }
    }
}

/// Replaces every use of a dictionary parameter by the constant dictionary bound to it.
///
/// The parameters themselves stay in the signature; see the module documentation. Binding fewer
/// dictionaries than the body has parameters is a caller bug rather than a partial specialization:
/// a call site either knows all of its callee's evidence or forwards its own.
fn bind_dictionaries(edit: &mut FunctionEdit, dictionaries: &[StaticEvidence]) {
    let parameters: Vec<ParameterId> = edit
        .parameters()
        .iter()
        .enumerate()
        .filter(|(_, parameter)| matches!(parameter.kind, ParameterKind::Dictionary))
        .map(|(index, _)| ParameterId::from_index(index))
        .collect();
    assert_eq!(
        parameters.len(),
        dictionaries.len(),
        "specializing a body with {} dictionary parameters by {} dictionaries",
        parameters.len(),
        dictionaries.len()
    );
    if dictionaries.is_empty() {
        return;
    }

    let bound: FxHashMap<ParameterId, StaticEvidence> = parameters
        .into_iter()
        .zip(dictionaries.iter().cloned())
        .collect();
    edit.visit_operands_mut(|operand| {
        if let mir::Value::Parameter(id) = operand
            && let Some(dictionary) = bound.get(id)
        {
            *operand = mir::Value::Evidence(Box::new(dictionary.clone()));
        }
    });
}

/// Rewrites the types one operation carries.
///
/// Exhaustive by construction: the `match` names every kind, so an operation that gains a type
/// field fails to compile here rather than silently keeping the generic one.
fn substitute_in_operation(operation: &mut Operation, mapper: &mut impl TypeMapper) {
    match &mut operation.kind {
        OperationKind::Alloca { ty }
        | OperationKind::BlackBox { ty }
        | OperationKind::DictEntry { ty, .. }
        | OperationKind::BuildDictionary { ty, .. }
        | OperationKind::SubscriptMember { ty, .. }
        | OperationKind::BuildSubscriptEvidence { ty }
        | OperationKind::BuildSubscript { ty }
        | OperationKind::CloneSubscriptEnv { ty }
        | OperationKind::BorrowSubscriptMember { ty, .. }
        | OperationKind::BuildClosure { ty, .. }
        | OperationKind::CloneClosureEnv { ty } => *ty = ty.map(mapper),
        OperationKind::Subfield { ty, product, .. } => {
            *ty = ty.map(mapper);
            if let Some(product) = product {
                product.aggregate_ty = product.aggregate_ty.map(mapper);
                for witness_ty in &mut product.layout_witness_tys {
                    *witness_ty = witness_ty.map(mapper);
                }
            }
        }
        OperationKind::AddressOffset { ty, .. }
        | OperationKind::MoveBytes { ty }
        | OperationKind::MoveRange { ty } => *ty = ty.map(mapper),
        OperationKind::AddressOffsetPlace { pointing_to } => *pointing_to = pointing_to.map(mapper),
        OperationKind::Variant { metadata, .. } => {
            metadata.ty = metadata.ty.map(mapper);
            metadata.payload_ty = metadata.payload_ty.map(mapper);
        }
        OperationKind::BuildArray { element_ty } => *element_ty = element_ty.map(mapper),
        OperationKind::AllocaPlace { pointing_to } => *pointing_to = pointing_to.map(mapper),
        OperationKind::RuntimeAlloc { pointee } => *pointee = pointee.map(mapper),
        OperationKind::Call { ty, metadata } => {
            **ty = ty.map(mapper);
            // The instantiation this body's own calls record. Easy to miss because it is not a
            // type field, and the one that makes specialization cascade: an inner call recording
            // the container's quantifiers becomes concrete exactly when the container does.
            if let Some(instantiation) = metadata
                .as_deref_mut()
                .and_then(|metadata| metadata.instantiation.as_mut())
            {
                substitute_in_instantiation(instantiation, mapper);
            }
        }
        OperationKind::Project { yielded, ty } => {
            *yielded = yielded.map(mapper);
            **ty = ty.map(mapper);
        }
        OperationKind::EndProject
        | OperationKind::CompareEqual
        | OperationKind::Load
        | OperationKind::ExtractTag
        | OperationKind::ExtractPayloadIndirection
        | OperationKind::IsInitialized
        | OperationKind::Store
        | OperationKind::Clear
        | OperationKind::Memcpy
        | OperationKind::Move
        | OperationKind::Replace
        | OperationKind::StackSave
        | OperationKind::StackRestore
        | OperationKind::CheckCallDepth
        | OperationKind::CheckFuel
        | OperationKind::RuntimeDealloc
        | OperationKind::DropSubscriptEnv
        | OperationKind::DropClosureEnv => {}
        OperationKind::Clone { ty }
        | OperationKind::Drop { ty }
        | OperationKind::DropInitialized { ty } => *ty = ty.map(mapper),
    }
}

/// Rewrites every call site of `func` that can be pointed at a specialized copy of its callee.
///
/// Returns `None` if nothing changed. A site is rewritten when all of the following hold, and each
/// is deliberately conservative — a refusal costs an optimization, never correctness:
///
/// - the callee is statically known and is not itself a specialization;
/// - the callee has a body and a concrete instantiation or known immutable callback;
/// - the call records a fully concrete instantiation, or its callee has no quantifiers and therefore
///   has the equivalent empty instantiation. A caller that forwards its own quantifiers records
///   them here, and specializing *it* makes this site concrete on a later round;
/// - every hidden evidence operand is a constant dictionary;
/// - specializing would achieve something (see [`worth_specializing`]);
/// - the budget allows another specialization, unless this one is already cached.
///
/// The callee may live in another module: the specialization is still created in the *optimizing*
/// module's table, from the callee's optimized body, which is safe because the session tracks the
/// dependency.
pub(crate) fn specialize_call_sites(
    func: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    specializations: &mut Specializations,
) -> Option<Function> {
    // Deciding a specialization mutates the cache and consumes the shared budget, so it cannot be
    // repeated after discovering that this body changes. Record the decisions while the body is
    // still borrowed, then pay for an editable copy only when there is something to apply.
    // Avoid another dataflow analysis unless a call can bind a function argument.
    // Callback descriptors are shared across callers and invalidated when a callee is published.
    let needs_callbacks = func.blocks().any(|block| {
        let block = func.block(block);
        block
            .operations()
            .iter()
            .chain(match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            })
            .any(|operation| may_bind_callback(operation, session, specializations))
    });
    let analysis = needs_callbacks.then(|| dataflow::analyze(func, env));
    let mut rewrites = Vec::new();
    for block_id in func.blocks() {
        let block = func.block(block_id);
        let mut state = analysis.as_ref().map(|a| a.entry_state(block_id));
        for (index, operation) in block.operations().iter().enumerate() {
            if let Some(id) = specialization_for(
                operation,
                analysis.as_ref().zip(state.as_ref()),
                env,
                session,
                specializations,
            ) {
                rewrites.push((
                    OperationSite {
                        block: block_id,
                        index: OperationIndex::from_index(index),
                    },
                    id,
                ));
            }
            if let Some((analysis, state)) = analysis.as_ref().zip(state.as_mut()) {
                analysis.step(func, env, operation, state);
            }
        }
        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind
            && let Some(id) = specialization_for(
                operation,
                analysis.as_ref().zip(state.as_ref()),
                env,
                session,
                specializations,
            )
        {
            rewrites.push((
                OperationSite {
                    block: block_id,
                    index: OperationIndex::from_index(block.operations().len()),
                },
                id,
            ));
        }
    }
    if rewrites.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for (site, id) in rewrites {
        let operation = operation_at_mut(&mut edit, site);
        operation.operands[0] = mir::Value::Function(FunctionId {
            module: module_id,
            function: id,
        });
        // The specialization is not generic, so it has no quantifiers for an instantiation to be
        // positional against. Leaving the old one would claim otherwise.
        if let OperationKind::Call { metadata, .. } = &mut operation.kind {
            *metadata = None;
        }
    }
    Some(edit.finish_unverified())
}

/// The operation recorded at `site`, where the one-past-the-end index names an invoke terminator.
fn operation_at_mut(edit: &mut FunctionEdit, site: OperationSite) -> &mut Operation {
    let block = edit.block_mut(site.block);
    let index = site.index.as_index();
    if index < block.operations.len() {
        return &mut block.operations[index];
    }
    assert_eq!(
        index,
        block.operations.len(),
        "a specialization site must name an operation or invoke terminator"
    );
    match &mut block.terminator.kind {
        TerminatorKind::Invoke { operation, .. } => operation,
        _ => unreachable!("a one-past-the-end specialization site must name an invoke"),
    }
}

/// Calls accept the parameter's place directly or a value loaded from it.
fn callback_parameter(
    callee: &mir::Value,
    loads: &FxHashMap<ValueId, ParameterId>,
) -> Option<ParameterId> {
    match callee {
        mir::Value::Parameter(parameter) => Some(*parameter),
        mir::Value::Register(id) => loads.get(id).copied(),
        _ => None,
    }
}

/// Immutable callback parameters invoked in a loop or directly by a self-recursive function.
/// A single isolated invocation does not justify copying the enclosing body.
fn repeated_callback_parameters(body: &Function, identity: FunctionId) -> FxHashSet<ParameterId> {
    let mut loads = FxHashMap::default();
    let mut callees = Vec::new();
    for block_id in body.blocks() {
        let block = body.block(block_id);
        for operation in block
            .operations()
            .iter()
            .chain(match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            })
        {
            match operation.kind {
                OperationKind::Load => {
                    if let mir::Value::Parameter(parameter) = operation.operands[0] {
                        loads.insert(operation.result_id().unwrap(), parameter);
                    }
                }
                OperationKind::Call { .. } => callees.push((block_id, &operation.operands[0])),
                _ => {}
            }
        }
    }
    let self_recursive = callees
        .iter()
        .any(|(_, callee)| **callee == mir::Value::Function(identity));
    let invoked = callees
        .into_iter()
        .filter_map(|(block, callee)| {
            let parameter = callback_parameter(callee, &loads)?;
            let definition = &body.parameters()[parameter.as_index()];
            (definition.kind == ParameterKind::Parameter(ArgConvention::Let)
                && definition.ty.is_function())
            .then_some((block, parameter))
        })
        .collect::<Vec<_>>();
    if invoked.is_empty() {
        return FxHashSet::default();
    }
    let cyclic = (!self_recursive).then(|| cost::cyclic_blocks(body));
    invoked
        .into_iter()
        .filter(|(block, _)| {
            cyclic
                .as_ref()
                .is_none_or(|cyclic| cyclic[block.as_index()])
        })
        .map(|(_, parameter)| parameter)
        .collect()
}

/// Eligibility shared by the callback preflight and specialization admission.
struct Candidate<'a> {
    callee: FunctionId,
    instantiation: Cow<'a, Instantiation>,
    dictionaries: &'a [mir::Value],
}

fn visible_start(operation: &Operation) -> Option<usize> {
    let OperationKind::Call { ty, .. } = &operation.kind else {
        return None;
    };
    operation
        .operands
        .len()
        .checked_sub(ty.fn_ty.args.len() + usize::from(ty.result_convention.has_result_place()))
        .filter(|start| *start >= 1)
}

/// Visible positions exclude dictionary and result parameters, even after evidence narrowing.
fn visible_parameters(parameters: &[mir::Parameter]) -> Vec<ParameterId> {
    parameters
        .iter()
        .enumerate()
        .filter(|(_, parameter)| {
            matches!(
                parameter.kind,
                ParameterKind::Parameter(_) | ParameterKind::Owned
            )
        })
        .map(|(index, _)| ParameterId::from_index(index))
        .collect()
}

fn visible_operand<'a>(
    operation: &'a Operation,
    parameters: &[ParameterId],
    parameter: ParameterId,
) -> Option<&'a mir::Value> {
    let position = parameters
        .iter()
        .position(|candidate| *candidate == parameter)?;
    operation.operands.get(visible_start(operation)? + position)
}

fn candidate<'a>(
    operation: &'a Operation,
    session: &CompilerSession,
    specializations: &Specializations,
) -> Option<Candidate<'a>> {
    let OperationKind::Call { metadata, .. } = &operation.kind else {
        return None;
    };
    let mir::Value::Function(callee) = operation.operands[0] else {
        return None;
    };
    if specializations.is_specialization(callee) {
        return None;
    }
    if callee.module == specializations.module()
        && specializations.finished_body(callee.function).is_none()
    {
        specializations.note_unsettled();
    }
    let module = session.expect_fresh_module(callee.module);
    let scheme = &module
        .get_function_by_id(callee.function)?
        .definition
        .ty_scheme;
    // Hidden-evidence variables need the complete recorded instantiation; visible types alone
    // cannot prove them. A non-generic callee has the equivalent empty instantiation.
    let instantiation = match metadata
        .as_deref()
        .and_then(|metadata| metadata.instantiation.as_ref())
    {
        Some(instantiation) => Cow::Borrowed(instantiation),
        None if scheme.ty_quantifiers.is_empty() && scheme.eff_quantifiers.is_empty() => {
            Cow::Owned(Instantiation {
                ty_args: Vec::new(),
                eff_args: Vec::new(),
            })
        }
        None => return None,
    };
    if instantiation.ty_args.iter().any(Type::is_variable) {
        return None;
    }
    let dictionaries = &operation.operands[1..visible_start(operation)?];
    if dictionaries
        .iter()
        .any(|operand| static_evidence_operand(operand).is_none())
    {
        return None;
    }
    Some(Candidate {
        callee,
        instantiation,
        dictionaries,
    })
}

/// Reject impossible callback sites before paying for caller dataflow.
fn may_bind_callback(
    operation: &Operation,
    session: &CompilerSession,
    specializations: &Specializations,
) -> bool {
    let OperationKind::Call { ty, .. } = &operation.kind else {
        return false;
    };
    if !ty
        .fn_ty
        .args
        .iter()
        .any(|argument| argument.ty.is_function())
    {
        return false;
    }
    candidate(operation, session, specializations).is_some_and(|candidate| {
        specializations
            .invoked_callbacks(candidate.callee, session)
            .is_some_and(|parameters| !parameters.is_empty())
    })
}

/// The specialization this call site should be pointed at, creating it if needed.
fn specialization_for(
    operation: &Operation,
    facts: Option<(&Analysis, &State)>,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    specializations: &mut Specializations,
) -> Option<LocalFunctionId> {
    let OperationKind::Call { ty, metadata } = &operation.kind else {
        return None;
    };
    let recorded_instantiation = metadata
        .as_deref()
        .and_then(|metadata| metadata.instantiation.as_ref());
    // Ordinary calls with neither type arguments nor callback facts need no metadata lookup.
    if recorded_instantiation.is_none()
        && (facts.is_none() || !ty.fn_ty.args.iter().any(|arg| arg.ty.is_function()))
    {
        return None;
    }
    let Candidate {
        callee,
        instantiation,
        dictionaries,
    } = candidate(operation, session, specializations)?;
    let module = session.expect_fresh_module(callee.module);
    let scheme = &module
        .get_function_by_id(callee.function)?
        .definition
        .ty_scheme;
    let invoked = if facts.is_some()
        && ty
            .fn_ty
            .args
            .iter()
            .any(|argument| argument.ty.is_function())
    {
        specializations.invoked_callbacks(callee, session)
    } else {
        None
    };
    let parameters = if invoked
        .as_ref()
        .is_some_and(|parameters| !parameters.is_empty())
    {
        let callees = SemanticCallees::new(session, Some(specializations));
        visible_parameters(callees.body(callee)?.parameters())
    } else {
        Vec::new()
    };
    let callbacks = parameters
        .iter()
        .filter_map(|parameter| {
            if !invoked
                .as_ref()
                .is_some_and(|invoked| invoked.contains(parameter))
            {
                return None;
            }
            let operand = visible_operand(operation, &parameters, *parameter)?;
            // Visible arguments are places, not materialized Function operands.
            let (analysis, state) = facts?;
            let fact = state.place(analysis.tracked_place_of(operand)?);
            let Const::Function(function) = fact.known()? else {
                return None;
            };
            let function = *function;
            Some((*parameter, function))
        })
        .collect::<Vec<_>>();
    drop(invoked);
    if recorded_instantiation.is_none() && callbacks.is_empty() {
        return None;
    }
    let mut key = SpecializationKey {
        callee,
        instantiation: instantiation.clone().into_owned(),
        dictionaries: dictionaries
            .iter()
            .map(static_evidence_operand)
            .collect::<Option<Vec<_>>>()?,
        callbacks,
    };
    loop {
        if let Some(existing) = specializations.cached(&key) {
            return Some(existing);
        }
        let callback = !key.callbacks.is_empty();
        if specializations.is_rejected(&key)
            || specializations.is_full()
            || (callback
                && (specializations.callbacks_full()
                    || !specializations.callback_growth_allows(&key)))
        {
            if callback {
                key.callbacks.clear();
                continue;
            }
            return None;
        }
        // Read the body only after cheap admission checks. Reacquiring it each iteration keeps
        // table borrows out of construction and allows callback refusals to use this same path.
        let callees = SemanticCallees::new(session, Some(specializations));
        let body = callees.body(callee)?;
        if !callback && !worth_specializing(body, scheme, &instantiation, &key.dictionaries, env) {
            specializations.reject(key);
            return None;
        }
        // Substitution interns types; release borrowed inputs before constructing the copy.
        let scheme = scheme.clone();
        let body = body.clone();
        if !callback {
            return Some(specializations.get_or_create(key, &scheme, &body, env));
        }
        if let Some(id) = specializations.get_or_create_callback(key.clone(), &scheme, &body, env) {
            return Some(id);
        }
        key.callbacks.clear();
    }
}

/// Moves `body`'s inline chains from module `from`'s table into module `to`'s.
fn move_inline_sites(body: Function, from: ModuleId, to: ModuleId, env: ModuleEnv<'_>) -> Function {
    if from == to {
        return body;
    }
    let source = env.inline_sites(from).borrow();
    let mut sites = env.inline_sites(to).borrow_mut();
    let mut rebase = InlineRebase::moved();
    let mut edit = FunctionEdit::new(body);
    edit.visit_spans_mut(|span| *span = rebase.span(*span, Some(&source), &mut sites));
    edit.finish_unverified()
}

/// Whether substitution exposes a reason Ferlium keeps a specialized body.
///
/// This is a linear preflight over the callee body, before cloning, verification or insertion into the
/// specialization worklist. It deliberately answers only “can this buy anything we know how to
/// realize?”, not “is the benefit worth this body size?” — useful specializations still need a
/// growth policy, but bodies that expose no payoff should not be built at all.
///
/// A bound dictionary pays off in three local ways, each recognized at the operation that the
/// existing specialization rewrites consume:
///
/// - a `dict_entry` feeding a call becomes a constant, and folding resolves it to a known function;
/// - a `Value::clone` or `Value::drop` through the dictionary becomes a `memcpy` or nothing, once
///   the concrete type is known to own nothing;
/// - a layout witness goes, once the concrete type has a size the backend can see.
///
/// There is also one interprocedural payoff: a small generic body cannot be inlined, while its
/// concrete specialization can. A larger body can still propagate concrete types or evidence into
/// one of its direct generic calls, making that callee eligible for specialization on a later
/// round. These are detected separately: body size prices the first, while changed call metadata
/// proves the second rather than treating arbitrary dictionary use as useful.
fn worth_specializing<Ty: TypeLike>(
    body: &Function,
    scheme: &TypeScheme<Ty>,
    instantiation: &Instantiation,
    dictionaries: &[StaticEvidence],
    env: ModuleEnv<'_>,
) -> bool {
    if dictionaries.is_empty() {
        return false;
    }
    let parameters: Vec<ParameterId> = body
        .parameters()
        .iter()
        .enumerate()
        .filter(|(_, parameter)| matches!(parameter.kind, ParameterKind::Dictionary))
        .map(|(index, _)| ParameterId::from_index(index))
        .collect();
    if parameters.len() != dictionaries.len() {
        // The call's evidence does not line up with the body's parameters. Not a case that should
        // arise, and not one to guess at.
        return false;
    }
    let bound: FxHashMap<_, _> = parameters
        .into_iter()
        .zip(dictionaries.iter().cloned())
        .collect();
    let subst = instantiation.substitution(scheme);
    let mut mapper = BitmapInstantiationMapper::new(&subst);
    let mut bound_entries = FxHashSet::default();
    let mut reads_bound_evidence = false;

    // First find local rewrites and remember dictionary-entry results. Calls can occur in a block
    // visited before their dominating definition in the function's storage order, so resolving the
    // devirtualization class is a second linear pass rather than relying on traversal order.
    for block in body.blocks() {
        let block = body.block(block);
        let operations = block
            .operations()
            .iter()
            .chain(match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            });
        for operation in operations {
            reads_bound_evidence |= operation.operands.iter().any(
                |operand| matches!(operand, mir::Value::Parameter(id) if bound.contains_key(id)),
            );
            match &operation.kind {
                OperationKind::DictEntry { .. }
                    if operation.operands.first().is_some_and(|operand| {
                        matches!(operand, mir::Value::Parameter(id) if bound.contains_key(id))
                    }) =>
                {
                    if let Some(result) = operation.result_id() {
                        bound_entries.insert(result);
                    }
                }
                OperationKind::Call { ty, metadata }
                    if matches!(operation.operands.first(), Some(mir::Value::Function(_)))
                        && metadata
                            .as_deref()
                            .and_then(|metadata| metadata.instantiation.as_ref())
                            .is_some_and(|inner| {
                            let visible_start = operation
                                .operands
                                .len()
                                .checked_sub(ty.fn_ty.args.len() + 1);
                            let binds_forwarded_evidence = visible_start.is_some_and(|start| {
                                operation.operands.get(1..start).is_some_and(|evidence| {
                                    evidence.iter().any(|operand| {
                                        matches!(
                                            operand,
                                            mir::Value::Parameter(id) if bound.contains_key(id)
                                        )
                                    })
                                })
                            });
                            let was_generic = inner.ty_args.iter().any(Type::is_variable)
                                || inner.eff_args.iter().any(EffType::has_variables);
                            let mut mapped = inner.clone();
                            substitute_in_instantiation(&mut mapped, &mut mapper);
                            let becomes_concrete = was_generic
                                && mapped.ty_args.iter().all(|ty| ty.is_constant())
                                && mapped.eff_args.iter().all(|effect| !effect.has_variables());
                            binds_forwarded_evidence || becomes_concrete
                        }) =>
                {
                    return true;
                }
                OperationKind::Clone { ty } | OperationKind::Drop { ty } | OperationKind::DropInitialized { ty }
                    if ty.is_variable()
                        && concrete_type_is_trivial_copy(ty.map(&mut mapper), &env) =>
                {
                    return true;
                }
                OperationKind::Alloca { ty }
                    if operation.operands.len() == 1
                        && matches!(
                            operation.operands.first(),
                            Some(mir::Value::Parameter(id)) if bound.contains_key(id)
                        )
                        && type_has_static_layout(ty.map(&mut mapper), operation.span.location, &env) =>
                {
                    return true;
                }
                OperationKind::Move | OperationKind::Replace
                    if operation.operands.len() == 3
                        && operation.operands.get(2).is_some_and(|witness| {
                            let mir::Value::Parameter(parameter) = witness else {
                                return false;
                            };
                            let Some(dictionary) = bound.get(parameter) else {
                                return false;
                            };
                            witnessed_type(
                                &mir::Value::Evidence(Box::new(dictionary.clone())),
                                env,
                            )
                            .is_some_and(
                                |ty| type_has_static_layout(ty, operation.span.location, &env),
                            )
                        }) =>
                {
                    return true;
                }
                OperationKind::Subfield {
                    variant_payload: false,
                    product: Some(product),
                    ..
                } => {
                    if product.layout_witness_tys.is_empty()
                        || !operation.operands[2..].iter().any(|operand| {
                            matches!(
                                operand,
                                mir::Value::Parameter(id) if bound.contains_key(id)
                            )
                        })
                    {
                        continue;
                    }
                    let aggregate_ty = product.aggregate_ty.map(&mut mapper);
                    let witness_tys = product
                        .layout_witness_tys
                        .iter()
                        .map(|ty| ty.map(&mut mapper))
                        .collect::<Vec<_>>();
                    let required =
                        dynamic_product_member_layouts(aggregate_ty, operation.span.location, &env);
                    if required != witness_tys {
                        let mut removes_bound_witness = false;
                        let schema_is_valid = visit_product_witness_retention(
                            &witness_tys,
                            &required,
                            |index, keep| {
                                removes_bound_witness |= !keep
                                    && matches!(
                                        operation.operands.get(index + 2),
                                        Some(mir::Value::Parameter(id)) if bound.contains_key(id)
                                    );
                            },
                        );
                        if schema_is_valid && removes_bound_witness {
                            return true;
                        }
                    }
                }
                OperationKind::Subfield {
                    ty,
                    variant_payload: true,
                    has_layout_witness: true,
                    ..
                } if operation.operands.get(2).is_some_and(|witness| {
                    matches!(witness, mir::Value::Parameter(id) if bound.contains_key(id))
                }) && type_has_static_layout(ty.map(&mut mapper), operation.span.location, &env) =>
                {
                    return true;
                }
                OperationKind::Variant {
                    metadata,
                    has_layout_witness: true,
                    ..
                } if operation.operands.last().is_some_and(|witness| {
                    matches!(witness, mir::Value::Parameter(id) if bound.contains_key(id))
                }) && type_has_static_layout(
                    metadata.payload_ty.map(&mut mapper),
                    operation.span.location,
                    &env,
                ) =>
                {
                    return true;
                }
                _ => {}
            }
        }
    }

    if reads_bound_evidence && !cost::hot_cost_exceeds(body, budget::INLINE_CALLEE_COST) {
        return true;
    }

    if bound_entries.is_empty() {
        return false;
    }
    for block in body.blocks() {
        let block = body.block(block);
        let operations = block
            .operations()
            .iter()
            .chain(match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            });
        for operation in operations {
            if matches!(operation.kind, OperationKind::Call { .. })
                && matches!(
                    operation.operands.first(),
                    Some(mir::Value::Register(id)) if bound_entries.contains(id)
                )
            {
                return true;
            }
        }
    }
    false
}

/// Rewrites a recorded instantiation, which is a list of types and effects like any other.
fn substitute_in_instantiation(instantiation: &mut Instantiation, mapper: &mut impl TypeMapper) {
    for ty in &mut instantiation.ty_args {
        *ty = ty.map(mapper);
    }
    for eff in &mut instantiation.eff_args {
        *eff = mapper.map_effect_type(eff);
    }
}

#[cfg(test)]
mod tests {
    use ustr::ustr;

    use super::*;
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization,
        compiler::ensure_mir_artifacts,
        hir::value::LiteralValue,
        mir::{Value, terminator::TerminatorKind},
        module::{ModuleId, Path},
        std::math::Float,
        types::{
            effects::{EffType, EffectVar},
            mutability::MutType,
            r#type::{FnType, Type, TypeVar},
        },
    };

    /// A generic callee, its declared scheme, and how one concrete call site instantiated it —
    /// everything specialization consumes, harvested from real lowering rather than hand-built.
    struct Site {
        body: Function,
        scheme: TypeScheme<FnType>,
        key: SpecializationKey,
    }

    impl Site {
        /// Specializes as the table would, at an identity past the module's own functions.
        fn specialize(&self, env: ModuleEnv<'_>) -> Function {
            let own = FunctionId {
                module: self.key.callee.module,
                function: LocalFunctionId::from_index(1000),
            };
            specialize(&self.body, &self.scheme, &self.key, own, env)
        }
    }

    fn compile(session: &mut CompilerSession, src: &str) -> ModuleId {
        session
            .compile_for(ExecutionTarget::Mir, src, "test", Path::single_str("test"))
            .expect("test source must compile")
            .module_id
    }

    /// A concrete dictionary method generated from a blanket implementation is a forwarding
    /// thunk. Its body calls the original generic method, so that call must carry the blanket
    /// match's instantiation just like a source-level generic call does. Without it the thunk is
    /// correct at runtime but specialization cannot see through the forwarding layer.
    #[test]
    fn blanket_method_thunk_records_and_uses_its_generic_instantiation() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module_id = compile(
            &mut session,
            "fn f(a: [[int]]) -> int { a[0][1] }\n\
             fn g() -> [int] { [0, 1, 2] |> map(|x| x + 1) }",
        );
        let module = session.expect_fresh_module(module_id);
        let thunk_id = (0..module.function_count())
            .map(LocalFunctionId::from_index)
            .find(|id| {
                module
                    .get_function_name_by_id(*id)
                    .is_some_and(|name| name.starts_with("std::Value<[std::int]>::clone#impl:"))
            })
            .expect("array Value materialization must create a concrete clone thunk");
        let thunk = session
            .mir_artifacts_for(module_id, MirOptimization::Disabled)
            .expect("raw MIR must be prepared")
            .get(thunk_id)
            .expect("the clone thunk must have a MIR body");

        let call = thunk
            .blocks()
            .flat_map(|block_id| {
                let block = thunk.block(block_id);
                block
                    .operations()
                    .iter()
                    .chain(match &block.terminator().kind {
                        TerminatorKind::Invoke { operation, .. } => Some(operation),
                        _ => None,
                    })
            })
            .find(|operation| matches!(operation.kind, OperationKind::Call { .. }))
            .expect("a blanket method thunk must forward to its generic method");
        let Value::Function(callee) = call.operands[0] else {
            panic!("the thunk must call a statically known generic method")
        };
        let callee_scheme = &session
            .expect_fresh_module(callee.module)
            .get_function_by_id(callee.function)
            .expect("the generic method must exist")
            .definition
            .ty_scheme;
        assert!(
            !callee_scheme.ty_quantifiers.is_empty(),
            "the forwarded method must be generic, or this test proves nothing"
        );
        let OperationKind::Call { metadata, .. } = &call.kind else {
            panic!("the thunk's generic call must record its instantiation")
        };
        let instantiation = metadata
            .as_deref()
            .and_then(|metadata| metadata.instantiation.as_ref())
            .expect("the thunk's generic call must record its instantiation");
        assert_eq!(
            instantiation.ty_args.len(),
            callee_scheme.ty_quantifiers.len()
        );
        assert_eq!(
            instantiation.eff_args.len(),
            callee_scheme.eff_quantifiers.len()
        );
        assert!(
            instantiation.ty_args.iter().all(Type::is_constant),
            "a concrete thunk must instantiate every generic type parameter concretely"
        );

        let from_iter_thunk_id = (0..module.function_count())
            .map(LocalFunctionId::from_index)
            .find(|id| {
                module.get_function_name_by_id(*id).is_some_and(|name| {
                    name.starts_with("std::FromIterator<[std::int],")
                        && name.contains("::from_iter#impl:")
                })
            })
            .expect("array collection must create a two-quantifier FromIterator thunk");
        let from_iter_thunk = session
            .mir_artifacts_for(module_id, MirOptimization::Disabled)
            .expect("raw MIR must be prepared")
            .get(from_iter_thunk_id)
            .expect("the FromIterator thunk must have a MIR body");
        let from_iter_instantiation = from_iter_thunk
            .blocks()
            .flat_map(|block_id| {
                let block = from_iter_thunk.block(block_id);
                block
                    .operations()
                    .iter()
                    .chain(match &block.terminator().kind {
                        TerminatorKind::Invoke { operation, .. } => Some(operation),
                        _ => None,
                    })
            })
            .find_map(|operation| match &operation.kind {
                OperationKind::Call { metadata, .. } => metadata
                    .as_deref()
                    .and_then(|metadata| metadata.instantiation.as_ref()),
                _ => None,
            })
            .expect("the two-quantifier forwarding call must record its instantiation");
        assert_eq!(from_iter_instantiation.ty_args.len(), 2);

        // Preparing optimized MIR verifies both recorded applications against their actual callee
        // schemes. In particular this catches swapping FromIterator's `[A, B]` to the equally
        // valid as a scheme, but positionally incompatible, `[B, A]`.
        // Closed dictionaries deliberately keep this concrete thunk open over its prerequisite
        // evidence. Preparing optimized MIR still verifies the recorded applications against the
        // original schemes; a caller with entirely static evidence may specialize the thunk, but
        // the module-owned open definition itself must remain valid for dynamic captures.
        let optimized = session.emit_mir_module(module_id);
        let thunk = optimized
            .split("fn std::Value<[std::int]>::clone#impl:")
            .nth(1)
            .and_then(|rest| rest.split("\nfn ").next())
            .expect("the open concrete thunk must remain");
        assert!(
            thunk.contains("from %p1"),
            "the open concrete thunk must still read its element evidence:\n{thunk}"
        );
    }

    fn body<'a>(session: &'a CompilerSession, module: ModuleId, name: &str) -> &'a Function {
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

    /// Finds the call to `callee_name` inside `caller_name` and collects what it instantiated.
    fn site(
        session: &CompilerSession,
        module: ModuleId,
        caller_name: &str,
        callee_name: &str,
    ) -> Site {
        let caller = body(session, module, caller_name);
        let wanted = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr(callee_name))
            .unwrap_or_else(|| panic!("no function named {callee_name}"));
        for block_id in caller.blocks() {
            let block = caller.block(block_id);
            let operations = block
                .operations()
                .iter()
                .chain(match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => Some(operation),
                    _ => None,
                });
            for operation in operations {
                let OperationKind::Call { ty, metadata } = &operation.kind else {
                    continue;
                };
                let Value::Function(callee) = &operation.operands[0] else {
                    continue;
                };
                if callee.module != module || callee.function != wanted {
                    continue;
                }
                let instantiation = metadata
                    .as_deref()
                    .and_then(|metadata| metadata.instantiation.as_ref())
                    .unwrap_or_else(|| {
                        panic!("the call to {callee_name} must record its instantiation")
                    })
                    .clone();
                // The operand layout the verifier assumes: callee, evidence, visible arguments,
                // result place.
                let visible_start = operation.operands.len() - (ty.fn_ty.args.len() + 1);
                let dictionaries = operation.operands[1..visible_start]
                    .iter()
                    .map(static_evidence_operand)
                    .collect::<Option<Vec<_>>>()
                    .unwrap_or_default();
                let scheme = session
                    .expect_fresh_module(module)
                    .get_function_by_id(wanted)
                    .expect("the callee is a function of this module")
                    .definition
                    .ty_scheme
                    .clone();
                return Site {
                    body: body(session, module, callee_name).clone(),
                    scheme,
                    key: SpecializationKey {
                        callee: *callee,
                        instantiation,
                        dictionaries,
                        callbacks: Vec::new(),
                    },
                };
            }
        }
        panic!("{caller_name} contains no call to {callee_name}");
    }

    /// Records every type and effect the traversal visits, returning each unchanged.
    #[derive(Default)]
    struct Collector {
        types: Vec<Type>,
        effects: Vec<EffType>,
    }

    impl TypeMapper for Collector {
        fn map_type(&mut self, ty: Type) -> Type {
            self.types.push(ty);
            ty
        }
        fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
            mut_ty
        }
        fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType {
            self.effects.push(eff_ty.clone());
            eff_ty.clone()
        }
    }

    /// The type variables still free anywhere in `func`.
    ///
    /// The signature and the constant pool are read from the function's own API, *not* through the
    /// traversal: sharing the traversal with what it checks is circular, and a version that skipped
    /// parameter types passed this test until they were read directly. What stays traversal-shared
    /// is the per-operation metadata, where the exhaustive `match` in
    /// [`substitute_in_operation`] gives coverage at compile time instead.
    fn free_ty_vars(func: &Function, env: ModuleEnv<'_>) -> Vec<TypeVar> {
        let mut collector = Collector::default();
        let mut edit = FunctionEdit::new(func.clone());
        map_types(&mut edit, &mut collector);
        edit.finish(env);
        func.parameters()
            .iter()
            .map(|parameter| parameter.ty)
            .chain(func.constants().iter().map(|constant| constant.ty))
            .chain(collector.types.iter().copied())
            .flat_map(|ty| ty.inner_ty_vars())
            .collect()
    }

    #[test]
    fn preflight_accepts_a_dictionary_entry_that_feeds_an_indirect_call() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn twice_it(x) { x + x }\n\
             fn use_it(n: int) -> int { twice_it(n) }",
        );
        let site = site(&session, module, "use_it", "twice_it");

        assert!(worth_specializing(
            &site.body,
            &site.scheme,
            &site.key.instantiation,
            &site.key.dictionaries,
            session.module_env(),
        ));
    }

    #[test]
    fn preflight_accepts_ownership_or_layout_simplification_without_an_indirect_call() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn swap(a, i, j) { let temp = a[i]; a[i] = a[j]; a[j] = temp }\n\
             fn swap_ints(a: [int], i: int, j: int) { let mut t = a; swap(t, i, j); t }",
        );
        let site = site(&session, module, "swap_ints", "swap");

        assert!(worth_specializing(
            &site.body,
            &site.scheme,
            &site.key.instantiation,
            &site.key.dictionaries,
            session.module_env(),
        ));
    }

    #[test]
    fn preflight_accepts_a_small_evidence_forwarder_that_specialization_makes_inlinable() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn inner<T>(x: T) -> T where T: Value { x }\n\
             fn outer<T>(x: T) -> T where T: Value { inner(x) }\n\
             fn use_it(x: string) -> string { outer(x) }",
        );
        let site = site(&session, module, "use_it", "outer");
        let dictionary_parameters: Vec<_> = site
            .body
            .parameters()
            .iter()
            .enumerate()
            .filter(|(_, parameter)| matches!(parameter.kind, ParameterKind::Dictionary))
            .map(|(index, _)| ParameterId::from_index(index))
            .collect();
        assert!(
            uses_any_parameter(&site.body, &dictionary_parameters),
            "the body must really forward evidence, or the old admission rule would reject it too"
        );
        assert!(worth_specializing(
            &site.body,
            &site.scheme,
            &site.key.instantiation,
            &site.key.dictionaries,
            session.module_env(),
        ));
    }

    #[test]
    fn preflight_accepts_a_large_forwarder_that_makes_an_inner_call_concrete() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn inner<T>(x: T) -> T where T: Value { x }\n\
             fn outer<T>(x: T) -> T where T: Value { inner(x) }\n\
             fn use_it(x: string) -> string { outer(x) }",
        );
        let mut site = site(&session, module, "use_it", "outer");
        let padding = budget::INLINE_CALLEE_COST + 1 - cost::hot_cost(&site.body);
        let entry = mir::BlockId::from_index(0);
        let span = site.body.block(entry).operations()[0].span;
        let mut edit = FunctionEdit::new(site.body);
        edit.block_mut(entry)
            .operations
            .extend((0..padding).map(|_| Operation::check_fuel(span)));
        site.body = edit.finish(session.module_env());

        assert!(cost::hot_cost(&site.body) > budget::INLINE_CALLEE_COST);
        assert!(worth_specializing(
            &site.body,
            &site.scheme,
            &site.key.instantiation,
            &site.key.dictionaries,
            session.module_env(),
        ));
    }

    #[test]
    fn preflight_rejects_a_body_with_no_remaining_specialization_exposure() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn inner<T>(x: T) -> T where T: Value { x }\n\
             fn outer<T>(x: T) -> T where T: Value { inner(x) }\n\
             fn use_it(x: string) -> string { outer(x) }",
        );
        let site = site(&session, module, "use_it", "outer");
        let specialized = site.specialize(session.module_env());

        assert!(!worth_specializing(
            &specialized,
            &site.scheme,
            &site.key.instantiation,
            &site.key.dictionaries,
            session.module_env(),
        ));
    }

    /// Specializing a generic body at a concrete call site leaves no type variable anywhere in it —
    /// and the result verifies, which is what makes evidence and types agree.
    #[test]
    fn specializing_a_generic_callee_makes_its_body_concrete() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn twice_it(x) { x + x }\n\
             fn use_it() -> int { twice_it(3) }",
        );
        let site = site(&session, module, "use_it", "twice_it");
        assert!(
            !free_ty_vars(&site.body, session.module_env()).is_empty(),
            "twice_it must be generic before specialization, or this test proves nothing"
        );

        let specialized = site.specialize(session.module_env());

        assert!(
            free_ty_vars(&specialized, session.module_env()).is_empty(),
            "no type variable may survive specialization at a concrete call site"
        );
    }

    #[test]
    fn specializations_with_different_zero_signs_are_distinct() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn with_zero(x) { (x, 0.0) }
fn use_it(x: int) { with_zero(x) }",
        );
        let site = site(&session, module, "use_it", "with_zero");
        let positive = site.specialize(session.module_env());
        let mut edit = FunctionEdit::new(positive.clone());
        let zero = edit
            .constants_mut()
            .iter_mut()
            .find(|constant| {
                constant
                    .representation
                    .as_primitive_ty::<Float>()
                    .is_some_and(|value| value.into_inner().to_bits() == 0.0f64.to_bits())
            })
            .expect("the specialization must contain positive zero");
        zero.representation = LiteralValue::new_native(Float::new(-0.0).unwrap());
        let negative = edit.finish(session.module_env());
        let canonical = |id| id;

        assert!(structurally_identical(
            &positive, &canonical, &positive, &canonical
        ));
        assert!(!structurally_identical(
            &positive, &canonical, &negative, &canonical
        ));
        assert_ne!(
            structure_digest(&positive, site.key.callee, &canonical),
            structure_digest(&negative, site.key.callee, &canonical),
        );
    }

    /// The other half: every use of a dictionary parameter becomes the constant the call site
    /// passes. That is what a later folding round resolves into a known function, turning the
    /// callee's indirect calls direct — the payoff specialization exists for.
    #[test]
    fn specializing_binds_the_dictionaries_the_call_site_passes() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn twice_it(x) { x + x }\n\
             fn use_it() -> int { twice_it(3) }",
        );
        let site = site(&session, module, "use_it", "twice_it");
        assert!(
            !site.key.dictionaries.is_empty(),
            "the call must pass constant evidence, or this test proves nothing"
        );
        let dictionary_parameters: Vec<ParameterId> = site
            .body
            .parameters()
            .iter()
            .enumerate()
            .filter(|(_, parameter)| matches!(parameter.kind, ParameterKind::Dictionary))
            .map(|(index, _)| ParameterId::from_index(index))
            .collect();
        assert!(
            uses_any_parameter(&site.body, &dictionary_parameters),
            "twice_it must read its evidence, or this test proves nothing"
        );

        let specialized = site.specialize(session.module_env());

        assert!(
            !uses_any_parameter(&specialized, &dictionary_parameters),
            "no use of a dictionary parameter may survive specialization"
        );
    }

    /// End to end through the driver, and the whole point of the phase: a concrete call to a
    /// generic callee is redirected to a specialized copy, which is concrete and therefore
    /// *inlinable* — so the caller ends up holding the callee's operations with its evidence
    /// resolved to a constant, where before it held an opaque call to a generic function.
    ///
    /// The argument is deliberately unknown. A *known* one lets folding const-evaluate the whole
    /// call instead, which is a better outcome and would hide what this test is about.
    #[test]
    fn a_concrete_call_is_specialized_and_then_inlined() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "spec",
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
            !caller.contains("call spec::twice_it"),
            "the generic callee must not survive as a call:\n{caller}"
        );
        assert!(
            caller.contains("call std::Num<std::int>::add"),
            "its body must arrive inlined, with the evidence it read resolved all the way to a \
             direct call on the concrete impl:\n{caller}"
        );
        assert!(
            !module.contains("fn twice_it#spec:[int]"),
            "and having been inlined into its only caller, the copy must not survive the \
             module: `prune_specializations` drops what nothing calls:\n{module}"
        );
    }

    #[test]
    fn a_call_forwarding_dynamic_evidence_is_not_specialized() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "dynamic",
            "fn inner<T>(value: T) -> T where T: Value { let copy = value; copy }\n\
             fn outer<T>(value: T) -> T where T: Value { inner(value) }",
        );
        let caller = module
            .split("fn outer")
            .nth(1)
            .expect("the module defines outer")
            .split("\nfn ")
            .next()
            .expect("outer has a body");
        assert!(
            caller.contains("call dynamic::inner(%p0"),
            "the open caller must keep forwarding its dynamic evidence:\n{caller}"
        );
        assert!(
            !module.contains("fn inner#spec:"),
            "dynamic evidence must not produce a partial specialization:\n{module}"
        );
    }

    /// A generic body allocates and moves dynamically-sized storage through a `Value` dictionary
    /// witnessing the layout its type variable hides. Substitution is what makes that type
    /// statically sized, so the witness must go with it — otherwise the specialization keeps a live
    /// use of the dictionary, and a backend would emit a dynamically-sized allocation for a value
    /// whose size it knows.
    #[test]
    fn substitution_drops_the_layout_witnesses_it_makes_redundant() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        // `swap` is generic in the element type, so its temporary is allocated through a witness.
        let module = session.emit_mir(
            "wit",
            "fn swap(a, i, j) { let temp = a[i]; a[i] = a[j]; a[j] = temp }\n\
             fn swap_ints(a: [int], i: int, j: int) { let mut t = a; swap(t, i, j); t }",
        );
        let caller = module
            .split("fn swap_ints")
            .nth(1)
            .expect("the module defines swap_ints")
            .split("\nfn ")
            .next()
            .expect("swap_ints has a body");
        assert!(
            caller.contains("memcpy"),
            "the generic swap body must be specialized or inlined into its concrete caller:\n{caller}"
        );
        assert!(
            !caller.contains("using dict"),
            "the concrete caller must carry no dynamic layout witness:\n{caller}"
        );
        for specialized in module.split("// specialization of ").skip(1) {
            assert!(
                !specialized.contains("using dict"),
                "a specialized body must carry no layout witness for a concrete type:\n\
                 {specialized}"
            );
        }
    }

    #[test]
    fn substitution_drops_variant_layout_witnesses_it_makes_redundant() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "enum Boxed<T> { Empty, Item(T) }\n\
             fn wrap<T>(x: T) -> Boxed<T> where T: Value { Boxed::Item(x) }\n\
             fn unwrap_or<T>(x: Boxed<T>, fallback: T) -> T where T: Value {\n\
                 match x { Boxed::Item(value) => value, Boxed::Empty => fallback }\n\
             }\n\
             fn wrap_int(x: int) -> Boxed<int> { wrap(x) }\n\
             fn unwrap_int(x: Boxed<int>, fallback: int) -> int { unwrap_or(x, fallback) }",
        );

        let construction =
            site(&session, module, "wrap_int", "wrap").specialize(session.module_env());
        let mut saw_construction = false;
        let mut saw_construction_projection = false;
        for block in construction.blocks() {
            for operation in construction.block(block).operations() {
                match &operation.kind {
                    OperationKind::Variant {
                        has_layout_witness, ..
                    } => {
                        saw_construction = true;
                        assert!(!has_layout_witness);
                    }
                    OperationKind::Subfield {
                        variant_payload: true,
                        has_layout_witness,
                        ..
                    } => {
                        saw_construction_projection = true;
                        assert!(!has_layout_witness);
                    }
                    _ => {}
                }
            }
        }
        assert!(saw_construction && saw_construction_projection);

        let projection =
            site(&session, module, "unwrap_int", "unwrap_or").specialize(session.module_env());
        let projections = projection
            .blocks()
            .flat_map(|block| projection.block(block).operations())
            .filter_map(|operation| match operation.kind {
                OperationKind::Subfield {
                    variant_payload: true,
                    has_layout_witness,
                    ..
                } => Some(has_layout_witness),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(!projections.is_empty());
        assert!(projections.iter().all(|witness| !witness));
    }

    #[test]
    fn substitution_drops_product_layout_witnesses_it_makes_redundant() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn second<A, B>(value: (A, B)) -> B { value.1 }\n\
             fn second_int(value: (int, int)) -> int { second(value) }",
        );

        let site = site(&session, module, "second_int", "second");
        assert!(worth_specializing(
            &site.body,
            &site.scheme,
            &site.key.instantiation,
            &site.key.dictionaries,
            session.module_env(),
        ));
        let specialized = site.specialize(session.module_env());
        let projections = specialized
            .blocks()
            .flat_map(|block| specialized.block(block).operations())
            .filter_map(|operation| match &operation.kind {
                OperationKind::Subfield {
                    product: Some(product),
                    ..
                } => Some((product.layout_witness_tys.len(), operation.operands.len())),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(!projections.is_empty());
        assert!(
            projections
                .iter()
                .all(|(witnesses, operands)| *witnesses == 0 && *operands == 2)
        );
    }

    /// A generic body copies and releases through `Value::clone` and `Value::drop`, because it
    /// cannot know whether its type owns anything. Substitution answers that, and when the answer is
    /// "nothing", the clone becomes a `memcpy` and the drop goes — leaving the dictionary entries
    /// they read unread, for `dce` to remove.
    #[test]
    fn substitution_turns_trivial_clones_and_drops_into_representation_copies() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "own",
            "fn swap(a, i, j) { let temp = a[i]; a[i] = a[j]; a[j] = temp }\n\
             fn swap_ints(a: [int], i: int, j: int) { let mut t = a; swap(t, i, j); t }",
        );
        let specialized = module
            .split("fn swap_ints")
            .nth(1)
            .expect("the module defines swap_ints")
            .split("\nfn ")
            .next()
            .expect("swap_ints has a body");
        assert!(
            specialized.contains("memcpy"),
            "a clone of a now-trivially-copyable type becomes a representation copy:\n{specialized}"
        );
        for spelling in ["clone int ", "drop int ", "dict_entry", "replace "] {
            assert!(
                !specialized.contains(spelling),
                "no `{spelling}` may survive for a type that owns nothing:\n{specialized}"
            );
        }
    }

    #[test]
    fn specialized_assignment_matches_direct_trivial_assignment() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "assignment",
            "fn set<A>(a: &mut A, b: A) { a = b }\n\
             fn ints(a: &mut int, b: int) { set(a, b) }\n\
             fn direct(a: &mut int, b: int) { a = b }\n\
             fn strings(a: &mut string, b: string) { set(a, b) }",
        );
        let body = |name: &str| {
            module
                .split(&format!("fn {name}("))
                .nth(1)
                .expect("function exists")
                .split("\nfn ")
                .next()
                .unwrap()
                .trim()
        };
        assert_eq!(body("ints"), body("direct"));
        assert!(body("ints").contains("memcpy %p1 to %p0"));
        let managed = body("strings");
        assert!(managed.find("replace ").unwrap() < managed.find("drop string ").unwrap());
    }

    /// The assigned value may be computed into its temporary by a call rather than a copy; the
    /// displaced value is equally unobserved, so the replacement must become a move there too.
    #[test]
    fn specialized_computed_assignment_matches_direct_trivial_assignment() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "assignment",
            "fn add_to(a, b) { a = a + b }\n\
             fn ints(a: &mut int, b: int) { add_to(a, b) }\n\
             fn direct(a: &mut int, b: int) { a = a + b }",
        );
        let body = |name: &str| {
            module
                .split(&format!("fn {name}("))
                .nth(1)
                .expect("function exists")
                .split("\nfn ")
                .next()
                .unwrap()
                .trim()
        };
        assert!(!body("ints").contains("replace "), "{}", body("ints"));
        assert_eq!(body("ints"), body("direct"));
    }

    #[test]
    fn specialization_preserves_an_observed_displaced_value() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn set<A>(a: &mut A, b: A) { a = b }\n\
             fn ints(a: &mut int, b: int) { set(a, b) }",
        );
        let mut site = site(&session, module, "ints", "set");
        let mut edit = FunctionEdit::new(site.body);
        let block = edit.blocks().next().unwrap();
        let (index, replacement) = edit
            .block(block)
            .operations
            .iter()
            .enumerate()
            .find(|(_, op)| matches!(op.kind, OperationKind::Replace))
            .map(|(index, op)| (index, op.clone()))
            .unwrap();
        // Even an initialization-state observation distinguishes replace from move.
        let mut observation =
            Operation::is_initialized(replacement.span, replacement.operands[0].clone());
        edit.assign_new_result(&mut observation);
        edit.block_mut(block)
            .operations
            .insert(index + 1, observation);
        site.body = edit.finish(session.module_env());
        let specialized = site.specialize(session.module_env());
        assert!(specialized.blocks().any(|block| {
            specialized
                .block(block)
                .operations()
                .iter()
                .any(|op| matches!(op.kind, OperationKind::Replace))
        }));
    }

    /// The point of `builtin::init_place`: with a container's element copy expressed in MIR rather
    /// than inside a native holding a runtime dictionary, substituting a trivially copyable element
    /// type turns that copy into a representation copy.
    ///
    /// Asserted through `array_append` because that is the case the measurement named, and because
    /// the property is not local — the clone is written in `array.fer` and only becomes a `memcpy`
    /// after specialization has substituted `A := int` and the clone-elision pass has run. A
    /// `Value::clone` call surviving here means the copy went back to being opaque.
    #[test]
    fn appending_a_trivially_copyable_element_becomes_a_representation_copy() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "append",
            "fn grow(n: int) -> [int] { let mut a = []; array_append(a, n); a }",
        );
        // The specialization, or `grow` once that specialization is inlined into it.
        let specialized = module
            .split("fn array_append#spec:[int]")
            .nth(1)
            .or_else(|| module.split("fn grow(").nth(1))
            .expect("the module declares `grow`")
            .split("\nfn ")
            .next()
            .expect("the specialization has a body");
        assert!(
            specialized.contains("memcpy"),
            "the element copy must be a representation copy:\n{specialized}"
        );
        assert!(
            !specialized.contains("buffer_clone_value_into"),
            "the element copy must not go back through the opaque native:\n{specialized}"
        );
    }

    /// Distinct keys whose substitutions erase to the same MIR body share one specialization.
    #[test]
    fn call_sites_separated_only_by_erased_effects_share_one_specialization() {
        let mut session = CompilerSession::new();
        let module_id = compile(&mut session, "fn identity(value: int) -> int { value }");
        let (function, function_count, mut scheme) = {
            let module = session.expect_fresh_module(module_id);
            let function = module
                .get_local_function_id(ustr("identity"))
                .expect("identity was just compiled");
            let scheme = module
                .get_function_by_id(function)
                .expect("identity was just compiled")
                .definition
                .ty_scheme
                .clone();
            (function, module.function_count(), scheme)
        };
        session.prepare_execution_target(ExecutionTarget::Mir, module_id);
        let body = body(&session, module_id, "identity").clone();
        scheme.eff_quantifiers.insert(EffectVar::new(0));
        let callee = FunctionId::new(module_id, function);
        let key = |effects| SpecializationKey {
            callee,
            instantiation: Instantiation {
                ty_args: Vec::new(),
                eff_args: vec![effects],
            },
            dictionaries: Vec::new(),
            callbacks: Vec::new(),
        };
        let mut specializations = Specializations::new(module_id, function_count, 1);
        let pure = specializations.get_or_create(
            key(EffType::empty()),
            &scheme,
            &body,
            session.module_env(),
        );
        let reading = specializations.get_or_create(
            key(EffType::single_primitive(PrimitiveEffect::Read)),
            &scheme,
            &body,
            session.module_env(),
        );

        assert_eq!(pure, reading);
        assert_eq!(specializations.len(), 1);
    }

    #[test]
    fn cross_module_erased_effect_keys_share_rebased_inline_locations() {
        use crate::{Location, mir::debug_location::InlineSite};

        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let dependency = session
            .compile_for(
                ExecutionTarget::Mir,
                "fn helper(x) { x + x } \
             pub fn callee(x: int) -> int { helper(x) }",
                "dependency.fer",
                Path::single_str("dependency"),
            )
            .unwrap()
            .module_id;
        session.prepare_execution_target(ExecutionTarget::Mir, dependency);
        let function = session
            .expect_fresh_module(dependency)
            .get_local_function_id(ustr("callee"))
            .unwrap();
        let body = session
            .mir_artifacts_for(dependency, MirOptimization::Enabled)
            .unwrap()
            .get(function)
            .unwrap()
            .clone();
        let mut source_inline = None;
        let mut inspect = FunctionEdit::new(body.clone());
        inspect.visit_spans_mut(|span| source_inline = source_inline.or(span.inlined_at));
        let source_inline = source_inline.unwrap_or_else(|| {
            panic!(
                "dependency must contain genuinely inlined code:\n{}",
                body.format_with(&session.module_env())
            )
        });
        let mut scheme = session
            .expect_fresh_module(dependency)
            .get_function_by_id(function)
            .unwrap()
            .definition
            .ty_scheme
            .clone();
        assert!(scheme.eff_quantifiers.is_empty());
        scheme.eff_quantifiers.insert(EffectVar::new(0));

        let destination = compile(&mut session, "fn dummy(x: int) -> int { x }");
        let env = session.module_env();
        let source_sites = env.inline_sites(dependency).borrow().len();
        // Ensure source ids cannot happen to equal their destination ids.
        let mut sites = env.inline_sites(destination).borrow_mut();
        let mut parent = None;
        for _ in 0..=source_sites {
            parent = Some(sites.intern(InlineSite {
                call: Location::new_synthesized(),
                parent,
            }));
        }
        drop(sites);
        let key = |effects| SpecializationKey {
            callee: FunctionId::new(dependency, function),
            instantiation: Instantiation {
                ty_args: Vec::new(),
                eff_args: vec![effects],
            },
            dictionaries: Vec::new(),
            callbacks: Vec::new(),
        };
        let mut table = Specializations::new(
            destination,
            session.expect_fresh_module(destination).function_count(),
            1,
        );
        let pure = table.get_or_create(key(EffType::empty()), &scheme, &body, env);
        let moved_sites = env.inline_sites(destination).borrow().len();
        let mut rebased = None;
        let mut inspect = FunctionEdit::new(table.raw[0].clone());
        inspect.visit_spans_mut(|span| rebased = rebased.or(span.inlined_at));
        assert_ne!(rebased.unwrap(), source_inline);
        let reading = table.get_or_create(
            key(EffType::single_primitive(PrimitiveEffect::Read)),
            &scheme,
            &body,
            env,
        );
        assert_eq!(
            pure, reading,
            "equivalent dependency bodies must share after relocation"
        );
        assert_eq!(table.len(), 1);
        assert_eq!(
            env.inline_sites(destination).borrow().len(),
            moved_sites,
            "duplicate relocation reuses interned inline sites"
        );
    }

    /// Publishing a callee ends what was decided from its raw body; the copy already made stays.
    #[test]
    fn publishing_a_callee_forgets_decisions_taken_from_its_raw_body() {
        let mut session = CompilerSession::new();
        let module_id = compile(&mut session, "fn identity(value: int) -> int { value }");
        let (function, function_count, scheme) = {
            let module = session.expect_fresh_module(module_id);
            let function = module
                .get_local_function_id(ustr("identity"))
                .expect("identity was just compiled");
            let scheme = module
                .get_function_by_id(function)
                .expect("identity was just compiled")
                .definition
                .ty_scheme
                .clone();
            (function, module.function_count(), scheme)
        };
        session.prepare_execution_target(ExecutionTarget::Mir, module_id);
        let body = body(&session, module_id, "identity").clone();
        let callee = FunctionId::new(module_id, function);
        let key = |effects| SpecializationKey {
            callee,
            instantiation: Instantiation {
                ty_args: Vec::new(),
                eff_args: vec![effects],
            },
            dictionaries: Vec::new(),
            callbacks: Vec::new(),
        };
        let mut specializations = Specializations::new(module_id, function_count, 1);
        let created = key(EffType::empty());
        let rejected = key(EffType::single_primitive(PrimitiveEffect::Read));
        specializations.get_or_create(created.clone(), &scheme, &body, session.module_env());
        specializations.reject(rejected.clone());

        specializations.finish(vec![(function, body)]);

        assert!(specializations.cached(&created).is_none());
        assert!(!specializations.is_rejected(&rejected));
        assert_eq!(specializations.len(), 1);
    }

    /// A specialization created from a final body is read optimized once it was optimized ahead of
    /// the worklist, unless that optimization read a body that is not final yet; one created from
    /// a raw body waits for the worklist.
    #[test]
    fn a_specialization_is_read_optimized_only_when_everything_it_read_was_final() {
        let mut session = CompilerSession::new();
        let module_id = compile(
            &mut session,
            "fn identity(value: int) -> int { value }\n\
             fn twice(value: int) -> int { value + value }\n\
             fn unfinished(value: int) -> int { value - 1 }",
        );
        let (ids, function_count, schemes) = {
            let module = session.expect_fresh_module(module_id);
            let ids = ["identity", "twice", "unfinished"].map(|name| {
                module
                    .get_local_function_id(ustr(name))
                    .expect("the function was just compiled")
            });
            let schemes = ids.map(|id| {
                module
                    .get_function_by_id(id)
                    .expect("the function was just compiled")
                    .definition
                    .ty_scheme
                    .clone()
            });
            (ids, module.function_count(), schemes)
        };
        session.prepare_execution_target(ExecutionTarget::Mir, module_id);
        let bodies =
            ["identity", "twice", "unfinished"].map(|name| body(&session, module_id, name).clone());
        let key = |index: usize| SpecializationKey {
            callee: FunctionId::new(module_id, ids[index]),
            instantiation: Instantiation {
                ty_args: Vec::new(),
                eff_args: Vec::new(),
            },
            dictionaries: Vec::new(),
            callbacks: Vec::new(),
        };
        let env = session.module_env();
        let mut specializations = Specializations::new(module_id, function_count, 3);
        let from_raw = specializations.get_or_create(key(2), &schemes[2], &bodies[2], env);
        specializations.finish(vec![
            (ids[0], bodies[0].clone()),
            (ids[1], bodies[1].clone()),
        ]);
        let settled = specializations.get_or_create(key(0), &schemes[0], &bodies[0], env);
        let unsettled = specializations.get_or_create(key(1), &schemes[1], &bodies[1], env);
        let spec = |id| FunctionId::new(module_id, id);
        assert!(!specializations.is_ready(spec(from_raw)));
        assert!(specializations.needs_worklist(from_raw));

        // Stands in for the optimized body, which the table does not look into.
        let marker = bodies[2].clone();
        let marker_name = marker.name;
        let (_, frame) = specializations.begin_ahead(settled);
        assert!(specializations.end_ahead(settled, marker.clone(), frame, Default::default()));
        assert!(!specializations.needs_worklist(settled));
        assert_eq!(
            specializations.callee_body(settled).map(|body| body.name),
            Some(marker.name)
        );

        let (_, frame) = specializations.begin_ahead(unsettled);
        SemanticCallees::new(&session, Some(&specializations))
            .body(FunctionId::new(module_id, ids[2]))
            .expect("an unfinished function is read raw");
        assert!(specializations.abandons_ahead());
        assert!(!specializations.end_ahead(unsettled, marker, frame, Default::default()));
        assert!(specializations.needs_worklist(unsettled));
        assert_ne!(
            specializations.callee_body(unsettled).map(|body| body.name),
            Some(marker_name)
        );
    }

    /// A recursive call records no instantiation — inference types a call within the defining group
    /// monomorphically rather than instantiating the scheme — so nothing else can redirect it. Left
    /// alone a specialization recurses into the generic original, and for a recursive algorithm
    /// every level below the first runs unspecialized.
    #[test]
    fn a_specialization_recurses_into_itself() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session.emit_mir(
            "rec",
            "fn count_down(a, n) { if n <= 0 { a } else { count_down(a, n - 1) } }\n\
             fn run(n: int) -> int { count_down(7, n) }",
        );
        let specialized = module
            .split("// specialization of ")
            .nth(1)
            .expect("count_down must specialize");
        assert!(
            specialized.contains("count_down#spec:"),
            "the recursive call must name the specialization:\n{specialized}"
        );
        assert!(
            !specialized.contains("call rec::count_down("),
            "and must not fall back into the generic original:\n{specialized}"
        );
    }

    /// Substituting effects changes *control flow*, not only annotations.
    ///
    /// A call whose effects are a variable is conservatively source-fallible, so lowering gives it
    /// an `invoke` and an error edge. Instantiating that variable at a concrete effect set can make
    /// it infallible, and MIR requires the form to agree — the verifier rejects a body where they
    /// disagree, which is how this was found. `ho` is the shape: a higher-order function whose
    /// callee's effects it does not know.
    #[test]
    fn an_invoke_that_substitution_makes_infallible_becomes_a_plain_call() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        // Compiling at all is the assertion: every specialized body goes through `verify_function`,
        // which is what rejected this before `demote_infallible_invokes` existed. `ho` is never
        // inlined so the copy survives into the final artifact and is verified in its own right —
        // inlined into its only caller, it would be pruned as unreachable and only the splice
        // would be checked.
        let module = session.emit_mir(
            "spec",
            "#[inline(never)]\n\
             fn ho(f, x) { match f(x) { 1 => 10, 2 => 20, 3 => 30, 4 => 40, 5 => 50, \
             6 => 60, 7 => 70, 8 => 80, _ => 90 } }\n\
             fn use_it(n: int) -> int { ho(|z| z, n) }",
        );
        assert!(
            module.contains("#spec:"),
            "the higher-order caller must specialize, or this test proves nothing:\n{module}"
        );
    }

    /// Two hand-written functions prove the mechanism; the standard library proves it survives real
    /// code. Every call site in std that names a generic callee, records an instantiation and passes
    /// constant evidence is specialized here, and each result goes through `verify_function`.
    ///
    /// This is the check that would catch a type field the traversal misses: the toy cases exercise
    /// `alloca`, `call` and `subfield`, while std reaches variants, closures, subscripts and
    /// dictionaries at depth. Asserting a floor on the count rather than an exact number — the
    /// figure moves with the standard library, and what matters is that the population is large and
    /// none of it fails.
    #[test]
    fn every_specializable_call_site_in_std_specializes() {
        let session = CompilerSession::new();
        let (std_id, _) = session
            .modules()
            .get_by_path(&Path::single_str("std"))
            .expect("the standard library is always registered");
        ensure_mir_artifacts(session.raw_modules(), std_id);
        let artifacts = session
            .mir_artifacts_for(std_id, MirOptimization::Disabled)
            .expect("std MIR must be prepared");
        let module = session.expect_fresh_module(std_id);

        let mut specialized = 0;
        for caller in artifacts.bodies().iter().flatten() {
            for block_id in caller.blocks() {
                let block = caller.block(block_id);
                let operations = block
                    .operations()
                    .iter()
                    .chain(match &block.terminator().kind {
                        TerminatorKind::Invoke { operation, .. } => Some(operation),
                        _ => None,
                    });
                for operation in operations {
                    let OperationKind::Call { ty, metadata } = &operation.kind else {
                        continue;
                    };
                    let Some(instantiation) = metadata
                        .as_deref()
                        .and_then(|metadata| metadata.instantiation.as_ref())
                    else {
                        continue;
                    };
                    // Intra-module only: another module's scheme and body would need its own env.
                    let Value::Function(callee) = &operation.operands[0] else {
                        continue;
                    };
                    if callee.module != std_id {
                        continue;
                    }
                    let Some(body) = artifacts.get(callee.function) else {
                        continue; // a native has no body to specialize
                    };
                    let scheme = &module
                        .get_function_by_id(callee.function)
                        .expect("a call names a function of its module")
                        .definition
                        .ty_scheme;
                    if scheme.ty_quantifiers.is_empty() {
                        continue; // not generic: nothing to substitute
                    }

                    let visible_start = operation.operands.len() - (ty.fn_ty.args.len() + 1);
                    let Some(dictionaries) = operation.operands[1..visible_start]
                        .iter()
                        .map(static_evidence_operand)
                        .collect::<Option<Vec<_>>>()
                    else {
                        continue; // the caller forwards evidence of its own
                    };

                    let key = SpecializationKey {
                        callee: *callee,
                        instantiation: instantiation.clone(),
                        dictionaries,
                        callbacks: Vec::new(),
                    };
                    let own = FunctionId {
                        module: std_id,
                        function: LocalFunctionId::from_index(artifacts.bodies().len()),
                    };
                    specialize(body, scheme, &key, own, session.module_env());
                    specialized += 1;
                }
            }
        }

        // Raw-MIR census: 180 before Ord predicates, 76 afterwards. The entire
        // difference is 19 lt + 41 le + 22 gt + 22 ge sites; all other counts agree.
        // This census does not filter on call-depth guards or inlining eligibility.
        assert!(
            specialized > 50,
            "specialized only {specialized} std call sites; the population should be in the \
             dozens even with concrete Ord predicates, so this is a lowering or harvesting regression"
        );
    }

    /// Every specialization the report prices must have been priced against a body it found.
    ///
    /// The comparison reaches for the original in *its own* module and falls back to zero when there
    /// is none, which is right for a report that must never bring a session down — and is also how
    /// the instrument would fail silently. A missing baseline reads as "removed nothing", so a
    /// lookup that quietly stopped working would report the whole population as inert and invite
    /// exactly the wrong conclusion about specialization's value. Asserted over std because
    /// cross-module specialization is what makes the lookup non-trivial: the original of a
    /// specialization in a user module lives in `std`, not where the copy does.
    #[test]
    fn every_specialization_is_priced_against_a_body_that_was_found() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let (std_id, _) = session
            .modules()
            .get_by_path(&Path::single_str("std"))
            .expect("the standard library is always registered");
        let report = session.optimization_report(std_id);
        assert!(
            !report.specializations.is_empty(),
            "std must specialize something, or this test proves nothing"
        );
        for specialization in &report.specializations {
            assert!(
                specialization.size > 0 && specialization.original_size > 0,
                "{} is priced at {} operations against an original of {}, so the original was \
                 not found and every payoff figure for it is meaningless",
                specialization.name,
                specialization.size,
                specialization.original_size,
            );
        }
    }

    #[test]
    fn callback_descriptors_are_shared_until_callee_publication() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            r#"
            #[inline(never)] fn apply(f, x: int) -> int { let mut result = x; for i in (0..x) { result = f(result) }; result }
            #[inline(never)] fn forwarding(f, x: int) -> int { apply(f, x) }
            "#,
        );
        let callee = FunctionId::new(
            module,
            session
                .expect_fresh_module(module)
                .get_local_function_id(ustr("apply"))
                .unwrap(),
        );
        let mut table = Specializations::new(
            module,
            session.expect_fresh_module(module).function_count(),
            2,
        );
        assert_eq!(table.invoked_callbacks(callee, &session).unwrap().len(), 1);
        table.read_unsettled.set(false);
        assert_eq!(table.invoked_callbacks(callee, &session).unwrap().len(), 1);
        assert!(
            table.read_unsettled.get(),
            "cached raw summaries remain dependencies"
        );
        assert_eq!(table.callback_parameters.borrow().len(), 1);
        table.finish(vec![(
            callee.function,
            body(&session, module, "forwarding").clone(),
        )]);
        assert!(table.callback_parameters.borrow().is_empty());
        assert!(
            table
                .invoked_callbacks(callee, &session)
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn callback_sub_budget_preserves_type_capacity_and_survives_publication() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            r#"
            #[inline(never)] fn apply(f, x: int) -> int {
                let mut result = x;
                for i in (0..x) { result = f(result) };
                result
            }
            fn inc(x: int) -> int { x + 1 }
            fn dec(x: int) -> int { x - 1 }
            fn first(x: int) -> int { apply(inc, x) }
            fn same(x: int) -> int { apply(inc, x) }
            fn other(x: int) -> int { apply(dec, x) }
            #[inline(never)] fn late(x) { x + x }
            fn typed(x: int) -> int { late(x) }
            "#,
        );
        let mut table = Specializations::new(
            module,
            session.expect_fresh_module(module).function_count(),
            8,
        );
        table.limit = 3;
        table.callback_limit = 1;
        for name in ["first", "same"] {
            assert!(
                specialize_call_sites(
                    body(&session, module, name),
                    session.module_env(),
                    &session,
                    module,
                    &mut table,
                )
                .is_some()
            );
        }
        assert_eq!(table.callback_created, 1);
        assert!(table.callbacks_full());
        assert!(!table.is_full());
        let late = site(&session, module, "typed", "late");
        assert!(
            specialize_call_sites(
                body(&session, module, "typed"),
                session.module_env(),
                &session,
                module,
                &mut table,
            )
            .is_some()
        );
        assert!(table.cached(&late.key).is_some());
        assert_eq!(table.len(), 2);
        let apply = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("apply"))
            .unwrap();
        table.finish(vec![(apply, body(&session, module, "apply").clone())]);
        assert!(
            table.callbacks_full(),
            "publication must not renew the allowance"
        );
        assert!(
            specialize_call_sites(
                body(&session, module, "other"),
                session.module_env(),
                &session,
                module,
                &mut table,
            )
            .is_none()
        );
        assert_eq!(table.len(), 2);
    }

    #[test]
    fn callback_growth_prices_whole_bodies_and_survives_publication() {
        for padding in [0, 64] {
            let mut source = String::from(
                "#[inline(never)] fn apply(f, x: int) -> int { let mut a = x; \
                 for i in 0..x { a = f(a);",
            );
            for n in 0..padding {
                source.push_str(&format!("a = rem(a * 17 + {n}, 100003);"));
            }
            source.push_str("}; a }\n");
            for n in 0..129 {
                source.push_str(&format!(
                    "fn cb{n}(x: int) -> int {{ x + {n} }} \
                     fn caller{n}(x: int) -> int {{ apply(cb{n}, x) }}\n"
                ));
            }
            let mut session = CompilerSession::new();
            let module = compile(&mut session, &source);
            let mut table = Specializations::new(
                module,
                session.expect_fresh_module(module).function_count(),
                20,
            );
            table.callback_limit = 256;
            for n in 0..128 {
                specialize_call_sites(
                    body(&session, module, &format!("caller{n}")),
                    session.module_env(),
                    &session,
                    module,
                    &mut table,
                );
            }
            if padding == 0 {
                assert!(
                    table.callback_created > 8,
                    "cheap copies must exceed the count floor"
                );
            } else {
                assert_eq!(table.callback_created, 2);
            }
            assert!(
                !table.callbacks_full(),
                "size, not count, must refuse the next copy"
            );
            let admitted = table.callback_created;
            let family = table.callback_growth.keys().next().unwrap().clone();
            let spent = table.callback_growth[&family].spent;
            let allowance = table.callback_growth[&family].allowance;
            assert!(spent <= allowance);
            let last = table.callback_growth[&family].last_admitted.unwrap();
            assert!(last > allowance - spent);
            if padding == 0 {
                assert_eq!(allowance, budget::MIN_CALLBACK_GROWTH);
            }
            let mut unseen = family.clone();
            let parameter = visible_parameters(body(&session, module, "apply").parameters())[0];
            let cb128 = session
                .expect_fresh_module(module)
                .get_local_function_id(ustr("cb128"))
                .unwrap();
            unseen
                .callbacks
                .push((parameter, FunctionId::new(module, cb128)));
            assert!(!table.callback_growth_allows(&unseen));
            // Repeated keys are free even after the family's allowance is exhausted.
            assert!(
                specialize_call_sites(
                    body(&session, module, "caller0"),
                    session.module_env(),
                    &session,
                    module,
                    &mut table,
                )
                .is_some()
            );
            assert_eq!(table.callback_growth[&family].spent, spent);
            table.finish(vec![(
                family.callee.function,
                body(&session, module, "apply").clone(),
            )]);
            assert_eq!(table.callback_growth[&family].spent, spent);
            assert_eq!(table.callback_growth[&family].allowance, allowance);
            assert!(
                specialize_call_sites(
                    body(&session, module, "caller128"),
                    session.module_env(),
                    &session,
                    module,
                    &mut table,
                )
                .is_none()
            );
            assert_eq!(table.callback_created, admitted);
            assert!(!table.callback_growth_allows(&unseen));
        }
    }

    #[test]
    fn structurally_shared_callback_bodies_are_charged_once() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            r#"
            fn apply(f: (int) -> int, x: int) -> int { x }
            fn inc(x: int) -> int { x + 1 }
            fn caller(x: int) -> int { apply(inc, x) }
        "#,
        );
        let mut site = site(&session, module, "caller", "apply");
        // An unused effect quantifier creates distinct keys with identical residual bodies.
        site.scheme.eff_quantifiers.insert(EffectVar::new(100));
        let parameter = visible_parameters(site.body.parameters())[0];
        let inc = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("inc"))
            .unwrap();
        site.key
            .callbacks
            .push((parameter, FunctionId::new(module, inc)));
        site.key.instantiation.eff_args.push(EffType::empty());
        let mut table = Specializations::new(
            module,
            session.expect_fresh_module(module).function_count(),
            3,
        );
        let first = table
            .get_or_create_callback(
                site.key.clone(),
                &site.scheme,
                &site.body,
                session.module_env(),
            )
            .unwrap();
        let spent = table.callback_growth.values().next().unwrap().spent;
        *site.key.instantiation.eff_args.last_mut().unwrap() =
            EffType::single_primitive(PrimitiveEffect::Read);
        let second = table
            .get_or_create_callback(site.key, &site.scheme, &site.body, session.module_env())
            .unwrap();
        assert_eq!(first, second);
        assert_eq!(table.callback_created, 1);
        assert_eq!(table.callback_growth.len(), 1);
        assert_eq!(table.callback_growth.values().next().unwrap().spent, spent);
    }

    #[test]
    fn callback_growth_refusal_can_create_a_new_type_copy() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            r#"
            #[inline(never)] fn apply(f, x) {
                let mut a = x;
                for i in 0..3 { a = f(a) + x };
                a
            }
            fn inc(x: int) -> int { x + 1 }
            fn caller(x: int) -> int { apply(inc, x) }
            fn inc_float(x: float) -> float { x + 1.0 }
            fn float_caller(x: float) -> float { apply(inc_float, x) }
        "#,
        );
        let site = site(&session, module, "caller", "apply");
        let mut table = Specializations::new(
            module,
            session.expect_fresh_module(module).function_count(),
            3,
        );
        table.callback_growth.insert(
            site.key.clone(),
            CallbackGrowth {
                allowance: 0,
                spent: 0,
                last_admitted: None,
            },
        );
        assert!(
            specialize_call_sites(
                body(&session, module, "caller"),
                session.module_env(),
                &session,
                module,
                &mut table,
            )
            .is_some()
        );
        assert_eq!(table.callback_created, 0);
        assert_eq!(table.len(), 1);
        assert!(table.cached(&site.key).is_some());
        // A different type/evidence family has its own allowance.
        assert!(
            specialize_call_sites(
                body(&session, module, "float_caller"),
                session.module_env(),
                &session,
                module,
                &mut table,
            )
            .is_some()
        );
        assert_eq!(table.callback_created, 1);
    }

    #[test]
    fn callback_admission_requires_repeated_invocation_of_the_bound_parameter() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            r#"
            fn once(f, x: int) -> int { f(x) }
            fn mixed(f, g, n: int, x: int) -> int {
                let mut result = g(x);
                for i in (0..n) { result = f(result) };
                result
            }
            "#,
        );
        for (name, expected) in [
            ("once", vec![]),
            ("mixed", vec![ParameterId::from_index(0)]),
        ] {
            let id = session
                .expect_fresh_module(module)
                .get_local_function_id(ustr(name))
                .unwrap();
            let parameters = repeated_callback_parameters(
                body(&session, module, name),
                FunctionId::new(module, id),
            );
            assert_eq!(parameters, expected.into_iter().collect());
        }
    }

    #[test]
    fn callback_specialization_obeys_the_shared_budget_and_reuses_cached_keys() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            r#"
            #[inline(never)] fn apply(f, x: int) -> int { let mut result = x; for i in (0..x) { result = f(result) }; result }
            fn inc(x: int) -> int { x + 1 }
            fn dec(x: int) -> int { x - 1 }
            fn first(x: int) -> int { apply(inc, x) }
            fn same(x: int) -> int { apply(inc, x) }
            fn other(x: int) -> int { apply(dec, x) }
        "#,
        );
        let mut table = Specializations::new(
            module,
            session.expect_fresh_module(module).function_count(),
            3,
        );
        table.limit = 1;
        let first = body(&session, module, "first");
        assert!(
            specialize_call_sites(first, session.module_env(), &session, module, &mut table)
                .is_some()
        );
        assert!(table.is_full());
        let same = body(&session, module, "same");
        assert!(
            specialize_call_sites(same, session.module_env(), &session, module, &mut table)
                .is_some()
        );
        let other = body(&session, module, "other");
        assert!(
            specialize_call_sites(other, session.module_env(), &session, module, &mut table)
                .is_none()
        );
        assert_eq!(table.len(), 1);
    }

    #[test]
    fn callback_specialization_falls_back_to_cached_type_only_copies() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            r#"
            #[inline(never)] fn apply(f, x) { let mut result = x; for i in (0..3) { result = f(result) + x }; result }
            fn inc(x: int) -> int { x + 1 }
            fn run(x: int) -> int { apply(inc, x) }
        "#,
        );
        let site = site(&session, module, "run", "apply");
        assert!(
            !site.key.dictionaries.is_empty(),
            "exercise dictionary-bearing specialization"
        );
        assert!(worth_specializing(
            &site.body,
            &site.scheme,
            &site.key.instantiation,
            &site.key.dictionaries,
            session.module_env()
        ));
        let mut table = Specializations::new(
            module,
            session.expect_fresh_module(module).function_count(),
            2,
        );
        table.limit = 1;
        let base = table.get_or_create(
            site.key.clone(),
            &site.scheme,
            &site.body,
            session.module_env(),
        );
        let check_fallback = |table: &mut Specializations| {
            let result = specialize_call_sites(
                body(&session, module, "run"),
                session.module_env(),
                &session,
                module,
                table,
            )
            .unwrap();
            assert!(result.blocks().any(|block| {
                result
                    .block(block)
                    .operations()
                    .iter()
                    .chain(match &result.block(block).terminator().kind {
                        TerminatorKind::Invoke { operation, .. } => Some(operation),
                        _ => None,
                    })
                    .any(|operation| {
                        matches!(operation.kind, OperationKind::Call { .. })
                            && operation.operands[0]
                                == mir::Value::Function(FunctionId::new(module, base))
                    })
            }));
            assert_eq!(table.len(), 1);
        };
        check_fallback(&mut table);
        table.limit = 2;
        table.callback_limit = 0;
        check_fallback(&mut table);
        table.callback_limit = budget::callback_specialization_limit(2);
        let mut rejected = site.key.clone();
        let parameter = site
            .body
            .parameters()
            .iter()
            .position(|parameter| {
                parameter.kind == ParameterKind::Parameter(ArgConvention::Let)
                    && parameter.ty.is_function()
            })
            .unwrap();
        let inc = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("inc"))
            .unwrap();
        rejected.callbacks.push((
            ParameterId::from_index(parameter),
            FunctionId::new(module, inc),
        ));
        table.reject(rejected);
        check_fallback(&mut table);
    }

    #[test]
    fn callback_binding_does_not_admit_a_body_that_only_forwards_it() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            r#"
            fn forwarding(f, x: int) -> int { apply(f, x) }
            fn apply(f, x: int) -> int { let mut result = x; for i in (0..x) { result = f(result) }; result }
        "#,
        );
        assert!(
            repeated_callback_parameters(
                body(&session, module, "forwarding"),
                FunctionId::new(
                    module,
                    session
                        .expect_fresh_module(module)
                        .get_local_function_id(ustr("forwarding"))
                        .unwrap()
                )
            )
            .is_empty()
        );
        assert_eq!(
            repeated_callback_parameters(
                body(&session, module, "apply"),
                FunctionId::new(
                    module,
                    session
                        .expect_fresh_module(module)
                        .get_local_function_id(ustr("apply"))
                        .unwrap()
                )
            )
            .len(),
            1
        );
    }

    /// Whether any operand of `func` names one of `parameters`.
    fn uses_any_parameter(func: &Function, parameters: &[ParameterId]) -> bool {
        let mut found = false;
        // Through the editor, so the terminator's operands are covered like any other.
        let mut edit = FunctionEdit::new(func.clone());
        edit.visit_operands_mut(|operand| {
            if let Value::Parameter(id) = operand
                && parameters.contains(id)
            {
                found = true;
            }
        });
        found
    }

    /// Specialization composes: a generic caller records its *own* quantifier on its inner call, so
    /// specializing the caller makes that inner call concrete without anything reasoning about
    /// nesting. This is the cascade the whole design rests on.
    #[test]
    fn specialization_makes_a_forwarded_inner_call_concrete() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn twice_it(x) { x + x }\n\
             fn forwarding(y) { twice_it(y) }\n\
             fn use_it() -> int { forwarding(3) }",
        );
        let inner = site(&session, module, "forwarding", "twice_it");
        assert!(
            inner
                .key
                .instantiation
                .ty_args
                .iter()
                .any(Type::is_variable),
            "the forwarding call must record a variable, or this test proves nothing"
        );

        let outer = site(&session, module, "use_it", "forwarding");
        let specialized = outer.specialize(session.module_env());

        let mut inner_calls = 0;
        for block_id in specialized.blocks() {
            for operation in specialized.block(block_id).operations() {
                if let OperationKind::Call { metadata, .. } = &operation.kind
                    && let Some(instantiation) = metadata
                        .as_deref()
                        .and_then(|metadata| metadata.instantiation.as_ref())
                {
                    inner_calls += 1;
                    assert!(
                        instantiation.ty_args.iter().all(Type::is_constant),
                        "an inner call's recorded instantiation must be substituted too"
                    );
                }
            }
        }
        assert!(
            inner_calls > 0,
            "the specialized body must still contain the forwarded call"
        );
    }
}
