// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Specializing a generic MIR body at one call site's instantiation.
//!
//! A generic function is compiled once, its type parameters left as quantified variables and its
//! trait constraints turned into hidden dictionary parameters. Specializing it has two halves —
//! substituting the types and binding the dictionaries — and **they must be applied together**. A
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

use std::cell::RefCell;

use rustc_hash::{FxHashMap, FxHashSet};
use ustr::{Ustr, ustr};

use crate::{
    CompilerSession, MirOptimization,
    compiler::Specialization,
    format::FormatWith,
    mir::{
        self, Function, Instantiation, Operation, OperationKind, ParameterKind,
        edit::FunctionEdit,
        operation::SourceFallibility,
        terminator::{Terminator, TerminatorKind},
    },
    module::{
        FunctionId, LocalFunctionId, ModuleEnv, ModuleId, TraitDictionaryId, id::Id,
        stable_generated_name_hash, unique_generated_name,
    },
    std::value::type_has_static_layout,
    types::effects::{EffType, Effect, PrimitiveEffect},
    types::type_properties::concrete_type_is_trivial_copy,
    types::{
        r#type::Type, type_like::TypeLike, type_mapper::BitmapInstantiationMapper,
        type_mapper::TypeMapper, type_scheme::TypeScheme,
    },
};

use super::{budget, function_size};

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
    pub(crate) dictionaries: Vec<TraitDictionaryId>,
}

/// The specializations one module's optimization has created, and the cache that keeps them shared.
///
/// Two call sites that instantiate a generic function the same way get the same body rather than a
/// copy each. Without that, a generic function called `n` times would be copied `n` times, which is
/// how naive specialization explodes.
#[derive(Default)]
pub(crate) struct Specializations {
    /// The module whose optimized artifacts will hold these, which is not in general the module a
    /// specialized callee came from: the identities below index *this* module's table.
    module: ModuleId,
    created: Vec<Specialization>,
    /// Each specialization as it was created, before the worklist optimized it.
    ///
    /// This is a specialization's *raw* stage, and it exists for the same reason the raw stage does:
    /// a pass that consults a callee's body must get the same answer whatever order functions are
    /// optimized in. `created` is mutated in place as the worklist reaches each entry, so reading it
    /// would make an inlining decision depend on whether that had happened yet.
    raw: Vec<Function>,
    cache: FxHashMap<SpecializationKey, LocalFunctionId>,
    /// Keys whose raw bodies expose none of the payoffs specialization can currently realize.
    ///
    /// A rejected key can occur at many call sites. Remembering it keeps the admission scan linear
    /// in the number of distinct candidates rather than in candidate call sites times body size.
    rejected: FxHashSet<SpecializationKey>,
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
    /// Where the module's HIR-declared functions end; specializations are numbered from here.
    first_index: usize,
}

impl Specializations {
    /// Starts an empty table for `module`, whose HIR function table has `function_count` entries.
    pub(crate) fn new(module: ModuleId, function_count: usize) -> Self {
        Self {
            module,
            created: Vec::new(),
            raw: Vec::new(),
            cache: FxHashMap::default(),
            rejected: FxHashSet::default(),
            substituted: RefCell::new(FxHashMap::default()),
            first_index: function_count,
        }
    }

    pub(crate) fn into_created(self) -> Vec<Specialization> {
        self.created
    }

    pub(crate) fn len(&self) -> usize {
        self.created.len()
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

    /// The body of a specialization as it was created, before the worklist optimized it.
    ///
    /// This is what a pass consulting a callee reads, so that its decision does not depend on
    /// optimization order — the same rule that makes every other callee lookup read the raw stage.
    pub(crate) fn raw_body(&self, id: LocalFunctionId) -> Option<&Function> {
        self.raw.get(id.as_index().checked_sub(self.first_index)?)
    }

    /// Replaces the body of a specialization this table created, after optimizing it.
    pub(crate) fn set_body(&mut self, id: LocalFunctionId, body: Function) {
        let index = id.as_index() - self.first_index;
        self.created[index].body = body;
    }

    /// A specialization already admitted for `key`, so another call site needs no scan or budget.
    pub(crate) fn cached(&self, key: &SpecializationKey) -> Option<LocalFunctionId> {
        self.cache.get(key).copied()
    }

    /// Whether the admission scan already found no specialization payoff for `key`.
    pub(crate) fn is_rejected(&self, key: &SpecializationKey) -> bool {
        self.rejected.contains(key)
    }

    /// Records that `key` exposes no specialization payoff in its raw body.
    pub(crate) fn reject(&mut self, key: SpecializationKey) {
        self.rejected.insert(key);
    }

    /// The local id of the specialization for `key`, creating it if this is the first call site to
    /// ask for it.
    pub(crate) fn get_or_create<Ty: TypeLike>(
        &mut self,
        key: SpecializationKey,
        scheme: &TypeScheme<Ty>,
        body: &Function,
        env: ModuleEnv<'_>,
    ) -> LocalFunctionId {
        if let Some(existing) = self.cache.get(&key) {
            return *existing;
        }
        let name = self.name_for(&key, body, env);
        // Allocated before the body is built, because a recursive callee has to be able to name
        // itself: see `redirect_recursion`.
        let id = LocalFunctionId::from_index(self.first_index + self.created.len());
        let own = FunctionId {
            module: self.module,
            function: id,
        };
        let mut specialized = FunctionEdit::new(specialize(body, scheme, &key, own, env));
        // The body carries its original's name until renamed, which would print two functions under
        // one header in a MIR dump.
        specialized.set_name(name);
        let specialized = specialized.finish(env);
        self.raw.push(specialized.clone());
        self.created.push(Specialization {
            original: key.callee,
            name,
            body: specialized,
        });
        self.cache.insert(key, id);
        id
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
            .map(|id| {
                mir::Value::Dictionary(*id)
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
        let canonical =
            format!("callee={qualified}; types=[{types}]; dictionaries=[{dictionaries}]");
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
    redirect_recursion(&mut edit, key.callee, own);
    simplify_after_substitution(&mut edit, env);
    edit.finish(env)
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
/// The specialization still carries its original's signature at this point, so the operands need no
/// adjustment; [`dead_evidence`](super::dead_evidence) narrows this call with every other.
fn redirect_recursion(edit: &mut FunctionEdit, original: FunctionId, own: FunctionId) {
    let own = mir::Value::Function(own);
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
                && operation.operands[0] == mir::Value::Function(original)
            {
                operation.operands[0] = own.clone();
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
    for block_id in edit.blocks().collect::<Vec<_>>() {
        let block = edit.block_mut(block_id);
        let mut dead_drops = Vec::new();
        for (index, operation) in block.operations.iter_mut().enumerate() {
            match &operation.kind {
                OperationKind::Clone { ty } if concrete_type_is_trivial_copy(*ty, &env) => {
                    let source = operation.operands[0].clone();
                    let destination = operation.operands[1].clone();
                    *operation = Operation::memcpy(operation.span, source, destination);
                }
                OperationKind::Drop { ty } if concrete_type_is_trivial_copy(*ty, &env) => {
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
}

/// Drops a `Value` dictionary layout witness that substitution made redundant.
///
/// `alloca` and `move` carry one when the value's size is only known at run time — a type that is,
/// or embeds, a bare type variable. Substituting a concrete instantiation is precisely what makes
/// such a type statically sized, so the witness the generic body needed is dead weight here: for
/// this type the emitter would have chosen the static form. Left in place it is a live use of the
/// dictionary, and a backend would honour it and emit a dynamically-sized allocation for a value
/// whose size it knows. The MIR interpreter ignores it, so this changes no behaviour today.
fn drop_redundant_layout_witnesses(edit: &mut FunctionEdit, env: ModuleEnv<'_>) {
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
            match &operation.kind {
                // The operand is present exactly in the dynamic form; the type it describes is the
                // operation's own.
                OperationKind::Alloca { ty } => {
                    if operation.operands.len() == 1 && type_has_static_layout(*ty, span, &env) {
                        operation.operands = Box::new([]);
                    }
                }
                // `move` records no type, so the witnessed type is read back from the `Value<T>`
                // dictionary that witnesses it.
                OperationKind::Move => {
                    if operation.operands.len() == 3
                        && let Some(ty) = witnessed_type(&operation.operands[2], env)
                        && type_has_static_layout(ty, span, &env)
                    {
                        let source = operation.operands[0].clone();
                        let destination = operation.operands[1].clone();
                        operation.operands = Box::new([source, destination]);
                    }
                }
                _ => {}
            }
        }
    }
}

/// The type a `Value<T>` dictionary operand witnesses the layout of.
fn witnessed_type(witness: &mir::Value, env: ModuleEnv<'_>) -> Option<Type> {
    let mir::Value::Dictionary(id) = witness else {
        return None;
    };
    let module = env.module_by_id(id.module_id)?;
    let key = module.get_impl_trait_key_by_id(id.impl_id)?;
    key.input_tys().first().copied()
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
            std::mem::replace(&mut block.terminator, Terminator::goto(span, normal)).kind
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
    projections: &FxHashMap<mir::ValueId, bool>,
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
fn open_projection_fallibility(edit: &FunctionEdit) -> FxHashMap<mir::ValueId, bool> {
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
fn map_types(edit: &mut FunctionEdit, mapper: &mut impl TypeMapper) {
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
fn bind_dictionaries(edit: &mut FunctionEdit, dictionaries: &[TraitDictionaryId]) {
    let parameters: Vec<mir::ParameterId> = edit
        .parameters()
        .iter()
        .enumerate()
        .filter(|(_, parameter)| matches!(parameter.kind, ParameterKind::Dictionary))
        .map(|(index, _)| mir::ParameterId::from_index(index))
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

    let bound: FxHashMap<mir::ParameterId, TraitDictionaryId> = parameters
        .into_iter()
        .zip(dictionaries.iter().copied())
        .collect();
    edit.visit_operands_mut(|operand| {
        if let mir::Value::Parameter(id) = operand
            && let Some(dictionary) = bound.get(id)
        {
            *operand = mir::Value::Dictionary(*dictionary);
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
        | OperationKind::Subfield { ty }
        | OperationKind::DictEntry { ty, .. }
        | OperationKind::SubscriptMember { ty, .. }
        | OperationKind::BuildSubscript { ty }
        | OperationKind::Variant { ty, .. }
        | OperationKind::BuildClosure { ty, .. }
        | OperationKind::CloneClosureEnv { ty } => *ty = ty.map(mapper),
        OperationKind::BuildArray { element_ty } => *element_ty = element_ty.map(mapper),
        OperationKind::AllocaPlace { pointing_to } => *pointing_to = pointing_to.map(mapper),
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
        | OperationKind::Store
        | OperationKind::Clear
        | OperationKind::Memcpy
        | OperationKind::Move
        | OperationKind::StackSave
        | OperationKind::StackRestore
        | OperationKind::CheckCallDepth
        | OperationKind::CheckFuel
        | OperationKind::DropClosureEnv => {}
        OperationKind::Clone { ty } | OperationKind::Drop { ty } => *ty = ty.map(mapper),
    }
}

/// Rewrites every call site of `func` that can be pointed at a specialized copy of its callee.
///
/// Returns `None` if nothing changed. A site is rewritten when all of the following hold, and each
/// is deliberately conservative — a refusal costs an optimization, never correctness:
///
/// - the callee is statically known and is not itself a specialization;
/// - the callee is generic and has a body to copy;
/// - the call records an instantiation, and that instantiation is fully concrete. A caller that
///   forwards its own quantifiers records them here, and specializing *it* is what makes this site
///   concrete on a later round — the cascade, which needs nothing extra to work;
/// - every hidden evidence operand is a constant dictionary;
/// - specializing would achieve something (see [`worth_specializing`]);
/// - the budget allows another specialization, unless this one is already cached.
///
/// The callee may live in another module: the specialization is still created in the *optimizing*
/// module's table, from the callee's raw body, which is safe because the session tracks the
/// dependency.
pub(crate) fn specialize_call_sites(
    func: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    specializations: &mut Specializations,
) -> Option<Function> {
    let mut edit = FunctionEdit::new(func.clone());
    let mut changed = false;

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
            if let Some(id) = specialization_for(operation, env, session, specializations) {
                operation.operands[0] = mir::Value::Function(FunctionId {
                    module: module_id,
                    function: id,
                });
                // The specialization is not generic, so it has no quantifiers for an instantiation
                // to be positional against. Leaving the old one would claim otherwise.
                if let OperationKind::Call { metadata, .. } = &mut operation.kind {
                    *metadata = None;
                }
                changed = true;
            }
        }
    }

    changed.then(|| edit.finish_unverified())
}

/// The specialization this call site should be pointed at, creating it if needed.
fn specialization_for(
    operation: &Operation,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    specializations: &mut Specializations,
) -> Option<LocalFunctionId> {
    let OperationKind::Call { ty, metadata } = &operation.kind else {
        return None;
    };
    let instantiation = metadata.as_deref()?.instantiation.as_ref()?;
    let mir::Value::Function(callee) = &operation.operands[0] else {
        return None;
    };
    // A specialization is never a callee to specialize again. The check only means anything for
    // this module's own table; another module's raw bodies contain no specializations at all.
    if specializations.is_specialization(*callee) {
        return None;
    }
    // A caller that still names its own quantifiers here would produce a specialization as generic
    if instantiation.ty_args.iter().any(Type::is_variable) {
        return None;
    }

    // The callee's own module, which need not be the one being optimized: a user module calling a
    // generic `std` helper is the case that matters, since otherwise every std generic stays generic
    // and uninlinable in every module but its own. Safe for the same reason cross-module *inlining*
    // is: a dependency's revision is immutable, so its raw body cannot change under us.
    let module = session.expect_fresh_module(callee.module);
    let scheme = &module
        .get_function_by_id(callee.function)?
        .definition
        .ty_scheme;
    if scheme.ty_quantifiers.is_empty() && scheme.eff_quantifiers.is_empty() {
        return None;
    }
    // Raw rather than optimized, like every other body the driver consults, so that what a
    // specialization contains never depends on the order functions are optimized in.
    let body = session
        .mir_artifacts_for(callee.module, MirOptimization::Disabled)?
        .get(callee.function)?;

    let visible_start = operation
        .operands
        .len()
        .checked_sub(ty.fn_ty.args.len() + 1)?;
    let dictionaries = operation.operands[1..visible_start]
        .iter()
        .map(|extra| match extra {
            mir::Value::Dictionary(id) => Some(*id),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let key = SpecializationKey {
        callee: *callee,
        instantiation: instantiation.clone(),
        dictionaries,
    };
    if let Some(existing) = specializations.cached(&key) {
        return Some(existing);
    }
    if specializations.is_rejected(&key) {
        return None;
    }
    if specializations.len() >= budget::MAX_SPECIALIZATIONS {
        return None;
    }
    if !worth_specializing(body, scheme, instantiation, &key.dictionaries, env) {
        specializations.reject(key);
        return None;
    }
    // Cloned out of the module borrow: substitution interns, and the type universe's lock is not
    // reentrant, so nothing may hold a type guard across it.
    let scheme = scheme.clone();
    let body = body.clone();
    Some(specializations.get_or_create(key, &scheme, &body, env))
}

/// Whether substitution exposes a reason Ferlium keeps a specialized body.
///
/// This is a linear preflight over the raw body, before cloning, verification or insertion into the
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
    dictionaries: &[TraitDictionaryId],
    env: ModuleEnv<'_>,
) -> bool {
    if dictionaries.is_empty() {
        return false;
    }
    let parameters: Vec<mir::ParameterId> = body
        .parameters()
        .iter()
        .enumerate()
        .filter(|(_, parameter)| matches!(parameter.kind, ParameterKind::Dictionary))
        .map(|(index, _)| mir::ParameterId::from_index(index))
        .collect();
    if parameters.len() != dictionaries.len() {
        // The call's evidence does not line up with the body's parameters. Not a case that should
        // arise, and not one to guess at.
        return false;
    }
    let bound: FxHashMap<_, _> = parameters
        .into_iter()
        .zip(dictionaries.iter().copied())
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
                OperationKind::Clone { ty } | OperationKind::Drop { ty }
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
                        && type_has_static_layout(ty.map(&mut mapper), operation.span, &env) =>
                {
                    return true;
                }
                OperationKind::Move
                    if operation.operands.len() == 3
                        && operation.operands.get(2).is_some_and(|witness| {
                            let mir::Value::Parameter(parameter) = witness else {
                                return false;
                            };
                            let Some(dictionary) = bound.get(parameter) else {
                                return false;
                            };
                            witnessed_type(&mir::Value::Dictionary(*dictionary), env).is_some_and(
                                |ty| type_has_static_layout(ty, operation.span, &env),
                            )
                        }) =>
                {
                    return true;
                }
                _ => {}
            }
        }
    }

    if reads_bound_evidence && function_size(body) <= budget::INLINE_CALLEE_OPERATIONS {
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
    use super::*;
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization,
        mir::{Value, terminator::TerminatorKind},
        module::{ModuleId, Path},
        types::{
            effects::EffType,
            mutability::MutType,
            r#type::{Type, TypeVar},
        },
    };
    use ustr::ustr;

    /// A generic callee, its declared scheme, and how one concrete call site instantiated it —
    /// everything specialization consumes, harvested from real lowering rather than hand-built.
    struct Site {
        body: Function,
        scheme: crate::types::type_scheme::TypeScheme<crate::types::r#type::FnType>,
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
        let optimized = session.emit_mir_module(module_id);
        assert!(
            !optimized.contains("call std::Value<[A]>::clone#impl:"),
            "specialization must remove the concrete thunk's call to the generic original:\n\
             {optimized}"
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
                    .map(|extra| match extra {
                        Value::Dictionary(id) => Some(*id),
                        _ => None,
                    })
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
            .map(|(index, _)| mir::ParameterId::from_index(index))
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
        let padding = budget::INLINE_CALLEE_OPERATIONS + 1 - function_size(&site.body);
        let entry = mir::BlockId::from_index(0);
        let span = site.body.block(entry).operations()[0].span;
        let mut edit = FunctionEdit::new(site.body);
        edit.block_mut(entry)
            .operations
            .extend((0..padding).map(|_| Operation::check_fuel(span)));
        site.body = edit.finish(session.module_env());

        assert!(function_size(&site.body) > budget::INLINE_CALLEE_OPERATIONS);
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
        let dictionary_parameters: Vec<mir::ParameterId> = site
            .body
            .parameters()
            .iter()
            .enumerate()
            .filter(|(_, parameter)| matches!(parameter.kind, ParameterKind::Dictionary))
            .map(|(index, _)| mir::ParameterId::from_index(index))
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
            module.contains("fn twice_it#spec:[int]"),
            "and the specialization it came from must be named after its instantiation:\n{module}"
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
        assert!(
            module.contains("#spec:"),
            "the generic callee must specialize, or this test proves nothing:\n{module}"
        );
        for specialized in module.split("// specialization of ").skip(1) {
            assert!(
                !specialized.contains("using dict"),
                "a specialized body must carry no layout witness for a concrete type:\n\
                 {specialized}"
            );
        }
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
            .split("// specialization of ")
            .nth(1)
            .expect("swap must specialize");
        assert!(
            specialized.contains("memcpy"),
            "a clone of a now-trivially-copyable type becomes a representation copy:\n{specialized}"
        );
        for spelling in ["clone ", "drop ", "dict_entry"] {
            assert!(
                !specialized.contains(spelling),
                "no `{spelling}` may survive for a type that owns nothing:\n{specialized}"
            );
        }
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
        let specialized = module
            .split("fn array_append#spec:[int]")
            .nth(1)
            .expect("array_append must specialize at int, or this test proves nothing")
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
        // which is what rejected this before `demote_infallible_invokes` existed.
        let module = session.emit_mir(
            "spec",
            "fn ho(f, x) { match f(x) { 1 => 10, _ => 20 } }\n\
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
        crate::compiler::ensure_mir_artifacts(session.raw_modules(), std_id);
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
                        .map(|extra| match extra {
                            Value::Dictionary(id) => Some(*id),
                            _ => None,
                        })
                        .collect::<Option<Vec<_>>>()
                    else {
                        continue; // the caller forwards evidence of its own
                    };

                    let key = SpecializationKey {
                        callee: *callee,
                        instantiation: instantiation.clone(),
                        dictionaries,
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

        assert!(
            specialized > 100,
            "specialized only {specialized} std call sites; the population should be in the \
             hundreds, so this is a lowering or harvesting regression rather than a small library"
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

    /// Whether any operand of `func` names one of `parameters`.
    fn uses_any_parameter(func: &Function, parameters: &[mir::ParameterId]) -> bool {
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
