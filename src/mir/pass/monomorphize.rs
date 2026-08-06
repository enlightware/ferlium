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
//! The specialized signature is deliberately identical to the original's: binding a dictionary
//! parameter replaces its *uses*, and leaves the now-unread parameter in place. That keeps every
//! HIR-table lookup the interpreter makes on a call — `code.as_script()`, `return_convention()`,
//! `parameter_passing` — answerable from the original's metadata. Dropping the dead parameters is a
//! later refinement and DCE's territory.
//!
//! Exercised only by its own tests until the specialization pass consumes it; remove the allow
//! below then, as `const_eval.rs` did when folding started calling it.
#![allow(dead_code)]

use rustc_hash::FxHashMap;
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
    types::{
        r#type::Type, type_like::TypeLike, type_mapper::BitmapInstantiationMapper,
        type_mapper::TypeMapper, type_scheme::TypeScheme,
    },
};

use super::budget;

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
    created: Vec<Specialization>,
    /// Each specialization as it was created, before the worklist optimized it.
    ///
    /// This is a specialization's *raw* stage, and it exists for the same reason the raw stage does:
    /// a pass that consults a callee's body must get the same answer whatever order functions are
    /// optimized in. `created` is mutated in place as the worklist reaches each entry, so reading it
    /// would make an inlining decision depend on whether that had happened yet.
    raw: Vec<Function>,
    cache: FxHashMap<SpecializationKey, LocalFunctionId>,
    /// Where the module's HIR-declared functions end; specializations are numbered from here.
    first_index: usize,
}

impl Specializations {
    /// Starts an empty table for a module whose HIR function table has `function_count` entries.
    pub(crate) fn new(function_count: usize) -> Self {
        Self {
            created: Vec::new(),
            raw: Vec::new(),
            cache: FxHashMap::default(),
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
    pub(crate) fn is_specialization(&self, id: LocalFunctionId) -> bool {
        id.as_index() >= self.first_index
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

    /// Whether a specialization for this key already exists, so asking for it costs no budget.
    pub(crate) fn is_cached(&self, key: &SpecializationKey) -> bool {
        self.cache.contains_key(key)
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
        let mut specialized = FunctionEdit::new(specialize(
            body,
            scheme,
            &key.instantiation,
            &key.dictionaries,
            env,
        ));
        // The body carries its original's name until renamed, which would print two functions under
        // one header in a MIR dump.
        specialized.set_name(name);
        let specialized = specialized.finish(env);
        let id = LocalFunctionId::from_index(self.first_index + self.created.len());
        self.raw.push(specialized.clone());
        self.created.push(Specialization {
            original: key.callee,
            name,
            body: specialized,
        });
        self.cache.insert(key, id);
        id
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
    instantiation: &Instantiation,
    dictionaries: &[TraitDictionaryId],
    env: ModuleEnv<'_>,
) -> Function {
    let subst = instantiation.substitution(scheme);
    // Bitmap rather than simple: one mapper is reused across every type in the body, which is what
    // makes its `affects_type` constant-time construction cost pay for itself.
    let mut mapper = BitmapInstantiationMapper::new(&subst);

    let mut edit = FunctionEdit::new(body.clone());
    map_types(&mut edit, &mut mapper);
    bind_dictionaries(&mut edit, dictionaries);
    demote_infallible_invokes(&mut edit);
    edit.finish(env)
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
    let mut demoted = false;
    for block_id in edit.blocks().collect::<Vec<_>>() {
        let block = edit.block_mut(block_id);
        let TerminatorKind::Invoke {
            operation, normal, ..
        } = &block.terminator.kind
        else {
            continue;
        };
        if operation_is_source_fallible(operation) {
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
fn operation_is_source_fallible(operation: &Operation) -> bool {
    match operation.source_fallibility() {
        SourceFallibility::Infallible => false,
        SourceFallibility::Fallible => true,
        // Fallibility belongs to the open projection this resumes, which is not something
        // substitution can settle from the operation alone. Left as it was found.
        SourceFallibility::FromOpenProjection => true,
    }
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
        OperationKind::AllocaPlace { pointing_to } => *pointing_to = pointing_to.map(mapper),
        OperationKind::Call { ty, instantiation } => {
            **ty = ty.map(mapper);
            // The instantiation this body's own calls record. Easy to miss because it is not a
            // type field, and the one that makes specialization cascade: an inner call recording
            // the container's quantifiers becomes concrete exactly when the container does.
            if let Some(instantiation) = instantiation {
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
        | OperationKind::Drop
        | OperationKind::DropClosureEnv => {}
    }
}

/// Rewrites every call site of `func` that can be pointed at a specialized copy of its callee.
///
/// Returns `None` if nothing changed. A site is rewritten when all of the following hold, and each
/// is deliberately conservative — a refusal costs an optimization, never correctness:
///
/// - the callee is statically known, declared in this module, and is not itself a specialization;
/// - the callee is generic and has a body to copy;
/// - the call records an instantiation, and that instantiation is fully concrete. A caller that
///   forwards its own quantifiers records them here, and specializing *it* is what makes this site
///   concrete on a later round — the cascade, which needs nothing extra to work;
/// - every hidden evidence operand is a constant dictionary;
/// - specializing would achieve something (see [`worth_specializing`]);
/// - the budget allows another specialization, unless this one is already cached.
///
/// Intra-module only for now, per the phase's non-goal: a specialization lives in the optimizing
/// module's table, and reaching another module's generic callees is a separate step.
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
            if let Some(id) =
                specialization_for(operation, env, session, module_id, specializations)
            {
                operation.operands[0] = mir::Value::Function(FunctionId {
                    module: module_id,
                    function: id,
                });
                // The specialization is not generic, so it has no quantifiers for an instantiation
                // to be positional against. Leaving the old one would claim otherwise.
                if let OperationKind::Call { instantiation, .. } = &mut operation.kind {
                    *instantiation = None;
                }
                changed = true;
            }
        }
    }

    changed.then(|| edit.finish(env))
}

/// The specialization this call site should be pointed at, creating it if needed.
fn specialization_for(
    operation: &Operation,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
    specializations: &mut Specializations,
) -> Option<LocalFunctionId> {
    let OperationKind::Call {
        ty,
        instantiation: Some(instantiation),
    } = &operation.kind
    else {
        return None;
    };
    let mir::Value::Function(callee) = &operation.operands[0] else {
        return None;
    };
    if callee.module != module_id || specializations.is_specialization(callee.function) {
        return None;
    }
    // A caller that still names its own quantifiers here would produce a specialization as generic
    // as the original. Specializing the caller is what makes this concrete, on a later round.
    if instantiation.ty_args.iter().any(Type::is_variable) {
        return None;
    }

    let module = session.expect_fresh_module(module_id);
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
        .mir_artifacts_for(module_id, MirOptimization::Disabled)?
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
    if !worth_specializing(body, &dictionaries) {
        return None;
    }

    let key = SpecializationKey {
        callee: *callee,
        instantiation: instantiation.as_ref().clone(),
        dictionaries,
    };
    if !specializations.is_cached(&key) && specializations.len() >= budget::MAX_SPECIALIZATIONS {
        return None;
    }
    // Cloned out of the module borrow: substitution interns, and the type universe's lock is not
    // reentrant, so nothing may hold a type guard across it.
    let scheme = scheme.clone();
    let body = body.clone();
    Some(specializations.get_or_create(key, &scheme, &body, env))
}

/// Whether a specialized copy of this body would be better than the original, judged from the body
/// alone.
///
/// **It must have a dictionary parameter that the body actually reads.** Binding that turns a
/// `dict_entry` on a parameter into one on a constant, which folding resolves to a known function —
/// the devirtualization that is specialization's payoff today.
///
/// Substituting the types of a callee with *no* evidence parameters looks worth it too: the copy
/// would be concrete, and a concrete body is one the inliner accepts. It is not, yet, and the reason
/// is worth stating because it is the next step rather than an oversight. Every pass resolves a
/// callee's body from the **raw** stage, so that what it decides never depends on the order
/// functions are optimized in — and a specialization exists only in the optimized stage. Until a
/// pass can reach one, such a copy would be created, verified, optimized and called by nobody.
fn worth_specializing(body: &Function, dictionaries: &[TraitDictionaryId]) -> bool {
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
    let mut read = false;
    let mut edit = FunctionEdit::new(body.clone());
    edit.visit_operands_mut(|operand| {
        if let mir::Value::Parameter(id) = operand
            && parameters.contains(id)
        {
            read = true;
        }
    });
    read
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
        callee: Function,
        scheme: crate::types::type_scheme::TypeScheme<crate::types::r#type::FnType>,
        instantiation: Instantiation,
        /// The constant dictionaries the call passes as `@extra` operands. Empty if any of them is
        /// not constant, which is the caller forwarding evidence of its own.
        dictionaries: Vec<TraitDictionaryId>,
    }

    impl Site {
        fn specialize(&self, env: ModuleEnv<'_>) -> Function {
            specialize(
                &self.callee,
                &self.scheme,
                &self.instantiation,
                &self.dictionaries,
                env,
            )
        }
    }

    fn compile(session: &mut CompilerSession, src: &str) -> ModuleId {
        session
            .compile_for(ExecutionTarget::Mir, src, "test", Path::single_str("test"))
            .expect("test source must compile")
            .module_id
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
                let OperationKind::Call { ty, instantiation } = &operation.kind else {
                    continue;
                };
                let Value::Function(callee) = &operation.operands[0] else {
                    continue;
                };
                if callee.module != module || callee.function != wanted {
                    continue;
                }
                let instantiation = instantiation
                    .as_ref()
                    .unwrap_or_else(|| {
                        panic!("the call to {callee_name} must record its instantiation")
                    })
                    .as_ref()
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
                    callee: body(session, module, callee_name).clone(),
                    scheme,
                    instantiation,
                    dictionaries,
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
            !free_ty_vars(&site.callee, session.module_env()).is_empty(),
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
            !site.dictionaries.is_empty(),
            "the call must pass constant evidence, or this test proves nothing"
        );
        let dictionary_parameters: Vec<mir::ParameterId> = site
            .callee
            .parameters()
            .iter()
            .enumerate()
            .filter(|(_, parameter)| matches!(parameter.kind, ParameterKind::Dictionary))
            .map(|(index, _)| mir::ParameterId::from_index(index))
            .collect();
        assert!(
            uses_any_parameter(&site.callee, &dictionary_parameters),
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
                    let OperationKind::Call {
                        ty,
                        instantiation: Some(instantiation),
                    } = &operation.kind
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

                    specialize(
                        body,
                        scheme,
                        instantiation,
                        &dictionaries,
                        session.module_env(),
                    );
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
            inner.instantiation.ty_args.iter().any(Type::is_variable),
            "the forwarding call must record a variable, or this test proves nothing"
        );

        let outer = site(&session, module, "use_it", "forwarding");
        let specialized = outer.specialize(session.module_env());

        let mut inner_calls = 0;
        for block_id in specialized.blocks() {
            for operation in specialized.block(block_id).operations() {
                if let OperationKind::Call {
                    instantiation: Some(instantiation),
                    ..
                } = &operation.kind
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
