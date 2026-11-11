// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Trait solving: shared state, visibility, and module access.
//! Matching, improvement, probing, materialization, and definition-site reduction live in
//! separate modules; their public entry points remain available through `TraitSolver`.

mod canonical;
mod context_reduction;
mod improvement;
mod matching;
mod materialization;
mod probe;
mod solve;
#[cfg(test)]
mod tests;

pub(crate) use canonical::{
    alpha_canonicalize_dictionary_requirements, alpha_canonicalize_types,
    alpha_canonicalize_types_with_instantiation, application_key,
};
pub(crate) use context_reduction::{
    EvidencePlan, EvidencePlanSource, REDUCTION_WORK_LIMIT, UniformDictionaryKey,
};
pub(crate) use matching::{input_heads_may_match, output_effect_fits};
pub(crate) use probe::{ConstraintAssumptions, TraitSolverProbe};

use std::{mem, rc::Rc};

use ustr::Ustr;

use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    compiler::error::InternalCompilationError,
    internal_compilation_error,
    module::{
        self, BlanketImpls, ConcreteImpls, ConcreteTraitImplKey, CurrentTypeItems, DefTable,
        FunctionId, GeneratedImplSource, LocalFunctionId, LocalImplId, LocalTraitId, Module,
        ModuleId, PendingFunctionCollector, ProjectionKey, ProjectionReceiverKey, QualifiedNameEnv,
        ResolvedValueLayout, TraitId, TraitImpl, TraitImplId, TraitImpls, TypeDefId, id::Id,
    },
    std::{
        STD_MODULE_ID,
        core_traits_names::TRIVIAL_COPY_TRAIT_NAME,
        value::{
            TypeLayoutEnv, is_compiler_provided_value_trait_application, value_layout_for_type,
        },
    },
    types::{
        effect_polarity::{EffectPolarity, trait_output_effect_polarities},
        effects::{EffType, EffectVar},
        r#trait::{Trait, TraitAssociatedConstIndex},
        r#type::{SubscriptType, Type, TypeDef, TypeKind, TypeVar},
        type_inference::effect_solver::EffectConstraintOrigin,
        type_like::TypeLike,
        type_properties::{TypePropertyEnv, concrete_type_is_trivial_copy, trivial_copy_impl_key},
        type_scheme::PubTypeConstraint,
    },
};

use self::{improvement::TraitImprovementKey, solve::TraitOutputCacheEntry};

pub(crate) struct DerivedImplSnapshot {
    concrete_key_to_id: Rc<ConcreteImpls>,
    blanket_key_to_id: Rc<BlanketImpls>,
    generated_value_key_to_id: Rc<FxHashMap<Vec<Type>, LocalImplId>>,
    application_key_to_id: Rc<ConcreteImpls>,
    generated_sources: Rc<FxHashMap<LocalImplId, GeneratedImplSource>>,
    uniform_dictionaries: Rc<FxHashMap<UniformDictionaryKey, LocalImplId>>,
    impl_data_len: usize,
    new_function_len: usize,
}

/// An application resolved symbolically by a blanket implementation: the implementation's
/// outputs and constraints in terms of the application's variables. Type and effect variables
/// from `type_var_base` and `effect_var_base` on are the implementation's own, which the caller
/// renames to fresh variables.
pub(crate) struct SymbolicApplication {
    /// The implementation's inputs, unrelated to the application's, which the caller relates.
    pub(crate) input_tys: Vec<Type>,
    pub(crate) output_tys: Vec<Type>,
    pub(crate) output_effs: Vec<EffType>,
    pub(crate) obligations: Vec<PubTypeConstraint>,
    pub(crate) type_var_base: u32,
    pub(crate) effect_var_base: u32,
}

/// Trait solving is performed by this structure, mutating it by caching intermediate results.
#[allow(clippy::too_many_arguments)]
#[derive(Debug)]
#[must_use = "call .finish().commit() to store the created functions"]
pub struct TraitSolver<'a> {
    /// Current module type-level items. Kept separately from `others` because the current module can be mid-compilation and not yet committed.
    pub(crate) current_type_items: CurrentTypeItems<'a>,
    /// Current module implementations.
    pub impls: &'a mut TraitImpls,
    /// Borrowed definitions for looking up existing named functions. Generated
    /// functions remain in `fn_collector` until commit.
    current_def_table: &'a DefTable,
    /// Current module dependencies discovered while solving.
    pub deps: &'a mut FxHashSet<ModuleId>,
    /// Current-module projection subscript capability types, materialized eagerly for real solvers and lazily for probes.
    current_projection_subscript_types: CurrentProjectionSubscriptTypes<'a>,
    /// Collector for newly created current module functions.
    pub fn_collector: PendingFunctionCollector,
    /// Other modules available for fetching trait implementations and normal functions (read only).
    pub(crate) others: &'a Modules,
    /// Current recursion depth of the trait solver.
    pub recursion_depth: usize,
    /// Whether this solver is deciding by structure if an impl applies, ignoring all effects.
    selecting_by_structure: bool,
    /// Current stack of trait implementations being solved, for cycle detection.
    pub solving_stack: FxHashSet<(TraitId, Vec<Type>)>,
    /// Partially known trait applications currently being improved, for cycle detection.
    active_improvements: FxHashSet<TraitImprovementKey>,
    /// Additional module whose private impls are visible to a privileged scratch expression.
    privileged_impl_module: Option<ModuleId>,
    /// For each other module looked at, the traits it has private impls of, which a derivation
    /// made in its private scope depends on.
    private_impl_traits: FxHashMap<ModuleId, Rc<FxHashSet<TraitId>>>,
    /// Successful fully-concrete, unconstrained output probes made during inference or defaulting.
    ///
    /// This is deliberately per-solver. A [`TraitSolverProbe`] can hide private implementations
    /// from its source solver, so it must not inherit answers from this cache.
    unmaterialized_output_cache: FxHashMap<TraitId, Vec<TraitOutputCacheEntry>>,
    /// While requesting a dictionary for a callable, the effect variables it quantifies: a reused
    /// dictionary must serve every value they may take. Taken by the request's top-level frame.
    quantified_request_effect_vars: FxHashSet<EffectVar>,
}

impl<'a> TraitSolver<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        current_type_items: CurrentTypeItems<'a>,
        impls: &'a mut TraitImpls,
        current_def_table: &'a DefTable,
        deps: &'a mut FxHashSet<ModuleId>,
        current_projection_subscript_types: CurrentProjectionSubscriptTypes<'a>,
        fn_collector: PendingFunctionCollector,
        others: &'a Modules,
    ) -> Self {
        debug_assert_eq!(current_type_items.module.id, impls.module_id);
        Self {
            current_type_items,
            impls,
            current_def_table,
            deps,
            current_projection_subscript_types,
            fn_collector,
            others,
            recursion_depth: 0,
            solving_stack: FxHashSet::default(),
            active_improvements: FxHashSet::default(),
            selecting_by_structure: false,
            privileged_impl_module: None,
            private_impl_traits: FxHashMap::default(),
            unmaterialized_output_cache: FxHashMap::default(),
            quantified_request_effect_vars: FxHashSet::default(),
        }
    }

    /// Record that the generated dictionary `local_impl_id` comes from `impl_id` of `module`, if
    /// that is another module.
    fn record_generated_source(
        &mut self,
        local_impl_id: LocalImplId,
        module: Option<ModuleId>,
        impl_id: LocalImplId,
    ) {
        let Some(module) = module else {
            return;
        };
        let private = !self
            .others
            .get(module)
            .and_then(|entry| entry.module())
            .is_some_and(|imp_module| imp_module.impls.data[impl_id.as_index()].public);
        Rc::make_mut(&mut self.impls.generated_sources)
            .insert(local_impl_id, GeneratedImplSource::Impl { module, private });
    }

    /// The other module whose private impls are visible in a privileged scratch scope, if any.
    fn foreign_private_scope(&self) -> Option<ModuleId> {
        let current = self.current_type_items.module.id;
        self.privileged_impl_module
            .filter(|&module| module != current)
    }

    /// The other module whose private impls of `trait_id` are visible besides the current
    /// module's, if any: a derivation of `trait_id` depends on these, and only on these.
    fn derivation_scope(&mut self, trait_id: TraitId) -> Option<ModuleId> {
        let module_id = self.foreign_private_scope()?;
        let others = self.others;
        let traits = self
            .private_impl_traits
            .entry(module_id)
            .or_insert_with(|| {
                let impls = &others
                    .get(module_id)
                    .and_then(|entry| entry.module())
                    .expect("a private impl scope is a compiled module")
                    .impls;
                let private = |id: &LocalImplId| !impls.data[id.as_index()].public;
                let concrete = impls
                    .concrete_key_to_id
                    .iter()
                    .filter(|(_, id)| private(id))
                    .map(|(key, _)| key.trait_id);
                let blanket = impls
                    .blanket_key_to_id
                    .iter()
                    .filter(|(_, blanket_impls)| blanket_impls.values().any(private))
                    .map(|(trait_id, _)| *trait_id);
                Rc::new(concrete.chain(blanket).collect())
            });
        traits.contains(&trait_id).then_some(module_id)
    }

    /// Whether the generated dictionary `local_impl_id` may serve here: one materialized from a
    /// private impl of another module serves only where that module's private impls are visible,
    /// and a derived one only where the same impls of its trait are visible as when it was
    /// derived, as there a visible impl takes precedence over the derivation.
    fn generated_impl_is_visible(&mut self, local_impl_id: LocalImplId) -> bool {
        match self.impls.generated_sources.get(&local_impl_id).copied() {
            None => true,
            Some(GeneratedImplSource::Impl { module, private }) => {
                !private || self.privileged_impl_module == Some(module)
            }
            Some(GeneratedImplSource::Derived { scope }) => {
                let trait_id = self.impls.data[local_impl_id.as_index()].trait_id;
                self.derivation_scope(trait_id) == scope
            }
        }
    }

    /// Allow this solver to use private trait implementations from `module_id`.
    ///
    /// This is used by the private scratch-expression machinery when dispatching on a value whose
    /// type originates in another module. It does not grant access to private names or type
    /// representations.
    pub(crate) fn allow_private_impls_from(&mut self, module_id: ModuleId) {
        debug_assert!(self.privileged_impl_module.is_none());
        self.privileged_impl_module = Some(module_id);
    }
}

pub(crate) const TRAIT_SOLVER_RECURSION_LIMIT: usize = 128;

/// Macro to create a trait solver from a module and a program.
/// This cannot be a function because of lifetime issues, as we must
/// mutably borrow parts of the module's data while not touching the function field.
macro_rules! trait_solver_from_module {
    ($module:expr, $program:expr) => {{
        let current_projection_subscript_types =
            crate::types::trait_solver::CurrentProjectionSubscriptTypes::from_map(
                crate::types::trait_solver::current_projection_subscript_type_map(&$module),
            );
        let function_count = $module.functions.len();
        TraitSolver::new(
            crate::module::CurrentTypeItems::new(
                crate::module::ModuleIdentity {
                    id: $module.module_id(),
                    path: &$module.path,
                },
                &$module.type_aliases,
                $module.type_defs.as_slice(),
                $module.traits.as_slice(),
                &$module.projection_subscripts,
                &$module.environment,
            ),
            &mut $module.impls,
            &$module.def_table,
            &mut $module.deps,
            current_projection_subscript_types,
            crate::module::PendingFunctionCollector::new(function_count),
            $program,
        )
    }};
}

pub(crate) use trait_solver_from_module;
#[derive(Debug, Clone)]
pub(crate) struct CurrentProjectionSubscriptTypes<'a> {
    source: CurrentProjectionSubscriptTypeSource<'a>,
    types: Option<Rc<FxHashMap<ProjectionKey, SubscriptType>>>,
}

#[derive(Debug, Clone, Copy)]
enum CurrentProjectionSubscriptTypeSource<'a> {
    Module(&'a Module),
    Materialized,
}

impl<'a> CurrentProjectionSubscriptTypes<'a> {
    pub(crate) fn from_module(module: &'a Module) -> Self {
        Self {
            source: CurrentProjectionSubscriptTypeSource::Module(module),
            types: None,
        }
    }

    pub(crate) fn from_map(types: FxHashMap<ProjectionKey, SubscriptType>) -> Self {
        Self {
            source: CurrentProjectionSubscriptTypeSource::Materialized,
            types: Some(Rc::new(types)),
        }
    }

    #[cfg(test)]
    pub(crate) fn empty() -> Self {
        Self::from_map(FxHashMap::default())
    }

    fn get(&mut self, key: ProjectionKey) -> Option<SubscriptType> {
        if self.types.is_none() {
            let CurrentProjectionSubscriptTypeSource::Module(source) = self.source else {
                return None;
            };
            self.types = Some(Rc::new(current_projection_subscript_type_map(source)));
        }
        self.types
            .as_ref()
            .and_then(|types| types.get(&key).cloned())
    }

    fn cache_materialized_types_from(&mut self, other: &CurrentProjectionSubscriptTypes<'_>) {
        if let Some(types) = &other.types {
            self.types = Some(Rc::clone(types));
        }
    }
}

pub(crate) fn current_projection_subscript_type_map(
    module: &Module,
) -> FxHashMap<ProjectionKey, SubscriptType> {
    module
        .projection_subscripts
        .iter()
        .filter_map(|(key, entry)| {
            let subscript = module.get_subscript_by_id(entry.subscript)?;
            Some((*key, subscript.type_scheme(module)?.ty))
        })
        .collect()
}

fn trait_def_from_parts<'a>(
    current: CurrentTypeItems<'a>,
    others: &'a Modules,
    id: TraitId,
) -> &'a Trait {
    if let Some(trait_def) = current.trait_def(id) {
        return trait_def;
    }
    others
        .get(id.module)
        .and_then(|entry| entry.module())
        .unwrap_or_else(|| panic!("Trait module #{} is unavailable", id.module))
        .trait_def(id)
}

fn is_compiler_provided_no_output_trait_application(
    trait_id: TraitId,
    trait_def: &Trait,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
    env: &impl TypeLayoutEnv,
) -> bool {
    output_tys.is_empty()
        && output_effs.is_empty()
        && is_compiler_provided_value_trait_application(
            trait_id, trait_def, input_tys, output_tys, env,
        )
}

impl<'a> TraitSolver<'a> {
    fn can_use_other_impl(&self, module_id: ModuleId, imp: &TraitImpl) -> bool {
        self.current_type_items.environment.contains(&module_id)
            && (imp.public || self.privileged_impl_module == Some(module_id))
    }

    pub(crate) fn reject_inaccessible_private_repr(
        &self,
        id: TypeDefId,
        access_span: Location,
    ) -> Result<(), InternalCompilationError> {
        if id.module != self.current_type_items.module.id && self.type_def(id).has_private_repr() {
            return Err(internal_compilation_error!(PrivateReprAccess {
                type_def: id,
                access_span,
            }));
        }
        Ok(())
    }

    pub fn trait_def(&self, id: TraitId) -> &Trait {
        trait_def_from_parts(self.current_type_items, self.others, id)
    }

    pub fn std_trait_id(&self, name: &str) -> TraitId {
        // The solver only keeps the current module's trait definitions, not its
        // definition table, so current-std lookups cannot use the symbol table.
        if self.current_type_items.module.id == STD_MODULE_ID
            && let Some((index, _)) = self
                .current_type_items
                .traits
                .iter()
                .enumerate()
                .find(|(_, trait_def)| trait_def.name == name)
        {
            return TraitId::new(STD_MODULE_ID, LocalTraitId::from_index(index));
        }
        Module::expect_std_trait_id(self.others, name)
    }

    pub fn type_def(&self, id: TypeDefId) -> &TypeDef {
        self.current_type_items.type_def(id).unwrap_or_else(|| {
            self.others
                .get(id.module)
                .and_then(|entry| entry.module())
                .unwrap_or_else(|| panic!("Type definition module #{} is unavailable", id.module))
                .type_def(id)
        })
    }

    pub(crate) fn projection_subscript_type(
        &mut self,
        receiver_ty: Type,
        field: Ustr,
    ) -> Option<SubscriptType> {
        let key = ProjectionKey::explicit_for_receiver_ty(receiver_ty, field)?;
        let receiver_params = {
            let data = receiver_ty.data();
            match &*data {
                TypeKind::Named(named) => named.params.clone(),
                TypeKind::Native(_) => Default::default(),
                _ => return None,
            }
        };
        let subscript = self.projection_subscript_id(key)?;
        let subscript_ty = if subscript.module == self.current_type_items.module.id {
            self.current_projection_subscript_types.get(key)?
        } else {
            let module = self
                .others
                .get(subscript.module)
                .and_then(|entry| entry.module())?;
            module
                .get_subscript_by_id(subscript.subscript)?
                .type_scheme(module)?
                .ty
        };
        let subst = (
            receiver_params
                .iter()
                .copied()
                .enumerate()
                .map(|(index, ty)| (TypeVar::new(index as u32), ty))
                .collect(),
            FxHashMap::default(),
        );
        Some(subscript_ty.instantiate_simple(&subst))
    }

    pub(crate) fn projection_subscript_id(
        &mut self,
        key: ProjectionKey,
    ) -> Option<module::SubscriptId> {
        if let Some(entry) = self.current_type_items.projection_subscripts.get(&key) {
            return Some(module::SubscriptId::new(
                self.current_type_items.module.id,
                entry.subscript,
            ));
        }

        let lookup = |module_id| {
            if !self.current_type_items.environment.contains(&module_id) {
                return None;
            }
            let module = self.others.get(module_id)?.module()?;
            let entry = module.get_projection_subscript(key)?;
            if entry.visibility != module::Visibility::Public {
                return None;
            }
            Some(module::SubscriptId::new(module_id, entry.subscript))
        };
        let subscript = match key.receiver {
            ProjectionReceiverKey::Nominal(def) => lookup(def.module),
            ProjectionReceiverKey::Structural(_) => self
                .others
                .enumerate()
                .find_map(|(module_id, _, _)| lookup(module_id)),
        }?;
        self.deps.insert(subscript.module);
        Some(subscript)
    }

    pub(crate) fn qualified_name_env(&self) -> QualifiedNameEnv<'_> {
        QualifiedNameEnv::new(self.current_type_items, self.others)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn impl_associated_const_names(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        ty_var_count: u32,
        eff_var_count: u32,
        constraints: &[PubTypeConstraint],
    ) -> Vec<Ustr> {
        let trait_def = self.trait_def(trait_id);
        let env = self.qualified_name_env();
        (0..trait_def.associated_const_count())
            .map(TraitAssociatedConstIndex::from_index)
            .map(|index| {
                env.disambiguated_impl_associated_const_name(
                    trait_id,
                    trait_def,
                    index,
                    input_tys,
                    output_tys,
                    output_effs,
                    ty_var_count,
                    eff_var_count,
                    constraints,
                )
                .into()
            })
            .collect()
    }

    pub(crate) fn solve_concrete_trivial_copy_layout(
        &mut self,
        ty: Type,
        span: Location,
    ) -> Result<Option<ResolvedValueLayout>, InternalCompilationError> {
        if !self.concrete_type_is_trivial_copy(ty) {
            return Ok(None);
        }
        Ok(Some(value_layout_for_type(ty, span, self)?))
    }

    /// Return whether representation-copying this concrete type is semantically valid.
    ///
    /// See [`concrete_type_is_trivial_copy`] for the rule; the solver supplies the environment,
    /// which unlike a `ModuleEnv`'s also sees the impls of the module being compiled.
    pub(crate) fn concrete_type_is_trivial_copy(&self, ty: Type) -> bool {
        concrete_type_is_trivial_copy(ty, self)
    }

    /// Probe the canonical module that owns the trait rather than the current
    /// visibility scope. Native-only marker properties must not change when an
    /// unrelated module is added to or removed from the solver environment.
    fn has_canonical_trait_impl(&self, key: &ConcreteTraitImplKey) -> bool {
        if key.trait_id.module == self.current_type_items.module.id {
            return self.impls.concrete_key_to_id.contains_key(key);
        }
        self.others
            .get(key.trait_id.module)
            .and_then(|entry| entry.module())
            .is_some_and(|module| module.impls.concrete_key_to_id.contains_key(key))
    }

    /// The polarity of each output effect of `trait_id`.
    pub(crate) fn output_effect_polarities(&self, trait_id: TraitId) -> Vec<EffectPolarity> {
        trait_output_effect_polarities(trait_id, &|id| self.trait_def(id))
    }

    /// The diagnostic origin of a constraint on the output effect `index` of `trait_id`, for an
    /// application at `span`.
    pub(crate) fn output_effect_origin(
        &self,
        trait_id: TraitId,
        index: usize,
        span: Location,
    ) -> EffectConstraintOrigin {
        EffectConstraintOrigin::TraitOutput {
            trait_id,
            output: self.trait_def(trait_id).output_effect_names[index],
            span,
        }
    }

    fn type_var_capacity_for_types<'t>(types: impl IntoIterator<Item = &'t Type>) -> u32 {
        types
            .into_iter()
            .flat_map(TypeLike::inner_ty_vars)
            .map(|var| var.name() + 1)
            .max()
            .unwrap_or(0)
    }

    fn effect_var_capacity<'t>(
        types: impl IntoIterator<Item = &'t Type>,
        effects: &[EffType],
    ) -> u32 {
        types
            .into_iter()
            .flat_map(TypeLike::inner_effect_vars)
            .chain(effects.iter().flat_map(EffType::inner_vars))
            .map(|var| var.name() + 1)
            .max()
            .unwrap_or(0)
    }

    /// Finish solving and release borrowed module definitions before committing
    /// generated functions back to the module.
    #[must_use = "commit the generated functions to the module"]
    pub fn finish(mut self) -> PendingFunctionCollector {
        let initial_count = self.fn_collector.initial_count;
        mem::replace(
            &mut self.fn_collector,
            PendingFunctionCollector::new(initial_count),
        )
    }

    /// Get a specific trait implementation data by its id.
    pub fn get_impl_data_by_id(&self, impl_id: TraitImplId) -> &TraitImpl {
        if impl_id.module == self.current_type_items.module.id
            && let Some(imp) = self.impls.data.get(impl_id.impl_id.as_index())
        {
            return imp;
        }
        &self
            .others
            .get(impl_id.module)
            .unwrap_or_else(|| panic!("module #{} not found", impl_id.module))
            .module()
            .unwrap()
            .impls
            .data[impl_id.impl_id.as_index()]
    }

    /// Get a specific function from a given module.
    /// If necessary, the value dependencies are updated.
    pub fn get_function(
        &mut self,
        use_site: Location,
        module_path: &module::Path,
        function_name: Ustr,
    ) -> Result<FunctionId, InternalCompilationError> {
        let module_not_found_error = || {
            internal_compilation_error!(Internal {
                error: format!(
                    "Module {module_path} not found when looking for function {function_name}"
                ),
                span: use_site
            })
        };
        let (module_id, entry) = self
            .others
            .get_by_name(module_path)
            .ok_or_else(module_not_found_error)?;
        let module = entry.module().ok_or_else(module_not_found_error)?;
        let function_id = module.get_local_function_id(function_name).ok_or_else(|| {
            internal_compilation_error!(Internal {
                error: format!("Function {function_name} not found in module {module_path}"),
                span: use_site
            })
        })?;
        Ok(self.function_id(module_id, function_id))
    }

    /// Look up an existing named function without rebuilding a function-only index.
    pub(crate) fn current_function(&self, name: Ustr) -> Option<LocalFunctionId> {
        let (_, def) = self.current_def_table.get_by_name(&name)?;
        if let Some(id) = def.kind.as_function() {
            return Some(*id);
        }
        // Helper lookup historically selected the last named function even if
        // a later non-function shadowed it. Preserve that behavior only for an
        // indexed name; ordinary misses must not scan the definition table.
        self.current_def_table
            .iter()
            .filter_map(|(def, entry_name)| {
                (*entry_name == Some(name))
                    .then(|| def.kind.as_function().copied())
                    .flatten()
            })
            .last()
    }

    /// Get a function from the current module if it is defined locally, otherwise import it.
    pub fn get_local_or_import_function(
        &mut self,
        use_site: Location,
        module_path: &module::Path,
        function_name: Ustr,
    ) -> Result<FunctionId, InternalCompilationError> {
        // We are only interested in named functions, not trait impl functions or lambdas, so we can ignore fn_collector.
        // if let Some(local_id) = self.fn_collector.get_function(function_name) {
        //     return Ok(self.function_id(self.current_type_items.module.id, local_id));
        // }
        if let Some(local_id) = self.current_function(function_name) {
            return Ok(self.function_id(self.current_type_items.module.id, local_id));
        }
        self.get_function(use_site, module_path, function_name)
    }

    /// Get a specific subscript member from a given module.
    /// If necessary, the value dependencies are updated.
    pub fn get_subscript_member(
        &mut self,
        use_site: Location,
        module_path: &module::Path,
        subscript_name: Ustr,
        mut_member: bool,
    ) -> Result<FunctionId, InternalCompilationError> {
        let module_not_found_error = || {
            internal_compilation_error!(Internal {
                error: format!(
                    "Module {module_path} not found when looking for subscript {subscript_name}"
                ),
                span: use_site
            })
        };
        let (module_id, entry) = self
            .others
            .get_by_name(module_path)
            .ok_or_else(module_not_found_error)?;
        let module = entry.module().ok_or_else(module_not_found_error)?;
        let subscript = module.get_subscript(subscript_name).ok_or_else(|| {
            internal_compilation_error!(Internal {
                error: format!("Subscript {subscript_name} not found in module {module_path}"),
                span: use_site
            })
        })?;
        let member = if mut_member {
            subscript.mut_member.as_ref()
        } else {
            subscript.ref_member.as_ref()
        };
        let Some(member) = member else {
            let member_name = if mut_member { "mut" } else { "ref" };
            return Err(internal_compilation_error!(Internal {
                error: format!(
                    "Subscript {subscript_name} in module {module_path} has no {member_name} member"
                ),
                span: use_site
            }));
        };
        Ok(self.function_id(module_id, member.function))
    }

    fn function_id(&mut self, module_id: ModuleId, function_id: LocalFunctionId) -> FunctionId {
        if module_id != self.current_type_items.module.id {
            self.deps.insert(module_id);
        }
        FunctionId::new(module_id, function_id)
    }

    fn impl_id(&mut self, module_id: ModuleId, impl_id: LocalImplId) -> TraitImplId {
        if module_id != self.current_type_items.module.id {
            self.deps.insert(module_id);
        }
        TraitImplId::new(module_id, impl_id)
    }
}

impl<'a> Drop for TraitSolver<'a> {
    fn drop(&mut self) {
        if !self.fn_collector.new_elements.is_empty() {
            log::warn!(
                "TraitSolver dropped without committing the created functions. Call .finish().commit() to store them in the module."
            );
        }
    }
}

impl TypePropertyEnv for TraitSolver<'_> {
    fn has_trivial_copy_impl(&self, ty: Type) -> bool {
        let key = trivial_copy_impl_key(self.std_trait_id(TRIVIAL_COPY_TRAIT_NAME), ty);
        self.has_canonical_trait_impl(&key)
    }

    fn type_def(&self, id: TypeDefId) -> &TypeDef {
        TraitSolver::type_def(self, id)
    }
}
