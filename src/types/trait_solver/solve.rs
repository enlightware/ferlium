// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Trait application selection, symbolic resolution, and output queries.

use std::{mem, rc::Rc};

use crate::{
    FxHashMap, FxHashSet, Location,
    compiler::error::InternalCompilationError,
    hir::{NodeArena, value::LiteralValue},
    internal_compilation_error,
    module::{
        CandidateSearch, ConcreteTraitImplKey, FunctionId, GeneratedImplSource, Module, ModuleEnv,
        ModuleId, TraitDictionary, TraitId, TraitImpl, TraitImplId, id::Id,
    },
    std::core_traits_names::{REPR_TRAIT_NAME, VALUE_TRAIT_NAME},
    types::{
        effects::{EffType, EffectVar},
        r#trait::{TraitAssociatedConstIndex, TraitMethodIndex},
        r#type::Type,
        type_inference::unify::UnifiedTypeInference,
        type_like::{TypeLike, instantiate_types},
        type_mapper::{BitmapInstantiationMapper, EffectErasingMapper, TypeMapper},
        type_scheme::PubTypeConstraint,
    },
};

use super::{
    SymbolicApplication, TRAIT_SOLVER_RECURSION_LIMIT, TraitSolver,
    canonical::application_key,
    matching::{BlanketCandidate, BlanketConstraintMode, DefaultedEffectRowsMapper},
    probe::TraitOutputQuery,
};

/// The trait selection context that can affect a probe's semantic answer.
#[derive(Debug, Clone)]
pub(super) struct TraitOutputCacheEntry {
    input_tys: Vec<Type>,
    privileged_impl_module: Option<ModuleId>,
    output_tys: Vec<Type>,
    pub(super) output_effs: Vec<EffType>,
}

impl<'a> TraitSolver<'a> {
    /// Check if a concrete trait implementation exists, without performing any solving.
    /// This searches in current module first, then in other modules.
    /// Only public implementations from other modules are considered.
    /// An absence that a pending impl may fill is recorded as blocked.
    pub fn has_concrete_impl(&self, key: &ConcreteTraitImplKey) -> bool {
        let found = self.impls.concrete_key_to_id.contains_key(key)
            || self.others.iter_named().any(|(_, entry)| {
                entry.module().is_some_and(|module| {
                    let impls = &module.impls;
                    let id = impls.concrete_key_to_id.get(key);
                    if let Some(id) = id {
                        self.can_use_other_impl(module.module_id(), &impls.data[id.as_index()])
                    } else {
                        false
                    }
                })
            });
        if !found {
            self.impls.pending.blocks(key.trait_id, &key.input_tys);
        }
        found
    }

    /// Whether an implementation applies to these inputs by structure, with effects ignored,
    /// as selection sees them, without keeping what solving generates.
    pub(crate) fn has_impl_by_structure(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> bool {
        self.solve_outputs_by_structure_query(trait_id, input_tys, fn_span)
            .is_ok()
    }

    /// Get a concrete trait implementation by its key, without performing any solving.
    /// This searches in current module first, then in other modules.
    /// Only public implementations from other modules are considered.
    /// If found in other modules, the value dependencies are updated.
    pub fn get_concrete_impl(&mut self, key: &ConcreteTraitImplKey) -> Option<TraitImplId> {
        if let Some(&id) = self.impls.concrete_key_to_id.get(key)
            && self.generated_impl_is_visible(id)
        {
            return Some(TraitImplId::new(self.current_type_items.module.id, id));
        }
        let found = self.others.enumerates().find_map(|(module_id, entry, _)| {
            entry.module().and_then(|module| {
                let impls = &module.impls;
                impls.concrete_key_to_id.get(key).and_then(|id| {
                    let imp = &impls.data[id.as_index()];
                    if self.can_use_other_impl(module_id, imp) {
                        Some((module_id, *id))
                    } else {
                        None
                    }
                })
            })
        });
        found.map(|(module_id, impl_id)| {
            self.deps.insert(module_id);
            TraitImplId::new(module_id, impl_id)
        })
    }

    /// Print all known implementations for the given trait id.
    fn log_debug_impls(&self, trait_id: TraitId) {
        if !log::log_enabled!(log::Level::Trace) {
            return;
        }
        log::trace!("In current module:");
        let mut fake_current = Module::new(
            self.current_type_items.module.id,
            self.current_type_items.module.path.clone(),
        );
        fake_current.type_aliases = self.current_type_items.type_aliases.clone();
        fake_current.traits = self.current_type_items.traits.to_vec();
        let env = ModuleEnv::new(&fake_current, self.others);
        self.impls.log_debug_impls_headers(trait_id, env);
        for (module_path, entry) in self.others.iter_named() {
            if let Some(module) = entry.module() {
                let impls = &module.impls;
                if impls.blanket_key_to_id.contains_key(&trait_id) {
                    log::trace!("In module {}:", module_path);
                    impls.log_debug_impls_headers(trait_id, env);
                }
            }
        }
    }

    /// Get a concrete trait implementation for the given trait id and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This is the trait solver's core function.
    /// The implementation for the application `trait_id` at `input_tys`, requested with the
    /// outputs it was inferred with: a dictionary is for the application it is requested for.
    /// Outputs that are missing or still open are left out of the request.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn solve_impl_for_application(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        quantified_effect_vars: &FxHashSet<EffectVar>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        // Inference is over: an effect variable the caller does not quantify can no longer grow,
        // so it takes its least solution, the empty row. Closing it here, once, leaves nested
        // requests with only the caller's quantified variables.
        let mut flexible = FxHashSet::default();
        for ty in input_tys.iter().chain(output_tys) {
            flexible.extend(ty.inner_effect_vars());
        }
        for eff in output_effs {
            eff.fill_with_inner_effect_vars(&mut flexible);
        }
        flexible.retain(|var| !quantified_effect_vars.contains(var));
        let closed;
        let (input_tys, output_tys, output_effs) = if flexible.is_empty() {
            (input_tys, output_tys, output_effs)
        } else {
            let mut mapper = DefaultedEffectRowsMapper {
                variables: &flexible,
            };
            closed = (
                instantiate_types(input_tys, &mut mapper),
                instantiate_types(output_tys, &mut mapper),
                output_effs
                    .iter()
                    .map(|eff| mapper.map_effect_type(eff))
                    .collect::<Vec<_>>(),
            );
            (&closed.0[..], &closed.1[..], &closed.2[..])
        };
        let trait_def = self.trait_def(trait_id);
        let requested_output_tys = (output_tys.len() == trait_def.output_type_count() as usize
            && output_tys.iter().all(|ty| ty.is_constant()))
        .then_some(output_tys);
        let requested_output_effs =
            (output_effs.len() == trait_def.output_effect_count() as usize).then_some(output_effs);
        let previous = mem::replace(
            &mut self.quantified_request_effect_vars,
            quantified_effect_vars.clone(),
        );
        let result = self.solve_impl_application(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            fn_span,
            arena,
        );
        self.quantified_request_effect_vars = previous;
        result
    }

    pub fn solve_impl(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        self.solve_impl_application(trait_id, input_tys, None, None, fn_span, arena)
    }

    #[allow(clippy::too_many_arguments)]
    fn solve_impl_application(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        // Sanity checks
        assert!(
            input_tys.iter().all(|ty| ty.is_trait_input_resolved()),
            "Getting trait implementation for unresolved input type shapes"
        );
        // The quantified variables name the top-level request's variables only; nested requests
        // made while materializing are in the implementation's variables.
        let quantified_effect_vars = mem::take(&mut self.quantified_request_effect_vars);

        // Cycle detection
        let key = (trait_id, input_tys.to_vec());
        let concrete_key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
        if let Some(imp) = self.get_concrete_impl(&concrete_key) {
            if self.impl_matches_requested_outputs(
                self.get_impl_data_by_id(imp),
                requested_output_tys,
                requested_output_effs,
                &quantified_effect_vars,
                fn_span,
            ) {
                return Ok(imp);
            }
        }
        {
            let canonical_key = application_key(
                trait_id,
                input_tys,
                requested_output_tys,
                requested_output_effs,
            );
            if let Some(local_impl_id) = self
                .impls
                .application_key_to_id
                .get(&canonical_key)
                .copied()
                && self.generated_impl_is_visible(local_impl_id)
            {
                return Ok(TraitImplId::new(
                    self.current_type_items.module.id,
                    local_impl_id,
                ));
            }
        }
        if self.solving_stack.contains(&key) {
            return Err(internal_compilation_error!(TraitSolverCycleDetected {
                trait_ref: trait_id,
                input_tys: input_tys.to_vec(),
                fn_span,
            }));
        }

        // Recursion limit check
        if self.recursion_depth > TRAIT_SOLVER_RECURSION_LIMIT {
            // Callers may read this failure as "this impl does not apply", yet nothing is known.
            self.impls.pending.block_all();
            return Err(internal_compilation_error!(
                TraitSolverRecursionLimitExceeded {
                    trait_ref: trait_id,
                    input_tys: input_tys.to_vec(),
                    fn_span,
                }
            ));
        }

        self.recursion_depth += 1;
        self.solving_stack.insert(key.clone());

        let result = self.solve_impl_actual(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            &quantified_effect_vars,
            fn_span,
            arena,
        );

        self.solving_stack.remove(&key);
        self.recursion_depth -= 1;
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn solve_impl_actual(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        quantified_effect_vars: &FxHashSet<EffectVar>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        let value_trait_id = self.std_trait_id(VALUE_TRAIT_NAME);
        // Special case for `Repr` trait.
        if trait_id == self.std_trait_id(REPR_TRAIT_NAME) {
            let input_ty = input_tys[0];
            let ty_data = input_ty.data();
            let output_ty = if ty_data.is_named() {
                let named = ty_data.as_named().unwrap().clone();
                self.reject_inaccessible_private_repr(named.def, fn_span)?;
                self.type_def(named.def)
                    .instantiated_shape_with_effects(&named.params, &named.effect_params)
            } else {
                input_ty
            };

            // Only search in current module, create a new implementation if not found.
            let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
            let local_id = if let Some(id) = self.impls.concrete_key_to_id.get(&key) {
                *id
            } else {
                let imp = TraitImpl {
                    trait_id,
                    output_tys: vec![output_ty],
                    output_effs: vec![],
                    methods: vec![],
                    associated_const_values: vec![],
                    associated_const_getters: vec![],
                    dictionary_value: TraitDictionary::new(&[], &[]),
                    dictionary_ty: Type::tuple([]),
                    public: false,
                    source_span: None,
                };
                self.impls.add_concrete_struct(key, imp)
            };
            return Ok(TraitImplId::new(
                self.current_type_items.module.id,
                local_id,
            ));
        }

        // If a concrete implementation is found, return it.
        let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
        if let Some(imp) = self.get_concrete_impl(&key) {
            if self.impl_matches_requested_outputs(
                self.get_impl_data_by_id(imp),
                requested_output_tys,
                requested_output_effs,
                quantified_effect_vars,
                fn_span,
            ) {
                return Ok(imp);
            }
            // The inputs select this impl: outputs differing only in effects are not a reason to
            // look for another one.
            if let Some(requested_output_tys) = requested_output_tys
                && !self.selecting_by_structure
                && instantiate_types(requested_output_tys, &mut EffectErasingMapper)
                    == instantiate_types(
                        &self.get_impl_data_by_id(imp).output_tys,
                        &mut EffectErasingMapper,
                    )
                && requested_output_tys != &self.get_impl_data_by_id(imp).output_tys[..]
            {
                return Err(internal_compilation_error!(TraitImplEffectsMismatch {
                    input_ty: input_tys[0],
                    fn_span,
                }));
            }
        }

        // No concrete implementation found, search for a matching blanket implementation.
        let mut search = CandidateSearch::new(&self.impls.pending);
        let blanket_constraint_mode = if self.selecting_by_structure {
            BlanketConstraintMode::Structural
        } else if trait_id == value_trait_id {
            BlanketConstraintMode::DeferConcreteObligations
        } else {
            BlanketConstraintMode::RequireAllResolved
        };
        if let Some(impl_id) = self.select_blanket_candidate(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            blanket_constraint_mode,
            &mut search,
            fn_span,
            arena,
            |solver, candidate, arena| {
                solver.materialize_blanket_candidate(
                    trait_id,
                    input_tys,
                    requested_output_tys,
                    requested_output_effs,
                    candidate,
                    fn_span,
                    arena,
                )
            },
        )? {
            return Ok(impl_id);
        }

        // A pending impl may still provide this application: neither derive nor conclude that
        // none exists.
        if self.impls.pending.blocks(trait_id, input_tys) {
            return Err(internal_compilation_error!(TraitImplNotFound {
                trait_ref: trait_id,
                input_tys: input_tys.to_vec(),
                fn_span,
            }));
        }

        // No blanket implementation found, look for a derived implementation.
        let (trait_name, derivers) = {
            let trait_def = self.trait_def(trait_id);
            (trait_def.name, trait_def.derivers.clone())
        };
        // Derived implementations do not depend on the effects of the callables in their input
        // types: derive them for these effects at their least solution, which any row includes.
        // This holds because no derived method calls a callable of its input: they print, hash,
        // compare, clone or drop it, and serialization and defaults have no callable instance.
        let effect_vars = input_tys
            .iter()
            .flat_map(TypeLike::inner_effect_vars)
            .collect::<FxHashSet<_>>();
        let erased_input_tys;
        let input_tys = if effect_vars.is_empty() {
            input_tys
        } else {
            let subst = (
                FxHashMap::default(),
                effect_vars
                    .into_iter()
                    .map(|var| (var, EffType::empty()))
                    .collect(),
            );
            let mut mapper = BitmapInstantiationMapper::new(&subst);
            erased_input_tys = input_tys
                .iter()
                .map(|ty| ty.map(&mut mapper))
                .collect::<Vec<_>>();
            let key = ConcreteTraitImplKey::new(trait_id, erased_input_tys.clone());
            if let Some(impl_id) = self.get_concrete_impl(&key) {
                return Ok(impl_id);
            }
            &erased_input_tys
        };
        for derive in derivers {
            if let Some(impl_id) = derive.derive_impl(trait_id, input_tys, fn_span, arena, self)? {
                if impl_id.module == self.current_type_items.module.id {
                    let scope = self.derivation_scope(trait_id);
                    Rc::make_mut(&mut self.impls.generated_sources)
                        .insert(impl_id.impl_id, GeneratedImplSource::Derived { scope });
                }
                return Ok(impl_id);
            } else {
                log::trace!(
                    "Tried derivation for trait {} with input types {:?}, but failed.",
                    trait_name,
                    input_tys
                );
            }
        }

        // No matching implementation found.
        log::trace!(
            "No matching impl for trait \"{}\" found. Existing impls:",
            trait_name
        );
        self.log_debug_impls(trait_id);
        if let Some(requested_output_effs) = requested_output_effs
            && let Some(imp) = self.get_concrete_impl(&key)
        {
            let mismatches = self.output_effect_mismatches(
                self.get_impl_data_by_id(imp),
                requested_output_effs,
                quantified_effect_vars,
                fn_span,
            );
            if !mismatches.is_empty() {
                return Err(internal_compilation_error!(
                    TraitImplOutputEffectsMismatch {
                        trait_ref: trait_id,
                        input_tys: input_tys.to_vec(),
                        mismatches,
                        fn_span,
                    }
                ));
            }
        }
        Err(internal_compilation_error!(TraitImplNotFound {
            trait_ref: trait_id,
            input_tys: input_tys.to_vec(),
            fn_span,
        }))
    }

    /// Get a specific method implementation for the given trait id and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This function is implemented using solve_impl.
    pub fn solve_impl_method(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        index: TraitMethodIndex,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<FunctionId, InternalCompilationError> {
        let impl_id = self.solve_impl(trait_id, input_tys, fn_span, arena)?;
        let method_id = self.get_impl_data_by_id(impl_id).methods[index.as_index()];
        Ok(self.function_id(impl_id.module, method_id))
    }

    /// Get the output types for the given trait id and input types.
    /// If no concrete implementation is found, a matching blanket implementation is searched for.
    /// If matching blanket implementation is found, a derivation is attempted, if available.
    /// Otherwise an error is returned.
    /// This function is implemented using solve_impl.
    pub fn solve_output_types(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        let impl_id = self.solve_impl(trait_id, input_tys, fn_span, arena)?;
        Ok(self.get_impl_data_by_id(impl_id).output_tys.clone())
    }

    /// Get the output types and effects for the given trait id and input types.
    /// This function is implemented using solve_impl, like `solve_output_types`.
    pub fn solve_outputs(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.solve_application_outputs_without_materializing(
            trait_id, input_tys, None, None, fn_span,
        )
    }

    pub(crate) fn resolve_application_symbolically(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: &[Type],
        requested_output_effs: &[EffType],
        fn_span: Location,
    ) -> Result<Option<SymbolicApplication>, InternalCompilationError> {
        // Without effect variables, the prerequisites of a `Value` impl cannot constrain the
        // caller: dictionary construction checks them exactly.
        if trait_id == self.std_trait_id(REPR_TRAIT_NAME)
            || (trait_id == self.std_trait_id(VALUE_TRAIT_NAME)
                && input_tys.iter().all(|ty| ty.inner_effect_vars().is_empty()))
        {
            return Ok(None);
        }
        let snapshot = self.snapshot_derived_impl_state();
        let result = self.resolve_application_symbolically_inner(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            fn_span,
        );
        self.rollback_derived_impl_state(snapshot);
        result
    }

    fn resolve_application_symbolically_inner(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: &[Type],
        requested_output_effs: &[EffType],
        fn_span: Location,
    ) -> Result<Option<SymbolicApplication>, InternalCompilationError> {
        let type_var_base =
            Self::type_var_capacity_for_types(input_tys.iter().chain(requested_output_tys));
        let effect_var_base = Self::effect_var_capacity(
            input_tys.iter().chain(requested_output_tys),
            requested_output_effs,
        );
        let mut arena = NodeArena::default();
        let mut search = CandidateSearch::new(&self.impls.pending);
        // `Value` is selected by structure, as inference does: a nested prerequisite need only
        // hold by structure, its effects become obligations through the instantiated head. Other
        // traits are selected as `solve_impl_actual` does.
        let by_structure = trait_id == self.std_trait_id(VALUE_TRAIT_NAME);
        let (selection_input_tys, mode) = if by_structure {
            (
                instantiate_types(input_tys, &mut EffectErasingMapper),
                BlanketConstraintMode::Structural,
            )
        } else {
            (
                input_tys.to_vec(),
                BlanketConstraintMode::RequireAllResolved,
            )
        };
        let previous = mem::replace(&mut self.selecting_by_structure, by_structure);
        let selected = self.select_blanket_candidate(
            trait_id,
            &selection_input_tys,
            Some(requested_output_tys),
            Some(requested_output_effs),
            mode,
            &mut search,
            fn_span,
            &mut arena,
            |_, candidate, _| {
                Ok(Some(Self::instantiate_symbolic_head(
                    &candidate,
                    input_tys,
                    type_var_base,
                    effect_var_base,
                    fn_span,
                )))
            },
        );
        self.selecting_by_structure = previous;
        selected?.transpose()
    }

    /// Instantiate the head of a selected blanket candidate alone, keeping its constraints as
    /// obligations in terms of the application's variables.
    fn instantiate_symbolic_head(
        candidate: &BlanketCandidate<'_>,
        input_tys: &[Type],
        type_var_base: u32,
        effect_var_base: u32,
        fn_span: Location,
    ) -> Result<SymbolicApplication, InternalCompilationError> {
        let sub_key = candidate.sub_key;
        let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(type_var_base);
        for _ in 0..effect_var_base {
            ty_inf.fresh_effect_var();
        }
        let inst_subst = (
            ty_inf.fresh_type_var_subst(sub_key.ty_var_count),
            ty_inf.fresh_effect_var_subst(sub_key.eff_var_count),
        );
        let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
        let imp_input_tys = instantiate_types(&sub_key.input_tys, &mut mapper);
        let output_tys = instantiate_types(&candidate.declared_output_tys, &mut mapper);
        let output_effs = candidate
            .declared_output_effs
            .iter()
            .map(|eff| mapper.map_effect_type(eff))
            .collect::<Vec<_>>();
        let constraints = sub_key
            .constraints
            .iter()
            // Selection checked the constraints; they matter here only for the outputs
            // they determine, which keep the variables of the application.
            .filter(|constraint| match constraint {
                PubTypeConstraint::HaveTrait {
                    output_tys,
                    output_effs,
                    ..
                } => !output_tys.is_empty() || !output_effs.is_empty(),
                PubTypeConstraint::VariantPayloadLayout { .. } => false,
                _ => true,
            })
            .map(|constraint| constraint.map(&mut mapper))
            .collect::<Vec<_>>();
        for (imp_input_ty, input_ty) in imp_input_tys.iter().zip(input_tys) {
            ty_inf.unify_same_type_with_sub_effects(*imp_input_ty, fn_span, *input_ty, fn_span)?;
        }
        // A prerequisite over the application's effects still has to hold for them: the
        // scratch match above let it choose them.
        let effect_prerequisites = sub_key
            .constraints
            .iter()
            .filter(|constraint| {
                matches!(constraint,
                    PubTypeConstraint::HaveTrait { output_tys, output_effs, .. }
                    if output_tys.is_empty() && output_effs.is_empty())
            })
            .map(|constraint| constraint.map(&mut mapper))
            .filter(|constraint| {
                !ty_inf
                    .substitute_in_constraint(constraint)
                    .inner_effect_vars()
                    .is_empty()
            })
            .collect::<Vec<_>>();
        let constraints = constraints
            .into_iter()
            .chain(effect_prerequisites)
            .collect::<Vec<_>>();
        Ok(SymbolicApplication {
            input_tys: imp_input_tys,
            output_tys: ty_inf.substitute_in_types(&output_tys),
            output_effs: ty_inf.substitute_in_effect_types(&output_effs),
            obligations: constraints
                .iter()
                .map(|constraint| ty_inf.substitute_in_constraint(constraint))
                .collect(),
            type_var_base,
            effect_var_base,
        })
    }

    pub fn solve_application_outputs(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: &[Type],
        requested_output_effs: &[EffType],
        fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.solve_application_outputs_without_materializing(
            trait_id,
            input_tys,
            Some(requested_output_tys),
            Some(requested_output_effs),
            fn_span,
        )
    }

    /// Return a cached answer for a fully concrete, unconstrained output query.
    ///
    /// The cache contains only semantic outputs, never an implementation identity or generated
    /// artifact. Private visibility is part of the key.
    pub(super) fn cached_unmaterialized_outputs(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
    ) -> Option<&TraitOutputCacheEntry> {
        if !input_tys.iter().all(|ty| ty.is_constant()) {
            return None;
        }
        self.unmaterialized_output_cache
            .get(&trait_id)?
            .iter()
            .find(|entry| {
                entry.input_tys == input_tys
                    && entry.privileged_impl_module == self.privileged_impl_module
            })
    }

    fn outputs_are_cacheable(output_tys: &[Type], output_effs: &[EffType]) -> bool {
        output_tys.iter().all(|ty| ty.is_constant())
            && output_effs.iter().all(|eff| !eff.has_variables())
    }

    fn cache_unmaterialized_outputs(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) {
        if !input_tys.iter().all(|ty| ty.is_constant())
            || !Self::outputs_are_cacheable(output_tys, output_effs)
        {
            return;
        }
        let entries = self
            .unmaterialized_output_cache
            .entry(trait_id)
            .or_default();
        if let Some(entry) = entries.iter().find(|entry| {
            entry.input_tys == input_tys
                && entry.privileged_impl_module == self.privileged_impl_module
        }) {
            debug_assert_eq!(entry.output_tys, output_tys);
            debug_assert_eq!(entry.output_effs, output_effs);
            return;
        }
        entries.push(TraitOutputCacheEntry {
            input_tys: input_tys.to_vec(),
            privileged_impl_module: self.privileged_impl_module,
            output_tys: output_tys.to_vec(),
            output_effs: output_effs.to_vec(),
        });
    }

    /// Resolve a trait application's associated outputs without committing its runtime artifacts.
    ///
    /// Type inference and defaulting ask whether an application exists and what outputs it
    /// determines while types and effects are still provisional. The materializing solver remains
    /// the single source of trait-selection semantics, but everything it derives for this query is
    /// transactional: method bodies, associated-const getters, dictionaries, and their cache keys
    /// are rolled back after the outputs have been copied. Final HIR elaboration calls
    /// [`solve_impl`](Self::solve_impl) and is therefore the only phase that retains those runtime
    /// artifacts.
    ///
    /// A scratch HIR arena is deliberate. Some trait derivers synthesize a body while determining
    /// whether they apply; a query must not leave those unused nodes in the expression being
    /// inferred either.
    ///
    /// Fully concrete, unconstrained queries can reuse their associated outputs within this
    /// solver. Constrained output applications can select different answers and are never cached.
    pub(super) fn solve_application_outputs_without_materializing(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        fn_span: Location,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        let unconstrained_output_query =
            requested_output_tys.is_none() && requested_output_effs.is_none();
        // Outputs found by structure come from erased candidates: they must stay out of the cache.
        if unconstrained_output_query
            && !self.selecting_by_structure
            && let Some(cached) = self.cached_unmaterialized_outputs(trait_id, input_tys)
        {
            return Ok((cached.output_tys.clone(), cached.output_effs.clone()));
        }

        let snapshot = self.snapshot_derived_impl_state();
        let mut scratch_arena = NodeArena::default();
        let result = self
            .solve_impl_application(
                trait_id,
                input_tys,
                requested_output_tys,
                requested_output_effs,
                fn_span,
                &mut scratch_arena,
            )
            .map(|impl_id| {
                let imp = self.get_impl_data_by_id(impl_id);
                (imp.output_tys.clone(), imp.output_effs.clone())
            });
        self.rollback_derived_impl_state(snapshot);
        if unconstrained_output_query
            && !self.selecting_by_structure
            && let Ok((output_tys, output_effs)) = &result
        {
            self.cache_unmaterialized_outputs(trait_id, input_tys, output_tys, output_effs);
        }
        result
    }

    pub fn solve_associated_const(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        associated_const_index: TraitAssociatedConstIndex,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<LiteralValue, InternalCompilationError> {
        assert!(
            associated_const_index.as_index() < self.trait_def(trait_id).associated_const_count(),
            "associated const index {} out of bounds for trait {}",
            associated_const_index,
            self.trait_def(trait_id).name
        );
        let impl_id = self.solve_impl(trait_id, input_tys, fn_span, arena)?;
        Ok(self
            .get_impl_data_by_id(impl_id)
            .associated_const_value(associated_const_index)
            .unwrap_or_else(|| {
                panic!(
                    "implementation of trait {} is missing associated const #{}",
                    self.trait_def(trait_id).name,
                    associated_const_index
                )
            }))
    }

    /// Resolve the zero-argument runtime getter for an associated constant.
    pub fn solve_associated_const_getter(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        associated_const_index: TraitAssociatedConstIndex,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<FunctionId, InternalCompilationError> {
        assert!(
            associated_const_index.as_index() < self.trait_def(trait_id).associated_const_count(),
            "associated const index {} out of bounds for trait {}",
            associated_const_index,
            self.trait_def(trait_id).name
        );
        let impl_id = self.solve_impl(trait_id, input_tys, fn_span, arena)?;
        let getter = self
            .get_impl_data_by_id(impl_id)
            .associated_const_getter(associated_const_index)
            .unwrap_or_else(|| {
                panic!(
                    "implementation of trait {} is missing associated const getter #{}",
                    self.trait_def(trait_id).name,
                    associated_const_index
                )
            });
        Ok(FunctionId::new(impl_id.module, getter))
    }
}
