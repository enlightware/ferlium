// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Trait application selection, symbolic resolution, and output queries.

use std::{borrow::Cow, mem, rc::Rc};

use crate::{
    FxHashMap, FxHashSet, Location,
    compiler::error::InternalCompilationError,
    hir::{NodeArena, value::LiteralValue},
    internal_compilation_error,
    module::{
        BlanketTraitImplSubKey, CandidateSearch, ConcreteTraitImplKey, FunctionId,
        GeneratedImplSource, ImplGenericNames, LocalImplId, Module, ModuleEnv, ModuleId,
        TraitDictionary, TraitId, TraitImpl, TraitImplId, id::Id, named_modules_in_environment,
    },
    std::core_traits_names::{REPR_TRAIT_NAME, VALUE_TRAIT_NAME},
    types::{
        effects::{EffType, EffectVar},
        r#trait::{TraitAssociatedConstIndex, TraitMethodIndex},
        r#type::Type,
        type_inference::{substitution::InstSubst, unify::UnifiedTypeInference},
        type_like::{TypeLike, instantiate_types},
        type_mapper::{BitmapInstantiationMapper, EffectErasingMapper, TypeMapper},
        type_scheme::PubTypeConstraint,
    },
};

use super::{
    SelectionFrame, SymbolicApplication, TRAIT_SOLVER_RECURSION_LIMIT, TraitSolver,
    canonical::application_key,
    matching::{
        BlanketCandidate, BlanketConstraintMode, DefaultedEffectRowsMapper, MatchedRequirement,
        UnresolvedConstraints, input_heads_may_match, visible_blanket_impls,
    },
    probe::TraitOutputQuery,
};

/// What selection finds for an application: how it is served, and the outputs that this
/// gives. Selecting an application builds nothing.
#[derive(Debug)]
pub(super) struct Selection {
    pub(super) output_tys: Vec<Type>,
    pub(super) output_effs: Vec<EffType>,
    pub(super) found: Found,
    /// What was selected for the applications that this selection asked for: construction
    /// follows these, instead of selecting them again where things may stand otherwise.
    pub(super) nested: Vec<CachedSelection>,
}

/// How an application is served.
#[derive(Debug)]
pub(super) enum Found {
    /// By an impl that exists.
    Impl(TraitImplId),
    /// `Repr`, which the head of its input gives.
    Repr,
    /// By a blanket impl at an instantiation, whose requirements hold.
    Blanket(SelectedBlanket),
    /// By the derivation of the trait's deriver at this index, whose requirements hold.
    Derived(usize),
    /// The application is being selected, and asked for again on the way: it holds if that
    /// selection does. Its dictionary is then reserved before it is asked for again.
    InProgress,
}

/// A blanket impl selected for an application.
#[derive(Debug)]
pub(super) struct SelectedBlanket {
    /// The module of the impl, `None` for the current one.
    pub(super) module: Option<ModuleId>,
    pub(super) impl_id: LocalImplId,
    pub(super) sub_key: BlanketTraitImplSubKey,
    pub(super) requirements: Vec<MatchedRequirement>,
    /// The generic parameters of the impl at this application.
    pub(super) instantiation: InstSubst,
}

/// A selection kept for later requests, with all that it is a function of besides the impls.
#[derive(Debug)]
pub(super) struct CachedSelection {
    trait_id: TraitId,
    input_tys: Vec<Type>,
    /// The outputs that the request named, `None` where it named none: an impl whose outputs
    /// do not follow from its inputs gives them by the request.
    requested_output_tys: Option<Vec<Type>>,
    requested_output_effs: Option<Vec<EffType>>,
    privileged_impl_module: Option<ModuleId>,
    /// Whether the selection is by structure, with all effects ignored: it is then none for a
    /// request with effects, even without any effect in its types.
    by_structure: bool,
    pub(super) selection: Rc<Selection>,
    /// For a provisional selection, the applications still being selected that it asked for,
    /// by their position in the stack, each with whether the path from it to where the
    /// selection was made may close a circle: what was found holds where these paths are the
    /// same. Empty for a final selection.
    paths: Vec<(usize, bool)>,
}

impl CachedSelection {
    fn answers(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        privileged_impl_module: Option<ModuleId>,
        by_structure: bool,
    ) -> bool {
        self.trait_id == trait_id
            && self.input_tys == input_tys
            && self.requested_output_tys.as_deref() == requested_output_tys
            && self.requested_output_effs.as_deref() == requested_output_effs
            && self.privileged_impl_module == privileged_impl_module
            && self.by_structure == by_structure
    }
}

impl<'a> TraitSolver<'a> {
    /// Check if a concrete trait implementation exists, without performing any solving.
    /// This searches in current module first, then in other modules.
    /// Only public implementations from other modules are considered.
    /// An absence that a pending impl may fill is recorded as blocked.
    pub fn has_concrete_impl(&self, key: &ConcreteTraitImplKey) -> bool {
        let found = self.impls.concrete_key_to_id.contains_key(key)
            || named_modules_in_environment(self.others, self.current_type_items.environment).any(
                |(_, module)| {
                    let impls = &module.impls;
                    impls.concrete_key_to_id.get(key).is_some_and(|id| {
                        self.can_use_other_impl(module.module_id(), &impls.data[id.as_index()])
                    })
                },
            );
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
        let found = self
            .others
            .enumerates()
            .filter(|(id, _, _)| self.current_type_items.environment.contains(id))
            .find_map(|(module_id, entry, _)| {
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
        for (module_path, module) in
            named_modules_in_environment(self.others, self.current_type_items.environment)
        {
            let impls = &module.impls;
            if impls.blanket_key_to_id.contains_key(&trait_id) {
                log::trace!("In module {}:", module_path);
                impls.log_debug_impls_headers(trait_id, env);
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

    /// Solve an application to a dictionary: one that exists, or the one built from what
    /// selection finds for the application.
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
        if self.impls.ignores_effects && !self.selecting_by_structure {
            // Only types are sought: the application is decided by structure, as are the
            // requests it makes in turn.
            let input_tys = instantiate_types(input_tys, &mut EffectErasingMapper);
            let requested_output_tys =
                requested_output_tys.map(|tys| instantiate_types(tys, &mut EffectErasingMapper));
            self.selecting_by_structure = true;
            let result = self.solve_impl_application(
                trait_id,
                &input_tys,
                requested_output_tys.as_deref(),
                None,
                fn_span,
                arena,
            );
            self.selecting_by_structure = false;
            return result;
        }
        // The quantified variables name the top-level request's variables only; nested requests
        // made while materializing are in the implementation's variables.
        let quantified_effect_vars = mem::take(&mut self.quantified_request_effect_vars);
        if let Some(impl_id) = self.existing_dictionary(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            &quantified_effect_vars,
            fn_span,
        ) {
            return Ok(impl_id);
        }
        let selection = match self.planned_selection(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            &quantified_effect_vars,
        ) {
            Some(selection) => selection,
            None => self.select(
                trait_id,
                input_tys,
                requested_output_tys,
                requested_output_effs,
                &quantified_effect_vars,
                fn_span,
            )?,
        };
        let key = (trait_id, input_tys.to_vec());
        let outermost = self.building.insert(key.clone());
        if !outermost && !matches!(selection.found, Found::Impl(_) | Found::Repr) {
            // Asked for again while it is being built, and no dictionary of it exists yet:
            // building it again would not end.
            return Err(internal_compilation_error!(TraitSolverCycleDetected {
                trait_ref: trait_id,
                input_tys: input_tys.to_vec(),
                fn_span,
            }));
        }
        self.plans.push(selection.clone());
        let result = self.build(
            &selection,
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            fn_span,
            arena,
        );
        self.plans.pop();
        if outermost {
            self.building.remove(&key);
        }
        result
    }

    /// What the selection being built found for an application it asked for, if anything.
    fn planned_selection(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        quantified_effect_vars: &FxHashSet<EffectVar>,
    ) -> Option<Rc<Selection>> {
        if !quantified_effect_vars.is_empty() {
            return None;
        }
        let (key_output_tys, key_output_effs) =
            self.request_key(trait_id, requested_output_tys, requested_output_effs);
        self.plans
            .last()?
            .nested
            .iter()
            .find(|nested| {
                nested.answers(
                    trait_id,
                    input_tys,
                    key_output_tys,
                    key_output_effs,
                    self.privileged_impl_module,
                    self.selecting_by_structure,
                )
            })
            .map(|nested| nested.selection.clone())
    }

    /// The dictionary that serves an application, if one exists already: an impl for its
    /// inputs, or a dictionary generated for it, which may still be under construction.
    fn existing_dictionary(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        quantified_effect_vars: &FxHashSet<EffectVar>,
        fn_span: Location,
    ) -> Option<TraitImplId> {
        let concrete_key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
        if let Some(imp) = self.get_concrete_impl(&concrete_key)
            && self.impl_matches_requested_outputs(
                self.get_impl_data_by_id(imp),
                requested_output_tys,
                requested_output_effs,
                quantified_effect_vars,
                fn_span,
            )
        {
            return Some(imp);
        }
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
            return Some(TraitImplId::new(
                self.current_type_items.module.id,
                local_impl_id,
            ));
        }
        // The application its inputs determine serves a request naming outputs it has.
        if requested_output_tys.is_some() || requested_output_effs.is_some() {
            let inputs_key = application_key(trait_id, input_tys, None, None);
            if let Some(local_impl_id) = self.impls.application_key_to_id.get(&inputs_key).copied()
                && self.generated_impl_is_visible(local_impl_id)
                && self.impl_matches_requested_outputs(
                    &self.impls.data[local_impl_id.as_index()],
                    requested_output_tys,
                    requested_output_effs,
                    quantified_effect_vars,
                    fn_span,
                )
            {
                return Some(TraitImplId::new(
                    self.current_type_items.module.id,
                    local_impl_id,
                ));
            }
        }
        None
    }

    /// Select what serves an application, without building anything; see [`Selection`].
    pub(super) fn select_application(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        fn_span: Location,
    ) -> Result<Rc<Selection>, InternalCompilationError> {
        assert!(
            input_tys.iter().all(|ty| ty.is_trait_input_resolved()),
            "Selecting a trait implementation for unresolved input type shapes"
        );
        if self.impls.ignores_effects && !self.selecting_by_structure {
            // Only types are sought: the application is decided by structure, as are the
            // requests it makes in turn.
            let input_tys = instantiate_types(input_tys, &mut EffectErasingMapper);
            let requested_output_tys =
                requested_output_tys.map(|tys| instantiate_types(tys, &mut EffectErasingMapper));
            self.selecting_by_structure = true;
            let result = self.select_application(
                trait_id,
                &input_tys,
                requested_output_tys.as_deref(),
                None,
                fn_span,
            );
            self.selecting_by_structure = false;
            return result;
        }
        let quantified_effect_vars = mem::take(&mut self.quantified_request_effect_vars);
        self.select(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            &quantified_effect_vars,
            fn_span,
        )
    }

    /// Select what serves an application: the selection kept from an earlier request, a
    /// dictionary that exists, or what [`Self::select_actual`] finds.
    ///
    /// Impls of a trait without outputs may require one another in a circle: an application
    /// asked for again while it is being selected holds if that selection does, provided that
    /// each application on the circle may be part of one. What is selected in between, held or
    /// not, depends on the path back to that application: it is provisional, and is used again
    /// only where that path is the same, until that application is selected. This is how
    /// rustc's trait solver keeps the results that depend on a cycle.
    ///
    /// What is found is recorded for the selection under way, whose construction follows it.
    fn select(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        quantified_effect_vars: &FxHashSet<EffectVar>,
        fn_span: Location,
    ) -> Result<Rc<Selection>, InternalCompilationError> {
        let selection = self.select_unrecorded(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            quantified_effect_vars,
            fn_span,
        )?;
        if !matches!(selection.found, Found::Impl(_))
            && let Some(frame) = self.solving_stack.last()
            && !frame
                .nested
                .iter()
                .any(|nested| nested.trait_id == trait_id && nested.input_tys == input_tys)
        {
            let (key_output_tys, key_output_effs) =
                self.request_key(trait_id, requested_output_tys, requested_output_effs);
            let nested = CachedSelection {
                trait_id,
                input_tys: input_tys.to_vec(),
                requested_output_tys: key_output_tys.map(<[Type]>::to_vec),
                requested_output_effs: key_output_effs.map(<[EffType]>::to_vec),
                privileged_impl_module: self.privileged_impl_module,
                by_structure: self.selecting_by_structure,
                selection: selection.clone(),
                paths: Vec::new(),
            };
            self.solving_stack
                .last_mut()
                .expect("the frame checked above")
                .nested
                .push(nested);
        }
        Ok(selection)
    }

    /// The outputs that a request names, as selections are kept by: requesting the outputs of a
    /// trait that has none requests nothing.
    fn request_key<'r>(
        &self,
        trait_id: TraitId,
        requested_output_tys: Option<&'r [Type]>,
        requested_output_effs: Option<&'r [EffType]>,
    ) -> (Option<&'r [Type]>, Option<&'r [EffType]>) {
        let trait_def = self.trait_def(trait_id);
        (
            requested_output_tys.filter(|_| trait_def.output_type_count() > 0),
            requested_output_effs.filter(|_| trait_def.output_effect_count() > 0),
        )
    }

    /// [`Self::select`], without recording what is found.
    fn select_unrecorded(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        quantified_effect_vars: &FxHashSet<EffectVar>,
        fn_span: Location,
    ) -> Result<Rc<Selection>, InternalCompilationError> {
        let allows_recursive_impls = self.trait_def(trait_id).allows_recursive_impls();
        let (key_output_tys, key_output_effs) =
            self.request_key(trait_id, requested_output_tys, requested_output_effs);
        // A request whose caller quantifies effect variables reads the requested outputs by
        // them: its selection is its own.
        let shared = quantified_effect_vars.is_empty();
        if shared
            && let Some(selection) =
                self.kept_selection(trait_id, input_tys, key_output_tys, key_output_effs)
        {
            return Ok(selection);
        }
        if let Some(impl_id) = self.existing_dictionary(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            quantified_effect_vars,
            fn_span,
        ) {
            return Ok(Rc::new(self.selection_of_impl(impl_id)));
        }

        if let Some(start) = self
            .solving_stack
            .iter()
            .position(|frame| frame.trait_id == trait_id && frame.input_tys.as_slice() == input_tys)
        {
            // Whether the circle holds depends on the path back: so does what is found from here.
            self.rest_on(start);
            if !self.path_may_close_circle(start) {
                return Err(internal_compilation_error!(TraitSolverCycleDetected {
                    trait_ref: trait_id,
                    input_tys: input_tys.to_vec(),
                    fn_span,
                }));
            }
            return Ok(Rc::new(Selection {
                output_tys: Vec::new(),
                output_effs: Vec::new(),
                found: Found::InProgress,
                nested: Vec::new(),
            }));
        }
        if shared
            && let Some(selection) =
                self.provisional_selection(trait_id, input_tys, key_output_tys, key_output_effs)
        {
            return Ok(selection);
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
        // A blanket impl of a trait without outputs reserves its dictionary first.
        let depth = self.solving_stack.len();
        self.solving_stack.push(SelectionFrame {
            trait_id,
            input_tys: input_tys.to_vec(),
            may_close_circle: allows_recursive_impls,
            heads: Vec::new(),
            provisional: Vec::new(),
            nested: Vec::new(),
        });
        #[cfg(debug_assertions)]
        let made = (self.impls.data.len(), self.fn_collector.new_elements.len());
        let result = self.select_actual(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            quantified_effect_vars,
            fn_span,
        );
        #[cfg(debug_assertions)]
        debug_assert_eq!(
            made,
            (self.impls.data.len(), self.fn_collector.new_elements.len()),
            "selection builds nothing"
        );
        let frame = self
            .solving_stack
            .pop()
            .expect("the frame of this selection");
        self.recursion_depth -= 1;

        // What this selection asked for while it was being selected, now done, no longer
        // matters; what it asked for below, whether it holds or not, is asked for by the
        // selection under way too. The selections made on the way that rested on this one last
        // go with its frame.
        let heads = frame
            .heads
            .into_iter()
            .filter(|&start| start < depth)
            .collect::<Vec<_>>();
        for &start in &heads {
            self.rest_on(start);
        }
        let mut selection = result?;
        selection.nested = frame.nested;
        let selection = Rc::new(selection);
        // An impl that exists is found again as fast.
        if shared && !matches!(selection.found, Found::Impl(_)) {
            let cached = CachedSelection {
                trait_id,
                input_tys: input_tys.to_vec(),
                requested_output_tys: key_output_tys.map(<[Type]>::to_vec),
                requested_output_effs: key_output_effs.map(<[EffType]>::to_vec),
                privileged_impl_module: self.privileged_impl_module,
                by_structure: self.selecting_by_structure,
                selection: selection.clone(),
                paths: heads
                    .iter()
                    .map(|&start| (start, self.path_may_close_circle(start)))
                    .collect(),
            };
            match heads.iter().max() {
                None => self.selections.entry(trait_id).or_default().push(cached),
                Some(&innermost) => self.solving_stack[innermost].provisional.push(cached),
            }
        }
        Ok(selection)
    }

    /// Whether each application on the path from the one selected at `start` of the stack to
    /// the top may be part of a circle, so that asking for that application from here closes one.
    fn path_may_close_circle(&self, start: usize) -> bool {
        self.solving_stack[start..]
            .iter()
            .all(|frame| frame.may_close_circle)
    }

    /// Record that the selection under way asked for the application selected at `start` of the
    /// stack, or for what rests on it.
    fn rest_on(&mut self, start: usize) {
        let heads = &mut self
            .solving_stack
            .last_mut()
            .expect("an application is asked for while another is being selected")
            .heads;
        if !heads.contains(&start) {
            heads.push(start);
        }
    }

    /// A provisional selection made for this request on a path that, back to each application
    /// still being selected that it asked for, is the same as the path from here.
    fn provisional_selection(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
    ) -> Option<Rc<Selection>> {
        let (selection, heads) = self
            .solving_stack
            .iter()
            .rev()
            .flat_map(|frame| &frame.provisional)
            .find(|kept| {
                kept.answers(
                    trait_id,
                    input_tys,
                    requested_output_tys,
                    requested_output_effs,
                    self.privileged_impl_module,
                    self.selecting_by_structure,
                ) && kept
                    .paths
                    .iter()
                    .all(|&(start, may_close)| self.path_may_close_circle(start) == may_close)
            })
            .map(|kept| {
                (
                    kept.selection.clone(),
                    kept.paths
                        .iter()
                        .map(|&(start, _)| start)
                        .collect::<Vec<_>>(),
                )
            })?;
        for start in heads {
            self.rest_on(start);
        }
        Some(selection)
    }

    /// Whether the application of `trait_id` to `input_tys` is being selected.
    pub(super) fn is_being_selected(&self, trait_id: TraitId, input_tys: &[Type]) -> bool {
        self.solving_stack
            .iter()
            .any(|frame| frame.trait_id == trait_id && frame.input_tys.as_slice() == input_tys)
    }

    fn selection_of_impl(&self, impl_id: TraitImplId) -> Selection {
        let imp = self.get_impl_data_by_id(impl_id);
        Selection {
            output_tys: imp.output_tys.clone(),
            output_effs: imp.output_effs.clone(),
            found: Found::Impl(impl_id),
            nested: Vec::new(),
        }
    }

    /// Find what serves an application: an impl for its inputs, else the first blanket impl
    /// that applies, else what a deriver of the trait makes.
    #[allow(clippy::too_many_arguments)]
    fn select_actual(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        quantified_effect_vars: &FxHashSet<EffectVar>,
        fn_span: Location,
    ) -> Result<Selection, InternalCompilationError> {
        // Special case for `Repr` trait.
        if trait_id == self.std_trait_id(REPR_TRAIT_NAME) {
            let input_ty = input_tys[0];
            let output_ty = self.repr_of_head(input_ty, fn_span)?.unwrap_or(input_ty);
            return Ok(Selection {
                output_tys: vec![output_ty],
                output_effs: Vec::new(),
                found: Found::Repr,
                nested: Vec::new(),
            });
        }

        // If a concrete implementation is found, it serves the application.
        let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
        if let Some(imp) = self.get_concrete_impl(&key) {
            if self.impl_matches_requested_outputs(
                self.get_impl_data_by_id(imp),
                requested_output_tys,
                requested_output_effs,
                quantified_effect_vars,
                fn_span,
            ) {
                return Ok(self.selection_of_impl(imp));
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
        let mode = BlanketConstraintMode {
            by_structure: self.selecting_by_structure,
            unresolved: UnresolvedConstraints::Reject,
        };
        let mut arena = NodeArena::default();
        if let Some(selection) = self.select_blanket_candidate(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            mode,
            &mut search,
            fn_span,
            &mut arena,
            |solver, candidate, _| solver.accept_blanket_candidate(candidate, input_tys, fn_span),
        )? {
            return Ok(selection);
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
        if let Some(found) = self.select_derivation(trait_id, input_tys, fn_span)? {
            if let Found::Impl(impl_id) = found {
                return Ok(self.selection_of_impl(impl_id));
            }
            // A trait with derivers has no outputs.
            return Ok(Selection {
                output_tys: Vec::new(),
                output_effs: Vec::new(),
                found,
                nested: Vec::new(),
            });
        }

        // No matching implementation found.
        log::trace!(
            "No matching impl for trait \"{}\" found. Existing impls:",
            self.trait_def(trait_id).name
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

    /// Accept a blanket candidate whose head and constraints match if its requirements hold as
    /// their dictionaries will be built, or return `None` to go on to the next candidate.
    fn accept_blanket_candidate(
        &mut self,
        candidate: BlanketCandidate<'_>,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Option<Selection>, InternalCompilationError> {
        if !self.requirements_hold(&candidate.runtime_requirements, fn_span, false)? {
            self.reject_if_requirements_fail_on_effects(
                &candidate.runtime_requirements,
                input_tys,
                fn_span,
            )?;
            return Ok(None);
        }
        Ok(Some(Selection {
            output_tys: candidate.output_tys,
            output_effs: candidate.output_effs,
            found: Found::Blanket(SelectedBlanket {
                module: candidate.module,
                impl_id: candidate.impl_id,
                sub_key: candidate.sub_key.clone(),
                requirements: candidate.runtime_requirements,
                instantiation: candidate.instantiation,
            }),
            nested: Vec::new(),
        }))
    }

    /// The first deriver of the trait that serves an application, once the impls that its
    /// derivation requires hold, or an impl derived already for it.
    fn select_derivation(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Option<Found>, InternalCompilationError> {
        let (allows_recursive_impls, derivers) = {
            let trait_def = self.trait_def(trait_id);
            (
                trait_def.allows_recursive_impls(),
                trait_def.derivers.clone(),
            )
        };
        let input_tys = Self::derivation_input_tys(input_tys);
        // A written impl whose head matches the application serves it alone: if its prerequisites
        // fail, that is an error, never a reason to derive another impl.
        if !derivers.is_empty() && self.written_head_matches(trait_id, &input_tys) {
            return Ok(None);
        }
        // An impl derived at inputs without effects serves them with effects.
        if let Cow::Owned(input_tys) = &input_tys
            && let Some(impl_id) =
                self.get_concrete_impl(&ConcreteTraitImplKey::new(trait_id, input_tys.clone()))
        {
            return Ok(Some(Found::Impl(impl_id)));
        }
        for (index, deriver) in derivers.iter().enumerate() {
            let Some(requirements) = deriver.requirements(trait_id, &input_tys, self) else {
                continue;
            };
            self.solving_stack
                .last_mut()
                .expect("a derivation is selected for the application being selected")
                .may_close_circle = allows_recursive_impls && requirements.reserves;
            for member in requirements.members {
                self.select_application(trait_id, &[member], None, None, fn_span)?;
            }
            return Ok(Some(Found::Derived(index)));
        }
        Ok(None)
    }

    /// Whether the head of a written impl of the trait that is visible here matches the
    /// application, whatever its prerequisites. Effects never select an impl, so the heads are
    /// compared without them.
    fn written_head_matches(&self, trait_id: TraitId, input_tys: &[Type]) -> bool {
        let span = Location::new_synthesized();
        let input_tys = instantiate_types(input_tys, &mut EffectErasingMapper);
        let input_tys = input_tys.as_slice();
        visible_blanket_impls(
            &self.impls.blanket_key_to_id,
            self.others,
            self.current_type_items.environment,
            trait_id,
        )
        .any(|(module, blankets)| {
            blankets.iter().any(|(sub_key, impl_id)| {
                if !input_heads_may_match(&sub_key.input_tys, input_tys) {
                    return false;
                }
                if let Some(module_id) = module {
                    let imp = &self
                        .others
                        .get(module_id)
                        .and_then(|entry| entry.module())
                        .expect("a visible module")
                        .impls
                        .data[impl_id.as_index()];
                    if !self.can_use_other_impl(module_id, imp) {
                        return false;
                    }
                }
                let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(
                    Self::type_var_capacity_for_types(input_tys),
                );
                for _ in 0..Self::effect_var_capacity(input_tys, &[]) {
                    ty_inf.fresh_effect_var();
                }
                let inst_subst = (
                    ty_inf.fresh_type_var_subst(sub_key.ty_var_count),
                    ty_inf.fresh_effect_var_subst(sub_key.eff_var_count),
                );
                let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
                let heads = instantiate_types(&sub_key.input_tys, &mut mapper);
                instantiate_types(&heads, &mut EffectErasingMapper)
                    .iter()
                    .zip(input_tys)
                    .all(|(head, input_ty)| {
                        ty_inf
                            .unify_same_type_with_sub_effects(*head, span, *input_ty, span)
                            .is_ok()
                    })
            })
        })
    }

    /// The inputs that an application is derived at. Derived implementations do not depend on
    /// the effects of the callables in their input types: derive them for these effects at their
    /// least solution, which any row includes. This holds because no derived method calls a
    /// callable of its input: they print, hash, compare, clone or drop it, and serialization and
    /// defaults have no callable instance.
    fn derivation_input_tys(input_tys: &[Type]) -> Cow<'_, [Type]> {
        let effect_vars = input_tys
            .iter()
            .flat_map(TypeLike::inner_effect_vars)
            .collect::<FxHashSet<_>>();
        if effect_vars.is_empty() {
            return Cow::Borrowed(input_tys);
        }
        let subst = (
            FxHashMap::default(),
            effect_vars
                .into_iter()
                .map(|var| (var, EffType::empty()))
                .collect(),
        );
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        Cow::Owned(input_tys.iter().map(|ty| ty.map(&mut mapper)).collect())
    }

    /// Build the impl of an application with the deriver that selection chose for it.
    fn derive_application(
        &mut self,
        deriver_index: usize,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        let input_tys = Self::derivation_input_tys(input_tys);
        let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
        if let Some(impl_id) = self.get_concrete_impl(&key) {
            return Ok(impl_id);
        }
        let deriver = self.trait_def(trait_id).derivers[deriver_index].clone();
        let Some(impl_id) = deriver.derive_impl(trait_id, &input_tys, fn_span, arena, self)? else {
            return Err(internal_compilation_error!(Internal {
                error: format!(
                    "a deriver of trait {} serves {:?} but did not derive it",
                    self.trait_def(trait_id).name,
                    input_tys
                ),
                span: fn_span,
            }));
        };
        if impl_id.module == self.current_type_items.module.id {
            let scope = self.derivation_scope(trait_id);
            Rc::make_mut(&mut self.impls.generated_sources)
                .insert(impl_id.impl_id, GeneratedImplSource::Derived { scope });
        }
        Ok(impl_id)
    }

    /// Build the dictionary of an application from what selection found for it.
    #[allow(clippy::too_many_arguments)]
    fn build(
        &mut self,
        selection: &Selection,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImplId, InternalCompilationError> {
        match &selection.found {
            Found::Impl(impl_id) => Ok(*impl_id),
            Found::Repr => {
                // Only search in current module, create a new implementation if not found.
                let key = ConcreteTraitImplKey::new(trait_id, input_tys.to_vec());
                let local_id = if let Some(id) = self.impls.concrete_key_to_id.get(&key) {
                    *id
                } else {
                    let imp = TraitImpl {
                        trait_id,
                        input_tys: input_tys.to_vec(),
                        output_tys: selection.output_tys.clone(),
                        output_effs: vec![],
                        methods: vec![],
                        associated_const_values: vec![],
                        associated_const_getters: vec![],
                        dictionary_value: TraitDictionary::new(&[], &[]),
                        dictionary_ty: Type::tuple([]),
                        public: false,
                        source_span: None,
                        generic_names: ImplGenericNames::default(),
                    };
                    self.impls.add_concrete_struct(key, imp)
                };
                Ok(TraitImplId::new(
                    self.current_type_items.module.id,
                    local_id,
                ))
            }
            Found::Blanket(blanket) => self.materialize_selected_blanket(
                trait_id,
                input_tys,
                requested_output_tys,
                requested_output_effs,
                selection,
                blanket,
                fn_span,
                arena,
            ),
            Found::Derived(index) => {
                self.derive_application(*index, trait_id, input_tys, fn_span, arena)
            }
            // A circle holds where each application on it has its dictionary reserved before it is
            // asked for again, and found then; what selection gives in progress has none yet.
            Found::InProgress => Err(internal_compilation_error!(TraitSolverCycleDetected {
                trait_ref: trait_id,
                input_tys: input_tys.to_vec(),
                fn_span,
            })),
        }
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
        let by_structure =
            trait_id == self.std_trait_id(VALUE_TRAIT_NAME) || self.impls.ignores_effects;
        let (selection_input_tys, mode) = if by_structure {
            (
                instantiate_types(input_tys, &mut EffectErasingMapper),
                BlanketConstraintMode::by_structure(UnresolvedConstraints::Reject),
            )
        } else {
            (
                input_tys.to_vec(),
                BlanketConstraintMode::with_effects(UnresolvedConstraints::Reject),
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

    /// The final selection kept for a request of this solver, if any.
    pub(super) fn kept_selection(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
    ) -> Option<Rc<Selection>> {
        self.selections
            .get(&trait_id)?
            .iter()
            .find(|kept| {
                kept.answers(
                    trait_id,
                    input_tys,
                    requested_output_tys,
                    requested_output_effs,
                    self.privileged_impl_module,
                    self.selecting_by_structure,
                )
            })
            .map(|kept| kept.selection.clone())
    }

    /// The outputs of an application, without building its dictionary.
    ///
    /// Type inference and defaulting ask whether an application exists and what outputs it
    /// determines while types and effects are still provisional. Final HIR elaboration calls
    /// [`solve_impl`](Self::solve_impl), and is the only phase that builds dictionaries.
    pub(super) fn solve_application_outputs_without_materializing(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        fn_span: Location,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        let selection = self.select_application(
            trait_id,
            input_tys,
            requested_output_tys,
            requested_output_effs,
            fn_span,
        )?;
        Ok((selection.output_tys.clone(), selection.output_effs.clone()))
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
