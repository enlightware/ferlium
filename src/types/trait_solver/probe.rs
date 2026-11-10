// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Scratch solver overlays and the output-query interface shared by matching and improvement.

use std::{borrow::Cow, mem, rc::Rc};

use crate::{
    FxHashSet, Location, Modules,
    compiler::error::InternalCompilationError,
    hir::NodeArena,
    module::{
        CurrentTypeItems, DefTable, Module, ModuleId, PendingFunctionCollector, TraitId,
        TraitImpls, id::Id,
    },
    types::{
        effect_polarity::EffectPolarity, effects::EffType, r#type::Type,
        type_inference::unify::UnifiedTypeInference, type_scheme::PubTypeConstraint,
    },
};

use super::{
    CurrentProjectionSubscriptTypes, TraitSolver,
    improvement::{TraitImprovementKey, TraitImprovementMatch},
    is_compiler_provided_no_output_trait_application,
};

/// Scratch overlay for running trait-solver queries without mutating a real module.
pub(crate) struct TraitSolverProbe<'a> {
    current_type_items: CurrentTypeItems<'a>,
    pub(super) impls: Cow<'a, TraitImpls>,
    current_def_table: &'a DefTable,
    current_projection_subscript_types: CurrentProjectionSubscriptTypes<'a>,
    deps: FxHashSet<ModuleId>,
    fn_collector: PendingFunctionCollector,
    active_improvements: FxHashSet<TraitImprovementKey>,
    privileged_impl_module: Option<ModuleId>,
    others: &'a Modules,
}

/// Stub `TraitOutputQuery` for paths that statically never invoke a query
/// (concrete candidate matching only unifies types and never reaches `match_blanket_impl`).
pub(super) struct NeverProbe;

impl TraitOutputQuery for NeverProbe {
    fn output_effect_polarities_query(&mut self, _trait_id: TraitId) -> Vec<EffectPolarity> {
        unreachable!("concrete candidate matching never queries nested trait outputs")
    }

    fn unify_non_trait_constraint_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        constraint: &PubTypeConstraint,
        _assumptions: ConstraintAssumptions<'_>,
        _arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        ty_inf.unify_structural_pub_constraint(constraint)
    }

    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        _trait_id: TraitId,
        _input_tys: &[Type],
        _output_tys: &[Type],
        _output_effs: &[EffType],
    ) -> bool {
        false
    }

    fn solve_outputs_query(
        &mut self,
        _trait_id: TraitId,
        _input_tys: &[Type],
        _output_effs: Option<&[EffType]>,
        _fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        unreachable!(
            "NeverProbe should not be queried — concrete candidates do not call match_blanket_impl"
        )
    }

    fn solve_outputs_by_structure_query(
        &mut self,
        _trait_id: TraitId,
        _input_tys: &[Type],
        _fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        unreachable!("concrete improvement candidates have no nested queries")
    }

    fn improve_trait_application_query(
        &mut self,
        _ty_inf: &mut UnifiedTypeInference,
        _trait_id: TraitId,
        _input_tys: &[Type],
        _output_tys: Option<&[Type]>,
        _output_effs: Option<&[EffType]>,
        _assumptions: ConstraintAssumptions<'_>,
        _fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        unreachable!(
            "NeverProbe should not be queried — concrete candidates do not call match_blanket_impl"
        )
    }
}

/// Minimal query interface needed by blanket matching.
///
/// This is a trait so the same matching code can run either against the real
/// solver, which may materialize concrete impls, or against `TraitSolverProbe`,
/// which answers the same questions through a scratch overlay.
pub(super) trait TraitOutputQuery {
    fn unify_non_trait_constraint_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        constraint: &PubTypeConstraint,
        assumptions: ConstraintAssumptions<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError>;

    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> bool;

    /// The outputs of the implementation selected for `input_tys`; requested output effects, if
    /// any, take part in matching it.
    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_effs: Option<&[EffType]>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError>;

    /// The outputs of the impl that `trait_id` selects for `input_tys` by structure, ignoring all
    /// effects: an impl selected with the wrong effects still gives its output types.
    fn solve_outputs_by_structure_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError>;

    /// The polarity of each output effect of `trait_id`.
    fn output_effect_polarities_query(&mut self, trait_id: TraitId) -> Vec<EffectPolarity>;

    /// Attempt to improve a trait application. `output_tys` and `output_effs`
    /// are `None` only for solver queries that intentionally ask for outputs
    /// from inputs alone; stored `HaveTrait` constraints pass full-arity lists.
    #[allow(clippy::too_many_arguments)]
    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError>;
}

/// Lazily materializes a scratch solver only if blanket matching reaches a
/// nested trait query. Head matching can reject many candidates without
/// needing to clone the solver state.
pub(super) struct LazyTraitSolverProbe<'solver, 'a> {
    solver: &'solver TraitSolver<'a>,
    probe: Option<TraitSolverProbe<'a>>,
}

impl<'solver, 'a> LazyTraitSolverProbe<'solver, 'a> {
    pub(super) fn new(solver: &'solver TraitSolver<'a>) -> Self {
        Self {
            solver,
            probe: None,
        }
    }

    fn probe(&mut self) -> &mut TraitSolverProbe<'a> {
        if self.probe.is_none() {
            self.probe = Some(TraitSolverProbe::from_solver(self.solver));
        }
        self.probe.as_mut().unwrap()
    }
}

impl TraitOutputQuery for LazyTraitSolverProbe<'_, '_> {
    fn output_effect_polarities_query(&mut self, trait_id: TraitId) -> Vec<EffectPolarity> {
        self.solver.output_effect_polarities(trait_id)
    }

    fn unify_non_trait_constraint_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        constraint: &PubTypeConstraint,
        assumptions: ConstraintAssumptions<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        self.probe()
            .unify_non_trait_constraint_query(ty_inf, constraint, assumptions, arena)
    }

    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> bool {
        self.probe().is_compiler_provided_no_output_trait_query(
            trait_id,
            input_tys,
            output_tys,
            output_effs,
        )
    }

    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_effs: Option<&[EffType]>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.probe()
            .solve_outputs_query(trait_id, input_tys, output_effs, fn_span, arena)
    }

    fn solve_outputs_by_structure_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        self.probe()
            .solve_outputs_by_structure_query(trait_id, input_tys, fn_span)
    }

    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        self.probe().improve_trait_application_query(
            ty_inf,
            trait_id,
            input_tys,
            output_tys,
            output_effs,
            assumptions,
            fn_span,
            arena,
        )
    }
}

/// Borrowed view over the ambient public trait constraints that may discharge
/// nested blanket-impl requirements.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ConstraintAssumptions<'a> {
    constraints: &'a [&'a PubTypeConstraint],
    skipped_index: Option<usize>,
}

impl<'a> ConstraintAssumptions<'a> {
    pub(crate) fn all(constraints: &'a [&'a PubTypeConstraint]) -> Self {
        Self {
            constraints,
            skipped_index: None,
        }
    }

    pub(crate) fn excluding(
        constraints: &'a [&'a PubTypeConstraint],
        skipped_index: usize,
    ) -> Self {
        Self {
            constraints,
            skipped_index: Some(skipped_index),
        }
    }

    pub(crate) fn iter(self) -> impl Iterator<Item = &'a PubTypeConstraint> {
        self.constraints
            .iter()
            .enumerate()
            .filter_map(move |(index, constraint)| {
                (self.skipped_index != Some(index)).then_some(*constraint)
            })
    }
}

impl<'a> TraitSolverProbe<'a> {
    pub(crate) fn from_module(module: &'a Module, others: &'a Modules) -> Self {
        Self {
            current_type_items: CurrentTypeItems::new_from_module(module),
            impls: Cow::Borrowed(&module.impls),
            current_def_table: &module.def_table,
            current_projection_subscript_types: CurrentProjectionSubscriptTypes::from_module(
                module,
            ),
            deps: module.deps.clone(),
            fn_collector: PendingFunctionCollector::new(module.functions.len()),
            active_improvements: FxHashSet::default(),
            privileged_impl_module: None,
            others,
        }
    }

    pub(super) fn from_solver(solver: &TraitSolver<'a>) -> Self {
        let mut impls = solver.impls.clone();
        // Most probes have no private concrete entries. Do not detach the shared
        // index for a retain that would leave it unchanged.
        if impls
            .concrete_key_to_id
            .values()
            .any(|id| !impls.data[id.as_index()].public)
        {
            Rc::make_mut(&mut impls.concrete_key_to_id).retain(|_, id| {
                let imp = &impls.data[id.as_index()];
                imp.public || imp.source_span.is_some()
            });
        }
        Self {
            current_type_items: solver.current_type_items,
            impls: Cow::Owned(impls),
            current_def_table: solver.current_def_table,
            current_projection_subscript_types: solver.current_projection_subscript_types.clone(),
            deps: solver.deps.clone(),
            fn_collector: solver.fn_collector.clone(),
            active_improvements: solver.active_improvements.clone(),
            privileged_impl_module: solver.privileged_impl_module,
            others: solver.others,
        }
    }

    pub(super) fn with_solver<R>(&mut self, f: impl FnOnce(&mut TraitSolver<'_>) -> R) -> R {
        let initial_count = self.fn_collector.initial_count;
        let fn_collector = mem::replace(
            &mut self.fn_collector,
            PendingFunctionCollector::new(initial_count),
        );
        let mut solver = TraitSolver::new(
            self.current_type_items,
            self.impls.to_mut(),
            self.current_def_table,
            &mut self.deps,
            self.current_projection_subscript_types.clone(),
            fn_collector,
            self.others,
        );
        solver.active_improvements = mem::take(&mut self.active_improvements);
        solver.privileged_impl_module = self.privileged_impl_module;
        let result = f(&mut solver);
        self.active_improvements = mem::take(&mut solver.active_improvements);
        self.privileged_impl_module = solver.privileged_impl_module;
        self.current_projection_subscript_types
            .cache_materialized_types_from(&solver.current_projection_subscript_types);
        self.fn_collector = mem::replace(
            &mut solver.fn_collector,
            PendingFunctionCollector::new(initial_count),
        );
        result
    }

    pub(crate) fn concrete_type_is_trivial_copy(&mut self, ty: Type) -> bool {
        self.with_solver(|solver| solver.concrete_type_is_trivial_copy(ty))
    }
}

impl TraitOutputQuery for TraitSolverProbe<'_> {
    fn output_effect_polarities_query(&mut self, trait_id: TraitId) -> Vec<EffectPolarity> {
        self.with_solver(|solver| solver.output_effect_polarities(trait_id))
    }

    fn unify_non_trait_constraint_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        constraint: &PubTypeConstraint,
        assumptions: ConstraintAssumptions<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        self.with_solver(|solver| {
            ty_inf.unify_pub_constraint(constraint, assumptions, |_| false, solver, arena)
        })
    }

    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> bool {
        self.with_solver(|solver| {
            is_compiler_provided_no_output_trait_application(
                trait_id,
                solver.trait_def(trait_id),
                input_tys,
                output_tys,
                output_effs,
                solver,
            )
        })
    }

    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_effs: Option<&[EffType]>,
        fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.with_solver(|solver| {
            solver.solve_application_outputs_without_materializing(
                trait_id,
                input_tys,
                None,
                output_effs,
                fn_span,
            )
        })
    }

    fn solve_outputs_by_structure_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        self.with_solver(|solver| {
            solver.solve_outputs_by_structure_query(trait_id, input_tys, fn_span)
        })
    }

    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        self.with_solver(|solver| {
            solver.improve_trait_application_match(
                ty_inf,
                trait_id,
                input_tys,
                output_tys,
                output_effs,
                assumptions,
                true,
                fn_span,
                arena,
            )
        })
    }
}

impl TraitOutputQuery for TraitSolver<'_> {
    fn output_effect_polarities_query(&mut self, trait_id: TraitId) -> Vec<EffectPolarity> {
        self.output_effect_polarities(trait_id)
    }

    fn unify_non_trait_constraint_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        constraint: &PubTypeConstraint,
        assumptions: ConstraintAssumptions<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        ty_inf.unify_pub_constraint(constraint, assumptions, |_| false, self, arena)
    }

    fn is_compiler_provided_no_output_trait_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> bool {
        is_compiler_provided_no_output_trait_application(
            trait_id,
            self.trait_def(trait_id),
            input_tys,
            output_tys,
            output_effs,
            self,
        )
    }

    fn solve_outputs_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_effs: Option<&[EffType]>,
        fn_span: Location,
        _arena: &mut NodeArena,
    ) -> Result<(Vec<Type>, Vec<EffType>), InternalCompilationError> {
        self.solve_application_outputs_without_materializing(
            trait_id,
            input_tys,
            None,
            output_effs,
            fn_span,
        )
    }

    fn solve_outputs_by_structure_query(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<Vec<Type>, InternalCompilationError> {
        let selecting_by_structure = mem::replace(&mut self.selecting_by_structure, true);
        let result = self.solve_application_outputs_without_materializing(
            trait_id, input_tys, None, None, fn_span,
        );
        self.selecting_by_structure = selecting_by_structure;
        result.map(|(output_tys, _)| output_tys)
    }

    fn improve_trait_application_query(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        self.improve_trait_application_match(
            ty_inf,
            trait_id,
            input_tys,
            output_tys,
            output_effs,
            assumptions,
            true,
            fn_span,
            arena,
        )
    }
}
