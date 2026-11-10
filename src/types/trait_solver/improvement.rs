// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Refine partially known trait applications without choosing protected generics or effects.

use std::hash::Hash;

use crate::{
    FxHashSet, Location,
    compiler::error::InternalCompilationError,
    hir::NodeArena,
    module::{TraitId, id::Id},
    types::{
        effect_polarity::EffectPolarity,
        effects::EffType,
        r#type::{Type, TypeKind},
        type_inference::unify::UnifiedTypeInference,
        type_like::{TypeLike, instantiate_types},
        type_mapper::{BitmapInstantiationMapper, EffectErasingMapper, TypeMapper},
        type_scheme::PubTypeConstraint,
    },
};

use super::{
    TraitSolver,
    canonical::AlphaCanonicalTypeMapper,
    matching::{BlanketConstraintMode, BlanketImplMatch, input_heads_may_match},
    probe::{ConstraintAssumptions, LazyTraitSolverProbe, NeverProbe, TraitOutputQuery},
};

/// Improvement nests deeper frames than solving, and giving up only leaves an application to be
/// resolved later, so its limit is lower.
const IMPROVEMENT_DEPTH_LIMIT: usize = 32;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct TraitImprovementKey {
    trait_id: TraitId,
    input_tys: Vec<Type>,
    output_tys: Option<Vec<Type>>,
    output_effs: Option<Vec<EffType>>,
}

/// Lightweight visible impl head used while probing whether a partially known
/// trait application already has a unique candidate.
#[derive(Clone)]
pub(super) enum TraitImprovementCandidate {
    /// A fully concrete impl head.
    Concrete {
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        output_effs: Vec<EffType>,
    },
    /// A blanket impl head plus the generic information needed to instantiate
    /// and check its impl constraints.
    Blanket {
        input_tys: Vec<Type>,
        output_tys: Vec<Type>,
        output_effs: Vec<EffType>,
        ty_var_count: u32,
        eff_var_count: u32,
        constraints: Vec<PubTypeConstraint>,
    },
}

/// Whether a visible impl candidate is compatible with the current partially known trait application.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum TraitImprovementMatch {
    /// The candidate is definitely incompatible.
    No,
    /// The candidate might still match later, but some blanket constraints are not resolved enough yet.
    Unknown,
    /// The candidate can already be matched uniquely with the current information.
    Yes,
}

impl<'a> TraitSolver<'a> {
    /// Whether a partially unresolved trait application has enough input-side
    /// shape for improvement to learn from visible impl heads.
    ///
    /// A bare inference variable carries no impl-selection information, but a
    /// resolved or structured input such as `[int]`, `Option<T>`, or
    /// `MapIterator<I, T, O>` can make an impl candidate unique even when some
    /// other input is still unresolved.
    ///
    /// A bare function type is deliberately not a driver here: generic
    /// function values such as `map` or `filter_map` can carry large unresolved
    /// effect/type graphs, and probing ordinary trait impl heads from that
    /// shape cannot select a user-visible impl. Function `Value` handling is
    /// covered by compiler-provided special cases once applicable.
    pub(crate) fn input_tys_can_drive_improvement(input_tys: &[Type]) -> bool {
        input_tys
            .iter()
            .any(|ty| !matches!(&*ty.data(), TypeKind::Variable(_) | TypeKind::Function(_)))
    }

    /// Collect visible impls whose outer input constructors may match the application.
    ///
    /// This is used by trait improvement to probe whether a partially known
    /// trait application already has a unique matching impl.
    fn improvement_candidates(
        &self,
        trait_id: TraitId,
        input_tys: &[Type],
    ) -> Vec<TraitImprovementCandidate> {
        fn semantic_constraints(constraints: &[PubTypeConstraint]) -> Vec<PubTypeConstraint> {
            constraints
                .iter()
                // Payload layout is code-generation evidence. It has no outputs and cannot make
                // an implementation applicable or inapplicable, so speculative improvement must
                // not pay to instantiate and solve it for every candidate. The full constraint
                // list is still used when the selected blanket implementation is materialized.
                .filter(|constraint| {
                    !matches!(constraint, PubTypeConstraint::VariantPayloadLayout { .. })
                })
                .cloned()
                .collect()
        }

        let compatible =
            |candidate_inputs: &[Type]| input_heads_may_match(candidate_inputs, input_tys);
        let mut candidates = Vec::new();

        for (key, id) in self.impls.concrete_key_to_id.iter() {
            if key.trait_id == trait_id {
                let imp = &self.impls.data[id.as_index()];
                if (!imp.public && imp.source_span.is_none()) || !compatible(&key.input_tys) {
                    continue;
                }
                candidates.push(TraitImprovementCandidate::Concrete {
                    input_tys: key.input_tys.clone(),
                    output_tys: imp.output_tys.clone(),
                    output_effs: imp.output_effs.clone(),
                });
            }
        }

        if let Some(blankets) = self.impls.blanket_key_to_id.get(&trait_id) {
            for (sub_key, id) in blankets {
                let imp = &self.impls.data[id.as_index()];
                if !compatible(&sub_key.input_tys) {
                    continue;
                }
                candidates.push(TraitImprovementCandidate::Blanket {
                    input_tys: sub_key.input_tys.clone(),
                    output_tys: imp.output_tys.clone(),
                    output_effs: imp.output_effs.clone(),
                    ty_var_count: sub_key.ty_var_count,
                    eff_var_count: sub_key.eff_var_count,
                    constraints: semantic_constraints(&sub_key.constraints),
                });
            }
        }

        for (_, entry) in self.others.iter_named() {
            let Some(module) = entry.module() else {
                continue;
            };

            for (key, id) in module.impls.concrete_key_to_id.iter() {
                if key.trait_id == trait_id {
                    let imp = &module.impls.data[id.as_index()];
                    if self.can_use_other_impl(module.module_id(), imp)
                        && compatible(&key.input_tys)
                    {
                        candidates.push(TraitImprovementCandidate::Concrete {
                            input_tys: key.input_tys.clone(),
                            output_tys: imp.output_tys.clone(),
                            output_effs: imp.output_effs.clone(),
                        });
                    }
                }
            }

            if let Some(blankets) = module.impls.blanket_key_to_id.get(&trait_id) {
                for (sub_key, id) in blankets {
                    let imp = &module.impls.data[id.as_index()];
                    if self.can_use_other_impl(module.module_id(), imp)
                        && compatible(&sub_key.input_tys)
                    {
                        candidates.push(TraitImprovementCandidate::Blanket {
                            input_tys: sub_key.input_tys.clone(),
                            output_tys: imp.output_tys.clone(),
                            output_effs: imp.output_effs.clone(),
                            ty_var_count: sub_key.ty_var_count,
                            eff_var_count: sub_key.eff_var_count,
                            constraints: semantic_constraints(&sub_key.constraints),
                        });
                    }
                }
            }
        }

        candidates
    }

    /// Check whether a visible impl candidate is compatible with the current
    /// partially known trait application.
    #[allow(clippy::too_many_arguments)]
    fn improvement_candidate_matches<Q: TraitOutputQuery>(
        query: &mut Q,
        ty_inf: &mut UnifiedTypeInference,
        candidate: &TraitImprovementCandidate,
        output_polarities: &[EffectPolarity],
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        match candidate {
            TraitImprovementCandidate::Concrete {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs: candidate_output_effs,
            } => {
                for (candidate_input, input_ty) in candidate_inputs.iter().zip(input_tys.iter()) {
                    if ty_inf
                        .unify_same_type_with_sub_effects(
                            *candidate_input,
                            fn_span,
                            *input_ty,
                            fn_span,
                        )
                        .is_err()
                    {
                        return Ok(TraitImprovementMatch::No);
                    }
                }
                if let Some(output_tys) = output_tys {
                    for (candidate_output, output_ty) in
                        candidate_outputs.iter().zip(output_tys.iter())
                    {
                        if ty_inf
                            .unify_same_type_with_sub_effects(
                                *candidate_output,
                                fn_span,
                                *output_ty,
                                fn_span,
                            )
                            .is_err()
                        {
                            return Ok(TraitImprovementMatch::No);
                        }
                    }
                }
                if let Some(output_effs) = output_effs {
                    for ((candidate_eff, output_eff), polarity) in candidate_output_effs
                        .iter()
                        .zip(output_effs.iter())
                        .zip(output_polarities)
                    {
                        if Self::match_trait_output_effect(
                            ty_inf,
                            candidate_eff,
                            output_eff,
                            *polarity,
                            fn_span,
                        )
                        .is_err()
                        {
                            return Ok(TraitImprovementMatch::No);
                        }
                    }
                }
                Ok(TraitImprovementMatch::Yes)
            }
            TraitImprovementCandidate::Blanket {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs: candidate_output_effs,
                ty_var_count,
                eff_var_count,
                constraints,
            } => Ok(
                match Self::match_blanket_impl(
                    query,
                    ty_inf,
                    candidate_inputs,
                    candidate_outputs,
                    candidate_output_effs,
                    output_polarities,
                    *ty_var_count,
                    *eff_var_count,
                    constraints,
                    input_tys,
                    output_tys,
                    output_effs,
                    assumptions,
                    fn_span,
                    arena,
                    BlanketConstraintMode::AllowUnknown,
                )? {
                    BlanketImplMatch::No => TraitImprovementMatch::No,
                    BlanketImplMatch::Unknown => TraitImprovementMatch::Unknown,
                    BlanketImplMatch::Yes { .. } => TraitImprovementMatch::Yes,
                },
            ),
        }
    }

    /// Whether an improvement candidate may apply when all effects are ignored.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn improvement_candidate_applies_by_structure<Q: TraitOutputQuery>(
        query: &mut Q,
        ty_inf: &mut UnifiedTypeInference,
        candidate: &TraitImprovementCandidate,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<bool, InternalCompilationError> {
        let input_tys = instantiate_types(input_tys, &mut EffectErasingMapper);
        let output_tys = output_tys.map(|tys| instantiate_types(tys, &mut EffectErasingMapper));
        let erased_candidate = match candidate {
            TraitImprovementCandidate::Concrete {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs,
            } => TraitImprovementCandidate::Concrete {
                input_tys: instantiate_types(candidate_inputs, &mut EffectErasingMapper),
                output_tys: instantiate_types(candidate_outputs, &mut EffectErasingMapper),
                output_effs: output_effs.clone(),
            },
            TraitImprovementCandidate::Blanket {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs,
                ty_var_count,
                eff_var_count,
                constraints,
            } => {
                let erased_inputs = instantiate_types(candidate_inputs, &mut EffectErasingMapper);
                let erased_outputs = instantiate_types(candidate_outputs, &mut EffectErasingMapper);
                let erased_constraints = instantiate_types(constraints, &mut EffectErasingMapper);
                let matched = Self::match_blanket_impl(
                    query,
                    ty_inf,
                    &erased_inputs,
                    &erased_outputs,
                    &vec![EffType::empty(); output_effs.len()],
                    &[],
                    *ty_var_count,
                    *eff_var_count,
                    &erased_constraints,
                    &input_tys,
                    output_tys.as_deref(),
                    None,
                    assumptions,
                    fn_span,
                    arena,
                    BlanketConstraintMode::StructuralAllowUnknown,
                )?;
                return Ok(!matches!(matched, BlanketImplMatch::No));
            }
        };
        Ok(!matches!(
            Self::improvement_candidate_matches(
                query,
                ty_inf,
                &erased_candidate,
                &[],
                &input_tys,
                output_tys.as_deref(),
                None,
                assumptions,
                fn_span,
                arena,
            )?,
            TraitImprovementMatch::No
        ))
    }

    fn improve_trait_application_with_candidate_head(
        ty_inf: &mut UnifiedTypeInference,
        candidate: &TraitImprovementCandidate,
        output_polarities: &[EffectPolarity],
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        fn_span: Location,
    ) -> Result<(), InternalCompilationError> {
        match candidate {
            TraitImprovementCandidate::Concrete {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs: candidate_output_effs,
            } => {
                for (candidate_input, input_ty) in candidate_inputs.iter().zip(input_tys.iter()) {
                    ty_inf.unify_same_type_with_sub_effects(
                        *candidate_input,
                        fn_span,
                        *input_ty,
                        fn_span,
                    )?;
                }
                if let Some(output_tys) = output_tys {
                    for (candidate_output, output_ty) in
                        candidate_outputs.iter().zip(output_tys.iter())
                    {
                        ty_inf.unify_same_type_with_sub_effects(
                            *candidate_output,
                            fn_span,
                            *output_ty,
                            fn_span,
                        )?;
                    }
                }
                if let Some(output_effs) = output_effs {
                    for ((candidate_eff, output_eff), polarity) in candidate_output_effs
                        .iter()
                        .zip(output_effs.iter())
                        .zip(output_polarities)
                    {
                        Self::match_trait_output_effect(
                            ty_inf,
                            candidate_eff,
                            output_eff,
                            *polarity,
                            fn_span,
                        )?;
                    }
                }
            }
            TraitImprovementCandidate::Blanket {
                input_tys: candidate_inputs,
                output_tys: candidate_outputs,
                output_effs: candidate_output_effs,
                ty_var_count,
                eff_var_count,
                constraints: _,
            } => {
                let inst_subst = (
                    ty_inf.fresh_type_var_subst(*ty_var_count),
                    ty_inf.fresh_effect_var_subst(*eff_var_count),
                );
                let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
                let candidate_inputs = instantiate_types(candidate_inputs, &mut mapper);
                let candidate_outputs = instantiate_types(candidate_outputs, &mut mapper);
                let candidate_output_effs: Vec<_> = candidate_output_effs
                    .iter()
                    .map(|eff| mapper.map_effect_type(eff))
                    .collect();
                for (candidate_input, input_ty) in candidate_inputs.iter().zip(input_tys.iter()) {
                    ty_inf.unify_same_type_with_sub_effects(
                        *candidate_input,
                        fn_span,
                        *input_ty,
                        fn_span,
                    )?;
                }
                if let Some(output_tys) = output_tys {
                    for (candidate_output, output_ty) in
                        candidate_outputs.iter().zip(output_tys.iter())
                    {
                        ty_inf.unify_same_type_with_sub_effects(
                            *candidate_output,
                            fn_span,
                            *output_ty,
                            fn_span,
                        )?;
                    }
                }
                if let Some(output_effs) = output_effs {
                    for ((candidate_eff, output_eff), polarity) in candidate_output_effs
                        .iter()
                        .zip(output_effs.iter())
                        .zip(output_polarities)
                    {
                        Self::match_trait_output_effect(
                            ty_inf,
                            candidate_eff,
                            output_eff,
                            *polarity,
                            fn_span,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Try to improve a deferred trait application from its partially known
    /// inputs and optional known outputs.
    ///
    /// The algorithm discards incompatible outer input constructors, then probes
    /// the remaining visible impls under a snapshot of the unifier. If exactly one candidate remains
    /// compatible, it commits the visible equalities learned by that probe,
    /// even when some nested blanket constraints are still unresolved.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn improve_trait_application_match(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        answer_used: bool,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        let mut key_mapper = AlphaCanonicalTypeMapper::default();
        let key = TraitImprovementKey {
            trait_id,
            input_tys: ty_inf
                .substitute_in_types(input_tys)
                .into_iter()
                .map(|ty| ty.map(&mut key_mapper))
                .collect(),
            output_tys: output_tys.map(|output_tys| {
                ty_inf
                    .substitute_in_types(output_tys)
                    .into_iter()
                    .map(|ty| ty.map(&mut key_mapper))
                    .collect()
            }),
            output_effs: output_effs.map(|output_effs| {
                output_effs
                    .iter()
                    .map(|eff| {
                        let eff = ty_inf.substitute_in_effect_type(eff);
                        key_mapper.map_effect_type(&eff)
                    })
                    .collect()
            }),
        };
        // A cycle, or nesting over ever-growing types, learns nothing conclusive.
        if self.active_improvements.len() > IMPROVEMENT_DEPTH_LIMIT
            || !self.active_improvements.insert(key.clone())
        {
            return Ok(TraitImprovementMatch::Unknown);
        }
        let result = self.improve_trait_application_match_actual(
            ty_inf,
            trait_id,
            input_tys,
            output_tys,
            output_effs,
            assumptions,
            answer_used,
            fn_span,
            arena,
        );
        self.active_improvements.remove(&key);
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn improve_trait_application_match_actual(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        answer_used: bool,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<TraitImprovementMatch, InternalCompilationError> {
        // Resolve current input bindings before testing heads. Candidate variables
        // belong to the impl's own namespace and must remain wildcards here.
        let normalized_inputs = ty_inf.substitute_in_types(input_tys);
        // A written generic stands for every type: an impl that fits only by narrowing it may
        // apply to some instances, but cannot be selected.
        let generics = ty_inf.declared_generic_roots();
        // When only written generics are unknown and nobody reads the answer, the requirement stays
        // on the caller's signature whatever impls exist, so no impl needs to be looked at. In
        // particular, this does not wait for a pending impl that calls this function.
        if !answer_used
            && !generics.is_empty()
            && self.nothing_to_learn(
                ty_inf,
                trait_id,
                &normalized_inputs,
                output_tys,
                output_effs,
                &generics,
            )
        {
            return Ok(TraitImprovementMatch::Unknown);
        }
        let candidates = self.improvement_candidates(trait_id, &normalized_inputs);
        let output_polarities = self.output_effect_polarities(trait_id);
        let original_vars = input_tys
            .iter()
            .chain(output_tys.unwrap_or_default().iter())
            .flat_map(TypeLike::inner_ty_vars)
            .collect::<FxHashSet<_>>();
        type Candidate = (
            TraitImprovementCandidate,
            TraitImprovementMatch,
            Vec<Type>,
            Option<Vec<Type>>,
        );
        let mut unique_candidate: Option<Candidate> = None;
        let mut found_multiple_candidates = false;

        for candidate in candidates {
            let mut snapshot = ty_inf.snapshot();
            // Concrete candidates only run unification against `ty_inf` and never reach `match_blanket_impl`, so they do not need a probe.
            // Skipping the probe avoids cloning the impl table once per concrete candidate, which is the dominant cost of this loop.
            let matched = match &candidate {
                TraitImprovementCandidate::Concrete { .. } => Self::improvement_candidate_matches(
                    &mut NeverProbe,
                    ty_inf,
                    &candidate,
                    &output_polarities,
                    input_tys,
                    output_tys,
                    output_effs,
                    assumptions,
                    fn_span,
                    arena,
                )?,
                TraitImprovementCandidate::Blanket { .. } => {
                    let mut query = LazyTraitSolverProbe::new(self);
                    Self::improvement_candidate_matches(
                        &mut query,
                        ty_inf,
                        &candidate,
                        &output_polarities,
                        input_tys,
                        output_tys,
                        output_effs,
                        assumptions,
                        fn_span,
                        arena,
                    )?
                }
            };
            // Effects never decide which candidates there are: one ruled out by them alone remains,
            // with what it would teach unknown.
            let matched = if matches!(matched, TraitImprovementMatch::No) {
                ty_inf.rollback_to(snapshot);
                let structural_snapshot = ty_inf.snapshot();
                let by_structure = match &candidate {
                    TraitImprovementCandidate::Concrete { .. } => {
                        Self::improvement_candidate_applies_by_structure(
                            &mut NeverProbe,
                            ty_inf,
                            &candidate,
                            input_tys,
                            output_tys,
                            assumptions,
                            fn_span,
                            arena,
                        )?
                    }
                    TraitImprovementCandidate::Blanket { .. } => {
                        let mut query = LazyTraitSolverProbe::new(self);
                        Self::improvement_candidate_applies_by_structure(
                            &mut query,
                            ty_inf,
                            &candidate,
                            input_tys,
                            output_tys,
                            assumptions,
                            fn_span,
                            arena,
                        )?
                    }
                };
                ty_inf.rollback_to(structural_snapshot);
                snapshot = ty_inf.snapshot();
                if by_structure {
                    TraitImprovementMatch::Unknown
                } else {
                    TraitImprovementMatch::No
                }
            } else {
                matched
            };
            let improved_input_tys = ty_inf.substitute_in_types(input_tys);
            let improved_output_tys =
                output_tys.map(|output_tys| ty_inf.substitute_in_types(output_tys));
            let keeps_generics = ty_inf.declared_generics_intact(&generics);
            ty_inf.rollback_to(snapshot);
            use TraitImprovementMatch::*;
            match matched {
                No => {}
                // This candidate fits only some instances of a written generic, so it may apply
                // but cannot be selected.
                Unknown | Yes if !keeps_generics => {
                    found_multiple_candidates = true;
                    unique_candidate = None;
                }
                Unknown | Yes => {
                    if unique_candidate.is_some() {
                        found_multiple_candidates = true;
                        unique_candidate = None;
                        continue;
                    }
                    unique_candidate =
                        Some((candidate, matched, improved_input_tys, improved_output_tys));
                }
            }
        }

        if found_multiple_candidates {
            return Ok(TraitImprovementMatch::Unknown);
        }
        // A pending impl may be another candidate, or the only one. One that fits only by
        // narrowing a written generic cannot be selected, but it can prevent selecting another.
        if self.impls.pending.blocks(trait_id, &normalized_inputs) {
            return Ok(TraitImprovementMatch::Unknown);
        }
        let Some((candidate, matched, improved_input_tys, improved_output_tys)) = unique_candidate
        else {
            // A deriver may become applicable once the remaining variables are
            // fixed, so absence of a visible impl head is not a definite miss.
            if !self.trait_def(trait_id).derivers.is_empty()
                && !input_tys.iter().all(|ty| ty.is_trait_input_resolved())
            {
                return Ok(TraitImprovementMatch::Unknown);
            }
            return Ok(TraitImprovementMatch::No);
        };

        // Visible impl uniqueness is not conclusive while a trait with derivers
        // still has unresolved inputs: a derived impl may become applicable
        // once those inputs are fixed.
        if !self.trait_def(trait_id).derivers.is_empty()
            && !input_tys.iter().all(|ty| ty.is_trait_input_resolved())
        {
            return Ok(TraitImprovementMatch::Unknown);
        }

        match matched {
            TraitImprovementMatch::No => unreachable!(),
            TraitImprovementMatch::Unknown => {
                let improved_vars = improved_input_tys
                    .iter()
                    .chain(improved_output_tys.as_deref().unwrap_or_default().iter())
                    .flat_map(TypeLike::inner_ty_vars)
                    .collect::<FxHashSet<_>>();
                if improved_vars.is_subset(&original_vars) {
                    for (input_ty, improved_input_ty) in
                        input_tys.iter().zip(improved_input_tys.iter())
                    {
                        ty_inf.unify_same_type_with_sub_effects(
                            *input_ty,
                            fn_span,
                            *improved_input_ty,
                            fn_span,
                        )?;
                    }
                    if let (Some(output_tys), Some(improved_output_tys)) =
                        (output_tys, improved_output_tys.as_deref())
                    {
                        for (output_ty, improved_output_ty) in
                            output_tys.iter().zip(improved_output_tys.iter())
                        {
                            ty_inf.unify_same_type_with_sub_effects(
                                *output_ty,
                                fn_span,
                                *improved_output_ty,
                                fn_span,
                            )?;
                        }
                    }
                } else {
                    Self::improve_trait_application_with_candidate_head(
                        ty_inf,
                        &candidate,
                        &output_polarities,
                        input_tys,
                        output_tys,
                        output_effs,
                        fn_span,
                    )?;
                }
                Ok(TraitImprovementMatch::Unknown)
            }
            TraitImprovementMatch::Yes => Self::improvement_candidate_matches(
                self,
                ty_inf,
                &candidate,
                &output_polarities,
                input_tys,
                output_tys,
                output_effs,
                assumptions,
                fn_span,
                arena,
            ),
        }
    }

    /// Whether the written generics in `generics` are all that a trait application leaves unknown.
    fn nothing_to_learn(
        &self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        generics: &[Type],
    ) -> bool {
        let trait_def = self.trait_def(trait_id);
        if (output_tys.is_none() && trait_def.output_type_count() > 0)
            || (output_effs.is_none() && trait_def.output_effect_count() > 0)
        {
            return false;
        }
        let output_tys = ty_inf.substitute_in_types(output_tys.unwrap_or_default());
        let output_effs = ty_inf.substitute_in_effect_types(output_effs.unwrap_or_default());
        let tys = || input_tys.iter().chain(&output_tys);
        output_effs.iter().all(|eff| eff.inner_vars().is_empty())
            && tys()
                .all(|ty| ty.inner_effect_vars().is_empty() && ty.inner_mut_ty_vars().is_empty())
            && tys()
                .flat_map(TypeLike::inner_ty_vars)
                .all(|var| generics.contains(&Type::variable(var)))
    }

    /// Try to improve a deferred trait application from its partially known
    /// inputs and outputs.
    ///
    /// The algorithm discards incompatible outer input constructors, then probes
    /// the remaining visible impls under a snapshot of the unifier. If exactly one candidate remains
    /// compatible, it commits the visible equalities learned by that probe,
    /// even when some nested blanket constraints are still unresolved.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn try_improve_trait_application(
        &mut self,
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
    ) -> Result<bool, InternalCompilationError> {
        Ok(matches!(
            self.improve_trait_application_match(
                ty_inf,
                trait_id,
                input_tys,
                output_tys,
                output_effs,
                assumptions,
                false,
                fn_span,
                arena,
            )?,
            TraitImprovementMatch::Yes
        ))
    }
}
