// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Impl-head and prerequisite matching, shared by selection and inference improvement.

use std::mem;

use ustr::Ustr;

use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    compiler::error::InternalCompilationError,
    hir::{NodeArena, dictionary::DictionaryReq},
    internal_compilation_error,
    module::{
        BlanketImpls, BlanketTraitImplSubKey, BlanketTraitImpls, CandidateSearch, LocalImplId,
        ModuleId, TraitId, TraitImpl, id::Id,
    },
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        value::{
            is_function_surface_only_value_trait_application, is_value_trait_for_function_type,
        },
    },
    types::{
        effect_polarity::EffectPolarity,
        effects::{EffType, Effect, EffectVar},
        mutability::MutType,
        r#type::{Type, TypeKind},
        type_inference::{
            effect_solver::EffectConstraintOrigin, substitution::InstSubst,
            unify::UnifiedTypeInference,
        },
        type_like::{TypeLike, instantiate_types},
        type_mapper::{
            BitmapInstantiationMapper, EffectErasingMapper, SimpleInstantiationMapper, TypeMapper,
        },
        type_scheme::PubTypeConstraint,
    },
};

use super::{
    TraitSolver,
    improvement::TraitImprovementMatch,
    probe::{ConstraintAssumptions, TraitOutputQuery},
};

#[cfg(debug_assertions)]
use crate::types::type_visitor::AllVarsCollector;

/// Whether an implementation's output effect fits the one a requirement names, by polarity:
/// a performed effect may be smaller, a received one larger. Rows are compared effect by effect,
/// which holds whatever their variables stand for.
pub(crate) fn output_effect_fits(
    solved: &EffType,
    required: &EffType,
    polarity: EffectPolarity,
) -> bool {
    let included =
        |smaller: &EffType, larger: &EffType| smaller.iter().all(|eff| larger.contains(eff));
    match polarity {
        EffectPolarity::Positive => included(solved, required),
        EffectPolarity::Negative => included(required, solved),
        EffectPolarity::Invariant => solved == required,
    }
}

pub(super) struct DefaultedEffectRowsMapper<'a> {
    pub(super) variables: &'a FxHashSet<EffectVar>,
}

impl TypeMapper for DefaultedEffectRowsMapper<'_> {
    fn map_type(&mut self, ty: Type) -> Type {
        ty
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        mut_ty
    }

    fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        eff_ty
            .iter()
            .filter(|effect| match effect {
                Effect::Variable(var) => !self.variables.contains(var),
                Effect::Primitive(_) => true,
            })
            .collect()
    }
}

/// The blanket impls of a trait visible from a module with the given local table: the local
/// ones first, then those of each other module.
pub(super) fn visible_blanket_impls<'b>(
    local: &'b BlanketImpls,
    others: &'b Modules,
    environment: &'b FxHashSet<ModuleId>,
    trait_id: TraitId,
) -> impl Iterator<Item = (Option<ModuleId>, &'b BlanketTraitImpls)> + use<'b> {
    local
        .get(&trait_id)
        .map(|blankets| (None, blankets))
        .into_iter()
        .chain(
            others
                .enumerates()
                .filter(move |(id, _, _)| environment.contains(id))
                .flat_map(move |(module_id, entry, _)| {
                    entry.module().and_then(|module| {
                        module
                            .impls
                            .blanket_key_to_id
                            .get(&trait_id)
                            .map(|blankets| (Some(module_id), blankets))
                    })
                }),
        )
}

/// Whether an impl's input types may match the requested ones, see [`input_head_may_match`].
pub(crate) fn input_heads_may_match(candidates: &[Type], inputs: &[Type]) -> bool {
    candidates
        .iter()
        .zip(inputs)
        .all(|(&candidate, &input)| input_head_may_match(candidate, input))
}

/// A necessary condition for the same-type relation that matches impl inputs.
/// Reject only fixed outer-constructor conflicts; unknowns, nested arguments,
/// mutability and effects still go through the full match. In particular Never
/// is not a wildcard here: matching checks equality, not bottom subtyping.
pub(super) fn input_head_may_match(candidate: Type, input: Type) -> bool {
    use TypeKind::*;
    match (&*candidate.data(), &*input.data()) {
        (Variable(_), _) | (_, Variable(_)) => true,
        (Native(a), Native(b)) => a.bare_ty == b.bare_ty,
        (Named(a), Named(b)) => a.def == b.def,
        (Tuple(a), Tuple(b)) => a.len() == b.len(),
        (Function(a), Function(b)) => a.args.len() == b.args.len(),
        (a, b) => mem::discriminant(a) == mem::discriminant(b),
    }
}

/// A blanket implementation whose inputs match an application, before its caller accepts it.
pub(super) struct BlanketCandidate<'k> {
    /// The module of the implementation, `None` for the current one.
    pub(super) module: Option<ModuleId>,
    pub(super) impl_id: LocalImplId,
    pub(super) sub_key: &'k BlanketTraitImplSubKey,
    /// The implementation's outputs, in its own variables.
    pub(super) declared_output_tys: Vec<Type>,
    pub(super) declared_output_effs: Vec<EffType>,
    /// The outputs at this application.
    pub(super) output_tys: Vec<Type>,
    pub(super) output_effs: Vec<EffType>,
    pub(super) runtime_requirements: Vec<ResolvedRuntimeRequirement>,
    /// The implementation's generic parameters resolved at this application.
    pub(super) instantiation: InstSubst,
}

/// A runtime hidden requirement from a matched blanket impl after substitution.
pub(super) struct ResolvedRuntimeRequirement {
    /// Original source order of the constraint in the blanket impl.
    pub(super) index: usize,
    pub(super) req: DictionaryReq,
}

/// Controls how `match_blanket_impl` treats nested trait constraints that are
/// still not fully resolved after reaching a fixed point.
#[derive(Clone, Copy)]
pub(super) enum BlanketConstraintMode {
    /// Matching is only considered successful if every nested trait constraint
    /// can be resolved immediately.
    RequireAllResolved,
    /// As `RequireAllResolved`, on arguments without effects: whether the impl applies by
    /// structure, which effects never decide. So nested outputs lose their effects too.
    Structural,
    /// As `AllowUnknown`, by structure as in `Structural`.
    StructuralAllowUnknown,
    /// A partially resolved fixed point is reported back as `Unknown` instead
    /// of being treated as a definite mismatch.
    AllowUnknown,
    /// Matching may succeed with concrete nested constraints that cannot be
    /// materialized until after reserving the concrete impl. Currently used for
    /// recursive `Value` materialization.
    DeferConcreteObligations,
}

/// Result of matching a blanket impl against a requested trait application.
pub(super) enum BlanketImplMatch {
    /// The blanket impl is definitely incompatible.
    No,
    /// The blanket impl may still match later, but some nested trait
    /// constraints remain unresolved.
    Unknown,
    /// The blanket impl matches, yielding instantiated output types and effects
    /// and the resolved runtime hidden requirements in source order.
    Yes {
        output_tys: Vec<Type>,
        output_effs: Vec<EffType>,
        runtime_requirements: Vec<ResolvedRuntimeRequirement>,
        /// The blanket implementation's generic parameters resolved at this application.
        instantiation: InstSubst,
    },
}

impl<'a> TraitSolver<'a> {
    /// Relate an implementation's output effect to the requested one by the output's polarity:
    /// an effect the methods perform may be smaller than requested, one they receive larger.
    pub(crate) fn match_trait_output_effect(
        ty_inf: &mut UnifiedTypeInference,
        impl_eff: &EffType,
        requested_eff: &EffType,
        polarity: EffectPolarity,
        fn_span: Location,
    ) -> Result<(), InternalCompilationError> {
        ty_inf.relate_trait_output_effect(
            impl_eff,
            requested_eff,
            polarity,
            fn_span,
            EffectConstraintOrigin::Inference,
        )
    }

    pub(super) fn impl_matches_requested_outputs(
        &self,
        imp: &TraitImpl,
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        quantified_effect_vars: &FxHashSet<EffectVar>,
        fn_span: Location,
    ) -> bool {
        if requested_output_tys.is_none() && requested_output_effs.is_none() {
            return true;
        }
        if requested_output_tys.is_some_and(|tys| tys.len() != imp.output_tys.len())
            || requested_output_effs.is_some_and(|effs| effs.len() != imp.output_effs.len())
        {
            return false;
        }

        let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(Self::type_var_capacity_for_types(
            imp.output_tys
                .iter()
                .chain(requested_output_tys.unwrap_or_default()),
        ));
        // The request's effect variables are renamed apart from the dictionary's. Those its caller
        // quantifies are rigid: the dictionary must serve every value they may take.
        let mut requested_vars = FxHashSet::default();
        for ty in requested_output_tys.unwrap_or_default() {
            requested_vars.extend(ty.inner_effect_vars());
        }
        for eff in requested_output_effs.unwrap_or_default() {
            eff.fill_with_inner_effect_vars(&mut requested_vars);
        }
        let mut impl_vars = FxHashSet::default();
        for ty in &imp.output_tys {
            impl_vars.extend(ty.inner_effect_vars());
        }
        for eff in &imp.output_effs {
            eff.fill_with_inner_effect_vars(&mut impl_vars);
        }
        let used = requested_vars
            .iter()
            .chain(&impl_vars)
            .map(|var| var.name() + 1)
            .max()
            .unwrap_or(0);
        while ty_inf.effect_var_count() < used {
            ty_inf.fresh_effect_var();
        }
        let mut requested_vars = requested_vars.into_iter().collect::<Vec<_>>();
        requested_vars.sort_by_key(|var| var.name());
        let renaming: InstSubst = (
            FxHashMap::default(),
            requested_vars
                .into_iter()
                .map(|var| {
                    let renamed = if quantified_effect_vars.contains(&var) {
                        ty_inf.fresh_rigid_effect_var()
                    } else {
                        ty_inf.fresh_effect_var()
                    };
                    (var, EffType::single_variable(renamed))
                })
                .collect(),
        );
        let requested_output_tys = requested_output_tys.map(|tys| {
            tys.iter()
                .map(|ty| ty.map(&mut SimpleInstantiationMapper::new(&renaming)))
                .collect::<Vec<_>>()
        });
        let requested_output_effs = requested_output_effs.map(|effs| {
            effs.iter()
                .map(|eff| eff.instantiate(&renaming.1))
                .collect::<Vec<_>>()
        });
        if let Some(requested_output_tys) = &requested_output_tys {
            for (impl_ty, requested_ty) in imp.output_tys.iter().zip(requested_output_tys.iter()) {
                if ty_inf
                    .unify_same_type_with_sub_effects(*impl_ty, fn_span, *requested_ty, fn_span)
                    .is_err()
                {
                    return false;
                }
            }
        }
        if let Some(requested_output_effs) = &requested_output_effs {
            let polarities = self.output_effect_polarities(imp.trait_id);
            for ((impl_eff, requested_eff), polarity) in imp
                .output_effs
                .iter()
                .zip(requested_output_effs.iter())
                .zip(polarities)
            {
                if Self::match_trait_output_effect(
                    &mut ty_inf,
                    impl_eff,
                    requested_eff,
                    polarity,
                    fn_span,
                )
                .is_err()
                {
                    return false;
                }
            }
        }
        true
    }

    /// Try to discharge a nested blanket-impl trait constraint from assumptions
    /// already in scope for the outer query.
    fn match_assumption(
        ty_inf: &mut UnifiedTypeInference,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
    ) -> bool {
        assumptions.iter().any(|assumption| {
            let PubTypeConstraint::HaveTrait {
                trait_id: assumption_trait_id,
                input_tys: assumption_input_tys,
                output_tys: assumption_output_tys,
                ..
            } = assumption
            else {
                return false;
            };
            if *assumption_trait_id != trait_id
                || assumption_input_tys.len() != input_tys.len()
                || output_tys
                    .is_some_and(|output_tys| assumption_output_tys.len() != output_tys.len())
            {
                return false;
            }

            let substituted_assumption = ty_inf.substitute_in_constraint(assumption);
            let Some((_, ass_trait_id, ass_input_tys, ass_output_tys, ass_output_effs, _)) =
                substituted_assumption.as_have_trait()
            else {
                return false;
            };
            if !ass_input_tys.iter().all(|ty| ty.is_trait_input_resolved())
                || !ass_output_tys.iter().all(|ty| ty.is_trait_input_resolved())
            {
                return false;
            }
            if *ass_trait_id != trait_id
                || ass_input_tys.len() != input_tys.len()
                || output_tys.is_some_and(|output_tys| ass_output_tys.len() != output_tys.len())
            {
                return false;
            }
            ass_input_tys == input_tys
                && output_tys.is_none_or(|output_tys| ass_output_tys == output_tys)
                && output_effs.is_none_or(|output_effs| ass_output_effs == output_effs)
        })
    }

    fn normalize_blanket_remaining_constraints(
        ty_inf: &mut UnifiedTypeInference,
        constraints: impl IntoIterator<Item = (usize, PubTypeConstraint)>,
    ) -> Vec<(usize, PubTypeConstraint)> {
        constraints
            .into_iter()
            .map(|(index, constraint)| (index, ty_inf.substitute_in_constraint(&constraint)))
            .collect()
    }

    #[cfg(debug_assertions)]
    fn assert_blanket_impl_is_well_formed(
        imp_input_tys: &[Type],
        imp_output_tys: &[Type],
        imp_output_effs: &[EffType],
        imp_constraints: &[PubTypeConstraint],
        imp_ty_var_count: u32,
        imp_eff_var_count: u32,
        input_tys: &[Type],
    ) {
        assert_eq!(imp_input_tys.len(), input_tys.len());
        let mut ty_vars = FxHashSet::default();
        let mut mut_vars = FxHashSet::default();
        let mut eff_vars = FxHashSet::default();
        {
            let mut collector = AllVarsCollector {
                ty_vars: &mut ty_vars,
                mut_vars: &mut mut_vars,
                effect_vars: &mut eff_vars,
            };
            for ty in imp_input_tys.iter().chain(imp_output_tys) {
                ty.visit(&mut collector);
            }
        }
        {
            let mut collector = AllVarsCollector {
                ty_vars: &mut ty_vars,
                mut_vars: &mut mut_vars,
                effect_vars: &mut eff_vars,
            };
            for constraint in imp_constraints {
                constraint.visit(&mut collector);
            }
        }
        assert!(mut_vars.is_empty());
        assert_eq!(ty_vars.len(), imp_ty_var_count as usize);
        // Every effect variable of the impl, wherever it occurs, is one of its quantifiers.
        for eff in imp_output_effs {
            eff.fill_with_inner_effect_vars(&mut eff_vars);
        }
        assert_eq!(
            eff_vars,
            (0..imp_eff_var_count).map(EffectVar::new).collect()
        );
    }

    /// Match a blanket impl head plus its impl constraints against a requested
    /// trait application.
    ///
    /// This is the shared fixed-point engine used by both normal blanket impl
    /// solving and trait improvement. It instantiates the blanket-local type
    /// variables, unifies the impl head with the requested types, unifies known
    /// requested outputs when present, then iterates the impl constraints until
    /// no more progress is possible.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn match_blanket_impl<Q: TraitOutputQuery>(
        query: &mut Q,
        ty_inf: &mut UnifiedTypeInference,
        imp_input_tys: &[Type],
        imp_output_tys: &[Type],
        imp_output_effs: &[EffType],
        output_polarities: &[EffectPolarity],
        imp_ty_var_count: u32,
        imp_eff_var_count: u32,
        imp_constraints: &[PubTypeConstraint],
        input_tys: &[Type],
        output_tys: Option<&[Type]>,
        output_effs: Option<&[EffType]>,
        assumptions: ConstraintAssumptions<'_>,
        fn_span: Location,
        arena: &mut NodeArena,
        mode: BlanketConstraintMode,
    ) -> Result<BlanketImplMatch, InternalCompilationError> {
        // First instantiate the blanket-local type and effect variables with
        // fresh inference variables in the caller-provided unifier.
        let local_effects_start = ty_inf.effect_var_count();
        let inst_subst = (
            ty_inf.fresh_type_var_subst(imp_ty_var_count),
            ty_inf.fresh_effect_var_subst(imp_eff_var_count),
        );
        let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
        let imp_input_tys = instantiate_types(imp_input_tys, &mut mapper);
        let mut imp_output_tys = instantiate_types(imp_output_tys, &mut mapper);
        let mut imp_output_effs: Vec<_> = imp_output_effs
            .iter()
            .map(|eff| mapper.map_effect_type(eff))
            .collect();
        let mut runtime_requirements = Vec::new();
        let structural = matches!(
            mode,
            BlanketConstraintMode::Structural | BlanketConstraintMode::StructuralAllowUnknown
        );
        let scratch = !matches!(
            mode,
            BlanketConstraintMode::AllowUnknown | BlanketConstraintMode::StructuralAllowUnknown
        );

        // Then unify the instantiated blanket input and output types against
        // the requested trait application. Propagating output equalities before
        // solving nested constraints lets those constraints observe any output
        // information already available at the use site.
        for (imp_input_ty, input_ty) in imp_input_tys.iter().zip(input_tys.iter()) {
            if ty_inf
                .unify_same_type_with_sub_effects(*imp_input_ty, fn_span, *input_ty, fn_span)
                .is_err()
            {
                return Ok(BlanketImplMatch::No);
            }
        }
        if let Some(output_tys) = output_tys {
            for (imp_output_ty, output_ty) in imp_output_tys.iter().zip(output_tys.iter()) {
                if ty_inf
                    .unify_same_type_with_sub_effects(*imp_output_ty, fn_span, *output_ty, fn_span)
                    .is_err()
                {
                    return Ok(BlanketImplMatch::No);
                }
            }
        }
        if let Some(output_effs) = output_effs {
            for ((imp_output_eff, output_eff), polarity) in imp_output_effs
                .iter()
                .zip(output_effs.iter())
                .zip(output_polarities)
            {
                if Self::match_trait_output_effect(
                    ty_inf,
                    imp_output_eff,
                    output_eff,
                    *polarity,
                    fn_span,
                )
                .is_err()
                {
                    return Ok(BlanketImplMatch::No);
                }
            }
        }

        // Most candidates fail above, so only now pay for instantiating the constraints.
        let remaining = instantiate_types(imp_constraints, &mut mapper)
            .into_iter()
            .enumerate()
            .collect::<Vec<_>>();
        let mut remaining = Self::normalize_blanket_remaining_constraints(ty_inf, remaining);
        let mut queued_bounds = false;
        loop {
            let old_remaining = mem::take(&mut remaining);
            let mut still_remaining = Vec::new();

            for (constraint_index, constraint) in old_remaining.iter() {
                // Re-substitute the constraint on every pass because earlier
                // solved constraints may have refined the type variables it uses.
                let substituted_constraint = ty_inf.substitute_in_constraint(constraint);
                let Some((
                    _,
                    trait_id,
                    constraint_inputs,
                    constraint_outputs,
                    constraint_output_effs,
                    _span,
                )) = substituted_constraint.as_have_trait()
                else {
                    debug_assert!(substituted_constraint.as_have_trait().is_none());
                    let runtime_requirement = match &substituted_constraint {
                        PubTypeConstraint::ProjectionSubscriptIs {
                            requirement,
                            field,
                            subscript_ty,
                            ..
                        } => Some(DictionaryReq::new_projection_subscript(
                            *requirement,
                            *field,
                            subscript_ty.clone(),
                        )),
                        PubTypeConstraint::TypeHasVariant {
                            variant_ty,
                            tag,
                            payload_ty,
                            ..
                        } => Some(DictionaryReq::new_variant_payload_indirection(
                            *variant_ty,
                            *tag,
                            *payload_ty,
                        )),
                        PubTypeConstraint::VariantPayloadLayout { .. } => {
                            // This is an inference-only trigger. The payload's ordinary `Value`
                            // leaves are separate constraints and therefore separate runtime
                            // requirements; the case-qualified trigger has no ABI slot.
                            continue;
                        }
                        _ => None,
                    };
                    let bounds = ty_inf.bound_count();
                    let unresolved = query.unify_non_trait_constraint_query(
                        ty_inf,
                        &substituted_constraint,
                        assumptions,
                        arena,
                    )?;
                    queued_bounds |= ty_inf.bound_count() > bounds;
                    if let Some(unresolved) = unresolved {
                        still_remaining.push((*constraint_index, unresolved));
                    } else if let Some(req) = runtime_requirement {
                        runtime_requirements.push(ResolvedRuntimeRequirement {
                            index: *constraint_index,
                            req,
                        });
                    }
                    continue;
                };
                let trait_id = *trait_id;
                let constraint_inputs = constraint_inputs.clone();
                let constraint_outputs = constraint_outputs.clone();
                let constraint_output_effs = constraint_output_effs.clone();
                if Self::match_assumption(
                    ty_inf,
                    trait_id,
                    &constraint_inputs,
                    Some(&constraint_outputs),
                    Some(&constraint_output_effs),
                    assumptions,
                ) {
                    continue;
                }
                if !constraint_inputs
                    .iter()
                    .all(|ty| ty.is_trait_input_resolved())
                {
                    if Self::input_tys_can_drive_improvement(&constraint_inputs) {
                        match query.improve_trait_application_query(
                            ty_inf,
                            trait_id,
                            &constraint_inputs,
                            Some(&constraint_outputs),
                            Some(&constraint_output_effs),
                            assumptions,
                            fn_span,
                            arena,
                        )? {
                            TraitImprovementMatch::No => return Ok(BlanketImplMatch::No),
                            TraitImprovementMatch::Unknown => {}
                            TraitImprovementMatch::Yes => {}
                        }
                    }
                    still_remaining.push((*constraint_index, substituted_constraint));
                    continue;
                }
                let (solved_outputs, solved_output_effs) = if query
                    .is_compiler_provided_no_output_trait_query(
                        trait_id,
                        &constraint_inputs,
                        &constraint_outputs,
                        &constraint_output_effs,
                    ) {
                    (Vec::new(), Vec::new())
                } else {
                    let solved = if structural {
                        query
                            .solve_outputs_by_structure_query(trait_id, &constraint_inputs, fn_span)
                            .map(|output_tys| (output_tys, Vec::new()))
                    } else {
                        query.solve_outputs_query(
                            trait_id,
                            &constraint_inputs,
                            Some(&constraint_output_effs),
                            fn_span,
                            arena,
                        )
                    };
                    match solved {
                        Ok(outputs) => outputs,
                        Err(_)
                            if matches!(mode, BlanketConstraintMode::DeferConcreteObligations) =>
                        {
                            still_remaining.push((*constraint_index, substituted_constraint));
                            continue;
                        }
                        Err(_) => return Ok(BlanketImplMatch::No),
                    }
                };
                let solved_outputs = if structural {
                    instantiate_types(&solved_outputs, &mut EffectErasingMapper)
                } else {
                    solved_outputs
                };
                for (solved_output, constraint_output) in
                    solved_outputs.iter().zip(constraint_outputs.iter())
                {
                    if ty_inf
                        .unify_same_type_with_sub_effects(
                            *solved_output,
                            fn_span,
                            *constraint_output,
                            fn_span,
                        )
                        .is_err()
                    {
                        return Ok(BlanketImplMatch::No);
                    }
                }
                // The nested implementation's outputs relate to the constraint's by their
                // polarity, as at the top level.
                if structural {
                    continue;
                }
                let polarities = query.output_effect_polarities_query(trait_id);
                for ((solved_output_eff, constraint_output_eff), polarity) in solved_output_effs
                    .iter()
                    .zip(constraint_output_effs.iter())
                    .zip(polarities)
                {
                    if Self::match_trait_output_effect(
                        ty_inf,
                        solved_output_eff,
                        constraint_output_eff,
                        polarity,
                        fn_span,
                    )
                    .is_err()
                    {
                        return Ok(BlanketImplMatch::No);
                    }
                }
                runtime_requirements.push(ResolvedRuntimeRequirement {
                    index: *constraint_index,
                    req: DictionaryReq::new_trait_impl(
                        trait_id,
                        constraint_inputs,
                        constraint_outputs,
                        constraint_output_effs,
                    ),
                });
            }

            let still_remaining =
                Self::normalize_blanket_remaining_constraints(ty_inf, still_remaining);
            let settled = still_remaining.is_empty() || still_remaining == old_remaining;

            // The answer to a non-trait constraint may bound a type from below, as the type
            // of a field does the type that the implementation reads it at. Once the
            // constraints tell nothing more, such a type is the least one, as an effect is: a
            // scratch match has no later inference to choose it. The caller's own inference,
            // matching for improvement, chooses it itself. A type that a constraint still
            // pending here may bound waits for it, so the constraints are tried again after
            // each choice.
            if settled && queued_bounds && scratch {
                let pending: Vec<_> = still_remaining
                    .iter()
                    .map(|(_, constraint)| constraint.clone())
                    .collect();
                match ty_inf.select_least_bounded_types(&pending) {
                    Ok(true) => {
                        remaining = still_remaining;
                        continue;
                    }
                    Ok(false) => {}
                    Err(_) => return Ok(BlanketImplMatch::No),
                }
            }

            // Fixed point reached: either all nested constraints are solved or
            // we have to stop according to the caller's mode.
            if still_remaining.is_empty() {
                break;
            }

            if still_remaining == old_remaining {
                match mode {
                    BlanketConstraintMode::RequireAllResolved
                    | BlanketConstraintMode::Structural => {
                        return Ok(BlanketImplMatch::No);
                    }
                    BlanketConstraintMode::AllowUnknown
                    | BlanketConstraintMode::StructuralAllowUnknown => {
                        return Ok(BlanketImplMatch::Unknown);
                    }
                    BlanketConstraintMode::DeferConcreteObligations => {
                        for (constraint_index, constraint) in still_remaining {
                            let substituted_constraint =
                                ty_inf.substitute_in_constraint(&constraint);
                            let Some((
                                _,
                                trait_id,
                                constraint_inputs,
                                constraint_outputs,
                                constraint_output_effs,
                                _span,
                            )) = substituted_constraint.as_have_trait()
                            else {
                                return Ok(BlanketImplMatch::No);
                            };
                            let trait_id = *trait_id;
                            let constraint_inputs = constraint_inputs.clone();
                            let constraint_outputs = constraint_outputs.clone();
                            let constraint_output_effs = constraint_output_effs.clone();
                            if !constraint_inputs
                                .iter()
                                .all(|ty| ty.is_trait_input_resolved())
                            {
                                return Ok(BlanketImplMatch::No);
                            }
                            runtime_requirements.push(ResolvedRuntimeRequirement {
                                index: constraint_index,
                                req: DictionaryReq::new_trait_impl(
                                    trait_id,
                                    constraint_inputs,
                                    constraint_outputs,
                                    constraint_output_effs,
                                ),
                            });
                        }
                        break;
                    }
                }
            }

            remaining = still_remaining;
        }

        // Finally, unify the instantiated blanket outputs with the requested
        // outputs if the caller supplied them, then return the resolved nested
        // trait constraints in source order.
        if let Some(output_tys) = output_tys {
            for (imp_output_ty, output_ty) in imp_output_tys.iter().zip(output_tys.iter()) {
                if ty_inf
                    .unify_same_type_with_sub_effects(*imp_output_ty, fn_span, *output_ty, fn_span)
                    .is_err()
                {
                    return Ok(BlanketImplMatch::No);
                }
            }
        }
        if let Some(output_effs) = output_effs {
            for ((imp_output_eff, output_eff), polarity) in imp_output_effs
                .iter()
                .zip(output_effs.iter())
                .zip(output_polarities)
            {
                if Self::match_trait_output_effect(
                    ty_inf,
                    imp_output_eff,
                    output_eff,
                    *polarity,
                    fn_span,
                )
                .is_err()
                {
                    return Ok(BlanketImplMatch::No);
                }
            }
        }

        // In a scratch match, the implementation's own effect variables take their least
        // solution; the caller's own inference, matching for improvement, may still bound them.
        if scratch && ty_inf.minimize_effects_from(local_effects_start).is_err() {
            return Ok(BlanketImplMatch::No);
        }
        // The match reads its results through the published effects, but `ty_inf` may be the
        // caller's own inference, which goes on afterwards.
        let effects_finalized = ty_inf.effects_finalized();
        if ty_inf.finalize_effects().is_err() {
            return Ok(BlanketImplMatch::No);
        }
        for requirement in &mut runtime_requirements {
            match &mut requirement.req {
                DictionaryReq::ProjectionSubscript { subscript_ty, .. } => {
                    ty_inf.substitute_in_subscript_type_in_place(subscript_ty);
                }
                DictionaryReq::VariantPayloadIndirection {
                    variant_ty,
                    payload_ty,
                    ..
                } => {
                    *variant_ty = ty_inf.substitute_in_type(*variant_ty);
                    *payload_ty = ty_inf.substitute_in_type(*payload_ty);
                }
                DictionaryReq::TraitImpl {
                    input_tys,
                    output_tys,
                    output_effs,
                    ..
                } => {
                    ty_inf.substitute_in_types_in_place(input_tys);
                    ty_inf.substitute_in_types_in_place(output_tys);
                    ty_inf.substitute_in_effect_types_in_place(output_effs);
                }
            }
        }
        runtime_requirements.sort_by_key(|requirement| requirement.index);
        ty_inf.substitute_in_types_in_place(&mut imp_output_tys);
        ty_inf.substitute_in_effect_types_in_place(&mut imp_output_effs);
        let mut instantiation = inst_subst;
        for ty in instantiation.0.values_mut() {
            *ty = ty_inf.substitute_in_type(*ty);
        }
        for eff in instantiation.1.values_mut() {
            *eff = ty_inf.substitute_in_effect_type(eff);
        }
        ty_inf.restore_effects_finalized(effects_finalized);
        Ok(BlanketImplMatch::Yes {
            output_tys: imp_output_tys,
            output_effs: imp_output_effs,
            runtime_requirements,
            instantiation,
        })
    }

    pub(super) fn runtime_requirements_from_resolved(
        &self,
        resolved_requirements: &[ResolvedRuntimeRequirement],
        source_constraints: &[PubTypeConstraint],
    ) -> Vec<DictionaryReq> {
        let value_trait_id = self.std_trait_id(VALUE_TRAIT_NAME);
        let mut source_slots = Vec::new();
        let mut requirements = Vec::new();
        for resolved in resolved_requirements {
            let source_constraint = &source_constraints[resolved.index];
            let source_requirement = match source_constraint {
                PubTypeConstraint::HaveTrait {
                    trait_id,
                    input_tys,
                    output_tys,
                    ..
                } if !self.trait_def(*trait_id).has_runtime_dictionary_entries()
                    || is_value_trait_for_function_type(
                        *trait_id,
                        self.trait_def(*trait_id),
                        input_tys,
                        output_tys,
                    )
                    || is_function_surface_only_value_trait_application(
                        *trait_id,
                        self.trait_def(*trait_id),
                        input_tys,
                        output_tys,
                    ) =>
                {
                    None
                }
                _ => source_constraint.dictionary_requirement_key(value_trait_id),
            };
            let Some(source_requirement) = source_requirement else {
                continue;
            };

            // Slot sharing is determined by the generic callee's ABI. Two different source slots
            // may resolve to equal requirements at this instantiation; in that case the same
            // dictionary value is passed twice, once in each original position.
            if source_slots.contains(&source_requirement) {
                continue;
            }

            let requirement = match &resolved.req {
                DictionaryReq::ProjectionSubscript { .. } => Some(resolved.req.clone()),
                DictionaryReq::VariantPayloadIndirection { .. } => Some(resolved.req.clone()),
                DictionaryReq::TraitImpl {
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                } => {
                    let trait_def = self.trait_def(*trait_id);
                    if !trait_def.has_runtime_dictionary_entries() {
                        None
                    } else {
                        Some(DictionaryReq::new_trait_impl(
                            *trait_id,
                            input_tys.clone(),
                            output_tys.clone(),
                            output_effs.clone(),
                        ))
                    }
                }
            };
            if let Some(requirement) = requirement {
                source_slots.push(source_requirement);
                requirements.push(requirement);
            }
        }
        requirements
    }

    pub(super) fn close_defaulted_requirement_effect_rows(
        requirements: &mut [DictionaryReq],
        variables: &FxHashSet<EffectVar>,
    ) {
        if variables.is_empty() {
            return;
        }
        let mut mapper = DefaultedEffectRowsMapper { variables };
        for requirement in requirements {
            requirement.instantiate_in_place(&mut mapper);
        }
    }

    pub(super) fn validate_runtime_requirements(
        &mut self,
        resolved_requirements: &[ResolvedRuntimeRequirement],
        fn_span: Location,
        arena: &mut NodeArena,
        validate_outputs: bool,
    ) -> Result<bool, InternalCompilationError> {
        for resolved_requirement in resolved_requirements {
            let DictionaryReq::TraitImpl {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
            } = &resolved_requirement.req
            else {
                continue;
            };
            // Marker traits have no runtime dictionary entries.
            if !self.trait_def(*trait_id).has_runtime_dictionary_entries() {
                continue;
            }
            if self.is_compiler_provided_no_output_trait_query(
                *trait_id,
                input_tys,
                output_tys,
                output_effs,
            ) {
                self.compiler_provided_value_dictionary_node_kind(
                    arena, *trait_id, input_tys, fn_span,
                )?;
                continue;
            }
            let dict_id = match self.solve_impl(*trait_id, input_tys, fn_span, arena) {
                Ok(functions) => functions,
                Err(err) => {
                    log::trace!(
                        "Blanket impl constraint failed while solving {} for {:?}: {:?}",
                        self.trait_def(*trait_id).name,
                        input_tys,
                        err
                    );
                    return Ok(false);
                }
            };
            let dict_impl_data = self.get_impl_data_by_id(dict_id);
            // By structure, only the types of the outputs count, without their effects.
            if self.selecting_by_structure {
                if validate_outputs
                    && instantiate_types(&dict_impl_data.output_tys, &mut EffectErasingMapper)
                        != *output_tys
                {
                    return Ok(false);
                }
                continue;
            }
            // Output effects relate by their polarity, as when matching.
            if validate_outputs
                && (dict_impl_data.output_tys != *output_tys
                    || !dict_impl_data
                        .output_effs
                        .iter()
                        .zip(output_effs.iter())
                        .zip(self.output_effect_polarities(*trait_id))
                        .all(|((solved_eff, constraint_eff), polarity)| {
                            output_effect_fits(solved_eff, constraint_eff, polarity)
                        }))
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// The output effects of `imp` that do not relate to the requested ones by polarity, each with
    /// its name, its declared row and the requested one.
    pub(super) fn output_effect_mismatches(
        &self,
        imp: &TraitImpl,
        requested_output_effs: &[EffType],
        quantified_effect_vars: &FxHashSet<EffectVar>,
        fn_span: Location,
    ) -> Vec<(Ustr, EffType, EffType)> {
        let names = &self.trait_def(imp.trait_id).output_effect_names;
        (0..imp.output_effs.len().min(requested_output_effs.len()))
            .filter_map(|index| {
                // Request this output alone; the others take the implementation's own rows.
                let mut requested = imp.output_effs.clone();
                requested[index] = requested_output_effs[index].clone();
                (!self.impl_matches_requested_outputs(
                    imp,
                    None,
                    Some(&requested),
                    quantified_effect_vars,
                    fn_span,
                ))
                .then(|| {
                    (
                        names[index],
                        imp.output_effs[index].clone(),
                        requested_output_effs[index].clone(),
                    )
                })
            })
            .collect()
    }

    /// Solve a full trait application.
    ///
    /// Impl identity is selected by trait id and resolved input types, but
    /// associated output types and effects are application parameters. They are
    /// matched against the selected impl for this application and must not be
    /// treated as canonical values of the input-keyed impl cache.
    /// Resolve an application by the blanket implementation the solver selects for it,
    /// symbolically: return that implementation's outputs and constraints in terms of the
    /// application's own variables, without materializing a dictionary. `None` if no blanket
    /// implementation applies.
    /// The runtime requirements of a matched blanket impl failed. If they hold without any effect,
    /// the impl applies and only its effects are wrong; other failures, such as a cycle, stand.
    pub(super) fn reject_if_requirements_fail_on_effects(
        &mut self,
        requirements: &[ResolvedRuntimeRequirement],
        input_tys: &[Type],
        fn_span: Location,
    ) -> Result<(), InternalCompilationError> {
        if self.selecting_by_structure {
            return Ok(());
        }
        let erased = requirements
            .iter()
            .map(|requirement| ResolvedRuntimeRequirement {
                index: requirement.index,
                req: match &requirement.req {
                    DictionaryReq::TraitImpl {
                        trait_id,
                        input_tys,
                        output_tys,
                        output_effs,
                    } => DictionaryReq::new_trait_impl(
                        *trait_id,
                        instantiate_types(input_tys, &mut EffectErasingMapper),
                        instantiate_types(output_tys, &mut EffectErasingMapper),
                        vec![EffType::empty(); output_effs.len()],
                    ),
                    other => other.clone(),
                },
            })
            .collect::<Vec<_>>();
        let snapshot = self.snapshot_derived_impl_state();
        let mut arena = NodeArena::default();
        self.selecting_by_structure = true;
        let holds = self.validate_runtime_requirements(&erased, fn_span, &mut arena, true);
        self.selecting_by_structure = false;
        self.rollback_derived_impl_state(snapshot);
        if holds? {
            return Err(internal_compilation_error!(TraitImplEffectsMismatch {
                input_ty: input_tys[0],
                fn_span,
            }));
        }
        Ok(())
    }

    /// A blanket impl did not match. If it applies by structure, ignoring all effects, it is
    /// nevertheless the selected impl, since effects never select one: its effects are then wrong,
    /// and no other impl or derivation may serve the application.
    fn reject_if_applies_by_structure(
        &mut self,
        (sub_key, imp_output_tys): (&BlanketTraitImplSubKey, &[Type]),
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        fn_span: Location,
    ) -> Result<(), InternalCompilationError> {
        // Already checking by structure: this candidate's answer is the one being sought.
        if self.selecting_by_structure {
            return Ok(());
        }
        let erased_input_tys = instantiate_types(input_tys, &mut EffectErasingMapper);
        let erased_output_tys =
            requested_output_tys.map(|tys| instantiate_types(tys, &mut EffectErasingMapper));
        let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(Self::type_var_capacity_for_types(
            erased_input_tys
                .iter()
                .chain(erased_output_tys.as_deref().unwrap_or_default()),
        ));
        let snapshot = self.snapshot_derived_impl_state();
        let mut arena = NodeArena::default();
        self.selecting_by_structure = true;
        let matched = Self::match_blanket_impl(
            self,
            &mut ty_inf,
            &instantiate_types(&sub_key.input_tys, &mut EffectErasingMapper),
            &instantiate_types(imp_output_tys, &mut EffectErasingMapper),
            &[],
            &[],
            sub_key.ty_var_count,
            0,
            &instantiate_types(&sub_key.constraints, &mut EffectErasingMapper),
            &erased_input_tys,
            erased_output_tys.as_deref(),
            None,
            ConstraintAssumptions::all(&[]),
            fn_span,
            &mut arena,
            BlanketConstraintMode::Structural,
        );
        self.selecting_by_structure = false;
        self.rollback_derived_impl_state(snapshot);
        if matches!(matched?, BlanketImplMatch::Yes { .. }) {
            return Err(internal_compilation_error!(TraitImplEffectsMismatch {
                input_ty: input_tys[0],
                fn_span,
            }));
        }
        Ok(())
    }

    /// Walk the visible blanket implementations in order and hand each one whose inputs match the
    /// application to `accept`, which validates it and returns its result, or `None` to go on to
    /// the next candidate. A candidate that does not match but applies by structure is rejected,
    /// as effects cannot select another implementation. Published requirements are solved in
    /// the caller's scope; private evidence is constructed by the provider's method bodies.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn select_blanket_candidate<R>(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        requested_output_tys: Option<&[Type]>,
        requested_output_effs: Option<&[EffType]>,
        mode: BlanketConstraintMode,
        search: &mut CandidateSearch,
        fn_span: Location,
        arena: &mut NodeArena,
        mut accept: impl FnMut(
            &mut Self,
            BlanketCandidate<'_>,
            &mut NodeArena,
        ) -> Result<Option<R>, InternalCompilationError>,
    ) -> Result<Option<R>, InternalCompilationError> {
        let output_polarities = self.output_effect_polarities(trait_id);
        // Share the local table to avoid borrowing issues: adding a blanket implementation
        // during the search copies it and leaves this view unchanged.
        let local_blankets = self.impls.blanket_key_to_id.clone();
        let blankets = visible_blanket_impls(
            &local_blankets,
            self.others,
            self.current_type_items.environment,
            trait_id,
        );
        let fully_determined = input_tys.iter().all(Type::is_constant);
        // By structure, the candidate is seen without effects, as the application is.
        let by_structure = matches!(mode, BlanketConstraintMode::Structural);
        for (module, blanket_impls) in blankets {
            for (sub_key, impl_id) in blanket_impls.iter() {
                if !input_heads_may_match(&sub_key.input_tys, input_tys) {
                    continue;
                }
                search.next_candidate();
                let (public, declared_output_tys, declared_output_effs) = match module {
                    Some(module_id) => {
                        let imp = &self
                            .others
                            .get(module_id)
                            .unwrap()
                            .module()
                            .unwrap()
                            .impls
                            .data[impl_id.as_index()];
                        (
                            self.can_use_other_impl(module_id, imp),
                            imp.output_tys.clone(),
                            imp.output_effs.clone(),
                        )
                    }
                    None => {
                        let imp = &self.impls.data[impl_id.as_index()];
                        (true, imp.output_tys.clone(), imp.output_effs.clone())
                    }
                };
                if !public {
                    continue;
                }

                #[cfg(debug_assertions)]
                Self::assert_blanket_impl_is_well_formed(
                    &sub_key.input_tys,
                    &declared_output_tys,
                    &declared_output_effs,
                    &sub_key.constraints,
                    sub_key.ty_var_count,
                    sub_key.eff_var_count,
                    input_tys,
                );

                // Keep the caller's visibility when solving the published requirements.
                let accepted = (|| {
                    // Match the blanket implementation and resolve its constraints to a fixed point.
                    let mut ty_inf =
                        UnifiedTypeInference::new_with_ty_vars(Self::type_var_capacity_for_types(
                            input_tys
                                .iter()
                                .chain(requested_output_tys.unwrap_or_default()),
                        ));
                    // Reserve the application's effect variables, so that the implementation's
                    // fresh effect variables cannot alias them.
                    for _ in 0..Self::effect_var_capacity(
                        input_tys
                            .iter()
                            .chain(requested_output_tys.unwrap_or_default()),
                        requested_output_effs.unwrap_or_default(),
                    ) {
                        ty_inf.fresh_effect_var();
                    }
                    let erased = by_structure.then(|| {
                        (
                            instantiate_types(&sub_key.input_tys, &mut EffectErasingMapper),
                            instantiate_types(&declared_output_tys, &mut EffectErasingMapper),
                            instantiate_types(&sub_key.constraints, &mut EffectErasingMapper),
                            vec![EffType::empty(); declared_output_effs.len()],
                        )
                    });
                    let (
                        matched_input_tys,
                        matched_output_tys,
                        matched_constraints,
                        matched_output_effs,
                    ) = match &erased {
                        Some((inputs, outputs, constraints, effs)) => {
                            (&inputs[..], &outputs[..], &constraints[..], &effs[..])
                        }
                        None => (
                            &sub_key.input_tys[..],
                            &declared_output_tys[..],
                            &sub_key.constraints[..],
                            &declared_output_effs[..],
                        ),
                    };
                    let blanket_match = Self::match_blanket_impl(
                        self,
                        &mut ty_inf,
                        matched_input_tys,
                        matched_output_tys,
                        matched_output_effs,
                        &output_polarities,
                        sub_key.ty_var_count,
                        sub_key.eff_var_count,
                        matched_constraints,
                        input_tys,
                        requested_output_tys,
                        requested_output_effs,
                        ConstraintAssumptions::all(&[]),
                        fn_span,
                        arena,
                        mode,
                    )?;
                    let BlanketImplMatch::Yes {
                        output_tys,
                        output_effs,
                        runtime_requirements,
                        instantiation,
                    } = blanket_match
                    else {
                        self.reject_if_applies_by_structure(
                            (sub_key, &declared_output_tys),
                            input_tys,
                            requested_output_tys,
                            fn_span,
                        )?;
                        return Ok(None);
                    };
                    let candidate = BlanketCandidate {
                        module,
                        impl_id: *impl_id,
                        sub_key,
                        declared_output_tys,
                        declared_output_effs,
                        output_tys,
                        output_effs,
                        runtime_requirements,
                        instantiation,
                    };
                    accept(self, candidate, arena)
                })();
                if let Some(result) = accepted? {
                    if fully_determined {
                        search.succeed();
                    }
                    return Ok(Some(result));
                }
            }
        }
        Ok(None)
    }
}
