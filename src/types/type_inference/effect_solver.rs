// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{borrow::Borrow, mem};

use ena::unify::{InPlace, InPlaceUnificationTable, Snapshot};
use ustr::Ustr;

use super::constraints::EffectConstraint;
use crate::{
    FxHashMap, FxHashSet,
    compiler::error::InternalCompilationError,
    internal_compilation_error,
    module::TraitId,
    parser::location::Location,
    types::{
        effects::{EffType, Effect, EffectVar, EffectVarKey},
        r#type::{FnType, SubscriptMemberType, SubscriptType, Type, TypeKind},
    },
};

/// A pending lower-bound dependency on an effect variable.
///
/// This is currently the representation used for constraints of the form
/// `source <= target_var`: the required source effects are pushed into the
/// target variable after ordinary type and trait solving has had a chance to
/// resolve more of the target's effect expression.
#[derive(Debug, Clone)]
pub(super) struct PendingEffectDependency {
    pub(super) source: EffType,
    pub(super) source_span: Location,
    pub(super) target: EffectVarKey,
    pub(super) target_span: Location,
    pub(super) origin: EffectConstraintOrigin,
}

/// Diagnostic origin for internal effect dependency constraints.
#[derive(Debug, Clone)]
pub(crate) enum EffectConstraintOrigin {
    Inference,
    TraitMethodImpl {
        trait_id: TraitId,
        method_name: Ustr,
        impl_span: Location,
    },
}

/// A deferred effect inclusion `lower <= upper`.
///
/// Effect equality is represented as two inclusions. Inclusions that have a
/// unique local interpretation are solved eagerly; ambiguous composite
/// inclusions are kept, as stated, until more type/trait solving has
/// substituted effect variables. Any residual inclusion is materialized conservatively into the
/// involved variables before generalization, preserving sound upper bounds at
/// the cost of possible imprecision.
#[derive(Debug, Clone)]
struct EffectInclusion {
    lower: EffType,
    lower_span: Location,
    upper: EffType,
    upper_span: Location,
    origin: EffectConstraintOrigin,
}

pub(crate) struct EffectSolverSnapshot {
    table: Snapshot<InPlace<EffectVarKey>>,
    pending_dependencies: Vec<PendingEffectDependency>,
    deferred_inclusions: Vec<EffectInclusion>,
    closed_bounds: Vec<EffectInclusion>,
}

/// Solver state for inferred effect variables and effect relations.
///
/// Effect unification is modeled as inclusion constraints. Simple inclusions
/// are solved eagerly in the union table, while ambiguous composite relations
/// are deferred until type and trait solving have substituted more variables.
/// Before generalization, any residual deferred relation is conservatively
/// materialized into the variables it constrains.
///
/// The table only records what a variable contains, so it can enforce an upper
/// bound only by closing the variable. A variable that is already open when a
/// closed bound arrives stays open, so each inclusion into a closed row is also
/// kept in `closed_bounds` and checked again whenever pending dependencies are
/// expanded. Recording upper bounds in the table itself would remove this
/// limitation.
#[derive(Default, Debug)]
pub(crate) struct EffectSolver {
    table: InPlaceUnificationTable<EffectVarKey>,
    constraints: Vec<EffectConstraint>,
    pending_dependencies: Vec<PendingEffectDependency>,
    deferred_inclusions: Vec<EffectInclusion>,
    closed_bounds: Vec<EffectInclusion>,
}

impl EffectSolver {
    pub(crate) fn fresh_var(&mut self) -> EffectVar {
        self.table.new_key(None)
    }

    fn ensure_var(&mut self, var: EffectVar) {
        while self.table.len() <= var.name() as usize {
            self.table.new_key(None);
        }
    }

    fn ensure_effect_vars(&mut self, eff: &EffType) {
        for var in eff.inner_vars() {
            self.ensure_var(var);
        }
    }

    pub(crate) fn fresh_var_ty(&mut self) -> EffType {
        EffType::single_variable(self.fresh_var())
    }

    pub(crate) fn snapshot(&mut self) -> EffectSolverSnapshot {
        EffectSolverSnapshot {
            table: self.table.snapshot(),
            pending_dependencies: self.pending_dependencies.clone(),
            deferred_inclusions: self.deferred_inclusions.clone(),
            closed_bounds: self.closed_bounds.clone(),
        }
    }

    pub(crate) fn rollback_to(&mut self, snapshot: EffectSolverSnapshot) {
        self.table.rollback_to(snapshot.table);
        self.pending_dependencies = snapshot.pending_dependencies;
        self.deferred_inclusions = snapshot.deferred_inclusions;
        self.closed_bounds = snapshot.closed_bounds;
    }

    pub(super) fn add_same_constraint(
        &mut self,
        current: &EffType,
        current_span: Location,
        expected: &EffType,
        expected_span: Location,
    ) {
        if current == expected {
            return;
        }
        self.constraints.push(EffectConstraint::SameEffect {
            current: current.clone(),
            current_span,
            expected: expected.clone(),
            expected_span,
        });
    }

    pub(super) fn drain_constraints(&mut self) -> Vec<EffectConstraint> {
        mem::take(&mut self.constraints)
    }

    pub(super) fn make_dependent_effect<T: Borrow<EffType> + Clone>(
        &mut self,
        deps: impl AsRef<[T]>,
    ) -> EffType {
        let deps = deps.as_ref();

        if deps.is_empty() {
            return EffType::empty();
        } else if deps.len() == 1 {
            return deps[0].borrow().clone();
        }

        let mut effects = deps[0].borrow().clone();
        for effect in &deps[1..] {
            effects.extend(effect.borrow());
        }

        if !effects.has_variables() || effects.to_single_variable().is_some() {
            return effects;
        }

        let effect_var = self.table.new_key(Some(effects));
        EffType::single_variable(effect_var)
    }

    /// Make the two effects equal and fuse their dependencies.
    pub(super) fn unify_effects(&mut self, eff1: &EffType, eff2: &EffType) -> EffType {
        self.ensure_effect_vars(eff1);
        self.ensure_effect_vars(eff2);
        let var1 = eff1.to_single_variable();
        let var2 = eff2.to_single_variable();
        match (var1, var2) {
            (None, None) => eff1.union(eff2),
            (None, Some(var)) => {
                self.table.union_value(var, Some(eff1.clone()));
                eff1.clone()
            }
            (Some(var), None) => {
                self.table.union_value(var, Some(eff2.clone()));
                eff2.clone()
            }
            (Some(var1), Some(var2)) => {
                self.table.union(var1, var2);
                eff1.clone()
            }
        }
    }

    pub(super) fn unify_fn_arg_effects(&mut self, fn_type: &FnType) {
        for arg in &fn_type.args {
            if let Some(fn_arg) = arg.ty.data().as_function() {
                let mut first_var = None;
                fn_arg.effects.iter().for_each(|eff| {
                    if let Some(var) = eff.as_variable() {
                        self.ensure_var(*var);
                        if let Some(first_var) = first_var {
                            self.table.union(first_var, *var);
                        } else {
                            first_var = Some(*var);
                        }
                    }
                });
            }
        }
    }

    pub(super) fn effect_unioned(&mut self, var: EffectVar) -> Option<EffectVar> {
        self.ensure_var(var);
        let root = self.table.find(var);
        if root != var { Some(root) } else { None }
    }

    /// Generalize concrete effects in first-class callable-like types to effect variables.
    ///
    /// This is needed when unifying a type variable with a function or subscript
    /// type, to preserve effect polymorphism.
    pub(super) fn generalize_effectful_callable_type(&mut self, ty: Type) -> Type {
        use TypeKind::*;
        let ty_data = ty.data();
        match &*ty_data {
            Function(fn_ty) => {
                let fn_ty = fn_ty.clone();
                drop(ty_data);
                if let Some(effects) = self.generalize_effect_type(&fn_ty.effects) {
                    let new_fn_ty = FnType::new(fn_ty.args.clone(), fn_ty.ret, effects);
                    Type::function_type(new_fn_ty)
                } else {
                    ty
                }
            }
            Subscript(subscript) => {
                let subscript = subscript.clone();
                drop(ty_data);
                let (ref_member, ref_changed) =
                    self.generalize_subscript_member(subscript.ref_member.as_ref());
                let (mut_member, mut_changed) =
                    self.generalize_subscript_member(subscript.mut_member.as_ref());
                if ref_changed || mut_changed {
                    Type::subscript_type(SubscriptType::new(
                        subscript.args.clone(),
                        subscript.ret,
                        ref_member,
                        mut_member,
                    ))
                } else {
                    ty
                }
            }
            _ => {
                drop(ty_data);
                ty
            }
        }
    }

    fn generalize_subscript_member(
        &mut self,
        member: Option<&SubscriptMemberType>,
    ) -> (Option<SubscriptMemberType>, bool) {
        let Some(member) = member else {
            return (None, false);
        };
        match self.generalize_effect_type(&member.effects) {
            Some(effects) => (
                Some(SubscriptMemberType::new(effects, member.result_convention)),
                true,
            ),
            None => (Some(member.clone()), false),
        }
    }

    fn generalize_effect_type(&mut self, effects: &EffType) -> Option<EffType> {
        let has_primitive_effects = effects.iter().any(|e| e.is_primitive());
        if !has_primitive_effects {
            return None;
        }
        let fresh_eff_var = self.table.new_key(None);
        for eff in effects.iter() {
            if eff.is_primitive() {
                self.pending_dependencies.push(PendingEffectDependency {
                    source: EffType::single(eff),
                    source_span: Location::new_synthesized(),
                    target: fresh_eff_var,
                    target_span: Location::new_synthesized(),
                    origin: EffectConstraintOrigin::Inference,
                });
            } else if let Some(var) = eff.as_variable() {
                self.table.union(fresh_eff_var, *var);
            }
        }
        Some(EffType::single_variable(fresh_eff_var))
    }

    /// Require the selected implementation's output effect to fit in the
    /// trait output effect requested by the call site.
    pub(super) fn resolve_trait_output_effect(
        &mut self,
        constraint_eff: &EffType,
        solved_eff: &EffType,
        span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.add_effect_inclusion(
            solved_eff.clone(),
            span,
            constraint_eff.clone(),
            span,
            EffectConstraintOrigin::Inference,
        )
    }

    /// Make current and target the same effect type.
    pub(crate) fn unify_same_effect(
        &mut self,
        current: EffType,
        current_span: Location,
        target: EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.ensure_effect_vars(&current);
        self.ensure_effect_vars(&target);
        match (current.to_single_variable(), target.to_single_variable()) {
            (Some(current_var), Some(target_var)) => {
                self.table
                    .unify_var_var(current_var, target_var)
                    .map_err(|_| {
                        invalid_effect_dependency(
                            current,
                            current_span,
                            target,
                            target_span,
                            EffectConstraintOrigin::Inference,
                        )
                    })?;
                return Ok(());
            }
            (Some(current_var), None) => {
                self.table.union_value(current_var, Some(target));
                return Ok(());
            }
            (None, Some(target_var)) => {
                self.table.union_value(target_var, Some(current));
                return Ok(());
            }
            (None, None) => {}
        }
        self.add_effect_inclusion(
            current.clone(),
            current_span,
            target.clone(),
            target_span,
            EffectConstraintOrigin::Inference,
        )?;
        self.add_effect_inclusion(
            target,
            target_span,
            current,
            current_span,
            EffectConstraintOrigin::Inference,
        )
    }

    pub(crate) fn add_effect_dep(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.add_effect_dep_with_origin(
            current,
            current_span,
            target,
            target_span,
            EffectConstraintOrigin::Inference,
        )
    }

    pub(crate) fn add_effect_dep_with_origin(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
        origin: EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        self.add_effect_inclusion(
            current.clone(),
            current_span,
            target.clone(),
            target_span,
            origin,
        )
    }

    pub(super) fn expand_pending_dependencies(&mut self) -> Result<(), InternalCompilationError> {
        self.expand_all_pending_dependencies()?;

        let deferred_inclusions = mem::take(&mut self.deferred_inclusions);
        let mut residual_inclusions = Vec::new();
        for inclusion in deferred_inclusions {
            if !self.try_add_effect_inclusion(inclusion.clone(), false)? {
                residual_inclusions.push(inclusion);
            }
        }
        for inclusion in residual_inclusions {
            self.materialize_residual_inclusion(inclusion)?;
        }

        self.expand_all_pending_dependencies()?;
        self.check_closed_bounds()
    }

    /// Check that every inclusion into a closed row still holds.
    ///
    /// Values only grow, so a bound that holds after the last expansion holds
    /// for good. A concrete effect outside the row is an ordinary effect error.
    /// A variable left in the lower side is one the table could not close: if
    /// it were generalized, its bound would be lost from the scheme, so this is
    /// an internal error rather than a silent unsoundness.
    fn check_closed_bounds(&mut self) -> Result<(), InternalCompilationError> {
        for bound in mem::take(&mut self.closed_bounds) {
            let lower = self.normalize_effect(&bound.lower);
            Self::check_closed_inclusion(&lower, &bound.upper, &bound)?;
            if lower.has_variables() {
                return Err(internal_compilation_error!(Internal {
                    error: format!(
                        "effect solver could not enforce the bound {lower} <= {}",
                        bound.upper
                    ),
                    span: bound.lower_span,
                }));
            }
            self.closed_bounds.push(bound);
        }
        Ok(())
    }

    fn expand_all_pending_dependencies(&mut self) -> Result<(), InternalCompilationError> {
        let pending_dependencies = mem::take(&mut self.pending_dependencies);
        for dep in pending_dependencies {
            self.expand_pending_dependency(dep)?;
        }
        Ok(())
    }

    fn add_effect_inclusion(
        &mut self,
        lower: EffType,
        lower_span: Location,
        upper: EffType,
        upper_span: Location,
        origin: EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        self.ensure_effect_vars(&lower);
        self.ensure_effect_vars(&upper);
        let inclusion = EffectInclusion {
            lower,
            lower_span,
            upper,
            upper_span,
            origin,
        };
        self.try_add_effect_inclusion(inclusion, true).map(|_| ())
    }

    fn try_add_effect_inclusion(
        &mut self,
        inclusion: EffectInclusion,
        defer_ambiguous: bool,
    ) -> Result<bool, InternalCompilationError> {
        if let Some(lower_var) = inclusion.lower.to_single_variable() {
            let lower_root = self.table.find(lower_var);
            let lower_value = self.table.probe_value(lower_root);
            // Preserve the original lower-bound accumulator while it contains
            // only variables. Normalizing it first would turn repeated
            // dependencies `e <= a`, `e <= b` into a chain `a <= b` instead of
            // the intended union `e <= a | b`. This only applies to an open
            // upper bound: a closed one is a bound on every variable the lower
            // side stands for, applied below.
            if lower_value
                .as_ref()
                .is_none_or(|effects| effects.is_only_vars())
            {
                let upper = self.normalize_effect(&inclusion.upper);
                if upper.has_variables() {
                    if EffType::single_variable(lower_root) != upper {
                        self.table.union_value(lower_root, Some(upper));
                    }
                    return Ok(true);
                }
            }
        }

        let lower = self.normalize_effect(&inclusion.lower);
        let upper = self.normalize_effect(&inclusion.upper);
        self.record_closed_bound(&inclusion, &upper);

        if lower.is_empty() || lower == upper || lower.is_subset_of(&upper) {
            return Ok(true);
        }

        let lower_vars = lower.inner_vars();
        let upper_vars = upper.inner_vars();
        match (lower_vars.is_empty(), upper_vars.is_empty()) {
            (true, true) => Err(invalid_effect_dependency(
                lower,
                inclusion.lower_span,
                upper,
                inclusion.upper_span,
                inclusion.origin,
            )),
            (false, true) => {
                Self::check_closed_inclusion(&lower, &upper, &inclusion)?;
                for var in lower_vars {
                    self.table.union_value(var, Some(upper.clone()));
                }
                Ok(true)
            }
            (true, false) => {
                if let Some(var) = upper.to_single_variable() {
                    self.pending_dependencies.push(PendingEffectDependency {
                        source: lower,
                        source_span: inclusion.lower_span,
                        target: var,
                        target_span: inclusion.upper_span,
                        origin: inclusion.origin,
                    });
                    Ok(true)
                } else if defer_ambiguous {
                    self.deferred_inclusions.push(inclusion);
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            (false, false) => {
                if let Some(var) = lower.to_single_variable() {
                    self.table.union_value(var, Some(upper));
                    Ok(true)
                } else if let Some(var) = upper.to_single_variable() {
                    self.pending_dependencies.push(PendingEffectDependency {
                        source: lower,
                        source_span: inclusion.lower_span,
                        target: var,
                        target_span: inclusion.upper_span,
                        origin: inclusion.origin,
                    });
                    Ok(true)
                } else if defer_ambiguous {
                    self.deferred_inclusions.push(inclusion);
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
        }
    }

    fn materialize_residual_inclusion(
        &mut self,
        inclusion: EffectInclusion,
    ) -> Result<(), InternalCompilationError> {
        let lower = self.normalize_effect(&inclusion.lower);
        let upper = self.normalize_effect(&inclusion.upper);
        self.record_closed_bound(&inclusion, &upper);

        if lower.is_empty() || lower == upper || lower.is_subset_of(&upper) {
            return Ok(());
        }

        let lower_vars = lower.inner_vars();
        let upper_vars = upper.inner_vars();
        match (lower_vars.is_empty(), upper_vars.is_empty()) {
            (true, true) => Err(invalid_effect_dependency(
                lower,
                inclusion.lower_span,
                upper,
                inclusion.upper_span,
                inclusion.origin,
            )),
            (false, true) => {
                Self::check_closed_inclusion(&lower, &upper, &inclusion)?;
                for var in lower_vars {
                    self.table.union_value(var, Some(upper.clone()));
                }
                Ok(())
            }
            (_, false) => {
                // The concrete part of the lower side flows into every upper
                // variable, and each lower variable is bounded by the upper side.
                let concrete = EffType::multiple_primitive(&lower.inner_non_vars());
                if !concrete.is_empty() {
                    for &var in &upper_vars {
                        self.pending_dependencies.push(PendingEffectDependency {
                            source: concrete.clone(),
                            source_span: inclusion.lower_span,
                            target: var,
                            target_span: inclusion.upper_span,
                            origin: inclusion.origin.clone(),
                        });
                    }
                }
                for var in lower_vars {
                    self.table.union_value(var, Some(upper.clone()));
                }
                Ok(())
            }
        }
    }

    /// Keep `inclusion` for [`Self::check_closed_bounds`] if its normalized
    /// upper side `upper` is a closed row and its lower side has variables.
    ///
    /// The kept inclusion has its lower side as stated, whatever it normalizes
    /// to now: a variable of it may later gain effects through its own value,
    /// which neither its current normalization nor an inclusion that already
    /// holds would show. A lower side without variables is decided now.
    fn record_closed_bound(&mut self, inclusion: &EffectInclusion, upper: &EffType) {
        if upper.has_variables() || !inclusion.lower.has_variables() {
            return;
        }
        self.closed_bounds.push(EffectInclusion {
            upper: upper.clone(),
            ..inclusion.clone()
        });
    }

    /// Check that the concrete effects of `lower` fit in the closed row `upper`.
    ///
    /// A closed upper bound cannot grow, so the concrete effects the lower side
    /// already has are decided now; only its variables are left to bound.
    fn check_closed_inclusion(
        lower: &EffType,
        upper: &EffType,
        inclusion: &EffectInclusion,
    ) -> Result<(), InternalCompilationError> {
        let concrete = EffType::multiple_primitive(&lower.inner_non_vars());
        if concrete.is_subset_of(upper) {
            return Ok(());
        }
        Err(invalid_effect_dependency(
            concrete,
            inclusion.lower_span,
            upper.clone(),
            inclusion.upper_span,
            inclusion.origin.clone(),
        ))
    }

    fn normalize_effect(&mut self, eff: &EffType) -> EffType {
        let mut cache = FxHashMap::default();
        let mut visiting = FxHashSet::default();
        self.normalize_effect_inner(eff, &mut visiting, &mut cache)
    }

    fn normalize_effect_inner(
        &mut self,
        eff: &EffType,
        visiting: &mut FxHashSet<EffectVarKey>,
        cache: &mut FxHashMap<EffectVarKey, EffType>,
    ) -> EffType {
        if eff.is_empty() || !eff.has_variables() {
            return eff.clone();
        }

        let mut normalized = EffType::multiple_primitive(&eff.inner_non_vars());
        for var in eff.inner_vars() {
            self.ensure_var(var);
            let root = self.table.find(var);
            if let Some(cached) = cache.get(&root) {
                normalized.extend(cached);
                continue;
            }
            if !visiting.insert(root) {
                normalized.insert(Effect::Variable(root));
                continue;
            }
            let root_effect = match self.table.probe_value(root) {
                Some(value) => self.normalize_effect_inner(&value, visiting, cache),
                None => EffType::single_variable(root),
            };
            visiting.remove(&root);
            cache.insert(root, root_effect.clone());
            normalized.extend(&root_effect);
        }
        normalized
    }

    fn expand_pending_dependency(
        &mut self,
        dep: PendingEffectDependency,
    ) -> Result<(), InternalCompilationError> {
        let mut visiting = FxHashSet::default();
        self.expand_pending_dependency_inner(dep, &mut visiting)
    }

    fn expand_pending_dependency_inner(
        &mut self,
        dep: PendingEffectDependency,
        visiting: &mut FxHashSet<EffectVarKey>,
    ) -> Result<(), InternalCompilationError> {
        self.ensure_var(dep.target);
        let target = self.table.find(dep.target);
        if !visiting.insert(target) {
            self.table.union_value(
                target,
                Some(dep.source.union(&EffType::single_variable(target))),
            );
            return Ok(());
        }

        let result = if let Some(existing_effects) = self.table.probe_value(target) {
            if current_satisfied_by_target(&dep.source, &existing_effects) {
                Ok(())
            } else {
                let target_vars = existing_effects.inner_vars();
                if target_vars.is_empty() {
                    Err(invalid_effect_dependency(
                        dep.source,
                        dep.source_span,
                        existing_effects,
                        dep.target_span,
                        dep.origin,
                    ))
                } else {
                    self.table
                        .union_value(target, Some(existing_effects.union(&dep.source)));
                    for var in target_vars {
                        self.expand_pending_dependency_inner(
                            PendingEffectDependency {
                                source: dep.source.clone(),
                                source_span: dep.source_span,
                                target: var,
                                target_span: dep.target_span,
                                origin: dep.origin.clone(),
                            },
                            visiting,
                        )?;
                    }
                    Ok(())
                }
            }
        } else {
            self.table.union_value(
                target,
                Some(dep.source.union(&EffType::single_variable(target))),
            );
            Ok(())
        };

        visiting.remove(&target);
        result
    }

    pub(super) fn effect_var_value(&mut self, var: EffectVar) -> Option<EffType> {
        self.ensure_var(var);
        let root = self.table.find(var);
        self.table.probe_value(root)
    }

    pub(super) fn effect_var_root(&mut self, var: EffectVar) -> EffectVar {
        self.ensure_var(var);
        self.table.find(var)
    }

    pub(super) fn effect_var_affects_substitution(&mut self, var: EffectVar) -> bool {
        self.ensure_var(var);
        let root = self.table.find(var);
        if root != var {
            return true;
        }
        self.table
            .probe_value(root)
            .is_some_and(|value| value.to_single_variable() != Some(root))
    }

    pub(super) fn log_debug_constraints(&mut self) {
        if !log::log_enabled!(log::Level::Trace) {
            return;
        }
        log::trace!("Effect substitution table:");
        for i in 0..self.table.len() {
            let var = EffectVar::new(i as u32);
            let value = self.table.probe_value(var);
            match value {
                Some(value) => log::trace!("  {var} → {value}"),
                None => log::trace!("  {var} → {} (unbound)", self.table.find(var)),
            }
        }
        if !self.pending_dependencies.is_empty() {
            log::trace!("Inverted effect constraints:");
            for dep in &self.pending_dependencies {
                log::trace!("  {} → {}", dep.source, dep.target);
            }
        }
    }
}

fn current_satisfied_by_target(current: &EffType, target: &EffType) -> bool {
    let target_primitives = EffType::multiple_primitive(&target.inner_non_vars());
    current.is_subset_of(&target_primitives)
}

fn invalid_effect_dependency(
    source: EffType,
    source_span: Location,
    target: EffType,
    target_span: Location,
    origin: EffectConstraintOrigin,
) -> InternalCompilationError {
    match origin {
        EffectConstraintOrigin::Inference => internal_compilation_error!(InvalidEffectDependency {
            source,
            source_span,
            target,
            target_span,
        }),
        EffectConstraintOrigin::TraitMethodImpl {
            trait_id,
            method_name,
            impl_span,
        } => internal_compilation_error!(TraitMethodEffectMismatch {
            trait_ref: trait_id,
            method_name,
            expected: target,
            got: source,
            span: impl_span,
        }),
    }
}

#[cfg(test)]
mod tests {
    use ustr::ustr;

    use super::{EffectConstraintOrigin, EffectSolver, PendingEffectDependency};
    use crate::{
        compiler::error::CompilationErrorImpl,
        module::{LocalTraitId, ModuleId, TraitId},
        parser::location::Location,
        types::effects::{EffType, Effect, PrimitiveEffect},
    };

    #[test]
    fn pure_effect_bound_survives_a_dependency_unified_with_its_target() {
        let mut solver = EffectSolver::default();
        let source = solver.fresh_var_ty();
        let target = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        // Equating a dependency with its target leaves a self-referential row, which the table
        // cannot close: the pure bound below leaves the variable open. The recorded closed bound
        // catches the later effect when pending dependencies are expanded.
        solver.add_effect_dep(&source, span, &target, span).unwrap();
        solver
            .unify_same_effect(source.clone(), span, target, span)
            .unwrap();
        solver
            .add_effect_dep(&source, span, &EffType::empty(), span)
            .unwrap();

        let result = solver
            .add_effect_dep(
                &EffType::single_primitive(PrimitiveEffect::Fallible),
                span,
                &source,
                span,
            )
            .and_then(|()| solver.expand_pending_dependencies());
        result.expect_err("a variable bounded by the pure row must reject fallible effects");
    }

    #[test]
    fn pure_effect_bound_on_a_variable_left_open_is_an_internal_error() {
        let mut solver = EffectSolver::default();
        let source = solver.fresh_var_ty();
        let target = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        // As above, but with no later effect: generalizing the open variable would drop its bound.
        solver.add_effect_dep(&source, span, &target, span).unwrap();
        solver
            .unify_same_effect(source.clone(), span, target, span)
            .unwrap();
        solver
            .add_effect_dep(&source, span, &EffType::empty(), span)
            .unwrap();

        let error = solver.expand_pending_dependencies().unwrap_err();
        assert!(
            matches!(&*error, CompilationErrorImpl::Internal { .. }),
            "expected an internal error, got {error:?}"
        );
    }

    #[test]
    fn pure_effect_bound_holds_for_the_variable_as_stated() {
        let mut solver = EffectSolver::default();
        let source = solver.fresh_var_ty();
        let dependency = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        // `source` stands for `dependency` when bounded, then gains an effect of its own.
        solver
            .add_effect_dep(&source, span, &dependency, span)
            .unwrap();
        solver
            .add_effect_dep(&source, span, &EffType::empty(), span)
            .unwrap();
        solver
            .unify_same_effect(
                source,
                span,
                EffType::single_primitive(PrimitiveEffect::Fallible),
                span,
            )
            .unwrap();

        solver.expand_pending_dependencies().unwrap_err();
    }

    #[test]
    fn pure_effect_bound_that_already_holds_is_kept() {
        let mut solver = EffectSolver::default();
        let source = solver.fresh_var_ty();
        let dependency = solver.fresh_var_ty();
        let span = Location::new_synthesized();

        // The bound holds when added, as `source` stands for the pure `dependency`; it must still
        // hold once `source` gains an effect of its own.
        solver
            .add_effect_dep(&source, span, &dependency, span)
            .unwrap();
        solver
            .unify_same_effect(dependency, span, EffType::empty(), span)
            .unwrap();
        solver
            .add_effect_dep(&source, span, &EffType::empty(), span)
            .unwrap();
        solver
            .unify_same_effect(
                source,
                span,
                EffType::single_primitive(PrimitiveEffect::Fallible),
                span,
            )
            .unwrap();

        solver.expand_pending_dependencies().unwrap_err();
    }

    #[test]
    fn deferred_inclusion_is_retried_as_stated() {
        let mut solver = EffectSolver::default();
        let alias = solver.fresh_var();
        let target = solver.fresh_var_ty();
        let other = solver.fresh_var();
        let left = solver.fresh_var();
        let right = solver.fresh_var();
        let span = Location::new_synthesized();

        // `alias` stands for `target` when the ambiguous inclusion is deferred, then gains an
        // effect of its own before the inclusion's upper side is closed.
        solver
            .add_effect_dep(&EffType::single_variable(alias), span, &target, span)
            .unwrap();
        solver
            .add_effect_dep(
                &EffType::multiple_variable(&[alias, other]),
                span,
                &EffType::multiple_variable(&[left, right]),
                span,
            )
            .unwrap();
        for var in [left, right] {
            solver
                .add_effect_dep(
                    &EffType::single_variable(var),
                    span,
                    &EffType::empty(),
                    span,
                )
                .unwrap();
        }
        solver
            .unify_same_effect(
                EffType::single_variable(alias),
                span,
                EffType::single_primitive(PrimitiveEffect::Fallible),
                span,
            )
            .unwrap();

        solver.expand_pending_dependencies().unwrap_err();
    }

    #[test]
    fn self_referential_effect_var_is_a_stable_noop() {
        let mut solver = EffectSolver::default();
        let var = solver.table.new_key(None);
        solver
            .table
            .union_value(var, Some(EffType::single_variable(var)));

        assert!(!solver.effect_var_affects_substitution(var));
        assert_eq!(
            solver.normalize_effect(&EffType::single_variable(var)),
            EffType::single_variable(var)
        );
    }

    #[test]
    fn expanding_inverted_effect_dependency_handles_variable_cycles() {
        let mut solver = EffectSolver::default();
        let first = solver.table.new_key(None);
        let second = solver.table.new_key(None);
        solver
            .table
            .union_value(first, Some(EffType::single_variable(second)));
        solver
            .table
            .union_value(second, Some(EffType::single_variable(first)));

        let span = Location::new_synthesized();
        solver
            .expand_pending_dependency(PendingEffectDependency {
                source: EffType::single_primitive(PrimitiveEffect::Write),
                source_span: span,
                target: first,
                target_span: span,
                origin: EffectConstraintOrigin::Inference,
            })
            .unwrap();

        let first_effects = solver.table.probe_value(first).unwrap();
        assert!(first_effects.contains(Effect::Primitive(PrimitiveEffect::Write)));
    }

    #[test]
    fn pending_effect_dependency_preserves_trait_method_origin() {
        let mut solver = EffectSolver::default();
        let target = solver.table.new_key(None);
        let span = Location::new_synthesized();
        let trait_id = TraitId::new(ModuleId::new(0), LocalTraitId::new(0));
        let method_name = ustr("pure");

        solver
            .add_effect_dep_with_origin(
                &EffType::single_primitive(PrimitiveEffect::Read),
                span,
                &EffType::single_variable(target),
                span,
                EffectConstraintOrigin::TraitMethodImpl {
                    trait_id,
                    method_name,
                    impl_span: span,
                },
            )
            .unwrap();
        solver.table.union_value(target, Some(EffType::empty()));

        let error = solver.expand_pending_dependencies().unwrap_err();
        match &*error {
            CompilationErrorImpl::TraitMethodEffectMismatch {
                trait_ref,
                method_name: got_method_name,
                expected,
                got,
                span: got_span,
            } => {
                assert_eq!(*trait_ref, trait_id);
                assert_eq!(*got_method_name, method_name);
                assert_eq!(*expected, EffType::empty());
                assert_eq!(*got, EffType::single_primitive(PrimitiveEffect::Read));
                assert_eq!(*got_span, span);
            }
            other => panic!("expected TraitMethodEffectMismatch, got {other:?}"),
        }
    }

    #[test]
    fn inclusion_into_pure_effect_closes_unconstrained_variable() {
        let mut solver = EffectSolver::default();
        let var = solver.table.new_key(None);
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(
                &EffType::single_variable(var),
                span,
                &EffType::empty(),
                span,
            )
            .unwrap();
        assert_eq!(solver.table.probe_value(var), Some(EffType::empty()));

        solver
            .add_effect_dep(
                &EffType::single_primitive(PrimitiveEffect::Fallible),
                span,
                &EffType::single_variable(var),
                span,
            )
            .unwrap_err();
    }

    #[test]
    fn inclusion_into_pure_effect_closes_the_variables_a_variable_stands_for() {
        let mut solver = EffectSolver::default();
        let left = solver.table.new_key(None);
        let right = solver.table.new_key(None);
        let union = solver
            .table
            .new_key(Some(EffType::multiple_variable(&[left, right])));
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(
                &EffType::single_variable(union),
                span,
                &EffType::empty(),
                span,
            )
            .unwrap();
        assert_eq!(solver.table.probe_value(left), Some(EffType::empty()));
        assert_eq!(solver.table.probe_value(right), Some(EffType::empty()));
    }

    #[test]
    fn inclusion_into_pure_effect_rejects_concrete_effects_beside_variables() {
        let mut solver = EffectSolver::default();
        let var = solver.table.new_key(None);
        let span = Location::new_synthesized();
        let lower = EffType::single_primitive(PrimitiveEffect::Fallible)
            .union(&EffType::single_variable(var));

        solver
            .add_effect_dep(&lower, span, &EffType::empty(), span)
            .unwrap_err();
    }

    #[test]
    fn effect_equality_binds_union_to_single_variable() {
        let mut solver = EffectSolver::default();
        let left = solver.table.new_key(None);
        let right = solver.table.new_key(None);
        let output = solver.table.new_key(None);
        let span = Location::new_synthesized();

        solver
            .unify_same_effect(
                EffType::multiple_variable(&[left, right]),
                span,
                EffType::single_variable(output),
                span,
            )
            .unwrap();

        solver
            .unify_same_effect(
                EffType::single_variable(left),
                span,
                EffType::single_primitive(PrimitiveEffect::Read),
                span,
            )
            .unwrap();
        solver
            .unify_same_effect(
                EffType::single_variable(right),
                span,
                EffType::single_primitive(PrimitiveEffect::Write),
                span,
            )
            .unwrap();
        solver.expand_pending_dependencies().unwrap();

        let output_effects = solver.normalize_effect(&EffType::single_variable(output));
        assert!(output_effects.contains(Effect::Primitive(PrimitiveEffect::Read)));
        assert!(output_effects.contains(Effect::Primitive(PrimitiveEffect::Write)));
    }

    #[test]
    fn effect_equality_defers_multi_variable_unions() {
        let mut solver = EffectSolver::default();
        let left_a = solver.table.new_key(None);
        let left_b = solver.table.new_key(None);
        let right_a = solver.table.new_key(None);
        let right_b = solver.table.new_key(None);
        let span = Location::new_synthesized();

        solver
            .unify_same_effect(
                EffType::multiple_variable(&[left_a, left_b]),
                span,
                EffType::multiple_variable(&[right_a, right_b]),
                span,
            )
            .unwrap();

        solver
            .unify_same_effect(
                EffType::single_variable(right_a),
                span,
                EffType::single_primitive(PrimitiveEffect::Read),
                span,
            )
            .unwrap();
        solver
            .unify_same_effect(
                EffType::single_variable(right_b),
                span,
                EffType::single_primitive(PrimitiveEffect::Write),
                span,
            )
            .unwrap();
        solver.expand_pending_dependencies().unwrap();

        let left_effects = solver.normalize_effect(&EffType::multiple_variable(&[left_a, left_b]));
        assert!(left_effects.contains(Effect::Primitive(PrimitiveEffect::Read)));
        assert!(left_effects.contains(Effect::Primitive(PrimitiveEffect::Write)));
    }

    #[test]
    fn residual_inclusion_is_materialized_conservatively() {
        let mut solver = EffectSolver::default();
        let left = solver.table.new_key(None);
        let right = solver.table.new_key(None);
        let span = Location::new_synthesized();

        solver
            .add_effect_dep(
                &EffType::single_primitive(PrimitiveEffect::Read),
                span,
                &EffType::multiple_variable(&[left, right]),
                span,
            )
            .unwrap();
        solver.expand_pending_dependencies().unwrap();

        let left_effects = solver.normalize_effect(&EffType::single_variable(left));
        let right_effects = solver.normalize_effect(&EffType::single_variable(right));
        assert!(left_effects.contains(Effect::Primitive(PrimitiveEffect::Read)));
        assert!(right_effects.contains(Effect::Primitive(PrimitiveEffect::Read)));
    }
}
