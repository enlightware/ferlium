use std::borrow::Borrow;

use ena::unify::{InPlace, InPlaceUnificationTable, Snapshot};

use crate::{
    FxHashSet,
    compiler::error::InternalCompilationError,
    internal_compilation_error,
    parser::location::Location,
    types::{
        effects::{EffType, Effect, EffectVar, EffectVarKey},
        r#type::{FnType, Type, TypeKind},
    },
};

use super::constraints::EffectConstraint;

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
}

/// A deferred effect inclusion `lower <= upper`.
///
/// Effect equality is represented as two inclusions. Inclusions that have a
/// unique local interpretation are solved eagerly; ambiguous composite
/// inclusions are kept until more type/trait solving has substituted effect
/// variables. Any residual inclusion is materialized conservatively into the
/// involved variables before generalization, preserving sound upper bounds at
/// the cost of possible imprecision.
#[derive(Debug, Clone)]
struct EffectInclusion {
    lower: EffType,
    lower_span: Location,
    upper: EffType,
    upper_span: Location,
}

pub(crate) struct EffectSolverSnapshot {
    table: Snapshot<InPlace<EffectVarKey>>,
    pending_dependencies: Vec<PendingEffectDependency>,
    deferred_inclusions: Vec<EffectInclusion>,
}

/// Solver state for inferred effect variables and effect relations.
///
/// Effect unification is modeled as inclusion constraints. Simple inclusions
/// are solved eagerly in the union table, while ambiguous composite relations
/// are deferred until type and trait solving have substituted more variables.
/// Before generalization, any residual deferred relation is conservatively
/// materialized into the variables it constrains.
#[derive(Default, Debug)]
pub(crate) struct EffectSolver {
    table: InPlaceUnificationTable<EffectVarKey>,
    constraints: Vec<EffectConstraint>,
    pending_dependencies: Vec<PendingEffectDependency>,
    deferred_inclusions: Vec<EffectInclusion>,
}

impl EffectSolver {
    pub(crate) fn fresh_var(&mut self) -> EffectVar {
        self.table.new_key(None)
    }

    pub(crate) fn fresh_var_ty(&mut self) -> EffType {
        EffType::single_variable(self.fresh_var())
    }

    pub(crate) fn snapshot(&mut self) -> EffectSolverSnapshot {
        EffectSolverSnapshot {
            table: self.table.snapshot(),
            pending_dependencies: self.pending_dependencies.clone(),
            deferred_inclusions: self.deferred_inclusions.clone(),
        }
    }

    pub(crate) fn rollback_to(&mut self, snapshot: EffectSolverSnapshot) {
        self.table.rollback_to(snapshot.table);
        self.pending_dependencies = snapshot.pending_dependencies;
        self.deferred_inclusions = snapshot.deferred_inclusions;
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
        std::mem::take(&mut self.constraints)
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
        let root = self.table.find(var);
        if root != var { Some(root) } else { None }
    }

    /// Generalize concrete effects in a function type to effect variables.
    ///
    /// This is needed when unifying a type variable with a function type, to
    /// preserve effect polymorphism.
    pub(super) fn generalize_function_effects(&mut self, ty: Type) -> Type {
        use TypeKind::*;
        let ty_data = ty.data();
        match &*ty_data {
            Function(fn_ty) => {
                let fn_ty = fn_ty.clone();
                drop(ty_data);
                let has_primitive_effects = fn_ty.effects.iter().any(|e| e.is_primitive());
                if has_primitive_effects {
                    let fresh_eff_var = self.table.new_key(None);
                    for eff in fn_ty.effects.iter() {
                        if eff.is_primitive() {
                            self.pending_dependencies.push(PendingEffectDependency {
                                source: EffType::single(eff),
                                source_span: Location::new_synthesized(),
                                target: fresh_eff_var,
                                target_span: Location::new_synthesized(),
                            });
                        } else if let Some(var) = eff.as_variable() {
                            self.table.union(fresh_eff_var, *var);
                        }
                    }
                    let new_fn_ty = FnType::new_with_return_convention(
                        fn_ty.args.clone(),
                        fn_ty.ret,
                        EffType::single_variable(fresh_eff_var),
                        fn_ty.return_convention,
                    );
                    Type::function_type(new_fn_ty)
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

    /// Require the selected implementation's output effect to fit in the
    /// trait output effect requested by the call site.
    pub(super) fn resolve_trait_output_effect(
        &mut self,
        constraint_eff: &EffType,
        solved_eff: &EffType,
        span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.add_effect_inclusion(solved_eff.clone(), span, constraint_eff.clone(), span)
    }

    /// Make current and target the same effect type.
    pub(crate) fn unify_same_effect(
        &mut self,
        current: EffType,
        current_span: Location,
        target: EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        match (current.to_single_variable(), target.to_single_variable()) {
            (Some(current_var), Some(target_var)) => {
                self.table
                    .unify_var_var(current_var, target_var)
                    .map_err(|_| {
                        internal_compilation_error!(InvalidEffectDependency {
                            source: current,
                            source_span: current_span,
                            target,
                            target_span,
                        })
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
        self.add_effect_inclusion(current.clone(), current_span, target.clone(), target_span)?;
        self.add_effect_inclusion(target, target_span, current, current_span)
    }

    pub(crate) fn add_effect_dep(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.add_effect_inclusion(current.clone(), current_span, target.clone(), target_span)
    }

    pub(super) fn expand_pending_dependencies(&mut self) -> Result<(), InternalCompilationError> {
        self.expand_all_pending_dependencies()?;

        let deferred_inclusions = std::mem::take(&mut self.deferred_inclusions);
        let mut residual_inclusions = Vec::new();
        for inclusion in deferred_inclusions {
            if !self.try_add_effect_inclusion(inclusion.clone(), false)? {
                residual_inclusions.push(inclusion);
            }
        }
        for inclusion in residual_inclusions {
            self.materialize_residual_inclusion(inclusion)?;
        }

        self.expand_all_pending_dependencies()
    }

    fn expand_all_pending_dependencies(&mut self) -> Result<(), InternalCompilationError> {
        let pending_dependencies = std::mem::take(&mut self.pending_dependencies);
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
    ) -> Result<(), InternalCompilationError> {
        let inclusion = EffectInclusion {
            lower,
            lower_span,
            upper,
            upper_span,
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
            // the intended union `e <= a | b`.
            if lower_value
                .as_ref()
                .is_none_or(|effects| effects.is_only_vars())
            {
                let upper = self.normalize_effect(&inclusion.upper);
                if upper.is_empty() || EffType::single_variable(lower_root) == upper {
                    return Ok(true);
                }
                self.table.union_value(lower_root, Some(upper));
                return Ok(true);
            }
        }

        let lower = self.normalize_effect(&inclusion.lower);
        let upper = self.normalize_effect(&inclusion.upper);

        if lower.is_empty() || lower == upper || lower.is_subset_of(&upper) {
            return Ok(true);
        }

        let lower_vars = lower.inner_vars();
        let upper_vars = upper.inner_vars();
        match (lower_vars.is_empty(), upper_vars.is_empty()) {
            (true, true) => Err(internal_compilation_error!(InvalidEffectDependency {
                source: lower,
                source_span: inclusion.lower_span,
                target: upper,
                target_span: inclusion.upper_span,
            })),
            (false, true) => {
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
                    });
                    Ok(true)
                } else if defer_ambiguous {
                    self.deferred_inclusions.push(EffectInclusion {
                        lower,
                        lower_span: inclusion.lower_span,
                        upper,
                        upper_span: inclusion.upper_span,
                    });
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
                    });
                    Ok(true)
                } else if defer_ambiguous {
                    self.deferred_inclusions.push(EffectInclusion {
                        lower,
                        lower_span: inclusion.lower_span,
                        upper,
                        upper_span: inclusion.upper_span,
                    });
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

        if lower.is_empty() || lower == upper || lower.is_subset_of(&upper) {
            return Ok(());
        }

        let lower_vars = lower.inner_vars();
        let upper_vars = upper.inner_vars();
        match (lower_vars.is_empty(), upper_vars.is_empty()) {
            (true, true) => Err(internal_compilation_error!(InvalidEffectDependency {
                source: lower,
                source_span: inclusion.lower_span,
                target: upper,
                target_span: inclusion.upper_span,
            })),
            (false, _) => {
                for var in lower_vars {
                    self.table.union_value(var, Some(upper.clone()));
                }
                Ok(())
            }
            (true, false) => {
                for var in upper_vars {
                    self.pending_dependencies.push(PendingEffectDependency {
                        source: lower.clone(),
                        source_span: inclusion.lower_span,
                        target: var,
                        target_span: inclusion.upper_span,
                    });
                }
                Ok(())
            }
        }
    }

    fn normalize_effect(&mut self, eff: &EffType) -> EffType {
        let mut visiting = FxHashSet::default();
        self.normalize_effect_inner(eff, &mut visiting)
    }

    fn normalize_effect_inner(
        &mut self,
        eff: &EffType,
        visiting: &mut FxHashSet<EffectVarKey>,
    ) -> EffType {
        if eff.is_empty() || !eff.has_variables() {
            return eff.clone();
        }

        let mut normalized = EffType::multiple_primitive(&eff.inner_non_vars());
        for var in eff.inner_vars() {
            let root = self.table.find(var);
            if !visiting.insert(root) {
                normalized.insert(Effect::Variable(root));
                continue;
            }
            match self.table.probe_value(root) {
                Some(value) => normalized.extend(&self.normalize_effect_inner(&value, visiting)),
                None => normalized.insert(Effect::Variable(root)),
            }
            visiting.remove(&root);
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
                    Err(internal_compilation_error!(InvalidEffectDependency {
                        source: dep.source,
                        source_span: dep.source_span,
                        target: existing_effects,
                        target_span: dep.target_span,
                    }))
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
        self.table.probe_value(var)
    }

    pub(super) fn effect_var_root(&mut self, var: EffectVar) -> EffectVar {
        self.table.find(var)
    }

    pub(super) fn effect_var_affects_substitution(&mut self, var: EffectVar) -> bool {
        self.table.probe_value(var).is_some() || self.table.find(var) != var
    }

    pub(super) fn log_debug_constraints(&mut self) {
        log::debug!("Effect substitution table:");
        for i in 0..self.table.len() {
            let var = EffectVar::new(i as u32);
            let value = self.table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {value}"),
                None => log::debug!("  {var} → {} (unbound)", self.table.find(var)),
            }
        }
        if !self.pending_dependencies.is_empty() {
            log::debug!("Inverted effect constraints:");
            for dep in &self.pending_dependencies {
                log::debug!("  {} → {}", dep.source, dep.target);
            }
        }
    }
}

fn current_satisfied_by_target(current: &EffType, target: &EffType) -> bool {
    let target_primitives = EffType::multiple_primitive(&target.inner_non_vars());
    current.is_subset_of(&target_primitives)
}

#[cfg(test)]
mod tests {
    use crate::{
        parser::location::Location,
        types::effects::{EffType, Effect, PrimitiveEffect},
    };

    use super::{EffectSolver, PendingEffectDependency};

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
            })
            .unwrap();

        let first_effects = solver.table.probe_value(first).unwrap();
        assert!(first_effects.contains(Effect::Primitive(PrimitiveEffect::Write)));
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
