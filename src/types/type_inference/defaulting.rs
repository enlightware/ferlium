use std::mem;

use itertools::Itertools;
use ustr::ustr;

use crate::{
    FxHashMap, FxHashSet,
    compiler::error::InternalCompilationError,
    hir::{NodeArena, NodeId, NodeKind},
    parser::location::Location,
    std::core_traits_names::NUM_TRAIT_NAME,
    types::{
        trait_solver::TraitSolver,
        r#type::{Type, TypeVar},
        type_like::TypeLike,
        type_scheme::PubTypeConstraint,
    },
};

use super::{
    substitution::InstSubstitution,
    unify::{UnifiedTypeInference, total_constraints_var_count},
};

/// A transitive boundary over public constraints, defined by seed type variables.
#[derive(Debug, Clone, Default)]
pub struct ConstraintBoundary {
    seed_ty_vars: Vec<TypeVar>,
}

impl ConstraintBoundary {
    pub fn from_seed_ty_vars(seed_ty_vars: impl IntoIterator<Item = TypeVar>) -> Self {
        Self {
            seed_ty_vars: seed_ty_vars.into_iter().unique().collect(),
        }
    }

    pub fn from_constraints(constraints: &[PubTypeConstraint]) -> Self {
        Self::from_seed_ty_vars(
            constraints
                .iter()
                .flat_map(|constraint| constraint.inner_ty_vars()),
        )
    }

    fn accessible_constraint_indices(&self, constraints: &[PubTypeConstraint]) -> FxHashSet<usize> {
        if self.seed_ty_vars.is_empty() {
            return FxHashSet::default();
        }

        let mut ins: FxHashSet<_> = constraints
            .iter()
            .enumerate()
            .filter(|(_, constraint)| constraint.contains_any_ty_vars(&self.seed_ty_vars))
            .map(|(index, _)| index)
            .collect();

        loop {
            let accessible_ty_vars: Vec<_> = ins
                .iter()
                .flat_map(|index| constraints[*index].inner_ty_vars())
                .unique()
                .collect();
            let new_ins: FxHashSet<_> = constraints
                .iter()
                .enumerate()
                .filter(|(_, constraint)| constraint.contains_any_ty_vars(&accessible_ty_vars))
                .map(|(index, _)| index)
                .collect();
            if new_ins.len() == ins.len() {
                break;
            }
            ins = new_ins;
        }

        ins
    }

    pub fn accessible_constraints<'a>(
        &self,
        constraints: &'a [PubTypeConstraint],
    ) -> Vec<&'a PubTypeConstraint> {
        let indices = self.accessible_constraint_indices(constraints);
        constraints
            .iter()
            .enumerate()
            .filter(|(index, _)| indices.contains(index))
            .map(|(_, constraint)| constraint)
            .collect()
    }

    pub fn inaccessible_constraints<'a>(
        &self,
        constraints: &'a [PubTypeConstraint],
    ) -> Vec<&'a PubTypeConstraint> {
        let indices = self.accessible_constraint_indices(constraints);
        constraints
            .iter()
            .enumerate()
            .filter(|(index, _)| !indices.contains(index))
            .map(|(_, constraint)| constraint)
            .collect()
    }

    fn owned_accessible_constraints(
        &self,
        constraints: &[PubTypeConstraint],
    ) -> Vec<PubTypeConstraint> {
        self.accessible_constraints(constraints)
            .into_iter()
            .cloned()
            .collect()
    }

    pub fn owned_inaccessible_constraints(
        &self,
        constraints: &[PubTypeConstraint],
    ) -> Vec<PubTypeConstraint> {
        self.inaccessible_constraints(constraints)
            .into_iter()
            .cloned()
            .collect()
    }
}

/// Semantic inputs for boundary-aware post-unification defaulting.
#[derive(Debug, Clone, Default)]
pub struct DefaultingScope {
    boundary: ConstraintBoundary,
    expr_root_ty: Option<Type>,
    unit_variant_seed_tys: Vec<Type>,
}

impl DefaultingScope {
    pub fn from_constraints(constraints: &[PubTypeConstraint]) -> Self {
        Self {
            boundary: ConstraintBoundary::from_constraints(constraints),
            expr_root_ty: None,
            unit_variant_seed_tys: Vec::new(),
        }
    }

    pub fn with_expr_root_ty(mut self, expr_root_ty: Type) -> Self {
        self.expr_root_ty = Some(expr_root_ty);
        self
    }

    pub fn with_unit_variant_seed_tys(
        mut self,
        unit_variant_seed_tys: impl IntoIterator<Item = Type>,
    ) -> Self {
        self.unit_variant_seed_tys = unit_variant_seed_tys.into_iter().unique().collect();
        self
    }

    fn boundary_constraints(&self, constraints: &[PubTypeConstraint]) -> Vec<PubTypeConstraint> {
        self.boundary.owned_accessible_constraints(constraints)
    }

    fn unit_default_constraints(
        &self,
        ty_inf: &mut UnifiedTypeInference,
        remaining_constraints: &[PubTypeConstraint],
        boundary_constraints: &[PubTypeConstraint],
    ) -> Vec<PubTypeConstraint> {
        let unit_variant_seed_ty_vars: Vec<_> = self
            .unit_variant_seed_tys
            .iter()
            .flat_map(|seed_ty| ty_inf.substitute_in_type(*seed_ty).inner_ty_vars())
            .unique()
            .collect();
        if unit_variant_seed_ty_vars.is_empty() {
            return Vec::new();
        }

        let unit_boundary = ConstraintBoundary::from_seed_ty_vars(unit_variant_seed_ty_vars);
        let source = if boundary_constraints.is_empty() {
            remaining_constraints
        } else {
            boundary_constraints
        };
        unit_boundary.owned_accessible_constraints(source)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DefaultingProgressKey {
    unresolved_expr_var_count: usize,
    boundary_constraint_var_count: usize,
}

impl UnifiedTypeInference {
    /// Re-solve remaining constraints after defaulting has added new information
    /// to the unification tables. Constraints that are now solvable are removed.
    fn resolve_remaining_constraints_to_fixed_point(
        &mut self,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<(), InternalCompilationError> {
        loop {
            self.normalize_remaining_constraints();
            let constraints = mem::take(&mut self.remaining_ty_constraints);
            let old_count = constraints.len();
            let old_var_count = total_constraints_var_count(constraints.iter());
            self.remaining_ty_constraints =
                self.unify_constraint_pass(&constraints, |_| false, trait_solver, arena)?;
            let new_var_count = total_constraints_var_count(self.remaining_ty_constraints.iter());
            if self.remaining_ty_constraints.len() == old_count && new_var_count == old_var_count {
                break;
            }
        }
        Ok(())
    }

    pub(crate) fn collect_unit_variant_seed_types(arena: &NodeArena, id: NodeId) -> Vec<Type> {
        let mut tys = FxHashSet::default();
        Self::collect_unit_variant_seed_types_into(arena, id, &mut tys);
        tys.into_iter().collect()
    }

    fn collect_unit_variant_seed_types_into(
        arena: &NodeArena,
        id: NodeId,
        tys: &mut FxHashSet<Type>,
    ) {
        match &arena[id].kind {
            NodeKind::Immediate(immediate) => immediate
                .value
                .as_variant()
                .filter(|variant| variant.value.is_unit())
                .into_iter()
                .for_each(|_| {
                    tys.insert(arena[id].ty);
                }),
            kind => kind.child_node_ids().into_iter().for_each(|child_id| {
                Self::collect_unit_variant_seed_types_into(arena, child_id, tys)
            }),
        }
    }

    /// Default variant constraints in the provided boundary by unifying
    /// eligible type variables with minimalist variant types.
    pub fn default_orphan_variants_in_constraints(
        &mut self,
        constraints: &[PubTypeConstraint],
    ) -> Result<(), InternalCompilationError> {
        use crate::types::type_scheme::VariantConstraint;

        // First, collect the type variables that are invalid for variant simplification.
        let mut invalid_ty_vars = FxHashSet::<TypeVar>::default();
        for constraint in constraints {
            match constraint {
                PubTypeConstraint::TypeHasVariant { payload_ty, .. } => {
                    invalid_ty_vars.extend(payload_ty.inner_ty_vars());
                }
                PubTypeConstraint::HaveTrait { .. } => {}
                _ => {
                    invalid_ty_vars.extend(constraint.inner_ty_vars());
                }
            }
        }

        // Collect variant constraints grouped by type variable.
        let mut variants: FxHashMap<TypeVar, VariantConstraint> = FxHashMap::default();
        let mut variant_spans: FxHashMap<TypeVar, Location> = FxHashMap::default();
        for constraint in constraints {
            if let PubTypeConstraint::TypeHasVariant {
                variant_ty,
                variant_span,
                tag,
                payload_ty,
                ..
            } = constraint
            {
                if let Some(ty_var) = variant_ty.data().as_variable() {
                    if !invalid_ty_vars.contains(ty_var) {
                        let existing = variants
                            .entry(*ty_var)
                            .or_default()
                            .insert(*tag, *payload_ty);
                        assert!(existing.is_none(), "Duplicate variant constraint for {tag}");
                        variant_spans
                            .entry(*ty_var)
                            .or_insert(variant_span.use_site);
                    }
                }
            }
        }

        // Unify each variable with its minimalist variant type.
        for (ty_var, variant) in variants {
            let variant_ty = Type::variant(variant.into_iter().collect::<Vec<_>>());
            let span = variant_spans[&ty_var];
            self.unify_same_type(Type::variable(ty_var), span, variant_ty, span)?;
        }
        Ok(())
    }

    /// Default Num-constrained type variables to int or float by unifying
    /// directly in the unification table.
    pub fn default_num_types_once(
        &mut self,
        constraints: &[PubTypeConstraint],
        trait_solver: &mut TraitSolver<'_>,
        _arena: &mut NodeArena,
    ) -> Result<(), InternalCompilationError> {
        if constraints.is_empty() {
            return Ok(());
        }

        use crate::module::ConcreteTraitImplKey;
        use crate::std::{
            STD_MODULE_ID,
            math::{float_type, int_type},
        };

        let default_tys = [int_type(), float_type()];

        // Re-substitute boundary constraints to see the current state of type variables.
        let subst_constraints = self.substitute_in_constraints(constraints);

        // First, collect invalid type variables and Num type variables.
        let mut invalid_ty_vars = FxHashSet::<TypeVar>::default();
        let mut num_ty_vars = FxHashSet::<TypeVar>::default();
        for constraint in &subst_constraints {
            if let PubTypeConstraint::HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                ..
            } = constraint
            {
                assert!(!input_tys.is_empty());
                if trait_ref.module_id() == Some(STD_MODULE_ID)
                    && trait_ref.name == ustr(NUM_TRAIT_NAME)
                {
                    let maybe_ty_var = input_tys[0].data().as_variable().cloned();
                    if let Some(ty_var) = maybe_ty_var {
                        num_ty_vars.insert(ty_var);
                    }
                }
                let input_ty_vars: FxHashSet<_> =
                    input_tys.iter().flat_map(|ty| ty.inner_ty_vars()).collect();
                invalid_ty_vars.extend(
                    output_tys
                        .iter()
                        .flat_map(|ty| ty.inner_ty_vars())
                        .filter(|ty_var| !input_ty_vars.contains(ty_var)),
                );
            } else if !constraint.is_type_has_variant() {
                invalid_ty_vars.extend(constraint.inner_ty_vars());
            }
        }

        // Determine defaults for Num-constrained type variables.
        let mut defaulted_ty_vars = FxHashMap::<TypeVar, usize>::default();
        for constraint in &subst_constraints {
            if let PubTypeConstraint::HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                ..
            } = constraint
            {
                if input_tys.len() > 1 || !output_tys.is_empty() {
                    continue;
                }
                let maybe_ty_var = input_tys[0].data().as_variable().cloned();
                if let Some(ty_var) = maybe_ty_var {
                    if invalid_ty_vars.contains(&ty_var) {
                        continue;
                    }
                    if !num_ty_vars.contains(&ty_var) {
                        continue;
                    }
                    let mut default_index = defaulted_ty_vars.get(&ty_var).copied().unwrap_or(0);
                    while default_index < default_tys.len() {
                        let key = ConcreteTraitImplKey::new(
                            trait_ref.clone(),
                            vec![default_tys[default_index]],
                        );
                        if trait_solver.has_concrete_impl(&key) {
                            break;
                        }
                        default_index += 1;
                    }
                    defaulted_ty_vars.insert(ty_var, default_index);
                }
            }
        }

        if defaulted_ty_vars.is_empty() {
            return Ok(());
        }

        // Unify each defaulted variable with its default type.
        let span = constraints[0].use_site();
        for (ty_var, default_index) in &defaulted_ty_vars {
            if let Some(default_ty) = default_tys.get(*default_index) {
                let current = self.lookup_type_var(*ty_var);
                if current.data().as_variable().is_some() {
                    self.unify_same_type(Type::variable(*ty_var), span, *default_ty, span)?;
                }
            }
        }
        Ok(())
    }

    /// Default naked orphan trait inputs to unit when they can be satisfied that way.
    /// This is a narrow fallback for cases like `s(None)`, where a unit variant constructor
    /// leaves only a trait constraint like `A: Value` after variant information is otherwise gone.
    pub fn default_naked_trait_inputs_to_unit(
        &mut self,
        constraints: &[PubTypeConstraint],
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<bool, InternalCompilationError> {
        let constraints = self.substitute_in_constraints(constraints);
        let mut candidate_ty_vars = FxHashSet::<TypeVar>::default();

        for constraint in &constraints {
            let PubTypeConstraint::HaveTrait { input_tys, .. } = constraint else {
                continue;
            };
            for input_ty in input_tys {
                if let Some(ty_var) = input_ty.data().as_variable().copied() {
                    candidate_ty_vars.insert(ty_var);
                }
            }
        }

        let mut progress = false;
        for ty_var in candidate_ty_vars {
            if self.lookup_type_var(ty_var).data().as_variable().is_none() {
                continue;
            }

            let mut valid_candidate = false;
            let mut all_satisfied = true;
            let trial_subst: InstSubstitution = (
                FxHashMap::from_iter([(ty_var, Type::unit())]),
                FxHashMap::default(),
            );

            for constraint in &constraints {
                if !constraint.contains_any_type_var(ty_var) {
                    continue;
                }

                let PubTypeConstraint::HaveTrait {
                    trait_ref,
                    input_tys,
                    output_tys,
                    span,
                } = constraint
                else {
                    all_satisfied = false;
                    break;
                };

                let occurs_naked_in_inputs = input_tys.iter().any(|input_ty| {
                    input_ty
                        .data()
                        .as_variable()
                        .is_some_and(|current| *current == ty_var)
                });
                let occurs_nested_elsewhere = input_tys.iter().any(|input_ty| {
                    input_ty.contains_any_type_var(ty_var)
                        && input_ty
                            .data()
                            .as_variable()
                            .is_none_or(|current| *current != ty_var)
                }) || output_tys
                    .iter()
                    .any(|output_ty| output_ty.contains_any_type_var(ty_var));
                if !occurs_naked_in_inputs || occurs_nested_elsewhere {
                    all_satisfied = false;
                    break;
                }

                valid_candidate = true;
                let inst_input_tys = input_tys
                    .iter()
                    .map(|input_ty| input_ty.instantiate(&trial_subst))
                    .collect::<Vec<_>>();
                if inst_input_tys.iter().all(Type::is_constant)
                    && trait_solver
                        .solve_impl(trait_ref, &inst_input_tys, span.use_site, arena)
                        .is_err()
                {
                    all_satisfied = false;
                    break;
                }
            }

            if valid_candidate && all_satisfied {
                let span = constraints
                    .iter()
                    .find(|constraint| constraint.contains_any_type_var(ty_var))
                    .expect("candidate type variable must appear in constraints")
                    .use_site();
                self.unify_same_type(Type::variable(ty_var), span, Type::unit(), span)?;
                progress = true;
            }
        }

        Ok(progress)
    }

    /// For expressions, try to default remaining unconstrained type variables to int.
    /// This handles cases like `concat([], [])` where the element type has no Num constraint
    /// but can be safely defaulted to int if all trait constraints are satisfiable.
    pub fn default_unconstrained_expr_ty_vars(
        &mut self,
        expr_ty: Type,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> bool {
        use crate::std::math::int_type;

        let mut progress = false;

        // Re-substitute the expression type through current tables.
        let substituted_ty = self.substitute_in_type(expr_ty);
        let remaining_vars: Vec<TypeVar> = substituted_ty
            .inner_ty_vars()
            .into_iter()
            .filter(|v| {
                // Only consider variables that are still unresolved.
                self.lookup_type_var(*v).data().as_variable().is_some()
            })
            .collect();

        // Get current normalized constraints.
        self.normalize_remaining_constraints();
        let subst_constraints = self.remaining_constraints().to_vec();

        for ty_var in remaining_vars {
            // Only default if this variable appears in at least one remaining constraint.
            let has_constraint = subst_constraints
                .iter()
                .any(|c| c.contains_any_type_var(ty_var));
            if !has_constraint {
                continue;
            }

            // Check if all constraints mentioning this variable are satisfied with int.
            let mut all_satisfied = true;
            let trial_subst: InstSubstitution = (
                FxHashMap::from_iter([(ty_var, int_type())]),
                FxHashMap::default(),
            );
            for c in &subst_constraints {
                if !c.contains_any_type_var(ty_var) {
                    continue;
                }
                let inst_c = c.instantiate(&trial_subst);
                if let PubTypeConstraint::HaveTrait {
                    trait_ref,
                    input_tys,
                    span,
                    ..
                } = &inst_c
                {
                    if input_tys.iter().all(Type::is_constant)
                        && trait_solver
                            .solve_impl(trait_ref, input_tys, span.use_site, arena)
                            .is_err()
                    {
                        all_satisfied = false;
                        break;
                    }
                }
            }

            if all_satisfied {
                let span = subst_constraints
                    .iter()
                    .find(|c| c.contains_any_type_var(ty_var))
                    .expect("there must be a relevant constraint for expr defaulting")
                    .use_site();
                if self
                    .unify_same_type(Type::variable(ty_var), span, int_type(), span)
                    .is_ok()
                {
                    progress = true;
                }
            }
        }

        progress
    }

    fn defaulting_progress_key(
        &mut self,
        scope: &DefaultingScope,
        boundary_constraints: &[PubTypeConstraint],
    ) -> DefaultingProgressKey {
        // This intentionally tracks only coarse counts, not full semantic state.
        // This currently work because any progress will remove at least one type variable.
        let unresolved_expr_var_count = scope
            .expr_root_ty
            .map(|expr_root_ty| {
                self.substitute_in_type(expr_root_ty)
                    .inner_ty_vars()
                    .into_iter()
                    .filter(|v| self.lookup_type_var(*v).data().as_variable().is_some())
                    .count()
            })
            .unwrap_or(0);
        let boundary_constraint_var_count = boundary_constraints
            .iter()
            .map(|constraint| constraint.inner_ty_vars().len())
            .sum();
        DefaultingProgressKey {
            unresolved_expr_var_count,
            boundary_constraint_var_count,
        }
    }

    /// Repeatedly default and re-solve remaining constraints within the given
    /// boundary scope until reaching a fixed point.
    pub fn resolve_defaults_to_fixed_point(
        &mut self,
        scope: &DefaultingScope,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<(), InternalCompilationError> {
        loop {
            self.normalize_remaining_constraints();
            let boundary_constraints = scope.boundary_constraints(self.remaining_constraints());
            let old_progress_key = self.defaulting_progress_key(scope, &boundary_constraints);

            self.default_orphan_variants_in_constraints(&boundary_constraints)?;
            self.default_num_types_once(&boundary_constraints, trait_solver, arena)?;

            let remaining_constraints = self.remaining_constraints().to_vec();
            let unit_default_constraints =
                scope.unit_default_constraints(self, &remaining_constraints, &boundary_constraints);
            if !unit_default_constraints.is_empty() {
                self.default_naked_trait_inputs_to_unit(
                    &unit_default_constraints,
                    trait_solver,
                    arena,
                )?;
            }

            self.resolve_remaining_constraints_to_fixed_point(trait_solver, arena)?;
            let unconstrained_progress = scope
                .expr_root_ty
                .map(|expr_root_ty| {
                    self.default_unconstrained_expr_ty_vars(expr_root_ty, trait_solver, arena)
                })
                .unwrap_or(false);

            self.normalize_remaining_constraints();
            let boundary_constraints = scope.boundary_constraints(self.remaining_constraints());
            let new_progress_key = self.defaulting_progress_key(scope, &boundary_constraints);

            if !unconstrained_progress && new_progress_key == old_progress_key {
                break;
            }
        }

        self.normalize_remaining_constraints();

        Ok(())
    }
}
