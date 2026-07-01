use std::borrow::Cow;

use ena::unify::{InPlace, InPlaceUnificationTable, Snapshot};
use ustr::Ustr;

use crate::{
    FxHashMap, FxHashSet,
    compiler::error::{
        ADTAccessType, InfiniteTypeKind, InternalCompilationError, InvalidRecordFieldContext,
        MutabilityMustBeContext, MutabilityMustBeWhat,
    },
    hir::NodeArena,
    internal_compilation_error,
    parser::location::Location,
    std::{
        core_traits_names::{FROM_ITERATOR_TRAIT_NAME, REPR_TRAIT_NAME, VALUE_TRAIT_NAME},
        value::{
            is_function_surface_only_value_trait_application, is_value_trait_for_function_type,
        },
    },
    types::{
        effects::{EffType, EffectVar, no_effects},
        mutability::{MutType, MutVal, MutVar, MutVarKey},
        recursive_equation::{RecursiveEquationError, try_intern_recursive_equation},
        trait_solver::{ConstraintAssumptions, TraitSolver},
        r#type::{
            FnArgType, FnType, SubscriptMemberType, SubscriptResultConvention, SubscriptType,
            TyVarKey, Type, TypeInstSubst, TypeKind, TypeVar,
        },
        type_like::TypeLike,
        type_scheme::PubTypeConstraint,
    },
};

use super::{
    constraints::{EffectConstraint, MutConstraint, TypeConstraint},
    effect_solver::EffectSolver,
    expr::TypeInference,
};

/// Whether the unification should target a subtype or the same type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubOrSameType {
    SubType,
    SameTypeWithSubEffects,
}

pub(crate) struct UnifiedTypeInferenceSnapshot {
    ty_unification_table: Snapshot<InPlace<TyVarKey>>,
    mut_unification_table: Snapshot<InPlace<MutVarKey>>,
    effects: super::effect_solver::EffectSolverSnapshot,
    remaining_ty_constraints_len: usize,
}

/// The type inference after unification, with only public constraints remaining
#[derive(Default, Debug)]
pub struct UnifiedTypeInference {
    pub(super) ty_unification_table: InPlaceUnificationTable<TyVarKey>,
    /// Remaining constraints that cannot be solved, will be part of the resulting type scheme
    pub(super) remaining_ty_constraints: Vec<PubTypeConstraint>,
    pub(super) mut_unification_table: InPlaceUnificationTable<MutVarKey>,
    pub(super) effects: EffectSolver,
}

/// Canonical constraints and same-family indexes for one unification pass.
pub(super) struct ConstraintPassAggregation<'a> {
    pub(super) constraints: Vec<Cow<'a, PubTypeConstraint>>,
    tuples_at_index_is: FxHashMap<Type, FxHashMap<usize, (Type, Location)>>,
    records_field_is: FxHashMap<Type, FxHashMap<Ustr, (Type, Location)>>,
    variants_are: FxHashMap<Type, FxHashMap<Ustr, (Type, Location)>>,
}

impl ConstraintPassAggregation<'_> {
    fn with_capacity(capacity: usize) -> Self {
        Self {
            constraints: Vec::with_capacity(capacity),
            tuples_at_index_is: FxHashMap::default(),
            records_field_is: FxHashMap::default(),
            variants_are: FxHashMap::default(),
        }
    }

    pub(super) fn is_ty_adt(&self, ty: Type) -> bool {
        self.tuples_at_index_is.contains_key(&ty)
            || self.records_field_is.contains_key(&ty)
            || self.variants_are.contains_key(&ty)
    }
}

impl UnifiedTypeInference {
    pub fn new_with_ty_vars(count: u32) -> Self {
        let mut unified_ty_inf = Self::default();
        unified_ty_inf.add_ty_vars(count);
        unified_ty_inf
    }

    pub(crate) fn fresh_type_var(&mut self) -> TypeVar {
        self.ty_unification_table.new_key(None)
    }

    pub fn add_ty_vars(&mut self, count: u32) {
        for _ in 0..count {
            self.ty_unification_table.new_key(None);
        }
    }

    pub(crate) fn fresh_type_var_subst(&mut self, count: u32) -> TypeInstSubst {
        (0..count)
            .map(|old_var| (TypeVar::new(old_var), Type::variable(self.fresh_type_var())))
            .collect()
    }

    pub(crate) fn fresh_effect_var(&mut self) -> EffectVar {
        self.effects.fresh_var()
    }

    pub(crate) fn fresh_effect_var_subst(
        &mut self,
        count: u32,
    ) -> crate::types::effects::EffectsInstSubst {
        (0..count)
            .map(|old_var| {
                (
                    EffectVar::new(old_var),
                    EffType::single_variable(self.fresh_effect_var()),
                )
            })
            .collect()
    }

    /// Build a substitution mapping every effect variable occurring in the given
    /// constraints and effect types to a fresh inference effect variable.
    pub(crate) fn fresh_effect_var_subst_for(
        &mut self,
        constraints: &[PubTypeConstraint],
        effs: &[EffType],
    ) -> crate::types::effects::EffectsInstSubst {
        let mut eff_vars = FxHashSet::default();
        for constraint in constraints {
            constraint.fill_with_inner_effect_vars(&mut eff_vars);
        }
        for eff in effs {
            eff.fill_with_inner_effect_vars(&mut eff_vars);
        }
        eff_vars
            .into_iter()
            .map(|var| (var, EffType::single_variable(self.fresh_effect_var())))
            .collect()
    }

    pub(crate) fn snapshot(&mut self) -> UnifiedTypeInferenceSnapshot {
        UnifiedTypeInferenceSnapshot {
            ty_unification_table: self.ty_unification_table.snapshot(),
            mut_unification_table: self.mut_unification_table.snapshot(),
            effects: self.effects.snapshot(),
            remaining_ty_constraints_len: self.remaining_ty_constraints.len(),
        }
    }

    pub(crate) fn rollback_to(&mut self, snapshot: UnifiedTypeInferenceSnapshot) {
        self.ty_unification_table
            .rollback_to(snapshot.ty_unification_table);
        self.mut_unification_table
            .rollback_to(snapshot.mut_unification_table);
        self.effects.rollback_to(snapshot.effects);
        self.remaining_ty_constraints
            .truncate(snapshot.remaining_ty_constraints_len);
    }

    pub fn unify_type_inference(
        ty_inf: TypeInference,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Self, InternalCompilationError> {
        let TypeInference {
            ty_unification_table,
            ty_constraints,
            mut_unification_table,
            mut_constraints,
            ty_coverage_constraints,
            mut effects,
            ..
        } = ty_inf;
        let effect_constraints = effects.drain_constraints();
        let mut unified_ty_inf = UnifiedTypeInference {
            ty_unification_table,
            remaining_ty_constraints: vec![],
            mut_unification_table,
            effects,
        };
        let mut remaining_constraints = FxHashSet::default();

        // First, resolve mutability constraints.
        for constraint in mut_constraints {
            use MutConstraint::*;
            match constraint {
                SameMut {
                    current,
                    current_span,
                    expected,
                    expected_span,
                } => {
                    unified_ty_inf.unify_mut_must_be_at_least_or_equal(
                        current,
                        current_span,
                        expected,
                        expected_span,
                        MutabilityMustBeContext::Value,
                        SubOrSameType::SameTypeWithSubEffects,
                    )?;
                }
                MutBeAtLeast {
                    current,
                    current_span,
                    target,
                    reason_span,
                } => {
                    unified_ty_inf.unify_mut_must_be_at_least_or_equal(
                        current,
                        current_span,
                        target,
                        reason_span,
                        MutabilityMustBeContext::Value,
                        SubOrSameType::SubType,
                    )?;
                }
            }
        }

        // Make the remaining mutability variables constant.
        for var in 0..unified_ty_inf.mut_unification_table.len() {
            let var = MutVarKey::new(var as u32);
            if unified_ty_inf
                .mut_unification_table
                .probe_value(var)
                .is_none()
            {
                unified_ty_inf
                    .mut_unification_table
                    .unify_var_value(var, Some(MutVal::constant()))
                    .expect("Cannot unify free mutability variable");
            }
        }

        // Then, solve all type equalities.
        for constraint in ty_constraints {
            use TypeConstraint::*;
            match constraint {
                SameTypeWithSubEffects {
                    current,
                    current_span,
                    expected,
                    expected_span,
                } => unified_ty_inf.unify_same_type_with_sub_effects(
                    current,
                    current_span,
                    expected,
                    expected_span,
                )?,
                SameType {
                    current,
                    current_span,
                    expected,
                    expected_span,
                } => unified_ty_inf.unify_same_type(
                    current,
                    current_span,
                    expected,
                    expected_span,
                )?,
                SubType {
                    current,
                    current_span,
                    expected,
                    expected_span,
                } => {
                    unified_ty_inf.unify_sub_type(current, current_span, expected, expected_span)?
                }
                Pub(cst) => {
                    remaining_constraints.insert(cst);
                }
            }
        }

        // Then, solve all effect equalities.
        for constraint in effect_constraints {
            use EffectConstraint::*;
            match constraint {
                SameEffect {
                    current,
                    current_span,
                    expected,
                    expected_span,
                } => unified_ty_inf.unify_same_effect(
                    current,
                    current_span,
                    expected,
                    expected_span,
                )?,
            }
        }

        // Then, solve type coverage constraints
        for (span, ty, values) in ty_coverage_constraints {
            let ty = unified_ty_inf.normalize_type(ty);
            let all_values = ty.data().all_values().ok_or_else(|| {
                internal_compilation_error!(TypeValuesCannotBeEnumerated { span, ty })
            })?;
            let mut complete = true;
            for ty_value in all_values {
                if !values.contains(&ty_value) {
                    complete = false;
                    break;
                }
            }
            if complete {
                continue;
            }
            return Err(internal_compilation_error!(NonExhaustivePattern {
                span,
                ty
            }));
        }

        // Then, solve other constraints.
        if !remaining_constraints.is_empty() {
            let mut constraints = remaining_constraints.into_iter().collect::<Vec<_>>();
            unified_ty_inf.substitute_in_constraints_in_place(&mut constraints);
            remaining_constraints = constraints.into_iter().collect();

            loop {
                // Loop as long as we make progress.
                let old_remaining_constraints = remaining_constraints;

                // Aggregate same-family constraints and check incompatible ADT views.
                let aggregation = unified_ty_inf
                    .aggregate_constraints_for_pass(old_remaining_constraints.iter())?;

                // Perform unification.
                let constraints = aggregation
                    .constraints
                    .iter()
                    .map(|constraint| constraint.as_ref())
                    .collect::<Vec<_>>();
                let is_ty_adt = |ty| aggregation.is_ty_adt(ty);
                let mut new_constraints = unified_ty_inf.unify_constraint_pass(
                    &constraints,
                    is_ty_adt,
                    trait_solver,
                    arena,
                )?;
                unified_ty_inf.substitute_in_constraints_in_place(&mut new_constraints);
                remaining_constraints = new_constraints.into_iter().collect();

                // Break if no progress was made
                if remaining_constraints == old_remaining_constraints {
                    break;
                }
            }
        }

        // Create minimalist types for orphan variant constraints.
        // FIXME: something is missing here
        // remaining_constraints = unified_ty_inf.simplify_variant_constraints(remaining_constraints);

        // Flatten inverted effect constraints into normal constraints
        unified_ty_inf.effects.expand_pending_dependencies()?;

        // FIXME: think whether we should have an intermediate struct without the remaining_constraints in it.
        unified_ty_inf.remaining_ty_constraints = remaining_constraints.into_iter().collect();
        Ok(unified_ty_inf)
    }

    pub fn unify_fn_arg_effects(&mut self, fn_type: &FnType) {
        self.effects.unify_fn_arg_effects(fn_type);
    }

    pub fn effect_unioned(&mut self, var: EffectVar) -> Option<EffectVar> {
        self.effects.effect_unioned(var)
    }

    pub fn effect_var_root(&mut self, var: EffectVar) -> EffectVar {
        self.effects.effect_var_root(var)
    }

    pub fn unify_sub_type(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.unify_sub_or_same_type(
            current,
            current_span,
            expected,
            expected_span,
            SubOrSameType::SubType,
        )
    }

    pub fn unify_same_type_with_sub_effects(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.unify_sub_or_same_type(
            current,
            current_span,
            expected,
            expected_span,
            SubOrSameType::SameTypeWithSubEffects,
        )
    }

    fn unify_same_type(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.unify_same_type_with_sub_effects(current, current_span, expected, expected_span)?;
        self.unify_equal_callable_effects(current, current_span, expected, expected_span)
    }

    fn unify_equal_callable_effects(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.unify_equal_callable_effects_inner(
            current,
            current_span,
            expected,
            expected_span,
            &mut FxHashSet::default(),
        )
    }

    fn unify_equal_callable_effects_inner(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
        visited: &mut FxHashSet<(Type, Type)>,
    ) -> Result<(), InternalCompilationError> {
        let current_ty = self.normalize_type(current);
        let expected_ty = self.normalize_type(expected);
        if current_ty == Type::never() || expected_ty == Type::never() {
            return Ok(());
        }
        if !visited.insert((current_ty, expected_ty)) {
            return Ok(());
        }

        let current_data = current_ty.data().clone();
        let expected_data = expected_ty.data().clone();
        use TypeKind::*;
        match (current_data, expected_data) {
            (Function(current_fn), Function(expected_fn)) => {
                self.unify_same_effect(
                    current_fn.effects.clone(),
                    current_span,
                    expected_fn.effects.clone(),
                    expected_span,
                )?;
                for (current_arg, expected_arg) in current_fn.args.iter().zip(&expected_fn.args) {
                    self.unify_equal_callable_effects_inner(
                        current_arg.ty,
                        current_span,
                        expected_arg.ty,
                        expected_span,
                        visited,
                    )?;
                }
                self.unify_equal_callable_effects_inner(
                    current_fn.ret,
                    current_span,
                    expected_fn.ret,
                    expected_span,
                    visited,
                )
            }
            (Subscript(current_subscript), Subscript(expected_subscript)) => {
                self.unify_equal_subscript_member_effects(
                    current_subscript.ref_member.as_ref(),
                    current_span,
                    expected_subscript.ref_member.as_ref(),
                    expected_span,
                )?;
                self.unify_equal_subscript_member_effects(
                    current_subscript.mut_member.as_ref(),
                    current_span,
                    expected_subscript.mut_member.as_ref(),
                    expected_span,
                )?;
                for (current_arg, expected_arg) in
                    current_subscript.args.iter().zip(&expected_subscript.args)
                {
                    self.unify_equal_callable_effects_inner(
                        current_arg.ty,
                        current_span,
                        expected_arg.ty,
                        expected_span,
                        visited,
                    )?;
                }
                self.unify_equal_callable_effects_inner(
                    current_subscript.ret,
                    current_span,
                    expected_subscript.ret,
                    expected_span,
                    visited,
                )
            }
            (Tuple(current_items), Tuple(expected_items)) => {
                for (current_item, expected_item) in current_items.into_iter().zip(expected_items) {
                    self.unify_equal_callable_effects_inner(
                        current_item,
                        current_span,
                        expected_item,
                        expected_span,
                        visited,
                    )?;
                }
                Ok(())
            }
            (Record(current_fields), Record(expected_fields)) => {
                for ((_, current_field), (_, expected_field)) in
                    current_fields.into_iter().zip(expected_fields)
                {
                    self.unify_equal_callable_effects_inner(
                        current_field,
                        current_span,
                        expected_field,
                        expected_span,
                        visited,
                    )?;
                }
                Ok(())
            }
            (Variant(current_variants), Variant(expected_variants)) => {
                for ((_, current_payload), (_, expected_payload)) in
                    current_variants.into_iter().zip(expected_variants)
                {
                    self.unify_equal_callable_effects_inner(
                        current_payload,
                        current_span,
                        expected_payload,
                        expected_span,
                        visited,
                    )?;
                }
                Ok(())
            }
            (Named(current_named), Named(expected_named)) => {
                for (current_param, expected_param) in
                    current_named.params.into_iter().zip(expected_named.params)
                {
                    self.unify_equal_callable_effects_inner(
                        current_param,
                        current_span,
                        expected_param,
                        expected_span,
                        visited,
                    )?;
                }
                for (current_effect, expected_effect) in current_named
                    .effect_params
                    .into_iter()
                    .zip(expected_named.effect_params)
                {
                    self.unify_same_effect(
                        current_effect,
                        current_span,
                        expected_effect,
                        expected_span,
                    )?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn unify_sub_or_same_type(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
        sub_or_same: SubOrSameType,
    ) -> Result<(), InternalCompilationError> {
        if current == expected {
            return Ok(());
        }
        let current_ty = self.normalize_type(current);
        let expected_ty = self.normalize_type(expected);
        if current_ty == expected_ty {
            return Ok(());
        }
        let cur_data = { current_ty.data().clone() };
        let exp_data = { expected_ty.data().clone() };
        use SubOrSameType::*;
        use TypeKind::*;
        match (cur_data, exp_data) {
            (Never, _) => Ok(()),
            (_, Never) => Ok(()),
            (Variable(cur), Variable(exp)) => self
                .ty_unification_table
                .unify_var_var(cur, exp)
                .map_err(|_| {
                    internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same: SameTypeWithSubEffects,
                    })
                }),
            (Variable(var), _) => {
                self.unify_type_variable(var, current_span, expected_ty, expected_span)
            }
            (_, Variable(var)) => {
                self.unify_type_variable(var, expected_span, current_ty, current_span)
            }
            (Native(cur), Native(exp)) => {
                if cur.bare_ty != exp.bare_ty {
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same: SameTypeWithSubEffects,
                    }));
                }
                for (cur_arg_ty, exp_arg_ty) in cur.arguments.into_iter().zip(exp.arguments) {
                    self.unify_sub_or_same_type(
                        cur_arg_ty,
                        current_span,
                        exp_arg_ty,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                Ok(())
            }
            (Variant(cur), Variant(exp)) => {
                if cur.len() != exp.len() {
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same,
                    }));
                }
                for (cur_variant, exp_variant) in cur.into_iter().zip(exp) {
                    if cur_variant.0 != exp_variant.0 {
                        return Err(internal_compilation_error!(TypeMismatch {
                            current_ty,
                            current_span,
                            expected_ty,
                            expected_span,
                            sub_or_same,
                        }));
                    }
                    self.unify_sub_or_same_type(
                        cur_variant.1,
                        current_span,
                        exp_variant.1,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                Ok(())
            }
            (Tuple(cur), Tuple(exp)) => {
                if cur.len() != exp.len() {
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same,
                    }));
                }
                for (cur_el_ty, exp_el_ty) in cur.into_iter().zip(exp) {
                    self.unify_sub_or_same_type(
                        cur_el_ty,
                        current_span,
                        exp_el_ty,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                Ok(())
            }
            (Record(cur), Record(exp)) => {
                for (cur_field, exp_field) in cur.into_iter().zip(exp) {
                    if cur_field.0 != exp_field.0 {
                        return Err(internal_compilation_error!(TypeMismatch {
                            current_ty,
                            current_span,
                            expected_ty,
                            expected_span,
                            sub_or_same,
                        }));
                    }
                    self.unify_sub_or_same_type(
                        cur_field.1,
                        current_span,
                        exp_field.1,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                Ok(())
            }
            (Function(cur), Function(exp)) => {
                if cur.args.len() != exp.args.len() {
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same,
                    }));
                }
                for ((index, cur_arg), exp_arg) in cur.args.iter().enumerate().zip(exp.args.iter())
                {
                    // Contravariance of argument types.
                    self.unify_mut_must_be_at_least_or_equal(
                        exp_arg.mut_ty,
                        current_span,
                        cur_arg.mut_ty,
                        expected_span,
                        MutabilityMustBeContext::FnTypeArg(index),
                        sub_or_same,
                    )?;
                    self.unify_sub_or_same_type(
                        exp_arg.ty,
                        current_span,
                        cur_arg.ty,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                // Covariant effects.
                self.add_effect_dep(&cur.effects, current_span, &exp.effects, expected_span)?;
                // Covariance of return type.
                self.unify_sub_or_same_type(
                    cur.ret,
                    current_span,
                    exp.ret,
                    expected_span,
                    sub_or_same,
                )
            }
            (Subscript(cur), Subscript(exp)) => {
                if cur.args.len() != exp.args.len() || !cur.can_satisfy_members(&exp) {
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same,
                    }));
                }
                for ((index, cur_arg), exp_arg) in cur.args.iter().enumerate().zip(exp.args.iter())
                {
                    // Contravariance of argument types.
                    self.unify_mut_must_be_at_least_or_equal(
                        exp_arg.mut_ty,
                        current_span,
                        cur_arg.mut_ty,
                        expected_span,
                        MutabilityMustBeContext::FnTypeArg(index),
                        sub_or_same,
                    )?;
                    self.unify_sub_or_same_type(
                        exp_arg.ty,
                        current_span,
                        cur_arg.ty,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                self.add_subscript_member_effect_dep(
                    cur.ref_member.as_ref(),
                    current_span,
                    exp.ref_member.as_ref(),
                    expected_span,
                )?;
                self.add_subscript_member_effect_dep(
                    cur.mut_member.as_ref(),
                    current_span,
                    exp.mut_member.as_ref(),
                    expected_span,
                )?;
                // Covariance of return type.
                self.unify_sub_or_same_type(
                    cur.ret,
                    current_span,
                    exp.ret,
                    expected_span,
                    sub_or_same,
                )
            }
            (Named(cur), Named(exp)) => {
                if cur.def != exp.def {
                    return Err(internal_compilation_error!(NamedTypeMismatch {
                        current_decl: cur.def,
                        current_span,
                        expected_decl: exp.def,
                        expected_span,
                    }));
                }
                assert_eq!(
                    cur.params.len(),
                    exp.params.len(),
                    "A Named type must have the same number of arguments for all its instances"
                );
                for (cur_el_ty, exp_el_ty) in cur.params.into_iter().zip(exp.params) {
                    self.unify_sub_or_same_type(
                        cur_el_ty,
                        current_span,
                        exp_el_ty,
                        expected_span,
                        sub_or_same,
                    )?;
                }
                assert_eq!(
                    cur.effect_params.len(),
                    exp.effect_params.len(),
                    "A Named type must have the same number of effect arguments for all its instances"
                );
                for (cur_eff, exp_eff) in cur.effect_params.into_iter().zip(exp.effect_params) {
                    self.unify_same_effect(cur_eff, current_span, exp_eff, expected_span)?;
                }
                Ok(())
            }
            _ => Err(internal_compilation_error!(TypeMismatch {
                current_ty,
                current_span,
                expected_ty,
                expected_span,
                sub_or_same: SameTypeWithSubEffects,
            })),
        }
    }

    fn unify_type_variable(
        &mut self,
        var: TypeVar,
        var_span: Location,
        ty: Type,
        ty_span: Location,
    ) -> Result<(), InternalCompilationError> {
        let ty = if ty.contains_any_type_var(var) {
            // A recursive type equation: intern it as a recursive type when it
            // satisfies the same rules as declared recursive types; otherwise
            // it denotes an infinite type.
            try_intern_recursive_equation(var, ty).map_err(|error| {
                let kind = match error {
                    RecursiveEquationError::UnguardedCycle => {
                        InfiniteTypeKind::TypeVariableCycle { ty_var: var, ty }
                    }
                    RecursiveEquationError::NoTerminatingPayload => {
                        InfiniteTypeKind::TypeVariableSumCycleWithoutTerminatingVariant {
                            ty_var: var,
                            ty,
                        }
                    }
                };
                internal_compilation_error!(InfiniteType {
                    kind,
                    span: ty_span
                })
            })?
        } else {
            // If the type is a first-class callable-like type with concrete effects,
            // we need to generalize those effects to preserve effect polymorphism.
            // Otherwise, the concrete effects would be "baked in" and the value
            // couldn't contribute its effect variable to the parent function.
            self.generalize_effectful_callable_type(ty)
        };
        self.ty_unification_table
            .unify_var_value(var, Some(ty))
            .map_err(|(l, r)| {
                internal_compilation_error!(TypeMismatch {
                    current_ty: l,
                    current_span: var_span,
                    expected_ty: r,
                    expected_span: ty_span,
                    sub_or_same: SubOrSameType::SameTypeWithSubEffects
                })
            })
    }

    fn generalize_effectful_callable_type(&mut self, ty: Type) -> Type {
        self.effects.generalize_effectful_callable_type(ty)
    }

    fn unify_tuple_project(
        &mut self,
        tuple_ty: Type,
        tuple_span: Location,
        index: usize,
        index_span: Location,
        element_ty: Type,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let tuple_ty = self.normalize_type(tuple_ty);
        let element_ty = self.normalize_type(element_ty);
        let tuple_data = { tuple_ty.data().clone() };
        match tuple_data {
            // A type variable may or may not be a tuple, defer the unification
            TypeKind::Variable(_) => Ok(Some(PubTypeConstraint::new_tuple_at_index_is(
                tuple_ty, tuple_span, index, index_span, element_ty,
            ))),
            // A tuple, verify length and element type
            TypeKind::Tuple(tys) => {
                if let Some(ty) = tys.get(index) {
                    self.unify_same_type_with_sub_effects(*ty, tuple_span, element_ty, index_span)?;
                    Ok(None)
                } else {
                    Err(internal_compilation_error!(InvalidTupleIndex {
                        index,
                        index_span,
                        tuple_length: tys.len(),
                        tuple_span,
                    }))
                }
            }
            // Not a tuple, error
            _ => Err(internal_compilation_error!(InvalidTupleProjection {
                expr_ty: tuple_ty,
                expr_span: tuple_span,
                index_span,
            })),
        }
    }

    fn structural_projection_subscript_type(
        &mut self,
        receiver_ty: Type,
        receiver_span: Location,
        field: Ustr,
        field_span: Location,
        ctx: InvalidRecordFieldContext,
        trait_solver: &mut TraitSolver<'_>,
    ) -> Result<Option<SubscriptType>, InternalCompilationError> {
        let receiver_ty = self.normalize_type(receiver_ty);
        let receiver_data = receiver_ty.data().clone();
        let field_ty = match receiver_data {
            TypeKind::Variable(_) => return Ok(None),
            TypeKind::Record(record) => record
                .iter()
                .find_map(|(name, ty)| (*name == field).then_some(*ty))
                .ok_or_else(|| {
                    internal_compilation_error!(InvalidRecordField {
                        field_span,
                        record_ty: receiver_ty,
                        record_span: receiver_span,
                        ctx: InvalidRecordFieldContext::StructuralField,
                    })
                })?,
            TypeKind::Named(named) => {
                trait_solver.reject_inaccessible_private_repr(named.def, field_span)?;
                let shape = trait_solver
                    .type_def(named.def)
                    .instantiated_shape_with_effects(&named.params, &named.effect_params);
                let shape_data = shape.data();
                shape_data
                    .as_record()
                    .and_then(|record| {
                        record
                            .iter()
                            .find_map(|(name, ty)| (*name == field).then_some(*ty))
                    })
                    .ok_or_else(|| {
                        internal_compilation_error!(InvalidRecordField {
                            field_span,
                            record_ty: receiver_ty,
                            record_span: receiver_span,
                            ctx,
                        })
                    })?
            }
            _ => {
                return Err(internal_compilation_error!(InvalidRecordFieldAccess {
                    record_ty: receiver_ty,
                    record_span: receiver_span,
                    field_span,
                    ctx,
                }));
            }
        };
        let member =
            SubscriptMemberType::new(no_effects(), SubscriptResultConvention::AddressorPlace);
        Ok(Some(SubscriptType::new(
            vec![FnArgType::new_by_val(receiver_ty)],
            field_ty,
            Some(member.clone()),
            Some(member),
        )))
    }

    fn unify_type_has_variant(
        &mut self,
        ty: Type,
        variant_span: Location,
        tag: Ustr,
        payload_ty: Type,
        payload_span: Location,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let ty = self.normalize_type(ty);
        let payload_ty = self.normalize_type(payload_ty);
        let data = { ty.data().clone() };
        match data {
            // A type variable may or may not be a variant, defer the unification
            TypeKind::Variable(_) => Ok(Some(PubTypeConstraint::new_type_has_variant(
                ty,
                variant_span,
                tag,
                payload_ty,
                payload_span,
            ))),
            // A variant, verify payload type
            TypeKind::Variant(variants) => {
                if let Some(ty) = variants
                    .iter()
                    .find_map(|(name, ty)| if *name == tag { Some(ty) } else { None })
                {
                    self.unify_same_type_with_sub_effects(
                        *ty,
                        payload_span,
                        payload_ty,
                        payload_span,
                    )?;
                    Ok(None)
                } else {
                    Err(internal_compilation_error!(InvalidVariantName {
                        name: payload_span,
                        ty,
                        valid: ()
                    }))
                }
            }
            // Not a variant, error
            _ => Err(internal_compilation_error!(InvalidVariantType {
                name: payload_span,
                ty,
            })),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn unify_have_trait(
        &mut self,
        trait_id: crate::module::TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        span: Location,
        assumptions: ConstraintAssumptions<'_>,
        is_ty_adt: impl Fn(Type) -> bool,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let mut input_tys = self.normalize_types(input_tys);
        let mut output_tys = self.normalize_types(output_tys);
        let mut output_effs = self.substitute_in_effect_types(output_effs);
        let repr_trait_id = trait_solver.std_trait_id(REPR_TRAIT_NAME);

        // Look for the special case of a Repr trait constraint where the target
        // is either definitely not a named type or is a tuple, a record or a variant.
        // This is needed to avoid creating functions where tuples and records would
        // unify indirectly through the Repr constraint, which could never be instantiated.
        if trait_id == repr_trait_id {
            let input_ty = input_tys[0];
            let ty_data = input_ty.data();
            let is_known_non_named_ty = !ty_data.is_named() && !ty_data.is_variable();
            let unify_to_ty = if ty_data.is_named() {
                let named = ty_data.as_named().unwrap().clone();
                drop(ty_data);
                trait_solver.reject_inaccessible_private_repr(named.def, span)?;
                Some(
                    trait_solver
                        .type_def(named.def)
                        .instantiated_shape_with_effects(&named.params, &named.effect_params),
                )
            } else if is_known_non_named_ty || is_ty_adt(input_ty) {
                drop(ty_data);
                Some(input_ty)
            } else {
                drop(ty_data);
                None
            };
            if let Some(unify_to_ty) = unify_to_ty {
                self.unify_same_type_with_sub_effects(unify_to_ty, span, output_tys[0], span)?;
                return Ok(None);
            }
        }

        // Normal case.
        // Is the trait fully resolved?
        let resolved = input_tys.iter().all(|ty| ty.is_trait_input_resolved());
        Ok(if resolved {
            let trait_def = trait_solver.trait_def(trait_id);
            if output_tys.is_empty()
                && output_effs.is_empty()
                && (is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &output_tys)
                    || is_function_surface_only_value_trait_application(
                        trait_id,
                        trait_def,
                        &input_tys,
                        &output_tys,
                    ))
            {
                return Ok(None);
            }
            // Fully resolved, validate the trait implementation.
            let (impl_output_tys, impl_output_effs) = trait_solver.solve_application_outputs(
                trait_id,
                &input_tys,
                &output_tys,
                &output_effs,
                span,
                arena,
            )?;
            // Found, unify the output types and resolve the output effects.
            assert_eq!(output_tys.len(), impl_output_tys.len());
            for (cur_ty, exp_ty) in output_tys.iter().zip(impl_output_tys.iter()) {
                self.unify_same_type_with_sub_effects(*cur_ty, span, *exp_ty, span)?;
            }
            assert_eq!(output_effs.len(), impl_output_effs.len());
            for (cur_eff, exp_eff) in output_effs.iter().zip(impl_output_effs.iter()) {
                self.resolve_trait_output_effect(cur_eff, exp_eff, span)?;
            }
            None
        } else {
            // Partially resolved, we can progress a bit.
            if TraitSolver::input_tys_can_drive_improvement(&input_tys) {
                let _ = trait_solver.try_improve_trait_application(
                    self,
                    trait_id,
                    &input_tys,
                    Some(&output_tys),
                    Some(&output_effs),
                    assumptions,
                    span,
                    arena,
                )?;
                self.normalize_types_in_place(&mut input_tys);
                self.normalize_types_in_place(&mut output_tys);
                self.substitute_in_effect_types_in_place(&mut output_effs);
            }
            if input_tys.iter().all(|ty| ty.is_trait_input_resolved()) {
                let (impl_output_tys, impl_output_effs) = trait_solver.solve_application_outputs(
                    trait_id,
                    &input_tys,
                    &output_tys,
                    &output_effs,
                    span,
                    arena,
                )?;
                assert_eq!(output_tys.len(), impl_output_tys.len());
                for (cur_ty, exp_ty) in output_tys.iter().zip(impl_output_tys.iter()) {
                    self.unify_same_type_with_sub_effects(*cur_ty, span, *exp_ty, span)?;
                }
                assert_eq!(output_effs.len(), impl_output_effs.len());
                for (cur_eff, exp_eff) in output_effs.iter().zip(impl_output_effs.iter()) {
                    self.resolve_trait_output_effect(cur_eff, exp_eff, span)?;
                }
                None
            } else {
                // Not fully resolved, defer the unification.
                Some(PubTypeConstraint::new_have_trait(
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                    span,
                ))
            }
        })
    }

    pub(super) fn unify_constraint_pass(
        &mut self,
        constraints: &[&PubTypeConstraint],
        is_ty_adt: impl Fn(Type) -> bool,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Vec<PubTypeConstraint>, InternalCompilationError> {
        let mut new_constraints = Vec::with_capacity(constraints.len());
        let mut ordered_constraints = constraints.iter().copied().enumerate().collect::<Vec<_>>();
        ordered_constraints
            .sort_by_key(|(_, constraint)| constraint_solve_priority(constraint, trait_solver));
        for (constraint_index, constraint) in ordered_constraints {
            let unified_constraint = self.unify_pub_constraint(
                constraint,
                ConstraintAssumptions::excluding(constraints, constraint_index),
                &is_ty_adt,
                trait_solver,
                arena,
            )?;
            if let Some(new_constraint) = unified_constraint {
                new_constraints.push(new_constraint);
            }
        }
        Ok(new_constraints)
    }

    /// Aggregate same-family public constraints before running one unification pass.
    pub(super) fn aggregate_constraints_for_pass<'a>(
        &mut self,
        constraints: impl IntoIterator<Item = &'a PubTypeConstraint>,
    ) -> Result<ConstraintPassAggregation<'a>, InternalCompilationError> {
        let constraints = constraints.into_iter();
        let mut aggregation = ConstraintPassAggregation::with_capacity(constraints.size_hint().0);
        let mut projection_indices = FxHashMap::<(Type, Ustr), usize>::default();
        type HaveTraitOutputs = (Vec<Type>, Vec<EffType>, Location);
        let mut have_traits: FxHashMap<(crate::module::TraitId, Vec<Type>), HaveTraitOutputs> =
            FxHashMap::default();

        for constraint in constraints {
            use PubTypeConstraint::*;
            match constraint {
                TupleAtIndexIs {
                    tuple_ty,
                    tuple_span,
                    index,
                    index_span,
                    element_ty,
                } => {
                    let tuple_ty = self.normalize_type(*tuple_ty);
                    let element_ty = self.normalize_type(*element_ty);
                    // tuple_span and index_span *must* originate from the same module
                    let span = Location::fuse([tuple_span.use_site, index_span.use_site]).unwrap();
                    if let Some(variant) = aggregation.variants_are.get(&tuple_ty) {
                        let variant_span = variant.iter().next().unwrap().1.1;
                        return Err(InternalCompilationError::new_inconsistent_adt(
                            ADTAccessType::Variant,
                            variant_span,
                            ADTAccessType::TupleProject,
                            span,
                        ));
                    } else if let Some(record) = aggregation.records_field_is.get(&tuple_ty) {
                        let record_span = record.iter().next().unwrap().1.1;
                        return Err(InternalCompilationError::new_inconsistent_adt(
                            ADTAccessType::RecordAccess,
                            record_span,
                            ADTAccessType::TupleProject,
                            span,
                        ));
                    } else if let Some(tuple) = aggregation.tuples_at_index_is.get_mut(&tuple_ty) {
                        if let Some((expected_ty, expected_span)) = tuple.get(index) {
                            self.unify_same_type_with_sub_effects(
                                element_ty,
                                span,
                                *expected_ty,
                                *expected_span,
                            )?;
                        } else {
                            tuple.insert(*index, (element_ty, span));
                        }
                    } else {
                        let tuple = FxHashMap::from_iter([(*index, (element_ty, span))]);
                        aggregation.tuples_at_index_is.insert(tuple_ty, tuple);
                    }
                    aggregation.constraints.push(Cow::Borrowed(constraint));
                }
                ProjectionSubscriptIs {
                    requirement,
                    receiver_span,
                    field,
                    field_span,
                    subscript_ty,
                } => {
                    let mut subscript_ty = subscript_ty.clone();
                    self.substitute_in_subscript_type_in_place(&mut subscript_ty);
                    let receiver_ty = self.normalize_type(subscript_ty.receiver_ty());
                    let element_ty = self.normalize_type(subscript_ty.ret);
                    let span = field_span.use_site;
                    if let Some(variant) = aggregation.variants_are.get(&receiver_ty) {
                        let variant_span = variant.iter().next().unwrap().1.1;
                        return Err(InternalCompilationError::new_inconsistent_adt(
                            ADTAccessType::Variant,
                            variant_span,
                            ADTAccessType::RecordAccess,
                            span,
                        ));
                    } else if let Some(tuple) = aggregation.tuples_at_index_is.get(&receiver_ty) {
                        let tuple_span = tuple.iter().next().unwrap().1.1;
                        return Err(InternalCompilationError::new_inconsistent_adt(
                            ADTAccessType::TupleProject,
                            tuple_span,
                            ADTAccessType::RecordAccess,
                            span,
                        ));
                    } else if let Some(record) = aggregation.records_field_is.get_mut(&receiver_ty)
                    {
                        if let Some((expected_ty, expected_span)) = record.get(field) {
                            self.unify_same_type_with_sub_effects(
                                element_ty,
                                span,
                                *expected_ty,
                                *expected_span,
                            )?;
                        } else {
                            record.insert(*field, (element_ty, span));
                        }
                    } else {
                        let record = FxHashMap::from_iter([(*field, (element_ty, span))]);
                        aggregation.records_field_is.insert(receiver_ty, record);
                    }

                    let key = (receiver_ty, *field);
                    let Some(&existing_index) = projection_indices.get(&key) else {
                        projection_indices.insert(key, aggregation.constraints.len());
                        aggregation.constraints.push(Cow::Owned(
                            PubTypeConstraint::ProjectionSubscriptIs {
                                requirement: *requirement,
                                receiver_span: receiver_span.clone(),
                                field: *field,
                                field_span: field_span.clone(),
                                subscript_ty,
                            },
                        ));
                        continue;
                    };

                    let PubTypeConstraint::ProjectionSubscriptIs {
                        receiver_span: existing_receiver_span,
                        field_span: existing_field_span,
                        subscript_ty: existing_subscript_ty,
                        ..
                    } = aggregation.constraints[existing_index].as_ref()
                    else {
                        unreachable!("projection index should reference a projection constraint");
                    };
                    let existing_receiver_span = existing_receiver_span.use_site;
                    let existing_field_span = existing_field_span.use_site;
                    let existing_subscript_ty = existing_subscript_ty.clone();
                    self.unify_projection_subscript_signature(
                        &existing_subscript_ty,
                        existing_receiver_span,
                        &subscript_ty,
                        receiver_span.use_site,
                    )?;
                    self.unify_projection_subscript_members(
                        &existing_subscript_ty,
                        existing_field_span,
                        &subscript_ty,
                        field_span.use_site,
                    )?;

                    let PubTypeConstraint::ProjectionSubscriptIs {
                        requirement: existing_requirement,
                        subscript_ty: existing_subscript_ty,
                        ..
                    } = aggregation.constraints[existing_index].to_mut()
                    else {
                        unreachable!("projection index should reference a projection constraint");
                    };
                    *existing_requirement = existing_requirement.merge(*requirement);
                    merge_projection_subscript_member_requirements(
                        existing_subscript_ty,
                        subscript_ty,
                    );
                }
                TypeHasVariant {
                    variant_ty,
                    variant_span,
                    tag,
                    payload_ty,
                    payload_span,
                } => {
                    let variant_ty = self.normalize_type(*variant_ty);
                    let payload_ty = self.normalize_type(*payload_ty);
                    // We observed that sometimes variant_span and payload_span come from different modules.
                    // So we just use variant_span here.
                    let span = variant_span.use_site;
                    if let Some(tuple) = aggregation.tuples_at_index_is.get(&variant_ty) {
                        let index_span = tuple.iter().next().unwrap().1.1;
                        return Err(InternalCompilationError::new_inconsistent_adt(
                            ADTAccessType::TupleProject,
                            index_span,
                            ADTAccessType::Variant,
                            span,
                        ));
                    } else if let Some(record) = aggregation.records_field_is.get(&variant_ty) {
                        let record_span = record.iter().next().unwrap().1.1;
                        return Err(InternalCompilationError::new_inconsistent_adt(
                            ADTAccessType::RecordAccess,
                            record_span,
                            ADTAccessType::Variant,
                            span,
                        ));
                    } else if let Some(variants) = aggregation.variants_are.get_mut(&variant_ty) {
                        if let Some((expected_ty, expected_span)) = variants.get(tag) {
                            self.unify_same_type_with_sub_effects(
                                payload_ty,
                                payload_span.use_site,
                                *expected_ty,
                                *expected_span,
                            )?;
                        } else {
                            variants.insert(*tag, (payload_ty, span));
                        }
                    } else {
                        let variant =
                            FxHashMap::from_iter([(*tag, (payload_ty, payload_span.use_site))]);
                        aggregation.variants_are.insert(variant_ty, variant);
                    }
                    aggregation.constraints.push(Cow::Borrowed(constraint));
                }
                HaveTrait {
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                    span,
                } => {
                    let input_types = self.normalize_types(input_tys);
                    let output_types = self.normalize_types(output_tys);
                    let output_effects = self.substitute_in_effect_types(output_effs);
                    let key = (*trait_id, input_types);
                    if let Some(have_trait) = have_traits.get(&key) {
                        assert_eq!(have_trait.0.len(), output_types.len());
                        for (expected, actual) in have_trait.0.iter().zip(output_types.iter()) {
                            self.unify_same_type_with_sub_effects(
                                *actual,
                                span.use_site,
                                *expected,
                                have_trait.2,
                            )?;
                        }
                        assert_eq!(have_trait.1.len(), output_effects.len());
                        for (expected, actual) in have_trait.1.iter().zip(output_effects.iter()) {
                            self.unify_same_effect(
                                actual.clone(),
                                span.use_site,
                                expected.clone(),
                                have_trait.2,
                            )?;
                        }
                    } else {
                        have_traits.insert(key, (output_types, output_effects, span.use_site));
                    }
                    aggregation.constraints.push(Cow::Borrowed(constraint));
                }
            }
        }
        Ok(aggregation)
    }

    fn unify_projection_subscript_signature(
        &mut self,
        existing: &SubscriptType,
        existing_span: Location,
        incoming: &SubscriptType,
        incoming_span: Location,
    ) -> Result<(), InternalCompilationError> {
        if existing.args.len() != incoming.args.len() {
            return Err(internal_compilation_error!(Internal {
                error: "Projection subscript constraints should have matching arity".into(),
                span: incoming_span,
            }));
        }
        for (index, (existing_arg, incoming_arg)) in
            existing.args.iter().zip(&incoming.args).enumerate()
        {
            self.unify_same_type_with_sub_effects(
                existing_arg.ty,
                existing_span,
                incoming_arg.ty,
                incoming_span,
            )?;
            self.unify_mut_must_be_at_least_or_equal(
                existing_arg.mut_ty,
                existing_span,
                incoming_arg.mut_ty,
                incoming_span,
                MutabilityMustBeContext::FnTypeArg(index),
                SubOrSameType::SameTypeWithSubEffects,
            )?;
        }
        self.unify_same_type_with_sub_effects(
            existing.ret,
            existing_span,
            incoming.ret,
            incoming_span,
        )
    }

    fn unify_projection_subscript_members(
        &mut self,
        existing: &SubscriptType,
        existing_span: Location,
        incoming: &SubscriptType,
        incoming_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.unify_projection_subscript_member(
            existing.ref_member.as_ref(),
            existing_span,
            incoming.ref_member.as_ref(),
            incoming_span,
        )?;
        self.unify_projection_subscript_member(
            existing.mut_member.as_ref(),
            existing_span,
            incoming.mut_member.as_ref(),
            incoming_span,
        )
    }

    fn unify_projection_subscript_member(
        &mut self,
        existing: Option<&SubscriptMemberType>,
        existing_span: Location,
        incoming: Option<&SubscriptMemberType>,
        incoming_span: Location,
    ) -> Result<(), InternalCompilationError> {
        let (Some(existing), Some(incoming)) = (existing, incoming) else {
            return Ok(());
        };
        self.unify_same_effect(
            existing.effects.clone(),
            existing_span,
            incoming.effects.clone(),
            incoming_span,
        )
    }

    pub(crate) fn unify_pub_constraint(
        &mut self,
        constraint: &PubTypeConstraint,
        assumptions: ConstraintAssumptions<'_>,
        is_ty_adt: impl Fn(Type) -> bool,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        if let PubTypeConstraint::HaveTrait {
            trait_id,
            input_tys,
            output_tys,
            output_effs,
            span,
        } = constraint
        {
            return self.unify_have_trait(
                *trait_id,
                input_tys,
                output_tys,
                output_effs,
                span.use_site,
                assumptions,
                is_ty_adt,
                trait_solver,
                arena,
            );
        }
        if let PubTypeConstraint::ProjectionSubscriptIs {
            requirement,
            receiver_span,
            field,
            field_span,
            subscript_ty,
        } = constraint
        {
            let mut subscript_ty = subscript_ty.clone();
            self.substitute_in_subscript_type_in_place(&mut subscript_ty);
            let receiver_ty = subscript_ty.receiver_ty();
            if matches!(&*receiver_ty.data(), TypeKind::Variable(_)) {
                return Ok(Some(PubTypeConstraint::ProjectionSubscriptIs {
                    requirement: *requirement,
                    receiver_span: receiver_span.clone(),
                    field: *field,
                    field_span: field_span.clone(),
                    subscript_ty,
                }));
            }
            let actual_subscript_ty = if requirement.accepts_user_defined_projection()
                && let Some(actual_subscript_ty) =
                    trait_solver.projection_subscript_type(receiver_ty, *field)
            {
                Some(actual_subscript_ty)
            } else {
                let ctx = if requirement.accepts_user_defined_projection() {
                    InvalidRecordFieldContext::ProjectionFallback
                } else {
                    InvalidRecordFieldContext::StructuralField
                };
                self.structural_projection_subscript_type(
                    receiver_ty,
                    receiver_span.use_site,
                    *field,
                    field_span.use_site,
                    ctx,
                    trait_solver,
                )?
            };
            let actual_subscript_ty =
                actual_subscript_ty.expect("resolved projection receiver should produce evidence");
            self.unify_sub_type(
                Type::subscript_type(actual_subscript_ty),
                receiver_span.use_site,
                Type::subscript_type(subscript_ty),
                field_span.use_site,
            )?;
            return Ok(None);
        }
        self.unify_structural_pub_constraint(constraint)
    }

    pub(crate) fn unify_structural_pub_constraint(
        &mut self,
        constraint: &PubTypeConstraint,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        use PubTypeConstraint::*;
        match constraint {
            TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => self.unify_tuple_project(
                *tuple_ty,
                tuple_span.use_site,
                *index,
                index_span.use_site,
                *element_ty,
            ),
            TypeHasVariant {
                variant_ty,
                variant_span,
                tag,
                payload_ty,
                payload_span,
            } => self.unify_type_has_variant(
                *variant_ty,
                variant_span.use_site,
                *tag,
                *payload_ty,
                payload_span.use_site,
            ),
            ProjectionSubscriptIs {
                requirement,
                receiver_span,
                field,
                field_span,
                subscript_ty,
            } => {
                let mut subscript_ty = subscript_ty.clone();
                self.substitute_in_subscript_type_in_place(&mut subscript_ty);
                let receiver_ty = subscript_ty.receiver_ty();
                if matches!(&*receiver_ty.data(), TypeKind::Variable(_)) {
                    Ok(Some(PubTypeConstraint::ProjectionSubscriptIs {
                        requirement: *requirement,
                        receiver_span: receiver_span.clone(),
                        field: *field,
                        field_span: field_span.clone(),
                        subscript_ty,
                    }))
                } else {
                    Ok(None)
                }
            }
            HaveTrait { .. } => unreachable!("trait constraints are handled by the caller"),
        }
    }

    fn unify_mut_must_be_at_least_or_equal(
        &mut self,
        current: MutType,
        current_span: Location,
        target: MutType,
        target_span: Location,
        ctx: MutabilityMustBeContext,
        sub_or_same: SubOrSameType,
    ) -> Result<(), InternalCompilationError> {
        let current_mut = self.normalize_mut_type(current);
        let target_mut = self.normalize_mut_type(target);
        // Note: here is the truth table of the constant/mutable relationship between
        // current and target, when sub_or_same is SubType:
        //            | cur cst | cur mut
        // -----------|---------|---------
        // target cst |   ok    |   ok
        // target mut |   err   |   ok
        // When it is SameTypeWithSubEffects, the table is a perfect diagonal.
        use MutType::*;
        use MutabilityMustBeWhat::*;
        match (current_mut, target_mut) {
            (Variable(current), Variable(target)) => {
                // Do unification. Fuse both variable as it is acceptable
                // due to the transitivity of the "must be at least mutability" relationship.
                self.mut_unification_table
                    .unify_var_var(current, target)
                    .map_err(|_| {
                        internal_compilation_error!(MutabilityMustBe {
                            source_span: current_span,
                            reason_span: target_span,
                            what: Equal,
                            ctx,
                        })
                    })
            }
            (Variable(current), Resolved(target)) => self.unify_mut_current_variable(
                current,
                current_span,
                target,
                target_span,
                ctx,
                sub_or_same,
            ),
            (Resolved(current), Variable(target)) => self.unify_mut_target_variable(
                current,
                current_span,
                target,
                target_span,
                ctx,
                sub_or_same,
            ),
            (Resolved(current), Resolved(target)) => {
                use SubOrSameType::*;
                if match sub_or_same {
                    // Check mutability value coercion.
                    SubType => current < target,
                    // Must be exactly the same.
                    SameTypeWithSubEffects => current != target,
                } {
                    Err(internal_compilation_error!(MutabilityMustBe {
                        source_span: current_span,
                        reason_span: target_span,
                        what: match sub_or_same {
                            SubType => Mutable,
                            SameTypeWithSubEffects => Equal,
                        },
                        ctx,
                    }))
                } else {
                    Ok(())
                }
            }
        }
    }

    pub fn unify_mut_current_variable(
        &mut self,
        current: MutVar,
        source_span: Location,
        target: MutVal,
        reason_span: Location,
        ctx: MutabilityMustBeContext,
        sub_or_same: SubOrSameType,
    ) -> Result<(), InternalCompilationError> {
        use MutabilityMustBeWhat::*;
        use SubOrSameType::*;
        match sub_or_same {
            SubType => {
                // Target is resolved, if it is constant, we are done as anything can be used as constant.
                if target == MutVal::constant() {
                    Ok(())
                } else {
                    // If it is mutable, current must be mutable as well.
                    self.mut_unification_table
                        .unify_var_value(current, Some(MutVal::mutable()))
                        .map_err(|_| {
                            internal_compilation_error!(MutabilityMustBe {
                                source_span,
                                reason_span,
                                what: Mutable,
                                ctx
                            })
                        })
                }
            }
            SameTypeWithSubEffects => self
                .mut_unification_table
                .unify_var_value(current, Some(target))
                .map_err(|_| {
                    internal_compilation_error!(MutabilityMustBe {
                        source_span,
                        reason_span,
                        what: Equal,
                        ctx
                    })
                }),
        }
    }

    pub fn unify_mut_target_variable(
        &mut self,
        current: MutVal,
        reason_span: Location,
        target: MutVar,
        source_span: Location,
        ctx: MutabilityMustBeContext,
        sub_or_same: SubOrSameType,
    ) -> Result<(), InternalCompilationError> {
        use MutabilityMustBeWhat::*;
        use SubOrSameType::*;
        match sub_or_same {
            SubType => {
                // Current is resolved, if it is mutable, we are done as it can be used for anything.
                if current == MutVal::mutable() {
                    Ok(())
                } else {
                    // If it is constant, target must be constant as well.
                    self.mut_unification_table
                        .unify_var_value(target, Some(MutVal::constant()))
                        .map_err(|_| {
                            internal_compilation_error!(MutabilityMustBe {
                                source_span,
                                reason_span,
                                what: Constant,
                                ctx
                            })
                        })
                }
            }
            SameTypeWithSubEffects => self
                .mut_unification_table
                .unify_var_value(target, Some(current))
                .map_err(|_| {
                    internal_compilation_error!(MutabilityMustBe {
                        source_span,
                        reason_span,
                        what: Equal,
                        ctx
                    })
                }),
        }
    }

    fn resolve_trait_output_effect(
        &mut self,
        constraint_eff: &EffType,
        solved_eff: &EffType,
        span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.effects
            .resolve_trait_output_effect(constraint_eff, solved_eff, span)
    }

    /// Make current and target the same effect type.
    pub fn unify_same_effect(
        &mut self,
        current: EffType,
        current_span: Location,
        target: EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.effects
            .unify_same_effect(current, current_span, target, target_span)
    }

    pub fn add_effect_dep(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.effects
            .add_effect_dep(current, current_span, target, target_span)
    }

    fn add_subscript_member_effect_dep(
        &mut self,
        current: Option<&SubscriptMemberType>,
        current_span: Location,
        target: Option<&SubscriptMemberType>,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        let Some(target) = target else {
            return Ok(());
        };
        let Some(current) = current else {
            return Ok(());
        };
        self.add_effect_dep(&current.effects, current_span, &target.effects, target_span)
    }

    fn unify_equal_subscript_member_effects(
        &mut self,
        current: Option<&SubscriptMemberType>,
        current_span: Location,
        target: Option<&SubscriptMemberType>,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        match (current, target) {
            (Some(current), Some(target)) => self.unify_same_effect(
                current.effects.clone(),
                current_span,
                target.effects.clone(),
                target_span,
            ),
            _ => Ok(()),
        }
    }

    pub fn finalize_effect_dependencies(&mut self) -> Result<(), InternalCompilationError> {
        self.effects.expand_pending_dependencies()
    }
}

fn merge_projection_subscript_member_requirements(
    existing: &mut SubscriptType,
    incoming: SubscriptType,
) {
    merge_subscript_member_requirement(&mut existing.ref_member, incoming.ref_member);
    merge_subscript_member_requirement(&mut existing.mut_member, incoming.mut_member);
}

fn merge_subscript_member_requirement(
    existing: &mut Option<SubscriptMemberType>,
    incoming: Option<SubscriptMemberType>,
) {
    match (existing, incoming) {
        (_, None) => {}
        (slot @ None, Some(incoming)) => *slot = Some(incoming),
        (Some(existing), Some(incoming)) => {
            existing.result_convention = existing.result_convention.max(incoming.result_convention);
        }
    }
}

fn constraint_solve_priority(constraint: &PubTypeConstraint, trait_solver: &TraitSolver<'_>) -> u8 {
    match constraint {
        PubTypeConstraint::TupleAtIndexIs { .. } | PubTypeConstraint::TypeHasVariant { .. } => 0,
        PubTypeConstraint::ProjectionSubscriptIs { .. } => 5,
        PubTypeConstraint::HaveTrait {
            trait_id,
            output_tys,
            output_effs,
            ..
        } if *trait_id == trait_solver.std_trait_id(REPR_TRAIT_NAME)
            || !output_tys.is_empty()
            || !output_effs.is_empty() =>
        {
            10
        }
        PubTypeConstraint::HaveTrait { trait_id, .. }
            if *trait_id == trait_solver.std_trait_id(FROM_ITERATOR_TRAIT_NAME) =>
        {
            20
        }
        PubTypeConstraint::HaveTrait { trait_id, .. }
            if *trait_id == trait_solver.std_trait_id(VALUE_TRAIT_NAME) =>
        {
            90
        }
        PubTypeConstraint::HaveTrait { .. } => 50,
    }
}
