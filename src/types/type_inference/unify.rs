use std::mem;

use ena::unify::{InPlace, InPlaceUnificationTable, Snapshot};
use ustr::Ustr;

use crate::{
    FxHashMap, FxHashSet,
    compiler::error::{
        ADTAccessType, InternalCompilationError, MutabilityMustBeContext, MutabilityMustBeWhat,
    },
    hir::NodeArena,
    internal_compilation_error,
    parser::location::Location,
    std::core::REPR_TRAIT,
    types::{
        effects::{EffType, EffectVar, EffectVarKey},
        mutability::{MutType, MutVal, MutVar, MutVarKey},
        r#trait::TraitRef,
        trait_solver::{ConstraintAssumptions, TraitSolver},
        r#type::{FnType, TyVarKey, Type, TypeKind, TypeSubstitution, TypeVar},
        type_like::TypeLike,
        type_scheme::PubTypeConstraint,
    },
};

use super::{
    constraints::{EffectConstraint, MutConstraint, TypeConstraint},
    expr::TypeInference,
};

/// Whether the unification should target a subtype or the same type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubOrSameType {
    SubType,
    SameType,
}

#[derive(Debug, Clone)]
pub(super) struct PendingEffectDependency {
    pub(super) source: EffType,
    pub(super) source_span: Location,
    pub(super) target: EffectVarKey,
    pub(super) target_span: Location,
}

pub(crate) struct UnifiedTypeInferenceSnapshot {
    ty_unification_table: Snapshot<InPlace<TyVarKey>>,
    mut_unification_table: Snapshot<InPlace<MutVarKey>>,
    effect_unification_table: Snapshot<InPlace<EffectVarKey>>,
    remaining_ty_constraints_len: usize,
    effect_constraints_inv: Vec<PendingEffectDependency>,
}

/// The type inference after unification, with only public constraints remaining
#[derive(Default, Debug)]
pub struct UnifiedTypeInference {
    pub(super) ty_unification_table: InPlaceUnificationTable<TyVarKey>,
    /// Remaining constraints that cannot be solved, will be part of the resulting type scheme
    pub(super) remaining_ty_constraints: Vec<PubTypeConstraint>,
    pub(super) mut_unification_table: InPlaceUnificationTable<MutVarKey>,
    pub(super) effect_unification_table: InPlaceUnificationTable<EffectVarKey>,
    pub(super) effect_constraints_inv: Vec<PendingEffectDependency>,
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

    pub(crate) fn fresh_type_var_subst(&mut self, count: u32) -> TypeSubstitution {
        (0..count)
            .map(|old_var| (TypeVar::new(old_var), Type::variable(self.fresh_type_var())))
            .collect()
    }

    pub(crate) fn snapshot(&mut self) -> UnifiedTypeInferenceSnapshot {
        UnifiedTypeInferenceSnapshot {
            ty_unification_table: self.ty_unification_table.snapshot(),
            mut_unification_table: self.mut_unification_table.snapshot(),
            effect_unification_table: self.effect_unification_table.snapshot(),
            remaining_ty_constraints_len: self.remaining_ty_constraints.len(),
            effect_constraints_inv: self.effect_constraints_inv.clone(),
        }
    }

    pub(crate) fn rollback_to(&mut self, snapshot: UnifiedTypeInferenceSnapshot) {
        self.ty_unification_table
            .rollback_to(snapshot.ty_unification_table);
        self.mut_unification_table
            .rollback_to(snapshot.mut_unification_table);
        self.effect_unification_table
            .rollback_to(snapshot.effect_unification_table);
        self.remaining_ty_constraints
            .truncate(snapshot.remaining_ty_constraints_len);
        self.effect_constraints_inv = snapshot.effect_constraints_inv;
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
            effect_unification_table,
            effect_constraints,
        } = ty_inf;
        let mut unified_ty_inf = UnifiedTypeInference {
            ty_unification_table,
            remaining_ty_constraints: vec![],
            mut_unification_table,
            effect_unification_table,
            effect_constraints_inv: Vec::default(),
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
                        SubOrSameType::SameType,
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
            loop {
                // Loop as long as we make progress.

                // Perform simplification for algebraic data type constraints.
                // Check for incompatible constraints as well.
                let mut tuples_at_index_is: FxHashMap<Type, FxHashMap<usize, (Type, Location)>> =
                    FxHashMap::default();
                let mut records_field_is: FxHashMap<Type, FxHashMap<Ustr, (Type, Location)>> =
                    FxHashMap::default();
                let mut variants_are: FxHashMap<Type, FxHashMap<Ustr, (Type, Location)>> =
                    FxHashMap::default();
                let mut have_traits: FxHashMap<(TraitRef, Vec<Type>), (Vec<Type>, Location)> =
                    FxHashMap::default();
                for constraint in &remaining_constraints {
                    use PubTypeConstraint::*;
                    match constraint {
                        TupleAtIndexIs {
                            tuple_ty,
                            tuple_span,
                            index,
                            index_span,
                            element_ty,
                        } => {
                            let tuple_ty = unified_ty_inf.normalize_type(*tuple_ty);
                            let element_ty = unified_ty_inf.normalize_type(*element_ty);
                            // tuple_span and index_span *must* originate from the same module
                            let span =
                                Location::fuse([tuple_span.use_site, index_span.use_site]).unwrap();
                            if let Some(variant) = variants_are.get(&tuple_ty) {
                                let variant_span = variant.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::Variant,
                                    variant_span,
                                    ADTAccessType::TupleProject,
                                    span,
                                ));
                            } else if let Some(record) = records_field_is.get(&tuple_ty) {
                                let record_span = record.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::RecordAccess,
                                    record_span,
                                    ADTAccessType::TupleProject,
                                    span,
                                ));
                            } else if let Some(tuple) = tuples_at_index_is.get_mut(&tuple_ty) {
                                if let Some((expected_ty, expected_span)) = tuple.get(index) {
                                    unified_ty_inf.unify_same_type(
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
                                tuples_at_index_is.insert(tuple_ty, tuple);
                            }
                        }
                        RecordFieldIs {
                            record_ty,
                            record_span,
                            field,
                            field_span,
                            element_ty,
                        } => {
                            let record_ty = unified_ty_inf.normalize_type(*record_ty);
                            let element_ty = unified_ty_inf.normalize_type(*element_ty);
                            // record_span and field_span *must* originate from the same module
                            let span = Location::fuse([record_span.use_site, field_span.use_site])
                                .unwrap();
                            if let Some(variant) = variants_are.get(&record_ty) {
                                let variant_span = variant.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::Variant,
                                    variant_span,
                                    ADTAccessType::TupleProject,
                                    span,
                                ));
                            } else if let Some(tuple) = tuples_at_index_is.get(&record_ty) {
                                let tuple_span = tuple.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::TupleProject,
                                    tuple_span,
                                    ADTAccessType::RecordAccess,
                                    span,
                                ));
                            } else if let Some(record) = records_field_is.get_mut(&record_ty) {
                                if let Some((expected_ty, expected_span)) = record.get(field) {
                                    unified_ty_inf.unify_same_type(
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
                                records_field_is.insert(record_ty, record);
                            }
                        }
                        TypeHasVariant {
                            variant_ty,
                            variant_span,
                            tag,
                            payload_ty,
                            payload_span,
                        } => {
                            let variant_ty = unified_ty_inf.normalize_type(*variant_ty);
                            let payload_ty = unified_ty_inf.normalize_type(*payload_ty);
                            // We observed that sometimes variant_span and payload_span come from different modules.
                            // So we just use variant_span here.
                            let span = variant_span.use_site;
                            if let Some(tuple) = tuples_at_index_is.get(&variant_ty) {
                                let index_span = tuple.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::TupleProject,
                                    index_span,
                                    ADTAccessType::Variant,
                                    span,
                                ));
                            } else if let Some(record) = records_field_is.get(&variant_ty) {
                                let record_span = record.iter().next().unwrap().1.1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::RecordAccess,
                                    record_span,
                                    ADTAccessType::Variant,
                                    span,
                                ));
                            } else if let Some(variants) = variants_are.get_mut(&variant_ty) {
                                if let Some((expected_ty, expected_span)) = variants.get(tag) {
                                    unified_ty_inf.unify_same_type(
                                        payload_ty,
                                        payload_span.use_site,
                                        *expected_ty,
                                        *expected_span,
                                    )?;
                                } else {
                                    variants.insert(*tag, (payload_ty, span));
                                }
                            } else {
                                let variant = FxHashMap::from_iter([(
                                    *tag,
                                    (payload_ty, payload_span.use_site),
                                )]);
                                variants_are.insert(variant_ty, variant);
                            }
                        }
                        HaveTrait {
                            trait_ref,
                            input_tys,
                            output_tys,
                            span,
                        } => {
                            let input_types = unified_ty_inf.normalize_types(input_tys);
                            let output_types = unified_ty_inf.normalize_types(output_tys);
                            let key = (trait_ref.clone(), input_types);
                            if let Some(have_trait) = have_traits.get(&key) {
                                assert_eq!(have_trait.0.len(), output_types.len());
                                for (expected, actual) in
                                    have_trait.0.iter().zip(output_types.iter())
                                {
                                    unified_ty_inf.unify_same_type(
                                        *actual,
                                        span.use_site,
                                        *expected,
                                        have_trait.1,
                                    )?;
                                }
                            } else {
                                have_traits.insert(key, (output_types, span.use_site));
                            }
                        }
                    }
                }

                // Perform unification.
                let constraints = remaining_constraints.into_iter().collect::<Vec<_>>();
                let old_constraint_count = constraints.len();
                let old_constraint_var_count = total_constraints_var_count(constraints.iter());
                let is_ty_adt = |ty| {
                    tuples_at_index_is.contains_key(&ty)
                        || records_field_is.contains_key(&ty)
                        || variants_are.contains_key(&ty)
                };
                remaining_constraints = unified_ty_inf
                    .unify_constraint_pass(&constraints, is_ty_adt, trait_solver, arena)?
                    .into_iter()
                    .collect();
                let new_constraint_var_count =
                    total_constraints_var_count(remaining_constraints.iter());

                // Break if no progress was made
                if remaining_constraints.len() == old_constraint_count
                    && new_constraint_var_count == old_constraint_var_count
                {
                    break;
                }
            }
        }

        // Create minimalist types for orphan variant constraints.
        // FIXME: something is missing here
        // remaining_constraints = unified_ty_inf.simplify_variant_constraints(remaining_constraints);

        // Flatten inverted effect constraints into normal constraints
        let effect_constraints_inv = mem::take(&mut unified_ty_inf.effect_constraints_inv);
        for dep in effect_constraints_inv {
            unified_ty_inf.expand_inv_effect_dep(dep)?;
        }

        // FIXME: think whether we should have an intermediate struct without the remaining_constraints in it.
        unified_ty_inf.remaining_ty_constraints = remaining_constraints.into_iter().collect();
        Ok(unified_ty_inf)
    }

    pub fn unify_fn_arg_effects(&mut self, fn_type: &FnType) {
        for arg in &fn_type.args {
            if let Some(fn_arg) = arg.ty.data().as_function() {
                let mut first_var = None;
                fn_arg.effects.iter().for_each(|eff| {
                    if let Some(var) = eff.as_variable() {
                        if let Some(first_var) = first_var {
                            self.effect_unification_table.union(first_var, *var);
                        } else {
                            first_var = Some(*var);
                        }
                    }
                });
            }
        }
    }

    pub fn effect_unioned(&mut self, var: EffectVar) -> Option<EffectVar> {
        let root = self.effect_unification_table.find(var);
        if root != var { Some(root) } else { None }
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

    pub fn unify_same_type(
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
            SubOrSameType::SameType,
        )
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
                        sub_or_same: SameType,
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
                        sub_or_same: SameType,
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
                Ok(())
            }
            _ => Err(internal_compilation_error!(TypeMismatch {
                current_ty,
                current_span,
                expected_ty,
                expected_span,
                sub_or_same: SameType,
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
        if ty.contains_any_type_var(var) {
            Err(internal_compilation_error!(InfiniteType(var, ty, ty_span)))
        } else {
            // If the type is a function type with concrete (non-variable) effects,
            // we need to generalize those effects to preserve effect polymorphism.
            // Otherwise, the concrete effects would be "baked in" and the function
            // parameter couldn't contribute its effect variable to the parent function.
            let ty = self.generalize_function_effects(ty);
            self.ty_unification_table
                .unify_var_value(var, Some(ty))
                .map_err(|(l, r)| {
                    internal_compilation_error!(TypeMismatch {
                        current_ty: l,
                        current_span: var_span,
                        expected_ty: r,
                        expected_span: ty_span,
                        sub_or_same: SubOrSameType::SameType
                    })
                })
        }
    }

    /// Generalize concrete effects in a function type to effect variables.
    /// This is needed when unifying a type variable with a function type,
    /// to preserve effect polymorphism.
    fn generalize_function_effects(&mut self, ty: Type) -> Type {
        use TypeKind::*;
        let ty_data = ty.data();
        match &*ty_data {
            Function(fn_ty) => {
                let fn_ty = fn_ty.clone();
                drop(ty_data);
                // Check if the function has any non-variable effects
                let has_primitive_effects = fn_ty.effects.iter().any(|e| e.is_primitive());
                if has_primitive_effects {
                    // Create a fresh effect variable
                    let fresh_eff_var = self.effect_unification_table.new_key(None);
                    // Add the concrete effects as dependencies to this fresh variable
                    // This is done through the inverted constraints mechanism
                    for eff in fn_ty.effects.iter() {
                        if eff.is_primitive() {
                            self.effect_constraints_inv.push(PendingEffectDependency {
                                source: EffType::single(*eff),
                                source_span: Location::new_synthesized(),
                                target: fresh_eff_var,
                                target_span: Location::new_synthesized(),
                            });
                        } else if let Some(var) = eff.as_variable() {
                            // Also union any existing effect variables
                            self.effect_unification_table.union(fresh_eff_var, *var);
                        }
                    }
                    // Create a new function type with the fresh effect variable
                    let new_fn_ty = FnType::new(
                        fn_ty.args.clone(),
                        fn_ty.ret,
                        EffType::single_variable(fresh_eff_var),
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
                    self.unify_same_type(*ty, tuple_span, element_ty, index_span)?;
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

    fn unify_record_field_access(
        &mut self,
        record_ty: Type,
        record_span: Location,
        field: Ustr,
        field_span: Location,
        element_ty: Type,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let record_ty = self.normalize_type(record_ty);
        let element_ty = self.normalize_type(element_ty);
        let record_data = { record_ty.data().clone() };
        match record_data {
            // A type variable may or may not be a tuple, defer the unification
            TypeKind::Variable(_) => Ok(Some(PubTypeConstraint::new_record_field_is(
                record_ty,
                record_span,
                field,
                field_span,
                element_ty,
            ))),
            // A record, verify element type
            TypeKind::Record(tys) => {
                if let Some(ty) = tys
                    .iter()
                    .find_map(|(name, ty)| if *name == field { Some(*ty) } else { None })
                {
                    self.unify_same_type(ty, record_span, element_ty, field_span)?;
                    Ok(None)
                } else {
                    Err(internal_compilation_error!(InvalidRecordField {
                        field_span,
                        record_ty,
                        record_span,
                    }))
                }
            }
            // Not a record, error
            _ => Err(internal_compilation_error!(InvalidRecordFieldAccess {
                record_ty,
                record_span,
                field_span,
            })),
        }
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
                    self.unify_same_type(*ty, payload_span, payload_ty, payload_span)?;
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
        trait_ref: TraitRef,
        input_tys: &[Type],
        output_tys: &[Type],
        span: Location,
        assumptions: ConstraintAssumptions<'_>,
        is_ty_adt: impl Fn(Type) -> bool,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let input_tys = self.normalize_types(input_tys);
        let output_tys = self.normalize_types(output_tys);

        // Look for the special case of a Repr trait constraint where the target
        // is either definitely not a named type or is a tuple, a record or a variant.
        // This is needed to avoid creating functions where tuples and records would
        // unify indirectly through the Repr constraint, which could never be instantiated.
        if trait_ref == *REPR_TRAIT {
            let input_ty = input_tys[0];
            let ty_data = input_ty.data();
            let is_known_non_named_ty = !ty_data.is_named() && !ty_data.is_variable();
            let unify_to_ty = if ty_data.is_named() {
                let named = ty_data.as_named().unwrap().clone();
                drop(ty_data);
                Some(named.instantiated_shape())
            } else if is_known_non_named_ty || is_ty_adt(input_ty) {
                drop(ty_data);
                Some(input_ty)
            } else {
                drop(ty_data);
                None
            };
            if let Some(unify_to_ty) = unify_to_ty {
                self.unify_same_type(unify_to_ty, span, output_tys[0], span)?;
                return Ok(None);
            }
        }

        // Normal case.
        // Is the trait fully resolved?
        let resolved = input_tys.iter().all(Type::is_constant);
        Ok(if resolved {
            // Fully resolved, validate the trait implementation.
            let impl_output_tys =
                trait_solver.solve_output_types(&trait_ref, &input_tys, span, arena)?;
            // Found, unify the output types.
            assert!(output_tys.is_empty() || output_tys.len() == impl_output_tys.len());
            for (cur_ty, exp_ty) in output_tys.iter().zip(impl_output_tys.iter()) {
                self.unify_same_type(*cur_ty, span, *exp_ty, span)?;
            }
            None
        } else {
            // Partially resolved, we can progress a bit.
            let has_structured_non_constant_input = input_tys
                .iter()
                .any(|ty| !ty.is_constant() && !ty.data().is_variable());
            if has_structured_non_constant_input {
                let _ = trait_solver.try_improve_trait_application(
                    self,
                    &trait_ref,
                    &input_tys,
                    &output_tys,
                    assumptions,
                    span,
                    arena,
                )?;
            }
            let input_tys = self.normalize_types(&input_tys);
            let output_tys = self.normalize_types(&output_tys);
            if input_tys.iter().all(Type::is_constant) {
                let impl_output_tys =
                    trait_solver.solve_output_types(&trait_ref, &input_tys, span, arena)?;
                assert!(output_tys.is_empty() || output_tys.len() == impl_output_tys.len());
                for (cur_ty, exp_ty) in output_tys.iter().zip(impl_output_tys.iter()) {
                    self.unify_same_type(*cur_ty, span, *exp_ty, span)?;
                }
                None
            } else {
                // Not fully resolved, defer the unification.
                Some(PubTypeConstraint::new_have_trait(
                    trait_ref, input_tys, output_tys, span,
                ))
            }
        })
    }

    pub(super) fn unify_constraint_pass(
        &mut self,
        constraints: &[PubTypeConstraint],
        is_ty_adt: impl Fn(Type) -> bool,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Vec<PubTypeConstraint>, InternalCompilationError> {
        let mut new_constraints = Vec::with_capacity(constraints.len());
        for (constraint_index, constraint) in constraints.iter().enumerate() {
            use PubTypeConstraint::*;
            let unified_constraint = match constraint {
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
                )?,
                RecordFieldIs {
                    record_ty,
                    record_span,
                    field,
                    field_span,
                    element_ty,
                } => self.unify_record_field_access(
                    *record_ty,
                    record_span.use_site,
                    *field,
                    field_span.use_site,
                    *element_ty,
                )?,
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
                )?,
                HaveTrait {
                    trait_ref,
                    input_tys,
                    output_tys,
                    span,
                } => self.unify_have_trait(
                    trait_ref.clone(),
                    input_tys,
                    output_tys,
                    span.use_site,
                    ConstraintAssumptions::excluding(constraints, constraint_index),
                    &is_ty_adt,
                    trait_solver,
                    arena,
                )?,
            };
            if let Some(new_constraint) = unified_constraint {
                new_constraints.push(new_constraint);
            }
        }
        Ok(new_constraints)
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
        // When it is SameType, the table is a perfect diagonal.
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
                    SameType => current != target,
                } {
                    Err(internal_compilation_error!(MutabilityMustBe {
                        source_span: current_span,
                        reason_span: target_span,
                        what: match sub_or_same {
                            SubType => Mutable,
                            SameType => Equal,
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
            SameType => self
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
            SameType => self
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

    /// Make current and target the same effect type.
    pub fn unify_same_effect(
        &mut self,
        current: EffType,
        current_span: Location,
        target: EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        let current_vars = current.inner_vars();
        let current_any_vars = !current_vars.is_empty();
        let target_vars = target.inner_vars();
        let target_any_vars = !target_vars.is_empty();
        match (current_any_vars, target_any_vars) {
            (false, false) => {
                if current == target {
                    Ok(())
                } else {
                    Err(internal_compilation_error!(InvalidEffectDependency {
                        source: current,
                        source_span: current_span,
                        target,
                        target_span,
                    }))
                }
            }
            (true, false) => {
                for var in current_vars {
                    self.effect_unification_table
                        .union_value(var, Some(target.clone()));
                }
                Ok(())
            }
            (false, true) => {
                for var in target_vars {
                    self.effect_unification_table
                        .union_value(var, Some(current.clone()));
                }
                Ok(())
            }
            (true, true) => {
                if current_vars.len() > 1 {
                    return Err(internal_compilation_error!(Unsupported {
                        span: current_span,
                        reason: "Cannot unify multiple effect variables in the source".into(),
                    }));
                }
                if target_vars.len() > 1 {
                    return Err(internal_compilation_error!(Unsupported {
                        span: target_span,
                        reason: "Cannot unify multiple effect variables in the target".into(),
                    }));
                }
                self.effect_unification_table.union_value(
                    current_vars[0],
                    Some(EffType::multiple_primitive(&target.inner_non_vars())),
                );
                self.effect_unification_table.union_value(
                    target_vars[0],
                    Some(EffType::multiple_primitive(&current.inner_non_vars())),
                );
                self.effect_unification_table
                    .unify_var_var(current_vars[0], target_vars[0])
                    .map_err(|_| {
                        internal_compilation_error!(InvalidEffectDependency {
                            source: current,
                            source_span: current_span,
                            target,
                            target_span,
                        })
                    })
            }
        }
    }

    pub fn add_effect_dep(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        if current.is_empty() || current == target {
            return Ok(());
        }
        let cur_single = current.as_single();
        let cur_var = cur_single.and_then(|eff| eff.as_variable().cloned());
        let tgt_single = target.as_single();
        let tgt_var = tgt_single.and_then(|eff| eff.as_variable().cloned());
        if let Some(var) = cur_var {
            // Left is a variable, put the effect dependency on the right.
            self.effect_unification_table
                .union_value(var, Some(target.clone()));
        } else if let Some(var) = tgt_var {
            // Right is a variable, put the effect dependency to the inverted constraints,
            // to be resolved later.
            self.effect_constraints_inv.push(PendingEffectDependency {
                source: current.clone(),
                source_span: current_span,
                target: var,
                target_span,
            });
        } else {
            return Err(internal_compilation_error!(InvalidEffectDependency {
                source: current.clone(),
                source_span: current_span,
                target: target.clone(),
                target_span,
            }));
        }
        Ok(())
    }

    fn expand_inv_effect_dep(
        &mut self,
        dep: PendingEffectDependency,
    ) -> Result<(), InternalCompilationError> {
        if let Some(existing_effects) = self.effect_unification_table.probe_value(dep.target) {
            if current_satisfied_by_target(&dep.source, &existing_effects) {
                return Ok(());
            }

            let target_vars = existing_effects.inner_vars();
            if target_vars.is_empty() {
                return Err(internal_compilation_error!(InvalidEffectDependency {
                    source: dep.source,
                    source_span: dep.source_span,
                    target: existing_effects,
                    target_span: dep.target_span,
                }));
            }

            for var in target_vars {
                self.expand_inv_effect_dep(PendingEffectDependency {
                    source: dep.source.clone(),
                    source_span: dep.source_span,
                    target: var,
                    target_span: dep.target_span,
                })?;
            }
        } else {
            self.effect_unification_table.union_value(
                dep.target,
                Some(dep.source.union(&EffType::single_variable(dep.target))),
            );
        }
        Ok(())
    }
}

pub(super) fn total_constraints_var_count<'a>(
    constraints: impl IntoIterator<Item = &'a PubTypeConstraint>,
) -> usize {
    constraints
        .into_iter()
        .map(|constraint| constraint.inner_ty_vars().len())
        .sum()
}

fn current_satisfied_by_target(current: &EffType, target: &EffType) -> bool {
    // A pending dependency is already satisfied if the target contains all currently required
    // primitive effects. Any target-side variables can still absorb the remaining uncertainty.
    let target_primitives = EffType::multiple_primitive(&target.inner_non_vars());
    current.is_subset_of(&target_primitives)
}
