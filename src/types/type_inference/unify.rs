// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{
    borrow::Cow,
    mem,
    ops::{Deref, DerefMut},
};

use ena::unify::{InPlace, InPlaceUnificationTable, Snapshot};
use ustr::Ustr;

use super::{
    constraints::{EffectConstraint, MutConstraint, TypeConstraint},
    effect_solver::{EffectSolver, EffectSolverSnapshot},
    evidence_uses::{EvidenceUses, GivenId},
    expr::TypeInference,
};
use crate::{
    FxHashMap, FxHashSet,
    compiler::error::{
        ADTAccessType, InfiniteTypeKind, InternalCompilationError, InvalidRecordFieldContext,
        MutabilityMustBeContext, MutabilityMustBeWhat,
    },
    hir::NodeArena,
    internal_compilation_error,
    module::{LocalFunctionId, TraitId},
    parser::location::Location,
    std::{
        core_traits_names::{FROM_ITERATOR_TRAIT_NAME, REPR_TRAIT_NAME, VALUE_TRAIT_NAME},
        value::{is_compiler_provided_value_trait_application, type_has_static_layout},
    },
    types::{
        effect_polarity::EffectPolarity,
        effects::{EffType, EffectVar, EffectsInstSubst, no_effects},
        mutability::{MutType, MutVal, MutVar, MutVarKey},
        recursive_equation::{RecursiveEquationError, try_intern_recursive_equation},
        trait_solver::{ConstraintAssumptions, TraitSolver},
        r#type::{
            FnArgType, FnType, SubscriptMemberType, SubscriptResultConvention, SubscriptType,
            TyVarKey, Type, TypeInstSubst, TypeKind, TypeVar,
        },
        type_inference::substitution::InstSubst,
        type_like::{TypeLike, instantiate_types},
        type_mapper::{BitmapInstantiationMapper, TypeMapper},
        type_scheme::{ConstraintOrigin, PubTypeConstraint},
        type_visitor::TypeInnerVisitor,
    },
};

/// Whether the unification should target a subtype or the same type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SubOrSameType {
    /// Directional value compatibility, including bottom-to-any subtyping.
    SubType,
    /// Equal type structure and mutability, with directional callable effects.
    SameTypeWithSubEffects,
    /// Equality throughout the type, including callable effects and mutability.
    SameType,
}

#[derive(Debug, PartialEq, Eq)]
enum GivenMatch {
    Resolved,
    Deferred,
    Absent,
}

pub(crate) struct UnifiedTypeInferenceSnapshot {
    evidence_uses: EvidenceUses,
    ty_unification_table: Snapshot<InPlace<TyVarKey>>,
    mut_unification_table: Snapshot<InPlace<MutVarKey>>,
    effects: EffectSolverSnapshot,
    remaining_ty_constraints_len: usize,
    obligations_len: usize,
}

/// The type inference after unification, with only public constraints remaining
#[derive(Default, Debug)]
pub struct UnifiedTypeInference {
    pub(super) given_constraints: Vec<PubTypeConstraint>,
    pub(super) evidence_uses: EvidenceUses,
    pub(super) ty_unification_table: InPlaceUnificationTable<TyVarKey>,
    /// Remaining constraints that cannot be solved, will be part of the resulting type scheme
    pub(super) remaining_ty_constraints: Vec<PubTypeConstraint>,
    pub(super) mut_unification_table: InPlaceUnificationTable<MutVarKey>,
    pub(super) effects: EffectSolver,
    /// Constraints of the implementations that resolved trait applications, still to solve.
    obligations: Vec<PubTypeConstraint>,
}

/// Lexical owner for deferred obligations. Restores the enclosing owner on every
/// exit, including early returns and unwinding.
pub(crate) struct ConstraintOwnerScope<'a> {
    inference: &'a mut UnifiedTypeInference,
    previous: Option<LocalFunctionId>,
}

impl Deref for ConstraintOwnerScope<'_> {
    type Target = UnifiedTypeInference;
    fn deref(&self) -> &Self::Target {
        self.inference
    }
}

impl DerefMut for ConstraintOwnerScope<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inference
    }
}

impl Drop for ConstraintOwnerScope<'_> {
    fn drop(&mut self) {
        self.inference
            .evidence_uses
            .replace_active_owner(self.previous);
    }
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

fn constraints_equal_as_sets(left: &[PubTypeConstraint], right: &[PubTypeConstraint]) -> bool {
    left.iter().collect::<FxHashSet<_>>() == right.iter().collect::<FxHashSet<_>>()
}

impl UnifiedTypeInference {
    pub(crate) fn given_used_by(&self, owner: LocalFunctionId, given: GivenId) -> bool {
        self.evidence_uses.used_by(owner, given)
    }

    pub(crate) fn constraint_owner_scope(
        &mut self,
        owner: LocalFunctionId,
    ) -> ConstraintOwnerScope<'_> {
        let previous = self.evidence_uses.replace_active_owner(Some(owner));
        ConstraintOwnerScope {
            inference: self,
            previous,
        }
    }

    fn deduplicate_constraints_in_place(&mut self, constraints: &mut Vec<PubTypeConstraint>) {
        let mut seen = FxHashMap::<PubTypeConstraint, ConstraintOrigin>::default();
        constraints.retain(|constraint| {
            if let Some(origin) = seen.get(constraint) {
                if origin.index().is_some() || constraint.origin().index().is_some() {
                    self.evidence_uses.merge(*origin, constraint.origin());
                }
                false
            } else {
                seen.insert(constraint.clone(), constraint.origin());
                true
            }
        });
    }

    /// Apply functional-dependency equalities before publishing a checked contract.
    /// A diamond may reach the same trait/input pair with distinct fresh outputs.
    pub(crate) fn coalesce_constraint_outputs(
        &mut self,
        constraints: &mut Vec<PubTypeConstraint>,
    ) -> Result<(), InternalCompilationError> {
        loop {
            let before = constraints.clone();
            self.aggregate_constraints_for_pass(constraints.iter())?;
            self.substitute_in_constraints_in_place(constraints);
            self.deduplicate_constraints_in_place(constraints);
            if *constraints == before {
                return Ok(());
            }
        }
    }

    /// Reconcile the supplied evidence after signature equalities are known and
    /// before solving body obligations. Preserve every slot for stable GivenIds;
    /// unlike published schemes, this list must not be deduplicated.
    fn normalize_given_outputs(&mut self) -> Result<(), InternalCompilationError> {
        let mut givens = mem::take(&mut self.given_constraints);
        let result = (|| {
            if givens.len() > 1 {
                loop {
                    let before = givens.clone();
                    self.aggregate_constraints_for_pass(givens.iter())?;
                    self.substitute_in_constraints_in_place(&mut givens);
                    if givens == before {
                        break;
                    }
                }
            }
            Ok(())
        })();
        self.given_constraints = givens;
        result
    }

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

    /// Whether `mut_ty` is mutable. Mutability is solved before types are related, so it is
    /// known whenever a relation depends on it.
    fn is_resolved_mutable(
        &mut self,
        mut_ty: MutType,
        span: Location,
    ) -> Result<bool, InternalCompilationError> {
        match self.normalize_mut_type(mut_ty) {
            MutType::Resolved(value) => Ok(value.is_mutable()),
            MutType::Variable(_) => Err(internal_compilation_error!(Internal {
                span,
                error: "unresolved mutability when relating types".into(),
            })),
        }
    }

    /// A fresh effect variable that solving may not constrain, standing for one fixed elsewhere.
    pub(crate) fn fresh_rigid_effect_var(&mut self) -> EffectVar {
        self.effects.fresh_rigid_var(None)
    }

    pub(crate) fn fresh_effect_var_subst(&mut self, count: u32) -> EffectsInstSubst {
        (0..count)
            .map(|old_var| {
                (
                    EffectVar::new(old_var),
                    EffType::single_variable(self.fresh_effect_var()),
                )
            })
            .collect()
    }

    pub(crate) fn snapshot(&mut self) -> UnifiedTypeInferenceSnapshot {
        UnifiedTypeInferenceSnapshot {
            evidence_uses: self.evidence_uses.clone(),
            ty_unification_table: self.ty_unification_table.snapshot(),
            mut_unification_table: self.mut_unification_table.snapshot(),
            effects: self.effects.snapshot(),
            remaining_ty_constraints_len: self.remaining_ty_constraints.len(),
            obligations_len: self.obligations.len(),
        }
    }

    pub(crate) fn rollback_to(&mut self, snapshot: UnifiedTypeInferenceSnapshot) {
        self.evidence_uses = snapshot.evidence_uses;
        self.ty_unification_table
            .rollback_to(snapshot.ty_unification_table);
        self.mut_unification_table
            .rollback_to(snapshot.mut_unification_table);
        self.effects.rollback_to(snapshot.effects);
        self.remaining_ty_constraints
            .truncate(snapshot.remaining_ty_constraints_len);
        self.obligations.truncate(snapshot.obligations_len);
    }

    pub fn unify_type_inference(
        ty_inf: TypeInference,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Self, InternalCompilationError> {
        let TypeInference {
            given_constraints,
            evidence_uses,
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
            given_constraints,
            evidence_uses,
            ty_unification_table,
            remaining_ty_constraints: vec![],
            mut_unification_table,
            effects,
            obligations: vec![],
        };
        // Keep source/inference order stable. Constraint equality deliberately ignores spans, so
        // iterating a hash set here made the diagnostic span and dictionary order depend on the
        // process-local identities assigned by the type interner.
        let mut remaining_constraints = Vec::new();
        // Case-qualified payload layouts are evidence obligations with no trait outputs, so they
        // cannot improve inference. Normalize them once after the semantic fixed point instead of
        // revisiting potentially large recursive `Value<B>` applications on every pass.
        let mut variant_layout_constraints = Vec::new();

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

        // Then, solve all type equalities. Subtyping between two unknown types is deferred until
        // one of them is known: binding it then relates their effects by inclusion, whereas
        // binding the variables to each other would equate them.
        let mut deferred_subtypes = Vec::new();
        for constraint in ty_constraints {
            use TypeConstraint::*;
            match constraint {
                Pub(cst) => {
                    let destination =
                        if matches!(cst, PubTypeConstraint::VariantPayloadLayout { .. }) {
                            &mut variant_layout_constraints
                        } else {
                            &mut remaining_constraints
                        };
                    destination.push(cst);
                }
                constraint if unified_ty_inf.relates_unknown_types(&constraint) => {
                    deferred_subtypes.push(constraint);
                }
                constraint => unified_ty_inf.unify_type_relation(constraint)?,
            }
        }
        loop {
            let count = deferred_subtypes.len();
            for constraint in mem::take(&mut deferred_subtypes) {
                if unified_ty_inf.relates_unknown_types(&constraint) {
                    deferred_subtypes.push(constraint);
                } else {
                    unified_ty_inf.unify_type_relation(constraint)?;
                }
            }
            if deferred_subtypes.len() == count {
                break;
            }
        }
        for constraint in deferred_subtypes {
            unified_ty_inf.unify_type_relation(constraint)?;
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

        unified_ty_inf.normalize_given_outputs()?;

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
            unified_ty_inf.substitute_in_constraints_in_place(&mut remaining_constraints);
            unified_ty_inf.deduplicate_constraints_in_place(&mut remaining_constraints);

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
                unified_ty_inf.deduplicate_constraints_in_place(&mut new_constraints);
                remaining_constraints = new_constraints;

                // Break if no progress was made
                if constraints_equal_as_sets(&remaining_constraints, &old_remaining_constraints) {
                    break;
                }
            }
        }

        if !variant_layout_constraints.is_empty() {
            unified_ty_inf.substitute_in_constraints_in_place(&mut variant_layout_constraints);
            variant_layout_constraints.retain(|constraint| {
                let PubTypeConstraint::VariantPayloadLayout {
                    payload_ty,
                    payload_span,
                    ..
                } = constraint
                else {
                    unreachable!("only variant layout evidence is deferred")
                };
                !type_has_static_layout(*payload_ty, payload_span.use_site, trait_solver)
            });
            remaining_constraints.extend(variant_layout_constraints);
            unified_ty_inf.deduplicate_constraints_in_place(&mut remaining_constraints);
        }

        // Create minimalist types for orphan variant constraints.
        // FIXME: something is missing here
        // remaining_constraints = unified_ty_inf.simplify_variant_constraints(remaining_constraints);

        // Flatten inverted effect constraints into normal constraints
        unified_ty_inf.effects.expand_pending_dependencies()?;

        // FIXME: think whether we should have an intermediate struct without the remaining_constraints in it.
        unified_ty_inf.remaining_ty_constraints = remaining_constraints;
        Ok(unified_ty_inf)
    }

    /// Whether `constraint` relates two types that are both still unknown.
    fn relates_unknown_types(&mut self, constraint: &TypeConstraint) -> bool {
        use TypeConstraint::*;
        let (SameTypeWithSubEffects {
            current, expected, ..
        }
        | SubType {
            current, expected, ..
        }) = constraint
        else {
            return false;
        };
        let current = self.normalize_type(*current);
        let expected = self.normalize_type(*expected);
        current != expected && current.data().is_variable() && expected.data().is_variable()
    }

    /// Solve a type relation, a constraint other than a public one.
    fn unify_type_relation(
        &mut self,
        constraint: TypeConstraint,
    ) -> Result<(), InternalCompilationError> {
        use TypeConstraint::*;
        match constraint {
            SameTypeWithSubEffects {
                current,
                current_span,
                expected,
                expected_span,
            } => self.unify_same_type_with_sub_effects(
                current,
                current_span,
                expected,
                expected_span,
            ),
            SubType {
                current,
                current_span,
                expected,
                expected_span,
            } => self.unify_sub_type(current, current_span, expected, expected_span),
            Pub(_) => unreachable!("public constraints are solved later"),
        }
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
            &mut FxHashSet::default(),
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
            &mut FxHashSet::default(),
        )
    }

    fn unify_sub_or_same_type(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
        sub_or_same: SubOrSameType,
        active: &mut FxHashSet<(Type, Type, SubOrSameType)>,
    ) -> Result<(), InternalCompilationError> {
        if current == expected {
            return Ok(());
        }
        let current_ty = self.normalize_type(current);
        let expected_ty = self.normalize_type(expected);
        if current_ty == expected_ty {
            return Ok(());
        }
        // Only recursive worlds can close a cycle. Keep the ordered, normalized pair
        // and its relation: contravariance reverses the pair, and named arguments
        // strengthen subtyping to equality. Neither may reuse the weaker assumption.
        let recursive = current_ty.is_global_recursive() && expected_ty.is_global_recursive();
        let key = (current_ty, expected_ty, sub_or_same);
        if recursive && !active.insert(key) {
            return Ok(());
        }
        let result = self.unify_type_structure(
            current_ty,
            current_span,
            expected_ty,
            expected_span,
            sub_or_same,
            active,
        );
        // These are assumptions on the current path, not cached results. Remove them
        // on success and failure; later comparisons may observe new variable bindings.
        if recursive {
            active.remove(&key);
        }
        result
    }

    fn unify_type_structure(
        &mut self,
        current_ty: Type,
        current_span: Location,
        expected_ty: Type,
        expected_span: Location,
        sub_or_same: SubOrSameType,
        active: &mut FxHashSet<(Type, Type, SubOrSameType)>,
    ) -> Result<(), InternalCompilationError> {
        let cur_data = { current_ty.data().clone() };
        let exp_data = { expected_ty.data().clone() };
        use SubOrSameType::*;
        use TypeKind::*;
        match (cur_data, exp_data) {
            // Bottom supplies no value and imposes no restriction on a supertype,
            // even when that supertype is still unknown. Equality is different:
            // the variable cases below must bind it to Never. Likewise, a variable
            // constrained to be a subtype of Never must itself become Never.
            (Never, _) if sub_or_same == SubType => Ok(()),
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
            (Variable(var), _) => self.unify_type_variable(
                var,
                current_span,
                expected_ty,
                expected_span,
                false,
                sub_or_same,
            ),
            (_, Variable(var)) => self.unify_type_variable(
                var,
                expected_span,
                current_ty,
                current_span,
                true,
                sub_or_same,
            ),
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
                        active,
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
                        active,
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
                        active,
                    )?;
                }
                Ok(())
            }
            (Record(cur), Record(exp)) => {
                if cur.len() != exp.len() {
                    return Err(internal_compilation_error!(TypeMismatch {
                        current_ty,
                        current_span,
                        expected_ty,
                        expected_span,
                        sub_or_same,
                    }));
                }
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
                        active,
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
                        active,
                    )?;
                    // Only a callee that can write needs the reverse check. A read-only
                    // implementation stays contravariant even when the expected contract
                    // permits writes; making that case invariant would break transitivity.
                    if sub_or_same != SameType
                        && self.is_resolved_mutable(cur_arg.mut_ty, current_span)?
                    {
                        self.unify_sub_or_same_type(
                            cur_arg.ty,
                            current_span,
                            exp_arg.ty,
                            expected_span,
                            sub_or_same,
                            active,
                        )?;
                    }
                }
                if sub_or_same == SameType {
                    self.unify_same_effect(cur.effects, current_span, exp.effects, expected_span)?;
                } else {
                    // Covariant effects.
                    self.add_effect_dep(&cur.effects, current_span, &exp.effects, expected_span)?;
                }
                // Covariance of return type.
                self.unify_sub_or_same_type(
                    cur.ret,
                    current_span,
                    exp.ret,
                    expected_span,
                    sub_or_same,
                    active,
                )
            }
            (Subscript(cur), Subscript(exp)) => {
                if cur.args.len() != exp.args.len()
                    || !cur.can_satisfy_members(&exp)
                    || (sub_or_same == SameType && !exp.can_satisfy_members(&cur))
                {
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
                        active,
                    )?;
                    // As for functions, write-back depends on the actual callee's access,
                    // not on the expected contract permitting mutable access.
                    if sub_or_same != SameType
                        && self.is_resolved_mutable(cur_arg.mut_ty, current_span)?
                    {
                        self.unify_sub_or_same_type(
                            cur_arg.ty,
                            current_span,
                            exp_arg.ty,
                            expected_span,
                            sub_or_same,
                            active,
                        )?;
                    }
                }
                self.unify_subscript_member_effects(
                    cur.ref_member.as_ref(),
                    current_span,
                    exp.ref_member.as_ref(),
                    expected_span,
                    sub_or_same,
                )?;
                self.unify_subscript_member_effects(
                    cur.mut_member.as_ref(),
                    current_span,
                    exp.mut_member.as_ref(),
                    expected_span,
                    sub_or_same,
                )?;
                // Covariance of return type.
                self.unify_sub_or_same_type(
                    cur.ret,
                    current_span,
                    exp.ret,
                    expected_span,
                    sub_or_same,
                    active,
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
                    // A parameter may occur in negative or mutable positions in the
                    // definition. Without variance analysis, named type arguments are invariant.
                    self.unify_sub_or_same_type(
                        cur_el_ty,
                        current_span,
                        exp_el_ty,
                        expected_span,
                        SameType,
                        active,
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
                sub_or_same,
            })),
        }
    }

    /// Bind `var` to `ty`; `var_is_supertype` tells whether values of type `ty` flow into `var`.
    fn unify_type_variable(
        &mut self,
        var: TypeVar,
        var_span: Location,
        ty: Type,
        ty_span: Location,
        var_is_supertype: bool,
        sub_or_same: SubOrSameType,
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
        } else if sub_or_same == SubOrSameType::SameType {
            ty
        } else {
            // A variable bound to a callable gets its own effect variable, related to the
            // callable's by inclusion in the direction of the subtyping, so that the other values
            // related to `var` do not share effects with this callable.
            self.effects
                .generalize_effectful_callable_type(ty, var_is_supertype)
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
    fn match_given(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        span: Location,
        origin: ConstraintOrigin,
    ) -> Result<GivenMatch, InternalCompilationError> {
        // Equal trait/input applications denote the same evidence. Reconcile every
        // matching given's outputs, rather than letting list order select a contract.
        let mut matches = Vec::new();
        let mut potential_inputs = Vec::new();
        for index in 0..self.given_constraints.len() {
            let given = self.substitute_in_constraint(&self.given_constraints[index].clone());
            let PubTypeConstraint::HaveTrait {
                trait_id: given_trait,
                input_tys: given_inputs,
                output_tys: given_outputs,
                output_effs: given_effects,
                ..
            } = given
            else {
                continue;
            };
            if given_trait != trait_id {
                continue;
            }
            debug_assert_eq!(given_inputs.len(), input_tys.len());
            debug_assert_eq!(given_outputs.len(), output_tys.len());
            debug_assert_eq!(given_effects.len(), output_effs.len());
            if given_inputs == input_tys {
                matches.push((GivenId(index), given_outputs, given_effects));
            } else {
                potential_inputs.push(given_inputs);
            }
        }
        if !matches.is_empty() {
            for (given, given_outputs, given_effects) in matches {
                for (actual, expected) in output_tys.iter().zip(&given_outputs) {
                    self.unify_same_type_with_sub_effects(*actual, span, *expected, span)?;
                }
                // Applications with equal trait and inputs in one scope are equal.
                for (actual, expected) in output_effs.iter().zip(&given_effects) {
                    self.unify_same_effect(actual.clone(), span, expected.clone(), span)?;
                }
                self.evidence_uses.record(origin, given);
            }
            return Ok(GivenMatch::Resolved);
        }
        for given_inputs in potential_inputs {
            // Probe compatibility without learning input equalities from evidence.
            // In particular Convert<A, ?b> must not force ?b to a given's B.
            let snapshot = self.snapshot();
            let compatible = input_tys
                .iter()
                .zip(&given_inputs)
                .all(|(actual, expected)| {
                    self.unify_same_type_with_sub_effects(*actual, span, *expected, span)
                        .is_ok()
                });
            self.rollback_to(snapshot);
            if compatible {
                return Ok(GivenMatch::Deferred);
            }
        }
        Ok(GivenMatch::Absent)
    }

    #[allow(clippy::too_many_arguments)]
    fn unify_have_trait(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        span: Location,
        origin: ConstraintOrigin,
        assumptions: ConstraintAssumptions<'_>,
        is_ty_adt: impl Fn(Type) -> bool,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let mut input_tys = self.normalize_types(input_tys);
        let mut output_tys = self.normalize_types(output_tys);
        let mut output_effs = self.substitute_in_effect_types(output_effs);
        match self.match_given(
            trait_id,
            &input_tys,
            &output_tys,
            &output_effs,
            span,
            origin,
        )? {
            GivenMatch::Resolved => return Ok(None),
            GivenMatch::Deferred => {
                return Ok(Some(PubTypeConstraint::new_have_trait(
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                    span,
                )));
            }
            GivenMatch::Absent => {}
        }
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
                && is_compiler_provided_value_trait_application(
                    trait_id,
                    trait_def,
                    &input_tys,
                    &output_tys,
                    trait_solver,
                )
            {
                return Ok(None);
            }
            // Fully resolved, validate the trait implementation.
            self.resolve_trait_application(
                trait_id,
                &input_tys,
                &output_tys,
                &output_effs,
                span,
                trait_solver,
                arena,
            )?;
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
                self.resolve_trait_application(
                    trait_id,
                    &input_tys,
                    &output_tys,
                    &output_effs,
                    span,
                    trait_solver,
                    arena,
                )?;
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
        ordered_constraints.sort_by_key(|(_, constraint)| {
            (
                constraint_solve_priority(constraint, trait_solver),
                constraint_solve_specificity(constraint),
            )
        });
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
            new_constraints.append(&mut self.obligations);
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
        let mut have_traits: FxHashMap<(TraitId, Vec<Type>), HaveTraitOutputs> =
            FxHashMap::default();

        for constraint in constraints {
            use PubTypeConstraint::*;
            match constraint {
                TupleAtIndexIs {
                    origin: _,
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
                    origin: _,
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
                                origin: constraint.origin(),
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
                    self.evidence_uses.merge(
                        aggregation.constraints[existing_index].origin(),
                        constraint.origin(),
                    );
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
                    origin: _,
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
                VariantPayloadLayout { .. } => {
                    aggregation.constraints.push(Cow::Borrowed(constraint));
                }
                HaveTrait {
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                    span,
                    ..
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
        let mut result = self.unify_pub_constraint_inner(
            constraint,
            assumptions,
            is_ty_adt,
            trait_solver,
            arena,
        )?;
        if let Some(constraint_out) = &mut result {
            constraint_out.set_origin(constraint.origin());
        }
        Ok(result)
    }

    fn unify_pub_constraint_inner(
        &mut self,
        constraint: &PubTypeConstraint,
        assumptions: ConstraintAssumptions<'_>,
        is_ty_adt: impl Fn(Type) -> bool,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        if let PubTypeConstraint::VariantPayloadLayout {
            origin: _,
            variant_ty,
            tag,
            payload_ty,
            payload_span,
        } = constraint
        {
            let payload_ty = self.normalize_type(*payload_ty);
            if type_has_static_layout(payload_ty, payload_span.use_site, trait_solver) {
                return Ok(None);
            }
            return Ok(Some(PubTypeConstraint::VariantPayloadLayout {
                origin: Default::default(),
                variant_ty: self.normalize_type(*variant_ty),
                tag: *tag,
                payload_ty,
                payload_span: payload_span.clone(),
            }));
        }
        if let PubTypeConstraint::HaveTrait {
            origin: _,
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
                constraint.origin(),
                assumptions,
                is_ty_adt,
                trait_solver,
                arena,
            );
        }
        if let PubTypeConstraint::ProjectionSubscriptIs {
            origin: _,
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
                    origin: Default::default(),
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
                origin: _,
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
                origin: _,
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
                origin: _,
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
                        origin: Default::default(),
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
            VariantPayloadLayout { .. } | HaveTrait { .. } => {
                unreachable!("evidence and trait constraints are handled by the caller")
            }
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
        // For either same-type relation, the table is a perfect diagonal.
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
                    SameTypeWithSubEffects | SameType => current != target,
                } {
                    Err(internal_compilation_error!(MutabilityMustBe {
                        source_span: current_span,
                        reason_span: target_span,
                        what: match sub_or_same {
                            SubType => Mutable,
                            SameTypeWithSubEffects | SameType => Equal,
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
            SameTypeWithSubEffects | SameType => self
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
            SameTypeWithSubEffects | SameType => self
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

    /// Resolve a trait application whose inputs are known: relate its outputs to those of the
    /// implementation the solver selects, output effects by their polarity. A blanket
    /// implementation is instantiated here, its constraints becoming obligations, so that its
    /// outputs keep their variables; other implementations have constant outputs.
    #[allow(clippy::too_many_arguments)]
    fn resolve_trait_application(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        span: Location,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<(), InternalCompilationError> {
        let (impl_output_tys, impl_output_effs) = match trait_solver
            .resolve_application_symbolically(trait_id, input_tys, output_tys, output_effs, span)?
        {
            Some(application) => {
                let mut subst: InstSubst = Default::default();
                let mut add_fresh_vars =
                    |ty_vars: Vec<TypeVar>, eff_vars: FxHashSet<EffectVar>, this: &mut Self| {
                        for var in ty_vars {
                            if var.name() >= application.type_var_base
                                && !subst.0.contains_key(&var)
                            {
                                subst.0.insert(var, Type::variable(this.fresh_type_var()));
                            }
                        }
                        for var in eff_vars {
                            if var.name() >= application.effect_var_base
                                && !subst.1.contains_key(&var)
                            {
                                subst
                                    .1
                                    .insert(var, EffType::single_variable(this.fresh_effect_var()));
                            }
                        }
                    };
                for ty in &application.output_tys {
                    add_fresh_vars(ty.inner_ty_vars(), ty.inner_effect_vars(), self);
                }
                for eff in &application.output_effs {
                    let mut vars = FxHashSet::default();
                    eff.fill_with_inner_effect_vars(&mut vars);
                    add_fresh_vars(vec![], vars, self);
                }
                for obligation in &application.obligations {
                    let mut vars = FxHashSet::default();
                    obligation.fill_with_inner_effect_vars(&mut vars);
                    add_fresh_vars(obligation.inner_ty_vars(), vars, self);
                }
                let mut mapper = BitmapInstantiationMapper::new(&subst);
                let impl_output_tys = instantiate_types(&application.output_tys, &mut mapper);
                let impl_output_effs = application
                    .output_effs
                    .iter()
                    .map(|eff| mapper.map_effect_type(eff))
                    .collect::<Vec<_>>();
                self.obligations.extend(
                    application
                        .obligations
                        .iter()
                        .map(|obligation| obligation.map(&mut mapper)),
                );
                (impl_output_tys, impl_output_effs)
            }
            None => trait_solver.solve_application_outputs(
                trait_id,
                input_tys,
                output_tys,
                output_effs,
                span,
                arena,
            )?,
        };
        assert_eq!(output_tys.len(), impl_output_tys.len());
        for (cur_ty, exp_ty) in output_tys.iter().zip(impl_output_tys.iter()) {
            self.unify_same_type_with_sub_effects(*cur_ty, span, *exp_ty, span)?;
        }
        assert_eq!(output_effs.len(), impl_output_effs.len());
        let polarities = trait_solver.output_effect_polarities(trait_id);
        for ((cur_eff, exp_eff), polarity) in output_effs
            .iter()
            .zip(impl_output_effs.iter())
            .zip(polarities)
        {
            match polarity {
                EffectPolarity::Positive => self.add_effect_dep(exp_eff, span, cur_eff, span)?,
                EffectPolarity::Negative => self.add_effect_dep(cur_eff, span, exp_eff, span)?,
                EffectPolarity::Invariant => {
                    self.unify_same_effect(cur_eff.clone(), span, exp_eff.clone(), span)?
                }
            }
        }
        Ok(())
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

    fn unify_subscript_member_effects(
        &mut self,
        current: Option<&SubscriptMemberType>,
        current_span: Location,
        target: Option<&SubscriptMemberType>,
        target_span: Location,
        sub_or_same: SubOrSameType,
    ) -> Result<(), InternalCompilationError> {
        let Some(target) = target else {
            return Ok(());
        };
        let Some(current) = current else {
            return Ok(());
        };
        if sub_or_same == SubOrSameType::SameType {
            self.unify_same_effect(
                current.effects.clone(),
                current_span,
                target.effects.clone(),
                target_span,
            )
        } else {
            self.add_effect_dep(&current.effects, current_span, &target.effects, target_span)
        }
    }

    pub fn finalize_effect_dependencies(&mut self) -> Result<(), InternalCompilationError> {
        self.effects.finalize()
    }

    /// The number of effect variables, which is the name of the next fresh one.
    pub(crate) fn effect_var_count(&self) -> u32 {
        self.effects.var_count()
    }

    /// Fix the effect variables named from `start` on, which nothing else observes, at their
    /// least solution.
    pub(crate) fn minimize_effects_from(
        &mut self,
        start: u32,
    ) -> Result<(), InternalCompilationError> {
        let observable = (0..start).map(EffectVar::new).collect();
        self.effects.minimize_except(&observable)
    }

    /// Fix the effect variables that nothing outside the inferred code observes at their least
    /// solution: all but `observable` and the variables of constraints with type variables.
    pub(crate) fn minimize_unobservable_effects(
        &mut self,
        mut observable: FxHashSet<EffectVar>,
    ) -> Result<(), InternalCompilationError> {
        self.normalize_remaining_constraints();
        for constraint in &self.remaining_ty_constraints {
            if !constraint.inner_ty_vars().is_empty() {
                constraint.fill_with_inner_effect_vars(&mut observable);
            }
        }
        self.effects.minimize_except(&observable)
    }

    /// Reject a type whose effects would combine two declared effect variables in one row, which
    /// no effect set can express.
    pub(crate) fn check_declared_effects_not_combined(
        &mut self,
        ty: &FnType,
        span: Location,
    ) -> Result<(), InternalCompilationError> {
        struct Rows(Vec<EffType>);
        impl TypeInnerVisitor for Rows {
            fn visit_eff_ty(&mut self, eff_ty: &EffType) {
                self.0.push(eff_ty.clone());
            }
        }
        let mut rows = Rows(Vec::new());
        ty.visit(&mut rows);
        for row in rows.0 {
            if let Some((first, second)) = self.effects.combined_declared_variables(&row) {
                return Err(internal_compilation_error!(EffectVariablesCombined {
                    first,
                    second,
                    span,
                }));
            }
        }
        Ok(())
    }

    /// Whether effects are read through their publication view, see
    /// [`Self::finalize_effect_dependencies`].
    pub(crate) fn effects_finalized(&self) -> bool {
        self.effects.is_finalized()
    }

    /// Return to reading effects as before [`Self::finalize_effect_dependencies`], for a
    /// solver whose inference goes on after a query read its published effects.
    pub(crate) fn restore_effects_finalized(&mut self, finalized: bool) {
        self.effects.set_finalized(finalized);
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
        PubTypeConstraint::VariantPayloadLayout { .. } => 95,
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

/// Prefer shaped trait inputs over bare variables at the same solver priority. A structural
/// requirement can decompose into obligations for its members (for example `Value<(A,)>` needs
/// `Value<A>`), while solving the bare obligation first cannot make the structural one progress.
/// This is semantic ordering and deliberately does not inspect interned type identities.
fn constraint_solve_specificity(constraint: &PubTypeConstraint) -> u8 {
    match constraint {
        PubTypeConstraint::HaveTrait { input_tys, .. }
            if input_tys
                .iter()
                .any(|ty| !matches!(&*ty.data(), TypeKind::Variable(_))) =>
        {
            0
        }
        _ => 1,
    }
}

#[cfg(test)]
mod never_tests {
    use super::*;
    use crate::{
        std::{logic::bool_type, math::int_type},
        types::effects::{PrimitiveEffect, effect},
    };

    fn relate(
        inference: &mut UnifiedTypeInference,
        current: Type,
        expected: Type,
        relation: SubOrSameType,
    ) -> Result<(), InternalCompilationError> {
        let span = Location::new_synthesized();
        inference.unify_sub_or_same_type(
            current,
            span,
            expected,
            span,
            relation,
            &mut FxHashSet::default(),
        )
    }

    #[test]
    fn never_is_bottom_only_for_subtyping() {
        use SubOrSameType::*;
        for relation in [SubType, SameTypeWithSubEffects, SameType] {
            for other in [int_type(), Type::tuple(vec![Type::never()])] {
                let mut inference = UnifiedTypeInference::default();
                assert_eq!(
                    relate(&mut inference, Type::never(), other, relation).is_ok(),
                    relation == SubType,
                );
                assert!(relate(&mut inference, other, Type::never(), relation).is_err());
            }
            assert!(
                relate(
                    &mut UnifiedTypeInference::default(),
                    Type::never(),
                    Type::never(),
                    relation,
                )
                .is_ok()
            );
        }
    }

    #[test]
    fn never_inference_respects_direction_and_constraint_order() {
        use SubOrSameType::*;
        let unknown = Type::variable_id(0);
        for relation in [SubType, SameTypeWithSubEffects, SameType] {
            for never_first in [false, true] {
                // A bottom lower bound leaves the variable free; equality or an
                // upper bound of bottom fixes it, whichever constraint is first.
                for bottom_on_left in [false, true] {
                    let mut inference = UnifiedTypeInference::new_with_ty_vars(1);
                    let bottom_relation = if bottom_on_left {
                        (Type::never(), unknown, relation)
                    } else {
                        (unknown, Type::never(), relation)
                    };
                    let integer_relation = (unknown, int_type(), SameType);
                    let constraints = if never_first {
                        [bottom_relation, integer_relation]
                    } else {
                        [integer_relation, bottom_relation]
                    };
                    let result = constraints
                        .into_iter()
                        .try_for_each(|(a, b, r)| relate(&mut inference, a, b, r));
                    let unconstrained = relation == SubType && bottom_on_left;
                    assert_eq!(result.is_ok(), unconstrained);
                    if unconstrained {
                        assert_eq!(inference.substitute_in_type(unknown), int_type());
                    }
                }
            }
            for (a, b) in [(unknown, Type::never()), (Type::never(), unknown)] {
                let mut inference = UnifiedTypeInference::new_with_ty_vars(1);
                relate(&mut inference, a, b, relation).unwrap();
                let expected = if relation == SubType && a == Type::never() {
                    unknown
                } else {
                    Type::never()
                };
                assert_eq!(inference.substitute_in_type(unknown), expected);
            }
        }
    }

    #[test]
    fn never_callable_variance_preserves_effects_and_mutable_arguments() {
        use SubOrSameType::*;
        let bottom_result = Type::nullary_function_by_val(Type::never());
        let bool_result = Type::nullary_function_by_val(bool_type());
        let mut inference = UnifiedTypeInference::default();
        relate(&mut inference, bottom_result, bool_result, SubType).unwrap();
        assert!(relate(&mut inference, bool_result, bottom_result, SubType).is_err());
        for relation in [SameTypeWithSubEffects, SameType] {
            assert!(relate(&mut inference, bottom_result, bool_result, relation).is_err());
        }
        let fallible_bottom = Type::function_by_val_with_effects(
            [],
            Type::never(),
            effect(PrimitiveEffect::Fallible),
        );
        assert!(relate(&mut inference, fallible_bottom, bool_result, SubType).is_err());

        let accepting = |ty, mutable| {
            Type::function_type(FnType::new(
                vec![FnArgType::new(
                    ty,
                    MutType::resolved(if mutable {
                        MutVal::mutable()
                    } else {
                        MutVal::constant()
                    }),
                )],
                Type::unit(),
                no_effects(),
            ))
        };
        relate(
            &mut inference,
            accepting(int_type(), false),
            accepting(Type::never(), false),
            SubType,
        )
        .unwrap();
        assert!(
            relate(
                &mut inference,
                accepting(Type::never(), false),
                accepting(int_type(), false),
                SubType
            )
            .is_err()
        );
        for (a, b) in [(int_type(), Type::never()), (Type::never(), int_type())] {
            assert!(
                relate(
                    &mut inference,
                    accepting(a, true),
                    accepting(b, true),
                    SubType
                )
                .is_err()
            );
        }
    }
}

#[cfg(test)]
mod callable_subtyping_tests {
    use super::*;
    use crate::{
        compiler::error::CompilationErrorImpl,
        std::{logic::bool_type, math::int_type},
        types::effects::{PrimitiveEffect::Fallible, effect},
    };

    fn accepting(
        arg: Type,
        mutable: impl Into<MutType>,
        effects: EffType,
        subscript: bool,
    ) -> Type {
        let args = vec![FnArgType::new(arg, mutable.into())];
        if subscript {
            Type::subscript_type(SubscriptType::new(
                args,
                Type::unit(),
                Some(SubscriptMemberType::new(
                    effects,
                    SubscriptResultConvention::AddressorPlace,
                )),
                None,
            ))
        } else {
            Type::function_type(FnType::new(args, Type::unit(), effects))
        }
    }

    fn relates(current: Type, expected: Type, relation: SubOrSameType) -> bool {
        let span = Location::new_synthesized();
        UnifiedTypeInference::default()
            .unify_sub_or_same_type(
                current,
                span,
                expected,
                span,
                relation,
                &mut FxHashSet::default(),
            )
            .is_ok()
    }

    #[test]
    fn callable_subtyping_matches_read_write_model_and_is_transitive() {
        // A finite interpretation independent of structural comparison: bits stand
        // for observable values/behaviors. The callback sets contain a divergent
        // behavior, then an integer-returning one, then a failing one.
        let arguments = [
            (Type::never(), 0_u8),
            (int_type(), 0b00001),
            (bool_type(), 0b00010),
            (Type::nullary_function_by_val(Type::never()), 0b00100),
            (Type::nullary_function_by_val(int_type()), 0b01100),
            (
                Type::function_by_val_with_effects([], int_type(), effect(Fallible)),
                0b11100,
            ),
        ];
        for subscript in [false, true] {
            let mut cases = Vec::new();
            for (argument, values) in arguments {
                for mutable in [false, true] {
                    for fallible in [false, true] {
                        let effects = if fallible {
                            effect(Fallible)
                        } else {
                            no_effects()
                        };
                        cases.push((
                            accepting(argument, mutable, effects, subscript),
                            values,
                            mutable.then_some(values),
                            fallible,
                        ));
                    }
                }
            }
            let mut relation = vec![vec![false; cases.len()]; cases.len()];
            for (i, &(actual, reads, writes, fails)) in cases.iter().enumerate() {
                for (j, &(expected, inputs, outputs, may_fail)) in cases.iter().enumerate() {
                    let can_read = inputs & !reads == 0;
                    let can_write = writes
                        .is_none_or(|writes| outputs.is_some_and(|outputs| writes & !outputs == 0));
                    let modeled = can_read && can_write && (!fails || may_fail);
                    relation[i][j] = relates(actual, expected, SubOrSameType::SubType);
                    assert_eq!(
                        relation[i][j], modeled,
                        "read/write model disagrees for {actual:?} <: {expected:?}"
                    );
                }
            }
            for (i, row) in relation.iter().enumerate() {
                assert!(row[i]);
                for (j, &ij) in row.iter().enumerate() {
                    for (k, &jk) in relation[j].iter().enumerate() {
                        assert!(
                            !ij || !jk || row[k],
                            "non-transitive callable relation: {:?} <: {:?} <: {:?}",
                            cases[i].0,
                            cases[j].0,
                            cases[k].0
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn unresolved_callable_mutability_is_an_internal_error() {
        for subscript in [false, true] {
            let mut inference = UnifiedTypeInference::default();
            let actual_mut = inference.mut_unification_table.new_key(None);
            let expected_mut = inference.mut_unification_table.new_key(None);
            let actual = accepting(
                int_type(),
                MutType::variable(actual_mut),
                no_effects(),
                subscript,
            );
            let expected = accepting(
                Type::never(),
                MutType::variable(expected_mut),
                no_effects(),
                subscript,
            );
            let span = Location::new_synthesized();
            let error = inference
                .unify_sub_type(actual, span, expected, span)
                .unwrap_err();
            assert!(matches!(
                &*error,
                CompilationErrorImpl::Internal { error, .. }
                    if error == "unresolved mutability when relating types"
            ));
        }
    }

    #[test]
    fn callable_mutability_coercion_does_not_weaken_equality() {
        for subscript in [false, true] {
            let read = accepting(int_type(), false, no_effects(), subscript);
            let write = accepting(int_type(), true, no_effects(), subscript);
            assert!(relates(read, write, SubOrSameType::SubType));
            assert!(!relates(write, read, SubOrSameType::SubType));
            for relation in [
                SubOrSameType::SameType,
                SubOrSameType::SameTypeWithSubEffects,
            ] {
                assert!(!relates(read, write, relation));
                assert!(!relates(write, read, relation));
            }
        }
    }
}

#[cfg(test)]
mod recursive_tests {
    use super::*;
    use crate::{
        module::{LocalTypeDefId, ModuleId, TypeDefId},
        std::{logic::bool_type, math::int_type},
        types::{
            effects::{PrimitiveEffect, effect},
            r#type::{NamedType, store_types},
        },
    };
    use ustr::ustr;

    fn tail_first_list(payload: Type) -> Type {
        store_types(&[
            TypeKind::Variant(vec![
                (ustr("Nil"), Type::unit()),
                (ustr("Cons"), Type::new_local(1)),
            ]),
            TypeKind::Tuple(vec![Type::new_local(0), payload]),
        ])[0]
    }

    #[test]
    fn recursive_comparison_observes_inferred_payloads() {
        let mut inference = UnifiedTypeInference::new_with_ty_vars(1);
        let span = Location::new_synthesized();
        let unknown = Type::variable_id(0);
        let generic = tail_first_list(unknown);
        let integers = tail_first_list(int_type());
        let booleans = tail_first_list(bool_type());

        inference
            .unify_same_type_with_sub_effects(generic, span, integers, span)
            .unwrap();
        assert_eq!(inference.substitute_in_type(unknown), int_type());
        assert_eq!(inference.substitute_in_type(generic), integers);
        // A later comparison sees the binding, and a failed comparison must not
        // leave a cycle assumption that would make a retry succeed.
        for _ in 0..2 {
            assert!(
                inference
                    .unify_sub_type(generic, span, booleans, span)
                    .is_err()
            );
        }
    }

    #[test]
    fn recursive_comparison_distinguishes_subtyping_from_equality() {
        // A<T> = Done | Next(Box<A<T>>, T). The named type's definition is not
        // consulted when comparing its arguments, so a synthetic id suffices.
        let recursive = |payload| {
            store_types(&[
                TypeKind::Variant(vec![
                    (ustr("Done"), Type::unit()),
                    (ustr("Next"), Type::new_local(1)),
                ]),
                TypeKind::Tuple(vec![Type::new_local(2), payload]),
                TypeKind::Named(NamedType {
                    def: TypeDefId::new(ModuleId::new(0), LocalTypeDefId::new(0)),
                    params: vec![Type::new_local(0)],
                    effect_params: vec![],
                }),
            ])[0]
        };
        let pure = Type::nullary_function_by_val(int_type());
        let fallible =
            Type::function_by_val_with_effects([], int_type(), effect(PrimitiveEffect::Fallible));
        let span = Location::new_synthesized();
        let mut inference = UnifiedTypeInference::default();
        inference
            .unify_sub_type(pure, span, fallible, span)
            .unwrap();
        // Traversing Box strengthens the active pair's relation. Skipping that
        // comparison would incorrectly allow the covariant callback widening.
        assert!(
            inference
                .unify_sub_type(recursive(pure), span, recursive(fallible), span)
                .is_err()
        );
    }
}

#[cfg(test)]
mod given_tests {
    use super::*;
    use crate::module::{LocalTraitId, ModuleId, id::Id};

    fn trait_id() -> TraitId {
        TraitId::new(ModuleId::new(0), LocalTraitId::new(0))
    }

    fn given(inputs: Vec<Type>, outputs: Vec<Type>) -> PubTypeConstraint {
        PubTypeConstraint::new_have_trait(
            trait_id(),
            inputs,
            outputs,
            vec![],
            Location::new_synthesized(),
        )
    }

    #[test]
    fn installed_givens_reconcile_transitive_outputs_without_changing_ids() {
        let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
        let first = Type::variable_id(0);
        let second = Type::variable_id(1);
        let boolean = Type::primitive::<bool>();
        // The first equality makes the final pair's inputs equal on a later pass.
        inference.given_constraints = vec![
            given(vec![Type::unit()], vec![first]),
            given(vec![Type::unit()], vec![boolean]),
            given(vec![first], vec![second]),
            given(vec![boolean], vec![Type::unit()]),
        ];
        inference.normalize_given_outputs().unwrap();
        assert_eq!(inference.substitute_in_type(first), boolean);
        assert_eq!(inference.substitute_in_type(second), Type::unit());
        assert_eq!(inference.given_constraints.len(), 4);
        assert_eq!(
            inference.given_constraints[0],
            given(vec![Type::unit()], vec![boolean])
        );
        assert_eq!(
            inference.given_constraints[2],
            given(vec![boolean], vec![Type::unit()])
        );
    }

    #[test]
    fn installed_givens_reject_conflicting_unused_outputs() {
        let mut inference = UnifiedTypeInference {
            given_constraints: vec![
                given(vec![Type::unit()], vec![Type::unit()]),
                given(vec![Type::unit()], vec![Type::primitive::<bool>()]),
            ],
            ..Default::default()
        };
        assert!(inference.normalize_given_outputs().is_err());
        assert_eq!(inference.given_constraints.len(), 2);
    }

    #[test]
    fn possible_given_defers_without_binding_independent_inputs() {
        let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
        let unknown = Type::variable_id(0);
        let declared = Type::variable_id(1);
        inference
            .given_constraints
            .push(given(vec![Type::unit(), declared], vec![]));
        assert_eq!(
            inference
                .match_given(
                    trait_id(),
                    &[Type::unit(), unknown],
                    &[],
                    &[],
                    Location::new_synthesized(),
                    Default::default()
                )
                .unwrap(),
            GivenMatch::Deferred
        );
        assert_eq!(inference.substitute_in_type(unknown), unknown);
        assert_eq!(inference.substitute_in_type(declared), declared);
        assert!(!inference.given_used_by(LocalFunctionId::from_index(0), GivenId(0)));
        inference
            .unify_same_type_with_sub_effects(
                unknown,
                Location::new_synthesized(),
                declared,
                Location::new_synthesized(),
            )
            .unwrap();
        let inputs = inference.normalize_types(&[Type::unit(), unknown]);
        assert_eq!(
            inference
                .match_given(
                    trait_id(),
                    &inputs,
                    &[],
                    &[],
                    Location::new_synthesized(),
                    Default::default()
                )
                .unwrap(),
            GivenMatch::Resolved
        );
    }

    #[test]
    fn duplicate_givens_reconcile_every_output_in_both_orders() {
        for reverse in [false, true] {
            let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
            let output = Type::variable_id(0);
            let query_output = Type::variable_id(1);
            inference.given_constraints = vec![
                given(vec![Type::unit()], vec![output]),
                given(vec![Type::unit()], vec![Type::primitive::<bool>()]),
            ];
            if reverse {
                inference.given_constraints.reverse();
            }
            assert_eq!(
                inference
                    .match_given(
                        trait_id(),
                        &[Type::unit()],
                        &[query_output],
                        &[],
                        Location::new_synthesized(),
                        Default::default()
                    )
                    .unwrap(),
                GivenMatch::Resolved
            );
            assert_eq!(
                inference.substitute_in_type(output),
                Type::primitive::<bool>()
            );
            assert_eq!(
                inference.substitute_in_type(query_output),
                Type::primitive::<bool>()
            );
        }
    }

    #[test]
    fn incompatible_duplicate_givens_are_rejected_in_both_orders() {
        for reverse in [false, true] {
            let mut inference = UnifiedTypeInference::new_with_ty_vars(1);
            inference.given_constraints = vec![
                given(vec![Type::unit()], vec![Type::unit()]),
                given(vec![Type::unit()], vec![Type::primitive::<bool>()]),
            ];
            if reverse {
                inference.given_constraints.reverse();
            }
            assert!(
                inference
                    .match_given(
                        trait_id(),
                        &[Type::unit()],
                        &[Type::variable_id(0)],
                        &[],
                        Location::new_synthesized(),
                        Default::default()
                    )
                    .is_err()
            );
        }
    }

    #[test]
    fn exact_given_use_is_attributed_to_its_identity() {
        let mut inference = UnifiedTypeInference {
            given_constraints: vec![
                given(vec![Type::unit()], vec![]),
                given(vec![Type::primitive::<bool>()], vec![]),
            ],
            ..Default::default()
        };
        inference.evidence_uses.enable();
        let origin = inference.evidence_uses.fresh_origin();
        let owner = LocalFunctionId::from_index(0);
        inference.evidence_uses.register(origin, owner);
        assert_eq!(
            inference
                .match_given(
                    trait_id(),
                    &[Type::primitive::<bool>()],
                    &[],
                    &[],
                    Location::new_synthesized(),
                    origin
                )
                .unwrap(),
            GivenMatch::Resolved
        );
        assert!(inference.given_used_by(owner, GivenId(1)));
        assert!(!inference.given_used_by(owner, GivenId(0)));
    }
}
