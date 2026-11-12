// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{
    borrow::Cow,
    collections::hash_map::Entry,
    mem,
    ops::{Deref, DerefMut},
};

use ena::unify::{InPlace, Snapshot};
use itertools::Itertools;
use ustr::Ustr;

use super::{
    constraints::{EffectConstraint, MutConstraint, TypeConstraint},
    effect_solver::{EffectConstraintOrigin, EffectSolver, EffectSolverSnapshot},
    evidence_uses::{EvidenceUses, GivenId},
    expr::TypeInference,
    ground_bounds::is_maximal,
    selection::SelectionStats,
    tables::{Revision, RevisionedConstraints, RevisionedTable},
    type_bounds::{TypeBound, TypeBounds},
};
use crate::{
    FxHashMap, FxHashSet,
    compiler::error::{
        ADTAccessType, InfiniteTypeKind, InternalCompilationError, InvalidRecordFieldContext,
        MutabilityMustBeContext, MutabilityMustBeWhat,
    },
    hir::{NodeArena, value::LiteralValue},
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
        trait_solver::{ConstraintAssumptions, TraitSolver, output_effect_fits},
        r#type::{
            FnArgType, FnType, SubscriptMemberType, SubscriptResultConvention, SubscriptType,
            TyVarKey, Type, TypeInstSubst, TypeKind, TypeVar,
        },
        type_inference::substitution::InstSubst,
        type_like::{TypeLike, instantiate_types},
        type_mapper::{BitmapInstantiationMapper, EffectErasingMapper, TypeMapper},
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
    bounds: TypeBounds,
    bottom_sources: FxHashMap<Type, Location>,
    evidence_uses: EvidenceUses,
    ty_unification_table: Snapshot<InPlace<TyVarKey>>,
    mut_unification_table: Snapshot<InPlace<MutVarKey>>,
    effects: EffectSolverSnapshot,
    remaining_ty_constraints_len: usize,
    obligations_len: usize,
    expanded_value_applications_len: usize,
}

/// Equality state, retained bounds and public obligations during inference.
#[derive(Default, Debug)]
pub struct UnifiedTypeInference {
    pub(super) selection_stats: SelectionStats,
    pub(super) constraints_normalized_at: Option<(Revision, Revision, Revision, Revision)>,
    /// Only immutable successful pairs; deliberately survives speculative rollback.
    pub(super) checked_bounds: FxHashSet<(Type, Type)>,
    pub(super) bounds: TypeBounds,
    pub(super) bottom_sources: FxHashMap<Type, Location>,
    pub(super) publication_inputs: Vec<Type>,
    ty_coverage_constraints: Vec<(Location, Type, Vec<LiteralValue>)>,
    pub(super) given_constraints: Vec<PubTypeConstraint>,
    pub(super) declared_generics: Vec<Type>,
    pub(super) evidence_uses: EvidenceUses,
    pub(super) ty_unification_table: RevisionedTable<TyVarKey>,
    /// Remaining constraints that cannot be solved, will be part of the resulting type scheme
    pub(super) remaining_ty_constraints: RevisionedConstraints,
    pub(super) mut_unification_table: RevisionedTable<MutVarKey>,
    pub(super) effects: EffectSolver,
    /// Constraints of the implementations that resolved trait applications, still to solve.
    obligations: Vec<PubTypeConstraint>,
    /// Inputs of the `Value` applications whose implementation's prerequisites are already among
    /// the obligations: an equal application reuses that expansion, so that recursive `Value`
    /// impls expand once. This guards expansion only; it proves nothing.
    expanded_value_applications: Vec<Vec<Type>>,
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
/// The outputs of the equal trait applications of one constraint pass.
struct HaveTraitOutputs {
    types: Vec<Type>,
    /// Per output effect, the first one still to learn.
    learned: Vec<Option<(EffType, Location)>>,
    /// Per output effect, the fixed bounds.
    bounds: Vec<Vec<(EffType, Location)>>,
    span: Location,
    /// The rank of the application among those of the pass.
    order: usize,
}

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

    pub(super) fn deduplicate_constraints_in_place(
        &mut self,
        constraints: &mut Vec<PubTypeConstraint>,
    ) {
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
        polarities: &dyn Fn(TraitId) -> Vec<EffectPolarity>,
    ) -> Result<(), InternalCompilationError> {
        loop {
            let before = constraints.clone();
            self.aggregate_constraints_for_pass(constraints.iter(), polarities)?;
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
    fn normalize_given_outputs(
        &mut self,
        polarities: &dyn Fn(TraitId) -> Vec<EffectPolarity>,
    ) -> Result<(), InternalCompilationError> {
        let mut givens = mem::take(&mut self.given_constraints);
        let result = (|| {
            if givens.len() > 1 {
                loop {
                    let before = givens.clone();
                    self.aggregate_constraints_for_pass(givens.iter(), polarities)?;
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
    /// The variables that the written generic parameters currently stand for.
    pub(crate) fn declared_generic_roots(&mut self) -> Vec<Type> {
        if self.declared_generics.is_empty() {
            return Vec::new();
        }
        let generics = self.declared_generics.clone();
        self.substitute_in_types(&generics)
            .into_iter()
            .filter(|ty| ty.data().is_variable())
            .unique()
            .collect()
    }

    /// Whether `roots`, as given by [`Self::declared_generic_roots`], are still distinct variables
    /// and no subtype bound will restrict them to a shape.
    pub(crate) fn declared_generics_intact(&mut self, roots: &[Type]) -> bool {
        if roots.is_empty() {
            return true;
        }
        if self.propagate_type_bounds().is_err() {
            return false;
        }
        let roots = self.substitute_in_types(roots);
        if !roots.iter().all(|ty| ty.data().is_variable()) || !roots.iter().all_unique() {
            return false;
        }
        let bounds = self.bounds.relations().copied().collect::<Vec<_>>();
        bounds.into_iter().all(|bound| {
            let lower = self.substitute_in_type(bound.lower);
            let upper = self.substitute_in_type(bound.upper);
            let restricts = |generic: Type, other: Type| {
                roots.contains(&generic) && {
                    let other = other.data();
                    !other.is_variable() && !other.is_never()
                }
            };
            !restricts(lower, upper) && !restricts(upper, lower)
        })
    }

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
            bounds: self.bounds.clone(),
            bottom_sources: self.bottom_sources.clone(),
            evidence_uses: self.evidence_uses.clone(),
            ty_unification_table: self.ty_unification_table.snapshot(),
            mut_unification_table: self.mut_unification_table.snapshot(),
            effects: self.effects.snapshot(),
            remaining_ty_constraints_len: self.remaining_ty_constraints.len(),
            obligations_len: self.obligations.len(),
            expanded_value_applications_len: self.expanded_value_applications.len(),
        }
    }

    pub(crate) fn rollback_to(&mut self, snapshot: UnifiedTypeInferenceSnapshot) {
        self.bounds = snapshot.bounds;
        self.bottom_sources = snapshot.bottom_sources;
        self.evidence_uses = snapshot.evidence_uses;
        self.ty_unification_table
            .rollback_to(snapshot.ty_unification_table);
        self.mut_unification_table
            .rollback_to(snapshot.mut_unification_table);
        self.effects.rollback_to(snapshot.effects);
        self.remaining_ty_constraints
            .truncate(snapshot.remaining_ty_constraints_len);
        self.obligations.truncate(snapshot.obligations_len);
        self.expanded_value_applications
            .truncate(snapshot.expanded_value_applications_len);
    }

    pub fn unify_type_inference(
        ty_inf: TypeInference,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<Self, InternalCompilationError> {
        let TypeInference {
            given_constraints,
            declared_generics,
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
            selection_stats: SelectionStats::default(),
            constraints_normalized_at: None,
            checked_bounds: FxHashSet::default(),
            bounds: TypeBounds::default(),
            bottom_sources: FxHashMap::default(),
            publication_inputs: Vec::new(),
            ty_coverage_constraints,
            given_constraints,
            declared_generics,
            evidence_uses,
            ty_unification_table: ty_unification_table.into(),
            remaining_ty_constraints: RevisionedConstraints::default(),
            mut_unification_table: mut_unification_table.into(),
            effects,
            obligations: vec![],
            expanded_value_applications: vec![],
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

        // Equality and directional constraints share generation, but unknown
        // subtype endpoints remain in the bounds graph until selection.
        for constraint in ty_constraints {
            match constraint {
                TypeConstraint::Pub(cst) => {
                    if matches!(cst, PubTypeConstraint::VariantPayloadLayout { .. }) {
                        variant_layout_constraints.push(cst);
                    } else {
                        remaining_constraints.push(cst);
                    }
                }
                constraint => unified_ty_inf.unify_type_relation(constraint)?,
            }
        }
        unified_ty_inf.propagate_type_bounds()?;

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
                    &current,
                    current_span,
                    &expected,
                    expected_span,
                )?,
            }
        }

        unified_ty_inf.normalize_given_outputs(&|id| trait_solver.output_effect_polarities(id))?;

        // Bounds and public constraints share one fixed point. Trait outputs
        // remain blockers until that pass has either resolved or deferred them.
        *unified_ty_inf.remaining_ty_constraints = remaining_constraints;
        unified_ty_inf.resolve_remaining_constraints_to_fixed_point(trait_solver, arena)?;
        let mut remaining_constraints = mem::take(&mut *unified_ty_inf.remaining_ty_constraints);

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
        unified_ty_inf.effects.expand_deferred_inclusions()?;

        // FIXME: think whether we should have an intermediate struct without the remaining_constraints in it.
        *unified_ty_inf.remaining_ty_constraints = remaining_constraints;
        Ok(unified_ty_inf)
    }

    /// Coverage needs the selected scrutinee type, including upper-only bounds
    /// such as a generic input matched against boolean literals. Keep these
    /// immutable checks until publication has resolved those bounds.
    pub(super) fn validate_type_coverage(&mut self) -> Result<(), InternalCompilationError> {
        for (span, ty, values) in self.ty_coverage_constraints.clone() {
            let ty = self.normalize_type(ty);
            let all_values = ty.data().all_values().ok_or_else(|| {
                internal_compilation_error!(TypeValuesCannotBeEnumerated { span, ty })
            })?;
            if all_values.iter().any(|value| !values.contains(value)) {
                return Err(internal_compilation_error!(NonExhaustivePattern {
                    span,
                    ty
                }));
            }
        }
        Ok(())
    }

    /// Solve a type relation, a constraint other than a public one.
    fn unify_type_relation(
        &mut self,
        constraint: TypeConstraint,
    ) -> Result<(), InternalCompilationError> {
        use TypeConstraint::*;
        match constraint {
            SameType {
                current,
                current_span,
                expected,
                expected_span,
            } => self.unify_sub_or_same_type(
                current,
                current_span,
                expected,
                expected_span,
                SubOrSameType::SameType,
                &mut FxHashSet::default(),
            ),
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

    pub(crate) fn unify_same_type(
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
            (Never, Variable(_)) if sub_or_same == SubType => {
                // Bottom imposes no restriction. Preserve only the provenance
                // needed by eligible fallback; do not propagate trivial edges.
                self.bottom_sources
                    .entry(expected_ty)
                    .or_insert(current_span);
                Ok(())
            }
            (_, Variable(var)) if sub_or_same == SubType && is_maximal(current_ty) => {
                // This is incorporation, not selection: no other supertype is
                // possible, even after instantiating invariant named arguments.
                self.unify_type_variable(
                    var,
                    expected_span,
                    current_ty,
                    current_span,
                    true,
                    SameType,
                )
            }
            (Variable(_), _) | (_, Variable(_))
                if sub_or_same == SubType && expected_ty != Type::never() =>
            {
                self.bounds.insert(TypeBound {
                    lower: current_ty,
                    lower_span: current_span,
                    upper: expected_ty,
                    upper_span: expected_span,
                });
                Ok(())
            }
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
                        expected_span,
                        cur_arg.mut_ty,
                        current_span,
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
                    self.unify_same_effect(
                        &cur.effects,
                        current_span,
                        &exp.effects,
                        expected_span,
                    )?;
                } else {
                    // Covariant effects.
                    self.add_effect_inclusion(
                        &cur.effects,
                        current_span,
                        &exp.effects,
                        expected_span,
                    )?;
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
                        expected_span,
                        cur_arg.mut_ty,
                        current_span,
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
                // An exposed mutable result permits replacement of the stored
                // value, so its complete type (including nested effects) must
                // agree. Forgetting mutable access still permits covariance.
                // Unlike argument write-back, this depends on the EXPECTED
                // capability: it controls the writes the consumer may perform.
                let result_relation = if exp.mut_member.is_some() {
                    SameType
                } else {
                    sub_or_same
                };
                self.unify_sub_or_same_type(
                    cur.ret,
                    current_span,
                    exp.ret,
                    expected_span,
                    result_relation,
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
                    self.unify_same_effect(&cur_eff, current_span, &exp_eff, expected_span)?;
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
        polarities: &dyn Fn(TraitId) -> Vec<EffectPolarity>,
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
            // Applications with equal trait and inputs in one scope are equal, except that
            // their fixed output effects are bounds, combined as by the constraint merge.
            let mut bounds = vec![Vec::new(); output_effs.len()];
            for (given, given_outputs, given_effects) in matches {
                for (actual, expected) in output_tys.iter().zip(&given_outputs) {
                    self.unify_same_type_with_sub_effects(*actual, span, *expected, span)?;
                }
                for ((actual, expected), bounds) in
                    output_effs.iter().zip(given_effects).zip(&mut bounds)
                {
                    if expected.has_variables() {
                        self.unify_same_effect(actual, span, &expected, span)?;
                    } else {
                        bounds.push((expected, span));
                    }
                }
                self.evidence_uses.record(origin, given);
            }
            // Polarities matter only to combine bounds, or to fit a fixed request to a bound.
            let mut trait_polarities = None;
            for (index, (actual, bounds)) in output_effs.iter().zip(&bounds).enumerate() {
                let mut lookup = || {
                    trait_polarities
                        .get_or_insert_with(|| polarities(trait_id))
                        .get(index)
                        .copied()
                        .unwrap_or(EffectPolarity::Invariant)
                };
                // A single bound needs no polarity.
                let combining = if bounds.len() > 1 {
                    lookup()
                } else {
                    EffectPolarity::Invariant
                };
                let Some((bound, _)) = self.combine_effect_bounds(bounds, combining)? else {
                    continue;
                };
                // A fixed request, such as a callee's `where` clause, is itself a bound that the
                // evidence must fit; an effect still being inferred takes the evidence's bound.
                if !actual.has_variables() && *actual != bound {
                    if output_effect_fits(&bound, actual, lookup()) {
                        continue;
                    }
                }
                self.unify_same_effect(actual, span, &bound, span)?;
            }
            return Ok(GivenMatch::Resolved);
        }
        for given_inputs in potential_inputs {
            // Probe compatibility without learning input equalities from evidence.
            // In particular Convert<A, ?b> must not force ?b to a given's B.
            let declared_roots = self.declared_generic_roots();
            let snapshot = self.snapshot();
            let compatible = input_tys
                .iter()
                .zip(&given_inputs)
                .all(|(actual, expected)| {
                    self.unify_same_type_with_sub_effects(*actual, span, *expected, span)
                        .is_ok()
                })
                // A written generic stands for every type, so it can never become a query's type.
                && self.declared_generics_intact(&declared_roots);
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
            &|id| trait_solver.output_effect_polarities(id),
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
                // The compiler provides the dictionary, but its members may have source impls
                // that restrict their effects.
                self.check_effects_through_derivation(
                    trait_id,
                    &input_tys,
                    span,
                    trait_solver,
                    arena,
                )?;
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
        let structural_count = ordered_constraints.partition_point(|(_, constraint)| {
            constraint_solve_priority(constraint, trait_solver) < 10
        });
        let mut deferred_structure = false;
        let mut retry_structure = false;
        for (position, &(constraint_index, constraint)) in ordered_constraints.iter().enumerate() {
            // A structural constraint can be deferred before another one reveals its receiver,
            // such as a tuple index before the `Repr` of a named type. Retry it before trait
            // improvement can specialize its still-unrelated output.
            // The enclosing fixed-point loop resumes us with the remaining constraints.
            if position == structural_count && retry_structure {
                new_constraints.extend(
                    ordered_constraints[position..]
                        .iter()
                        .map(|(_, constraint)| (*constraint).clone()),
                );
                break;
            }
            let unified_constraint = self.unify_pub_constraint(
                constraint,
                ConstraintAssumptions::excluding(constraints, constraint_index),
                &is_ty_adt,
                trait_solver,
                arena,
            )?;
            if let Some(new_constraint) = unified_constraint {
                deferred_structure |= position < structural_count;
                new_constraints.push(new_constraint);
            } else if position < structural_count && deferred_structure {
                retry_structure = true;
            }
            new_constraints.append(&mut self.obligations);
        }
        Ok(new_constraints)
    }

    /// Aggregate same-family public constraints before running one unification pass.
    ///
    /// Equal trait applications have the same outputs, so their output types and the output
    /// effects still to learn are equated. Fixed output effects are bounds: they are combined by
    /// their `polarities` and the effects to learn take the combined bound, whatever their order.
    ///
    /// Applications that differ only by effects have the same implementation, as effects do not
    /// select one: their output types have the same structure, and effects of their own, see
    /// [`Self::unify_same_structures`].
    pub(super) fn aggregate_constraints_for_pass<'a>(
        &mut self,
        constraints: impl IntoIterator<Item = &'a PubTypeConstraint>,
        polarities: &dyn Fn(TraitId) -> Vec<EffectPolarity>,
    ) -> Result<ConstraintPassAggregation<'a>, InternalCompilationError> {
        let constraints = constraints.into_iter();
        let mut aggregation = ConstraintPassAggregation::with_capacity(constraints.size_hint().0);
        let mut projection_indices = FxHashMap::<(Type, Ustr), usize>::default();
        let mut have_traits: FxHashMap<(TraitId, Vec<Type>), HaveTraitOutputs> =
            FxHashMap::default();
        // The applications that have output types, by trait and inputs without their effects,
        // and whether two of them differ only by effects.
        let mut output_structures: FxHashSet<(TraitId, Vec<Type>)> = FxHashSet::default();
        let mut differ_only_by_effects = false;

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
                    let site = span.use_site;
                    let order = have_traits.len();
                    let outputs = match have_traits.entry(key) {
                        Entry::Occupied(entry) => {
                            let outputs = entry.into_mut();
                            assert_eq!(outputs.types.len(), output_types.len());
                            for (expected, actual) in outputs.types.iter().zip(&output_types) {
                                self.unify_same_type(*actual, site, *expected, outputs.span)?;
                            }
                            outputs
                        }
                        Entry::Vacant(entry) => {
                            if !output_types.is_empty() {
                                let (trait_id, input_types) = entry.key();
                                let erased =
                                    instantiate_types(input_types, &mut EffectErasingMapper);
                                differ_only_by_effects |=
                                    !output_structures.insert((*trait_id, erased));
                            }
                            entry.insert(HaveTraitOutputs {
                                types: output_types,
                                learned: vec![None; output_effects.len()],
                                bounds: vec![Vec::new(); output_effects.len()],
                                span: site,
                                order,
                            })
                        }
                    };
                    assert_eq!(outputs.learned.len(), output_effects.len());
                    for (index, effect) in output_effects.into_iter().enumerate() {
                        if !effect.has_variables() {
                            outputs.bounds[index].push((effect, site));
                        } else if let Some((learned, learned_site)) = &outputs.learned[index] {
                            self.unify_same_effect(&effect, site, learned, *learned_site)?;
                        } else {
                            outputs.learned[index] = Some((effect, site));
                        }
                    }
                    aggregation.constraints.push(Cow::Borrowed(constraint));
                }
            }
        }
        if differ_only_by_effects {
            let applications = have_traits
                .iter()
                .filter(|(_, outputs)| !outputs.types.is_empty())
                .sorted_by_key(|(_, outputs)| outputs.order)
                .map(|((trait_id, inputs), outputs)| {
                    (*trait_id, &inputs[..], &outputs.types[..], outputs.span)
                })
                .collect::<Vec<_>>();
            self.unify_same_structures(&applications)?;
        }
        for ((trait_id, _), outputs) in have_traits {
            if outputs.bounds.iter().all(Vec::is_empty) {
                continue;
            }
            let polarities = polarities(trait_id);
            for (index, (learned, bounds)) in
                outputs.learned.into_iter().zip(outputs.bounds).enumerate()
            {
                let polarity = polarities
                    .get(index)
                    .copied()
                    .unwrap_or(EffectPolarity::Invariant);
                let Some(bound) = self.combine_effect_bounds(&bounds, polarity)? else {
                    continue;
                };
                if let Some((learned, learned_site)) = learned {
                    self.unify_same_effect(&learned, learned_site, &bound.0, bound.1)?;
                }
            }
        }
        Ok(aggregation)
    }

    /// Give the same structure to the output types of the trait applications whose inputs have
    /// the same structure, the effects in them staying unrelated. Each application is its
    /// trait, its input types, its output types and its site.
    ///
    /// Two types have the same structure when they are equal once their effects are removed.
    /// Such applications have one implementation, as effects do not select one, so their outputs
    /// are its output types at different effects. This holds again for the applications that
    /// take these outputs as inputs, so the relation is closed under the applications.
    ///
    /// The structures are solved apart from the types. Each type is read without its effects, a
    /// twin variable standing for each of its unknown parts, and the readings of the outputs of
    /// applications whose inputs have the same reading are unified as types are: this refuses
    /// the structures that no type has, and accepts the recursive ones that a type can have. A
    /// variable whose twin is then known takes a copy of that structure, see
    /// [`Self::structure_copy`]. Nothing is kept from one pass to the next, as the applications
    /// relate these copies again.
    fn unify_same_structures(
        &mut self,
        applications: &[(TraitId, &[Type], &[Type], Location)],
    ) -> Result<(), InternalCompilationError> {
        let mut reading = StructureReading {
            inference: self,
            twins: FxHashMap::default(),
            read: Vec::new(),
        };
        let structures = applications
            .iter()
            .map(|(trait_id, inputs, outputs, site)| {
                let inputs = reading.read(inputs, *site);
                (*trait_id, inputs, reading.read(outputs, *site), *site)
            })
            .collect::<Vec<_>>();
        let read = reading.read;
        // Unifying outputs can give two other applications inputs of the same reading, which
        // were visited before if the applications do not come in the order of their dependencies.
        loop {
            let mut firsts: FxHashMap<(TraitId, Vec<Type>), usize> = FxHashMap::default();
            let mut progress = false;
            for (index, (trait_id, inputs, outputs, site)) in structures.iter().enumerate() {
                let first = match firsts.entry((*trait_id, self.normalize_types(inputs))) {
                    Entry::Occupied(first) => *first.get(),
                    Entry::Vacant(first) => {
                        first.insert(index);
                        continue;
                    }
                };
                let (_, _, first_outputs, first_site) = &structures[first];
                for (first_output, output) in first_outputs.iter().zip(outputs) {
                    let first_output = self.normalize_type(*first_output);
                    let output = self.normalize_type(*output);
                    if first_output != output {
                        self.unify_same_type(first_output, *first_site, output, *site)?;
                        progress = true;
                    }
                }
            }
            if !progress {
                break;
            }
        }
        for (var, twin, site) in read {
            let structure = self.normalize_type(Type::variable(twin));
            if let Some(copy) = self.structure_copy(structure) {
                self.unify_same_type(Type::variable(var), site, copy, site)?;
            }
        }
        Ok(())
    }

    /// The most general type of a structure read by [`StructureReading`], if it is known and
    /// finite: the structure with a new effect at each place, and a new type variable for each
    /// part that is not copied.
    ///
    /// An unknown part is not copied, and neither is a recursive one: it stands for an infinite
    /// tree, whose effects can repeat with any period when it has some, so a copy with a finite
    /// number of effects may not be the most general. Such a part stays a variable that the
    /// pairs keep checking against the structure, until its own implementation or its uses give
    /// its type.
    fn structure_copy(&mut self, structure: Type) -> Option<Type> {
        let mut kind = { structure.data().clone() };
        if kind.as_variable().is_some() || structure.is_global_recursive() {
            return None;
        }
        kind.for_each_inner_type_mut(|part| {
            *part = match self.structure_copy(*part) {
                Some(copy) => copy,
                None => Type::variable(self.fresh_type_var()),
            };
        });
        Some(kind.map(&mut FreshEffects { inference: self }))
    }

    /// Combine fixed bounds on one output effect: an implementation's performed effect fits all
    /// of them, so they intersect; a received one includes all of them, so they unite; invariant
    /// ones must be equal. The site is that of a bound equal to the result, if any.
    fn combine_effect_bounds(
        &mut self,
        bounds: &[(EffType, Location)],
        polarity: EffectPolarity,
    ) -> Result<Option<(EffType, Location)>, InternalCompilationError> {
        let Some((first, first_site)) = bounds.first() else {
            return Ok(None);
        };
        let mut combined = first.clone();
        for (bound, site) in &bounds[1..] {
            combined = match polarity {
                EffectPolarity::Positive => combined.difference(&combined.difference(bound)),
                EffectPolarity::Negative => combined.union(bound),
                EffectPolarity::Invariant => {
                    self.unify_same_effect(bound, *site, first, *first_site)?;
                    combined
                }
            };
        }
        let site = bounds
            .iter()
            .find(|(bound, _)| *bound == combined)
            .map_or(*first_site, |(_, site)| *site);
        Ok(Some((combined, site)))
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
            &existing.effects,
            existing_span,
            &incoming.effects,
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

    /// Derivation erases the effects of its input, so that its dictionaries can be shared. An impl
    /// from source that a derivation needs for a member may however require something of these
    /// effects: apply such impls here, where the real effects are known. A derivable trait has no
    /// output and a member's impl cannot perform an effect its trait does not expose, so what
    /// remains is valid for every effect.
    fn check_effects_through_derivation(
        &mut self,
        trait_id: TraitId,
        input_tys: &[Type],
        span: Location,
        trait_solver: &mut TraitSolver<'_>,
        arena: &mut NodeArena,
    ) -> Result<(), InternalCompilationError> {
        if input_tys.iter().all(|ty| ty.inner_effect_vars().is_empty()) {
            return Ok(());
        }
        let trait_def = trait_solver.trait_def(trait_id);
        if trait_def.derivers.is_empty()
            || trait_def.output_type_count() != 0
            || !trait_def.output_effect_names.is_empty()
        {
            return Ok(());
        }
        let derivers = trait_def.derivers.clone();
        let members_of = |ty: Type, trait_solver: &TraitSolver<'_>| {
            derivers
                .iter()
                .flat_map(|deriver| deriver.derived_members(ty, trait_solver))
                .collect::<Vec<_>>()
        };
        let mut seen = FxHashSet::default();
        let mut pending = input_tys
            .iter()
            .flat_map(|ty| members_of(*ty, trait_solver))
            .collect::<Vec<_>>();
        while let Some(ty) = pending.pop() {
            if ty.inner_effect_vars().is_empty() || !seen.insert(ty) {
                continue;
            }
            let member = [ty];
            if trait_solver
                .resolve_application_symbolically(trait_id, &member, &[], &[], span)?
                .is_some()
            {
                self.resolve_trait_application(
                    trait_id,
                    &member,
                    &[],
                    &[],
                    span,
                    trait_solver,
                    arena,
                )?;
            } else {
                pending.extend(members_of(ty, trait_solver));
            }
        }
        Ok(())
    }

    /// Whether a `Value` application with these normalized inputs is already expanded.
    fn is_expanded_value_application(&mut self, inputs: &[Type]) -> bool {
        // Normalization does not touch the table, so set it aside rather than copy its rows.
        let expanded = mem::take(&mut self.expanded_value_applications);
        let found = expanded
            .iter()
            .any(|expanded| self.normalize_types(expanded) == inputs);
        self.expanded_value_applications = expanded;
        found
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
        // `Value` has no outputs: an application equal to one already expanded has nothing to add.
        let value_application = (trait_id == trait_solver.std_trait_id(VALUE_TRAIT_NAME))
            .then(|| self.normalize_types(input_tys));
        if let Some(inputs) = &value_application
            && self.is_expanded_value_application(inputs)
        {
            return Ok(());
        }
        let (impl_output_tys, impl_output_effs) = match trait_solver
            .resolve_application_symbolically(trait_id, input_tys, output_tys, output_effs, span)?
        {
            Some(application) => {
                if let Some(inputs) = value_application {
                    self.expanded_value_applications.push(inputs);
                }
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
                for ty in &application.input_tys {
                    add_fresh_vars(ty.inner_ty_vars(), ty.inner_effect_vars(), self);
                }
                let mut mapper = BitmapInstantiationMapper::new(&subst);
                // Selection saw the inputs in a scratch solver: their effects must really fit the
                // impl, which may require two of them to be equal.
                for (imp_input_ty, input_ty) in application.input_tys.iter().zip(input_tys) {
                    let imp_input_ty = imp_input_ty.map(&mut mapper);
                    self.unify_same_type_with_sub_effects(imp_input_ty, span, *input_ty, span)?;
                }
                let impl_output_tys = instantiate_types(&application.output_tys, &mut mapper);
                let impl_output_effs = application
                    .output_effs
                    .iter()
                    .map(|eff| mapper.map_effect_type(eff))
                    .collect::<Vec<_>>();
                // What the impl requires, this application must provide: report it here.
                let obligations = application
                    .obligations
                    .iter()
                    .map(|obligation| {
                        obligation
                            .map(&mut mapper)
                            .instantiate_location_cloned(span)
                    })
                    .collect::<Vec<_>>();
                self.obligations.extend(obligations);
                (impl_output_tys, impl_output_effs)
            }
            None => {
                self.check_effects_through_derivation(
                    trait_id,
                    input_tys,
                    span,
                    trait_solver,
                    arena,
                )?;
                // `Value` has no outputs, and its effects are only known once inference is over:
                // select it here by the types, and check its effects when its dictionary is
                // elaborated, where open effects have taken their least solution.
                let erased_input_tys;
                let input_tys = if trait_id == trait_solver.std_trait_id(VALUE_TRAIT_NAME)
                    && input_tys
                        .iter()
                        .any(|ty| !ty.inner_effect_vars().is_empty())
                {
                    erased_input_tys = instantiate_types(input_tys, &mut EffectErasingMapper);
                    &erased_input_tys[..]
                } else {
                    input_tys
                };
                trait_solver.solve_application_outputs(
                    trait_id,
                    input_tys,
                    output_tys,
                    output_effs,
                    span,
                    arena,
                )?
            }
        };
        assert_eq!(output_tys.len(), impl_output_tys.len());
        // The output types are those of the implementation, effects included: unlike its
        // output effects, they have no polarity by which a request could differ from them.
        for (cur_ty, exp_ty) in output_tys.iter().zip(impl_output_tys.iter()) {
            self.unify_same_type(*cur_ty, span, *exp_ty, span)?;
        }
        assert_eq!(output_effs.len(), impl_output_effs.len());
        let polarities = trait_solver.output_effect_polarities(trait_id);
        for (index, ((cur_eff, exp_eff), polarity)) in output_effs
            .iter()
            .zip(impl_output_effs.iter())
            .zip(polarities)
            .enumerate()
        {
            let origin = trait_solver.output_effect_origin(trait_id, index, span);
            self.relate_trait_output_effect(exp_eff, cur_eff, polarity, span, origin)?;
        }
        Ok(())
    }

    /// Relate an implementation's output effect to the requested one by the output's polarity:
    /// an effect the methods perform may be smaller than requested, one they receive larger.
    pub(crate) fn relate_trait_output_effect(
        &mut self,
        impl_eff: &EffType,
        requested_eff: &EffType,
        polarity: EffectPolarity,
        span: Location,
        origin: EffectConstraintOrigin,
    ) -> Result<(), InternalCompilationError> {
        match polarity {
            EffectPolarity::Positive => self.effects.add_effect_inclusion_with_origin(
                impl_eff,
                span,
                requested_eff,
                span,
                origin,
            ),
            EffectPolarity::Negative => self.effects.add_effect_inclusion_with_origin(
                requested_eff,
                span,
                impl_eff,
                span,
                origin,
            ),
            EffectPolarity::Invariant => self.effects.unify_same_effect_with_origin(
                impl_eff,
                span,
                requested_eff,
                span,
                origin,
            ),
        }
    }

    /// Make current and target the same effect type.
    pub fn unify_same_effect(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.effects
            .unify_same_effect(current, current_span, target, target_span)
    }

    pub fn add_effect_inclusion(
        &mut self,
        current: &EffType,
        current_span: Location,
        target: &EffType,
        target_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.effects
            .add_effect_inclusion(current, current_span, target, target_span)
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
            self.unify_same_effect(&current.effects, current_span, &target.effects, target_span)
        } else {
            self.add_effect_inclusion(&current.effects, current_span, &target.effects, target_span)
        }
    }

    pub fn finalize_effects(&mut self) -> Result<(), InternalCompilationError> {
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

    /// Fix the effect variables that nothing outside the inferred code determines at their
    /// least solution.
    ///
    /// The determined variables are the least set that holds `observable`, the variables of
    /// the signatures; the outputs of a requirement whose inputs are all determined, as a
    /// caller's implementation gives them; and what a requirement on the structure of a type
    /// names. Variables are the same up to the equalities that the solver holds; a bound does
    /// not determine.
    ///
    /// A variable that is not determined and that an input of a requirement names is
    /// ambiguous: no call says what it is. It takes its least solution, with the variables
    /// that no requirement names, unless it is a written generic, which is an error. Once it
    /// has its solution, the outputs of its requirement are determined in turn, so an output
    /// is only given a solution when requirements determine one another in a circle.
    pub(crate) fn minimize_unobservable_effects(
        &mut self,
        observable: FxHashSet<EffectVar>,
    ) -> Result<(), InternalCompilationError> {
        self.normalize_remaining_constraints();
        // Per requirement on types still to know, the classes of its inputs and of its outputs.
        let mut applications = Vec::new();
        for constraint in self.remaining_ty_constraints.iter() {
            if constraint.inner_ty_vars().is_empty() {
                continue;
            }
            let mut inputs = FxHashSet::default();
            let mut outputs = FxHashSet::default();
            match constraint {
                PubTypeConstraint::HaveTrait {
                    input_tys,
                    output_tys,
                    output_effs,
                    ..
                } => {
                    for ty in input_tys {
                        ty.fill_with_inner_effect_vars(&mut inputs);
                    }
                    for ty in output_tys {
                        ty.fill_with_inner_effect_vars(&mut outputs);
                    }
                    for eff in output_effs {
                        eff.fill_with_inner_effect_vars(&mut outputs);
                    }
                }
                _ => constraint.fill_with_inner_effect_vars(&mut outputs),
            }
            let inputs = inputs.into_iter().sorted().collect::<Vec<_>>();
            applications.push((inputs, outputs, constraint.use_site()));
        }
        for (inputs, outputs, _) in &mut applications {
            for var in inputs.iter_mut() {
                *var = self.effects.class_root(*var);
            }
            *outputs = outputs
                .iter()
                .map(|var| self.effects.class_root(*var))
                .collect();
        }
        // The variables that are determined, or ambiguous with their solution chosen.
        let mut known = FxHashSet::default();
        for var in &observable {
            known.insert(self.effects.class_root(*var));
        }
        let mut ambiguous = FxHashSet::default();
        loop {
            loop {
                let count = known.len();
                for (inputs, outputs, _) in &applications {
                    if inputs.iter().all(|var| known.contains(var)) {
                        known.extend(outputs.iter().copied());
                    }
                }
                if known.len() == count {
                    break;
                }
            }
            // The inputs still unknown: those that no requirement gives, or all of them if
            // requirements only give them to one another.
            let mut pending = Vec::new();
            for (inputs, _, site) in &applications {
                for var in inputs {
                    if !known.contains(var) && !pending.iter().any(|(other, _)| other == var) {
                        pending.push((*var, *site));
                    }
                }
            }
            if pending.is_empty() {
                break;
            }
            let given = |var: &EffectVar| {
                applications
                    .iter()
                    .any(|(_, outputs, _)| outputs.contains(var))
            };
            if pending.iter().any(|(var, _)| !given(var)) {
                pending.retain(|(var, _)| !given(var));
            }
            for (var, site) in pending {
                if let Some(name) = self.effects.rigid_name(var) {
                    return Err(internal_compilation_error!(AmbiguousEffectGeneric {
                        name,
                        span: site,
                    }));
                }
                ambiguous.insert(var);
                known.insert(var);
            }
        }
        let determined = known
            .into_iter()
            .filter(|var| !ambiguous.contains(var))
            .collect();
        self.effects.minimize_except(&determined)
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
    /// [`Self::finalize_effects`].
    pub(crate) fn effects_finalized(&self) -> bool {
        self.effects.is_finalized()
    }

    /// Return to reading effects as before [`Self::finalize_effects`], for a
    /// solver whose inference goes on after a query read its published effects.
    pub(crate) fn restore_effects_finalized(&mut self, finalized: bool) {
        self.effects.set_finalized(finalized);
    }
}

/// Reads the structure of types for [`UnifiedTypeInference::unify_same_structures`]: the types
/// without their effects, a twin variable standing for each type variable.
struct StructureReading<'a> {
    inference: &'a mut UnifiedTypeInference,
    twins: FxHashMap<TypeVar, TypeVar>,
    /// Each variable read, its twin, and the site of the types that first held it.
    read: Vec<(TypeVar, TypeVar, Location)>,
}

impl StructureReading<'_> {
    fn read(&mut self, tys: &[Type], site: Location) -> Vec<Type> {
        let tys = self.inference.normalize_types(tys);
        let read = self.read.len();
        let tys = instantiate_types(&tys, self);
        for (_, _, read_site) in &mut self.read[read..] {
            *read_site = site;
        }
        tys
    }
}

impl TypeMapper for StructureReading<'_> {
    fn map_type(&mut self, ty: Type) -> Type {
        let var = { ty.data().as_variable().copied() };
        let Some(var) = var else {
            return ty;
        };
        let twin = *self.twins.entry(var).or_insert_with(|| {
            let twin = self.inference.fresh_type_var();
            self.read.push((var, twin, Location::new_synthesized()));
            twin
        });
        Type::variable(twin)
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        mut_ty
    }

    fn map_effect_type(&mut self, _eff_ty: &EffType) -> EffType {
        EffType::empty()
    }
}

/// Gives a new effect to each effect place of one type constructor, leaving its parts as they
/// are, for [`UnifiedTypeInference::structure_copy`].
struct FreshEffects<'a> {
    inference: &'a mut UnifiedTypeInference,
}

impl TypeMapper for FreshEffects<'_> {
    fn map_type(&mut self, ty: Type) -> Type {
        ty
    }

    fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
        mut_ty
    }

    fn map_effect_type(&mut self, _eff_ty: &EffType) -> EffType {
        EffType::single_variable(self.inference.fresh_effect_var())
    }

    fn affects_type(&mut self, _ty: Type) -> bool {
        false
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
        PubTypeConstraint::HaveTrait { trait_id, .. }
            if *trait_id == trait_solver.std_trait_id(REPR_TRAIT_NAME) =>
        {
            1
        }
        PubTypeConstraint::ProjectionSubscriptIs { .. } => 5,
        PubTypeConstraint::VariantPayloadLayout { .. } => 95,
        PubTypeConstraint::HaveTrait {
            output_tys,
            output_effs,
            ..
        } if !output_tys.is_empty() || !output_effs.is_empty() => 10,
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

    #[test]
    fn subscript_mutable_results_preserve_storage_type() {
        let narrow = Type::nullary_function_by_val(Type::never());
        let wide = Type::nullary_function_by_val(int_type());
        let fallible = Type::function_by_val_with_effects([], int_type(), effect(Fallible));
        for convention in [
            SubscriptResultConvention::AddressorPlace,
            SubscriptResultConvention::YieldedOnce,
        ] {
            let member = SubscriptMemberType::new(no_effects(), convention);
            let accessor = |ret, writable: bool| {
                Type::subscript_type(SubscriptType::new(
                    vec![FnArgType::new_by_val(Type::unit())],
                    ret,
                    Some(member.clone()),
                    writable.then(|| member.clone()),
                ))
            };
            for (narrow, wide) in [(narrow, wide), (wide, fallible)] {
                assert!(!relates(
                    accessor(narrow, true),
                    accessor(wide, true),
                    SubOrSameType::SubType
                ));
                assert!(!relates(
                    accessor(narrow, true),
                    accessor(wide, true),
                    SubOrSameType::SameTypeWithSubEffects
                ));
                assert!(relates(
                    accessor(narrow, true),
                    accessor(wide, false),
                    SubOrSameType::SubType
                ));
                assert!(relates(
                    accessor(narrow, true),
                    accessor(narrow, true),
                    SubOrSameType::SubType
                ));
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
        inference.normalize_given_outputs(&|_| Vec::new()).unwrap();
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
        assert!(inference.normalize_given_outputs(&|_| Vec::new()).is_err());
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
                    Default::default(),
                    &|_| Vec::new()
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
                    Default::default(),
                    &|_| Vec::new()
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
                        Default::default(),
                        &|_| Vec::new()
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
                        Default::default(),
                        &|_| Vec::new()
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
                    origin,
                    &|_| Vec::new()
                )
                .unwrap(),
            GivenMatch::Resolved
        );
        assert!(inference.given_used_by(owner, GivenId(1)));
        assert!(!inference.given_used_by(owner, GivenId(0)));
    }
}
