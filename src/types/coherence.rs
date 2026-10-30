// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use ustr::ustr;

use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    compiler::error::{InternalCompilationError, InternalTraitImplHeader},
    internal_compilation_error,
    module::{
        BlanketTraitImplKey, BlanketTraitImplSubKey, ConcreteTraitImplKey, Module, ModuleEnv,
        ModuleId, TraitId, TraitImpl, TraitKey,
    },
    std::value::{NO_DERIVE_VALUE_ATTRIBUTE, is_value_trait},
    types::{
        effect_polarity::{EffectPolarity, trait_output_effect_polarities},
        effects::EffType,
        r#trait::TraitImplPolicy,
        trait_solver::{TRAIT_SOLVER_RECURSION_LIMIT, TraitSolver},
        r#type::{Type, TypeKind, TypeVar},
        type_inference::unify::{UnifiedTypeInference, UnifiedTypeInferenceSnapshot},
        type_like::{TypeLike, instantiate_types},
        type_mapper::{BitmapInstantiationMapper, SimpleInstantiationMapper, TypeMapper},
        type_scheme::PubTypeConstraint,
        type_visitor::collect_ty_vars,
    },
};

struct CoherenceTypeUnifier {
    inner: UnifiedTypeInference,
}

struct CoherenceTypeUnifierSnapshot {
    inner: UnifiedTypeInferenceSnapshot,
}

impl CoherenceTypeUnifier {
    fn new_with_ty_vars(count: u32) -> Self {
        Self {
            inner: UnifiedTypeInference::new_with_ty_vars(count),
        }
    }

    fn add_ty_vars(&mut self, count: u32) {
        self.inner.add_ty_vars(count);
    }

    fn snapshot(&mut self) -> CoherenceTypeUnifierSnapshot {
        CoherenceTypeUnifierSnapshot {
            inner: self.inner.snapshot(),
        }
    }

    fn rollback_to(&mut self, snapshot: CoherenceTypeUnifierSnapshot) {
        self.inner.rollback_to(snapshot.inner);
    }

    fn unify_same_type_with_sub_effects(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.inner
            .unify_same_type_with_sub_effects(current, current_span, expected, expected_span)
    }

    /// Relate an impl's output effects to the requested ones by each output's polarity, with
    /// the rule resolution uses, so that coherence is never stricter than resolution.
    fn match_output_effects(
        &mut self,
        polarities: &[EffectPolarity],
        impl_effs: &[EffType],
        requested_effs: &[EffType],
    ) -> bool {
        let span = Location::new_synthesized();
        impl_effs.iter().zip(requested_effs).zip(polarities).all(
            |((impl_eff, requested_eff), &polarity)| {
                TraitSolver::match_trait_output_effect(
                    &mut self.inner,
                    impl_eff,
                    requested_eff,
                    polarity,
                    span,
                )
                .is_ok()
            },
        )
    }

    fn substitute_in_constraint(&mut self, constraint: &PubTypeConstraint) -> PubTypeConstraint {
        self.inner.substitute_in_constraint(constraint)
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn check_trait_impl(
    current: &Module,
    others: &Modules,
    trait_id: TraitId,
    trait_is_local: bool,
    input_tys: &[Type],
    output_tys: &[Type],
    ty_var_count: u32,
    eff_var_count: u32,
    constraints: &[PubTypeConstraint],
    span: Location,
) -> Result<(), InternalCompilationError> {
    let env = ModuleEnv::new(current, others);
    let trait_def = env.trait_def(trait_id);
    if trait_def.impl_policy == TraitImplPolicy::NativeOnly {
        return Err(internal_compilation_error!(TraitImplNativeOnly {
            trait_ref: trait_id,
            impl_span: span,
        }));
    }

    if let Some(&input_ty) = input_tys
        .iter()
        .find(|&&ty| has_anonymous_structural_head(ty))
    {
        return Err(internal_compilation_error!(
            TraitImplForAnonymousStructuralType {
                input_ty,
                impl_span: span,
            }
        ));
    }

    if is_value_trait(trait_id, trait_def)
        && current.module_id() != trait_id.module
        && !input_tys
            .iter()
            .any(|&ty| has_local_named_head(current, ty))
    {
        return Err(internal_compilation_error!(TraitImplOrphanRuleViolation {
            trait_ref: trait_id,
            input_tys: input_tys.to_vec(),
            impl_span: span,
        }));
    }

    if !trait_is_local
        && !input_tys
            .iter()
            .any(|&ty| has_local_named_head(current, ty))
    {
        return Err(internal_compilation_error!(TraitImplOrphanRuleViolation {
            trait_ref: trait_id,
            input_tys: input_tys.to_vec(),
            impl_span: span,
        }));
    }

    if let Some(output_ty) = undetermined_output(input_tys, output_tys, constraints) {
        return Err(internal_compilation_error!(TraitImplOutputNotDetermined {
            trait_ref: trait_id,
            output_ty,
            impl_span: span,
        }));
    }

    let new_key = if ty_var_count == 0 && eff_var_count == 0 {
        TraitKey::Concrete(ConcreteTraitImplKey::new(trait_id, input_tys.to_vec()))
    } else {
        TraitKey::Blanket(BlanketTraitImplKey::new(
            trait_id,
            BlanketTraitImplSubKey::new(
                input_tys.to_vec(),
                ty_var_count,
                eff_var_count,
                constraints.to_vec(),
            ),
        ))
    };

    for (key, imp, module_id) in
        iter_visible_impls(current, others, current.module_id(), Some(trait_id))
    {
        if impls_overlap(current, others, &new_key, &key, module_id)? {
            return Err(internal_compilation_error!(OverlappingTraitImpls {
                trait_ref: trait_id,
                input_tys: input_tys.to_vec(),
                impl_span: span,
                existing_impl: existing_impl_header(&key, imp, module_id),
                existing_span: imp.source_span,
            }));
        }
    }

    Ok(())
}

/// Returns an output type that the impl's inputs do not determine, if any.
///
/// Inputs select at most one impl, so each output must be a function of the inputs. A type
/// variable is determined if it occurs in an input type, or on the determined side of a
/// constraint whose determining side is: a trait application's outputs from its inputs, a tuple's
/// element, a field from its receiver, or a variant's payload. The determined set is the least
/// fixed point from the input variables, so constraints cannot determine each other without an
/// input-derived start. Constraints that only restrict a variable, such as `T: Default`, do not
/// determine it. Effect variables are instantiated per application and are not checked.
fn undetermined_output(
    input_tys: &[Type],
    output_tys: &[Type],
    constraints: &[PubTypeConstraint],
) -> Option<Type> {
    use PubTypeConstraint::*;
    let mut determined: FxHashSet<TypeVar> = collect_ty_vars(input_tys).into_iter().collect();
    loop {
        let mut changed = false;
        for constraint in constraints {
            let (from, to) = match constraint {
                HaveTrait {
                    input_tys,
                    output_tys,
                    ..
                } => (collect_ty_vars(input_tys), collect_ty_vars(output_tys)),
                TupleAtIndexIs {
                    tuple_ty,
                    element_ty,
                    ..
                } => (tuple_ty.inner_ty_vars(), element_ty.inner_ty_vars()),
                ProjectionSubscriptIs { subscript_ty, .. } => (
                    subscript_ty
                        .args
                        .first()
                        .map(|receiver| receiver.ty.inner_ty_vars())
                        .unwrap_or_default(),
                    subscript_ty.inner_ty_vars(),
                ),
                TypeHasVariant {
                    variant_ty,
                    payload_ty,
                    ..
                } => (variant_ty.inner_ty_vars(), payload_ty.inner_ty_vars()),
                VariantPayloadLayout { .. } => continue,
            };
            if from.iter().all(|var| determined.contains(var)) {
                for var in to {
                    changed |= determined.insert(var);
                }
            }
        }
        if !changed {
            break;
        }
    }
    output_tys
        .iter()
        .find(|ty| {
            ty.inner_ty_vars()
                .iter()
                .any(|var| !determined.contains(var))
        })
        .copied()
}

/// Check the module's impls against each other and against the visible impls of other modules,
/// once all of them are registered.
///
/// Each impl is also checked when it is registered, but only against the impls registered so
/// far: a non-overlap concluded then may rely on a prerequisite that only a later impl of the
/// module satisfies. Overlaps found then stay valid, as adding impls never removes one.
///
/// As in the incremental check, only source impls are compared: impls the compiler generates,
/// such as instances materialized from a source impl, are not separate declarations.
pub(crate) fn check_module_coherence(
    current: &Module,
    others: &Modules,
) -> Result<(), InternalCompilationError> {
    // Local impls come first, so each pair involving a local impl is checked once.
    let impls: Vec<_> = iter_visible_impls(current, others, current.module_id(), None)
        .filter(|(_, imp, _)| imp.source_span.is_some())
        .collect();
    for (index, (key, imp, module_id)) in impls.iter().enumerate() {
        if module_id.is_some() {
            break;
        }
        for (other_key, other_imp, other_module_id) in &impls[index + 1..] {
            if other_key.trait_id() != key.trait_id() {
                continue;
            }
            if impls_overlap(current, others, key, other_key, *other_module_id)? {
                let input_tys = match key {
                    TraitKey::Concrete(key) => key.input_tys.clone(),
                    TraitKey::Blanket(key) => key.sub_key.input_tys.clone(),
                };
                return Err(internal_compilation_error!(OverlappingTraitImpls {
                    trait_ref: key.trait_id(),
                    input_tys,
                    impl_span: imp.source_span.unwrap_or_else(Location::new_synthesized),
                    existing_impl: existing_impl_header(other_key, other_imp, *other_module_id),
                    existing_span: other_imp.source_span,
                }));
            }
        }
    }
    Ok(())
}

fn has_local_named_head(current: &Module, ty: Type) -> bool {
    let ty_data = ty.data();
    ty_data
        .as_named()
        .is_some_and(|named| current.owns_type_def(named.def))
}

fn has_anonymous_structural_head(ty: Type) -> bool {
    let ty_data = ty.data();
    matches!(
        &*ty_data,
        TypeKind::Tuple(_) | TypeKind::Record(_) | TypeKind::Variant(_) | TypeKind::Function(_)
    )
}

/// The impls visible from the current module: its own, the public ones of other modules, and
/// the private ones of `private_scope`, the module whose impl's prerequisites are being checked.
/// If `trait_filter` is given, only the impls of that trait, filtered before their keys are
/// cloned.
fn iter_visible_impls<'a>(
    current: &'a Module,
    others: &'a Modules,
    private_scope: ModuleId,
    trait_filter: Option<TraitId>,
) -> impl Iterator<Item = (TraitKey, &'a TraitImpl, Option<ModuleId>)> + 'a {
    let selected = move |trait_id: TraitId| trait_filter.is_none_or(|filter| filter == trait_id);
    let local = current
        .impls
        .concrete()
        .iter()
        .filter(move |(key, _)| selected(key.trait_id))
        .map(|(key, &id)| {
            (
                TraitKey::Concrete(key.clone()),
                current.impls.get_impl_by_local_id(id),
                None,
            )
        });
    let local_blankets = current
        .impls
        .blanket()
        .iter()
        .filter(move |(trait_id, _)| selected(**trait_id))
        .flat_map(|(trait_id, blanket_impls)| {
            blanket_impls.iter().map(|(sub_key, &id)| {
                (
                    TraitKey::Blanket(BlanketTraitImplKey::new(*trait_id, sub_key.clone())),
                    current.impls.get_impl_by_local_id(id),
                    None,
                )
            })
        });
    let imported = others.enumerates().flat_map(move |(module_id, entry, _)| {
        entry.module().into_iter().flat_map(move |module| {
            let concrete = module
                .impls
                .concrete()
                .iter()
                .filter(move |(key, _)| selected(key.trait_id))
                .map(move |(key, &id)| {
                    (
                        TraitKey::Concrete(key.clone()),
                        module.impls.get_impl_by_local_id(id),
                        Some(module_id),
                    )
                })
                .filter(move |(_, imp, _)| imp.public || module_id == private_scope);
            let blankets = module
                .impls
                .blanket()
                .iter()
                .filter(move |(trait_id, _)| selected(**trait_id))
                .flat_map(move |(trait_id, blanket_impls)| {
                    blanket_impls.iter().map(move |(sub_key, &id)| {
                        (
                            TraitKey::Blanket(BlanketTraitImplKey::new(*trait_id, sub_key.clone())),
                            module.impls.get_impl_by_local_id(id),
                            Some(module_id),
                        )
                    })
                })
                .filter(move |(_, imp, _)| imp.public || module_id == private_scope);
            concrete.chain(blankets)
        })
    });
    local.chain(local_blankets).chain(imported)
}

/// Whether two impls of the same trait may apply to a common application.
///
/// An application's inputs select at most one impl, so overlap is decided on inputs and
/// constraints alone: impls differing only in their output types or effects still overlap.
/// The new impl belongs to the current module; the existing one may be imported from
/// `existing_module`, in whose private scope its constraints are checked.
fn impls_overlap(
    current: &Module,
    others: &Modules,
    new_key: &TraitKey,
    existing_key: &TraitKey,
    existing_module: Option<ModuleId>,
) -> Result<bool, InternalCompilationError> {
    use TraitKey::*;
    let new_sub_key;
    let new_sub_key = match new_key {
        Concrete(key) => {
            new_sub_key = concrete_as_blanket_sub_key(&key.input_tys);
            &new_sub_key
        }
        Blanket(key) => &key.sub_key,
    };
    let existing_sub_key;
    let existing_sub_key = match existing_key {
        Concrete(key) => {
            existing_sub_key = concrete_as_blanket_sub_key(&key.input_tys);
            &existing_sub_key
        }
        Blanket(key) => &key.sub_key,
    };
    if let (Concrete(new_key), Concrete(existing_key)) = (new_key, existing_key) {
        return Ok(new_key.input_tys == existing_key.input_tys);
    }
    let current_id = current.module_id();
    blanket_impls_overlap(
        current,
        others,
        (new_sub_key, current_id),
        (existing_sub_key, existing_module.unwrap_or(current_id)),
    )
}

fn concrete_as_blanket_sub_key(input_tys: &[Type]) -> BlanketTraitImplSubKey {
    BlanketTraitImplSubKey::new(input_tys.to_vec(), 0, 0, Vec::new())
}

fn blanket_impls_overlap(
    current: &Module,
    others: &Modules,
    (lhs, lhs_scope): (&BlanketTraitImplSubKey, ModuleId),
    (rhs, rhs_scope): (&BlanketTraitImplSubKey, ModuleId),
) -> Result<bool, InternalCompilationError> {
    if lhs.input_tys.len() != rhs.input_tys.len() {
        return Ok(false);
    }

    let span = Location::new_synthesized();
    let mut ty_inf = CoherenceTypeUnifier::new_with_ty_vars(lhs.ty_var_count + rhs.ty_var_count);

    // Both sides use raw effect variable indices, so each side is renamed to
    // its own fresh inference effect variables before unification.
    let lhs_eff_subst = ty_inf.inner.fresh_effect_var_subst(lhs.eff_var_count);
    let lhs_inst_subst = (FxHashMap::default(), lhs_eff_subst);
    let mut lhs_mapper = SimpleInstantiationMapper::new(&lhs_inst_subst);
    let lhs_inputs = instantiate_types(&lhs.input_tys, &mut lhs_mapper);
    let lhs_constraints = instantiate_types(&lhs.constraints, &mut lhs_mapper);

    let rhs_ty_subst: FxHashMap<_, _> = (0..rhs.ty_var_count)
        .map(|index| {
            let var = TypeVar::new(index);
            let shifted = Type::variable_id(lhs.ty_var_count + index);
            (var, shifted)
        })
        .collect();
    let rhs_eff_subst = ty_inf.inner.fresh_effect_var_subst(rhs.eff_var_count);
    let inst_subst = (rhs_ty_subst, rhs_eff_subst);
    let mut mapper = SimpleInstantiationMapper::new(&inst_subst);
    let rhs_inputs = instantiate_types(&rhs.input_tys, &mut mapper);
    let rhs_constraints = instantiate_types(&rhs.constraints, &mut mapper);
    for (&lhs_ty, &rhs_ty) in lhs_inputs.iter().zip(rhs_inputs.iter()) {
        if ty_inf
            .unify_same_type_with_sub_effects(lhs_ty, span, rhs_ty, span)
            .is_err()
        {
            return Ok(false);
        }
    }
    let pending = scoped(lhs_constraints, lhs_scope)
        .chain(scoped(rhs_constraints, rhs_scope))
        .collect();
    constraints_may_be_satisfiable(
        current,
        others,
        &mut ty_inf,
        pending,
        lhs.ty_var_count + rhs.ty_var_count,
        &mut FxHashSet::default(),
    )
}

/// A constraint to check, with the module whose private impls may satisfy it: the module of the
/// impl that requires it, as resolution checks an impl's prerequisites in that module's scope.
#[derive(Clone)]
struct ScopedConstraint {
    constraint: PubTypeConstraint,
    private_scope: ModuleId,
}

fn scoped(
    constraints: Vec<PubTypeConstraint>,
    private_scope: ModuleId,
) -> impl Iterator<Item = ScopedConstraint> {
    constraints
        .into_iter()
        .map(move |constraint| ScopedConstraint {
            constraint,
            private_scope,
        })
}

fn constraints_may_be_satisfiable(
    current: &Module,
    others: &Modules,
    ty_inf: &mut CoherenceTypeUnifier,
    mut pending: Vec<ScopedConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitId, Vec<Type>, Vec<Type>)>,
) -> Result<bool, InternalCompilationError> {
    if pending.is_empty() {
        return Ok(true);
    }

    let ScopedConstraint {
        constraint,
        private_scope,
    } = pending.pop().unwrap();
    let constraint = ty_inf.substitute_in_constraint(&constraint);
    // Another module may implement the trait for its own type substituted for a type-variable
    // head, so such a constraint is potentially satisfiable. The other constraints are decided
    // first, as they may still give the variable a concrete head.
    if is_open_world(current, others, &constraint) {
        let all_open = pending.iter().all(|scoped| {
            let constraint = ty_inf.substitute_in_constraint(&scoped.constraint);
            is_open_world(current, others, &constraint)
        });
        if all_open {
            return Ok(true);
        }
        pending.insert(
            0,
            ScopedConstraint {
                constraint,
                private_scope,
            },
        );
        return constraints_may_be_satisfiable(
            current,
            others,
            ty_inf,
            pending,
            next_ty_var_index,
            stack,
        );
    }
    // Structural requirements that impl methods infer, such as a field of `Self`, are not
    // decided here: taking them as satisfiable can report an overlap, never hide one.
    let Ok((_, trait_id, input_tys, output_tys, output_effs, _span)) = constraint.into_have_trait()
    else {
        return constraints_may_be_satisfiable(
            current,
            others,
            ty_inf,
            pending,
            next_ty_var_index,
            stack,
        );
    };
    trait_constraint_may_be_satisfiable(
        current,
        others,
        ty_inf,
        pending,
        next_ty_var_index,
        stack,
        trait_id,
        &input_tys,
        &output_tys,
        &output_effs,
        private_scope,
    )
}

fn output_effect_polarities(
    current: &Module,
    others: &Modules,
    trait_id: TraitId,
) -> Vec<EffectPolarity> {
    let env = ModuleEnv::new(current, others);
    trait_output_effect_polarities(trait_id, &|id| env.trait_def(id))
}

/// Whether other modules may add impls satisfying this constraint: by the orphan rule, a module
/// may implement a user-implementable trait for its own named type, which a type-variable input
/// head may become. Prerequisites of candidate impls go through the same check.
fn is_open_world(current: &Module, others: &Modules, constraint: &PubTypeConstraint) -> bool {
    let PubTypeConstraint::HaveTrait {
        trait_id,
        input_tys,
        ..
    } = constraint
    else {
        return false;
    };
    ModuleEnv::new(current, others)
        .trait_def(*trait_id)
        .impl_policy
        == TraitImplPolicy::UserImplementable
        && input_tys
            .iter()
            .any(|ty| matches!(*ty.data(), TypeKind::Variable(_)))
}

#[allow(clippy::too_many_arguments)]
fn trait_constraint_may_be_satisfiable(
    current: &Module,
    others: &Modules,
    ty_inf: &mut CoherenceTypeUnifier,
    pending: Vec<ScopedConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitId, Vec<Type>, Vec<Type>)>,
    trait_id: TraitId,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
    private_scope: ModuleId,
) -> Result<bool, InternalCompilationError> {
    let derivers_enabled = !value_deriver_disabled_for_input(current, others, trait_id, input_tys);
    let env = ModuleEnv::new(current, others);
    let trait_def = env.trait_def(trait_id);
    if derivers_enabled
        && !trait_def.derivers.is_empty()
        && !input_tys.iter().all(Type::is_constant)
    {
        return constraints_may_be_satisfiable(
            current,
            others,
            ty_inf,
            pending,
            next_ty_var_index,
            stack,
        );
    }

    let query = (trait_id, input_tys.to_vec(), output_tys.to_vec());
    // Prerequisites can nest ever larger goals, such as `[T]: P` requiring `[[T]]: P`. Resolution
    // gives up beyond its recursion limit, so the search may stop there too, but only as an
    // undecided goal: exhaustion is never evidence that the impls are disjoint.
    if stack.len() >= TRAIT_SOLVER_RECURSION_LIMIT {
        return Ok(true);
    }
    // A goal already being examined is assumed to hold, but the rest of the conjunction must
    // still be satisfiable.
    if !stack.insert(query.clone()) {
        return constraints_may_be_satisfiable(
            current,
            others,
            ty_inf,
            pending,
            next_ty_var_index,
            stack,
        );
    }

    for (key, imp, module_id) in iter_visible_impls(current, others, private_scope, Some(trait_id))
    {
        // An imported impl's prerequisites are checked in its module's scope, a local one's in
        // the current scope, as resolution does.
        let candidate_scope = module_id.unwrap_or(private_scope);

        let snapshot = ty_inf.snapshot();
        let result = match &key {
            TraitKey::Concrete(key) => concrete_impl_may_match_constraint(
                current,
                others,
                ty_inf,
                pending.clone(),
                next_ty_var_index,
                stack,
                key,
                imp,
                input_tys,
                output_tys,
                output_effs,
            )?,
            TraitKey::Blanket(key) => blanket_impl_may_match_constraint(
                current,
                others,
                ty_inf,
                pending.clone(),
                next_ty_var_index,
                stack,
                (key, candidate_scope),
                imp,
                input_tys,
                output_tys,
                output_effs,
            )?,
        };
        ty_inf.rollback_to(snapshot);
        if result {
            stack.remove(&query);
            return Ok(true);
        }
    }

    stack.remove(&query);
    if !derivers_enabled || trait_def.derivers.is_empty() {
        Ok(false)
    } else {
        constraints_may_be_satisfiable(current, others, ty_inf, pending, next_ty_var_index, stack)
    }
}

fn value_deriver_disabled_for_input(
    current: &Module,
    others: &Modules,
    trait_id: TraitId,
    input_tys: &[Type],
) -> bool {
    let env = ModuleEnv::new(current, others);
    if !is_value_trait(trait_id, env.trait_def(trait_id)) || input_tys.len() != 1 {
        return false;
    }
    let ty_data = input_tys[0].data();
    let TypeKind::Named(named) = &*ty_data else {
        return false;
    };
    current.try_type_def(named.def).is_some_and(|type_def| {
        type_def
            .attributes
            .iter()
            .any(|attribute| attribute.path.0 == ustr(NO_DERIVE_VALUE_ATTRIBUTE))
    })
}

#[allow(clippy::too_many_arguments)]
fn concrete_impl_may_match_constraint(
    current: &Module,
    others: &Modules,
    ty_inf: &mut CoherenceTypeUnifier,
    pending: Vec<ScopedConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitId, Vec<Type>, Vec<Type>)>,
    key: &ConcreteTraitImplKey,
    imp: &TraitImpl,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
) -> Result<bool, InternalCompilationError> {
    let span = Location::new_synthesized();
    for (&candidate_input_ty, &constraint_input_ty) in key.input_tys.iter().zip(input_tys) {
        if ty_inf
            .unify_same_type_with_sub_effects(candidate_input_ty, span, constraint_input_ty, span)
            .is_err()
        {
            return Ok(false);
        }
    }
    for (&candidate_output_ty, &constraint_output_ty) in imp.output_tys.iter().zip(output_tys) {
        if ty_inf
            .unify_same_type_with_sub_effects(candidate_output_ty, span, constraint_output_ty, span)
            .is_err()
        {
            return Ok(false);
        }
    }
    let polarities = output_effect_polarities(current, others, key.trait_id);
    if !ty_inf.match_output_effects(&polarities, &imp.output_effs, output_effs) {
        return Ok(false);
    }
    constraints_may_be_satisfiable(current, others, ty_inf, pending, next_ty_var_index, stack)
}

#[allow(clippy::too_many_arguments)]
fn blanket_impl_may_match_constraint(
    current: &Module,
    others: &Modules,
    ty_inf: &mut CoherenceTypeUnifier,
    mut pending: Vec<ScopedConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitId, Vec<Type>, Vec<Type>)>,
    (key, candidate_scope): (&BlanketTraitImplKey, ModuleId),
    imp: &TraitImpl,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
) -> Result<bool, InternalCompilationError> {
    let offset = next_ty_var_index;
    ty_inf.add_ty_vars(key.sub_key.ty_var_count);
    let candidate_ty_subst: FxHashMap<_, _> = (0..key.sub_key.ty_var_count)
        .map(|index| {
            let var = TypeVar::new(index);
            let shifted = Type::variable_id(offset + index);
            (var, shifted)
        })
        .collect();
    let candidate_eff_subst = ty_inf
        .inner
        .fresh_effect_var_subst(key.sub_key.eff_var_count);
    let inst_subst = (candidate_ty_subst, candidate_eff_subst);
    let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
    let candidate_inputs = instantiate_types(&key.sub_key.input_tys, &mut mapper);
    let candidate_outputs = instantiate_types(&imp.output_tys, &mut mapper);
    let candidate_output_effs: Vec<_> = imp
        .output_effs
        .iter()
        .map(|eff| mapper.map_effect_type(eff))
        .collect();
    let candidate_constraints = instantiate_types(&key.sub_key.constraints, &mut mapper);

    let span = Location::new_synthesized();
    for (&candidate_input_ty, &constraint_input_ty) in candidate_inputs.iter().zip(input_tys) {
        if ty_inf
            .unify_same_type_with_sub_effects(candidate_input_ty, span, constraint_input_ty, span)
            .is_err()
        {
            return Ok(false);
        }
    }
    for (&candidate_output_ty, &constraint_output_ty) in candidate_outputs.iter().zip(output_tys) {
        if ty_inf
            .unify_same_type_with_sub_effects(candidate_output_ty, span, constraint_output_ty, span)
            .is_err()
        {
            return Ok(false);
        }
    }
    let polarities = output_effect_polarities(current, others, key.trait_id);
    if !ty_inf.match_output_effects(&polarities, &candidate_output_effs, output_effs) {
        return Ok(false);
    }
    pending.extend(scoped(candidate_constraints, candidate_scope));
    constraints_may_be_satisfiable(
        current,
        others,
        ty_inf,
        pending,
        next_ty_var_index + key.sub_key.ty_var_count,
        stack,
    )
}

fn existing_impl_header(
    key: &TraitKey,
    imp: &TraitImpl,
    module_id: Option<ModuleId>,
) -> InternalTraitImplHeader {
    match key {
        TraitKey::Concrete(key) => InternalTraitImplHeader {
            input_tys: key.input_tys.clone(),
            output_tys: imp.output_tys.clone(),
            ty_var_count: 0,
            constraints: Vec::new(),
            module_id,
        },
        TraitKey::Blanket(key) => InternalTraitImplHeader {
            input_tys: key.sub_key.input_tys.clone(),
            output_tys: imp.output_tys.clone(),
            ty_var_count: key.sub_key.ty_var_count,
            constraints: key.sub_key.constraints.clone(),
            module_id,
        },
    }
}
