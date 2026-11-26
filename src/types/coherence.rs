// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::collections::VecDeque;

use ustr::ustr;

use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    compiler::error::{ImplEffectRestriction, InternalCompilationError, InternalTraitImplHeader},
    internal_compilation_error,
    module::{
        BlanketTraitImplKey, BlanketTraitImplSubKey, ConcreteTraitImplKey, ImplGenericNames,
        Module, ModuleEnv, ModuleId, TraitId, TraitImpl, TraitKey,
    },
    std::{
        STD_MODULE_ID,
        core_traits_names::REPR_TRAIT_NAME,
        value::{NO_DERIVE_VALUE_ATTRIBUTE, is_value_trait},
    },
    types::{
        effects::EffType,
        r#trait::TraitImplPolicy,
        trait_solver::{TRAIT_SOLVER_RECURSION_LIMIT, input_heads_may_match},
        r#type::{Type, TypeKind, TypeVar},
        type_inference::{
            speculation::{Snapshotting, Speculation},
            unify::{UnifiedTypeInference, UnifiedTypeInferenceSnapshot},
        },
        type_like::{TypeLike, instantiate_types},
        type_mapper::{BitmapInstantiationMapper, EffectErasingMapper, SimpleInstantiationMapper},
        type_scheme::PubTypeConstraint,
        type_visitor::{OncePerType, TypeInnerVisitor, collect_ty_vars},
    },
};

struct CoherenceTypeUnifier {
    inner: UnifiedTypeInference,
}

impl Snapshotting for CoherenceTypeUnifier {
    type Snapshot = UnifiedTypeInferenceSnapshot;
    fn snapshot(&mut self) -> Self::Snapshot {
        self.inner.snapshot()
    }
    fn rollback_to(&mut self, snapshot: Self::Snapshot) {
        self.inner.rollback_to(snapshot);
    }
    fn commit(&mut self, snapshot: Self::Snapshot) {
        self.inner.commit(snapshot);
    }
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

    /// Whether two types unify. A resource limit tells nothing about whether impls overlap, so it
    /// is an error.
    fn unifies(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) -> Result<bool, InternalCompilationError> {
        let unified = self.inner.unify_same_type_with_sub_effects(
            current,
            current_span,
            expected,
            expected_span,
        );
        Ok(InternalCompilationError::attempt(unified)?.is_some())
    }

    fn substitute_in_constraint(
        &mut self,
        constraint: &PubTypeConstraint,
    ) -> Result<PubTypeConstraint, InternalCompilationError> {
        self.inner.substitute_in_constraint(constraint)
    }
}

/// Whether an impl's constraints mention an effect, which its overlaps do not consider.
fn has_effect_requirement(key: &TraitKey) -> bool {
    let TraitKey::Blanket(key) = key else {
        return false;
    };
    let mut rows = OncePerType::new(EffectRowCollector::default());
    key.sub_key.constraints.visit(&mut rows);
    !rows.visitor.0.is_empty()
}

/// Collects every occurrence of an effect row in the types it visits.
#[derive(Default)]
struct EffectRowCollector(Vec<EffType>);

impl TypeInnerVisitor for EffectRowCollector {
    fn visit_eff_ty(&mut self, eff_ty: &EffType) {
        self.0.push(eff_ty.clone());
    }
}

/// Effects never select impls, so each effect in an impl's inputs must be a variable of the impl,
/// used once. A type holding an effect uses it once per simple path from the inputs to it:
/// `Two<F, F>` uses the effect of `F` twice, but a recursive type uses its effects once for all
/// its unrollings.
fn check_impl_leaves_effects_open(
    trait_id: TraitId,
    input_tys: &[Type],
    span: Location,
) -> Result<(), InternalCompilationError> {
    let restricted = |input: usize, restriction: ImplEffectRestriction| {
        internal_compilation_error!(TraitImplInputRestrictsEffect {
            trait_ref: trait_id,
            input_ty: input_tys[input],
            restriction,
            impl_span: span,
        })
    };
    let graph = InputGraph::new(input_tys);
    let mut seen = FxHashSet::default();
    for &(holder, input) in &graph.holders {
        for row in effect_rows(&holder.data()) {
            let Some(var) = row.to_single_variable() else {
                return Err(restricted(input, ImplEffectRestriction::FixedInInput));
            };
            if !seen.insert(var) {
                return Err(restricted(input, ImplEffectRestriction::RepeatedInInput));
            }
        }
    }
    for &(holder, _) in &graph.holders {
        if let Some(input) = graph.second_simple_path(holder) {
            return Err(restricted(input, ImplEffectRestriction::RepeatedInInput));
        }
    }
    Ok(())
}

/// The effect rows that a type holds itself, not through its children.
fn effect_rows(kind: &TypeKind) -> Vec<EffType> {
    match kind {
        TypeKind::Function(function) => vec![function.effects.clone()],
        TypeKind::Subscript(subscript) => subscript
            .members()
            .map(|member| member.effects.clone())
            .collect(),
        TypeKind::Named(named) => named.effect_params.clone(),
        _ => Vec::new(),
    }
}

/// The types that an impl's inputs reach. A path through them is a sequence of occurrences, so
/// that `(F, F)` reaches `F` by two paths. A recursive type makes the graph cyclic, and the paths
/// through it can be exponentially many, so they are not enumerated.
struct InputGraph<'a> {
    inputs: &'a [Type],
    /// The children of each type reached, at each of their occurrences.
    children: FxHashMap<Type, Vec<Type>>,
    /// The types reached that hold effect rows, each with the first input reaching it.
    holders: Vec<(Type, usize)>,
}

impl<'a> InputGraph<'a> {
    fn new(inputs: &'a [Type]) -> Self {
        let mut children = FxHashMap::default();
        let mut holders = Vec::new();
        for (input, &root) in inputs.iter().enumerate() {
            let mut stack = vec![root];
            while let Some(ty) = stack.pop() {
                if children.contains_key(&ty) {
                    continue;
                }
                let kind = ty.data();
                if !effect_rows(&kind).is_empty() {
                    holders.push((ty, input));
                }
                let mut occurrences = Vec::new();
                kind.for_each_inner_type(|child| occurrences.push(child));
                stack.extend(occurrences.iter().rev());
                children.insert(ty, occurrences);
            }
        }
        Self {
            inputs,
            children,
            holders,
        }
    }

    /// The types that `node` leads to, `None` being the root that leads to the inputs.
    fn out(&self, node: Option<Type>) -> &[Type] {
        match node {
            None => self.inputs,
            Some(ty) => &self.children[&ty],
        }
    }

    /// If the inputs reach `target` by a second simple path, the input where it starts. One
    /// simple path P is found first; any other leaves P at some node u by another edge, and then
    /// reaches `target` without going through the part of P up to u.
    fn second_simple_path(&self, target: Type) -> Option<usize> {
        let path = self.shortest_path(target);
        let (_, first_input) = path[0];
        let mut prefix = FxHashSet::default();
        for &(node, taken) in &path {
            if let Some(ty) = node {
                prefix.insert(ty);
            }
            let others = self
                .out(node)
                .iter()
                .enumerate()
                .filter(|&(edge, ty)| edge != taken && !prefix.contains(ty));
            if node.is_none() {
                // The second path starts at another input.
                for (input, &ty) in others {
                    if self.reaches_avoiding([ty], target, &prefix) {
                        return Some(input);
                    }
                }
            } else if self.reaches_avoiding(others.map(|(_, &ty)| ty), target, &prefix) {
                return Some(first_input);
            }
        }
        None
    }

    /// A shortest path from the root to `target`, as the nodes it goes through, `None` being the
    /// root, each with the index of the edge it takes.
    fn shortest_path(&self, target: Type) -> Vec<(Option<Type>, usize)> {
        let mut parents = FxHashMap::<Type, (Option<Type>, usize)>::default();
        let mut queue = VecDeque::from([None]);
        while let Some(node) = queue.pop_front() {
            for (edge, &child) in self.out(node).iter().enumerate() {
                if Some(child) == node || parents.contains_key(&child) {
                    continue;
                }
                parents.insert(child, (node, edge));
                if child == target {
                    let mut path = Vec::new();
                    let mut at = Some(child);
                    while let Some(ty) = at {
                        let (parent, edge) = parents[&ty];
                        path.push((parent, edge));
                        at = parent;
                    }
                    path.reverse();
                    return path;
                }
                queue.push_back(Some(child));
            }
        }
        unreachable!("the inputs reach every holder of effect rows")
    }

    /// Whether a walk from `sources` reaches `target` without entering `avoided`.
    fn reaches_avoiding(
        &self,
        sources: impl IntoIterator<Item = Type>,
        target: Type,
        avoided: &FxHashSet<Type>,
    ) -> bool {
        let mut reached = FxHashSet::default();
        let mut stack: Vec<Type> = sources.into_iter().collect();
        while let Some(ty) = stack.pop() {
            if ty == target {
                return true;
            }
            if avoided.contains(&ty) || !reached.insert(ty) {
                continue;
            }
            stack.extend(&self.children[&ty]);
        }
        false
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
    generic_names: &ImplGenericNames,
    span: Location,
) -> Result<(), InternalCompilationError> {
    let env = ModuleEnv::new(current, others);
    let trait_def = env.trait_def(trait_id);
    match trait_def.impl_policy {
        TraitImplPolicy::NativeOnly => {
            return Err(internal_compilation_error!(TraitImplNativeOnly {
                trait_ref: trait_id,
                impl_span: span,
            }));
        }
        TraitImplPolicy::Sealed if trait_id.module != current.module_id() => {
            return Err(internal_compilation_error!(TraitImplSealed {
                trait_ref: trait_id,
                impl_span: span,
            }));
        }
        TraitImplPolicy::Sealed | TraitImplPolicy::UserImplementable => {}
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

    check_impl_leaves_effects_open(trait_id, input_tys, span)?;

    // An implementation of a trait of another module owns the applications it matches through
    // its owning input, so modules that do not know each other cannot both implement one.
    if !trait_is_local && current.owning_input(input_tys).is_none() {
        return Err(internal_compilation_error!(TraitImplOrphanRuleViolation {
            trait_ref: trait_id,
            input_tys: input_tys.to_vec(),
            impl_span: span,
        }));
    }

    // A public implementation is part of its module's contract, so it may not hide behind a
    // private type: an implementation is private only through its owning input.
    if current.is_trait_impl_exportable(trait_id, input_tys, others)
        && let Some(&private_ty) = input_tys
            .iter()
            .chain(output_tys)
            .find(|&&ty| !current.is_type_public(ty, others))
    {
        return Err(internal_compilation_error!(
            PublicTraitImplMentionsPrivateType {
                trait_ref: trait_id,
                private_ty,
                impl_span: span,
            }
        ));
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
            // Materialized dictionaries and derivations are not source declarations. In
            // particular, helper inference may derive Value before its blanket is published.
            .filter(|(_, imp, _)| imp.public || imp.source_span.is_some())
    {
        if impls_overlap(current, others, &new_key, &key, module_id)
            .map_err(|error| error.locate_limit(span))?
        {
            return Err(internal_compilation_error!(OverlappingTraitImpls {
                trait_ref: trait_id,
                input_tys: input_tys.to_vec(),
                generic_names: generic_names.clone(),
                impl_span: span,
                existing_impl: existing_impl_header(&key, imp, module_id),
                existing_span: imp.source_span,
                effects_ignored: has_effect_requirement(&new_key) || has_effect_requirement(&key),
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
                VariantPayloadLayout { .. } | VariantPayloadStorage { .. } => continue,
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
            let impl_span = imp.source_span.unwrap_or_else(Location::new_synthesized);
            if impls_overlap(current, others, key, other_key, *other_module_id)
                .map_err(|error| error.locate_limit(impl_span))?
            {
                let input_tys = match key {
                    TraitKey::Concrete(key) => key.input_tys.clone(),
                    TraitKey::Blanket(key) => key.sub_key.input_tys.clone(),
                };
                return Err(internal_compilation_error!(OverlappingTraitImpls {
                    trait_ref: key.trait_id(),
                    input_tys,
                    generic_names: imp.generic_names.clone(),
                    impl_span,
                    existing_impl: existing_impl_header(other_key, other_imp, *other_module_id),
                    existing_span: other_imp.source_span,
                    effects_ignored: has_effect_requirement(key)
                        || has_effect_requirement(other_key),
                }));
            }
        }
    }
    Ok(())
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
    let imported = others
        .enumerates()
        .filter(move |(id, _, _)| current.environment.contains(id))
        .flat_map(move |(module_id, entry, _)| {
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
                                TraitKey::Blanket(BlanketTraitImplKey::new(
                                    *trait_id,
                                    sub_key.clone(),
                                )),
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
/// constraints alone: impls differing only in their output types or effects still overlap, and
/// so do impls differing only in the output effects their constraints require.
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

/// The same types or constraints, without any effect.
fn erased<T: TypeLike>(values: &[T]) -> Vec<T> {
    instantiate_types(values, &mut EffectErasingMapper)
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
    if lhs.input_tys.len() != rhs.input_tys.len()
        || !input_heads_may_match(&lhs.input_tys, &rhs.input_tys)
    {
        return Ok(false);
    }

    let span = Location::new_synthesized();
    let mut ty_inf = CoherenceTypeUnifier::new_with_ty_vars(lhs.ty_var_count + rhs.ty_var_count);

    // Both sides use raw effect variable indices, so each side is renamed to
    // its own fresh inference effect variables before unification.
    let lhs_eff_subst = ty_inf.inner.fresh_effect_var_subst(lhs.eff_var_count);
    let lhs_inst_subst = (FxHashMap::default(), lhs_eff_subst);
    let mut lhs_mapper = SimpleInstantiationMapper::new(&lhs_inst_subst);
    // Effects never select an impl, so they cannot keep two impls apart.
    let lhs_inputs = erased(&instantiate_types(&lhs.input_tys, &mut lhs_mapper));

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
    let rhs_inputs = erased(&instantiate_types(&rhs.input_tys, &mut mapper));
    for (&lhs_ty, &rhs_ty) in lhs_inputs.iter().zip(rhs_inputs.iter()) {
        if !ty_inf.unifies(lhs_ty, span, rhs_ty, span)? {
            return Ok(false);
        }
    }
    let lhs_constraints = erased(&instantiate_types(&lhs.constraints, &mut lhs_mapper));
    let rhs_constraints = erased(&instantiate_types(&rhs.constraints, &mut mapper));
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
    let constraint = ty_inf.substitute_in_constraint(&constraint)?;
    // Another module may implement the trait for its own type substituted for a type-variable
    // head, so such a constraint is potentially satisfiable. The other constraints are decided
    // first, as they may still give the variable a concrete head.
    if is_open_world(current, others, &constraint) {
        let mut all_open = true;
        for scoped in &pending {
            let constraint = ty_inf.substitute_in_constraint(&scoped.constraint)?;
            if !is_open_world(current, others, &constraint) {
                all_open = false;
                break;
            }
        }
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
    let Ok((_, trait_id, input_tys, output_tys, _, _span)) = constraint.into_have_trait() else {
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
        private_scope,
    )
}

/// Whether other modules may add impls satisfying this constraint: by the orphan rule, a module
/// may implement a user-implementable trait for its own named type, which a type-variable input
/// head may become. Prerequisites of candidate impls go through the same check. A sealed trait
/// counts as open too: sealing restricts where its impls are written, but does not let the
/// compiler assume that it knows them all.
///
/// `Repr` of a type variable is open too: the type it becomes has a representation.
fn is_open_world(current: &Module, others: &Modules, constraint: &PubTypeConstraint) -> bool {
    let PubTypeConstraint::HaveTrait {
        trait_id,
        input_tys,
        ..
    } = constraint
    else {
        return false;
    };
    let env = ModuleEnv::new(current, others);
    let trait_def = env.trait_def(*trait_id);
    (trait_def.impl_policy != TraitImplPolicy::NativeOnly || is_repr_trait(*trait_id, trait_def))
        && input_tys
            .iter()
            .any(|ty| matches!(*ty.data(), TypeKind::Variable(_)))
}

fn is_repr_trait(trait_id: TraitId, trait_def: &crate::types::r#trait::Trait) -> bool {
    trait_id.module == STD_MODULE_ID && trait_def.name == REPR_TRAIT_NAME
}

/// Whether `Repr` of `input_ty`, whose head is known, may be `output_ty`. Selection gives it from
/// the head, without any impl: the shape of a named type, any other type itself. A private
/// representation counts as possible, which can report an overlap, never hide one.
#[allow(clippy::too_many_arguments)]
fn repr_may_be(
    current: &Module,
    others: &Modules,
    ty_inf: &mut CoherenceTypeUnifier,
    pending: Vec<ScopedConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitId, Vec<Type>, Vec<Type>)>,
    input_ty: Type,
    output_ty: Type,
) -> Result<bool, InternalCompilationError> {
    let named = input_ty.data().as_named().cloned();
    let repr = match named {
        Some(named) => {
            let env = ModuleEnv::new(current, others);
            env.type_def(named.def)
                .instantiated_shape_with_effects(&named.params, &named.effect_params)
        }
        None => input_ty,
    };
    let repr = erased(&[repr])[0];
    let span = Location::new_synthesized();
    if !ty_inf.unifies(repr, span, output_ty, span)? {
        return Ok(false);
    }
    constraints_may_be_satisfiable(current, others, ty_inf, pending, next_ty_var_index, stack)
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
    private_scope: ModuleId,
) -> Result<bool, InternalCompilationError> {
    let derivers_enabled = !value_deriver_disabled_for_input(current, others, trait_id, input_tys);
    let env = ModuleEnv::new(current, others);
    let trait_def = env.trait_def(trait_id);
    if is_repr_trait(trait_id, trait_def) {
        return repr_may_be(
            current,
            others,
            ty_inf,
            pending,
            next_ty_var_index,
            stack,
            input_tys[0],
            output_tys[0],
        );
    }
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
    // Prerequisites can nest ever more goals. Resolution gives up beyond its recursion limit, and
    // so does the search: exhaustion tells nothing of whether the impls are disjoint, so it is an
    // error, located at the impl.
    if stack.len() >= TRAIT_SOLVER_RECURSION_LIMIT {
        return Err(internal_compilation_error!(
            TraitSolverRecursionLimitExceeded {
                trait_ref: trait_id,
                input_tys: input_tys.to_vec(),
                fn_span: Location::new_synthesized(),
            }
        ));
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

        if !input_heads_may_match(key.input_tys(), input_tys) {
            continue;
        }

        let mut speculation = Speculation::new(ty_inf);
        let result = match &key {
            TraitKey::Concrete(key) => concrete_impl_may_match_constraint(
                current,
                others,
                &mut speculation,
                &pending,
                next_ty_var_index,
                stack,
                key,
                imp,
                input_tys,
                output_tys,
            )?,
            TraitKey::Blanket(key) => blanket_impl_may_match_constraint(
                current,
                others,
                &mut speculation,
                &pending,
                next_ty_var_index,
                stack,
                (key, candidate_scope),
                imp,
                input_tys,
                output_tys,
            )?,
        };
        drop(speculation);
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
    pending: &[ScopedConstraint],
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitId, Vec<Type>, Vec<Type>)>,
    key: &ConcreteTraitImplKey,
    imp: &TraitImpl,
    input_tys: &[Type],
    output_tys: &[Type],
) -> Result<bool, InternalCompilationError> {
    let span = Location::new_synthesized();
    let candidate_inputs = erased(&key.input_tys);
    let candidate_outputs = erased(&imp.output_tys);
    for (&candidate_input_ty, &constraint_input_ty) in candidate_inputs.iter().zip(input_tys) {
        if !ty_inf.unifies(candidate_input_ty, span, constraint_input_ty, span)? {
            return Ok(false);
        }
    }
    for (&candidate_output_ty, &constraint_output_ty) in candidate_outputs.iter().zip(output_tys) {
        if !ty_inf.unifies(candidate_output_ty, span, constraint_output_ty, span)? {
            return Ok(false);
        }
    }
    constraints_may_be_satisfiable(
        current,
        others,
        ty_inf,
        pending.to_vec(),
        next_ty_var_index,
        stack,
    )
}

#[allow(clippy::too_many_arguments)]
fn blanket_impl_may_match_constraint(
    current: &Module,
    others: &Modules,
    ty_inf: &mut CoherenceTypeUnifier,
    pending: &[ScopedConstraint],
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitId, Vec<Type>, Vec<Type>)>,
    (key, candidate_scope): (&BlanketTraitImplKey, ModuleId),
    imp: &TraitImpl,
    input_tys: &[Type],
    output_tys: &[Type],
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
    let candidate_inputs = erased(&instantiate_types(&key.sub_key.input_tys, &mut mapper));
    let candidate_outputs = erased(&instantiate_types(&imp.output_tys, &mut mapper));

    let span = Location::new_synthesized();
    for (&candidate_input_ty, &constraint_input_ty) in candidate_inputs.iter().zip(input_tys) {
        if !ty_inf.unifies(candidate_input_ty, span, constraint_input_ty, span)? {
            return Ok(false);
        }
    }
    for (&candidate_output_ty, &constraint_output_ty) in candidate_outputs.iter().zip(output_tys) {
        if !ty_inf.unifies(candidate_output_ty, span, constraint_output_ty, span)? {
            return Ok(false);
        }
    }
    let candidate_constraints = erased(&instantiate_types(&key.sub_key.constraints, &mut mapper));
    let mut pending = pending.to_vec();
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
            generic_names: ImplGenericNames::default(),
            module_id,
        },
        TraitKey::Blanket(key) => InternalTraitImplHeader {
            input_tys: key.sub_key.input_tys.clone(),
            output_tys: imp.output_tys.clone(),
            ty_var_count: key.sub_key.ty_var_count,
            constraints: key.sub_key.constraints.clone(),
            generic_names: imp.generic_names.clone(),
            module_id,
        },
    }
}
