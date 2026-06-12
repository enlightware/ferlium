// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    FxHashMap, FxHashSet, Location, Modules,
    compiler::error::{InternalCompilationError, InternalTraitImplHeader},
    hir::NodeArena,
    internal_compilation_error,
    module::{
        BlanketTraitImplKey, BlanketTraitImplSubKey, ConcreteTraitImplKey, Module, ModuleEnv,
        ModuleId, TraitId, TraitImpl, TraitKey,
    },
    std::value::{NO_DERIVE_VALUE_ATTRIBUTE, is_value_trait},
    types::effects::{EffType, EffectsInstSubst},
    types::r#trait::TraitImplPolicy,
    types::trait_solver::TraitSolverProbe,
    types::r#type::{Type, TypeKind, TypeVar},
    types::type_inference::unify::{UnifiedTypeInference, UnifiedTypeInferenceSnapshot},
    types::type_like::TypeLike,
    types::type_like::instantiate_types,
    types::type_mapper::{BitmapInstantiationMapper, SimpleInstantiationMapper, TypeMapper},
    types::type_scheme::PubTypeConstraint,
};
use ustr::ustr;

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

    fn unify_same_type(
        &mut self,
        current: Type,
        current_span: Location,
        expected: Type,
        expected_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.inner
            .unify_same_type(current, current_span, expected, expected_span)
    }

    fn unify_same_effect(
        &mut self,
        current: EffType,
        current_span: Location,
        expected: EffType,
        expected_span: Location,
    ) -> Result<(), InternalCompilationError> {
        self.inner
            .unify_same_effect(current, current_span, expected, expected_span)
    }

    fn fresh_effect_var_subst_for(
        &mut self,
        constraints: &[PubTypeConstraint],
        effs: &[EffType],
    ) -> EffectsInstSubst {
        self.inner.fresh_effect_var_subst_for(constraints, effs)
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
    output_effs: &[EffType],
    ty_var_count: u32,
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

    let new_key = if ty_var_count == 0 {
        TraitKey::Concrete(ConcreteTraitImplKey::new(trait_id, input_tys.to_vec()))
    } else {
        TraitKey::Blanket(BlanketTraitImplKey::new(
            trait_id,
            BlanketTraitImplSubKey::new(input_tys.to_vec(), ty_var_count, constraints.to_vec()),
        ))
    };

    for (key, imp, module_id) in iter_visible_impls(current, others) {
        if key.trait_id() != trait_id {
            continue;
        }
        if impls_overlap(
            current,
            others,
            &new_key,
            output_tys,
            output_effs,
            &key,
            imp.output_tys.as_slice(),
            imp.output_effs.as_slice(),
        )? {
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
        crate::types::r#type::TypeKind::Tuple(_)
            | crate::types::r#type::TypeKind::Record(_)
            | crate::types::r#type::TypeKind::Variant(_)
            | crate::types::r#type::TypeKind::Function(_)
    )
}

fn iter_visible_impls<'a>(
    current: &'a Module,
    others: &'a Modules,
) -> impl Iterator<Item = (TraitKey, &'a TraitImpl, Option<ModuleId>)> + 'a {
    let local = current.impls.concrete().iter().map(|(key, &id)| {
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
        .flat_map(|(trait_id, blanket_impls)| {
            blanket_impls.iter().map(|(sub_key, &id)| {
                (
                    TraitKey::Blanket(BlanketTraitImplKey::new(*trait_id, sub_key.clone())),
                    current.impls.get_impl_by_local_id(id),
                    None,
                )
            })
        });
    let imported = others.enumerates().flat_map(|(module_id, entry, _)| {
        entry.module().into_iter().flat_map(move |module| {
            let concrete = module
                .impls
                .concrete()
                .iter()
                .map(move |(key, &id)| {
                    (
                        TraitKey::Concrete(key.clone()),
                        module.impls.get_impl_by_local_id(id),
                        Some(module_id),
                    )
                })
                .filter(|(_, imp, _)| imp.public);
            let blankets = module
                .impls
                .blanket()
                .iter()
                .flat_map(move |(trait_id, blanket_impls)| {
                    blanket_impls.iter().map(move |(sub_key, &id)| {
                        (
                            TraitKey::Blanket(BlanketTraitImplKey::new(*trait_id, sub_key.clone())),
                            module.impls.get_impl_by_local_id(id),
                            Some(module_id),
                        )
                    })
                })
                .filter(|(_, imp, _)| imp.public);
            concrete.chain(blankets)
        })
    });
    local.chain(local_blankets).chain(imported)
}

#[allow(clippy::too_many_arguments)]
fn impls_overlap(
    current: &Module,
    others: &Modules,
    new_key: &TraitKey,
    new_output_tys: &[Type],
    new_output_effs: &[EffType],
    existing_key: &TraitKey,
    existing_output_tys: &[Type],
    existing_output_effs: &[EffType],
) -> Result<bool, InternalCompilationError> {
    use TraitKey::*;
    let overlap = match (new_key, existing_key) {
        (Concrete(new_key), Concrete(existing_key)) => new_key.input_tys == existing_key.input_tys,
        (Concrete(new_key), Blanket(existing_key)) => blanket_impls_overlap(
            current,
            others,
            &concrete_as_blanket_sub_key(&new_key.input_tys),
            new_output_tys,
            new_output_effs,
            &existing_key.sub_key,
            existing_output_tys,
            existing_output_effs,
        )?,
        (Blanket(new_key), Concrete(existing_key)) => blanket_impls_overlap(
            current,
            others,
            &new_key.sub_key,
            new_output_tys,
            new_output_effs,
            &concrete_as_blanket_sub_key(&existing_key.input_tys),
            existing_output_tys,
            existing_output_effs,
        )?,
        (Blanket(new_key), Blanket(existing_key)) => blanket_impls_overlap(
            current,
            others,
            &new_key.sub_key,
            new_output_tys,
            new_output_effs,
            &existing_key.sub_key,
            existing_output_tys,
            existing_output_effs,
        )?,
    };
    Ok(overlap)
}

fn concrete_as_blanket_sub_key(input_tys: &[Type]) -> BlanketTraitImplSubKey {
    BlanketTraitImplSubKey::new(input_tys.to_vec(), 0, Vec::new())
}

#[allow(clippy::too_many_arguments)]
fn blanket_impls_overlap(
    current: &Module,
    others: &Modules,
    lhs: &BlanketTraitImplSubKey,
    lhs_output_tys: &[Type],
    lhs_output_effs: &[EffType],
    rhs: &BlanketTraitImplSubKey,
    rhs_output_tys: &[Type],
    rhs_output_effs: &[EffType],
) -> Result<bool, InternalCompilationError> {
    if lhs.input_tys.len() != rhs.input_tys.len() {
        return Ok(false);
    }

    let span = Location::new_synthesized();
    let mut ty_inf = CoherenceTypeUnifier::new_with_ty_vars(lhs.ty_var_count + rhs.ty_var_count);

    // Both sides use raw effect variable indices, so each side is renamed to
    // its own fresh inference effect variables before unification.
    let lhs_eff_subst = ty_inf.fresh_effect_var_subst_for(&lhs.constraints, lhs_output_effs);
    let lhs_inst_subst = (FxHashMap::default(), lhs_eff_subst);
    let mut lhs_mapper = SimpleInstantiationMapper::new(&lhs_inst_subst);
    let lhs_constraints = instantiate_types(&lhs.constraints, &mut lhs_mapper);
    let lhs_output_effs: Vec<_> = lhs_output_effs
        .iter()
        .map(|eff| lhs_mapper.map_effect_type(eff))
        .collect();

    let rhs_ty_subst: FxHashMap<_, _> = (0..rhs.ty_var_count)
        .map(|index| {
            let var = TypeVar::new(index);
            let shifted = Type::variable_id(lhs.ty_var_count + index);
            (var, shifted)
        })
        .collect();
    let rhs_eff_subst = ty_inf.fresh_effect_var_subst_for(&rhs.constraints, rhs_output_effs);
    let inst_subst = (rhs_ty_subst, rhs_eff_subst);
    let mut mapper = SimpleInstantiationMapper::new(&inst_subst);
    let rhs_inputs = instantiate_types(&rhs.input_tys, &mut mapper);
    let rhs_outputs = instantiate_types(rhs_output_tys, &mut mapper);
    let rhs_output_effs: Vec<_> = rhs_output_effs
        .iter()
        .map(|eff| mapper.map_effect_type(eff))
        .collect();
    let rhs_constraints = instantiate_types(&rhs.constraints, &mut mapper);
    for (&lhs_ty, &rhs_ty) in lhs.input_tys.iter().zip(rhs_inputs.iter()) {
        if ty_inf.unify_same_type(lhs_ty, span, rhs_ty, span).is_err() {
            return Ok(false);
        }
    }
    for (&lhs_output_ty, &rhs_output_ty) in lhs_output_tys.iter().zip(rhs_outputs.iter()) {
        if ty_inf
            .unify_same_type(lhs_output_ty, span, rhs_output_ty, span)
            .is_err()
        {
            return Ok(false);
        }
    }
    for (lhs_output_eff, rhs_output_eff) in lhs_output_effs.iter().zip(rhs_output_effs.iter()) {
        if ty_inf
            .unify_same_effect(lhs_output_eff.clone(), span, rhs_output_eff.clone(), span)
            .is_err()
        {
            return Ok(false);
        }
    }
    let mut pending = lhs_constraints;
    pending.extend(rhs_constraints);
    constraints_may_be_satisfiable(
        current,
        others,
        &mut ty_inf,
        pending,
        lhs.ty_var_count + rhs.ty_var_count,
        &mut FxHashSet::default(),
    )
}

fn constraints_may_be_satisfiable(
    current: &Module,
    others: &Modules,
    ty_inf: &mut CoherenceTypeUnifier,
    mut pending: Vec<PubTypeConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitId, Vec<Type>, Vec<Type>)>,
) -> Result<bool, InternalCompilationError> {
    if pending.is_empty() {
        return Ok(true);
    }

    let constraint = pending.pop().unwrap();
    let constraint = ty_inf.substitute_in_constraint(&constraint);
    let (trait_id, input_tys, output_tys, output_effs, _span) = constraint
        .into_have_trait()
        .expect("Non trait constraint in blanket impl overlap check");
    if input_tys.iter().all(Type::is_constant) && output_tys.iter().all(Type::is_constant) {
        let mut trait_solver = TraitSolverProbe::from_module(current, others);
        let mut arena = NodeArena::default();
        let (solved_output_tys, solved_output_effs) = match trait_solver.solve_outputs(
            trait_id,
            &input_tys,
            Location::new_synthesized(),
            &mut arena,
        ) {
            Ok(outputs) => outputs,
            Err(_) => return Ok(false),
        };
        for (&solved_output_ty, &output_ty) in solved_output_tys.iter().zip(&output_tys) {
            if ty_inf
                .unify_same_type(
                    solved_output_ty,
                    Location::new_synthesized(),
                    output_ty,
                    Location::new_synthesized(),
                )
                .is_err()
            {
                return Ok(false);
            }
        }
        for (solved_output_eff, output_eff) in solved_output_effs.iter().zip(&output_effs) {
            if ty_inf
                .unify_same_effect(
                    solved_output_eff.clone(),
                    Location::new_synthesized(),
                    output_eff.clone(),
                    Location::new_synthesized(),
                )
                .is_err()
            {
                return Ok(false);
            }
        }
        return constraints_may_be_satisfiable(
            current,
            others,
            ty_inf,
            pending,
            next_ty_var_index,
            stack,
        );
    }

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
    )
}

#[allow(clippy::too_many_arguments)]
fn trait_constraint_may_be_satisfiable(
    current: &Module,
    others: &Modules,
    ty_inf: &mut CoherenceTypeUnifier,
    pending: Vec<PubTypeConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitId, Vec<Type>, Vec<Type>)>,
    trait_id: TraitId,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
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
    if !stack.insert(query.clone()) {
        return Ok(true);
    }

    for (key, imp, _) in iter_visible_impls(current, others) {
        if key.trait_id() != trait_id {
            continue;
        }

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
                key,
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
    pending: Vec<PubTypeConstraint>,
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
            .unify_same_type(candidate_input_ty, span, constraint_input_ty, span)
            .is_err()
        {
            return Ok(false);
        }
    }
    for (&candidate_output_ty, &constraint_output_ty) in imp.output_tys.iter().zip(output_tys) {
        if ty_inf
            .unify_same_type(candidate_output_ty, span, constraint_output_ty, span)
            .is_err()
        {
            return Ok(false);
        }
    }
    for (candidate_output_eff, constraint_output_eff) in imp.output_effs.iter().zip(output_effs) {
        if ty_inf
            .unify_same_effect(
                candidate_output_eff.clone(),
                span,
                constraint_output_eff.clone(),
                span,
            )
            .is_err()
        {
            return Ok(false);
        }
    }
    constraints_may_be_satisfiable(current, others, ty_inf, pending, next_ty_var_index, stack)
}

#[allow(clippy::too_many_arguments)]
fn blanket_impl_may_match_constraint(
    current: &Module,
    others: &Modules,
    ty_inf: &mut CoherenceTypeUnifier,
    mut pending: Vec<PubTypeConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitId, Vec<Type>, Vec<Type>)>,
    key: &BlanketTraitImplKey,
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
    let candidate_eff_subst =
        ty_inf.fresh_effect_var_subst_for(&key.sub_key.constraints, &imp.output_effs);
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
            .unify_same_type(candidate_input_ty, span, constraint_input_ty, span)
            .is_err()
        {
            return Ok(false);
        }
    }
    for (&candidate_output_ty, &constraint_output_ty) in candidate_outputs.iter().zip(output_tys) {
        if ty_inf
            .unify_same_type(candidate_output_ty, span, constraint_output_ty, span)
            .is_err()
        {
            return Ok(false);
        }
    }
    for (candidate_output_eff, constraint_output_eff) in
        candidate_output_effs.iter().zip(output_effs)
    {
        if ty_inf
            .unify_same_effect(
                candidate_output_eff.clone(),
                span,
                constraint_output_eff.clone(),
                span,
            )
            .is_err()
        {
            return Ok(false);
        }
    }
    pending.extend(candidate_constraints);
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
