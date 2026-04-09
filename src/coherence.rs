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
    error::{InternalCompilationError, InternalTraitImplHeader},
    internal_compilation_error,
    ir::NodeArena,
    module::{
        BlanketTraitImplKey, BlanketTraitImplSubKey, ConcreteTraitImplKey, Module, ModuleId,
        TraitImpl, TraitKey,
    },
    r#trait::TraitRef,
    trait_solver::{TraitSolver, trait_solver_from_module},
    r#type::{Type, TypeVar},
    type_inference::UnifiedTypeInference,
    type_like::TypeLike,
    type_like::instantiate_types,
    type_scheme::PubTypeConstraint,
};

pub(crate) fn check_trait_impl(
    current: &Module,
    others: &Modules,
    trait_ref: &TraitRef,
    trait_is_local: bool,
    input_tys: &[Type],
    ty_var_count: u32,
    constraints: &[PubTypeConstraint],
    span: Location,
) -> Result<(), InternalCompilationError> {
    if !trait_is_local
        && !input_tys
            .iter()
            .any(|&ty| has_local_named_head(current, ty))
    {
        return Err(internal_compilation_error!(TraitImplOrphanRuleViolation {
            trait_ref: trait_ref.clone(),
            input_tys: input_tys.to_vec(),
            impl_span: span,
        }));
    }

    let new_key = if ty_var_count == 0 {
        TraitKey::Concrete(ConcreteTraitImplKey::new(
            trait_ref.clone(),
            input_tys.to_vec(),
        ))
    } else {
        TraitKey::Blanket(BlanketTraitImplKey::new(
            trait_ref.clone(),
            BlanketTraitImplSubKey::new(input_tys.to_vec(), ty_var_count, constraints.to_vec()),
        ))
    };

    for (key, imp, module_id) in iter_visible_impls(current, others) {
        if key.trait_ref() != trait_ref {
            continue;
        }
        if impls_overlap(current, others, &new_key, &key)? {
            return Err(internal_compilation_error!(OverlappingTraitImpls {
                trait_ref: trait_ref.clone(),
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
        .is_some_and(|named| current.owns_type_def(&named.def))
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
        .flat_map(|(trait_ref, blanket_impls)| {
            blanket_impls.iter().map(|(sub_key, &id)| {
                (
                    TraitKey::Blanket(BlanketTraitImplKey::new(trait_ref.clone(), sub_key.clone())),
                    current.impls.get_impl_by_local_id(id),
                    None,
                )
            })
        });
    let imported = others.enumerates().flat_map(|(module_id, entry, _)| {
        entry.module().into_iter().flat_map(move |module| {
            let concrete = module.impls.concrete().iter().map(move |(key, &id)| {
                (
                    TraitKey::Concrete(key.clone()),
                    module.impls.get_impl_by_local_id(id),
                    Some(module_id),
                )
            });
            let blankets =
                module
                    .impls
                    .blanket()
                    .iter()
                    .flat_map(move |(trait_ref, blanket_impls)| {
                        blanket_impls.iter().map(move |(sub_key, &id)| {
                            (
                                TraitKey::Blanket(BlanketTraitImplKey::new(
                                    trait_ref.clone(),
                                    sub_key.clone(),
                                )),
                                module.impls.get_impl_by_local_id(id),
                                Some(module_id),
                            )
                        })
                    });
            concrete.chain(blankets)
        })
    });
    local.chain(local_blankets).chain(imported)
}

fn impls_overlap(
    current: &Module,
    others: &Modules,
    new_key: &TraitKey,
    existing_key: &TraitKey,
) -> Result<bool, InternalCompilationError> {
    use TraitKey::*;
    let overlap = match (new_key, existing_key) {
        (Concrete(new_key), Concrete(existing_key)) => new_key.input_tys == existing_key.input_tys,
        (Concrete(new_key), Blanket(existing_key)) => {
            blanket_matches_concrete(current, others, &existing_key.sub_key, &new_key.input_tys)?
        }
        (Blanket(new_key), Concrete(existing_key)) => {
            blanket_matches_concrete(current, others, &new_key.sub_key, &existing_key.input_tys)?
        }
        (Blanket(new_key), Blanket(existing_key)) => {
            blanket_impls_overlap(current, others, &new_key.sub_key, &existing_key.sub_key)?
        }
    };
    Ok(overlap)
}

fn blanket_matches_concrete(
    current: &Module,
    others: &Modules,
    blanket: &BlanketTraitImplSubKey,
    concrete_inputs: &[Type],
) -> Result<bool, InternalCompilationError> {
    if blanket.input_tys.len() != concrete_inputs.len() {
        return Ok(false);
    }

    let span = Location::new_synthesized();
    let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(blanket.ty_var_count);
    for (&blanket_input, &concrete_input) in blanket.input_tys.iter().zip(concrete_inputs) {
        if ty_inf
            .unify_same_type(blanket_input, span, concrete_input, span)
            .is_err()
        {
            return Ok(false);
        }
    }

    let mut scratch_module = current.clone();
    let mut arena = NodeArena::default();
    let mut trait_solver = trait_solver_from_module!(scratch_module, others);
    let mut remaining_indices: Vec<_> = (0..blanket.constraints.len()).collect();
    loop {
        let initial_count = remaining_indices.len();
        let mut still_remaining = Vec::new();
        for constraint_idx in remaining_indices {
            let constraint = &blanket.constraints[constraint_idx];
            let (trait_ref, input_tys, output_tys, _) = ty_inf
                .substitute_in_constraint(constraint)
                .into_have_trait()
                .expect("Non trait constraint in blanket impl");
            if !input_tys.iter().all(Type::is_constant) {
                still_remaining.push(constraint_idx);
                continue;
            }
            let solved_output_tys: Vec<Type> =
                match trait_solver.solve_output_types(&trait_ref, &input_tys, span, &mut arena) {
                    Ok(tys) => tys,
                    Err(_) => return Ok(false),
                };
            for (&solved_output_ty, &output_ty) in solved_output_tys.iter().zip(&output_tys) {
                if ty_inf
                    .unify_same_type(solved_output_ty, span, output_ty, span)
                    .is_err()
                {
                    return Ok(false);
                }
            }
        }

        if still_remaining.is_empty() {
            return Ok(true);
        }
        if still_remaining.len() == initial_count {
            return Ok(false);
        }
        remaining_indices = still_remaining;
    }
}

fn blanket_impls_overlap(
    current: &Module,
    others: &Modules,
    lhs: &BlanketTraitImplSubKey,
    rhs: &BlanketTraitImplSubKey,
) -> Result<bool, InternalCompilationError> {
    if lhs.input_tys.len() != rhs.input_tys.len() {
        return Ok(false);
    }

    let rhs_ty_subst: FxHashMap<_, _> = (0..rhs.ty_var_count)
        .map(|index| {
            let var = TypeVar::new(index);
            let shifted = Type::variable_id(lhs.ty_var_count + index);
            (var, shifted)
        })
        .collect();
    let rhs_inputs = instantiate_types(
        &rhs.input_tys,
        &(rhs_ty_subst.clone(), FxHashMap::default()),
    );
    let rhs_constraints =
        instantiate_types(&rhs.constraints, &(rhs_ty_subst, FxHashMap::default()));
    let span = Location::new_synthesized();
    let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(lhs.ty_var_count + rhs.ty_var_count);
    for (&lhs_ty, &rhs_ty) in lhs.input_tys.iter().zip(rhs_inputs.iter()) {
        if ty_inf.unify_same_type(lhs_ty, span, rhs_ty, span).is_err() {
            return Ok(false);
        }
    }
    let mut pending = lhs.constraints.clone();
    pending.extend(rhs_constraints);
    constraints_may_be_satisfiable(
        current,
        others,
        ty_inf,
        pending,
        lhs.ty_var_count + rhs.ty_var_count,
        &mut FxHashSet::default(),
    )
}

fn constraints_may_be_satisfiable(
    current: &Module,
    others: &Modules,
    mut ty_inf: UnifiedTypeInference,
    mut pending: Vec<PubTypeConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitRef, Vec<Type>, Vec<Type>)>,
) -> Result<bool, InternalCompilationError> {
    if pending.is_empty() {
        return Ok(true);
    }

    let constraint = pending.pop().unwrap();
    let constraint = ty_inf.substitute_in_constraint(&constraint);
    let (trait_ref, input_tys, output_tys, _span) = constraint
        .into_have_trait()
        .expect("Non trait constraint in blanket impl overlap check");
    if input_tys.iter().all(Type::is_constant) {
        let mut scratch_module = current.clone();
        let mut arena = NodeArena::default();
        let mut trait_solver = trait_solver_from_module!(scratch_module, others);
        let solved_output_tys = match trait_solver.solve_output_types(
            &trait_ref,
            &input_tys,
            Location::new_synthesized(),
            &mut arena,
        ) {
            Ok(tys) => tys,
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
        &trait_ref,
        &input_tys,
        &output_tys,
    )
}

fn trait_constraint_may_be_satisfiable(
    current: &Module,
    others: &Modules,
    ty_inf: UnifiedTypeInference,
    pending: Vec<PubTypeConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitRef, Vec<Type>, Vec<Type>)>,
    trait_ref: &TraitRef,
    input_tys: &[Type],
    output_tys: &[Type],
) -> Result<bool, InternalCompilationError> {
    let query = (trait_ref.clone(), input_tys.to_vec(), output_tys.to_vec());
    if !stack.insert(query.clone()) {
        return Ok(true);
    }

    for (key, imp, _) in iter_visible_impls(current, others) {
        if key.trait_ref() != trait_ref {
            continue;
        }

        let result = match &key {
            TraitKey::Concrete(key) => concrete_impl_may_match_constraint(
                current,
                others,
                ty_inf.clone(),
                pending.clone(),
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
                ty_inf.clone(),
                pending.clone(),
                next_ty_var_index,
                stack,
                key,
                imp,
                input_tys,
                output_tys,
            )?,
        };
        if result {
            stack.remove(&query);
            return Ok(true);
        }
    }

    stack.remove(&query);
    Ok(!trait_ref.derives.is_empty())
}

#[allow(clippy::too_many_arguments)]
fn concrete_impl_may_match_constraint(
    current: &Module,
    others: &Modules,
    mut ty_inf: UnifiedTypeInference,
    pending: Vec<PubTypeConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitRef, Vec<Type>, Vec<Type>)>,
    key: &ConcreteTraitImplKey,
    imp: &TraitImpl,
    input_tys: &[Type],
    output_tys: &[Type],
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
    constraints_may_be_satisfiable(current, others, ty_inf, pending, next_ty_var_index, stack)
}

#[allow(clippy::too_many_arguments)]
fn blanket_impl_may_match_constraint(
    current: &Module,
    others: &Modules,
    mut ty_inf: UnifiedTypeInference,
    mut pending: Vec<PubTypeConstraint>,
    next_ty_var_index: u32,
    stack: &mut FxHashSet<(TraitRef, Vec<Type>, Vec<Type>)>,
    key: &BlanketTraitImplKey,
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
    let inst_subst = (candidate_ty_subst, FxHashMap::default());
    let candidate_inputs = instantiate_types(&key.sub_key.input_tys, &inst_subst);
    let candidate_outputs = instantiate_types(&imp.output_tys, &inst_subst);
    let candidate_constraints = instantiate_types(&key.sub_key.constraints, &inst_subst);

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
