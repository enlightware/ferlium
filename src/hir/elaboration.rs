// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{FxHashMap, FxHashSet, Modules};
use ustr::{Ustr, ustr};

use crate::{
    Location,
    compiler::{diagnostics::CompilationWarning, error::InternalCompilationError},
    hir::hir_syn::{call_dictionary_function, get_dictionary, static_apply},
    hir::{
        dictionary::{
            DictElaborationCtx, DictionaryReq, ExtraParameters, LateFunctionInstData,
            find_projection_subscript_dict_index,
            find_projection_subscript_dict_index_for_receiver_ty, find_trait_impl_dict_index,
            find_variant_payload_indirection_index, find_variant_payload_layout_index,
            instantiate_dictionary_requirements,
        },
        value_dispatch::{resolve_local_clone, resolve_local_drop},
    },
    internal_compilation_error,
    module::{
        ELocalDecl, ExtraParameterId, FunctionId, GeneratedStructuralProjectionSpec, LocalDecl,
        LocalDeclId, LocalFunctionId, Module, ModuleEnv, PendingLocalClone, PendingLocalDrop,
        PendingModuleFunction, PendingTakeLocalValueMode, ProjectionIndex, ProjectionKey,
        ResolvedLocalClone, ResolvedLocalDrop, SubscriptId, SubscriptMemberKind, TraitId, id::Id,
    },
    types::r#trait::{TraitDictionaryEntryIndex, TraitMethodIndex},
    types::trait_solver::{TraitSolver, trait_solver_from_module},
};
use itertools::process_results;

use crate::{
    containers::{SVec2, b},
    hir::emit_value_impl::{function_value_method, generic_value_methods_for_type},
    hir::value::LiteralValue,
    hir::{
        self, ArgConvention, CallArgument, ENodeArena, ENodeId, Elaborated, Node, NodeArena,
        NodeKind, Project as HirProject, StaticApplication, UNodeArena, UNodeId, Unelaborated,
        VariantPayloadStorageSource,
    },
    std::value::{
        is_function_surface_only_value_trait_application, is_value_trait_for_function_type,
        type_has_static_layout, value_layout_associated_const_values,
        variant_payload_storage_for_type,
    },
    types::effects::{EffType, Effect, EffectsInstSubst, no_effects},
    types::mutability::MutType,
    types::r#type::{
        CallImplType, CallResultConvention, FnArgType, FnType, Type, TypeKind, TypeVar,
    },
    types::type_mapper::BitmapInstantiationMapper,
};

/// Build the use-site HIR expression for a generated `Value` dictionary.
fn value_dictionary_node_kind_from_methods(
    trait_id: TraitId,
    input_tys: &[Type],
    span: Location,
    methods: Vec<LocalFunctionId>,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let (dictionary, ty) = ctx
        .trait_solver
        .materialize_generated_value_impl_from_methods(trait_id, input_tys, span, methods)?;
    Ok((get_dictionary(dictionary), ty))
}

/// Build the compiler-provided `Value` dictionary for a concrete function type.
fn function_value_dictionary_node_kind(
    trait_id: TraitId,
    input_tys: &[Type],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let method_count = ctx.trait_solver.trait_def(trait_id).methods.len();
    let methods = (0..method_count)
        .map(TraitMethodIndex::from_index)
        .map(|method_index| function_value_method(ctx.trait_solver, method_index, span))
        .collect::<Result<Vec<_>, _>>()?;
    value_dictionary_node_kind_from_methods(trait_id, input_tys, span, methods, ctx)
}

/// Build a generated `Value` dictionary for a structural type whose unresolved
/// type variables appear only inside function types.
fn generic_derived_value_dictionary_node_kind(
    arena: &mut NodeArena,
    trait_id: TraitId,
    input_tys: &[Type],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let methods =
        generic_value_methods_for_type(ctx.trait_solver, trait_id, input_tys, span, arena)?;
    value_dictionary_node_kind_from_methods(trait_id, input_tys, span, methods, ctx)
}

/// Build the HIR expression that provides the runtime dictionary for a trait requirement.
#[allow(clippy::too_many_arguments)]
fn trait_dictionary_node_kind(
    arena: &mut NodeArena,
    trait_id: TraitId,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
) -> Result<(NodeKind, Type), InternalCompilationError> {
    let trait_def = ctx.trait_solver.trait_def(trait_id);
    if is_value_trait_for_function_type(trait_id, trait_def, input_tys, output_tys) {
        return function_value_dictionary_node_kind(trait_id, input_tys, span, ctx);
    }

    let trait_def = ctx.trait_solver.trait_def(trait_id);
    if is_function_surface_only_value_trait_application(trait_id, trait_def, input_tys, output_tys)
    {
        return generic_derived_value_dictionary_node_kind(arena, trait_id, input_tys, span, ctx);
    }

    let ty = ctx
        .trait_solver
        .trait_def(trait_id)
        .get_dictionary_type_for_tys(input_tys, output_tys, output_effs);

    let node_kind = if input_tys.iter().all(|ty| ty.is_trait_input_resolved()) {
        let dictionary = ctx
            .trait_solver
            .solve_impl(trait_id, input_tys, span, arena)?;
        NodeKind::GetDictionary(hir::GetDictionary { dictionary })
    } else {
        let index = find_trait_impl_dict_index(ctx.dicts, trait_id, input_tys).unwrap_or_else(|| {
            panic!(
                "dictionary for trait {trait_id:?} with inputs {input_tys:?} was not found in caller requirements {:?}; type inference should have failed",
                ctx.dicts.requirements
            )
        });
        NodeKind::LoadDictionary(hir::LoadDictionary {
            extra_parameter: ExtraParameterId::from_index(index),
        })
    };
    Ok((node_kind, ty))
}

/// Return the method slot and callable type from an already-instantiated dictionary type.
fn dictionary_method_projection_data(
    trait_def: &crate::types::r#trait::Trait,
    dictionary_ty: Type,
    method_index: TraitMethodIndex,
) -> (TraitDictionaryEntryIndex, Type) {
    let entry_index = trait_def.dictionary_method_index(method_index);
    let function_ty = dictionary_ty
        .data()
        .as_tuple()
        .expect("Trait impl dict should be a tuple type")[usize::from(entry_index)];
    (entry_index, function_ty)
}

fn get_projection_subscript_node_kind(
    subscript: SubscriptId,
    name: Ustr,
    span: Location,
) -> NodeKind {
    NodeKind::GetSubscript(b(hir::GetSubscript {
        subscript,
        subscript_path: crate::ast::Path::new(vec![(name, span)]),
        inst_data: hir::FnInstData::none(),
    }))
}

fn extra_arg_kind_from_inst_data(
    inst_data: &hir::FnInstData,
    span: Location,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    arena: &mut NodeArena,
) -> Result<Vec<(NodeKind, Type, FnArgType)>, InternalCompilationError> {
    use NodeKind as K;
    use TypeKind::*;
    process_results(inst_data
        .dicts_req
        .iter()
        .map(|dict| {
            use DictionaryReq::*;
            let (node_kind, node_ty) = match dict {
                ProjectionSubscript {
                    requirement,
                    field: name,
                    subscript_ty,
                } => {
                    let ty = subscript_ty.receiver_ty();
                    let expected_node_ty = Type::subscript_type(subscript_ty.clone());
                    let expected_arg_ty = FnArgType::new_by_val(expected_node_ty);
                    let generated = ctx
                        .generated_projection_subscripts
                        .as_mut()
                        .expect("projection evidence generation requires module elaboration");
                    let structural_key = ProjectionKey::structural(ty, *name);
                    if let Some(subscript) = generated.get_existing(structural_key) {
                        let node_kind = get_projection_subscript_node_kind(subscript, *name, span);
                        return Ok((node_kind, expected_node_ty, expected_arg_ty));
                    }
                    if requirement.accepts_user_defined_projection()
                        && let Some(key) = ProjectionKey::nominal_for_receiver_ty(ty, *name)
                        && let Some(subscript) = ctx.trait_solver.projection_subscript_id(key)
                    {
                        let node_kind = get_projection_subscript_node_kind(subscript, *name, span);
                        return Ok((node_kind, expected_node_ty, expected_arg_ty));
                    }
                    let ty_kind = ty.data().clone();
                    let node_kind = match ty_kind {
                        Record(record) => {
                            let index = record.iter().position(|field| field.0 == *name).expect(
                                "Field not found in type, type inference should have failed"
                            );
                            let subscript =
                                generated.get_or_create(GeneratedStructuralProjectionSpec {
                                    key: structural_key,
                                    index,
                                    field_ty: subscript_ty.ret,
                                });
                            get_projection_subscript_node_kind(subscript, *name, span)
                        }
                        Named(named) => {
                            let shape = ctx
                                .trait_solver
                                .type_def(named.def)
                                .instantiated_shape_with_effects(
                                    &named.params,
                                    &named.effect_params,
                                );
                            let shape_data = shape.data();
                            let record = shape_data
                                .as_record()
                                .expect("ProjectionSubscript named receiver should have a record representation or explicit projection");
                            let index = record.iter().position(|field| field.0 == *name).expect(
                                "Field not found in type, type inference should have failed"
                            );
                            let subscript =
                                generated.get_or_create(GeneratedStructuralProjectionSpec {
                                    key: structural_key,
                                    index,
                                    field_ty: subscript_ty.ret,
                                });
                            get_projection_subscript_node_kind(subscript, *name, span)
                        }
                        Variable(var) => {
                            let index = find_projection_subscript_dict_index(ctx.dicts, var, name).unwrap_or_else(
                                || panic!("Projection subscript dictionary for field \"{name}\" in type variable \"{var}\" not found, type inference should have failed"),
                            );
                            K::LoadSubscriptEvidence(hir::LoadSubscriptEvidence {
                                extra_parameter: ExtraParameterId::from_index(index),
                            })
                        }
                        _ => {
                            panic!("ProjectionSubscript dictionary should have a variable or record type");
                        }
                    };
                    (node_kind, expected_node_ty)
                }
                VariantPayloadIndirection {
                    variant_ty,
                    tag,
                    ..
                } => {
                    let node_ty = Type::primitive::<bool>();
                    if matches!(&*variant_ty.data(), TypeKind::Variable(_)) {
                        let index = find_variant_payload_indirection_index(
                            ctx.dicts,
                            *variant_ty,
                            *tag,
                        )
                        .ok_or_else(|| {
                            internal_compilation_error!(Internal {
                                error: format!(
                                    "variant payload-indirection evidence {dict:?} not found in generic caller requirements {:?}",
                                    ctx.dicts.requirements
                                ),
                                span,
                            })
                        })?;
                        (
                            K::LoadVariantPayloadStorageEvidence(
                                hir::LoadVariantPayloadStorageEvidence {
                                    extra_parameter: ExtraParameterId::from_index(index),
                                },
                            ),
                            node_ty,
                        )
                    } else {
                        let storage = variant_payload_storage_for_type(
                            *variant_ty,
                            *tag,
                            span,
                            ctx.trait_solver,
                        )?;
                        (K::Immediate(LiteralValue::new_native(storage.is_indirect())), node_ty)
                    }
                }
                TraitImpl { trait_id, input_tys, output_tys, output_effs } => {
                    let (node_kind, ty) = trait_dictionary_node_kind(
                        arena,
                        *trait_id,
                        input_tys,
                        output_tys,
                        output_effs,
                        span,
                        ctx,
                    )?;
                    (node_kind, ty)
                }
            };
            Ok((
                node_kind,
                node_ty,
                FnArgType::new(node_ty, MutType::constant()),
            ))
        }), |iter| iter.collect()
    )
}

/// Instantiate requirements that were discovered only after a recursive module call was inferred.
///
/// Recursive type inference can finalize a mutually recursive type world after the call's
/// preliminary `FnInstData` was recorded, so type identity is reconstructed from the final callee
/// surface, the call-site type, `Repr` relationships, and constraint payload edges. A preliminary
/// call may likewise predate final effect quantification: complete positional effect arguments are
/// used when present, otherwise the function surface reconstructs the missing mapping.
fn late_module_call_inst_data(
    callee: &LateFunctionInstData,
    call_ty: &FnType,
    call_inst_data: &hir::FnInstData,
    caller_requirements: &ExtraParameters,
    span: Location,
) -> Result<hir::FnInstData, InternalCompilationError> {
    let error = |message: String| {
        internal_compilation_error!(Internal {
            error: message,
            span,
        })
    };
    let mut ty_subst = FxHashMap::default();
    // Preserve the rooted correspondence between non-variable nodes in the final callee's type
    // graph and the call-site graph. Recursive graphs can be structurally symmetric even though
    // their nodes have distinct identities; the variable substitution alone loses that orientation.
    let mut type_correspondence = FxHashMap::default();
    let mut eff_subst = if call_inst_data.eff_args.len() == callee.effect_quantifiers.len() {
        callee
            .effect_quantifiers
            .iter()
            .copied()
            .zip(call_inst_data.eff_args.iter().cloned())
            .collect::<EffectsInstSubst>()
    } else {
        // Finalization may add or remove effect quantifiers. In that case preliminary positions do
        // not name the final universe and must not be replayed; reconstruct it below instead.
        EffectsInstSubst::default()
    };
    if callee.fn_ty.args.len() != call_ty.args.len() {
        return Err(error(format!(
            "late-instantiated call has arity {}, but its final callee has arity {}",
            call_ty.args.len(),
            callee.fn_ty.args.len()
        )));
    }
    let mut active = FxHashSet::default();
    for (pattern, actual) in callee.fn_ty.args.iter().zip(&call_ty.args) {
        if !bind_call_type_instantiation(
            pattern.ty,
            actual.ty,
            &mut ty_subst,
            &mut type_correspondence,
            &mut active,
        ) {
            return Err(error(format!(
                "late-instantiated call argument type {:?} does not match final callee type {:?}",
                actual.ty, pattern.ty
            )));
        }
        if !bind_type_effect_instantiation(
            pattern.ty,
            actual.ty,
            &mut eff_subst,
            &mut FxHashSet::default(),
        ) {
            return Err(error(format!(
                "cannot reconstruct effects for late-instantiated call argument types {:?} and {:?}",
                pattern.ty, actual.ty
            )));
        }
    }
    if !bind_call_type_instantiation(
        callee.fn_ty.ret,
        call_ty.ret,
        &mut ty_subst,
        &mut type_correspondence,
        &mut active,
    ) {
        return Err(error(format!(
            "late-instantiated call result type {:?} does not match final callee type {:?}",
            call_ty.ret, callee.fn_ty.ret
        )));
    }
    if !bind_type_effect_instantiation(
        callee.fn_ty.ret,
        call_ty.ret,
        &mut eff_subst,
        &mut FxHashSet::default(),
    ) {
        return Err(error(format!(
            "cannot reconstruct nested effects for late-instantiated result types {:?} and {:?}",
            callee.fn_ty.ret, call_ty.ret
        )));
    }
    if !bind_effect_instantiation(&callee.fn_ty.effects, &call_ty.effects, &mut eff_subst) {
        return Err(error(format!(
            "cannot reconstruct late call effects {:?} as {:?} with substitution {eff_subst:?}",
            callee.fn_ty.effects, call_ty.effects
        )));
    }
    if !bind_representation_type_instantiation(
        &callee.requirements,
        caller_requirements,
        &mut ty_subst,
    ) {
        return Err(error(
            "late call maps one representation variable to two caller types".into(),
        ));
    }
    bind_constraint_only_variant_types_with_correspondence(
        &callee.requirements,
        caller_requirements,
        &mut ty_subst,
        &mut type_correspondence,
    )
    .map_err(error)?;
    // Functions and associated lambdas in one recursive group share the final normalized effect
    // universe. A quantifier absent from both preliminary arguments and the function surface is
    // therefore an unchanged caller quantifier, not an unknown positional argument.
    for quantifier in &callee.effect_quantifiers {
        eff_subst
            .entry(*quantifier)
            .or_insert_with(|| EffType::single_variable(*quantifier));
    }
    let subst = (ty_subst, eff_subst);
    let mut mapper = BitmapInstantiationMapper::new(&subst);
    let dicts_req =
        instantiate_dictionary_requirements(&callee.requirements.requirements, &mut mapper);
    Ok(hir::FnInstData::new(
        dicts_req,
        call_inst_data.ty_args.clone(),
        call_inst_data.eff_args.clone(),
    ))
}

/// Carry the function-surface substitution through `Repr` relationships. Variant constraints are
/// stated on the representation variable, while a function argument can expose the user-facing
/// variable; both sides' `repr_map`s connect those identities without consulting a case tag.
fn bind_representation_type_instantiation(
    callee: &ExtraParameters,
    caller: &ExtraParameters,
    subst: &mut FxHashMap<TypeVar, Type>,
) -> bool {
    for (surface_var, repr_var) in &callee.repr_map {
        let Some(actual) = subst.get(surface_var).copied() else {
            continue;
        };
        let TypeKind::Variable(actual_var) = actual.data().clone() else {
            continue;
        };
        let actual_repr = *caller.repr_map.get(&actual_var).unwrap_or(&actual_var);
        if let Some(previous) = subst.insert(*repr_var, Type::variable(actual_repr)) {
            if previous != Type::variable(actual_repr) {
                return false;
            }
        }
    }
    true
}

/// Extend a late recursive-call substitution through variant constraints.
///
/// The function surface often maps only one node of a mutually recursive type world. Variant
/// storage and layout requirements retain both their enclosing type and payload type, so
/// matching the same kind of case requirement propagates that known mapping to the adjacent node.
/// A small backtracking search finds the unique globally compatible assignment; choosing
/// requirements greedily would not be confluent. A shared tag alone is never enough: two unrelated
/// `.Some` requirements remain ambiguous and cause an internal error rather than exchanging
/// evidence.
#[cfg(test)]
fn bind_constraint_only_variant_types(
    callee_requirements: &ExtraParameters,
    caller: &ExtraParameters,
    subst: &mut FxHashMap<TypeVar, Type>,
) -> Result<(), String> {
    bind_constraint_only_variant_types_with_correspondence(
        callee_requirements,
        caller,
        subst,
        &mut FxHashMap::default(),
    )
}

fn bind_constraint_only_variant_types_with_correspondence(
    callee_requirements: &ExtraParameters,
    caller: &ExtraParameters,
    subst: &mut FxHashMap<TypeVar, Type>,
    correspondence: &mut FxHashMap<Type, Type>,
) -> Result<(), String> {
    let requirements = variant_requirements(callee_requirements);
    let caller_requirements = variant_requirements(caller);
    let mut remaining = (0..requirements.len()).collect::<Vec<_>>();
    let mut solutions = Vec::new();
    search_variant_requirement_substitutions(
        &requirements,
        &caller_requirements,
        &mut remaining,
        VariantRequirementSubstitution {
            types: subst.clone(),
            correspondence: correspondence.clone(),
            used_caller_requirements: FxHashSet::default(),
        },
        &mut solutions,
    );
    if solutions.len() != 1 {
        return Err(format!(
            "late variant evidence requirements have {} globally compatible caller mappings; expected exactly one ({} callee requirements, {} caller requirements)",
            solutions.len(),
            requirements.len(),
            caller_requirements.len(),
        ));
    }
    let solution = solutions.pop().unwrap();
    *subst = solution.types;
    *correspondence = solution.correspondence;
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct VariantRequirementSubstitution {
    types: FxHashMap<TypeVar, Type>,
    correspondence: FxHashMap<Type, Type>,
    used_caller_requirements: FxHashSet<usize>,
}

fn search_variant_requirement_substitutions(
    requirements: &[VariantRequirement],
    caller: &[VariantRequirement],
    remaining: &mut Vec<usize>,
    subst: VariantRequirementSubstitution,
    solutions: &mut Vec<VariantRequirementSubstitution>,
) {
    if solutions.len() > 1 {
        return;
    }
    if remaining.is_empty() {
        if !solutions
            .iter()
            .any(|solution| solution.types == subst.types)
        {
            solutions.push(subst);
        }
        return;
    }

    // Branch first on the most constrained requirement. This does not affect correctness, but
    // keeps mutually recursive worlds with repeatedly named cases from exploring needless paths.
    let Some((position, trials)) = remaining
        .iter()
        .enumerate()
        .map(|(position, index)| {
            (
                position,
                compatible_variant_requirement_substitutions(requirements[*index], caller, &subst),
            )
        })
        .min_by_key(|(_, trials)| trials.len())
    else {
        return;
    };
    if trials.is_empty() {
        return;
    }
    let requirement = remaining.swap_remove(position);
    for trial in trials {
        search_variant_requirement_substitutions(requirements, caller, remaining, trial, solutions);
        if solutions.len() > 1 {
            break;
        }
    }
    remaining.push(requirement);
}

fn compatible_variant_requirement_substitutions(
    requirement: VariantRequirement,
    caller: &[VariantRequirement],
    subst: &VariantRequirementSubstitution,
) -> Vec<VariantRequirementSubstitution> {
    let VariantRequirement {
        kind,
        variant_ty,
        tag,
        payload_ty,
    } = requirement;
    let trials = caller
        .iter()
        .enumerate()
        .filter_map(|(candidate_index, candidate)| {
            if subst.used_caller_requirements.contains(&candidate_index) {
                return None;
            }
            let VariantRequirement {
                kind: candidate_kind,
                variant_ty: candidate_variant_ty,
                tag: candidate_tag,
                payload_ty: candidate_payload_ty,
            } = *candidate;
            if candidate_kind != kind || candidate_tag != tag {
                return None;
            }
            let mut trial = subst.clone();
            let mut active = FxHashSet::default();
            if !bind_call_type_instantiation(
                variant_ty,
                candidate_variant_ty,
                &mut trial.types,
                &mut trial.correspondence,
                &mut active,
            ) {
                return None;
            }
            if !bind_call_type_instantiation(
                payload_ty,
                candidate_payload_ty,
                &mut trial.types,
                &mut trial.correspondence,
                &mut active,
            ) {
                return None;
            }
            trial.used_caller_requirements.insert(candidate_index);
            let exact = variant_ty == candidate_variant_ty && payload_ty == candidate_payload_ty;
            Some((exact, trial))
        })
        .collect::<Vec<_>>();

    // An identical finalized requirement is already in the caller's type universe and is the
    // canonical match. Do not exchange it for an isomorphic recursive requirement that happens to
    // use the same case name; doing so would invent a mapping between otherwise independent type
    // worlds. Structural matching remains available when late finalization genuinely changed the
    // interned identities.
    let has_exact = trials.iter().any(|(exact, _)| *exact);
    trials
        .into_iter()
        .filter_map(|(exact, trial)| (!has_exact || exact).then_some(trial))
        .collect()
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum VariantEvidenceKind {
    Storage,
    Layout,
}

#[derive(Clone, Copy)]
struct VariantRequirement {
    kind: VariantEvidenceKind,
    variant_ty: Type,
    tag: Ustr,
    payload_ty: Type,
}

fn variant_requirements(parameters: &ExtraParameters) -> Vec<VariantRequirement> {
    let mut requirements = parameters
        .requirements
        .iter()
        .filter_map(|requirement| match requirement {
            DictionaryReq::VariantPayloadIndirection {
                variant_ty,
                tag,
                payload_ty,
            } => Some(VariantRequirement {
                kind: VariantEvidenceKind::Storage,
                variant_ty: *variant_ty,
                tag: *tag,
                payload_ty: *payload_ty,
            }),
            _ => None,
        })
        .collect::<Vec<_>>();
    requirements.extend(parameters.variant_payload_layouts.iter().map(|binding| {
        VariantRequirement {
            kind: VariantEvidenceKind::Layout,
            variant_ty: binding.variant_ty,
            tag: binding.tag,
            payload_ty: binding.payload_ty,
        }
    }));
    requirements
}

/// Reconstruct effect-variable instantiation while walking corresponding type surfaces.
fn bind_type_effect_instantiation(
    pattern: Type,
    actual: Type,
    subst: &mut EffectsInstSubst,
    active: &mut FxHashSet<(Type, Type)>,
) -> bool {
    if !active.insert((pattern, actual)) {
        return true;
    }
    let pattern_kind = pattern.data().clone();
    let actual_kind = actual.data().clone();
    let matches = match (pattern_kind, actual_kind) {
        (TypeKind::Variable(_), _) => true,
        (TypeKind::Tuple(left), TypeKind::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .into_iter()
                    .zip(right)
                    .all(|(left, right)| bind_type_effect_instantiation(left, right, subst, active))
        }
        (TypeKind::Record(left), TypeKind::Record(right))
        | (TypeKind::Variant(left), TypeKind::Variant(right)) => {
            left.len() == right.len()
                && left
                    .into_iter()
                    .zip(right)
                    .all(|((left_name, left), (right_name, right))| {
                        left_name == right_name
                            && bind_type_effect_instantiation(left, right, subst, active)
                    })
        }
        (TypeKind::Native(left), TypeKind::Native(right)) => {
            left.bare_ty == right.bare_ty
                && left.arguments.len() == right.arguments.len()
                && left
                    .arguments
                    .into_iter()
                    .zip(right.arguments)
                    .all(|(left, right)| bind_type_effect_instantiation(left, right, subst, active))
        }
        (TypeKind::Named(left), TypeKind::Named(right)) => {
            left.def == right.def
                && left.params.len() == right.params.len()
                && left.effect_params.len() == right.effect_params.len()
                && left
                    .params
                    .into_iter()
                    .zip(right.params)
                    .all(|(left, right)| bind_type_effect_instantiation(left, right, subst, active))
                && left
                    .effect_params
                    .iter()
                    .zip(&right.effect_params)
                    .all(|(left, right)| bind_effect_instantiation(left, right, subst))
        }
        (TypeKind::Function(left), TypeKind::Function(right)) => {
            left.args.len() == right.args.len()
                && left.args.iter().zip(&right.args).all(|(left, right)| {
                    bind_type_effect_instantiation(left.ty, right.ty, subst, active)
                })
                && bind_type_effect_instantiation(left.ret, right.ret, subst, active)
                && bind_effect_instantiation(&left.effects, &right.effects, subst)
        }
        (TypeKind::Subscript(left), TypeKind::Subscript(right)) => {
            left.args.len() == right.args.len()
                && left.args.iter().zip(&right.args).all(|(left, right)| {
                    bind_type_effect_instantiation(left.ty, right.ty, subst, active)
                })
                && bind_type_effect_instantiation(left.ret, right.ret, subst, active)
                && match (&left.ref_member, &right.ref_member) {
                    (Some(left), Some(right)) => {
                        bind_effect_instantiation(&left.effects, &right.effects, subst)
                    }
                    (None, None) => true,
                    _ => false,
                }
                && match (&left.mut_member, &right.mut_member) {
                    (Some(left), Some(right)) => {
                        bind_effect_instantiation(&left.effects, &right.effects, subst)
                    }
                    (None, None) => true,
                    _ => false,
                }
        }
        (TypeKind::Never, TypeKind::Never) => true,
        (left, right) => left == right,
    };
    active.remove(&(pattern, actual));
    matches
}

/// Bind one effect-set pattern. A lone unmapped variable absorbs the effects not already accounted
/// for by primitives and previously bound variables. Multiple missing variables are accepted only
/// when their identities are already present on the actual side; otherwise the mapping is not
/// unique.
fn bind_effect_instantiation(
    pattern: &EffType,
    actual: &EffType,
    subst: &mut EffectsInstSubst,
) -> bool {
    let missing = pattern
        .iter()
        .filter_map(|effect| match effect {
            Effect::Variable(var) => Some(var),
            Effect::Primitive(_) => None,
        })
        .filter(|var| !subst.contains_key(var))
        .collect::<Vec<_>>();
    if missing.is_empty() {
        return effect_set_is_contained_in(&pattern.instantiate(subst), actual);
    }
    let mut without_missing = subst.clone();
    for var in &missing {
        without_missing.insert(*var, EffType::empty());
    }
    let known = pattern.instantiate(&without_missing);
    if known.iter().any(|effect| !actual.contains(effect)) {
        return false;
    }
    let residual = actual
        .iter()
        .filter(|effect| !known.contains(*effect))
        .collect::<EffType>();
    if missing.len() > 1 {
        if residual.is_empty() {
            for var in missing {
                subst.insert(var, EffType::empty());
            }
            return true;
        }
        for var in missing {
            if !residual.contains(Effect::Variable(var)) {
                return false;
            }
            subst.insert(var, EffType::single_variable(var));
        }
        return effect_set_is_contained_in(&pattern.instantiate(subst), actual);
    }

    let var = missing[0];
    subst.insert(var, residual);
    effect_set_is_contained_in(&pattern.instantiate(subst), actual)
}

fn effect_set_is_contained_in(required: &EffType, available: &EffType) -> bool {
    required.iter().all(|effect| available.contains(effect))
}

/// Bind the variables in a final callee type to the corresponding call-site types.
///
/// Recursive module calls were inferred from a preliminary scheme, whose positional quantifier
/// order need not match the final generalized scheme. The function surface is nevertheless the
/// authoritative relationship between both schemes. Repeated pairs are accepted coinductively so
/// recursive interned type graphs terminate without assigning identity by case tag.
fn bind_call_type_instantiation(
    pattern: Type,
    actual: Type,
    subst: &mut FxHashMap<TypeVar, Type>,
    correspondence: &mut FxHashMap<Type, Type>,
    active: &mut FxHashSet<(Type, Type)>,
) -> bool {
    let pattern_kind = pattern.data().clone();
    if let TypeKind::Variable(var) = &pattern_kind {
        return match subst.get(var) {
            Some(bound) => *bound == actual,
            None => {
                subst.insert(*var, actual);
                true
            }
        };
    }
    if let Some(bound) = correspondence.get(&pattern) {
        return *bound == actual;
    }
    correspondence.insert(pattern, actual);
    if pattern == actual {
        return true;
    }
    if !active.insert((pattern, actual)) {
        return true;
    }

    let actual_kind = actual.data().clone();
    let matches = match (pattern_kind, actual_kind) {
        (TypeKind::Tuple(left), TypeKind::Tuple(right)) => {
            left.len() == right.len()
                && left.into_iter().zip(right).all(|(left, right)| {
                    bind_call_type_instantiation(left, right, subst, correspondence, active)
                })
        }
        (TypeKind::Record(left), TypeKind::Record(right))
        | (TypeKind::Variant(left), TypeKind::Variant(right)) => {
            left.len() == right.len()
                && left
                    .into_iter()
                    .zip(right)
                    .all(|((left_name, left), (right_name, right))| {
                        left_name == right_name
                            && bind_call_type_instantiation(
                                left,
                                right,
                                subst,
                                correspondence,
                                active,
                            )
                    })
        }
        (TypeKind::Native(left), TypeKind::Native(right)) => {
            left.bare_ty == right.bare_ty
                && left.arguments.len() == right.arguments.len()
                && left
                    .arguments
                    .into_iter()
                    .zip(right.arguments)
                    .all(|(left, right)| {
                        bind_call_type_instantiation(left, right, subst, correspondence, active)
                    })
        }
        (TypeKind::Named(left), TypeKind::Named(right)) => {
            left.def == right.def
                && left.params.len() == right.params.len()
                && left
                    .params
                    .into_iter()
                    .zip(right.params)
                    .all(|(left, right)| {
                        bind_call_type_instantiation(left, right, subst, correspondence, active)
                    })
        }
        (TypeKind::Function(left), TypeKind::Function(right)) => {
            left.args.len() == right.args.len()
                && left.args.iter().zip(&right.args).all(|(left, right)| {
                    bind_call_type_instantiation(left.ty, right.ty, subst, correspondence, active)
                })
                && bind_call_type_instantiation(left.ret, right.ret, subst, correspondence, active)
        }
        (TypeKind::Subscript(left), TypeKind::Subscript(right)) => {
            left.args.len() == right.args.len()
                && left.args.iter().zip(&right.args).all(|(left, right)| {
                    bind_call_type_instantiation(left.ty, right.ty, subst, correspondence, active)
                })
                && bind_call_type_instantiation(left.ret, right.ret, subst, correspondence, active)
        }
        (TypeKind::Never, TypeKind::Never) => true,
        _ => false,
    };
    active.remove(&(pattern, actual));
    matches
}

/// Result of elaborating one unelaborated HIR root into the final HIR arena.
pub struct ElaboratedHir {
    pub root: ENodeId,
    pub remap: FxHashMap<UNodeId, ENodeId>,
    pub locals: Vec<ELocalDecl>,
}

fn node_contains_yield(arena: &UNodeArena, root: UNodeId) -> bool {
    matches!(arena[root].kind, NodeKind::Yield(_))
        || arena[root]
            .kind
            .child_node_ids()
            .into_iter()
            .any(|child| node_contains_yield(arena, child))
}

/// Elaborate a pre-dictionary-passing HIR tree into the final HIR arena.
#[cfg(test)]
fn elaborate_hir<'d, 'sr, 'sm>(
    src: &UNodeArena,
    root: UNodeId,
    dst: &mut ENodeArena,
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
    locals: Vec<LocalDecl>,
) -> Result<ElaboratedHir, InternalCompilationError> {
    let mut warnings = Vec::new();
    elaborate_hir_with_warnings(src, root, dst, ctx, locals, &mut warnings)
}

/// Elaborate HIR while reporting unreachable suffixes that became visible only after final type
/// substitution. Most suffixes are already diagnosed and pruned during inference.
pub(crate) fn elaborate_hir_with_warnings<'d, 'sr, 'sm>(
    src: &UNodeArena,
    root: UNodeId,
    dst: &mut ENodeArena,
    ctx: &mut DictElaborationCtx<'d, 'sr, 'sm>,
    locals: Vec<LocalDecl>,
    warnings: &mut Vec<CompilationWarning>,
) -> Result<ElaboratedHir, InternalCompilationError> {
    let mut elaboration = HirElaboration::new(dst, ctx, locals, warnings);
    let root = elaboration.elaborate_node(src, root)?;
    LocalDecl::assign_sequential_slots(&mut elaboration.locals);
    Ok(ElaboratedHir {
        root,
        remap: elaboration.remap,
        locals: elaboration
            .locals
            .into_iter()
            .map(LocalDecl::into_elaborated)
            .collect(),
    })
}

/// Finalize generated functions returned by trait-solver commits into the final HIR arena.
pub fn elaborate_generated_functions(
    module: &mut Module,
    others: &Modules,
    pending_functions: &mut FxHashMap<LocalFunctionId, PendingModuleFunction>,
    ids: impl IntoIterator<Item = LocalFunctionId>,
) -> Result<(), InternalCompilationError> {
    let mut pending = ids.into_iter().collect::<Vec<_>>();
    let mut index = 0;
    while index < pending.len() {
        let id = pending[index];
        index += 1;
        let Some(mut function) = pending_functions.remove(&id) else {
            continue;
        };
        function.definition = module.functions[id.as_index()].definition.clone();
        function.spans = module.functions[id.as_index()].spans.clone();

        let dicts = module.functions[id.as_index()]
            .definition
            .ty_scheme
            .extra_parameters(ModuleEnv::new(module, others));
        let generated_projection_subscripts =
            crate::module::PendingGeneratedStructuralProjectionSubscripts::new(module);
        let mut solver = trait_solver_from_module!(module, others);
        let mut ctx = DictElaborationCtx::new_with_generated_projection_subscripts(
            &dicts,
            None,
            &mut solver,
            generated_projection_subscripts,
        );
        let elaborated =
            function.check_borrows_and_elaborate_hir(&mut module.hir_arena, &mut ctx)?;
        module.functions[id.as_index()] = elaborated;
        let generated_projection_subscripts = ctx.take_generated_projection_subscripts();
        let generated = solver.commit(
            &mut module.functions,
            &mut module.def_table,
            pending_functions,
        );
        if let Some(generated_projection_subscripts) = generated_projection_subscripts {
            generated_projection_subscripts.commit(module, others);
        }
        pending.extend(generated);
    }
    Ok(())
}

/// Stateful worker that appends elaborated HIR nodes while tracking UNodeId-to-ENodeId remaps.
struct HirElaboration<'a, 'w, 'd, 'sr, 'sm> {
    generated: UNodeArena,
    dst: &'a mut ENodeArena,
    ctx: &'a mut DictElaborationCtx<'d, 'sr, 'sm>,
    locals: Vec<LocalDecl>,
    remap: FxHashMap<UNodeId, ENodeId>,
    in_progress: FxHashSet<UNodeId>,
    warnings: &'w mut Vec<CompilationWarning>,
}

#[derive(Debug, Clone, Copy)]
enum ArgumentLifetimePlan {
    Direct,
    Snapshot {
        clone: ResolvedLocalClone,
        drop: Option<ResolvedLocalDrop>,
    },
    MaterializeOwned {
        drop: ResolvedLocalDrop,
    },
}

struct ElaboratedCallArguments {
    arguments: Vec<CallArgument<Elaborated>>,
    cleanup: Vec<LocalDeclId>,
}

impl<'a, 'w, 'd, 'sr, 'sm> HirElaboration<'a, 'w, 'd, 'sr, 'sm> {
    fn new(
        dst: &'a mut ENodeArena,
        ctx: &'a mut DictElaborationCtx<'d, 'sr, 'sm>,
        locals: Vec<LocalDecl>,
        warnings: &'w mut Vec<CompilationWarning>,
    ) -> Self {
        Self {
            generated: UNodeArena::default(),
            dst,
            ctx,
            locals,
            remap: FxHashMap::default(),
            in_progress: FxHashSet::default(),
            warnings,
        }
    }

    fn push_owned_call_temp(
        &mut self,
        ty: Type,
        drop: ResolvedLocalDrop,
        span: Location,
        name: Ustr,
    ) -> LocalDeclId {
        let mut local = LocalDecl::new(
            (name, Location::new_synthesized()),
            MutType::constant(),
            ty,
            None,
            span,
        );
        local.set_owned_storage(PendingLocalDrop::Resolved(drop));
        LocalDecl::push_with_next_slot(&mut self.locals, local)
    }

    #[allow(clippy::too_many_arguments)]
    fn materialize_call_value(
        &mut self,
        value: ENodeId,
        ty: Type,
        effects: &EffType,
        value_span: Location,
        scope_span: Location,
        name: Ustr,
        drop: ResolvedLocalDrop,
    ) -> (ENodeId, LocalDeclId) {
        let local = self.push_owned_call_temp(ty, drop, scope_span, name);
        let store = self.alloc_elaborated_node(
            NodeKind::StoreLocal(hir::StoreLocal { value, id: local }),
            Type::unit(),
            effects.clone(),
            value_span,
        );
        let load = self.alloc_elaborated_node(
            NodeKind::LoadLocal(hir::LoadLocal { id: local }),
            ty,
            no_effects(),
            value_span,
        );
        let value = self.alloc_elaborated_node(
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![store, load])),
                cleanup: Vec::new(),
            })),
            ty,
            effects.clone(),
            value_span,
        );
        (value, local)
    }

    fn elaborate_node(
        &mut self,
        src: &UNodeArena,
        old: UNodeId,
    ) -> Result<ENodeId, InternalCompilationError> {
        if let Some(&new) = self.remap.get(&old) {
            return Ok(new);
        }
        if !self.in_progress.insert(old) {
            return Err(internal_compilation_error!(Internal {
                error: "cycle found while elaborating HIR".to_string(),
                span: src[old].span,
            }));
        }

        let old_node = &src[old];
        let old_ty = old_node.ty;
        let old_effects = old_node.effects.clone();
        let old_span = old_node.span;
        let kind = self.elaborate_source_kind(src, old, old_ty, &old_effects, old_span)?;
        let new = self
            .dst
            .alloc(Node::<Elaborated>::new(kind, old_ty, old_effects, old_span));
        self.in_progress.remove(&old);
        self.remap.insert(old, new);
        Ok(new)
    }

    fn elaborate_synthetic_node(
        &mut self,
        kind: NodeKind<Unelaborated>,
        ty: Type,
        effects: EffType,
        span: Location,
    ) -> Result<ENodeId, InternalCompilationError> {
        let kind = self.elaborate_synthetic_kind(kind, span)?;
        Ok(self.alloc_elaborated_node(kind, ty, effects, span))
    }

    fn elaborate_synthetic_kind(
        &mut self,
        kind: NodeKind<Unelaborated>,
        span: Location,
    ) -> Result<NodeKind<Elaborated>, InternalCompilationError> {
        use NodeKind::*;
        Ok(match kind {
            Immediate(value) => Immediate(value),
            GetSubscript(get_subscript) => GetSubscript(get_subscript),
            GetDictionary(get_dict) => GetDictionary(get_dict),
            LoadDictionary(load) => LoadDictionary(load),
            LoadSubscriptEvidence(load) => LoadSubscriptEvidence(load),
            LoadVariantPayloadStorageEvidence(load) => LoadVariantPayloadStorageEvidence(load),
            _ => {
                return Err(internal_compilation_error!(Internal {
                    error: "unexpected synthetic HIR node requiring recursive elaboration"
                        .to_string(),
                    span,
                }));
            }
        })
    }

    fn alloc_elaborated_node(
        &mut self,
        kind: NodeKind<Elaborated>,
        ty: Type,
        effects: EffType,
        span: Location,
    ) -> ENodeId {
        self.dst
            .alloc(Node::<Elaborated>::new(kind, ty, effects, span))
    }

    fn projection_evidence_field_access(
        &mut self,
        child: ENodeId,
        field_name: Ustr,
        access_mode: SubscriptMemberKind,
        index: usize,
        node_ty: Type,
        node_span: Location,
    ) -> NodeKind<Elaborated> {
        use NodeKind::*;
        let extra_parameter = ExtraParameterId::from_index(index);
        let DictionaryReq::ProjectionSubscript { subscript_ty, .. } =
            &self.ctx.dicts.requirements[index]
        else {
            panic!("Projection subscript dictionary index should reference projection evidence");
        };
        let member_ty = match access_mode {
            SubscriptMemberKind::Ref => subscript_ty.ref_member.as_ref(),
            SubscriptMemberKind::Mut => subscript_ty.mut_member.as_ref(),
        }
        .unwrap_or_else(|| {
            panic!(
                "Projection evidence for field \"{field_name}\" should contain the selected member"
            )
        });
        let mut inst_fn_args = subscript_ty.args.clone();
        if access_mode.mut_member() {
            inst_fn_args[0].mut_ty = crate::types::mutability::MutType::mutable();
        }
        let subscript = self.alloc_elaborated_node(
            LoadSubscriptEvidence(hir::LoadSubscriptEvidence { extra_parameter }),
            Type::subscript_type(subscript_ty.clone()),
            no_effects(),
            node_span,
        );
        let passing = if access_mode.mut_member() {
            ArgConvention::MutableRef
        } else {
            ArgConvention::Let
        };
        SubscriptApply(b(hir::SubscriptApplication {
            subscript,
            mut_member: access_mode.mut_member(),
            arguments: vec![CallArgument {
                value: child,
                passing,
            }],
            ty: CallImplType::new(
                FnType::new(inst_fn_args, node_ty, member_ty.effects.clone()),
                CallResultConvention::Subscript(member_ty.result_convention),
            ),
        }))
    }

    fn elaborated_node_is_place_reference(&self, node_id: ENodeId) -> bool {
        // Elaborated HIR has no `FieldAccess`, `TraitMethodApply`, or
        // `GetTraitMethod` nodes; keep this phase-specific rather than
        // teaching the unelaborated place helper about elaboration payloads.
        match &self.dst[node_id].kind {
            NodeKind::LoadLocal(_) | NodeKind::Project(_) => true,
            NodeKind::FunctionApply(app) => app.ty.returns_place(),
            NodeKind::SubscriptApply(app) => app.ty.returns_place(),
            NodeKind::StaticApply(app) => app.ty.returns_place(),
            NodeKind::CallDictionaryFunction(call) => call.ty.returns_place(),
            NodeKind::WithPlace(node) => self.elaborated_node_is_place_reference(node.body),
            NodeKind::Block(block) => block
                .tail_node()
                .is_some_and(|node| self.elaborated_node_is_place_reference(node)),
            _ => false,
        }
    }

    fn materialize_elaborated_place_value(
        &mut self,
        source: ENodeId,
        ty: Type,
        span: Location,
    ) -> Result<ENodeId, InternalCompilationError> {
        let effects = self.dst[source].effects.clone();
        let clone = resolve_local_clone(&mut self.generated, self.ctx, ty, span)?;
        Ok(self.alloc_elaborated_node(
            NodeKind::CloneValue(hir::CloneValue { source, clone }),
            ty,
            effects,
            span,
        ))
    }

    fn inline_yielded_binding_body(
        &mut self,
        binding: LocalDeclId,
        place: ENodeId,
        body: ENodeId,
    ) -> Result<Option<NodeKind<Elaborated>>, InternalCompilationError> {
        match &self.dst[body].kind {
            NodeKind::LoadLocal(load) if load.id == binding => {
                Ok(Some(self.dst[place].kind.clone()))
            }
            NodeKind::CloneValue(clone) => match &self.dst[clone.source].kind {
                NodeKind::LoadLocal(load) if load.id == binding => {
                    Ok(Some(NodeKind::CloneValue(hir::CloneValue {
                        source: place,
                        clone: clone.clone,
                    })))
                }
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }

    fn elaborate_node_iter(
        &mut self,
        src: &UNodeArena,
        nodes: impl IntoIterator<Item = UNodeId>,
    ) -> Result<Vec<ENodeId>, InternalCompilationError> {
        let nodes = nodes.into_iter();
        let (lower, _) = nodes.size_hint();
        let mut result = Vec::with_capacity(lower);
        for node in nodes {
            result.push(self.elaborate_node(src, node)?);
        }
        Ok(result)
    }

    fn elaborate_extra_arg_kinds(
        &mut self,
        args: impl IntoIterator<Item = (NodeKind<Unelaborated>, Type, FnArgType)>,
        span: Location,
    ) -> Result<(Vec<ENodeId>, Vec<FnArgType>), InternalCompilationError> {
        let args = args.into_iter();
        let (lower, _) = args.size_hint();
        let mut nodes = Vec::with_capacity(lower);
        let mut arg_tys = Vec::with_capacity(lower);
        for (kind, ty, arg_ty) in args {
            nodes.push(self.elaborate_synthetic_node(kind, ty, no_effects(), span)?);
            arg_tys.push(arg_ty);
        }
        Ok((nodes, arg_tys))
    }

    fn elaborate_extra_args_from_inst_data(
        &mut self,
        inst_data: &hir::FnInstData,
        span: Location,
    ) -> Result<(Vec<ENodeId>, Vec<FnArgType>), InternalCompilationError> {
        let args = extra_arg_kind_from_inst_data(inst_data, span, self.ctx, &mut self.generated)?;
        self.elaborate_extra_arg_kinds(args, span)
    }

    fn elaborate_call_arguments(
        &mut self,
        src: &UNodeArena,
        arguments: &[CallArgument],
        returns_caller_rooted_place: bool,
        node_span: Location,
    ) -> Result<ElaboratedCallArguments, InternalCompilationError> {
        let mut snapshot = vec![false; arguments.len()];
        let caller_rooted_base = returns_caller_rooted_place.then(|| {
            hir::addressor_place_base_argument_index(src, arguments)
                .expect("addressor-place application should have a base argument")
        });

        for (let_index, mutable_index) in
            hir::borrow_checker::let_arguments_overlapping_mutable(src, arguments)
        {
            if caller_rooted_base == Some(let_index) {
                return Err(internal_compilation_error!(MutablePathsOverlap {
                    a_span: src[arguments[let_index].value].span,
                    b_span: src[arguments[mutable_index].value].span,
                    fn_span: node_span,
                }));
            }
            snapshot[let_index] = true;
        }

        for (let_index, _) in
            hir::borrow_checker::let_arguments_overlapping_later_argument_writes(src, arguments)
        {
            if caller_rooted_base != Some(let_index) {
                snapshot[let_index] = true;
            }
        }

        // Resolve the complete plan before rewriting an argument. This keeps conflict
        // classification independent of elaboration traversal and allocation order.
        let mut plans = Vec::with_capacity(arguments.len());
        for (index, argument) in arguments.iter().enumerate() {
            let source = argument.value;
            let ty = src[source].ty;
            let plan = if ty == Type::never() {
                // Evaluating a `never` argument transfers control before the call. It therefore
                // needs neither a snapshot nor an owned call lifetime, even if conservative path
                // analysis happened to classify its place as overlapping.
                ArgumentLifetimePlan::Direct
            } else if snapshot[index] {
                let clone = resolve_local_clone(&mut self.generated, self.ctx, ty, node_span)?;
                let drop = if matches!(clone, ResolvedLocalClone::TrivialCopy) {
                    None
                } else {
                    Some(
                        resolve_local_drop(&mut self.generated, self.ctx, ty, node_span)?
                            .into_elaborated(),
                    )
                };
                ArgumentLifetimePlan::Snapshot { clone, drop }
            } else if argument.passing == ArgConvention::Let
                && (!hir::node_is_place_reference(src, source)
                    // A generic trait method is place-like only while type inference represents
                    // dictionary dispatch. Elaboration produces a fresh function value, so its
                    // owned environment needs the same explicit call lifetime as any rvalue.
                    || matches!(src[source].kind, NodeKind::GetTraitMethod(_)))
            {
                let drop = resolve_local_drop(&mut self.generated, self.ctx, ty, node_span)?
                    .into_elaborated();
                if drop == ResolvedLocalDrop::Skip {
                    ArgumentLifetimePlan::Direct
                } else {
                    ArgumentLifetimePlan::MaterializeOwned { drop }
                }
            } else {
                ArgumentLifetimePlan::Direct
            };
            plans.push(plan);
        }

        let mut result = Vec::with_capacity(arguments.len());
        let mut cleanup = Vec::new();
        for (argument, plan) in arguments.iter().zip(plans) {
            let source = argument.value;
            let source_node = &src[source];
            let mut value = self.elaborate_node(src, source)?;
            let drop = match plan {
                ArgumentLifetimePlan::Direct => None,
                ArgumentLifetimePlan::Snapshot { clone, drop } => {
                    value = self.alloc_elaborated_node(
                        NodeKind::CloneValue(hir::CloneValue {
                            source: value,
                            clone,
                        }),
                        source_node.ty,
                        source_node.effects.clone(),
                        source_node.span,
                    );
                    drop
                }
                ArgumentLifetimePlan::MaterializeOwned { drop } => Some(drop),
            };

            if let Some(drop) = drop {
                let (materialized, local) = self.materialize_call_value(
                    value,
                    source_node.ty,
                    &source_node.effects,
                    source_node.span,
                    node_span,
                    if matches!(plan, ArgumentLifetimePlan::Snapshot { .. }) {
                        ustr("$snapshot")
                    } else {
                        ustr("$arg")
                    },
                    drop,
                );
                value = materialized;
                cleanup.push(local);
            }

            result.push(CallArgument {
                value,
                passing: argument.passing,
            });
        }
        Ok(ElaboratedCallArguments {
            arguments: result,
            cleanup,
        })
    }

    fn wrap_call_cleanup(
        &mut self,
        call: NodeKind<Elaborated>,
        cleanup: Vec<LocalDeclId>,
        ty: Type,
        effects: &EffType,
        span: Location,
    ) -> NodeKind<Elaborated> {
        if cleanup.is_empty() {
            return call;
        }
        let call = self.alloc_elaborated_node(call, ty, effects.clone(), span);
        NodeKind::Block(b(hir::Block {
            body: b(SVec2::from_vec(vec![call])),
            cleanup,
        }))
    }

    fn elaborate_source_kind(
        &mut self,
        src: &UNodeArena,
        old: UNodeId,
        node_ty: Type,
        node_effects: &EffType,
        node_span: Location,
    ) -> Result<NodeKind<Elaborated>, InternalCompilationError> {
        use NodeKind::*;

        Ok(match &src[old].kind {
            Immediate(value) => Immediate(value.clone()),
            Uninit => Uninit,
            BuildClosure(build_closure) => {
                let captures_value_dictionary = build_closure.captures_value_dictionary;
                let function = build_closure.function;
                let mut dictionary_captures = self
                    .elaborate_node_iter(src, build_closure.dictionary_captures.iter().copied())?;
                let mut captures =
                    self.elaborate_node_iter(src, build_closure.captures.iter().copied())?;
                let mut captures_value_dictionary = captures_value_dictionary
                    .map(|node| self.elaborate_node(src, node))
                    .transpose()?;
                let function = self.elaborate_node(src, function)?;

                let function = if let BuildClosure(inner) = &self.dst[function].kind {
                    dictionary_captures.splice(0..0, inner.dictionary_captures.iter().copied());
                    if !inner.captures.is_empty() && !captures.is_empty() {
                        panic!("Cannot flatten closures with two owned capture environments yet");
                    }
                    if captures.is_empty() {
                        captures = inner.captures.clone();
                        captures_value_dictionary = inner.captures_value_dictionary;
                    }
                    inner.function
                } else {
                    function
                };

                BuildClosure(b(hir::BuildClosure {
                    function,
                    dictionary_captures,
                    captures,
                    captures_value_dictionary,
                }))
            }
            BuildSubscriptValue(build) => {
                let mut evidence_captures =
                    self.elaborate_node_iter(src, build.evidence_captures.iter().copied())?;
                let subscript = self.elaborate_node(src, build.subscript)?;

                let subscript = if let BuildSubscriptValue(inner) = &self.dst[subscript].kind {
                    evidence_captures.splice(0..0, inner.evidence_captures.iter().copied());
                    inner.subscript
                } else {
                    subscript
                };

                BuildSubscriptValue(b(hir::BuildSubscriptValue {
                    subscript,
                    evidence_captures,
                }))
            }
            FunctionApply(app) => {
                let function_source = app.function;
                let ty = app.ty.clone();
                let snapshot_function = hir::borrow_checker::callee_overlaps_argument_writes(
                    src,
                    function_source,
                    &app.arguments,
                );

                // The function expression is evaluated before every argument. Preserve that
                // observation when a later argument may modify the same storage by cloning the
                // function value into an owned call temporary at its source position. Allocate
                // this temporary before argument temporaries so reverse cleanup order remains
                // argument(s), then function.
                let function_node = &src[function_source];
                let mut function = self.elaborate_node(src, function_source)?;
                let mut cleanup = Vec::new();
                if snapshot_function {
                    let clone = resolve_local_clone(
                        &mut self.generated,
                        self.ctx,
                        function_node.ty,
                        node_span,
                    )?;
                    let drop = resolve_local_drop(
                        &mut self.generated,
                        self.ctx,
                        function_node.ty,
                        node_span,
                    )?
                    .into_elaborated();
                    function = self.alloc_elaborated_node(
                        NodeKind::CloneValue(hir::CloneValue {
                            source: function,
                            clone,
                        }),
                        function_node.ty,
                        function_node.effects.clone(),
                        function_node.span,
                    );
                    let (materialized, local) = self.materialize_call_value(
                        function,
                        function_node.ty,
                        &function_node.effects,
                        function_node.span,
                        node_span,
                        ustr("$function_snapshot"),
                        drop,
                    );
                    function = materialized;
                    cleanup.push(local);
                }
                let arguments = self.elaborate_call_arguments(
                    src,
                    &app.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                cleanup.extend(arguments.cleanup);
                let call = FunctionApply(b(hir::FunctionApplication {
                    function,
                    arguments: arguments.arguments,
                    ty,
                }));
                self.wrap_call_cleanup(call, cleanup, node_ty, node_effects, node_span)
            }
            CloneClosureEnv(node) => {
                let source = node.source;
                CloneClosureEnv(hir::CloneClosureEnv {
                    source: self.elaborate_node(src, source)?,
                })
            }
            DropClosureEnv(node) => {
                let target = node.target;
                DropClosureEnv(hir::DropClosureEnv {
                    target: self.elaborate_node(src, target)?,
                })
            }
            CloneSubscriptValue(node) => {
                let source = node.source;
                CloneSubscriptValue(hir::CloneSubscriptValue {
                    source: self.elaborate_node(src, source)?,
                })
            }
            DropSubscriptValue(node) => {
                let target = node.target;
                DropSubscriptValue(hir::DropSubscriptValue {
                    target: self.elaborate_node(src, target)?,
                })
            }
            CloneValue(node) => {
                let source = node.source;
                let mut clone = node.clone;
                if matches!(clone, PendingLocalClone::Unknown) {
                    clone = PendingLocalClone::Resolved(resolve_local_clone(
                        &mut self.generated,
                        self.ctx,
                        node_ty,
                        node_span,
                    )?);
                }
                CloneValue(hir::CloneValue {
                    source: self.elaborate_node(src, source)?,
                    clone: clone.into_elaborated(),
                })
            }
            StaticApply(app) => {
                let function = app.function;
                let function_path = app.function_path.clone();
                let function_span = app.function_span;
                let argument_names = app.argument_names.clone();
                let argument_name_hint_policy = app.argument_name_hint_policy;
                let ty = app.ty.clone();
                let inst_data = app.inst_data.clone();
                let source_extra_arguments = app.extra_arguments.iter().copied();
                let mut extra_arguments = if !inst_data.dicts_req.is_empty() {
                    self.elaborate_extra_args_from_inst_data(&inst_data, function_span)?
                        .0
                } else if function.module == self.ctx.trait_solver.current_type_items.module.id
                    && let Some(requirements) = self
                        .ctx
                        .module_inst_data
                        .and_then(|inst_data| inst_data.get(&function.function))
                {
                    let late_inst_data = late_module_call_inst_data(
                        requirements,
                        &ty.fn_ty,
                        &inst_data,
                        self.ctx.dicts,
                        node_span,
                    )?;
                    self.elaborate_extra_args_from_inst_data(&late_inst_data, node_span)?
                        .0
                } else {
                    Vec::new()
                };
                let source_extra_arguments =
                    self.elaborate_node_iter(src, source_extra_arguments)?;
                extra_arguments.extend(source_extra_arguments);
                let arguments = self.elaborate_call_arguments(
                    src,
                    &app.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = StaticApply(b(StaticApplication {
                    function,
                    function_path,
                    function_span,
                    extra_arguments,
                    arguments: arguments.arguments,
                    argument_names,
                    argument_name_hint_policy,
                    ty,
                    inst_data,
                }));
                self.wrap_call_cleanup(call, arguments.cleanup, node_ty, node_effects, node_span)
            }
            SubscriptApply(app) => {
                let subscript = app.subscript;
                let mut_member = app.mut_member;
                let ty = app.ty.clone();
                let arguments = self.elaborate_call_arguments(
                    src,
                    &app.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = SubscriptApply(b(hir::SubscriptApplication {
                    subscript: self.elaborate_node(src, subscript)?,
                    mut_member,
                    arguments: arguments.arguments,
                    ty,
                }));
                self.wrap_call_cleanup(call, arguments.cleanup, node_ty, node_effects, node_span)
            }
            TraitMethodApply(app) => {
                let trait_id = app.trait_id;
                let method_index = app.method_index;
                let method_path = app.method_path.clone();
                let method_span = app.method_span;
                let arguments_unnamed = app.arguments_unnamed;
                let ty = app.ty.clone();
                let input_tys = app.input_tys.clone();
                let inst_data = app.inst_data.clone();
                assert!(
                    inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait method is not supported yet."
                );
                let resolved = input_tys.iter().all(|ty| ty.is_trait_input_resolved());
                let (is_value_function, is_function_surface_only, argument_names) = {
                    let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                    let definition = &trait_def.method(method_index).1;
                    (
                        is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &[]),
                        is_function_surface_only_value_trait_application(
                            trait_id,
                            trait_def,
                            &input_tys,
                            &[],
                        ),
                        definition.arg_names.clone(),
                    )
                };
                let arguments = self.elaborate_call_arguments(
                    src,
                    &app.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = if is_value_function || resolved {
                    let function = if is_value_function {
                        FunctionId::new(
                            self.ctx.trait_solver.current_type_items.module.id,
                            function_value_method(
                                self.ctx.trait_solver,
                                method_index,
                                method_span,
                            )?,
                        )
                    } else {
                        self.ctx.trait_solver.solve_impl_method(
                            trait_id,
                            &input_tys,
                            method_index,
                            method_span,
                            &mut self.generated,
                        )?
                    };
                    StaticApply(b(hir::StaticApplication {
                        function,
                        function_path: Some(method_path),
                        function_span: method_span,
                        extra_arguments: Vec::new(),
                        arguments: arguments.arguments,
                        argument_names,
                        argument_name_hint_policy: arguments_unnamed,
                        ty,
                        inst_data: hir::FnInstData::none(),
                    }))
                } else if is_function_surface_only {
                    let (dict_ty, entry_index) = {
                        let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                        let dict_ty = trait_def.get_dictionary_type_for_tys(&input_tys, &[], &[]);
                        let (entry_index, _) =
                            dictionary_method_projection_data(trait_def, dict_ty, method_index);
                        (dict_ty, entry_index)
                    };
                    let (dict_kind, _) = trait_dictionary_node_kind(
                        &mut self.generated,
                        trait_id,
                        &input_tys,
                        &[],
                        &[],
                        method_span,
                        self.ctx,
                    )?;
                    let dictionary = self.elaborate_synthetic_node(
                        dict_kind,
                        dict_ty,
                        no_effects(),
                        method_span,
                    )?;
                    call_dictionary_function(dictionary, entry_index, arguments.arguments, ty)
                } else {
                    let dict_index = find_trait_impl_dict_index(
                        self.ctx.dicts,
                        trait_id,
                        &input_tys,
                    )
                    .expect(
                        "Dictionary for trait impl not found, type inference should have failed",
                    );
                    let dict_ty =
                        self.ctx.dicts.requirements[dict_index].to_dict_type(self.ctx.trait_solver);
                    let dictionary = self.elaborate_synthetic_node(
                        NodeKind::LoadDictionary(hir::LoadDictionary {
                            extra_parameter: ExtraParameterId::from_index(dict_index),
                        }),
                        dict_ty,
                        no_effects(),
                        method_span,
                    )?;
                    let (entry_index, _) = dictionary_method_projection_data(
                        self.ctx.trait_solver.trait_def(trait_id),
                        dict_ty,
                        method_index,
                    );
                    call_dictionary_function(dictionary, entry_index, arguments.arguments, ty)
                };
                self.wrap_call_cleanup(call, arguments.cleanup, node_ty, node_effects, node_span)
            }
            GetFunction(get_fn) => {
                let mut get_fn = (**get_fn).clone();
                let captures = if !get_fn.inst_data.dicts_req.is_empty() {
                    let (captures, _) =
                        self.elaborate_extra_args_from_inst_data(&get_fn.inst_data, node_span)?;
                    get_fn.inst_data.dicts_req.clear();
                    captures
                } else if get_fn.function.module
                    == self.ctx.trait_solver.current_type_items.module.id
                {
                    if let Some(requirements) = self
                        .ctx
                        .module_inst_data
                        .and_then(|inst_data| inst_data.get(&get_fn.function.function))
                        .filter(|inst_data| !inst_data.requirements.is_empty())
                    {
                        let TypeKind::Function(call_ty) = node_ty.data().clone() else {
                            panic!("get_function must have a function type")
                        };
                        let late_inst_data = late_module_call_inst_data(
                            requirements,
                            &call_ty,
                            &get_fn.inst_data,
                            self.ctx.dicts,
                            node_span,
                        )?;
                        self.elaborate_extra_args_from_inst_data(&late_inst_data, node_span)?
                            .0
                    } else {
                        Vec::new()
                    }
                } else {
                    Vec::new()
                };
                if captures.is_empty() {
                    GetFunction(b(get_fn))
                } else {
                    let function = self.alloc_elaborated_node(
                        GetFunction(b(get_fn)),
                        node_ty,
                        node_effects.clone(),
                        node_span,
                    );
                    BuildClosure(b(hir::BuildClosure {
                        function,
                        dictionary_captures: captures,
                        captures: Vec::new(),
                        captures_value_dictionary: None,
                    }))
                }
            }
            GetSubscript(get_subscript) => {
                let mut get_subscript = (**get_subscript).clone();
                let captures = if !get_subscript.inst_data.dicts_req.is_empty() {
                    let (captures, _) = self
                        .elaborate_extra_args_from_inst_data(&get_subscript.inst_data, node_span)?;
                    get_subscript.inst_data.dicts_req.clear();
                    captures
                } else {
                    Vec::new()
                };
                if captures.is_empty() {
                    GetSubscript(b(get_subscript))
                } else {
                    let subscript = self.alloc_elaborated_node(
                        GetSubscript(b(get_subscript)),
                        node_ty,
                        node_effects.clone(),
                        node_span,
                    );
                    BuildSubscriptValue(b(hir::BuildSubscriptValue {
                        subscript,
                        evidence_captures: captures,
                    }))
                }
            }
            GetTraitMethod(get_method) => {
                let trait_id = get_method.trait_id;
                let method_index = get_method.method_index;
                let method_path = get_method.method_path.clone();
                let method_span = get_method.method_span;
                assert!(
                    get_method.inst_data.dicts_req.is_empty(),
                    "Instantiation data for trait method is not supported yet."
                );
                let input_tys = get_method.input_tys.clone();
                let output_tys = get_method.output_tys.clone();
                let output_effs = get_method.output_effs.clone();
                let resolved = input_tys.iter().all(|ty| ty.is_trait_input_resolved());
                let is_value_function = {
                    let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                    is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &output_tys)
                };
                if is_value_function || resolved {
                    let function = if is_value_function {
                        FunctionId::new(
                            self.ctx.trait_solver.current_type_items.module.id,
                            function_value_method(
                                self.ctx.trait_solver,
                                method_index,
                                method_span,
                            )?,
                        )
                    } else {
                        self.ctx.trait_solver.solve_impl_method(
                            trait_id,
                            &input_tys,
                            method_index,
                            method_span,
                            &mut self.generated,
                        )?
                    };
                    GetFunction(b(hir::GetFunction {
                        function,
                        function_path: method_path,
                        function_span: method_span,
                        inst_data: hir::FnInstData::none(),
                    }))
                } else {
                    let (dict_ty, entry_index) = {
                        let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                        let dict_ty = trait_def.get_dictionary_type_for_tys(
                            &input_tys,
                            &output_tys,
                            &output_effs,
                        );
                        let (entry_index, _) =
                            dictionary_method_projection_data(trait_def, dict_ty, method_index);
                        (dict_ty, entry_index)
                    };
                    let (dict_kind, _) = trait_dictionary_node_kind(
                        &mut self.generated,
                        trait_id,
                        &input_tys,
                        &output_tys,
                        &output_effs,
                        method_span,
                        self.ctx,
                    )?;
                    let dictionary = self.elaborate_synthetic_node(
                        dict_kind,
                        dict_ty,
                        no_effects(),
                        method_span,
                    )?;
                    GetDictionaryFunction(hir::GetDictionaryFunction {
                        dictionary,
                        entry_index,
                    })
                }
            }
            GetTraitAssociatedConst(get_const) => {
                let trait_id = get_const.trait_id;
                let associated_const_index = get_const.associated_const_index;
                let associated_const_span = get_const.associated_const_span;
                let input_tys = get_const.input_tys.clone();
                let output_tys = get_const.output_tys.clone();
                let resolved = input_tys.iter().all(|ty| ty.is_trait_input_resolved());
                let is_compiler_value_application = {
                    let trait_def = self.ctx.trait_solver.trait_def(trait_id);
                    is_value_trait_for_function_type(trait_id, trait_def, &input_tys, &output_tys)
                        || is_function_surface_only_value_trait_application(
                            trait_id,
                            trait_def,
                            &input_tys,
                            &output_tys,
                        )
                };
                if is_compiler_value_application {
                    let values = value_layout_associated_const_values(
                        input_tys[0],
                        node_span,
                        self.ctx.trait_solver,
                    )?;
                    Immediate(LiteralValue::new_native(
                        values[usize::from(associated_const_index)],
                    ))
                } else if resolved {
                    let function = self.ctx.trait_solver.solve_associated_const_getter(
                        trait_id,
                        &input_tys,
                        associated_const_index,
                        associated_const_span,
                        &mut self.generated,
                    )?;
                    static_apply(
                        function,
                        FnType::new_by_val([], node_ty, no_effects()),
                        Vec::new(),
                        associated_const_span,
                    )
                } else {
                    let dict_index = find_trait_impl_dict_index(
                        self.ctx.dicts,
                        trait_id,
                        &input_tys,
                    )
                    .expect(
                        "Dictionary for trait impl not found, type inference should have failed",
                    );
                    let dict_ty =
                        self.ctx.dicts.requirements[dict_index].to_dict_type(self.ctx.trait_solver);
                    let dictionary = self.elaborate_synthetic_node(
                        NodeKind::LoadDictionary(hir::LoadDictionary {
                            extra_parameter: ExtraParameterId::from_index(dict_index),
                        }),
                        dict_ty,
                        no_effects(),
                        associated_const_span,
                    )?;
                    call_dictionary_function(
                        dictionary,
                        self.ctx
                            .trait_solver
                            .trait_def(trait_id)
                            .dictionary_associated_const_index(associated_const_index),
                        Vec::new(),
                        CallImplType::value(FnType::new_by_val([], node_ty, no_effects())),
                    )
                }
            }
            GetTraitDictionary(get_dict) => {
                let input_tys = get_dict.input_tys.clone();
                let output_tys = get_dict.output_tys.clone();
                let output_effs = get_dict.output_effs.clone();
                let (node_kind, _) = trait_dictionary_node_kind(
                    &mut self.generated,
                    get_dict.trait_id,
                    &input_tys,
                    &output_tys,
                    &output_effs,
                    node_span,
                    self.ctx,
                )?;
                self.elaborate_synthetic_kind(node_kind, node_span)?
            }
            GetDictionary(get_dict) => GetDictionary(*get_dict),
            LoadDictionary(load) => LoadDictionary(*load),
            LoadSubscriptEvidence(load) => LoadSubscriptEvidence(*load),
            LoadVariantPayloadStorageEvidence(load) => LoadVariantPayloadStorageEvidence(*load),
            StoreLocal(store) => {
                let value = store.value;
                let id = store.id;
                StoreLocal(hir::StoreLocal {
                    value: self.elaborate_node(src, value)?,
                    id,
                })
            }
            TakeLocalValue(node) => {
                let id = node.id;
                let mut mode = node.mode;
                if matches!(mode, PendingTakeLocalValueMode::Unknown) {
                    mode = if self.locals[id.as_index()].owns_storage() {
                        PendingTakeLocalValueMode::MoveOwned
                    } else {
                        PendingTakeLocalValueMode::CloneBorrowed(resolve_local_clone(
                            &mut self.generated,
                            self.ctx,
                            node_ty,
                            node_span,
                        )?)
                    };
                }
                TakeLocalValue(hir::TakeLocalValue {
                    id,
                    mode: mode.into_elaborated(),
                })
            }
            LoadLocal(load) => LoadLocal(*load),
            GetDictionaryFunction(node) => {
                let dictionary = node.dictionary;
                let entry_index = node.entry_index;
                GetDictionaryFunction(hir::GetDictionaryFunction {
                    dictionary: self.elaborate_node(src, dictionary)?,
                    entry_index,
                })
            }
            CallDictionaryFunction(call) => {
                let dictionary = call.dictionary;
                let entry_index = call.entry_index;
                let ty = call.ty.clone();
                let arguments = self.elaborate_call_arguments(
                    src,
                    &call.arguments,
                    ty.returns_place(),
                    node_span,
                )?;
                let call = CallDictionaryFunction(b(hir::CallDictionaryFunction {
                    dictionary: self.elaborate_node(src, dictionary)?,
                    entry_index,
                    arguments: arguments.arguments,
                    ty,
                }));
                self.wrap_call_cleanup(call, arguments.cleanup, node_ty, node_effects, node_span)
            }
            Return(node) => Return(self.elaborate_node(src, *node)?),
            Block(block) => {
                let cleanup = block.cleanup.clone();
                let mut body = Vec::with_capacity(block.body.len());
                for (index, node) in block.body.iter().copied().enumerate() {
                    body.push(self.elaborate_node(src, node)?);
                    if src[node].ty == Type::never()
                        && !node_contains_yield(src, node)
                        && let Some(location) = Location::fuse(
                            block
                                .body
                                .iter()
                                .skip(index + 1)
                                .map(|node| src[*node].span)
                                .filter(|location| !location.is_synthesized()),
                        )
                    {
                        self.warnings
                            .push(CompilationWarning::unreachable_code(location));
                        break;
                    }
                }
                Block(b(hir::Block {
                    body: b(SVec2::from_vec(body)),
                    cleanup,
                }))
            }
            Assign(assignment) => {
                let place = assignment.place;
                let value = assignment.value;
                let mut drop = assignment.drop;
                let place_ty = src[place].ty;
                if let Some(drop) = &mut drop
                    && matches!(drop, PendingLocalDrop::Unknown)
                {
                    *drop = resolve_local_drop(&mut self.generated, self.ctx, place_ty, node_span)?;
                }
                Assign(hir::Assignment {
                    place: self.elaborate_node(src, place)?,
                    value: self.elaborate_node(src, value)?,
                    drop: drop.map(|drop| drop.into_elaborated()),
                })
            }
            Tuple(nodes) => Tuple(b(SVec2::from_vec(
                self.elaborate_node_iter(src, nodes.iter().copied())?,
            ))),
            Project(project) => {
                let value = project.value;
                let index = project.index;
                if project.variant_payload
                    && !type_has_static_layout(node_ty, node_span, self.ctx.trait_solver)
                {
                    let variant_ty = src[value].ty;
                    // A projection carries no semantic case tag. That is sufficient here because
                    // cases with the same payload type use the same Value<B> layout dictionary;
                    // construction, which must encode the selected tag, performs the exact lookup.
                    let has_case_layout =
                        self.ctx
                            .dicts
                            .variant_payload_layouts
                            .iter()
                            .any(|binding| {
                                binding.variant_ty == variant_ty && binding.payload_ty == node_ty
                            });
                    if !has_case_layout {
                        return Err(internal_compilation_error!(Internal {
                            error: format!(
                                "dynamic variant payload projection from {variant_ty:?} to {node_ty:?} has no case-qualified layout binding"
                            ),
                            span: node_span,
                        }));
                    }
                }
                Project(hir::Project {
                    value: self.elaborate_node(src, value)?,
                    index,
                    variant_payload: project.variant_payload,
                })
            }
            Record(nodes) => Record(b(SVec2::from_vec(
                self.elaborate_node_iter(src, nodes.iter().copied())?,
            ))),
            FieldAccess(field_access) => {
                use TypeKind::*;
                let child_id = field_access.value;
                let field_name = field_access.field;
                let child = self.elaborate_node(src, child_id)?;
                let child_ty = src[child_id].ty;
                let ty_data = child_ty.data();
                let ty_data = if let Some(named) = ty_data.as_named() {
                    let named = named.clone();
                    drop(ty_data);
                    self.ctx
                        .trait_solver
                        .type_def(named.def)
                        .instantiated_shape_with_effects(&named.params, &named.effect_params)
                        .data()
                } else {
                    ty_data
                };
                match &*ty_data {
                    Record(record) => {
                        if let Some(index) = record.iter().position(|field| field.0 == field_name) {
                            Project(HirProject::new(child, ProjectionIndex::from_index(index)))
                        } else if let Some(index) =
                            find_projection_subscript_dict_index_for_receiver_ty(
                                self.ctx.dicts,
                                child_ty,
                                &field_name,
                            )
                        {
                            self.projection_evidence_field_access(
                                child,
                                field_name,
                                field_access.access_mode,
                                index,
                                node_ty,
                                node_span,
                            )
                        } else {
                            panic!("Field not found in type, type inference should have failed");
                        }
                    }
                    Variable(var) => {
                        let var = *var;
                        drop(ty_data);
                        let access_mode = field_access.access_mode;
                        let index = find_projection_subscript_dict_index(
                            self.ctx.dicts,
                            var,
                            &field_name,
                        )
                            .unwrap_or_else(
                                || panic!("Projection subscript dictionary for field \"{field_name}\" in type variable \"{var}\" not found, type inference should have failed"),
                            );
                        self.projection_evidence_field_access(
                            child,
                            field_name,
                            access_mode,
                            index,
                            node_ty,
                            node_span,
                        )
                    }
                    _ => {
                        panic!("FieldAccess should have a record or variable type");
                    }
                }
            }
            Variant(variant) => {
                let payload_ty = src[variant.payload].ty;
                if !type_has_static_layout(payload_ty, node_span, self.ctx.trait_solver) {
                    let index = find_variant_payload_layout_index(
                        self.ctx.dicts,
                        node_ty,
                        variant.tag,
                        payload_ty,
                    )
                    .ok_or_else(|| {
                        internal_compilation_error!(Internal {
                            error: format!(
                                "dynamic payload layout evidence for type {node_ty:?} and case .{}({payload_ty:?}) not found for generic construction",
                                variant.tag
                            ),
                            span: node_span,
                        })
                    })?;
                    let value_trait_id = self
                        .ctx
                        .trait_solver
                        .std_trait_id(crate::std::core_traits_names::VALUE_TRAIT_NAME);
                    debug_assert!(matches!(
                        &self.ctx.dicts.requirements[index],
                        DictionaryReq::TraitImpl { trait_id, input_tys, .. }
                            if *trait_id == value_trait_id && input_tys.as_slice() == [payload_ty]
                    ));
                }
                let payload_storage = if matches!(&*node_ty.data(), TypeKind::Variable(_)) {
                    let index = find_variant_payload_indirection_index(
                        self.ctx.dicts,
                        node_ty,
                        variant.tag,
                    )
                    .ok_or_else(|| {
                        internal_compilation_error!(Internal {
                            error: format!(
                                "variant payload-indirection evidence for type {node_ty:?} and case .{} not found for generic construction",
                                variant.tag
                            ),
                            span: node_span,
                        })
                    })?;
                    VariantPayloadStorageSource::Evidence(ExtraParameterId::from_index(index))
                } else {
                    VariantPayloadStorageSource::Static(variant_payload_storage_for_type(
                        node_ty,
                        variant.tag,
                        node_span,
                        self.ctx.trait_solver,
                    )?)
                };
                Variant(hir::Variant {
                    tag: variant.tag,
                    payload: self.elaborate_node(src, variant.payload)?,
                    payload_storage: Some(payload_storage),
                })
            }
            Array(nodes) => Array(b(SVec2::from_vec(
                self.elaborate_node_iter(src, nodes.iter().copied())?,
            ))),
            Case(case) => {
                let value = case.value;
                let default = case.default;
                let mut alternatives = Vec::with_capacity(case.alternatives.len());
                for (literal, node) in &case.alternatives {
                    alternatives.push((literal.clone(), self.elaborate_node(src, *node)?));
                }
                Case(b(hir::Case {
                    value: self.elaborate_node(src, value)?,
                    alternatives,
                    default: self.elaborate_node(src, default)?,
                }))
            }
            Loop(node) => Loop(hir::Loop {
                label: node.label,
                body: self.elaborate_node(src, node.body)?,
            }),
            Break(node) => Break(hir::Break {
                label: node.label,
                value: self.elaborate_node(src, node.value)?,
            }),
            Continue(node) => Continue(hir::Continue { label: node.label }),
            Yield(node) => Yield(self.elaborate_node(src, *node)?),
            WithYielded(node) => {
                let accessor = self.elaborate_node(src, node.accessor)?;
                let body = self.elaborate_node(src, node.body)?;
                // A generic yielded projection may resolve to a concrete direct
                // projection or addressor-place call. In either case the
                // elaborated accessor already produces a place and needs no
                // suspended yielded-accessor protocol.
                if self.elaborated_node_is_place_reference(accessor) {
                    if let Some(inlined) =
                        self.inline_yielded_binding_body(node.binding, accessor, body)?
                    {
                        inlined
                    } else {
                        WithPlace(hir::WithPlace {
                            place: accessor,
                            binding: node.binding,
                            body,
                        })
                    }
                } else {
                    let mut body = body;
                    if self.elaborated_node_is_place_reference(body) {
                        body = self.materialize_elaborated_place_value(body, node_ty, node_span)?;
                    }
                    WithYielded(hir::WithYielded {
                        accessor,
                        binding: node.binding,
                        body,
                    })
                }
            }
            WithPlace(node) => WithPlace(hir::WithPlace {
                place: self.elaborate_node(src, node.place)?,
                binding: node.binding,
                body: self.elaborate_node(src, node.body)?,
            }),
            CheckCallDepth => CheckCallDepth,
            CheckFuel => CheckFuel,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        FxHashMap, Location, Modules,
        containers::b,
        hir::function::Function,
        hir::{GetTraitAssociatedConst, value::LiteralValue},
        module::{
            CurrentTypeItems, FunctionCollector, LocalDecl, LocalTraitId, Module, ModuleId, Path,
            PendingFunctionCollector, PendingGeneratedStructuralProjectionSubscripts,
            QualifiedNameEnv, TraitId, TraitImpls, id::Id,
        },
        std::math::int_type,
        types::{
            effects::{EffectVar, PrimitiveEffect},
            r#trait::{Trait, TraitAssociatedConst, TraitAssociatedConstIndex},
            trait_solver::{CurrentProjectionSubscriptTypes, TraitSolver},
            r#type::Type,
        },
    };

    fn extra_parameters(requirements: Vec<DictionaryReq>) -> ExtraParameters {
        ExtraParameters {
            requirements,
            variant_payload_layouts: Vec::new(),
            repr_map: FxHashMap::default(),
        }
    }

    #[test]
    fn late_variant_storage_mapping_uses_the_unique_global_assignment() {
        let callee_variant = TypeVar::new(0);
        let callee_payload = TypeVar::new(1);
        let matching_variant = TypeVar::new(2);
        let matching_payload = TypeVar::new(3);
        let decoy_variant = TypeVar::new(4);
        let decoy_payload = TypeVar::new(5);
        let callee_requirements = extra_parameters(vec![
            DictionaryReq::new_variant_payload_indirection(
                Type::variable(callee_variant),
                ustr("Shared"),
                Type::variable(callee_payload),
            ),
            DictionaryReq::new_variant_payload_indirection(
                Type::variable(callee_payload),
                ustr("Marker"),
                int_type(),
            ),
        ]);
        let caller = extra_parameters(vec![
            DictionaryReq::new_variant_payload_indirection(
                Type::variable(matching_variant),
                ustr("Shared"),
                Type::variable(matching_payload),
            ),
            DictionaryReq::new_variant_payload_indirection(
                Type::variable(decoy_variant),
                ustr("Shared"),
                Type::variable(decoy_payload),
            ),
            DictionaryReq::new_variant_payload_indirection(
                Type::variable(matching_payload),
                ustr("Marker"),
                int_type(),
            ),
        ]);
        let mut subst = FxHashMap::default();

        bind_constraint_only_variant_types(&callee_requirements, &caller, &mut subst).unwrap();

        assert_eq!(
            subst.get(&callee_variant),
            Some(&Type::variable(matching_variant))
        );
        assert_eq!(
            subst.get(&callee_payload),
            Some(&Type::variable(matching_payload))
        );
    }

    #[test]
    fn late_variant_storage_mapping_rejects_same_tag_ambiguity() {
        let callee_left = TypeVar::new(0);
        let callee_right = TypeVar::new(1);
        let caller_left = TypeVar::new(2);
        let caller_right = TypeVar::new(3);
        let callee_requirements = extra_parameters(vec![
            DictionaryReq::new_variant_payload_indirection(
                Type::variable(callee_left),
                ustr("Some"),
                Type::unit(),
            ),
            DictionaryReq::new_variant_payload_indirection(
                Type::variable(callee_right),
                ustr("Some"),
                Type::unit(),
            ),
        ]);
        let caller = extra_parameters(vec![
            DictionaryReq::new_variant_payload_indirection(
                Type::variable(caller_left),
                ustr("Some"),
                Type::unit(),
            ),
            DictionaryReq::new_variant_payload_indirection(
                Type::variable(caller_right),
                ustr("Some"),
                Type::unit(),
            ),
        ]);

        assert!(
            bind_constraint_only_variant_types(
                &callee_requirements,
                &caller,
                &mut FxHashMap::default(),
            )
            .is_err()
        );

        let callee = LateFunctionInstData {
            requirements: callee_requirements,
            fn_ty: FnType::new_by_val(Vec::<Type>::new(), Type::unit(), EffType::empty()),
            effect_quantifiers: Vec::new(),
        };
        assert!(
            late_module_call_inst_data(
                &callee,
                &callee.fn_ty,
                &hir::FnInstData::none(),
                &caller,
                Location::new_synthesized(),
            )
            .is_err()
        );
    }

    #[test]
    fn late_call_reconstructs_effect_quantifiers_added_or_removed_by_finalization() {
        let effect = EffectVar::new(0);
        let no_parameters = extra_parameters(Vec::new());
        let span = Location::new_synthesized();

        let added = LateFunctionInstData {
            requirements: no_parameters.clone(),
            fn_ty: FnType::new_by_val(
                Vec::<Type>::new(),
                Type::unit(),
                EffType::single_variable(effect),
            ),
            effect_quantifiers: vec![effect],
        };
        assert!(
            late_module_call_inst_data(
                &added,
                &added.fn_ty,
                &hir::FnInstData::none(),
                &no_parameters,
                span,
            )
            .is_ok()
        );

        let removed = LateFunctionInstData {
            requirements: no_parameters.clone(),
            fn_ty: FnType::new_by_val(Vec::<Type>::new(), Type::unit(), EffType::empty()),
            effect_quantifiers: Vec::new(),
        };
        let preliminary = hir::FnInstData::new(
            Vec::new(),
            Vec::new(),
            vec![EffType::single_variable(effect)],
        );
        assert!(
            late_module_call_inst_data(
                &removed,
                &removed.fn_ty,
                &preliminary,
                &no_parameters,
                span,
            )
            .is_ok()
        );
    }

    #[test]
    fn late_effect_mapping_accepts_call_site_effect_supersets() {
        let callee_effect = EffectVar::new(0);
        let caller_only_effect = EffectVar::new(1);
        let pattern = EffType::multiple(&[
            Effect::Primitive(PrimitiveEffect::Write),
            Effect::Variable(callee_effect),
        ]);
        let actual = EffType::multiple(&[
            Effect::Primitive(PrimitiveEffect::Write),
            Effect::Variable(callee_effect),
            Effect::Variable(caller_only_effect),
        ]);
        let mut subst =
            EffectsInstSubst::from_iter([(callee_effect, EffType::single_variable(callee_effect))]);

        assert!(bind_effect_instantiation(&pattern, &actual, &mut subst));
    }

    #[test]
    fn late_effect_mapping_can_instantiate_multiple_variables_as_pure() {
        let left = EffectVar::new(0);
        let right = EffectVar::new(1);
        let pattern = EffType::multiple(&[
            Effect::Primitive(PrimitiveEffect::Fallible),
            Effect::Variable(left),
            Effect::Variable(right),
        ]);
        let actual = EffType::single_primitive(PrimitiveEffect::Fallible);
        let mut subst = EffectsInstSubst::default();

        assert!(bind_effect_instantiation(&pattern, &actual, &mut subst));
        assert_eq!(subst.get(&left), Some(&EffType::empty()));
        assert_eq!(subst.get(&right), Some(&EffType::empty()));
    }

    fn layout_trait() -> Trait {
        Trait::new_with_self_input_type(
            "Layout",
            "Compiler-only layout metadata.",
            Vec::<&str>::new(),
            Vec::<(&str, crate::hir::function::CallableDefinition)>::new(),
        )
        .with_associated_consts([
            TraitAssociatedConst::new("SIZE", Type::primitive::<isize>(), "Size in bytes."),
            TraitAssociatedConst::new("ALIGN", Type::primitive::<isize>(), "Alignment in bytes."),
        ])
    }

    #[test]
    fn final_elaboration_prunes_suffix_after_late_never_substitution() {
        let source_id = crate::SourceId::from_index(1);
        let live_span = Location::new(0, 6, source_id);
        let dead_span = Location::new(8, 11, source_id);
        let other_dead_span = Location::new(13, 17, source_id);
        let block_span = Location::new(0, 17, source_id);
        let mut arena = NodeArena::default();
        // This models a node whose type became Never only when final substitutions were applied.
        let diverging = arena.alloc(Node::new(
            NodeKind::Immediate(LiteralValue::new_native(())),
            Type::never(),
            no_effects(),
            live_span,
        ));
        let dead = arena.alloc(Node::new(
            NodeKind::Immediate(LiteralValue::new_native(999isize)),
            int_type(),
            no_effects(),
            dead_span,
        ));
        let other_dead = arena.alloc(Node::new(
            NodeKind::Immediate(LiteralValue::new_native(1000isize)),
            int_type(),
            no_effects(),
            other_dead_span,
        ));
        let root = arena.alloc(Node::new(
            NodeKind::Block(b(hir::Block {
                body: b(SVec2::from_vec(vec![diverging, dead, other_dead])),
                cleanup: Vec::new(),
            })),
            Type::never(),
            no_effects(),
            block_span,
        ));

        let modules = Modules::new();
        let current_module = Module::new(ModuleId::new(0), Path::single_str("$elaboration_test"));
        let mut impls = TraitImpls::new(ModuleId::new(0));
        let mut deps = FxHashSet::default();
        let mut solver = TraitSolver::new(
            CurrentTypeItems::new_from_module(&current_module),
            &mut impls,
            FxHashMap::default(),
            &mut deps,
            CurrentProjectionSubscriptTypes::empty(),
            PendingFunctionCollector::new(0),
            &modules,
        );
        let dicts = ExtraParameters {
            requirements: vec![],
            variant_payload_layouts: vec![],
            repr_map: FxHashMap::default(),
        };
        let generated_projection_subscripts =
            PendingGeneratedStructuralProjectionSubscripts::new(&current_module);
        let mut ctx = DictElaborationCtx::new_with_generated_projection_subscripts(
            &dicts,
            None,
            &mut solver,
            generated_projection_subscripts,
        );
        let mut elaborated_arena = ENodeArena::default();
        let mut warnings = Vec::new();

        let elaborated = elaborate_hir_with_warnings(
            &arena,
            root,
            &mut elaborated_arena,
            &mut ctx,
            Vec::new(),
            &mut warnings,
        )
        .unwrap();

        let NodeKind::Block(block) = &elaborated_arena[elaborated.root].kind else {
            panic!("expected elaborated block");
        };
        assert_eq!(block.body.len(), 1);
        assert_eq!(
            warnings,
            vec![CompilationWarning::unreachable_code(Location::new(
                dead_span.start(),
                other_dead_span.end(),
                source_id,
            ))]
        );
    }

    fn get_associated_const_node(
        trait_id: TraitId,
        trait_def: &Trait,
        associated_const_index: TraitAssociatedConstIndex,
        input_tys: Vec<Type>,
    ) -> NodeKind {
        NodeKind::GetTraitAssociatedConst(b(GetTraitAssociatedConst {
            associated_const_name: trait_def.associated_const(associated_const_index).name,
            associated_const_span: Location::new_synthesized(),
            trait_id,
            associated_const_index,
            input_tys,
            output_tys: vec![],
            output_effs: vec![],
        }))
    }

    #[test]
    fn concrete_associated_const_elaborates_to_static_getter_call() {
        let traits = vec![layout_trait()];
        let trait_def = &traits[0];
        let trait_id = TraitId::new(ModuleId::new(0), LocalTraitId::new(0));
        let mut arena = NodeArena::default();
        let span = Location::new_synthesized();
        let node = arena.alloc(Node::new(
            get_associated_const_node(
                trait_id,
                trait_def,
                TraitAssociatedConstIndex::from_index(0),
                vec![Type::unit()],
            ),
            int_type(),
            no_effects(),
            span,
        ));

        let modules = Modules::new();
        let mut current_module =
            Module::new(ModuleId::new(0), Path::single_str("$elaboration_test"));
        current_module.traits = traits.clone();
        let qualified_name_env = QualifiedNameEnv::new_from_module(&current_module, &modules);
        let mut impls = TraitImpls::new(ModuleId::new(0));
        let mut fn_collector = FunctionCollector::new(0);
        let mut getter_arena = ENodeArena::default();
        impls.add_concrete_raw(
            trait_id,
            trait_def,
            [Type::unit()],
            [],
            [],
            [
                LiteralValue::new_native(8isize),
                LiteralValue::new_native(4isize),
            ],
            Vec::<(Function, Vec<LocalDecl>)>::new(),
            &mut getter_arena,
            &mut fn_collector,
            &qualified_name_env,
        );
        let mut deps = FxHashSet::default();
        let mut solver = TraitSolver::new(
            CurrentTypeItems::new_from_module(&current_module),
            &mut impls,
            FxHashMap::default(),
            &mut deps,
            CurrentProjectionSubscriptTypes::empty(),
            PendingFunctionCollector::new(0),
            &modules,
        );
        let dicts = ExtraParameters {
            requirements: vec![],
            variant_payload_layouts: vec![],
            repr_map: FxHashMap::default(),
        };
        let generated_projection_subscripts =
            PendingGeneratedStructuralProjectionSubscripts::new(&current_module);
        let mut ctx = DictElaborationCtx::new_with_generated_projection_subscripts(
            &dicts,
            None,
            &mut solver,
            generated_projection_subscripts,
        );

        let mut elaborated_arena = ENodeArena::default();
        let elaborated =
            elaborate_hir(&arena, node, &mut elaborated_arena, &mut ctx, Vec::new()).unwrap();

        let NodeKind::StaticApply(call) = &elaborated_arena[elaborated.root].kind else {
            panic!("expected associated const to elaborate to a static getter call");
        };
        assert!(call.arguments.is_empty());
        assert_eq!(call.function.function.as_index(), 0);
    }

    #[test]
    fn generic_associated_const_elaborates_to_dictionary_getter_call() {
        let traits = vec![layout_trait()];
        let trait_def = &traits[0];
        let trait_id = TraitId::new(ModuleId::new(0), LocalTraitId::new(0));
        let input_ty = Type::variable_id(0);
        let mut arena = NodeArena::default();
        let span = Location::new_synthesized();
        let node = arena.alloc(Node::new(
            get_associated_const_node(
                trait_id,
                trait_def,
                TraitAssociatedConstIndex::from_index(1),
                vec![input_ty],
            ),
            int_type(),
            no_effects(),
            span,
        ));

        let mut impls = TraitImpls::new(ModuleId::new(0));
        let modules = Modules::new();
        let mut current_module =
            Module::new(ModuleId::new(0), Path::single_str("$elaboration_test"));
        current_module.traits = traits.clone();
        let mut deps = FxHashSet::default();
        let mut solver = TraitSolver::new(
            CurrentTypeItems::new_from_module(&current_module),
            &mut impls,
            FxHashMap::default(),
            &mut deps,
            CurrentProjectionSubscriptTypes::empty(),
            PendingFunctionCollector::new(0),
            &modules,
        );
        let dicts = ExtraParameters {
            requirements: vec![DictionaryReq::new_trait_impl(
                trait_id,
                vec![input_ty],
                vec![],
                vec![],
            )],
            variant_payload_layouts: vec![],
            repr_map: FxHashMap::default(),
        };
        let generated_projection_subscripts =
            PendingGeneratedStructuralProjectionSubscripts::new(&current_module);
        let mut ctx = DictElaborationCtx::new_with_generated_projection_subscripts(
            &dicts,
            None,
            &mut solver,
            generated_projection_subscripts,
        );

        let mut elaborated_arena = ENodeArena::default();
        let elaborated =
            elaborate_hir(&arena, node, &mut elaborated_arena, &mut ctx, Vec::new()).unwrap();

        let NodeKind::CallDictionaryFunction(call) = &elaborated_arena[elaborated.root].kind else {
            panic!("expected associated const to elaborate to a dictionary getter call");
        };
        assert!(call.arguments.is_empty());
        assert_eq!(usize::from(call.entry_index), 1);
        let NodeKind::LoadDictionary(load) = &elaborated_arena[call.dictionary].kind else {
            panic!("expected dictionary getter source to load a dictionary");
        };
        assert_eq!(load.extra_parameter.as_index(), 0);
    }
}
