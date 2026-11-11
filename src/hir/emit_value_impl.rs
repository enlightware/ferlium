// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexSet;
use itertools::Itertools;
use ustr::{Ustr, ustr};

use crate::{
    FxHashMap, FxHashSet, Location, Modules, ast,
    compiler::error::InternalCompilationError,
    hir::{
        NodeArena,
        dictionary::DictElaborationCtx,
        elaboration::elaborate_generated_functions,
        emit_associated_consts::emitted_associated_const_values,
        emit_functions::EmitTraitOutput,
        emit_hir::{
            PendingModuleFunctions, add_pending_function_anonymous,
            add_source_associated_const_getters,
        },
    },
    internal_compilation_error,
    module::{
        DictionaryEntryRequirements, ImplGenericNames, LocalFunctionId, Module, ModuleEnv,
        PendingGeneratedStructuralProjectionSubscripts, PendingModuleFunction, QualifiedNameEnv,
        TraitId, TypeDefId, Visibility, id::Id,
    },
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        value::{
            NO_DERIVE_VALUE_ATTRIBUTE, derive_generic_value_code_entries,
            function_value_method_function, function_value_method_name,
            generated_value_evidence_types, generated_value_layout_getter,
            variant_payload_storage_for_type, variant_payload_storage_type,
        },
    },
    types::{
        coherence::check_trait_impl,
        effects::{EffType, EffectVar, EffectsInstSubst},
        r#trait::{TraitAssociatedConstIndex, TraitMethodIndex},
        trait_solver::{
            EvidencePlan, TraitSolver, alpha_canonicalize_types, trait_solver_from_module,
        },
        r#type::{Type, TypeDef, TypeKind, TypeVar},
        type_constraints::named_type_constraints_in_types,
        type_inference::unify::UnifiedTypeInference,
        type_like::{TypeLike, instantiate_types_in_place},
        type_mapper::BitmapInstantiationMapper,
        type_scheme::{PubTypeConstraint, TypeScheme, extra_parameters_from_constraints},
    },
};

/// Return or lazily emit one compiler-provided `Value` method for function values.
pub(crate) fn function_value_method(
    solver: &mut TraitSolver<'_>,
    method_index: TraitMethodIndex,
    span: Location,
) -> Result<LocalFunctionId, InternalCompilationError> {
    let name = function_value_method_name(method_index);
    if let Some(local_id) = solver.current_function(name) {
        return Ok(local_id);
    }
    if let Some(local_id) = solver.fn_collector.get_function(name) {
        return Ok(local_id);
    }

    let local_id = solver.fn_collector.next_id();
    let function = function_value_method_function(method_index, span, solver)?;
    solver
        .fn_collector
        .push_with_visibility(name, function, Visibility::Module);
    Ok(local_id)
}

/// Emit generated structural `Value` methods for a non-concrete type shape.
pub(crate) fn generic_value_methods_for_type(
    solver: &mut TraitSolver<'_>,
    trait_id: TraitId,
    input_tys: &[Type],
    span: Location,
    arena: &mut NodeArena,
) -> Result<Vec<LocalFunctionId>, InternalCompilationError> {
    // These methods quantify every unresolved variable, so caller-local variable identities do not
    // distinguish their code or interface. Generate and look them up at one alpha-canonical type;
    // the use-site dictionary retains the caller's actual type.
    let canonical_input_tys = alpha_canonicalize_types(input_tys);
    let input_tys = canonical_input_tys.as_slice();
    let evidence_tys = generated_value_evidence_types(input_tys[0], solver).ok_or_else(|| {
        internal_compilation_error!(TraitImplNotFound {
            trait_ref: trait_id,
            input_tys: input_tys.to_vec(),
            fn_span: span,
        })
    })?;
    let constraints = evidence_tys
        .into_iter()
        .map(|ty| PubTypeConstraint::new_have_trait(trait_id, vec![ty], vec![], vec![], span))
        .collect::<Vec<_>>();
    let Some(mut code_entries) =
        derive_generic_value_code_entries(trait_id, input_tys, span, arena, solver)?
    else {
        return Err(internal_compilation_error!(TraitImplNotFound {
            trait_ref: trait_id,
            input_tys: input_tys.to_vec(),
            fn_span: span,
        }));
    };

    let (definitions, method_names) = {
        let trait_def = solver.trait_def(trait_id);
        let definitions = trait_def.instantiate_for_tys(input_tys, &[], &[]);
        let qualified_name_env = solver.qualified_name_env();
        let suffix = if input_tys.iter().any(|ty| !ty.is_constant()) {
            "-generic"
        } else {
            ""
        };
        let method_names = (0..definitions.len())
            .map(|index| {
                let method_index = TraitMethodIndex::from_index(index);
                Ustr::from(&format!(
                    "{}{suffix}",
                    qualified_name_env.disambiguated_impl_method_name(
                        trait_id,
                        trait_def,
                        method_index,
                        input_tys,
                        &[],
                        &[],
                        0,
                        0,
                        &[],
                    )
                ))
            })
            .collect::<Vec<_>>();
        (definitions, method_names)
    };
    let supplied_count = crate::hir::trait_defaults::complete_pending_methods(
        solver.trait_def(trait_id),
        &definitions,
        crate::hir::dictionary::DictionaryReq::new_trait_impl(
            trait_id,
            input_tys.to_vec(),
            vec![],
            vec![],
        ),
        &mut code_entries,
    );
    let mut methods = Vec::with_capacity(code_entries.len());
    for (method_index, (mut definition, (body, locals))) in
        definitions.into_iter().zip(code_entries).enumerate()
    {
        let name = method_names[method_index];
        if let Some(local_id) = solver.current_function(name) {
            methods.push(local_id);
            continue;
        }
        if let Some(local_id) = solver.fn_collector.get_function(name) {
            methods.push(local_id);
            continue;
        }

        let mut method_constraints = constraints.clone();
        if method_index >= supplied_count {
            method_constraints.push(PubTypeConstraint::new_have_trait(
                trait_id,
                input_tys.to_vec(),
                vec![],
                vec![],
                span,
            ));
        }
        definition.ty_scheme = TypeScheme::new_infer_quantifiers_with_constraints(
            definition.ty_scheme.ty.clone(),
            method_constraints,
        );
        let runtime_arg_count = definition.arg_names.len();
        let function =
            PendingModuleFunction::from_body(definition, body, runtime_arg_count, None, locals);
        let id = solver.fn_collector.next_id();
        solver
            .fn_collector
            .push_with_visibility(name, function, Visibility::Module);
        methods.push(id);
    }
    Ok(methods)
}

fn type_has_any_ty_var(ty: Type, vars: &[TypeVar]) -> bool {
    let vars = vars.iter().copied().collect::<FxHashSet<_>>();
    ty.inner_ty_vars()
        .into_iter()
        .any(|var| vars.contains(&var))
}

/// Return the fields/payloads whose `Value` impls are called directly by the
/// generated `Value` impl for `ty`.
fn auto_value_direct_members(ty: Type, env: &ModuleEnv<'_>) -> Vec<(Option<(Type, Ustr)>, Type)> {
    let ty_data = ty.data();
    match &*ty_data {
        TypeKind::Tuple(member_tys) => member_tys.iter().map(|ty| (None, *ty)).collect(),
        TypeKind::Record(fields) => fields.iter().map(|(_, ty)| (None, *ty)).collect(),
        TypeKind::Variant(variants) => variants
            .iter()
            .map(|(tag, payload_ty)| (Some((ty, *tag)), *payload_ty))
            .collect(),
        TypeKind::Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = named.instantiated_shape(env);
            let shape_data = shape_ty.data();
            match &*shape_data {
                TypeKind::Variant(variants) => variants
                    .iter()
                    .map(|(tag, payload_ty)| (Some((ty, *tag)), *payload_ty))
                    .collect(),
                _ => {
                    drop(shape_data);
                    auto_value_direct_members(shape_ty, env)
                }
            }
        }
        _ => Vec::new(),
    }
}

/// Build the where-clause for an auto-emitted generic `Value` impl.
///
/// Function-typed members are skipped because their `Value` impl is
/// compiler-provided from the hidden closure environment, not from a
/// user-visible dictionary requirement.
fn auto_value_constraints(
    type_def: &TypeDef,
    input_ty: Type,
    env: &ModuleEnv<'_>,
) -> Vec<PubTypeConstraint> {
    let span = type_def.span;
    let params = &type_def.shape.ty_quantifiers;
    let value_trait_id = env.expect_std_trait_id(VALUE_TRAIT_NAME);
    let mut constraints = IndexSet::new();

    for constraint in named_type_constraints_in_types([input_ty], span, env) {
        constraints.insert(constraint);
    }

    for member_ty in generated_value_evidence_types(input_ty, env).unwrap_or_default() {
        if member_ty == Type::unit() || !type_has_any_ty_var(member_ty, params) {
            continue;
        }
        let constraint = PubTypeConstraint::new_have_trait(
            value_trait_id,
            vec![member_ty],
            vec![],
            vec![],
            span,
        );
        constraints.insert(constraint);
    }

    for (variant_case, member_ty) in auto_value_direct_members(input_ty, env) {
        if let Some((variant_ty, tag)) = variant_case {
            if variant_payload_storage_for_type(variant_ty, tag, span, env).is_ok() {
                continue;
            }
            // The layout witness describes the object projected directly from the variant. For
            // scalar payloads that object is the uniform one-element tuple storage, even though
            // the generated Value method subsequently projects and operates on the scalar member.
            let storage_ty = variant_payload_storage_type(member_ty);
            constraints.insert(PubTypeConstraint::new_variant_payload_layout(
                variant_ty, tag, storage_ty, span,
            ));
        }
    }

    constraints.into_iter().collect()
}

fn explicit_value_impl_overlaps_type_def(imp: &ast::DTraitImpl, type_def: TypeDefId) -> bool {
    if imp.trait_name.0 != VALUE_TRAIT_NAME {
        return false;
    }
    let Some(for_trait) = &imp.for_trait else {
        return false;
    };
    if for_trait.input_types.len() != 1 {
        return false;
    }
    let ty = for_trait.input_types[0].ty.0;
    has_named_head_for_type_def(ty, type_def)
}

fn has_named_head_for_type_def(ty: Type, type_def: TypeDefId) -> bool {
    let ty_data = ty.data();
    ty_data
        .as_named()
        .is_some_and(|named| named.def == type_def)
}

/// Build layout entries in the defining scope, with exactly the impl's supplied evidence.
/// Symbolic constant reads in the body construct private field dictionaries from those leaves.
pub(super) fn add_value_layout_getters(
    output: &mut Module,
    others: &Modules,
    input_ty: Type,
    constraints: &[PubTypeConstraint],
    evidence_plan: &EvidencePlan,
    names: &[Ustr],
    span: Location,
) -> Result<Vec<LocalFunctionId>, InternalCompilationError> {
    let kind = input_ty.data().clone();
    let layout_ty = match kind {
        TypeKind::Named(named) => ModuleEnv::new(output, others)
            .type_def(named.def)
            .instantiated_shape_with_effects(&named.params, &named.effect_params),
        _ => input_ty,
    };
    let quantifiers = TypeScheme::list_ty_vars(&input_ty, constraints.iter())
        .into_iter()
        .sorted()
        .collect::<Vec<_>>();
    let effects = TypeScheme::list_eff_vars(&input_ty, constraints.iter());
    let mut pending = PendingModuleFunctions::default();
    let mut ids = Vec::new();
    for index in (0..names.len()).map(TraitAssociatedConstIndex::from_index) {
        let mut solver = trait_solver_from_module!(output, others);
        let mut getter = generated_value_layout_getter(layout_ty, index, span, &mut solver)?;
        getter.evidence_plan = evidence_plan.clone();
        getter.definition.ty_scheme.constraints = constraints.to_vec();
        getter.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
        getter.definition.ty_scheme.eff_quantifiers = effects.clone();
        let generated =
            solver
                .finish()
                .commit(&mut output.functions, &mut output.def_table, &mut pending);
        elaborate_generated_functions(output, others, &mut pending, generated)?;
        ids.push(add_pending_function_anonymous(output, &mut pending, getter));
    }
    elaborate_generated_functions(output, others, &mut pending, ids.iter().copied())?;
    for (name, id) in names.iter().copied().zip(ids.iter().copied()) {
        output.name_function_with_visibility(id, name, Visibility::Module);
    }
    Ok(ids)
}

fn value_impl_for_type_def_already_exists(
    output: &Module,
    value_trait_id: TraitId,
    type_def: TypeDefId,
) -> bool {
    output.impls.concrete().iter().any(|(key, id)| {
        key.trait_id == value_trait_id
            && output.impls.get_impl_by_local_id(*id).source_span.is_some()
            && key
                .input_tys
                .iter()
                .any(|&ty| has_named_head_for_type_def(ty, type_def))
    }) || output
        .impls
        .blanket()
        .get(&value_trait_id)
        .is_some_and(|impls| {
            impls.iter().any(|(sub_key, id)| {
                output.impls.get_impl_by_local_id(*id).source_span.is_some()
                    && sub_key
                        .input_tys
                        .iter()
                        .any(|&ty| has_named_head_for_type_def(ty, type_def))
            })
        })
}

/// Emit compiler-generated `Value` impls for local named ADTs that do not have
/// an overlapping explicit local `Value` impl.
///
/// The owning module exports the implementation when it exports the named type. Its generated
/// methods remain module-private implementation details; making the implementation visible lets
/// consumers reuse the owner's canonical ownership behavior without exposing the representation.
pub(super) fn emit_auto_value_impls(
    output: &mut Module,
    solver_arena: &mut NodeArena,
    others: &Modules,
    explicit_impls: &[ast::DTraitImpl],
) -> Result<(), InternalCompilationError> {
    let value_trait_id = ModuleEnv::new(output, others).expect_std_trait_id(VALUE_TRAIT_NAME);
    let type_defs = output.type_def_ids().collect::<Vec<_>>();
    let mut pending_functions = FxHashMap::default();
    for type_def_id in type_defs {
        if value_impl_for_type_def_already_exists(output, value_trait_id, type_def_id) {
            continue;
        }
        if explicit_impls
            .iter()
            .any(|imp| explicit_value_impl_overlaps_type_def(imp, type_def_id))
        {
            continue;
        }

        let type_def = output.type_def(type_def_id);
        if type_def.has_custom_value_impl {
            continue;
        }
        if type_def
            .attributes
            .iter()
            .any(|attribute| attribute.path.0 == ustr(NO_DERIVE_VALUE_ATTRIBUTE))
        {
            continue;
        }
        let type_def_span = type_def.span;
        let type_names = type_def
            .param_names()
            .enumerate()
            .map(|(index, name)| (TypeVar::new(index as u32), name))
            .collect::<Vec<_>>();
        let type_def_param_count = type_def.param_count();
        let type_def_effect_param_count = type_def.effect_param_count();
        let input_ty = Type::named_with_effects(
            type_def_id,
            (0..type_def_param_count)
                .map(|index| Type::variable_id(index as u32))
                .collect::<Vec<_>>(),
            (0..type_def_effect_param_count)
                .map(|index| EffType::single_variable(EffectVar::new(index as u32)))
                .collect::<Vec<_>>(),
        );
        let public = output.is_trait_impl_exportable(value_trait_id, &[input_ty], others);
        let mut evidence_plan = EvidencePlan::default();
        let mut constraints = {
            let env = ModuleEnv::new(output, others);
            auto_value_constraints(type_def, input_ty, &env)
        };
        if public {
            let mut solver = trait_solver_from_module!(output, others);
            if constraints.iter().any(|c| !solver.requirement_is_public(c)) {
                let count = TypeScheme::list_ty_vars(&input_ty, constraints.iter())
                    .iter()
                    .map(|var| var.name() + 1)
                    .max()
                    .unwrap_or(0);
                let mut inference = UnifiedTypeInference::new_with_ty_vars(count);
                let count = TypeScheme::list_eff_vars(&input_ty, constraints.iter())
                    .iter()
                    .map(|var| var.name() + 1)
                    .max()
                    .unwrap_or(0);
                for _ in 0..count {
                    inference.fresh_effect_var();
                }
                let reduced = solver
                    .reduce_public_requirements(
                        constraints,
                        &[input_ty],
                        &mut inference,
                        solver_arena,
                    )
                    .map_err(|error| {
                        error.with_private_requirement_names(type_names.iter().copied())
                    })?;
                constraints = reduced.requirements;
                evidence_plan = reduced.evidence;
                inference.finalize_effects()?;
                evidence_plan.substitute(&mut inference);
                constraints = constraints
                    .iter()
                    .map(|c| inference.substitute_in_constraint(c))
                    .collect();
            }
            let generated = solver.finish().commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
        }
        // Reduction may introduce output variables from a selected private impl. Keep the
        // type's input parameters first and number those new variables contiguously after them.
        let ty_vars = TypeScheme::list_ty_vars(&input_ty, constraints.iter());
        let ty_var_count = ty_vars.len() as u32;
        let ty_subst = ty_vars
            .into_iter()
            .sorted()
            .enumerate()
            .map(|(index, var)| (var, Type::variable_id(index as u32)))
            .collect();
        // Effect variables occurring only in the type's where clause are impl variables too, as
        // that clause determines them. They follow the effect parameters, so renumbering them
        // canonically leaves the input type unchanged.
        let eff_subst: EffectsInstSubst = TypeScheme::list_eff_vars(&input_ty, constraints.iter())
            .into_iter()
            .sorted()
            .enumerate()
            .map(|(index, var)| (var, EffType::single_variable(EffectVar::new(index as u32))))
            .collect();
        let eff_var_count = eff_subst.len() as u32;
        let subst = (ty_subst, eff_subst);
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        instantiate_types_in_place(&mut constraints, &mut mapper);
        evidence_plan.instantiate_in_place(&mut mapper);
        // A generated dictionary supplies its own evidence when an entry runs. Keep that
        // parameter in entry ABIs, but do not publish a circular prerequisite on the impl.
        let self_requirement = PubTypeConstraint::new_have_trait(
            value_trait_id,
            vec![input_ty],
            vec![],
            vec![],
            type_def_span,
        );
        let supplies_self = constraints.contains(&self_requirement);
        constraints.retain(|constraint| constraint != &self_requirement);
        let mut entry_constraints = constraints.clone();
        if supplies_self {
            entry_constraints.push(self_requirement);
        }
        let associated_const_values = {
            let solver = trait_solver_from_module!(output, others);
            emitted_associated_const_values(
                value_trait_id,
                &[input_ty],
                ty_var_count,
                type_def_span,
                &solver,
            )?
        };

        check_trait_impl(
            output,
            others,
            value_trait_id,
            value_trait_id.module == output.module_id(),
            &[input_ty],
            &[],
            ty_var_count,
            eff_var_count,
            &constraints,
            &ImplGenericNames::default(),
            type_def_span,
        )?;

        let Some(mut code_entries) = ({
            let mut solver = trait_solver_from_module!(output, others);
            let code_entries = derive_generic_value_code_entries(
                value_trait_id,
                &[input_ty],
                type_def_span,
                solver_arena,
                &mut solver,
            )?;
            let generated = solver.finish().commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
            code_entries
        }) else {
            continue;
        };

        let quantifiers = (0..ty_var_count).map(TypeVar::new).collect::<Vec<_>>();
        let (definitions, method_names) = {
            let env = ModuleEnv::new(output, others);
            let qualified_name_env = QualifiedNameEnv::new_from_module(output, others);
            let trait_def = env.trait_def(value_trait_id);
            let definitions = trait_def.instantiate_for_tys(&[input_ty], &[], &[]);
            let method_names = (0..definitions.len())
                .map(|index| {
                    let method_index = TraitMethodIndex::from_index(index);
                    Ustr::from(&qualified_name_env.disambiguated_impl_method_name(
                        value_trait_id,
                        trait_def,
                        method_index,
                        &[input_ty],
                        &[],
                        &[],
                        ty_var_count,
                        0,
                        &constraints,
                    ))
                })
                .collect::<Vec<_>>();
            (definitions, method_names)
        };
        let supplied_count = crate::hir::trait_defaults::complete_pending_methods(
            ModuleEnv::new(output, others).trait_def(value_trait_id),
            &definitions,
            crate::hir::dictionary::DictionaryReq::new_trait_impl(
                value_trait_id,
                vec![input_ty],
                vec![],
                vec![],
            ),
            &mut code_entries,
        );
        let mut function_ids = Vec::with_capacity(code_entries.len());

        for (method_index, (definition, (body, locals))) in
            definitions.into_iter().zip(code_entries).enumerate()
        {
            let method_index = TraitMethodIndex::from_index(method_index);
            let mut definition = definition;
            definition.ty_scheme.ty_quantifiers = quantifiers.clone();
            definition.ty_scheme.eff_quantifiers = (0..eff_var_count).map(EffectVar::new).collect();
            definition.ty_scheme.constraints = entry_constraints.clone();
            if method_index.as_index() >= supplied_count && !supplies_self {
                definition
                    .ty_scheme
                    .constraints
                    .push(PubTypeConstraint::new_have_trait(
                        value_trait_id,
                        vec![input_ty],
                        vec![],
                        vec![],
                        type_def_span,
                    ));
            }
            let dicts = extra_parameters_from_constraints(
                &definition.ty_scheme.constraints,
                ModuleEnv::new(output, others),
            );

            let runtime_arg_count = definition.arg_names.len();
            let mut function =
                PendingModuleFunction::from_body(definition, body, runtime_arg_count, None, locals);
            function.evidence_plan = evidence_plan.clone();
            {
                let generated_projection_subscripts =
                    PendingGeneratedStructuralProjectionSubscripts::new(output);
                let mut solver = trait_solver_from_module!(output, others);
                let mut ctx = DictElaborationCtx::new_with_generated_projection_subscripts(
                    &dicts,
                    None,
                    &mut solver,
                    generated_projection_subscripts,
                );
                let function =
                    function.check_borrows_and_elaborate_hir(&mut output.hir_arena, &mut ctx)?;
                let generated_projection_subscripts = ctx.take_generated_projection_subscripts();
                let generated = solver.finish().commit(
                    &mut output.functions,
                    &mut output.def_table,
                    &mut pending_functions,
                );
                if let Some(generated_projection_subscripts) = generated_projection_subscripts {
                    generated_projection_subscripts.commit(output, others);
                }
                elaborate_generated_functions(output, others, &mut pending_functions, generated)?;
                let id = output.add_function_anonymous(function);
                output.name_function(id, method_names[usize::from(method_index)]);
                function_ids.push(id);
            }
        }

        let associated_const_tys = {
            let env = ModuleEnv::new(output, others);
            env.trait_def(value_trait_id)
                .instantiate_associated_const_tys_for_tys(&[input_ty], &[], &[])
        };
        let mut associated_const_names = trait_solver_from_module!(output, others)
            .impl_associated_const_names(
                value_trait_id,
                &[input_ty],
                &[],
                &[],
                ty_var_count,
                eff_var_count,
                &constraints,
            );
        let associated_const_getters =
            if associated_const_values.is_empty() && !associated_const_tys.is_empty() {
                add_value_layout_getters(
                    output,
                    others,
                    input_ty,
                    &entry_constraints,
                    &evidence_plan,
                    &associated_const_names,
                    type_def_span,
                )?
            } else {
                associated_const_names.truncate(associated_const_values.len());
                add_source_associated_const_getters(
                    output,
                    others,
                    &associated_const_values,
                    &associated_const_tys,
                    &associated_const_names,
                    type_def_span,
                )?
            };
        let entry_requirements = function_ids
            .iter()
            .map(|id| {
                output.functions[id.as_index()]
                    .definition
                    .ty_scheme
                    .extra_parameters(ModuleEnv::new(output, others))
                    .requirements
            })
            .map(DictionaryEntryRequirements::from_callable)
            .collect::<Vec<_>>();
        output.add_emitted_impl(
            value_trait_id,
            EmitTraitOutput {
                evidence_plan,
                input_tys: vec![input_ty],
                output_tys: vec![],
                output_effs: vec![],
                ty_var_count,
                eff_var_count,
                constraints,
                method_requirements: entry_requirements,
                functions: function_ids,
                generic_names: ImplGenericNames::default(),
            },
            associated_const_values,
            associated_const_getters,
            associated_const_tys,
            public,
            Some(type_def_span),
            others,
        );
    }

    Ok(())
}
