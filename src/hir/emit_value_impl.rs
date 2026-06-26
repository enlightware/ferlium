// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    FxHashMap, FxHashSet, Location, Modules, ast,
    compiler::error::InternalCompilationError,
    hir::{
        NodeArena, dictionary::DictElaborationCtx, elaboration::elaborate_generated_functions,
        emit_associated_consts::emitted_associated_const_values, emit_functions::EmitTraitOutput,
    },
    internal_compilation_error,
    module::{
        LocalFunctionId, Module, ModuleEnv, PendingModuleFunction, QualifiedNameEnv, TypeDefId,
        Visibility, id::Id,
    },
    std::core_traits_names::VALUE_TRAIT_NAME,
    std::value::{
        NO_DERIVE_VALUE_ATTRIBUTE, derive_generic_value_code_entries,
        function_value_method_function, function_value_method_name,
        is_function_surface_only_value_type,
    },
    types::{
        coherence::check_trait_impl,
        effects::{EffType, EffectVar},
        r#trait::TraitMethodIndex,
        trait_solver::{TraitSolver, trait_solver_from_module},
        r#type::{Type, TypeDef, TypeKind, TypeVar},
        type_constraints::named_type_constraints_in_types,
        type_like::TypeLike,
        type_scheme::{PubTypeConstraint, TypeScheme, extra_parameters_from_constraints},
    },
};
use indexmap::IndexSet;
use ustr::Ustr;

/// Return or lazily emit one compiler-provided `Value` method for function values.
pub(crate) fn function_value_method(
    solver: &mut TraitSolver<'_>,
    method_index: TraitMethodIndex,
    span: Location,
) -> Result<LocalFunctionId, InternalCompilationError> {
    let name = function_value_method_name(method_index);
    if let Some(local_id) = solver.current_functions.get(&name).copied() {
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
    trait_id: crate::module::TraitId,
    input_tys: &[Type],
    span: Location,
    arena: &mut NodeArena,
) -> Result<Vec<LocalFunctionId>, InternalCompilationError> {
    let Some(code_entries) =
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
        let method_names = (0..definitions.len())
            .map(|index| {
                let method_index = TraitMethodIndex::from_index(index);
                Ustr::from(&format!(
                    "{}-generic",
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
    let mut methods = Vec::with_capacity(code_entries.len());
    for (method_index, (definition, (body, locals))) in
        definitions.into_iter().zip(code_entries).enumerate()
    {
        let name = method_names[method_index];
        if let Some(local_id) = solver.current_functions.get(&name).copied() {
            methods.push(local_id);
            continue;
        }
        if let Some(local_id) = solver.fn_collector.get_function(name) {
            methods.push(local_id);
            continue;
        }

        let runtime_arg_count = definition.arg_names.len();
        let function =
            PendingModuleFunction::from_body(definition, body, runtime_arg_count, None, locals);
        let id = solver.fn_collector.next_id();
        solver.fn_collector.push(name, function);
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
fn auto_value_direct_member_tys(ty: Type, env: &ModuleEnv<'_>) -> Vec<Type> {
    let ty_data = ty.data();
    match &*ty_data {
        TypeKind::Tuple(member_tys) => member_tys.clone(),
        TypeKind::Record(fields) => fields.iter().map(|(_, ty)| *ty).collect(),
        TypeKind::Variant(variants) => variants.iter().map(|(_, ty)| *ty).collect(),
        TypeKind::Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = named.instantiated_shape(env);
            auto_value_direct_member_tys(shape_ty, env)
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

    for member_ty in auto_value_direct_member_tys(input_ty, env) {
        if member_ty == Type::unit()
            || member_ty.is_function()
            || is_function_surface_only_value_type(member_ty)
            || !type_has_any_ty_var(member_ty, params)
        {
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

fn value_impl_for_type_def_already_exists(
    output: &Module,
    value_trait_id: crate::module::TraitId,
    type_def: TypeDefId,
) -> bool {
    output.impls.concrete().keys().any(|key| {
        key.trait_id == value_trait_id
            && key
                .input_tys
                .iter()
                .any(|&ty| has_named_head_for_type_def(ty, type_def))
    }) || output
        .impls
        .blanket()
        .get(&value_trait_id)
        .is_some_and(|impls| {
            impls.keys().any(|sub_key| {
                sub_key
                    .input_tys
                    .iter()
                    .any(|&ty| has_named_head_for_type_def(ty, type_def))
            })
        })
}

/// Emit compiler-generated `Value` impls for local named ADTs that do not have
/// an overlapping explicit local `Value` impl.
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
        if type_def
            .attributes
            .iter()
            .any(|attribute| attribute.path.0 == ustr::ustr(NO_DERIVE_VALUE_ATTRIBUTE))
        {
            continue;
        }
        let type_def_span = type_def.span;
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
        let constraints = {
            let env = ModuleEnv::new(output, others);
            auto_value_constraints(type_def, input_ty, &env)
        };
        let ty_var_count = TypeScheme::list_ty_vars(&input_ty, constraints.iter()).len() as u32;
        let eff_var_count = input_ty.inner_effect_vars().len() as u32;
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
            false,
            &[input_ty],
            &[],
            &[],
            ty_var_count,
            eff_var_count,
            &constraints,
            type_def_span,
        )?;

        let Some(code_entries) = ({
            let mut solver = trait_solver_from_module!(output, others);
            let code_entries = derive_generic_value_code_entries(
                value_trait_id,
                &[input_ty],
                type_def_span,
                solver_arena,
                &mut solver,
            )?;
            let generated = solver.commit(
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
        let dicts = extra_parameters_from_constraints(&constraints, ModuleEnv::new(output, others));
        let mut function_ids = Vec::with_capacity(code_entries.len());

        for (method_index, (definition, (body, locals))) in
            definitions.into_iter().zip(code_entries).enumerate()
        {
            let method_index = TraitMethodIndex::from_index(method_index);
            let mut definition = definition;
            definition.ty_scheme.ty_quantifiers = quantifiers.clone();
            definition.ty_scheme.constraints = constraints.clone();
            let runtime_arg_count = definition.arg_names.len();
            let function =
                PendingModuleFunction::from_body(definition, body, runtime_arg_count, None, locals);
            {
                let mut solver = trait_solver_from_module!(output, others);
                let mut ctx = DictElaborationCtx::new(&dicts, None, &mut solver);
                let (function, _) =
                    function.check_borrows_and_elaborate_hir(&mut output.hir_arena, &mut ctx)?;
                let generated = solver.commit(
                    &mut output.functions,
                    &mut output.def_table,
                    &mut pending_functions,
                );
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
        output.add_emitted_impl(
            value_trait_id,
            EmitTraitOutput {
                input_tys: vec![input_ty],
                output_tys: vec![],
                output_effs: vec![],
                ty_var_count,
                eff_var_count,
                constraints,
                functions: function_ids,
            },
            associated_const_values,
            associated_const_tys,
            false,
            Some(type_def_span),
        );
    }

    Ok(())
}
