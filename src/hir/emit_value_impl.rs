// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    FxHashSet, Modules, ast,
    compiler::error::InternalCompilationError,
    containers::b,
    hir::{
        self, NodeArena,
        dictionary_passing::DictElaborationCtx,
        emit_ir::{EmitTraitOutput, emitted_associated_const_values},
        function::ScriptFunction,
    },
    module::{Module, ModuleFunction},
    std::value::{VALUE_TRAIT, derive_generic_value_code_entries},
    types::{
        coherence::check_trait_impl,
        trait_solver::{TraitSolver, trait_solver_from_module},
        r#type::{Type, TypeDefRef, TypeKind, TypeVar},
        type_constraints::named_type_constraints_in_types,
        type_like::TypeLike,
        type_scheme::{PubTypeConstraint, TypeScheme, extra_parameters_from_constraints},
    },
};
use indexmap::IndexSet;

fn type_has_any_ty_var(ty: Type, vars: &[TypeVar]) -> bool {
    let vars = vars.iter().copied().collect::<FxHashSet<_>>();
    ty.inner_ty_vars()
        .into_iter()
        .any(|var| vars.contains(&var))
}

fn auto_value_direct_member_tys(ty: Type) -> Vec<Type> {
    let ty_data = ty.data();
    match &*ty_data {
        TypeKind::Tuple(member_tys) => member_tys.clone(),
        TypeKind::Record(fields) => fields.iter().map(|(_, ty)| *ty).collect(),
        TypeKind::Variant(variants) => variants.iter().map(|(_, ty)| *ty).collect(),
        TypeKind::Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = named.instantiated_shape();
            auto_value_direct_member_tys(shape_ty)
        }
        _ => Vec::new(),
    }
}

fn auto_value_constraints(type_def: &TypeDefRef, input_ty: Type) -> Vec<PubTypeConstraint> {
    let span = type_def.span;
    let params = &type_def.shape.ty_quantifiers;
    let mut constraints = IndexSet::new();

    for constraint in named_type_constraints_in_types([input_ty], span) {
        constraints.insert(constraint);
    }

    for member_ty in auto_value_direct_member_tys(input_ty) {
        if member_ty == Type::unit() || !type_has_any_ty_var(member_ty, params) {
            continue;
        }
        let constraint =
            PubTypeConstraint::new_have_trait(VALUE_TRAIT.clone(), vec![member_ty], vec![], span);
        constraints.insert(constraint);
    }

    constraints.into_iter().collect()
}

fn explicit_value_impl_overlaps_type_def(imp: &ast::DTraitImpl, type_def: &TypeDefRef) -> bool {
    if imp.trait_name.0 != VALUE_TRAIT.name {
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

fn has_named_head_for_type_def(ty: Type, type_def: &TypeDefRef) -> bool {
    let ty_data = ty.data();
    ty_data
        .as_named()
        .is_some_and(|named| named.def == *type_def)
}

fn value_impl_for_type_def_already_exists(output: &Module, type_def: &TypeDefRef) -> bool {
    output.impls.concrete().keys().any(|key| {
        key.trait_ref == *VALUE_TRAIT
            && key
                .input_tys
                .iter()
                .any(|&ty| has_named_head_for_type_def(ty, type_def))
    }) || output
        .impls
        .blanket()
        .get(&*VALUE_TRAIT)
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
    ir_arena: &mut NodeArena,
    others: &Modules,
    explicit_impls: &[ast::DTraitImpl],
) -> Result<(), InternalCompilationError> {
    let type_defs = output.type_defs().to_vec();
    for type_def in type_defs {
        if value_impl_for_type_def_already_exists(output, &type_def) {
            continue;
        }
        if explicit_impls
            .iter()
            .any(|imp| explicit_value_impl_overlaps_type_def(imp, &type_def))
        {
            continue;
        }

        let input_ty = Type::named(
            type_def.clone(),
            (0..type_def.param_names.len())
                .map(|index| Type::variable_id(index as u32))
                .collect::<Vec<_>>(),
        );
        let constraints = auto_value_constraints(&type_def, input_ty);
        let ty_var_count = TypeScheme::list_ty_vars(&input_ty, constraints.iter()).len() as u32;
        let associated_const_values = emitted_associated_const_values(
            &VALUE_TRAIT,
            &[input_ty],
            ty_var_count,
            type_def.span,
        )?;

        check_trait_impl(
            output,
            others,
            &VALUE_TRAIT,
            false,
            &[input_ty],
            ty_var_count,
            &constraints,
            type_def.span,
        )?;

        let Some(code_entries) = ({
            let mut solver = trait_solver_from_module!(output, others);
            let code_entries = derive_generic_value_code_entries(
                &VALUE_TRAIT,
                &[input_ty],
                type_def.span,
                ir_arena,
                &mut solver,
            )?;
            solver.commit(&mut output.functions, &mut output.def_table);
            code_entries
        }) else {
            continue;
        };

        let quantifiers = (0..ty_var_count).map(TypeVar::new).collect::<Vec<_>>();
        let definitions = VALUE_TRAIT.instantiate_for_tys(&[input_ty], &[]);
        let dicts = extra_parameters_from_constraints(&constraints);
        let mut function_ids = Vec::with_capacity(code_entries.len());

        for (method_index, (definition, (root, locals))) in
            definitions.into_iter().zip(code_entries).enumerate()
        {
            let mut definition = definition;
            definition.ty_scheme.ty_quantifiers = quantifiers.clone();
            definition.ty_scheme.constraints = constraints.clone();
            let arg_names = definition.arg_names.clone();
            let code = b(ScriptFunction::new(root, arg_names)) as hir::function::Function;
            let mut function = ModuleFunction::new(definition, code, None, locals);
            {
                let mut solver = trait_solver_from_module!(output, others);
                let mut ctx = DictElaborationCtx::new(&dicts, None, &mut solver);
                function.check_borrows_and_elaborate_dictionaries(ir_arena, &mut ctx)?;
                solver.commit(&mut output.functions, &mut output.def_table);
            }
            let id = output.add_function_anonymous(function);
            output.name_function(
                id,
                VALUE_TRAIT
                    .qualified_method_name(method_index, &[input_ty])
                    .into(),
            );
            function_ids.push(id);
        }

        output.add_emitted_impl(
            VALUE_TRAIT.clone(),
            EmitTraitOutput {
                input_tys: vec![input_ty],
                output_tys: vec![],
                ty_var_count,
                constraints,
                functions: function_ids,
            },
            associated_const_values,
            Some(type_def.span),
        );
    }

    Ok(())
}
