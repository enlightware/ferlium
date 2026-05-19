// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::mem;

use crate::{
    FxHashMap, FxHashSet, Modules,
    containers::B,
    hir::{
        borrow_checker::check_borrows, dictionary_passing::elaborate_dictionaries,
        function::VoidFunction,
    },
    module::Uses,
    types::r#trait::TraitMethodIndex,
};

use indexmap::IndexMap;
use itertools::Itertools;
use log::log_enabled;
use ustr::Ustr;

use super::emit_value_impl::emit_auto_value_impls;

use crate::{
    Location,
    ast::{self, *},
    compiler::error::InternalCompilationError,
    containers::{b, iterable_to_string},
    desugar::desugar_expr_with_empty_ctx,
    format::FormatWith,
    hir::dictionary_passing::{
        DictElaborationCtx, ExtraParameters, elaborate_local_value_dispatches,
    },
    hir::function::{FunctionDefinition, ScriptFunction},
    hir::{self, NodeArena},
    internal_compilation_error,
    module::{
        ConcreteTraitImplKey, LocalAssignmentMode, LocalDecl, LocalDeclId, LocalFunctionId,
        LocalImplId, Module, ModuleEnv, ModuleFunction, ModuleFunctionSpans, ModuleId, TraitImpl,
        build_dictionary_value, id::Id,
    },
    std::{
        new_module_using_std,
        value::{
            VALUE_CLONE_METHOD_INDEX, VALUE_TRAIT,
            is_function_surface_only_value_trait_application, is_value_trait_for_function_type,
            value_layout_associated_const_values,
        },
    },
    types::coherence::check_trait_impl,
    types::effects::EffType,
    types::mutability::MutType,
    types::r#trait::TraitRef,
    types::trait_solver::{TraitSolver, trait_solver_from_module},
    types::r#type::{FnArgType, FnType, Type, TypeInstSubst, TypeVar},
    types::type_constraints::named_type_constraints_in_types,
    types::type_inference::{
        defaulting::{ConstraintBoundary, DefaultingScope},
        expr::{AnnotationTypeMapper, TypeInference},
        unify::UnifiedTypeInference,
    },
    types::type_like::{TypeLike, instantiate_types_in_place},
    types::type_mapper::{BitmapInstantiationMapper, TypeMapper},
    types::type_scheme::{
        PubTypeConstraint, TypeScheme, extra_parameters_from_constraints, normalize_types,
    },
    types::type_visitor::{TyVarsCollector, collect_ty_vars},
    types::typing_env::TypingEnv,
};

fn validate_name_uniqueness(source: &ast::PModule) -> Result<(), InternalCompilationError> {
    let mut names = FxHashMap::default();
    for (name, span) in source.own_symbols() {
        if let Some(first_occurrence) = names.insert(name, span) {
            return Err(internal_compilation_error!(NameDefinedMultipleTimes {
                name,
                first_occurrence,
                second_occurrence: span,
            }));
        }
    }
    Ok(())
}

fn insert_inst_data_for_function_and_lambdas(
    module_inst_data: &mut FxHashMap<LocalFunctionId, ExtraParameters>,
    associated_lambdas: &FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    id: LocalFunctionId,
    dicts: ExtraParameters,
) {
    module_inst_data.insert(id, dicts.clone());
    if let Some(lambda_ids) = associated_lambdas.get(&id) {
        for lambda_id in lambda_ids {
            module_inst_data.insert(*lambda_id, dicts.clone());
        }
    }
}

pub(super) fn emitted_associated_const_values(
    trait_ref: &TraitRef,
    input_tys: &[Type],
    ty_var_count: u32,
    span: Location,
    solver: &TraitSolver<'_>,
) -> Result<Vec<isize>, InternalCompilationError> {
    if trait_ref.associated_const_count() == 0 {
        return Ok(Vec::new());
    }

    // Temporary special case: generic source impls cannot yet store associated
    // const formulas, so only Value has compiler-owned layout synthesis here.
    if trait_ref == &*VALUE_TRAIT {
        if ty_var_count != 0 {
            return Ok(Vec::new());
        }
        return Ok(value_layout_associated_const_values(input_tys[0], span, solver)?.into());
    }

    Err(internal_compilation_error!(Internal {
        error: format!(
            "cannot emit compiler-defined associated consts for source impl of trait {}",
            trait_ref.name
        ),
        span,
    }))
}

/// Data for a pre-registered stub implementation for `impl Trait for ConcreteType`.
struct ImplStubData {
    id: LocalImplId,
    input_tys: Vec<Type>,
    method_ids: Vec<LocalFunctionId>,
}

fn instantiate_function_descr_in_place<M: TypeMapper>(
    ir_arena: &mut NodeArena,
    descr: &mut ModuleFunction,
    mapper: &mut M,
) {
    let root = descr.get_code_entry().unwrap();
    hir::instantiate_node_in_place(ir_arena, root, mapper);
    for local in &mut descr.locals {
        local.ty = local.ty.map(mapper);
    }
}

fn refresh_debug_info_for_functions(
    output: &mut Module,
    associated_lambdas: &FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    local_fns: &[LocalFunctionId],
) {
    for id in local_fns {
        let function_and_lambdas =
            std::iter::once(id).chain(associated_lambdas.get(id).into_iter().flatten());
        for id in function_and_lambdas {
            output.functions[id.as_index()].refresh_debug_info();
        }
    }
}

fn default_output_effects_in_functions(
    output: &mut Module,
    ir_arena: &mut NodeArena,
    associated_lambdas: &FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    function_ids: &[LocalFunctionId],
) {
    for &id in function_ids {
        let effect_subst: FxHashMap<_, _> = {
            let descr = &output.functions[id.as_index()];
            let input_effect_vars = descr.definition.ty_scheme.ty.input_effect_vars();
            descr
                .definition
                .ty_scheme
                .ty
                .output_effect_vars()
                .into_iter()
                .filter(|var| !input_effect_vars.contains(var))
                .map(|var| (var, EffType::empty()))
                .collect()
        };
        if effect_subst.is_empty() {
            continue;
        }

        let subst = (FxHashMap::default(), effect_subst);
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        let function_and_lambdas =
            std::iter::once(id).chain(associated_lambdas.get(&id).into_iter().flatten().copied());
        for function_id in function_and_lambdas {
            let descr = &mut output.functions[function_id.as_index()];
            descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
            instantiate_function_descr_in_place(ir_arena, descr, &mut mapper);
        }
    }
}

/// Kinds existing data to be used when emitting a new module in [`emit_module`]
pub enum EmitModuleFrom {
    /// A fresh module with specific use-directives is created
    Uses(Uses),
    /// An existing module extended
    Existing(B<Module>),
}

/// Emit HIR for the given module.
/// Optionally merge with an existing module (when compiling std).
pub fn emit_module(
    source: ast::PModule,
    parsed_arena: &PExprArena,
    module_id: ModuleId,
    others: &Modules,
    emit_from: EmitModuleFrom,
) -> Result<Module, InternalCompilationError> {
    // Preliminary: Make sure no name is defined multiple times.
    validate_name_uniqueness(&source)?;

    // First desugar the module.
    let mut output = match emit_from {
        EmitModuleFrom::Uses(uses) => Module::from_uses(module_id, uses),
        EmitModuleFrom::Existing(module) => *module,
    };
    let (source, desugared_arena, sorted_sccs) =
        source.desugar(&mut output, others, parsed_arena)?;

    // Pre-registration pass: for trait impls with an explicit `for ConcreteType` annotation,
    // register a stub implementation before processing any function SCCs. This allows module
    // functions to use trait methods from these impls regardless of source order.
    let mut concrete_impl_stubs: FxHashMap<usize, ImplStubData> = FxHashMap::default();
    for (imp_idx, imp) in source.impls.iter().enumerate() {
        if let Some(for_trait) = &imp.for_trait {
            let input_tys = for_trait.input_tys();
            let output_tys = for_trait.output_tys();
            let module_env = ModuleEnv::new(&output, others);
            let Some((trait_module_id, trait_ref)) =
                module_env.trait_ref_with_module(&Path::single_tuple(imp.trait_name))?
            else {
                continue; // Trait not found; the error will be reported in the main impl loop
            };
            if input_tys.len() != trait_ref.input_type_count() as usize {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: trait_ref.input_type_count() as usize,
                    expected_span: imp.trait_name.1,
                    got: input_tys.len(),
                    got_span: imp.span,
                }));
            }
            let mut stub_tys = input_tys.clone();
            stub_tys.extend(output_tys.iter().copied());
            if !collect_ty_vars(&stub_tys).is_empty() {
                continue;
            }
            if !output_tys.is_empty() && output_tys.len() != trait_ref.output_type_count() as usize
            {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: trait_ref.output_type_count() as usize,
                    expected_span: imp.trait_name.1,
                    got: output_tys.len(),
                    got_span: for_trait.span,
                }));
            }
            if output_tys.is_empty() && trait_ref.output_type_count() != 0 {
                continue;
            }
            check_trait_impl(
                &output,
                others,
                &trait_ref,
                trait_module_id.is_none(),
                &input_tys,
                0,
                &[],
                imp.span,
            )?;
            // Pre-allocate placeholder functions for each trait method.
            let method_defs = trait_ref.instantiate_for_tys(&input_tys, &output_tys);
            let mut method_ids = Vec::with_capacity(method_defs.len());
            for def in method_defs {
                // Placeholder ModuleFunction that will be replaced later.
                let placeholder = b(VoidFunction);
                let module_fn = ModuleFunction::new_without_spans_nor_locals(def, placeholder);
                method_ids.push(output.add_function_anonymous(module_fn));
            }
            // Build the trait impl and fill it with placeholders.
            let associated_const_values = {
                let solver = trait_solver_from_module!(output, others);
                emitted_associated_const_values(&trait_ref, &input_tys, 0, imp.span, &solver)?
            };
            let dictionary_value = build_dictionary_value(&method_ids, &associated_const_values);
            let dictionary_ty =
                output.computer_dictionary_ty(&method_ids, associated_const_values.len());
            let stub = TraitImpl::new(
                output_tys,
                method_ids.clone(),
                dictionary_value,
                dictionary_ty,
                true,
                Some(imp.span),
            )
            .with_associated_const_values(associated_const_values);
            let key = ConcreteTraitImplKey::new(trait_ref, input_tys.clone());
            let id = output.impls.add_concrete_struct(key, stub);
            concrete_impl_stubs.insert(
                imp_idx,
                ImplStubData {
                    id,
                    method_ids,
                    input_tys,
                },
            );
        }
    }

    // Take the module's HIR node arena out for compilation so it can be passed separately
    // from the module borrow, then put it back at the end.
    let mut ir_arena = std::mem::take(&mut output.ir_arena);

    emit_auto_value_impls(&mut output, &mut ir_arena, others, &source.impls)?;

    // Process each functions' SCC one by one.
    for mut scc in sorted_sccs.into_iter().rev() {
        scc.sort(); // for compatibility due to bug in effect tracking

        // Extract functions from the SCC.
        let functions = || scc.iter().map(|&idx| &source.functions[idx]);
        if log_enabled!(log::Level::Debug) {
            let names = functions().map(|f| f.name.0).collect::<Vec<_>>();
            log::debug!(
                "Processing circularly dependent functions: {}",
                iterable_to_string(names, ", ")
            );
        }

        // Emit the corresponding functions.
        emit_functions(
            &mut output,
            &mut ir_arena,
            functions,
            &desugared_arena,
            others,
            None,
        )?;
    }

    // Process trait implementations
    for (imp_idx, imp) in source.impls.iter().enumerate() {
        // Validate the function mapping.
        let module_env = ModuleEnv::new(&output, others);
        let (trait_module_id, trait_ref) = module_env
            .trait_ref_with_module(&Path::single_tuple(imp.trait_name))?
            .ok_or_else(|| internal_compilation_error!(TraitNotFound(imp.trait_name.1)))?;

        // Check that all methods in the impl are part of the trait.
        let mut extra_spans = vec![];
        for func in imp.functions.iter() {
            if trait_ref.method_index(func.name.0).is_none() {
                extra_spans.push(func.name.1);
            }
        }
        if !extra_spans.is_empty() {
            return Err(internal_compilation_error!(MethodsNotPartOfTrait {
                trait_ref: trait_ref.clone(),
                spans: extra_spans,
            }));
        }

        // Collect references to functions in the impl, in the order of the trait methods.
        let mut missings = vec![];
        let functions: Vec<_> = trait_ref
            .methods
            .iter()
            .filter_map(|(name, _)| {
                imp.functions
                    .iter()
                    .find(|func| func.name.0 == *name)
                    .or_else(|| {
                        missings.push(*name);
                        None
                    })
            })
            .collect();
        if !missings.is_empty() {
            return Err(internal_compilation_error!(TraitMethodImplsMissing {
                trait_ref: trait_ref.clone(),
                impl_span: imp.span,
                missings,
            }));
        }

        // Emit the functions.
        debug_assert_eq!(functions.len(), trait_ref.methods.len());
        let functions = || functions.iter().copied();
        let trait_ctx = EmitTraitCtx {
            trait_ref: trait_ref.clone(),
            span: imp.span,
            stub_data: concrete_impl_stubs.get(&imp_idx),
            generic_param_count: imp.generic_params.len(),
            for_trait: imp.for_trait.as_ref(),
            impl_constraints: &imp.where_clause,
        };
        let emit_output = emit_functions(
            &mut output,
            &mut ir_arena,
            functions,
            &desugared_arena,
            others,
            Some(trait_ctx),
        )?
        .unwrap();

        // Register the implementation if no stub was present.
        let is_concrete = emit_output.ty_var_count == 0;
        let local_impl_id = if let Some(stub_data) = concrete_impl_stubs.get(&imp_idx) {
            assert_eq!(
                &emit_output.functions,
                &output.impls.data[stub_data.id.as_index()].methods
            );
            let associated_const_count = output.impls.data[stub_data.id.as_index()]
                .associated_const_values
                .len();
            let new_dictionary_ty =
                output.computer_dictionary_ty(&emit_output.functions, associated_const_count);
            let impl_data = output.impls.data.get_mut(stub_data.id.as_index()).unwrap();
            assert_eq!(new_dictionary_ty, impl_data.dictionary_ty);
            stub_data.id
        } else {
            check_trait_impl(
                &output,
                others,
                &trait_ref,
                trait_module_id.is_none(),
                &emit_output.input_tys,
                emit_output.ty_var_count,
                &emit_output.constraints,
                imp.span,
            )?;
            let associated_const_values = emitted_associated_const_values(
                &trait_ref,
                &emit_output.input_tys,
                emit_output.ty_var_count,
                imp.span,
                &trait_solver_from_module!(output, others),
            )?;
            output.add_emitted_impl(
                trait_ref,
                emit_output,
                associated_const_values,
                Some(imp.span),
            )
        };
        let module_env = ModuleEnv::new(&output, others);
        let header = output
            .impls
            .impl_header_to_string_by_id(local_impl_id, module_env);
        let header = header.strip_suffix("\n").unwrap_or_else(|| &header);
        let impl_type = if is_concrete { "Concrete" } else { "Blanket" };
        log::debug!("Emitted {impl_type} {header}");
    }

    // Restore the HIR arena.
    output.ir_arena = ir_arena;
    Ok(output)
}

/// Context passed to emit_functions when a trait implementation is being emitted.
struct EmitTraitCtx<'a> {
    trait_ref: TraitRef,
    span: Location,
    stub_data: Option<&'a ImplStubData>,
    generic_param_count: usize,
    for_trait: Option<&'a ast::DTraitImplFor>,
    impl_constraints: &'a [PubTypeConstraint],
}

pub(crate) struct EmitTraitOutput {
    pub(crate) input_tys: Vec<Type>,
    pub(crate) output_tys: Vec<Type>,
    pub(crate) ty_var_count: u32,
    pub(crate) constraints: Vec<PubTypeConstraint>,
    pub(crate) functions: Vec<LocalFunctionId>,
}

fn emit_functions<'a, F, I>(
    output: &mut Module,
    ir_arena: &mut NodeArena,
    ast_functions: F,
    desugared_arena: &DExprArena,
    others: &Modules,
    trait_ctx: Option<EmitTraitCtx>,
) -> Result<Option<EmitTraitOutput>, InternalCompilationError>
where
    I: Iterator<Item = &'a DModuleFunction>,
    F: Fn() -> I,
{
    // First pass, populate the function table and allocate fresh mono type variables.
    let mut ty_inf = TypeInference::default();
    let mut impl_annotation_subst = None;
    let mut outer_annotation_var_count = 0;
    let mut explicit_trait_impl = None;
    let module_env = ModuleEnv::new(output, others);

    // If we are emitting a trait implementation, create generics for the trait input and output types
    // and add the constraints from the trait definition to the type inference.
    let trait_output = if let Some(trait_ctx) = &trait_ctx {
        let trait_ref = &trait_ctx.trait_ref;
        let input_tys = ty_inf.fresh_type_var_tys(trait_ref.input_type_count() as usize);
        let output_tys = ty_inf.fresh_type_var_tys(trait_ref.output_type_count() as usize);
        let explicit_quantifiers = if trait_ctx.generic_param_count > 0 {
            (0..trait_ctx.generic_param_count)
                .map(|index| TypeVar::new(index as u32))
                .collect::<Vec<_>>()
        } else if let Some(for_trait) = trait_ctx.for_trait {
            let mut tys = for_trait.input_tys();
            tys.extend(for_trait.output_tys());
            collect_ty_vars(&tys)
        } else {
            vec![]
        };
        // Reserve the leading annotation placeholder indices for explicit impl-level generics,
        // so any function-level generics in this shared path start after them.
        outer_annotation_var_count = explicit_quantifiers.len();
        if !explicit_quantifiers.is_empty() {
            impl_annotation_subst = Some((
                ty_inf.fresh_type_var_subst(&explicit_quantifiers),
                FxHashMap::default(),
            ));
        }
        explicit_trait_impl = trait_ctx.for_trait.map(|for_trait| {
            let mut mapper = impl_annotation_subst
                .as_ref()
                .map(BitmapInstantiationMapper::new);
            let mut instantiate = |ty: Type| match &mut mapper {
                Some(m) => ty.map(m),
                None => ty,
            };
            let input_tys: Vec<_> = for_trait
                .input_tys()
                .into_iter()
                .map(&mut instantiate)
                .collect();
            let output_tys: Vec<_> = for_trait
                .output_tys()
                .into_iter()
                .map(&mut instantiate)
                .collect();
            let mut explicit_tys = input_tys.clone();
            explicit_tys.extend(output_tys.iter().copied());
            let explicit_constraints =
                named_type_constraints_in_types(explicit_tys, trait_ctx.span, &module_env);
            (input_tys, output_tys, explicit_constraints)
        });
        if let Some((explicit_input_tys, explicit_output_tys, explicit_constraints)) =
            &explicit_trait_impl
        {
            if explicit_input_tys.len() != input_tys.len() {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: input_tys.len(),
                    expected_span: trait_ctx.span,
                    got: explicit_input_tys.len(),
                    got_span: trait_ctx.span,
                }));
            }
            if !explicit_output_tys.is_empty() && explicit_output_tys.len() != output_tys.len() {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: output_tys.len(),
                    expected_span: trait_ctx.span,
                    got: explicit_output_tys.len(),
                    got_span: trait_ctx.span,
                }));
            }
            for constraint in explicit_constraints {
                ty_inf.add_pub_constraint(constraint.clone());
            }
            for (input_ty, explicit_ty) in input_tys.iter().zip(explicit_input_tys.iter()) {
                ty_inf.add_same_type_constraint(
                    *input_ty,
                    trait_ctx.span,
                    *explicit_ty,
                    trait_ctx.span,
                );
            }
            for (output_ty, explicit_ty) in output_tys.iter().zip(explicit_output_tys.iter()) {
                ty_inf.add_same_type_constraint(
                    *output_ty,
                    trait_ctx.span,
                    *explicit_ty,
                    trait_ctx.span,
                );
            }
        } else if let Some(stub_data) = trait_ctx.stub_data {
            // For a stub implementation, equate the fresh input types with the concrete types from the impl annotation.
            assert_eq!(input_tys.len(), stub_data.input_tys.len());
            for (ty_var, concrete_ty) in input_tys.iter().zip(stub_data.input_tys.iter()) {
                ty_inf.add_same_type_constraint(
                    *ty_var,
                    trait_ctx.span,
                    *concrete_ty,
                    trait_ctx.span,
                );
            }
        }
        for constraint in &trait_ctx.trait_ref.constraints {
            ty_inf.add_pub_constraint(constraint.instantiate_location_cloned(trait_ctx.span));
        }
        let mut mapper = impl_annotation_subst
            .as_ref()
            .map(BitmapInstantiationMapper::new);
        for constraint in trait_ctx.impl_constraints {
            let constraint = match &mut mapper {
                Some(m) => constraint.map(m),
                None => constraint.clone(),
            };
            ty_inf.add_pub_constraint(constraint);
        }
        Some(EmitTraitOutput {
            input_tys,
            output_tys,
            ty_var_count: 0,
            constraints: vec![],
            functions: vec![],
        })
    } else {
        None
    };
    let instantiated_trait_method_defs = match (&trait_ctx, &trait_output) {
        (Some(trait_ctx), Some(trait_output)) => Some(
            trait_ctx
                .trait_ref
                .instantiate_for_tys(&trait_output.input_tys, &trait_output.output_tys),
        ),
        _ => None,
    };

    // Populate the function table
    let mut local_fns = Vec::new();
    let mut function_annotation_ty_substs = Vec::new();
    let mut function_explicit_root_tys = Vec::new();
    for ast::ModuleFunction {
        name,
        generic_params,
        args,
        args_span,
        ret_ty,
        where_clause,
        span,
        doc,
        ..
    } in ast_functions()
    {
        // Create type and mutability variables for the arguments.
        // Note: the type quantifiers and constraints are left empty.
        // They will be filled in the second pass.
        // The effect quantifiers are filled with the output effect variable.
        if let Some(trait_ctx) = &trait_ctx {
            if let Some((_, generic_span)) = generic_params.first() {
                return Err(internal_compilation_error!(Unsupported {
                    span: *generic_span,
                    reason: format!(
                        "Explicit generic parameters on trait impl methods are not supported yet: method `{}` in impl of trait `{}`",
                        name.0, trait_ctx.trait_ref.name
                    ),
                }));
            }
            if let Some(constraint) = where_clause.first() {
                return Err(internal_compilation_error!(Unsupported {
                    span: constraint.use_site(),
                    reason: format!(
                        "Method-local where clauses on trait impl methods are not supported yet: method `{}` in impl of trait `{}`",
                        name.0, trait_ctx.trait_ref.name
                    ),
                }));
            }
        }
        let mut annotation_ty_subst = impl_annotation_subst
            .as_ref()
            .map(|subst| subst.0.clone())
            .unwrap_or_default();
        let explicit_root_tys = generic_params
            .iter()
            .enumerate()
            .map(|(index, _)| {
                let source_var = TypeVar::new((outer_annotation_var_count + index) as u32);
                let fresh_ty = ty_inf.fresh_type_var_ty();
                annotation_ty_subst.insert(source_var, fresh_ty);
                fresh_ty
            })
            .collect::<Vec<_>>();
        let args_ty = args
            .iter()
            .map(|arg| {
                if let Some((mut_ty, ty, _)) = &arg.ty {
                    let mut mapper =
                        AnnotationTypeMapper::new(&mut ty_inf, Some(&annotation_ty_subst));
                    let mut_ty = match mut_ty {
                        Some(mut_ty) => mapper.map_mut_type(*mut_ty),
                        None => MutType::constant(),
                    };
                    let ty = ty.map(&mut mapper);
                    FnArgType::new(ty, mut_ty)
                } else {
                    ty_inf.fresh_fn_arg()
                }
            })
            .collect();
        let ret_ty_ty = if let Some((ret_ty, _)) = ret_ty {
            ret_ty.map(&mut AnnotationTypeMapper::new(
                &mut ty_inf,
                Some(&annotation_ty_subst),
            ))
        } else {
            ty_inf.fresh_type_var_ty()
        };
        let annotation_subst = (annotation_ty_subst.clone(), FxHashMap::default());
        let mut mapper = BitmapInstantiationMapper::new(&annotation_subst);
        for constraint in where_clause {
            ty_inf.add_pub_constraint(constraint.map(&mut mapper));
        }
        let effects = ty_inf.fresh_effect_var_ty();
        let fn_type = FnType::new(args_ty, ret_ty_ty, effects.clone());

        // If we are emitting a trait implementation, make sure this function conforms to it.
        if let Some(trait_ctx) = &trait_ctx {
            let index = trait_ctx.trait_ref.method_index(name.0).unwrap();
            let (method_name, raw_method_def) = trait_ctx.trait_ref.method(index);
            let instantiated_method_def =
                &instantiated_trait_method_defs.as_ref().unwrap()[index.as_index()];
            if args.len() != raw_method_def.ty_scheme.ty.args.len() {
                return Err(internal_compilation_error!(TraitMethodArgCountMismatch {
                    trait_ref: trait_ctx.trait_ref.clone(),
                    method_index: index.as_index(),
                    method_name: *method_name,
                    expected: raw_method_def.ty_scheme.ty.args.len(),
                    got: args.len(),
                    args_span: *args_span,
                }));
            }
            // TODO: get span from the trait method definition, when available
            // Note: we use the variant without effects because trait impl effects are validated
            // separately after type inference (they must be a subset of trait definition effects).
            ty_inf.add_same_fn_type_constraint_without_effects(
                &fn_type,
                *span,
                &instantiated_method_def.ty_scheme.ty,
                *span,
            );
        }

        // Create dummy code.
        let arg_names: Vec<_> = args.iter().map(|arg| arg.name.0).collect();

        // Assemble the spans and the description
        let spans = ModuleFunctionSpans {
            name: name.1,
            args: args
                .iter()
                .map(DModuleFunctionArg::locations_and_ty_concreteness)
                .collect(),
            args_span: *args_span,
            ret_ty: ret_ty.map(|ret_ty| (ret_ty.1, ret_ty.0.is_constant())),
            span: *span,
        };
        let ty_scheme = TypeScheme::new_just_type(fn_type);
        let definition = FunctionDefinition::new_with_generic_params(
            ty_scheme,
            generic_params.clone(),
            arg_names,
            doc.clone(),
        );
        let descr = ModuleFunction::new_without_debug_info(
            definition,
            b(VoidFunction),
            Some(spans),
            vec![],
        );
        let id = if let Some(placeholder_ids) = trait_ctx
            .as_ref()
            .and_then(|tc| tc.stub_data.as_ref().map(|tys| &tys.method_ids))
        {
            // Reuse the pre-allocated stub slot so existing StaticApply nodes remain valid.
            let placeholder_id = placeholder_ids[local_fns.len()];
            output.functions[placeholder_id.as_index()] = descr;
            placeholder_id
        } else if trait_ctx.is_some() {
            output.add_function_anonymous(descr)
        } else {
            output.add_function(name.0, descr)
        };
        local_fns.push(id);
        function_annotation_ty_substs.push(annotation_ty_subst);
        function_explicit_root_tys.push(explicit_root_tys);
    }

    // Associated lambdas and macro to call and id and its associated lambdas
    let mut associated_lambdas: FxHashMap<LocalFunctionId, Vec<LocalFunctionId>> =
        FxHashMap::default();
    macro_rules! apply_to_function_and_associated_lambdas {
        ($id:expr, $f:expr) => {
            $f($id);
            associated_lambdas
                .get($id)
                .into_iter()
                .flatten()
                .for_each(|lambda_id| $f(lambda_id));
        };
    }
    macro_rules! try_apply_to_function_and_associated_lambdas {
        ($id:expr, $f:expr) => {
            $f($id)?;
            associated_lambdas
                .get($id)
                .into_iter()
                .flatten()
                .try_for_each(|lambda_id| $f(lambda_id))?;
        };
    }

    // Second pass, infer types and emit function bodies.
    for ((function, id), annotation_ty_subst) in ast_functions()
        .zip(local_fns.iter())
        .zip(function_annotation_ty_substs.iter())
    {
        let descr = output.get_function_by_id(*id).unwrap();
        let module_env = ModuleEnv::new(output, others);
        let mut new_import_slots = vec![];
        let mut new_type_deps = FxHashSet::default();
        let expected_ret_ty = descr.definition.ty_scheme.ty.ret;
        let expected_span = descr.spans.as_ref().unwrap().args_span;
        let mut lambda_functions = vec![];
        let mut locals = descr.gen_locals_no_bounds();
        LocalDecl::assign_sequential_slots(&mut locals);
        let cur_locals = (0..locals.len()).map(LocalDeclId::from_index).collect();
        if let Some(trait_ctx) = &trait_ctx
            && trait_ctx.trait_ref == *VALUE_TRAIT
            && trait_ctx.trait_ref.method_index(function.name.0) == Some(VALUE_CLONE_METHOD_INDEX)
        {
            locals[1].assignment_mode = LocalAssignmentMode::InitializeStorage;
        }
        let mut ty_env = TypingEnv::new(
            &mut locals,
            cur_locals,
            &mut new_import_slots,
            &mut new_type_deps,
            module_env,
            Some((expected_ret_ty, expected_span)),
            (!annotation_ty_subst.is_empty()).then_some(annotation_ty_subst),
            vec![],
            &mut lambda_functions,
            output.functions.len() as u32,
            desugared_arena,
            ir_arena,
        );
        let fn_node_id = ty_inf.check_expr(
            &mut ty_env,
            function.body,
            descr.definition.ty_scheme.ty.ret,
            MutType::constant(),
            expected_span,
        )?;
        lambda_functions.drain(..).for_each(|function| {
            let lambda_id = output.add_function_anonymous(function);
            output.name_function(
                lambda_id,
                format!("$lambda${}", lambda_id.as_index()).into(),
            );
            associated_lambdas.entry(*id).or_default().push(lambda_id);
        });
        let descr = output.get_function_by_id_mut(*id).unwrap();
        descr.definition.ty_scheme.ty.effects = ty_inf.unify_effects(
            &ir_arena[fn_node_id].effects,
            &descr.definition.ty_scheme.ty.effects,
        );
        descr.code = b(ScriptFunction::new(
            fn_node_id,
            descr.definition.arg_names.clone(),
        ));
        descr.locals = locals;
        output.import_fn_slots.extend(new_import_slots);
        output.type_deps.extend(new_type_deps);
    }
    let module_env = ModuleEnv::new(output, others);
    ty_inf.log_debug_constraints(module_env);

    // Third pass, perform the unification.
    let mut solver = trait_solver_from_module!(output, others);
    let mut ty_inf = ty_inf.unify(&mut solver, ir_arena)?;
    solver.commit(&mut output.functions, &mut output.def_table);
    let module_env = ModuleEnv::new(output, others);
    ty_inf.log_debug_substitution_tables(module_env);
    ty_inf.log_debug_constraints(module_env);

    // Helpers to de-duplicate later phases between trait and normal function emission.
    let substitute_and_canonicalize_functions =
        |output: &mut Module, ir_arena: &mut _, ty_inf: &mut UnifiedTypeInference| {
            for id in local_fns.iter() {
                apply_to_function_and_associated_lambdas!(id, |id: &LocalFunctionId| {
                    let descr = &mut output.functions[id.as_index()];
                    ty_inf.substitute_in_module_function(descr, ir_arena);
                });

                // Union duplicated effects from function arguments, and build a substitution
                // for the fully unioned effects, to remove duplications.
                let descr = &mut output.functions[id.as_index()];
                ty_inf.unify_fn_arg_effects(&descr.definition.ty_scheme.ty);
                let effect_subst: FxHashMap<_, _> = descr
                    .definition
                    .ty_scheme
                    .ty
                    .inner_effect_vars()
                    .iter()
                    .filter_map(|var| {
                        ty_inf
                            .effect_unioned(*var)
                            .map(|target| (*var, EffType::single_variable(target)))
                    })
                    .collect();
                if !effect_subst.is_empty() {
                    let subst = (FxHashMap::default(), effect_subst);
                    let mut mapper = BitmapInstantiationMapper::new(&subst);
                    apply_to_function_and_associated_lambdas!(id, |id: &LocalFunctionId| {
                        let descr = &mut output.functions[id.as_index()];
                        descr.definition.ty_scheme.ty =
                            descr.definition.ty_scheme.ty.map(&mut mapper);
                        let root = descr.get_code_entry().unwrap();
                        hir::instantiate_node_in_place(ir_arena, root, &mut mapper);
                    });
                }
            }
        };
    let borrow_check_and_elaborate_dict =
        |output: &mut Module, ir_arena: &mut _, dicts, module_inst_data, id| -> Result<_, _> {
            let mut solver = trait_solver_from_module!(output, &others);
            let mut ctx = DictElaborationCtx::new(dicts, Some(module_inst_data), &mut solver);
            try_apply_to_function_and_associated_lambdas!(id, |id: &LocalFunctionId| -> Result<
                (),
                InternalCompilationError,
            > {
                let descr = &mut output.functions[id.as_index()];
                descr.check_borrows_and_elaborate_dictionaries(ir_arena, &mut ctx)
            });
            solver.commit(&mut output.functions, &mut output.def_table);
            Ok(())
        };
    // Fourth pass: default orphan constraints and substitute types.
    if let Some(mut trait_output) = trait_output {
        // Default orphan constraints for the trait implementation into the unification tables.
        {
            let input_tys = ty_inf.substitute_in_types(&trait_output.input_tys);
            let output_tys = ty_inf.substitute_in_types(&trait_output.output_tys);
            let mut head_tys = input_tys.clone();
            head_tys.extend(output_tys.iter().copied());
            let head_quantifiers = collect_ty_vars(&head_tys);
            ty_inf.normalize_remaining_constraints();
            let head_boundary =
                ConstraintBoundary::from_seed_ty_vars(head_quantifiers.iter().copied());
            let orphan_constraints =
                head_boundary.owned_inaccessible_constraints(ty_inf.remaining_constraints());
            let scope = DefaultingScope::from_constraints(&orphan_constraints);
            let mut solver = trait_solver_from_module!(output, others);
            ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, ir_arena)?;
            solver.commit(&mut output.functions, &mut output.def_table);

            // Check for remaining orphans.
            ty_inf.normalize_remaining_constraints();
            let input_tys = ty_inf.substitute_in_types(&trait_output.input_tys);
            let output_tys = ty_inf.substitute_in_types(&trait_output.output_tys);
            let mut head_tys = input_tys.clone();
            head_tys.extend(output_tys.iter().copied());
            let head_quantifiers = collect_ty_vars(&head_tys);
            let head_boundary =
                ConstraintBoundary::from_seed_ty_vars(head_quantifiers.iter().copied());
            let remaining_orphans: Vec<_> = head_boundary
                .inaccessible_constraints(ty_inf.remaining_constraints())
                .into_iter()
                .filter(|c| !c.is_type_has_variant())
                .filter(|c| !is_compiler_provided_value_constraint(c))
                .collect();
            if !remaining_orphans.is_empty() {
                let fake_current = new_module_using_std(ModuleId(0));
                let env = ModuleEnv::new(&fake_current, others);
                return Err(internal_compilation_error!(Internal {
                    error: format!(
                        "Orphan constraints found in trait impl: {}",
                        remaining_orphans.format_with(&env)
                    ),
                    span: remaining_orphans[0].use_site(),
                }));
            }
        }

        // Substitute everything using ty_inf (single pass, includes all defaults).
        substitute_and_canonicalize_functions(output, ir_arena, &mut ty_inf);
        default_output_effects_in_functions(output, ir_arena, &associated_lambdas, &local_fns);

        // Resolve input and output types.
        ty_inf.substitute_in_types_in_place(&mut trait_output.input_tys);
        ty_inf.substitute_in_types_in_place(&mut trait_output.output_tys);

        // Take final substituted constraints.
        ty_inf.normalize_remaining_constraints();
        let all_constraints = ty_inf.take_constraints();

        // Validate that each method's effects are a subset of the trait definition's effects,
        // and override them with the trait's effects.
        // This ensures ABI consistency: the calling convention is determined by the trait definition.
        let trait_ref = &trait_ctx.unwrap().trait_ref;
        for (i, id) in local_fns.iter().enumerate() {
            let i = TraitMethodIndex::from_index(i);
            let descr = &mut output.functions[id.as_index()];
            let (method_name, trait_method_def) = trait_ref.method(i);
            let trait_effects = &trait_method_def.ty_scheme.ty.effects;
            let impl_effects = &descr.definition.ty_scheme.ty.effects;

            // Check that impl effects are a subset of trait effects.
            if !impl_effects.is_subset_of(trait_effects) {
                let span = descr.spans.as_ref().unwrap().span;
                return Err(internal_compilation_error!(TraitMethodEffectMismatch {
                    trait_ref: trait_ref.clone(),
                    method_name: *method_name,
                    expected: trait_effects.clone(),
                    got: impl_effects.clone(),
                    span,
                }));
            }

            // Override the function's effects with the trait's effects for ABI consistency.
            descr.definition.ty_scheme.ty.effects = trait_effects.clone();
        }

        // Store the functions in the trait output.
        trait_output.functions = local_fns.clone();

        // Compute quantifiers from input types and constraints.
        let mut head_tys = trait_output.input_tys.clone();
        head_tys.extend(trait_output.output_tys.iter().copied());
        let input_quantifiers = collect_ty_vars(&head_tys);
        let head_boundary =
            ConstraintBoundary::from_seed_ty_vars(input_quantifiers.iter().copied());
        let related_constraints = head_boundary.accessible_constraints(&all_constraints);
        let mut quantifiers = input_quantifiers.to_vec();
        let mut collector = TyVarsCollector(&mut quantifiers);
        for constraint in related_constraints.iter() {
            constraint.visit(&mut collector);
        }
        quantifiers = quantifiers.into_iter().unique().collect();

        // Detect unbound type variables in the code and return error if not in unused variants only.
        let mut unbound_subst = FxHashMap::default();
        for id in local_fns.iter() {
            let descr = &mut output.functions[id.as_index()];
            let root = descr.get_code_entry().unwrap();
            let unbound = hir::all_unbound_ty_vars(ir_arena, root);
            let uninstantiated_unbound = check_unbounds(unbound, &quantifiers)?;
            unbound_subst.extend(
                uninstantiated_unbound
                    .into_iter()
                    .map(|ty_var| (ty_var, Type::never())),
            );
        }

        // Update quantifiers and constraints with unbound substitution.
        quantifiers.retain(|ty_var| !unbound_subst.contains_key(ty_var));
        trait_output.ty_var_count = quantifiers.len() as u32;
        let mut subst = (unbound_subst, FxHashMap::default());
        let subst_size = subst.0.len();
        let mut solver = trait_solver_from_module!(output, others);
        trait_output.constraints = all_constraints
            .iter()
            .filter_map(|constraint| {
                constraint
                    .instantiate_and_drop_if_solved(&mut subst, &mut solver, ir_arena)
                    .transpose()
            })
            .collect::<Result<_, _>>()?;
        solver.commit(&mut output.functions, &mut output.def_table);
        // Make sure substitution is not due to constraint processing.
        assert_eq!(subst_size, subst.0.len());
        let dicts = extra_parameters_from_constraints(&trait_output.constraints);

        // Apply unbound substitution to code and types.
        if !subst.0.is_empty() {
            let mut mapper = BitmapInstantiationMapper::new(&subst);
            instantiate_types_in_place(&mut trait_output.input_tys, &mut mapper);
            instantiate_types_in_place(&mut trait_output.output_tys, &mut mapper);
            for id in local_fns.iter() {
                apply_to_function_and_associated_lambdas!(id, |id: &LocalFunctionId| {
                    let descr = &mut output.functions[id.as_index()];
                    descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
                    instantiate_function_descr_in_place(ir_arena, descr, &mut mapper);
                });
            }
        }

        // Fifth pass, run the borrow checker and elaborate dictionaries.
        let mut module_inst_data = FxHashMap::default();
        for id in local_fns.iter() {
            insert_inst_data_for_function_and_lambdas(
                &mut module_inst_data,
                &associated_lambdas,
                *id,
                dicts.clone(),
            );
        }
        for id in local_fns.iter() {
            borrow_check_and_elaborate_dict(output, ir_arena, &dicts, &module_inst_data, id)?;
        }

        // Sixth pass, normalize the input types, substitute the types in the functions and input/output types.
        let subst = (normalize_types(&mut quantifiers), FxHashMap::default());
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        instantiate_types_in_place(&mut trait_output.input_tys, &mut mapper);
        instantiate_types_in_place(&mut trait_output.output_tys, &mut mapper);
        instantiate_types_in_place(&mut trait_output.constraints, &mut mapper);
        for (method_index, id) in local_fns.iter().enumerate() {
            let method_index = TraitMethodIndex::from_index(method_index);
            apply_to_function_and_associated_lambdas!(id, |id: &LocalFunctionId| {
                let descr = &mut output.functions[id.as_index()];
                descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
                descr.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
                let eff_quantifiers = descr.definition.ty_scheme.ty.input_effect_vars();
                assert!(eff_quantifiers.is_empty());
                descr.definition.ty_scheme.eff_quantifiers = eff_quantifiers;
                descr.definition.ty_scheme.constraints = trait_output.constraints.clone();
                instantiate_function_descr_in_place(ir_arena, descr, &mut mapper);
            });

            // Name the function
            let name = trait_ref
                .qualified_method_name(method_index, &trait_output.input_tys)
                .into();
            output.name_function(*id, name);
        }

        refresh_debug_info_for_functions(output, &associated_lambdas, &local_fns);
        Ok(Some(trait_output))
    } else {
        // We are emitting normal module functions.

        // Default orphan constraints for each function into the unification tables.
        for (id, explicit_root_tys) in local_fns.iter().zip(function_explicit_root_tys.iter()) {
            let descr = &output.functions[id.as_index()];
            let fn_ty = ty_inf.substitute_in_fn_type(&descr.definition.ty_scheme.ty);
            let mut sig_ty_vars = fn_ty.inner_ty_vars();
            sig_ty_vars.extend(
                explicit_root_tys
                    .iter()
                    .flat_map(|ty| ty_inf.substitute_in_type(*ty).inner_ty_vars().into_iter())
                    .collect::<Vec<_>>(),
            );
            sig_ty_vars = sig_ty_vars.into_iter().unique().collect();
            ty_inf.normalize_remaining_constraints();
            let sig_boundary = ConstraintBoundary::from_seed_ty_vars(sig_ty_vars.iter().copied());
            let orphan_constraints =
                sig_boundary.owned_inaccessible_constraints(ty_inf.remaining_constraints());
            let mut solver = trait_solver_from_module!(output, others);
            // If the signature still exposes type variables, it defines the boundary for
            // defaulting and body-local `None`/unit evidence must not bias it.
            // Only functions with no remaining signature boundary can use their body root
            // to seed the narrow unit-constructor fallback.
            let unit_variant_seed_tys = if sig_ty_vars.is_empty() {
                descr
                    .get_code_entry()
                    .map(|root_node| {
                        UnifiedTypeInference::collect_unit_variant_seed_types(ir_arena, root_node)
                    })
                    .unwrap_or_default()
            } else {
                Vec::new()
            };
            let scope = DefaultingScope::from_constraints(&orphan_constraints)
                .with_unit_variant_seed_tys(unit_variant_seed_tys);
            ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, ir_arena)?;
            solver.commit(&mut output.functions, &mut output.def_table);
        }
        for (id, explicit_root_tys) in local_fns.iter().zip(function_explicit_root_tys.iter()) {
            let descr = &output.functions[id.as_index()];
            let fn_ty = ty_inf.substitute_in_fn_type(&descr.definition.ty_scheme.ty);
            let mut sig_ty_vars = fn_ty.inner_ty_vars();
            sig_ty_vars.extend(
                explicit_root_tys
                    .iter()
                    .flat_map(|ty| ty_inf.substitute_in_type(*ty).inner_ty_vars().into_iter())
                    .collect::<Vec<_>>(),
            );
            sig_ty_vars = sig_ty_vars.into_iter().unique().collect();
            ty_inf.normalize_remaining_constraints();
            let sig_boundary = ConstraintBoundary::from_seed_ty_vars(sig_ty_vars.iter().copied());
            let remaining_orphans: Vec<_> = sig_boundary
                .inaccessible_constraints(ty_inf.remaining_constraints())
                .into_iter()
                .filter(|c| !c.is_type_has_variant())
                .filter(|c| !is_compiler_provided_value_constraint(c))
                .collect();
            if !remaining_orphans.is_empty() {
                let fake_current = new_module_using_std(ModuleId(0));
                let env = ModuleEnv::new(&fake_current, others);
                return Err(internal_compilation_error!(Internal {
                    error: format!(
                        "Orphan constraints found in module fn: {}",
                        remaining_orphans.format_with(&env)
                    ),
                    span: remaining_orphans[0].use_site(),
                }));
            }
        }

        // Substitute everything using ty_inf (single pass, includes all defaults).
        substitute_and_canonicalize_functions(output, ir_arena, &mut ty_inf);

        // Take final substituted constraints.
        ty_inf.normalize_remaining_constraints();
        let all_constraints = ty_inf.take_constraints();

        // For each function: filter constraints, check unbounds, finalize type scheme.
        let mut used_constraints: FxHashSet<PubTypeConstraintPtr> = FxHashSet::default();
        for ((function, id), explicit_root_tys) in ast_functions()
            .zip(local_fns.iter())
            .zip(function_explicit_root_tys.iter())
        {
            let descr = &output.functions[id.as_index()];
            let code_entry = descr.get_code_entry().unwrap();

            // Find constraints related to this function's signature.
            let mut sig_ty_vars = descr.definition.ty_scheme.ty.inner_ty_vars();
            let explicit_ty_vars = explicit_root_tys
                .iter()
                .flat_map(|ty| ty_inf.substitute_in_type(*ty).inner_ty_vars().into_iter())
                .collect::<Vec<_>>();
            sig_ty_vars.extend(explicit_ty_vars.iter().copied());
            sig_ty_vars = sig_ty_vars.into_iter().unique().collect();
            let sig_boundary = ConstraintBoundary::from_seed_ty_vars(sig_ty_vars.iter().copied());
            let related_constraints = sig_boundary.accessible_constraints(&all_constraints);
            let related_ptrs: FxHashSet<PubTypeConstraintPtr> = related_constraints
                .iter()
                .map(|c| constraint_ptr(c))
                .collect();
            for ptr in &related_ptrs {
                used_constraints.insert(*ptr);
            }

            // Compute quantifiers.
            let mut quantifiers = TypeScheme::list_ty_vars(
                &descr.definition.ty_scheme.ty,
                related_constraints.iter().copied(),
            );
            quantifiers.extend(explicit_ty_vars.iter().copied());
            quantifiers = quantifiers.into_iter().unique().collect();

            // Check for unbound type variables.
            let unbound = hir::all_unbound_ty_vars(ir_arena, code_entry);
            let uninstantiated_unbound = check_unbounds(unbound, &quantifiers)?;

            // Apply unbound→Never fixup if needed.
            if !uninstantiated_unbound.is_empty() {
                let fixup_subst: (TypeInstSubst, FxHashMap<_, _>) = (
                    uninstantiated_unbound
                        .iter()
                        .map(|v| (*v, Type::never()))
                        .collect(),
                    FxHashMap::default(),
                );
                let mut mapper = BitmapInstantiationMapper::new(&fixup_subst);
                apply_to_function_and_associated_lambdas!(id, |id: &LocalFunctionId| {
                    let descr = &mut output.functions[id.as_index()];
                    instantiate_function_descr_in_place(ir_arena, descr, &mut mapper);
                });
                quantifiers.retain(|v| !uninstantiated_unbound.contains(v));
            }

            // Filter and finalize constraints.
            let mut solver = trait_solver_from_module!(output, others);
            let mut drop_subst = (FxHashMap::default(), FxHashMap::default());
            let constraints: Vec<_> = all_constraints
                .iter()
                .filter(|c| related_ptrs.contains(&constraint_ptr(c)))
                .filter_map(|constraint| {
                    constraint
                        .instantiate_and_drop_if_solved(&mut drop_subst, &mut solver, ir_arena)
                        .transpose()
                })
                .collect::<Result<_, _>>()?;
            solver.commit(&mut output.functions, &mut output.def_table);

            // Write the final type scheme.
            let explicit_ty_vars = explicit_ty_vars
                .iter()
                .copied()
                .unique()
                .collect::<Vec<_>>();
            quantifiers = explicit_ty_vars
                .iter()
                .copied()
                .chain(
                    quantifiers
                        .into_iter()
                        .filter(|ty_var| !explicit_ty_vars.contains(ty_var)),
                )
                .collect();
            apply_to_function_and_associated_lambdas!(id, |id: &LocalFunctionId| {
                let descr = &mut output.functions[id.as_index()];
                descr.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
                descr.definition.ty_scheme.eff_quantifiers =
                    descr.definition.ty_scheme.ty.input_effect_vars();
                descr.definition.ty_scheme.constraints = constraints.clone();
                descr.definition.generic_params = function.generic_params.clone();
            });

            // Log dropped constraints.
            if log_enabled!(log::Level::Debug) {
                let module_env = ModuleEnv::new(output, others);
                let retained_ptrs: FxHashSet<PubTypeConstraintPtr> =
                    constraints.iter().map(constraint_ptr).collect();
                log_dropped_constraints_module(
                    function.name.0,
                    &all_constraints,
                    &related_ptrs,
                    &retained_ptrs,
                    module_env,
                );
            }
        }

        // Safety check: make sure that there are no unused constraints.
        let unused_constraints = all_constraints
            .iter()
            .filter(|c| {
                !used_constraints.contains(&constraint_ptr(c))
                    && !c.is_type_has_variant()
                    && !is_compiler_provided_value_constraint(c)
            })
            .collect::<Vec<_>>();
        if !unused_constraints.is_empty() {
            let module_env = ModuleEnv::new(output, others);
            let constraints = unused_constraints
                .iter()
                .map(|c| c.format_with(&module_env))
                .join(" ∧ ");
            return Err(internal_compilation_error!(Internal {
                error: format!("Unused constraints in module compilation: {}", constraints),
                span: unused_constraints[0].use_site(),
            }));
        }

        // Fifth pass, run the borrow checker and elaborate dictionaries.
        let mut module_inst_data = FxHashMap::default();
        for id in local_fns.iter() {
            let descr = &output.functions[id.as_index()];
            let dicts = descr.definition.ty_scheme.extra_parameters();
            insert_inst_data_for_function_and_lambdas(
                &mut module_inst_data,
                &associated_lambdas,
                *id,
                dicts,
            );
        }
        for id in local_fns.iter() {
            let dicts = module_inst_data.get(id).unwrap();
            borrow_check_and_elaborate_dict(output, ir_arena, dicts, &module_inst_data, id)?;
        }

        // Sixth pass, normalize the type schemes, substitute the types in the functions.
        for id in local_fns.iter() {
            apply_to_function_and_associated_lambdas!(id, |id: &LocalFunctionId| {
                let descr = &mut output.functions[id.as_index()];
                // Note: after that normalization, the functions do not share the same
                // type variables anymore.
                let subst = descr.definition.ty_scheme.normalize();
                let mut mapper = BitmapInstantiationMapper::new(&subst);
                instantiate_function_descr_in_place(ir_arena, descr, &mut mapper);
            });
        }

        refresh_debug_info_for_functions(output, &associated_lambdas, &local_fns);
        Ok(None)
    }
}

/// Check all unbound variables from unbound that are not in bounds,
/// and if they are not only seen in variants, return an error.
fn check_unbounds(
    unbound: IndexMap<TypeVar, hir::UnboundTyCtxs>,
    bounds: &[TypeVar],
) -> Result<FxHashSet<TypeVar>, InternalCompilationError> {
    let mut uninstantiated_unbound = FxHashSet::default();
    for (ty_var, ctxs) in unbound {
        if !bounds.contains(&ty_var) {
            if ctxs.seen_only_in_variants(ty_var) {
                uninstantiated_unbound.insert(ty_var);
            } else {
                let (ty, span) = ctxs.first();
                return Err(internal_compilation_error!(UnboundTypeVar {
                    ty_var,
                    ty,
                    span
                }));
            }
        }
    }
    Ok(uninstantiated_unbound)
}

/// A compiled expression
#[derive(Debug)]
pub struct CompiledExpr {
    pub expr: hir::NodeId,
    pub ty: TypeScheme<Type>,
    pub locals: Vec<LocalDecl>,
}

/// Emit HIR for an expression.
/// Return the compiled expression and any remaining external constraints
/// referring to lower-generation type variables.
/// Note: the expression might not be safe to use if it has unbound constraints or type variables.
pub fn emit_expr_unsafe(
    source: PExprId,
    parsed_arena: &PExprArena,
    module: &mut Module,
    others: &Modules,
    locals: Vec<LocalDecl>,
) -> Result<CompiledExpr, InternalCompilationError> {
    // Take the module's node arena out for compilation, then restore it unconditionally.
    let mut ir_arena = std::mem::take(&mut module.ir_arena);
    let result =
        emit_expr_unsafe_inner(source, parsed_arena, module, others, locals, &mut ir_arena);
    module.ir_arena = ir_arena;
    result
}

fn emit_expr_unsafe_inner(
    source: PExprId,
    parsed_arena: &PExprArena,
    module: &mut Module,
    others: &Modules,
    mut locals: Vec<LocalDecl>,
    ir_arena: &mut NodeArena,
) -> Result<CompiledExpr, InternalCompilationError> {
    // Make sure that the locals' types have no type variables in them
    assert!(
        locals
            .iter()
            .all(|local| local.ty.inner_ty_vars().is_empty()),
        "Locals passed to expression compilation must not contain type variables"
    );

    // Create a list of all available trait implementations.
    let module_env = ModuleEnv::new(module, others);

    // First desugar the expression.
    let mut modules_used = FxHashSet::default();
    let (source, desugared_arena) =
        desugar_expr_with_empty_ctx(source, parsed_arena, &module_env, &mut modules_used)?;

    // Infer the expression with the existing locals.
    let initial_local_count = locals.len();
    let mut new_import_slots = vec![];
    let mut new_type_deps = FxHashSet::default();
    let mut lambda_functions = vec![];
    LocalDecl::assign_sequential_slots(&mut locals);
    let cur_locals = (0..locals.len()).map(LocalDeclId::from_index).collect();
    let mut ty_env = TypingEnv::new(
        &mut locals,
        cur_locals,
        &mut new_import_slots,
        &mut new_type_deps,
        module_env,
        None,
        None,
        vec![],
        &mut lambda_functions,
        module.functions.len() as u32,
        &desugared_arena,
        ir_arena,
    );
    let mut ty_inf = TypeInference::new_empty();
    let (node_id, _) = ty_inf.infer_expr(&mut ty_env, source)?;
    let mut locals = mem::take(&mut locals);
    ty_inf.log_debug_constraints(module_env);
    let lambda_functions = lambda_functions
        .drain(..)
        .map(|function| {
            let id = module.add_function_anonymous(function);
            module.name_function(id, format!("$lambda${}", id.as_index()).into());
            id
        })
        .collect::<Vec<_>>();
    module.import_fn_slots.extend(new_import_slots);
    module.type_deps.extend(new_type_deps);
    module.type_deps.extend(modules_used);

    // Perform the unification.
    let mut solver = trait_solver_from_module!(module, others);
    let mut ty_inf = ty_inf.unify(&mut solver, ir_arena)?;
    solver.commit(&mut module.functions, &mut module.def_table);
    let module_env = ModuleEnv::new(module, others);
    ty_inf.log_debug_substitution_tables(module_env);
    ty_inf.log_debug_constraints(module_env);

    // Default constraints into the unification tables (pre-substitution).
    // For expressions, iterate defaulting and re-solving to a fixed point.
    {
        let node_ty = ty_inf.substitute_in_type(ir_arena[node_id].ty);
        let mut solver = trait_solver_from_module!(module, others);
        let orphan_constraints = ty_inf.remaining_constraints().to_vec();
        let unit_variant_seed_tys =
            UnifiedTypeInference::collect_unit_variant_seed_types(ir_arena, node_id);
        let scope = DefaultingScope::from_constraints(&orphan_constraints)
            .with_expr_root_ty(node_ty)
            .with_unit_variant_seed_tys(unit_variant_seed_tys);
        ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, ir_arena)?;
        solver.commit(&mut module.functions, &mut module.def_table);
    }

    // Substitute everything using ty_inf (single pass, includes all defaults).
    ty_inf.substitute_in_node(ir_arena, node_id);
    for lambda_id in lambda_functions.iter() {
        let descr = module.get_function_by_id_mut(*lambda_id).unwrap();
        ty_inf.substitute_in_module_function(descr, ir_arena);
    }
    ty_inf.substitute_in_local_decls_in_place(&mut locals[initial_local_count..]);

    // Take final substituted constraints.
    let module_env = ModuleEnv::new(module, others);
    ty_inf.log_debug_constraints(module_env);
    ty_inf.normalize_remaining_constraints();
    let all_constraints = ty_inf.take_constraints();

    // Compute quantifiers from the node type and remaining constraints.
    let node_ty = ir_arena[node_id].ty;
    let mut quantifiers = TypeScheme::list_ty_vars(&node_ty, all_constraints.iter());

    // Check for unbound type variables.
    let unbound = hir::all_unbound_ty_vars(ir_arena, node_id);
    let uninstantiated_unbound = check_unbounds(unbound, &quantifiers)?;

    // Apply unbound→Never fixup if needed.
    let fixup_subst: (TypeInstSubst, FxHashMap<_, _>) = (
        uninstantiated_unbound
            .iter()
            .map(|v| (*v, Type::never()))
            .collect(),
        FxHashMap::default(),
    );
    if !fixup_subst.0.is_empty() {
        let mut mapper = BitmapInstantiationMapper::new(&fixup_subst);
        hir::instantiate_node_in_place(ir_arena, node_id, &mut mapper);
        for lambda_id in lambda_functions.iter() {
            let descr = &mut module.functions[lambda_id.as_index()];
            descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
            let root = descr.get_code_entry().unwrap();
            hir::instantiate_node_in_place(ir_arena, root, &mut mapper);
            for local in &mut descr.locals {
                local.ty = local.ty.map(&mut mapper);
            }
        }
        for local in locals.iter_mut().skip(initial_local_count) {
            local.ty = local.ty.map(&mut mapper);
        }
        quantifiers.retain(|v| !uninstantiated_unbound.contains(v));
    }

    // Filter solved constraints.
    let mut solver = trait_solver_from_module!(module, others);
    let mut drop_subst = (FxHashMap::default(), FxHashMap::default());
    let mut constraints: Vec<_> = all_constraints
        .iter()
        .filter_map(|constraint| {
            constraint
                .instantiate_and_drop_if_solved(&mut drop_subst, &mut solver, ir_arena)
                .transpose()
        })
        .collect::<Result<_, _>>()?;
    // Loop to drop constraints that become solved due to output type resolution.
    let mut progress = true;
    while progress {
        progress = false;
        let mut new_constraints = Vec::new();
        for constraint in constraints.iter() {
            if let Some(new_constraint) =
                constraint.instantiate_and_drop_if_solved(&mut drop_subst, &mut solver, ir_arena)?
            {
                new_constraints.push(new_constraint);
            } else {
                progress = true;
            }
        }
        constraints = new_constraints;
    }
    quantifiers.retain(|ty_var| !drop_subst.0.contains_key(ty_var));
    if !drop_subst.0.is_empty() {
        let mut mapper = BitmapInstantiationMapper::new(&drop_subst);
        hir::instantiate_node_in_place(ir_arena, node_id, &mut mapper);
        for lambda_id in lambda_functions.iter() {
            let descr = &mut module.functions[lambda_id.as_index()];
            descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
            let root = descr.get_code_entry().unwrap();
            hir::instantiate_node_in_place(ir_arena, root, &mut mapper);
            for local in &mut descr.locals {
                local.ty = local.ty.map(&mut mapper);
            }
        }
        for local in locals.iter_mut().skip(initial_local_count) {
            local.ty = local.ty.map(&mut mapper);
        }
    }
    for lambda_id in lambda_functions.iter() {
        let descr = &mut module.functions[lambda_id.as_index()];
        descr.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
        descr.definition.ty_scheme.eff_quantifiers =
            descr.definition.ty_scheme.ty.input_effect_vars();
        descr.definition.ty_scheme.constraints = constraints.clone();
    }
    solver.commit(&mut module.functions, &mut module.def_table);

    // Log dropped constraints.
    if log_enabled!(log::Level::Debug) {
        let module_env = ModuleEnv::new(module, others);
        let retained_ptrs: FxHashSet<PubTypeConstraintPtr> =
            constraints.iter().map(constraint_ptr).collect();
        log_dropped_constraints_expr(&all_constraints, &retained_ptrs, module_env);
    }

    // Normalize the type scheme.
    let node_ty = ir_arena[node_id].ty;
    let mut ty_scheme = TypeScheme {
        ty: node_ty,
        eff_quantifiers: node_ty.inner_effect_vars(),
        ty_quantifiers: quantifiers,
        constraints,
    };
    let mut subst = ty_scheme.normalize();

    // Remove output effects of the expression (i.e. not in the type of the expression).
    for effect in ir_arena[node_id].effects.iter() {
        if let Some(var) = effect.as_variable() {
            if !subst.1.contains_key(var) {
                subst.1.insert(*var, EffType::empty());
            }
        }
    }

    // Substitute the normalized types in the node, effects and locals.
    let mut mapper = BitmapInstantiationMapper::new(&subst);
    hir::instantiate_node_in_place(ir_arena, node_id, &mut mapper);
    for lambda_id in lambda_functions.iter() {
        let descr = &mut module.functions[lambda_id.as_index()];
        descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
        let root = descr.get_code_entry().unwrap();
        hir::instantiate_node_in_place(ir_arena, root, &mut mapper);
        for local in &mut descr.locals {
            local.ty = local.ty.map(&mut mapper);
        }
    }
    ty_scheme.ty = ty_scheme.ty.map(&mut mapper);
    for local in locals.iter_mut().skip(initial_local_count) {
        local.ty = local.ty.map(&mut mapper);
    }
    drop(mapper);

    // Do borrow checking and dictionary elaboration.
    let dicts = ty_scheme.extra_parameters();
    let mut solver = trait_solver_from_module!(module, &others);
    let mut ctx = DictElaborationCtx::new(&dicts, None, &mut solver);
    check_borrows(ir_arena, node_id)?;
    let local_count = locals.len();
    elaborate_local_value_dispatches(ir_arena, &mut locals, &mut ctx)?;
    elaborate_dictionaries(ir_arena, node_id, &mut ctx, local_count)?;
    for lambda_id in lambda_functions.iter() {
        let descr = &mut module.functions[lambda_id.as_index()];
        descr.check_borrows_and_elaborate_dictionaries(ir_arena, &mut ctx)?;
    }
    solver.commit(&mut module.functions, &mut module.def_table);
    assert_eq!(locals.len(), local_count);
    for lambda_id in lambda_functions {
        module.functions[lambda_id.as_index()].refresh_debug_info();
    }

    Ok(CompiledExpr {
        expr: node_id,
        ty: ty_scheme,
        locals,
    })
}

/// Emit HIR for an expression, and fails if there are any unbound type variables or constraints.
/// If the expression imports functions from the Program, module's imports will be updated.
pub fn emit_expr(
    source: PExprId,
    parsed_arena: &PExprArena,
    module: &mut Module,
    others: &Modules,
    locals: Vec<LocalDecl>,
) -> Result<CompiledExpr, InternalCompilationError> {
    let span = parsed_arena[source].span;
    let CompiledExpr { ty, expr, locals } =
        emit_expr_unsafe(source, parsed_arena, module, others, locals)?;
    let ty_vars = ty.ty.inner_ty_vars();
    if !ty_vars.is_empty() {
        return Err(internal_compilation_error!(UnboundTypeVar {
            ty_var: ty_vars[0],
            ty: ty.ty,
            span,
        }));
    }
    if let Some((ty_var, ty, span)) = first_unbound_type_in_constraints(&ty.constraints) {
        return Err(internal_compilation_error!(UnboundTypeVar {
            ty_var,
            ty,
            span
        }));
    }
    if !ty.constraints.is_empty() {
        return Err(internal_compilation_error!(UnresolvedConstraints {
            constraints: ty.constraints.clone(),
            span,
        }));
    }
    Ok(CompiledExpr { ty, expr, locals })
}

fn first_unbound_type_in_constraints(
    constraints: &[PubTypeConstraint],
) -> Option<(TypeVar, Type, Location)> {
    fn in_type(ty: Type, span: Location) -> Option<(TypeVar, Type, Location)> {
        ty.inner_ty_vars().first().map(|ty_var| (*ty_var, ty, span))
    }

    for constraint in constraints {
        let span = constraint.use_site();
        match constraint {
            PubTypeConstraint::TupleAtIndexIs {
                tuple_ty,
                element_ty,
                ..
            } => {
                if let Some(unbound) = in_type(*tuple_ty, span) {
                    return Some(unbound);
                }
                if let Some(unbound) = in_type(*element_ty, span) {
                    return Some(unbound);
                }
            }
            PubTypeConstraint::RecordFieldIs {
                record_ty,
                element_ty,
                ..
            } => {
                if let Some(unbound) = in_type(*record_ty, span) {
                    return Some(unbound);
                }
                if let Some(unbound) = in_type(*element_ty, span) {
                    return Some(unbound);
                }
            }
            PubTypeConstraint::TypeHasVariant {
                variant_ty,
                payload_ty,
                ..
            } => {
                if let Some(unbound) = in_type(*variant_ty, span) {
                    return Some(unbound);
                }
                if let Some(unbound) = in_type(*payload_ty, span) {
                    return Some(unbound);
                }
            }
            PubTypeConstraint::HaveTrait {
                input_tys,
                output_tys,
                ..
            } => {
                for ty in input_tys.iter().chain(output_tys) {
                    if let Some(unbound) = in_type(*ty, span) {
                        return Some(unbound);
                    }
                }
            }
        }
    }
    None
}

type PubTypeConstraintPtr = *const PubTypeConstraint;

fn constraint_ptr(c: &PubTypeConstraint) -> PubTypeConstraintPtr {
    c as *const PubTypeConstraint
}

fn is_compiler_provided_value_constraint(c: &PubTypeConstraint) -> bool {
    match c {
        PubTypeConstraint::HaveTrait {
            trait_ref,
            input_tys,
            output_tys,
            ..
        } => {
            is_value_trait_for_function_type(trait_ref, input_tys, output_tys)
                || is_function_surface_only_value_trait_application(
                    trait_ref, input_tys, output_tys,
                )
        }
        _ => false,
    }
}

fn log_dropped_constraints_expr(
    all: &[PubTypeConstraint],
    retained: &FxHashSet<PubTypeConstraintPtr>,
    module_env: ModuleEnv,
) {
    if retained.len() == all.len() {
        return;
    }
    let dropped = all
        .iter()
        .filter(|c| {
            let ptr = constraint_ptr(c);
            !retained.contains(&ptr)
        })
        .map(|c| c.format_with(&module_env));
    let dropped = iterable_to_string(dropped, " ∧ ");
    log::debug!("Dropped/resolved constraints in expr: {dropped}");
}

fn log_dropped_constraints_module(
    ctx: Ustr,
    all: &[PubTypeConstraint],
    related: &FxHashSet<PubTypeConstraintPtr>,
    retained: &FxHashSet<PubTypeConstraintPtr>,
    module_env: ModuleEnv,
) {
    if retained.len() == related.len() {
        return;
    }
    let dropped = all
        .iter()
        .filter(|c| {
            let ptr = constraint_ptr(c);
            related.contains(&ptr) && !retained.contains(&ptr)
        })
        .map(|c| c.format_with(&module_env));
    let dropped = iterable_to_string(dropped, " ∧ ");
    log::debug!("Dropped/resolved constraints in {ctx}: {dropped}");
}
