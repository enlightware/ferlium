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
        borrow_checker::check_borrows,
        emit_associated_consts::{
            SourceAssociatedConstImpl, associated_const_values_for_source_impl,
        },
        function::VoidFunction,
    },
    module::Uses,
    types::r#trait::TraitMethodIndex,
};

use indexmap::IndexMap;
use itertools::Itertools;
use log::log_enabled;
use ustr::{Ustr, ustr};

use super::emit_value_impl::emit_auto_value_impls;

use crate::{
    Location,
    ast::{self, *},
    compiler::error::{
        AttributeTarget, InternalCompilationError, InvalidAttributeKind, UnsafeFeature,
    },
    containers::{SVec2, b, iterable_to_string},
    desugar::desugar_expr_with_empty_ctx,
    format::FormatWith,
    hir::function::{FunctionDefinition, PendingScriptFunction},
    hir::{self, NodeArena, UNodeArena},
    hir::{
        dictionary::{DictElaborationCtx, ExtraParameters},
        elaboration::{elaborate_generated_functions, elaborate_hir},
        value_dispatch::elaborate_local_ownership_and_value_dispatches,
    },
    internal_compilation_error,
    module::{
        ConcreteTraitImplKey, ELocalDecl, FunctionId, GENERATED_LAMBDA_PREFIX, LocalAssignmentMode,
        LocalDecl, LocalDeclId, LocalFunctionId, LocalImplId, Module, ModuleEnv, ModuleFunction,
        ModuleFunctionSpans, ModuleId, PendingModuleFunction, TraitId, TraitImpl, UModuleFunction,
        build_dictionary_value, id::Id,
    },
    std::{
        STD_MODULE_ID, new_module_using_std,
        value::{
            VALUE_CLONE_METHOD_INDEX, is_function_surface_only_value_trait_application,
            is_value_trait, is_value_trait_for_function_type,
        },
    },
    types::coherence::check_trait_impl,
    types::effects::{EffType, PrimitiveEffect, effect},
    types::mutability::MutType,
    types::r#trait::Trait,
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
    if let Some(lambda_ids) = associated_lambdas.get(&id) {
        for lambda_id in lambda_ids {
            module_inst_data.insert(*lambda_id, dicts.clone());
        }
    }
    module_inst_data.insert(id, dicts);
}

fn function_and_associated_lambdas<'a>(
    id: &'a LocalFunctionId,
    associated_lambdas: &'a FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
) -> impl Iterator<Item = LocalFunctionId> + 'a {
    std::iter::once(*id).chain(associated_lambdas.get(id).into_iter().flatten().copied())
}

type PendingModuleFunctions = FxHashMap<LocalFunctionId, PendingModuleFunction>;

fn add_pending_function_anonymous(
    module: &mut Module,
    pending_functions: &mut PendingModuleFunctions,
    function: UModuleFunction,
) -> LocalFunctionId {
    let id = module.add_function_anonymous(function.placeholder());
    pending_functions.insert(id, function);
    id
}

fn set_pending_function(
    module: &mut Module,
    pending_functions: &mut PendingModuleFunctions,
    id: LocalFunctionId,
    function: UModuleFunction,
) {
    module.functions[id.as_index()] = function.placeholder();
    pending_functions.insert(id, function);
}

/// Data for a pre-registered stub implementation for `impl Trait for ConcreteType`.
struct ImplStubData {
    id: LocalImplId,
    input_tys: Vec<Type>,
    method_ids: Vec<LocalFunctionId>,
}

fn instantiate_function_descr_in_place<M: TypeMapper>(
    ir_arena: &mut NodeArena,
    descr: &mut UModuleFunction,
    mapper: &mut M,
) {
    hir::instantiate_node_in_place(ir_arena, descr.code.entry_node_id, mapper);
    for local in &mut descr.locals {
        local.ty = local.ty.map(mapper);
    }
}

fn borrow_check_and_elaborate_pending_function(
    function_slot: &mut ModuleFunction,
    dst_arena: &mut hir::ENodeArena,
    ir_arena: &mut NodeArena,
    pending_functions: &mut PendingModuleFunctions,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    id: LocalFunctionId,
) -> Result<(), InternalCompilationError> {
    let mut function = pending_functions
        .remove(&id)
        .expect("expected pending function body");
    function.definition = function_slot.definition.clone();
    function.spans = function_slot.spans.clone();
    let (elaborated, _) = function.check_borrows_and_elaborate_hir(ir_arena, dst_arena, ctx)?;
    *function_slot = elaborated;
    Ok(())
}

fn refresh_debug_info_for_functions(
    output: &mut Module,
    associated_lambdas: &FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    local_fns: &[LocalFunctionId],
) {
    for id in local_fns {
        for function_id in function_and_associated_lambdas(id, associated_lambdas) {
            output.functions[function_id.as_index()].refresh_debug_info();
        }
    }
}

fn default_output_effects_in_functions(
    output: &mut Module,
    ir_arena: &mut NodeArena,
    pending_functions: &mut PendingModuleFunctions,
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
        for function_id in function_and_associated_lambdas(&id, associated_lambdas) {
            let descr = &mut output.functions[function_id.as_index()];
            descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
            let pending = pending_functions
                .get_mut(&function_id)
                .expect("expected pending function body");
            pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
            instantiate_function_descr_in_place(ir_arena, pending, &mut mapper);
        }
    }
}

fn substitute_and_canonicalize_functions(
    output: &mut Module,
    ir_arena: &mut NodeArena,
    pending_functions: &mut PendingModuleFunctions,
    associated_lambdas: &FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    local_fns: &[LocalFunctionId],
    ty_inf: &mut UnifiedTypeInference,
) {
    for id in local_fns.iter() {
        for function_id in function_and_associated_lambdas(id, associated_lambdas) {
            let descr = pending_functions
                .get_mut(&function_id)
                .expect("expected pending function body");
            ty_inf.substitute_in_pending_module_function(descr, ir_arena);
            output.functions[function_id.as_index()].definition = descr.definition.clone();
        }

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
            for function_id in function_and_associated_lambdas(id, associated_lambdas) {
                let descr = &mut output.functions[function_id.as_index()];
                descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
                let pending = pending_functions
                    .get_mut(&function_id)
                    .expect("expected pending function body");
                pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
                hir::instantiate_node_in_place(ir_arena, pending.code.entry_node_id, &mut mapper);
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn borrow_check_and_elaborate_dict(
    output: &mut Module,
    ir_arena: &mut NodeArena,
    others: &Modules,
    pending_functions: &mut PendingModuleFunctions,
    associated_lambdas: &FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    dicts: &ExtraParameters,
    module_inst_data: &FxHashMap<LocalFunctionId, ExtraParameters>,
    id: &LocalFunctionId,
) -> Result<(), InternalCompilationError> {
    let mut solver = trait_solver_from_module!(output, others);
    let mut ctx = DictElaborationCtx::new(dicts, Some(module_inst_data), &mut solver);
    for function_id in function_and_associated_lambdas(id, associated_lambdas) {
        let function_slot = &mut output.functions[function_id.as_index()];
        borrow_check_and_elaborate_pending_function(
            function_slot,
            &mut output.ir_arena,
            ir_arena,
            pending_functions,
            &mut ctx,
            function_id,
        )?;
    }
    let generated = solver.commit(
        &mut output.functions,
        &mut output.def_table,
        pending_functions,
    );
    elaborate_generated_functions(output, ir_arena, others, pending_functions, generated)?;
    Ok(())
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
            let Some((trait_module_id, trait_id, trait_def)) = ({
                let module_env = ModuleEnv::new(&output, others);
                module_env
                    .trait_id_with_module(&Path::single_tuple(imp.trait_name))?
                    .map(|(trait_module_id, trait_id)| {
                        (
                            trait_module_id,
                            trait_id,
                            module_env.trait_def(trait_id).clone(),
                        )
                    })
            }) else {
                continue; // Trait not found; the error will be reported in the main impl loop
            };
            let trait_def = &trait_def;
            if input_tys.len() != trait_def.input_type_count() as usize {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: trait_def.input_type_count() as usize,
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
            if !output_tys.is_empty() && output_tys.len() != trait_def.output_type_count() as usize
            {
                return Err(internal_compilation_error!(WrongNumberOfArguments {
                    expected: trait_def.output_type_count() as usize,
                    expected_span: imp.trait_name.1,
                    got: output_tys.len(),
                    got_span: for_trait.span,
                }));
            }
            if output_tys.is_empty() && trait_def.output_type_count() != 0 {
                continue;
            }
            check_trait_impl(
                &output,
                others,
                trait_id,
                trait_module_id.is_none(),
                &input_tys,
                0,
                &[],
                imp.span,
            )?;
            // Pre-allocate placeholder functions for each trait method.
            let method_defs = trait_def.instantiate_for_tys(&input_tys, &output_tys);
            let mut method_ids = Vec::with_capacity(method_defs.len());
            for def in method_defs {
                // Placeholder ModuleFunction that will be replaced later.
                let placeholder = b(VoidFunction);
                let module_fn = ModuleFunction::new_without_spans_nor_locals(def, placeholder);
                method_ids.push(output.add_function_anonymous(module_fn));
            }
            // Build the trait impl and fill it with placeholders.
            let public = output.is_trait_impl_exportable(trait_id, &input_tys, &output_tys, others);
            let associated_const_values = {
                let solver = trait_solver_from_module!(output, others);
                associated_const_values_for_source_impl(
                    trait_id,
                    trait_def,
                    SourceAssociatedConstImpl {
                        input_tys: &input_tys,
                        output_tys: &output_tys,
                        ty_var_count: 0,
                        associated_consts: &imp.associated_consts,
                        span: imp.span,
                    },
                    &solver,
                )?
            };
            let dictionary_value = build_dictionary_value(&method_ids, &associated_const_values);
            let associated_const_tys =
                trait_def.instantiate_associated_const_tys_for_tys(&input_tys, &output_tys);
            let dictionary_ty = output.computer_dictionary_ty(&method_ids, associated_const_tys);
            let stub = TraitImpl::new(
                output_tys,
                method_ids.clone(),
                dictionary_value,
                dictionary_ty,
                public,
                Some(imp.span),
            )
            .with_associated_const_values(associated_const_values);
            let key = ConcreteTraitImplKey::new(trait_id, input_tys.clone());
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

    // Emit into a temporary pre-elaboration arena. The module stores only finalized HIR.
    let mut ir_arena = UNodeArena::default();

    emit_auto_value_impls(&mut output, &mut ir_arena, others, &source.impls)?;

    // Process each functions' SCC one by one.
    for mut scc in sorted_sccs.into_iter().rev() {
        scc.functions.sort(); // for compatibility due to bug in effect tracking

        // Extract functions from the SCC.
        let functions = || {
            scc.functions
                .iter()
                .map(|idx| &source.functions[idx.as_index()])
        };
        let recursive_function_names = if scc.recursive {
            functions().map(|function| function.name.0).collect()
        } else {
            FxHashSet::default()
        };
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
            &recursive_function_names,
        )?;
    }

    // Process trait implementations
    for (imp_idx, imp) in source.impls.iter().enumerate() {
        // Validate the function mapping.
        let module_env = ModuleEnv::new(&output, others);
        let (trait_module_id, trait_id) = module_env
            .trait_id_with_module(&Path::single_tuple(imp.trait_name))?
            .ok_or_else(|| internal_compilation_error!(TraitNotFound(imp.trait_name.1)))?;
        // Snapshot once per impl emission while later phases mutate the module.
        let trait_def = module_env.trait_def(trait_id).clone();
        let trait_def_for_consts = trait_def.clone();

        // Check that all methods in the impl are part of the trait.
        let mut extra_spans = vec![];
        for func in imp.functions.iter() {
            if trait_def.method_index(func.name.0).is_none() {
                extra_spans.push(func.name.1);
            }
        }
        if !extra_spans.is_empty() {
            return Err(internal_compilation_error!(MethodsNotPartOfTrait {
                trait_ref: trait_id,
                spans: extra_spans,
            }));
        }

        // Collect references to functions in the impl, in the order of the trait methods.
        let mut missings = vec![];
        let functions: Vec<_> = trait_def
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
                trait_ref: trait_id,
                impl_span: imp.span,
                missings,
            }));
        }

        // Emit the functions.
        debug_assert_eq!(functions.len(), trait_def.methods.len());
        let functions = || functions.iter().copied();
        let trait_ctx = EmitTraitCtx {
            trait_id,
            trait_def,
            span: imp.span,
            stub_data: concrete_impl_stubs.get(&imp_idx),
            generic_param_count: imp.generic_params.len(),
            for_trait: imp.for_trait.as_ref(),
            impl_constraints: &imp.where_clause,
        };
        let recursive_function_names = imp
            .function_sccs
            .iter()
            .filter(|scc| scc.recursive)
            .flat_map(|scc| {
                scc.functions
                    .iter()
                    .map(|index| imp.functions[index.as_index()].name.0)
            })
            .collect::<FxHashSet<_>>();
        let emit_output = emit_functions(
            &mut output,
            &mut ir_arena,
            functions,
            &desugared_arena,
            others,
            Some(trait_ctx),
            &recursive_function_names,
        )?
        .unwrap();

        // Register the implementation if no stub was present.
        let is_concrete = emit_output.ty_var_count == 0;
        let local_impl_id = if let Some(stub_data) = concrete_impl_stubs.get(&imp_idx) {
            assert_eq!(
                &emit_output.functions,
                &output.impls.data[stub_data.id.as_index()].methods
            );
            let associated_const_tys = trait_def_for_consts
                .instantiate_associated_const_tys_for_tys(
                    &emit_output.input_tys,
                    &emit_output.output_tys,
                );
            let new_dictionary_ty =
                output.computer_dictionary_ty(&emit_output.functions, associated_const_tys);
            let impl_data = output.impls.data.get_mut(stub_data.id.as_index()).unwrap();
            assert_eq!(new_dictionary_ty, impl_data.dictionary_ty);
            stub_data.id
        } else {
            check_trait_impl(
                &output,
                others,
                trait_id,
                trait_module_id.is_none(),
                &emit_output.input_tys,
                emit_output.ty_var_count,
                &emit_output.constraints,
                imp.span,
            )?;
            let associated_const_values = associated_const_values_for_source_impl(
                trait_id,
                &trait_def_for_consts,
                SourceAssociatedConstImpl {
                    input_tys: &emit_output.input_tys,
                    output_tys: &emit_output.output_tys,
                    ty_var_count: emit_output.ty_var_count,
                    associated_consts: &imp.associated_consts,
                    span: imp.span,
                },
                &trait_solver_from_module!(output, others),
            )?;
            let public = output.is_trait_impl_exportable(
                trait_id,
                &emit_output.input_tys,
                &emit_output.output_tys,
                others,
            );
            let associated_const_tys = trait_def_for_consts
                .instantiate_associated_const_tys_for_tys(
                    &emit_output.input_tys,
                    &emit_output.output_tys,
                );
            output.add_emitted_impl(
                trait_id,
                emit_output,
                associated_const_values,
                associated_const_tys,
                public,
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

    Ok(output)
}

/// Context passed to emit_functions when a trait implementation is being emitted.
struct EmitTraitCtx<'a> {
    trait_id: TraitId,
    trait_def: Trait,
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

#[derive(Clone, Copy, Debug, Default)]
struct FunctionAttributes {
    returns_place: bool,
    no_fuel_check: bool,
}

fn validate_function_attributes(
    attributes: &[ast::Attribute],
    function_name: Ustr,
    is_std_module: bool,
) -> Result<FunctionAttributes, InternalCompilationError> {
    let mut returns_place = false;
    let mut no_fuel_check = false;
    let known_attributes = [ustr("place_result"), ustr("no_fuel_check")];
    for attribute in attributes {
        let attr_name = attribute.path.0;
        if !known_attributes.contains(&attr_name) {
            continue;
        }
        if !is_std_module {
            return Err(
                InternalCompilationError::new_unsafe_feature_use_not_allowed(
                    UnsafeFeature::FunctionAttribute(attr_name),
                    attribute.span,
                ),
            );
        }
        if !attribute.items.is_empty() {
            return Err(internal_compilation_error!(InvalidAttribute {
                attribute_name: attr_name,
                target: AttributeTarget::Function {
                    name: function_name,
                },
                kind: InvalidAttributeKind::HasArguments,
                span: attribute.span,
            }));
        }
        let enabled = if attr_name == known_attributes[0] {
            &mut returns_place
        } else {
            &mut no_fuel_check
        };
        if *enabled {
            return Err(internal_compilation_error!(InvalidAttribute {
                attribute_name: attr_name,
                target: AttributeTarget::Function {
                    name: function_name,
                },
                kind: InvalidAttributeKind::Duplicate,
                span: attribute.span,
            }));
        }
        *enabled = true;
    }
    Ok(FunctionAttributes {
        returns_place,
        no_fuel_check,
    })
}

fn node_references_any_function(
    arena: &NodeArena,
    node_id: hir::NodeId,
    targets: &FxHashSet<FunctionId>,
) -> bool {
    if targets.is_empty() {
        return false;
    }
    match &arena[node_id].kind {
        hir::NodeKind::StaticApply(app) if targets.contains(&app.function) => return true,
        hir::NodeKind::GetFunction(get_fn) if targets.contains(&get_fn.function) => return true,
        _ => {}
    }
    arena[node_id]
        .kind
        .child_node_ids()
        .into_iter()
        .any(|child| node_references_any_function(arena, child, targets))
}

fn wrap_body_with_call_depth_check_if_recursive(
    ty_inf: &mut TypeInference,
    arena: &mut NodeArena,
    body_id: hir::NodeId,
    recursive_function_ids: &FxHashSet<FunctionId>,
    return_ty: Type,
    check_span: Location,
    block_span: Location,
) -> hir::NodeId {
    if !node_references_any_function(arena, body_id, recursive_function_ids) {
        return body_id;
    }

    let check_id = arena.alloc(hir::Node::new(
        hir::NodeKind::CheckCallDepth,
        Type::unit(),
        effect(PrimitiveEffect::Fallible),
        check_span,
    ));
    let body_effects = arena[body_id].effects.clone();
    let effects = ty_inf.make_dependent_effect([&arena[check_id].effects, &body_effects]);
    arena.alloc(hir::Node::new(
        hir::NodeKind::Block(b(hir::Block {
            body: b(SVec2::from_vec(vec![check_id, body_id])),
            cleanup: Vec::new(),
        })),
        return_ty,
        effects,
        block_span,
    ))
}

struct RecursiveReturnDefaultingInputs<'ctx, I> {
    ast_functions: I,
    local_fns: &'ctx [LocalFunctionId],
    function_explicit_root_tys: &'ctx [Vec<Type>],
    recursive_function_ids: &'ctx FxHashSet<FunctionId>,
    associated_lambdas: &'ctx FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
    pending_functions: &'ctx mut PendingModuleFunctions,
}

fn default_unconstrained_recursive_returns_to_never<'func, I>(
    output: &mut Module,
    ir_arena: &mut NodeArena,
    ty_inf: &mut UnifiedTypeInference,
    inputs: RecursiveReturnDefaultingInputs<'_, I>,
) where
    I: Iterator<Item = &'func DModuleFunction>,
{
    for ((function, id), explicit_root_tys) in inputs
        .ast_functions
        .zip(inputs.local_fns.iter())
        .zip(inputs.function_explicit_root_tys.iter())
    {
        if !inputs
            .recursive_function_ids
            .contains(&FunctionId::Local(*id))
            || function.ret_ty.is_some()
        {
            continue;
        }

        let Some(pending) = inputs.pending_functions.get(id) else {
            continue;
        };
        let root = pending.code.entry_node_id;
        if !node_references_any_function(ir_arena, root, inputs.recursive_function_ids) {
            continue;
        }

        let descr = &output.functions[id.as_index()];
        let fn_ty = ty_inf.substitute_in_fn_type(&descr.definition.ty_scheme.ty);
        let Some(ret_var) = fn_ty.ret.data().as_variable().copied() else {
            continue;
        };

        if fn_ty
            .args
            .iter()
            .any(|arg| arg.ty.contains_any_type_var(ret_var))
            || explicit_root_tys.iter().any(|ty| {
                ty_inf
                    .substitute_in_type(*ty)
                    .contains_any_type_var(ret_var)
            })
            || ty_inf
                .remaining_constraints()
                .iter()
                .any(|constraint| constraint.contains_any_type_var(ret_var))
        {
            continue;
        }

        let subst: (TypeInstSubst, FxHashMap<_, _>) = (
            FxHashMap::from_iter([(ret_var, Type::never())]),
            FxHashMap::default(),
        );
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        for function_id in function_and_associated_lambdas(id, inputs.associated_lambdas) {
            let descr = &mut output.functions[function_id.as_index()];
            descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
            let pending = inputs
                .pending_functions
                .get_mut(&function_id)
                .expect("expected pending function body");
            pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
            instantiate_function_descr_in_place(ir_arena, pending, &mut mapper);
        }
    }
}

fn emit_functions<'a, F, I>(
    output: &mut Module,
    ir_arena: &mut NodeArena,
    ast_functions: F,
    desugared_arena: &DExprArena,
    others: &Modules,
    trait_ctx: Option<EmitTraitCtx>,
    recursive_function_names: &FxHashSet<Ustr>,
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
        let trait_def = &trait_ctx.trait_def;
        let input_tys = ty_inf.fresh_type_var_tys(trait_def.input_type_count() as usize);
        let output_tys = ty_inf.fresh_type_var_tys(trait_def.output_type_count() as usize);
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
        for constraint in &trait_def.parent_constraints {
            ty_inf.add_pub_constraint(constraint.instantiate_location_cloned(trait_ctx.span));
        }
        for constraint in &trait_def.constraints {
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
                .trait_def
                .instantiate_for_tys(&trait_output.input_tys, &trait_output.output_tys),
        ),
        _ => None,
    };

    // Populate the function table
    let mut local_fns = Vec::new();
    let mut function_annotation_ty_substs = Vec::new();
    let mut function_explicit_root_tys = Vec::new();
    let mut function_attrs = Vec::new();
    for ast::ModuleFunction {
        visibility,
        name,
        generic_params,
        args,
        args_span,
        ret_ty,
        where_clause,
        attributes,
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
                        name.0, trait_ctx.trait_def.name
                    ),
                }));
            }
            if let Some(constraint) = where_clause.first() {
                return Err(internal_compilation_error!(Unsupported {
                    span: constraint.use_site(),
                    reason: format!(
                        "Method-local where clauses on trait impl methods are not supported yet: method `{}` in impl of trait `{}`",
                        name.0, trait_ctx.trait_def.name
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
            let index = trait_ctx.trait_def.method_index(name.0).unwrap();
            let (method_name, raw_method_def) = trait_ctx.trait_def.method(index);
            let instantiated_method_def =
                &instantiated_trait_method_defs.as_ref().unwrap()[index.as_index()];
            if args.len() != raw_method_def.ty_scheme.ty.args.len() {
                return Err(internal_compilation_error!(TraitMethodArgCountMismatch {
                    trait_ref: trait_ctx.trait_id,
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
        let attrs =
            validate_function_attributes(attributes, name.0, output.module_id() == STD_MODULE_ID)?;
        let returns_place = attrs.returns_place;
        let definition = FunctionDefinition::new_with_generic_params_and_attributes(
            ty_scheme,
            generic_params.clone(),
            arg_names,
            doc.clone(),
            attributes.clone(),
            returns_place,
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
        } else if returns_place {
            output.add_private_unsafe_function(name.0, descr)
        } else {
            output.add_function_with_visibility(name.0, descr, *visibility)
        };
        local_fns.push(id);
        function_annotation_ty_substs.push(annotation_ty_subst);
        function_explicit_root_tys.push(explicit_root_tys);
        function_attrs.push(attrs);
    }

    // Associated lambdas for functions emitted while lowering closure expressions.
    let mut associated_lambdas: FxHashMap<LocalFunctionId, Vec<LocalFunctionId>> =
        FxHashMap::default();
    let mut pending_functions = PendingModuleFunctions::default();

    let recursive_function_ids = ast_functions()
        .zip(local_fns.iter())
        .filter_map(|(function, id)| {
            recursive_function_names
                .contains(&function.name.0)
                .then_some(FunctionId::Local(*id))
        })
        .collect::<FxHashSet<_>>();

    // Second pass, infer types and emit function bodies.
    for (((function, id), annotation_ty_subst), attrs) in ast_functions()
        .zip(local_fns.iter())
        .zip(function_annotation_ty_substs.iter())
        .zip(function_attrs.iter())
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
            && is_value_trait(trait_ctx.trait_id, &trait_ctx.trait_def)
            && trait_ctx.trait_def.method_index(function.name.0) == Some(VALUE_CLONE_METHOD_INDEX)
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
            !attrs.no_fuel_check,
            &mut lambda_functions,
            output.functions.len() as u32,
            desugared_arena,
            ir_arena,
        );
        let mut fn_node_id = ty_inf.check_expr(
            &mut ty_env,
            function.body,
            descr.definition.ty_scheme.ty.ret,
            MutType::constant(),
            expected_span,
        )?;
        fn_node_id = wrap_body_with_call_depth_check_if_recursive(
            &mut ty_inf,
            ir_arena,
            fn_node_id,
            &recursive_function_ids,
            descr.definition.ty_scheme.ty.ret,
            function.name.1,
            expected_span,
        );
        lambda_functions.drain(..).for_each(|function| {
            let lambda_id =
                add_pending_function_anonymous(output, &mut pending_functions, function);
            output.name_function(
                lambda_id,
                format!("{GENERATED_LAMBDA_PREFIX}{}", lambda_id.as_index()).into(),
            );
            associated_lambdas.entry(*id).or_default().push(lambda_id);
        });
        let descr = output.get_function_by_id_mut(*id).unwrap();
        descr.definition.ty_scheme.ty.effects = ty_inf.unify_effects(
            &ir_arena[fn_node_id].effects,
            &descr.definition.ty_scheme.ty.effects,
        );
        let pending = PendingModuleFunction::new(
            descr.definition.clone(),
            PendingScriptFunction::new(fn_node_id, descr.definition.arg_names.len()),
            descr.spans.clone(),
            locals,
        );
        set_pending_function(output, &mut pending_functions, *id, pending);
        output.import_fn_slots.extend(new_import_slots);
        output.type_deps.extend(new_type_deps);
    }
    let module_env = ModuleEnv::new(output, others);
    ty_inf.log_debug_constraints(module_env);

    // Third pass, perform the unification.
    let mut solver = trait_solver_from_module!(output, others);
    let mut ty_inf = ty_inf.unify(&mut solver, ir_arena)?;
    let generated = solver.commit(
        &mut output.functions,
        &mut output.def_table,
        &mut pending_functions,
    );
    elaborate_generated_functions(output, ir_arena, others, &mut pending_functions, generated)?;
    let module_env = ModuleEnv::new(output, others);
    ty_inf.log_debug_substitution_tables(module_env);
    ty_inf.log_debug_constraints(module_env);

    // Resolve local-storage decisions before defaulting so only finalized ownership semantics add `Value`.
    let value_trait_id =
        module_env.expect_std_trait_id(crate::std::core_traits_names::VALUE_TRAIT_NAME);
    for id in local_fns.iter() {
        for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
            let descr = pending_functions
                .get_mut(&function_id)
                .expect("expected pending function body");
            let root = descr.code.entry_node_id;
            ty_inf.resolve_local_storage_and_activate_value_constraints(
                ir_arena,
                root,
                &mut descr.locals,
                value_trait_id,
            );
        }
    }

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
            let generated = solver.commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(
                output,
                ir_arena,
                others,
                &mut pending_functions,
                generated,
            )?;

            // Check for remaining orphans.
            ty_inf.normalize_remaining_constraints();
            let input_tys = ty_inf.substitute_in_types(&trait_output.input_tys);
            let output_tys = ty_inf.substitute_in_types(&trait_output.output_tys);
            let mut head_tys = input_tys.clone();
            head_tys.extend(output_tys.iter().copied());
            let head_quantifiers = collect_ty_vars(&head_tys);
            let head_boundary =
                ConstraintBoundary::from_seed_ty_vars(head_quantifiers.iter().copied());
            let module_env = ModuleEnv::new(output, others);
            let remaining_orphans: Vec<_> = head_boundary
                .inaccessible_constraints(ty_inf.remaining_constraints())
                .into_iter()
                .filter(|c| !c.is_type_has_variant())
                .filter(|c| !is_compiler_provided_value_constraint(c, module_env))
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
        substitute_and_canonicalize_functions(
            output,
            ir_arena,
            &mut pending_functions,
            &associated_lambdas,
            &local_fns,
            &mut ty_inf,
        );
        default_output_effects_in_functions(
            output,
            ir_arena,
            &mut pending_functions,
            &associated_lambdas,
            &local_fns,
        );

        // Resolve input and output types.
        ty_inf.substitute_in_types_in_place(&mut trait_output.input_tys);
        ty_inf.substitute_in_types_in_place(&mut trait_output.output_tys);

        // Take final substituted constraints.
        ty_inf.normalize_remaining_constraints();
        let all_constraints = ty_inf.take_constraints();

        // Validate that each method's effects are a subset of the trait definition's effects,
        // and override them with the trait's effects.
        // This ensures ABI consistency: the calling convention is determined by the trait definition.
        let trait_ctx = trait_ctx.unwrap();
        let trait_def = &trait_ctx.trait_def;
        for (i, id) in local_fns.iter().enumerate() {
            let i = TraitMethodIndex::from_index(i);
            let descr = &mut output.functions[id.as_index()];
            let (method_name, trait_method_def) = trait_def.method(i);
            let trait_effects = &trait_method_def.ty_scheme.ty.effects;
            let impl_effects = &descr.definition.ty_scheme.ty.effects;

            // Check that impl effects are a subset of trait effects.
            if !impl_effects.is_subset_of(trait_effects) {
                let span = descr.spans.as_ref().unwrap().span;
                return Err(internal_compilation_error!(TraitMethodEffectMismatch {
                    trait_ref: trait_ctx.trait_id,
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
            let root = pending_functions
                .get(id)
                .expect("expected pending function body")
                .code
                .entry_node_id;
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
        let generated = solver.commit(
            &mut output.functions,
            &mut output.def_table,
            &mut pending_functions,
        );
        elaborate_generated_functions(output, ir_arena, others, &mut pending_functions, generated)?;
        // Make sure substitution is not due to constraint processing.
        assert_eq!(subst_size, subst.0.len());

        // Apply unbound substitution to code and types.
        if !subst.0.is_empty() {
            let mut mapper = BitmapInstantiationMapper::new(&subst);
            instantiate_types_in_place(&mut trait_output.input_tys, &mut mapper);
            instantiate_types_in_place(&mut trait_output.output_tys, &mut mapper);
            for id in local_fns.iter() {
                for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                    let descr = &mut output.functions[function_id.as_index()];
                    descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
                    let pending = pending_functions
                        .get_mut(&function_id)
                        .expect("expected pending function body");
                    pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
                    instantiate_function_descr_in_place(ir_arena, pending, &mut mapper);
                }
            }
        }

        // Fifth pass, normalize the input types, substitute the types in the functions and input/output types.
        let subst = (normalize_types(&mut quantifiers), FxHashMap::default());
        let mut mapper = BitmapInstantiationMapper::new(&subst);
        instantiate_types_in_place(&mut trait_output.input_tys, &mut mapper);
        instantiate_types_in_place(&mut trait_output.output_tys, &mut mapper);
        instantiate_types_in_place(&mut trait_output.constraints, &mut mapper);
        for (method_index, id) in local_fns.iter().enumerate() {
            let method_index = TraitMethodIndex::from_index(method_index);
            for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                let descr = &mut output.functions[function_id.as_index()];
                descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
                descr.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
                let eff_quantifiers = descr.definition.ty_scheme.ty.input_effect_vars();
                assert!(eff_quantifiers.is_empty());
                descr.definition.ty_scheme.eff_quantifiers = eff_quantifiers;
                descr.definition.ty_scheme.constraints = trait_output.constraints.clone();
                let pending = pending_functions
                    .get_mut(&function_id)
                    .expect("expected pending function body");
                pending.definition = descr.definition.clone();
                instantiate_function_descr_in_place(ir_arena, pending, &mut mapper);
            }

            // Name the function
            let name = trait_def
                .qualified_method_name(method_index, &trait_output.input_tys)
                .into();
            output.name_function(*id, name);
        }

        // Sixth pass, run the borrow checker and elaborate into the final HIR arena.
        let dicts = extra_parameters_from_constraints(
            &trait_output.constraints,
            ModuleEnv::new(output, others),
        );
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
            borrow_check_and_elaborate_dict(
                output,
                ir_arena,
                others,
                &mut pending_functions,
                &associated_lambdas,
                &dicts,
                &module_inst_data,
                id,
            )?;
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
                pending_functions
                    .get(id)
                    .map(|function| {
                        UnifiedTypeInference::collect_unit_variant_seed_types(
                            ir_arena,
                            function.code.entry_node_id,
                        )
                    })
                    .unwrap_or_default()
            } else {
                Vec::new()
            };
            let scope = DefaultingScope::from_constraints(&orphan_constraints)
                .with_unit_variant_seed_tys(unit_variant_seed_tys);
            ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, ir_arena)?;
            let generated = solver.commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(
                output,
                ir_arena,
                others,
                &mut pending_functions,
                generated,
            )?;
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
            let module_env = ModuleEnv::new(output, others);
            let remaining_orphans: Vec<_> = sig_boundary
                .inaccessible_constraints(ty_inf.remaining_constraints())
                .into_iter()
                .filter(|c| !c.is_type_has_variant())
                .filter(|c| !is_compiler_provided_value_constraint(c, module_env))
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
        substitute_and_canonicalize_functions(
            output,
            ir_arena,
            &mut pending_functions,
            &associated_lambdas,
            &local_fns,
            &mut ty_inf,
        );

        // Recursive-return defaulting inspects the final constraints.
        ty_inf.normalize_remaining_constraints();
        default_unconstrained_recursive_returns_to_never(
            output,
            ir_arena,
            &mut ty_inf,
            RecursiveReturnDefaultingInputs {
                ast_functions: ast_functions(),
                local_fns: &local_fns,
                function_explicit_root_tys: &function_explicit_root_tys,
                recursive_function_ids: &recursive_function_ids,
                associated_lambdas: &associated_lambdas,
                pending_functions: &mut pending_functions,
            },
        );

        // Take final substituted constraints.
        let all_constraints = ty_inf.take_constraints();

        // For each function: filter constraints, check unbounds, finalize type scheme.
        let mut used_constraints: FxHashSet<PubTypeConstraintPtr> = FxHashSet::default();
        for ((function, id), explicit_root_tys) in ast_functions()
            .zip(local_fns.iter())
            .zip(function_explicit_root_tys.iter())
        {
            let descr = &output.functions[id.as_index()];
            let code_entry = pending_functions
                .get(id)
                .expect("expected pending function body")
                .code
                .entry_node_id;

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
                for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                    let pending = pending_functions
                        .get_mut(&function_id)
                        .expect("expected pending function body");
                    instantiate_function_descr_in_place(ir_arena, pending, &mut mapper);
                }
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
            let generated = solver.commit(
                &mut output.functions,
                &mut output.def_table,
                &mut pending_functions,
            );
            elaborate_generated_functions(
                output,
                ir_arena,
                others,
                &mut pending_functions,
                generated,
            )?;

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
            for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                let descr = &mut output.functions[function_id.as_index()];
                descr.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
                descr.definition.ty_scheme.eff_quantifiers =
                    descr.definition.ty_scheme.ty.input_effect_vars();
                descr.definition.ty_scheme.constraints = constraints.clone();
                descr.definition.generic_params = function.generic_params.clone();
                pending_functions
                    .get_mut(&function_id)
                    .expect("expected pending function body")
                    .definition = descr.definition.clone();
            }

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
        let module_env = ModuleEnv::new(output, others);
        let unused_constraints = all_constraints
            .iter()
            .filter(|c| {
                !used_constraints.contains(&constraint_ptr(c))
                    && !c.is_type_has_variant()
                    && !is_compiler_provided_value_constraint(c, module_env)
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

        // Fifth pass, normalize the type schemes, substitute the types in the functions.
        for id in local_fns.iter() {
            for function_id in function_and_associated_lambdas(id, &associated_lambdas) {
                let descr = &mut output.functions[function_id.as_index()];
                // Note: after that normalization, the functions do not share the same
                // type variables anymore.
                let subst = descr.definition.ty_scheme.normalize();
                let mut mapper = BitmapInstantiationMapper::new(&subst);
                let pending = pending_functions
                    .get_mut(&function_id)
                    .expect("expected pending function body");
                pending.definition = descr.definition.clone();
                instantiate_function_descr_in_place(ir_arena, pending, &mut mapper);
            }
        }

        // Sixth pass, run the borrow checker and elaborate into the final HIR arena.
        let mut module_inst_data = FxHashMap::default();
        for id in local_fns.iter() {
            let descr = &output.functions[id.as_index()];
            let dicts = descr
                .definition
                .ty_scheme
                .extra_parameters(ModuleEnv::new(output, others));
            insert_inst_data_for_function_and_lambdas(
                &mut module_inst_data,
                &associated_lambdas,
                *id,
                dicts,
            );
        }
        for id in local_fns.iter() {
            let dicts = module_inst_data.get(id).unwrap();
            borrow_check_and_elaborate_dict(
                output,
                ir_arena,
                others,
                &mut pending_functions,
                &associated_lambdas,
                dicts,
                &module_inst_data,
                id,
            )?;
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
    pub expr: hir::ENodeId,
    pub ty: TypeScheme<Type>,
    pub locals: Vec<ELocalDecl>,
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
    let mut ir_arena = UNodeArena::default();
    emit_expr_unsafe_inner(source, parsed_arena, module, others, locals, &mut ir_arena)
}

fn emit_expr_unsafe_inner(
    source: PExprId,
    parsed_arena: &PExprArena,
    module: &mut Module,
    others: &Modules,
    mut locals: Vec<LocalDecl>,
    ir_arena: &mut UNodeArena,
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
    let expr_span = parsed_arena[source].span;

    // First desugar the expression.
    let mut modules_used = FxHashSet::default();
    let (source, desugared_arena) =
        desugar_expr_with_empty_ctx(source, parsed_arena, &module_env, &mut modules_used)?;

    // Infer the expression with the existing locals.
    let initial_local_count = locals.len();
    let mut new_import_slots = vec![];
    let mut new_type_deps = FxHashSet::default();
    let mut lambda_functions = vec![];
    let mut pending_functions = PendingModuleFunctions::default();
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
        true,
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
            let id = add_pending_function_anonymous(module, &mut pending_functions, function);
            module.name_function(
                id,
                format!("{GENERATED_LAMBDA_PREFIX}{}", id.as_index()).into(),
            );
            id
        })
        .collect::<Vec<_>>();
    module.import_fn_slots.extend(new_import_slots);
    module.type_deps.extend(new_type_deps);
    module.type_deps.extend(modules_used);

    // Perform the unification.
    let mut solver = trait_solver_from_module!(module, others);
    let mut ty_inf = ty_inf.unify(&mut solver, ir_arena)?;
    let generated = solver.commit(
        &mut module.functions,
        &mut module.def_table,
        &mut pending_functions,
    );
    elaborate_generated_functions(module, ir_arena, others, &mut pending_functions, generated)?;
    let module_env = ModuleEnv::new(module, others);
    ty_inf.log_debug_substitution_tables(module_env);
    ty_inf.log_debug_constraints(module_env);

    // Resolve local-storage decisions before defaulting so only finalized ownership semantics add `Value`.
    let value_trait_id =
        module_env.expect_std_trait_id(crate::std::core_traits_names::VALUE_TRAIT_NAME);
    for lambda_id in lambda_functions.iter() {
        let descr = pending_functions
            .get_mut(lambda_id)
            .expect("expected pending function body");
        let root = descr.code.entry_node_id;
        ty_inf.resolve_local_storage_and_activate_value_constraints(
            ir_arena,
            root,
            &mut descr.locals,
            value_trait_id,
        );
    }
    ty_inf.resolve_local_storage_and_activate_value_constraints(
        ir_arena,
        node_id,
        &mut locals,
        value_trait_id,
    );

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
        let generated = solver.commit(
            &mut module.functions,
            &mut module.def_table,
            &mut pending_functions,
        );
        elaborate_generated_functions(module, ir_arena, others, &mut pending_functions, generated)?;
    }

    // Substitute everything using ty_inf (single pass, includes all defaults).
    ty_inf.substitute_in_node(ir_arena, node_id);
    for lambda_id in lambda_functions.iter() {
        let descr = pending_functions
            .get_mut(lambda_id)
            .expect("expected pending function body");
        ty_inf.substitute_in_pending_module_function(descr, ir_arena);
        module.functions[lambda_id.as_index()].definition = descr.definition.clone();
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
            let pending = pending_functions
                .get_mut(lambda_id)
                .expect("expected pending function body");
            pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
            hir::instantiate_node_in_place(ir_arena, pending.code.entry_node_id, &mut mapper);
            for local in &mut pending.locals {
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
            let pending = pending_functions
                .get_mut(lambda_id)
                .expect("expected pending function body");
            pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
            hir::instantiate_node_in_place(ir_arena, pending.code.entry_node_id, &mut mapper);
            for local in &mut pending.locals {
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
        pending_functions
            .get_mut(lambda_id)
            .expect("expected pending function body")
            .definition = descr.definition.clone();
    }
    let generated = solver.commit(
        &mut module.functions,
        &mut module.def_table,
        &mut pending_functions,
    );
    elaborate_generated_functions(module, ir_arena, others, &mut pending_functions, generated)?;

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
        let pending = pending_functions
            .get_mut(lambda_id)
            .expect("expected pending function body");
        pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
        hir::instantiate_node_in_place(ir_arena, pending.code.entry_node_id, &mut mapper);
        for local in &mut pending.locals {
            local.ty = local.ty.map(&mut mapper);
        }
    }
    ty_scheme.ty = ty_scheme.ty.map(&mut mapper);
    for local in locals.iter_mut().skip(initial_local_count) {
        local.ty = local.ty.map(&mut mapper);
    }
    drop(mapper);

    validate_safe_expr_type_scheme(&ty_scheme, expr_span)?;

    // Do borrow checking and dictionary elaboration.
    let dicts = ty_scheme.extra_parameters(ModuleEnv::new(module, others));
    let mut solver = trait_solver_from_module!(module, &others);
    let mut ctx = DictElaborationCtx::new(&dicts, None, &mut solver);
    let local_count = locals.len();
    elaborate_local_ownership_and_value_dispatches(ir_arena, &mut locals, &mut ctx)?;
    check_borrows(ir_arena, node_id)?;
    let expr = elaborate_hir(ir_arena, node_id, &mut module.ir_arena, &mut ctx, &locals)?.root;
    for lambda_id in lambda_functions.iter() {
        let function_slot = &mut module.functions[lambda_id.as_index()];
        borrow_check_and_elaborate_pending_function(
            function_slot,
            &mut module.ir_arena,
            ir_arena,
            &mut pending_functions,
            &mut ctx,
            *lambda_id,
        )?;
    }
    let generated = solver.commit(
        &mut module.functions,
        &mut module.def_table,
        &mut pending_functions,
    );
    elaborate_generated_functions(module, ir_arena, others, &mut pending_functions, generated)?;
    assert_eq!(locals.len(), local_count);
    for lambda_id in lambda_functions {
        module.functions[lambda_id.as_index()].refresh_debug_info();
    }

    Ok(CompiledExpr {
        expr,
        ty: ty_scheme,
        locals: locals.into_iter().map(LocalDecl::into_elaborated).collect(),
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
    validate_safe_expr_type_scheme(&ty, span)?;
    Ok(CompiledExpr { ty, expr, locals })
}

fn validate_safe_expr_type_scheme(
    ty: &TypeScheme<Type>,
    span: Location,
) -> Result<(), InternalCompilationError> {
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
    Ok(())
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

fn is_compiler_provided_value_constraint(c: &PubTypeConstraint, module_env: ModuleEnv<'_>) -> bool {
    match c {
        PubTypeConstraint::HaveTrait {
            trait_id,
            input_tys,
            output_tys,
            ..
        } => {
            let trait_def = module_env.trait_def(*trait_id);
            is_value_trait_for_function_type(*trait_id, trait_def, input_tys, output_tys)
                || is_function_surface_only_value_trait_application(
                    *trait_id, trait_def, input_tys, output_tys,
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
