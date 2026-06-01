// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    FxHashMap, FxHashSet, Modules,
    containers::B,
    hir::{
        emit_associated_consts::{
            SourceAssociatedConstImpl, associated_const_values_for_source_impl,
        },
        function::VoidFunction,
    },
    module::Uses,
};

use log::log_enabled;
use ustr::Ustr;

use crate::{
    ast::{self, *},
    compiler::error::InternalCompilationError,
    containers::{b, iterable_to_string},
    format::FormatWith,
    hir::{self, UNodeArena},
    hir::{
        dictionary::{DictElaborationCtx, ExtraParameters},
        elaboration::elaborate_generated_functions,
        emit_functions::{EmitTraitCtx, emit_functions},
        emit_value_impl::emit_auto_value_impls,
    },
    internal_compilation_error,
    module::{
        ConcreteTraitImplKey, LocalFunctionId, LocalImplId, Module, ModuleEnv, ModuleFunction,
        ModuleId, PendingModuleFunction, TraitImpl, UModuleFunction, build_dictionary_value,
        id::Id,
    },
    std::value::{
        is_function_surface_only_value_trait_application, is_value_trait_for_function_type,
    },
    types::coherence::check_trait_impl,
    types::effects::EffType,
    types::trait_solver::{TraitSolver, trait_solver_from_module},
    types::r#type::Type,
    types::type_inference::unify::UnifiedTypeInference,
    types::type_like::TypeLike,
    types::type_mapper::{BitmapInstantiationMapper, TypeMapper},
    types::type_scheme::PubTypeConstraint,
    types::type_visitor::collect_ty_vars,
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

pub(super) fn insert_inst_data_for_function_and_lambdas(
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

pub(super) fn function_and_associated_lambdas<'a>(
    id: &'a LocalFunctionId,
    associated_lambdas: &'a FxHashMap<LocalFunctionId, Vec<LocalFunctionId>>,
) -> impl Iterator<Item = LocalFunctionId> + 'a {
    std::iter::once(*id).chain(associated_lambdas.get(id).into_iter().flatten().copied())
}

pub(super) type PendingModuleFunctions = FxHashMap<LocalFunctionId, PendingModuleFunction>;

pub(super) fn add_pending_function_anonymous(
    module: &mut Module,
    pending_functions: &mut PendingModuleFunctions,
    function: UModuleFunction,
) -> LocalFunctionId {
    let id = module.add_function_anonymous(function.placeholder());
    pending_functions.insert(id, function);
    id
}

pub(super) fn set_pending_function(
    module: &mut Module,
    pending_functions: &mut PendingModuleFunctions,
    id: LocalFunctionId,
    function: UModuleFunction,
) {
    module.functions[id.as_index()] = function.placeholder();
    pending_functions.insert(id, function);
}

/// Data for a pre-registered stub implementation for `impl Trait for ConcreteType`.
pub(super) struct ImplStubData {
    pub(super) id: LocalImplId,
    pub(super) input_tys: Vec<Type>,
    pub(super) method_ids: Vec<LocalFunctionId>,
}

pub(super) fn instantiate_function_descr_in_place<M: TypeMapper>(
    descr: &mut UModuleFunction,
    mapper: &mut M,
) {
    hir::instantiate_node_in_place(&mut descr.code.arena, descr.code.entry_node_id, mapper);
    for local in &mut descr.locals {
        local.ty = local.ty.map(mapper);
    }
}

pub(super) fn borrow_check_and_elaborate_pending_function(
    function_slot: &mut ModuleFunction,
    dst_arena: &mut hir::ENodeArena,
    pending_functions: &mut PendingModuleFunctions,
    ctx: &mut DictElaborationCtx<'_, '_, '_>,
    id: LocalFunctionId,
) -> Result<(), InternalCompilationError> {
    let mut function = pending_functions
        .remove(&id)
        .expect("expected pending function body");
    function.definition = function_slot.definition.clone();
    function.spans = function_slot.spans.clone();
    let (elaborated, _) = function.check_borrows_and_elaborate_hir(dst_arena, ctx)?;
    *function_slot = elaborated;
    Ok(())
}

pub(super) fn refresh_debug_info_for_functions(
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

pub(super) fn default_output_effects_in_functions(
    output: &mut Module,
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
            instantiate_function_descr_in_place(pending, &mut mapper);
        }
    }
}

pub(super) fn substitute_and_canonicalize_functions(
    output: &mut Module,
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
            ty_inf.substitute_in_pending_module_function(descr);
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
                hir::instantiate_node_in_place(
                    &mut pending.code.arena,
                    pending.code.entry_node_id,
                    &mut mapper,
                );
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn borrow_check_and_elaborate_dict(
    output: &mut Module,
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
    elaborate_generated_functions(output, others, pending_functions, generated)?;
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

    // Temporary unelaborated HIR arena used by trait solving/defaulting paths.
    let mut solver_arena = UNodeArena::default();

    emit_auto_value_impls(&mut output, &mut solver_arena, others, &source.impls)?;

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
            &mut solver_arena,
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
            &mut solver_arena,
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

pub(super) type PubTypeConstraintPtr = *const PubTypeConstraint;

pub(super) fn constraint_ptr(c: &PubTypeConstraint) -> PubTypeConstraintPtr {
    c as *const PubTypeConstraint
}

pub(super) fn is_compiler_provided_value_constraint(
    c: &PubTypeConstraint,
    module_env: ModuleEnv<'_>,
) -> bool {
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

pub(super) fn log_dropped_constraints_expr(
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

pub(super) fn log_dropped_constraints_module(
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
