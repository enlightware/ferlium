// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    borrow::Borrow,
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use indexmap::IndexMap;
use itertools::{process_results, Itertools};
use log::log_enabled;
use ustr::{ustr, Ustr};

use crate::{
    ast::{self, *},
    containers::{b, iterable_to_string, sorted},
    dictionary_passing::DictElaborationCtx,
    effects::EffType,
    error::InternalCompilationError,
    function::{FunctionDefinition, ScriptFunction},
    internal_compilation_error,
    ir::{self, Immediate, Node},
    module::{self, FmtWithModuleEnv, Module, ModuleEnv, Modules, Use},
    mutability::MutType,
    r#trait::TraitRef,
    r#type::{FnArgType, FnType, Type, TypeDefRef, TypeSubstitution, TypeVar},
    std::math::{float_type, int_type, NUM_TRAIT},
    trait_solver::TraitImpls,
    type_inference::{FreshVariableTypeMapper, TypeInference},
    type_like::{instantiate_types, TypeLike},
    type_mapper::TypeMapper,
    type_scheme::{
        extra_parameters_from_constraints, normalize_types, PubTypeConstraint, TypeScheme,
        VariantConstraint,
    },
    type_visitor::{collect_ty_vars, TyVarsCollector},
    typing_env::{Local, TypingEnv},
    value::Value,
};

fn validate_name_uniqueness(source: &ast::PModule) -> Result<(), InternalCompilationError> {
    let mut names = HashMap::new();
    for (name, span) in source.name_iter() {
        if let Some(first_occurrence) = names.insert(name, span) {
            return Err(internal_compilation_error!(NameDefinedMultipleTimes {
                first_occurrence,
                second_occurrence: span,
            }));
        }
    }
    Ok(())
}

/// Emit IR for the given module
pub fn emit_module(
    source: ast::PModule,
    others: &Modules,
    merge_with: Option<&Module>,
) -> Result<Module, InternalCompilationError> {
    // Preliminary: Make sure no name is defined multiple times.
    validate_name_uniqueness(&source)?;

    // First desugar the module.
    let (source, sorted_sccs) = source.desugar()?;

    // Prepare target module and list of all available trait implementations.
    let mut output = merge_with.map_or_else(Module::default, |module| module.clone());
    let mut trait_impls = ModuleEnv::new(&output, others).collect_trait_impls();

    // Add types aliases and definitions to output module
    for ((name, _), ty) in source.type_aliases {
        output.type_aliases.set_with_ustr(name, ty);
    }
    for type_def in source.type_defs {
        assert!(type_def.generic_params.is_empty());
        assert!(type_def.doc_comments.is_empty());
        output.type_defs.insert(
            type_def.name.0,
            TypeDefRef::new(crate::r#type::TypeDef {
                name: type_def.name.0,
                param_names: vec![],
                shape: type_def.shape,
                span: type_def.span,
                attributes: HashMap::new(),
            }),
        );
    }

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
        emit_functions(&mut output, functions, others, &mut trait_impls, None)?;
    }

    // Process trait implementations
    let rc_output: Rc<Module> = output.clone().into(); // TODO: use Rc for module as well
    for imp in &source.impls {
        // Build a module environment for the compiling the trait implementation.
        // We create a standalone module, importing the current module as
        // the "module" namespace, with a "use all" directive.
        let mut trait_others = others.clone();
        trait_others.insert(ustr("module"), rc_output.clone());
        let mut trait_output = Module {
            uses: output.uses.clone(),
            ..Default::default()
        };
        trait_output.uses.push(Use::All(ustr("module")));

        // Validate the function mapping.
        let module_env = ModuleEnv::new(&trait_output, &trait_others);
        let trait_ref = module_env
            .get_trait_ref(&imp.trait_name.0)
            .ok_or_else(|| internal_compilation_error!(TraitNotFound(imp.trait_name.1)))?;

        // Collect references to the method definitions in the trait, and a map of their name to index.
        let (fn_defs, fn_names, fn_indices): (Vec<_>, HashMap<_, _>, HashMap<_, _>) =
            process_results(
                imp.functions.iter().map(|func| {
                    let (index, (fn_name, fn_def)) = &trait_ref
                        .functions
                        .iter()
                        .find_position(|trait_func| trait_func.0 == func.name.0)
                        .ok_or_else(|| {
                            internal_compilation_error!(MethodNotPartOfTrait {
                                trait_ref: trait_ref.clone(),
                                fn_span: func.name.1
                            })
                        })?;
                    Ok((fn_def, (*index, *fn_name), (*fn_name, *index)))
                }),
                |iter| iter.multiunzip(),
            )?;

        // Make sure all trait methods are present.
        if fn_defs.len() < trait_ref.functions.len() {
            let missings = trait_ref
                .functions
                .iter()
                .filter_map(|(name, _)| {
                    let name = *name;
                    if imp.functions.iter().any(|func| func.name.0 == name) {
                        None
                    } else {
                        Some(name)
                    }
                })
                .collect::<Vec<_>>();
            return Err(internal_compilation_error!(TraitMethodImplMissing {
                impl_span: imp.span,
                trait_ref: trait_ref.clone(),
                missings,
            }));
        }

        // Emit the functions.
        let functions = || imp.functions.iter();
        let trait_ctx = EmitTraitCtx {
            trait_ref: trait_ref.clone(),
            fn_indices,
        };
        let emit_output = emit_functions(
            &mut trait_output,
            functions,
            &trait_others,
            &mut trait_impls,
            Some(trait_ctx),
        )?
        .unwrap();

        // Build the implementations by extracting functions from the built module.
        let functions: Vec<_> = (0..trait_ref.functions.len())
            .map(|index| {
                let func = trait_output.functions.get(&fn_names[&index]).unwrap();
                func.code.clone()
            })
            .collect();
        drop(trait_output); // needed so that the try_unwrap below works
        if emit_output.ty_var_count == 0 {
            let functions: Vec<_> = functions
                .into_iter()
                .map(|f| Rc::try_unwrap(f).unwrap().into_inner())
                .collect();
            let key = (trait_ref.clone(), emit_output.input_tys.clone());
            let imp = output.impls.add_concrete(
                trait_ref,
                emit_output.input_tys,
                emit_output.output_tys,
                functions,
            );
            trait_impls.concrete.insert(key, imp);
        } else {
            let input_tys = emit_output.input_tys.clone();
            let imp = output.impls.add_blanket(
                trait_ref.clone(),
                emit_output.input_tys,
                emit_output.output_tys,
                emit_output.ty_var_count,
                emit_output.constraints,
                functions,
            );
            trait_impls
                .blanket
                .entry(trait_ref)
                .or_default()
                .push((input_tys, imp));
        }
    }

    Ok(output)
}

struct EmitTraitCtx {
    trait_ref: TraitRef,
    fn_indices: HashMap<Ustr, usize>,
}

struct EmitTraitOutput {
    input_tys: Vec<Type>,
    output_tys: Vec<Type>,
    ty_var_count: u32,
    constraints: Vec<PubTypeConstraint>,
}

fn emit_functions<'a, F, I>(
    output: &mut Module,
    functions: F,
    others: &Modules,
    trait_impls: &mut TraitImpls,
    trait_ctx: Option<EmitTraitCtx>,
) -> Result<Option<EmitTraitOutput>, InternalCompilationError>
where
    I: Iterator<Item = &'a DModuleFunction>,
    F: Fn() -> I,
{
    use ir::Node as N;
    use ir::NodeKind as K;

    // First pass, populate the function table and allocate fresh mono type variables.
    let mut ty_inf = TypeInference::default();

    // If we are emitting a trait implementation, create generics for the trait input and output types
    // and add the constraints from the trait definition to the type inference.
    let trait_output = if let Some(trait_ctx) = &trait_ctx {
        let trait_ref = &trait_ctx.trait_ref;
        let input_tys = ty_inf.fresh_type_var_tys(trait_ref.input_type_count.get() as usize);
        let output_tys = ty_inf.fresh_type_var_tys(trait_ref.output_type_count() as usize);
        for constraint in &trait_ctx.trait_ref.constraints {
            ty_inf.add_pub_constraint(constraint.clone());
        }
        Some(EmitTraitOutput {
            input_tys,
            output_tys,
            ty_var_count: 0,
            constraints: vec![],
        })
    } else {
        None
    };

    // Populate the function table
    for ModuleFunction {
        name,
        args,
        args_span,
        ret_ty,
        span,
        doc,
        ..
    } in functions()
    {
        // Create type and mutability variables for the arguments.
        // Note: the type quantifiers and constraints are left empty.
        // They will be filled in the second pass.
        // The effect quantifiers are filled with the output effect variable.
        let args_ty = args
            .iter()
            .map(|arg| {
                if let Some((mut_ty, ty, _)) = arg.1 {
                    let mut mapper = FreshVariableTypeMapper::new(&mut ty_inf);
                    let mut_ty = mapper.map_mut_type(mut_ty);
                    let ty = ty.map(&mut mapper);
                    FnArgType::new(ty, mut_ty)
                } else {
                    ty_inf.fresh_fn_arg()
                }
            })
            .collect();
        let ret_ty_ty = if let Some((ret_ty, _)) = ret_ty {
            ret_ty.map(&mut FreshVariableTypeMapper::new(&mut ty_inf))
        } else {
            ty_inf.fresh_type_var_ty()
        };
        let effects = ty_inf.fresh_effect_var_ty();
        let fn_type = FnType::new(args_ty, ret_ty_ty, effects.clone());

        // If we are emitting a trait implementation, make sure this function conforms to it.
        if let Some(trait_ctx) = &trait_ctx {
            let index = trait_ctx.fn_indices[&name.0];
            let fn_def = &trait_ctx.trait_ref.functions[index].1;
            if args.len() != fn_def.ty_scheme.ty.args.len() {
                return Err(internal_compilation_error!(TraitMethodArgCountMismatch {
                    trait_ref: trait_ctx.trait_ref.clone(),
                    index,
                    expected: fn_def.ty_scheme.ty.args.len(),
                    got: args.len(),
                    args_span: *args_span,
                }));
            }
            // TODO: get span from the trait method definition, when available
            ty_inf.add_same_fn_type_constraint(&fn_type, *span, &fn_def.ty_scheme.ty, *span);
        }

        // Create dummy code.
        let dummy_code = b(ScriptFunction::new(N::new(
            K::Immediate(Immediate::new(Value::unit())),
            Type::unit(),
            effects,
            *span,
        )));

        // Assemble the spans and the description
        let spans = module::ModuleFunctionSpans {
            name: name.1,
            args: args
                .iter()
                .map(|((_, span), ty)| {
                    (
                        *span,
                        ty.map(|ty| (ty.2, !ty.0.is_variable() && ty.1.is_constant())),
                    )
                })
                .collect(),
            args_span: *args_span,
            ret_ty: ret_ty.map(|ret_ty| (ret_ty.1, ret_ty.0.is_constant())),
            span: *span,
        };
        let ty_scheme = TypeScheme::new_just_type(fn_type);
        let arg_names = args.iter().map(|arg| arg.0 .0).collect();
        let descr = module::ModuleFunction {
            definition: FunctionDefinition::new(ty_scheme, arg_names, doc.clone()),
            code: Rc::new(RefCell::new(dummy_code)),
            spans: Some(spans),
        };
        output.functions.insert(name.0, descr);
    }

    // Second pass, infer types and emit function bodies.
    for function in functions() {
        let name = function.name.0;
        let descr = output.functions.get(&name).unwrap();
        let module_env = ModuleEnv::new(output, others);
        let arg_names: Vec<_> = function.args.iter().map(|arg| arg.0).collect();
        let mut ty_env = TypingEnv::new(
            descr.definition.ty_scheme.ty.as_locals_no_bound(&arg_names),
            module_env,
        );
        let expected_span = descr.spans.as_ref().unwrap().args_span;
        let fn_node = ty_inf.check_expr(
            &mut ty_env,
            &function.body,
            descr.definition.ty_scheme.ty.ret,
            MutType::constant(),
            expected_span,
        )?;
        let descr = output.functions.get_mut(&name).unwrap();
        descr.definition.ty_scheme.ty.effects =
            ty_inf.unify_effects(&fn_node.effects, &descr.definition.ty_scheme.ty.effects);
        *descr.code.borrow_mut() = b(ScriptFunction::new(fn_node));
    }
    let module_env = ModuleEnv::new(output, others);
    ty_inf.log_debug_constraints(module_env);

    // Third pass, perform the unification.
    let mut ty_inf = ty_inf.unify(trait_impls)?;
    ty_inf.log_debug_substitution_tables(module_env);
    ty_inf.log_debug_constraints(module_env);

    // Fourth pass, substitute the mono type variables with the inferred types.
    for ModuleFunction { name, .. } in functions() {
        let descr = output.functions.get_mut(&name.0).unwrap();
        ty_inf.substitute_in_module_function(descr);

        // Union duplicated effects from function arguments, and build a substitution for the
        // fully unioned effects, to removed duplications.
        ty_inf.unify_fn_arg_effects(&descr.definition.ty_scheme.ty);
        let effect_subst = descr
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
        let mut node = descr.get_node_mut().unwrap();
        let subst = (HashMap::new(), effect_subst);
        node.instantiate(&subst);
        drop(node);
        descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.instantiate(&subst);
    }

    // Fifth pass, get the remaining constraints and collect the free type variables.
    if let Some(mut trait_output) = trait_output {
        // We are emitting a trait.

        // Resolve input and output types.
        trait_output.input_tys = ty_inf.substitute_in_types(&trait_output.input_tys);
        trait_output.output_tys = ty_inf.substitute_in_types(&trait_output.output_tys);

        // Validate and simplify constraints.
        let constraints = ty_inf.constraints();
        let input_quantifiers = collect_ty_vars(&trait_output.input_tys);
        let (mut quantifiers, mut subst) = validate_and_simplify_trait_imp_constraints(
            &input_quantifiers,
            &constraints,
            trait_impls,
        )?;

        // Detect unbound type variables in the code and return error if not in unused variants only.
        // These are neither part of the function signature nor of the constraints.
        let bounds: Vec<_> = quantifiers.iter().chain(subst.keys()).cloned().collect();
        for ModuleFunction { name, .. } in functions() {
            let node = output.get_own_function_node_mut(name.0).unwrap();
            let unbound = node.all_unbound_ty_vars();
            let uninstantiated_unbound = check_unbounds(unbound, &bounds)?;
            subst.extend(
                uninstantiated_unbound
                    .into_iter()
                    .map(|ty_var| (ty_var, Type::never())),
            );
        }

        // Update quantifiers and constraints with substitution.
        quantifiers.retain(|ty_var| !subst.contains_key(ty_var));
        trait_output.ty_var_count = quantifiers.len() as u32;
        let mut subst = (subst, HashMap::new());
        let subst_size = subst.0.len();
        trait_output.constraints = constraints
            .iter()
            .filter_map(|constraint| {
                constraint
                    .instantiate_and_drop_if_known_trait(&mut subst, trait_impls)
                    .transpose()
            })
            .collect::<Result<_, _>>()?;
        // Make sure substitution is not due to constraint processing.
        assert_eq!(subst_size, subst.0.len());
        let dicts = extra_parameters_from_constraints(&trait_output.constraints);

        // Update node code with substitution and build the module instantiation data
        trait_output.input_tys = instantiate_types(&trait_output.input_tys, &subst);
        trait_output.output_tys = instantiate_types(&trait_output.output_tys, &subst);
        let mut module_inst_data = HashMap::new();
        for ModuleFunction { name, .. } in functions() {
            let descr = output.functions.get_mut(&name.0).unwrap();
            descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.instantiate(&subst);
            // type scheme quantifiers will be updated later on
            let mut node = descr.get_node_mut().unwrap();
            node.instantiate(&subst);
            drop(node);
            let fn_ptr = descr.code.as_ptr();
            module_inst_data.insert(fn_ptr, dicts.clone());
        }

        // Sixth pass, run the borrow checker and elaborate dictionaries.
        for ModuleFunction { name, .. } in functions() {
            let mut node = output.get_own_function_node_mut(name.0).unwrap();
            node.check_borrows()?;
            let ctx = DictElaborationCtx::new(&dicts, Some(&module_inst_data), trait_impls);
            node.elaborate_dictionaries(ctx)?;
        }

        // Seventh pass, normalize the input types, substitute the types in the functions and input/output types.
        let subst = (normalize_types(&mut quantifiers), HashMap::new());
        trait_output.input_tys = instantiate_types(&trait_output.input_tys, &subst);
        trait_output.output_tys = instantiate_types(&trait_output.output_tys, &subst);
        trait_output.constraints = constraints
            .into_iter()
            .map(|c| c.instantiate(&subst))
            .collect();
        for ModuleFunction { name, .. } in functions() {
            let descr = output.functions.get_mut(&name.0).unwrap();
            descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.instantiate(&subst);
            descr.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
            let eff_quantifiers = descr.definition.ty_scheme.ty.input_effect_vars();
            assert!(eff_quantifiers.is_empty());
            descr.definition.ty_scheme.eff_quantifiers = eff_quantifiers;
            descr.definition.ty_scheme.constraints = trait_output.constraints.clone();
            let mut node = output.get_own_function_node_mut(name.0).unwrap();
            node.instantiate(&subst);
        }

        Ok(Some(trait_output))
    } else {
        // We are emitting normal module functions.

        // Limit each function to its own constants and type variables
        let all_constraints = ty_inf.constraints();
        let mut used_constraints: HashSet<PubTypeConstraintPtr> = HashSet::new();
        for ModuleFunction { name, .. } in functions() {
            let descr = output.functions.get(&name.0).unwrap();
            let node = descr.get_node().unwrap();

            // Clean up constraints and validate them.
            let ConstraintValidationOutput {
                mut quantifiers,
                related_constraints,
                retained_constraints,
                constraint_subst,
            } = validate_and_cleanup_constraints(
                &descr.definition.ty_scheme.ty,
                &all_constraints,
                &node,
                false,
                trait_impls,
            )?;
            let mut constraints: Vec<_> = all_constraints
                .iter()
                .filter(|c| {
                    let ptr = constraint_ptr(c);
                    if related_constraints.contains(&ptr) {
                        used_constraints.insert(ptr);
                    }
                    retained_constraints.contains(&ptr)
                })
                .cloned()
                .collect();
            assert_eq!(constraints.len(), retained_constraints.len());
            drop(node);

            // Substitute the constraint-originating types in the node.
            let mut subst = (constraint_subst, HashMap::new());
            constraints = constraints
                .iter()
                .filter_map(|constraint| {
                    constraint
                        .instantiate_and_drop_if_known_trait(&mut subst, trait_impls)
                        .transpose()
                })
                .collect::<Result<_, _>>()?;
            quantifiers.retain(|ty_var| !subst.0.contains_key(ty_var));
            let descr = output.functions.get_mut(&name.0).unwrap();
            let mut node = descr.get_node_mut().unwrap();
            node.instantiate(&subst);
            drop(node);

            // Write the final type scheme.
            descr.definition.ty_scheme.ty_quantifiers = quantifiers.clone();
            descr.definition.ty_scheme.eff_quantifiers =
                descr.definition.ty_scheme.ty.input_effect_vars();
            descr.definition.ty_scheme.constraints = constraints;
            assert_eq!(
                sorted(descr.definition.ty_scheme.ty_quantifiers_from_signature()),
                sorted(quantifiers)
            );

            // Log the dropped constraints.
            let module_env = ModuleEnv::new(output, others);
            log_dropped_constraints_module(
                name.0,
                &all_constraints,
                &related_constraints,
                &retained_constraints,
                module_env,
            );
        }

        // Safety check: make sure that there are no unused constraints.
        let unused_constraints = all_constraints
            .iter()
            .filter(|c| !used_constraints.contains(&constraint_ptr(c)) && !c.is_type_has_variant())
            .collect::<Vec<_>>();
        if !unused_constraints.is_empty() {
            let module_env = ModuleEnv::new(output, others);
            let constraints = unused_constraints
                .iter()
                .map(|c| c.format_with(&module_env))
                .join(" ∧ ");
            return Err(internal_compilation_error!(Internal(format!(
                "Unused constraints in module compilation: {}",
                constraints
            ))));
        }

        // Sixth pass, run the borrow checker and elaborate dictionaries.
        let mut module_inst_data = HashMap::new();
        for ModuleFunction { name, .. } in functions() {
            let descr = output.functions.get_mut(&name.0).unwrap();
            let fn_ptr = descr.code.as_ptr();
            let dicts = descr.definition.ty_scheme.extra_parameters();
            module_inst_data.insert(fn_ptr, dicts);
        }
        for ModuleFunction { name, .. } in functions() {
            let descr = output.functions.get_mut(&name.0).unwrap();
            let mut code = descr.code.borrow_mut();
            let fn_ptr = descr.code.as_ptr();
            let dicts = module_inst_data.get(&fn_ptr).unwrap();
            let node = &mut code.as_script_mut().unwrap().code;
            node.check_borrows()?;
            let ctx = DictElaborationCtx::new(dicts, Some(&module_inst_data), trait_impls);
            node.elaborate_dictionaries(ctx)?;
        }

        // Seventh pass, normalize the type schemes, substitute the types in the functions.
        for ModuleFunction { name, .. } in functions() {
            let descr = output.functions.get_mut(&name.0).unwrap();
            // Note: after that normalization, the functions do not share the same
            // type variables anymore.
            let subst = descr.definition.ty_scheme.normalize();
            let mut node = descr.get_node_mut().unwrap();
            node.instantiate(&subst);
        }

        Ok(None)
    }
}

/// Check all unbound variables from unbound that are not in bounds,
/// and if they are not only seen in variants, return an error.
fn check_unbounds(
    unbound: IndexMap<TypeVar, ir::UnboundTyCtxs>,
    bounds: &[TypeVar],
) -> Result<HashSet<TypeVar>, InternalCompilationError> {
    let mut uninstantiated_unbound = HashSet::new();
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
    pub expr: ir::Node,
    pub ty: TypeScheme<Type>,
    pub locals: Vec<Local>,
}

/// Emit IR for an expression
/// Return the compiled expression and any remaining external constraints
/// referring to lower-generation type variables.
/// Note: the expression might not be safe to use if it has unbound constraints or type variables.
pub fn emit_expr_unsafe(
    source: ast::PExpr,
    module_env: ModuleEnv,
    locals: Vec<Local>,
) -> Result<CompiledExpr, InternalCompilationError> {
    // Make sure that the locals' types have no type variables in them
    assert!(
        locals
            .iter()
            .all(|local| local.ty.inner_ty_vars().is_empty()),
        "Locals passed to expression compilation must not contain type variables"
    );

    // Create a list of all available trait implementations.
    let mut trait_impls = module_env.collect_trait_impls();

    // First desugar the expression.
    let source = source.desugar_with_empty_ctx()?;

    // Infer the expression with the existing locals.
    let initial_local_count = locals.len();
    let mut ty_env = TypingEnv::new(locals, module_env);
    let mut ty_inf = TypeInference::new();
    let (mut node, _) = ty_inf.infer_expr(&mut ty_env, &source)?;
    let mut locals = ty_env.get_locals_and_drop();
    ty_inf.log_debug_constraints(module_env);

    // Perform the unification.
    let mut ty_inf = ty_inf.unify(&mut trait_impls)?;
    ty_inf.log_debug_substitution_tables(module_env);

    // Substitute the result of the unification.
    ty_inf.substitute_in_node(&mut node);
    for local in locals.iter_mut().skip(initial_local_count) {
        local.ty = ty_inf.substitute_in_type(local.ty);
    }

    // Get the remaining constraints and collect the free variables.
    ty_inf.log_debug_constraints(module_env);
    let mut constraints = ty_inf.constraints();

    // Clean-up constraints and validate them.
    let ConstraintValidationOutput {
        mut quantifiers,
        retained_constraints,
        constraint_subst,
        ..
    } = validate_and_cleanup_constraints(&node.ty, &constraints, &node, true, &trait_impls)?;
    log_dropped_constraints_expr(
        &constraints,
        &retained_constraints,
        &constraint_subst,
        module_env,
    );
    constraints.retain(|c| retained_constraints.contains(&constraint_ptr(c)));
    assert_eq!(constraints.len(), retained_constraints.len());

    // Apply the constraint-originating substitution.
    let mut subst = (constraint_subst, HashMap::new());
    let mut progress = true;
    while progress {
        progress = false;
        let mut new_constraints = Vec::new();
        for constraint in constraints.iter() {
            if let Some(new_constraint) =
                constraint.instantiate_and_drop_if_known_trait(&mut subst, &mut trait_impls)?
            {
                new_constraints.push(new_constraint);
            } else {
                progress = true;
            }
        }
        constraints = new_constraints;
    }
    node.instantiate(&subst);
    quantifiers.retain(|ty_var| !subst.0.contains_key(ty_var));
    for local in locals.iter_mut().skip(initial_local_count) {
        local.ty = local.ty.instantiate(&subst);
    }

    // Normalize the type scheme
    let mut ty_scheme = TypeScheme {
        ty: node.ty,
        eff_quantifiers: node.ty.inner_effect_vars(),
        ty_quantifiers: quantifiers,
        constraints,
    };
    let mut subst = ty_scheme.normalize();

    // Remove output effects of the expression (i.e. not in the type of the expression).
    for effect in node.effects.iter() {
        if let Some(var) = effect.as_variable() {
            if !subst.1.contains_key(var) {
                subst.1.insert(*var, EffType::empty());
            }
        }
    }

    // Substitute the normalized and constraint-originating types in the node, effects and locals.
    node.instantiate(&subst);
    ty_scheme.ty = ty_scheme.ty.instantiate(&subst);
    for local in locals.iter_mut().skip(initial_local_count) {
        local.ty = local.ty.instantiate(&subst);
    }

    // Do borrow checking and dictionary elaboration.
    node.check_borrows()?;
    let dicts = ty_scheme.extra_parameters();
    let ctx = DictElaborationCtx::new(&dicts, None, &mut trait_impls);
    node.elaborate_dictionaries(ctx)?;

    Ok(CompiledExpr {
        expr: node,
        ty: ty_scheme,
        locals,
    })
}

/// Emit IR for an expression, and fails if there are any unbound type variables or constraints.
pub fn emit_expr(
    source: ast::PExpr,
    module_env: ModuleEnv,
    locals: Vec<Local>,
) -> Result<CompiledExpr, InternalCompilationError> {
    let span = source.span;
    let CompiledExpr { ty, expr, locals } = emit_expr_unsafe(source, module_env, locals)?;
    let ty_vars = ty.ty.inner_ty_vars();
    if !ty_vars.is_empty() {
        return Err(internal_compilation_error!(UnboundTypeVar {
            ty_var: ty_vars[0],
            ty: ty.ty,
            span,
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

/// Filter constraints that contain at least of the type variables listed in ty_vars
#[allow(dead_code)]
fn select_constraints_any_of_these_ty_vars(
    constraints: &[PubTypeConstraint],
    ty_vars: &[TypeVar],
) -> Vec<PubTypeConstraint> {
    constraints
        .iter()
        .filter(|constraint| constraint.contains_any_ty_vars(ty_vars))
        .cloned()
        .collect()
}

/// Filter constraints that contain only type variables listed in the ty_vars
fn select_constraints_only_these_ty_vars<'c>(
    constraints: &'c [PubTypeConstraint],
    ty_vars: &[TypeVar],
) -> Vec<&'c PubTypeConstraint> {
    constraints
        .iter()
        .filter(|constraint| {
            constraint.is_have_trait() || constraint.contains_only_ty_vars(ty_vars)
        })
        .collect()
}

/// Return the constraints that are transitively accessible from the ty_vars
fn select_constraints_accessible_from<'c: 'r, 'r, C, T>(
    constraints: &'r C,
    ty_vars: &[TypeVar],
) -> (
    HashSet<&'c PubTypeConstraint>,
    HashSet<&'c PubTypeConstraint>,
)
where
    &'r C: IntoIterator<Item = &'c T>,
    T: Borrow<PubTypeConstraint> + 'c,
{
    // Split the constraints into those that contain at least one of the ty_vars and those that don't.
    fn partition<'c: 'r, 'r, C, T>(
        constraints: &'r C,
        ty_vars: &[TypeVar],
    ) -> (
        HashSet<&'c PubTypeConstraint>,
        HashSet<&'c PubTypeConstraint>,
    )
    where
        &'r C: IntoIterator<Item = &'c T>,
        T: Borrow<PubTypeConstraint> + 'c,
    {
        constraints
            .into_iter()
            .map(|item| item.borrow())
            .partition(|constraint| constraint.contains_any_ty_vars(ty_vars))
    }

    // First partition with the input ty_vars.
    let (mut ins, mut outs) = partition(constraints, ty_vars);

    // As long as there is progress, loop.
    loop {
        // Collect the type variables that are accessible from the constraints in ins.
        let accessible_ty_vars: Vec<_> = ins
            .iter()
            .flat_map(|c| c.inner_ty_vars())
            .unique()
            .collect();

        // Re-partition with the new type variables.
        let (new_ins, new_outs) = partition(constraints, &accessible_ty_vars);

        // In case we did not collect any new constraints, we are done.
        if new_ins.len() == ins.len() {
            break;
        }
        ins = new_ins;
        outs = new_outs;
    }
    (ins, outs)
}

/// Partition the orphan variant constraints and the others, and for the variant constraints,
/// create a substitution into a minimalist variant type.
fn partition_variant_constraints(
    constraints: &HashSet<&PubTypeConstraint>,
) -> (TypeSubstitution, HashSet<PubTypeConstraintPtr>) {
    // First, collect the type variables that are invalid for variant simplification.
    let mut invalid_ty_vars = HashSet::<TypeVar>::new();
    for constraint in constraints {
        if let Some(has_variant) = constraint.as_type_has_variant() {
            invalid_ty_vars.extend(has_variant.3.inner_ty_vars())
        } else if !constraint.is_have_trait() {
            invalid_ty_vars.extend(constraint.inner_ty_vars());
        }
    }

    // Then, extract the variant constraints and partition them by type variable,
    // if the type variable is not in invalid_ty_vars.
    let mut variants: HashMap<TypeVar, VariantConstraint> = HashMap::new();
    let mut others = HashSet::new();
    for constraint in constraints {
        match constraint {
            PubTypeConstraint::TypeHasVariant {
                variant_ty,
                tag,
                payload_ty,
                ..
            } => {
                if let Some(ty_var) = variant_ty.data().as_variable() {
                    if !invalid_ty_vars.contains(ty_var) {
                        let existing = variants
                            .entry(*ty_var)
                            .or_default()
                            .insert(*tag, *payload_ty);
                        assert!(existing.is_none(), "Duplicate variant constraint for {tag}");
                    } else {
                        others.insert(constraint_ptr(constraint));
                    }
                } else {
                    others.insert(constraint_ptr(constraint));
                }
            }
            _ => {
                others.insert(constraint_ptr(constraint));
            }
        }
    }

    // And create minimalist variant type for them.
    let subst = variants
        .into_iter()
        .map(|(ty_var, variant)| {
            let variant_ty = Type::variant(variant.into_iter().collect::<Vec<_>>());
            (ty_var, variant_ty)
        })
        .collect();
    (subst, others)
}

type PubTypeConstraintPtr = *const PubTypeConstraint;

fn constraint_ptr(c: &PubTypeConstraint) -> PubTypeConstraintPtr {
    c as *const PubTypeConstraint
}

struct ConstraintValidationOutput {
    quantifiers: Vec<TypeVar>,
    related_constraints: HashSet<PubTypeConstraintPtr>,
    retained_constraints: HashSet<PubTypeConstraintPtr>,
    constraint_subst: TypeSubstitution,
}

fn validate_and_cleanup_constraints(
    ty: &impl TypeLike,
    constraints: &[PubTypeConstraint],
    node: &Node,
    is_expr: bool,
    trait_impls: &TraitImpls,
) -> Result<ConstraintValidationOutput, InternalCompilationError> {
    // Filter out constraints that have types not found in our code.
    let unbound = node.all_unbound_ty_vars();
    // let ty_vars = unbound.keys().cloned().collect::<Vec<_>>();
    // let constraints = select_constraints_only_these_ty_vars(constraints, &ty_vars);
    let constraints = constraints.iter().collect::<Vec<_>>();
    let related_constraints = constraints.iter().map(|c| constraint_ptr(c)).collect();

    let (constraints, subst) = if is_expr {
        // An expression, keep all constraints
        let (subst, other_constraints) =
            partition_variant_constraints(&constraints.iter().copied().collect());
        let constraints = constraints
            .iter()
            .copied()
            .filter(|c| other_constraints.contains(&constraint_ptr(c)))
            .collect();
        (constraints, subst)
    } else {
        // A module function, find constraints that are not transitively accessible from the fn signature.
        let sig_ty_vars = ty.inner_ty_vars();
        let (constraints, orphan_constraints) =
            select_constraints_accessible_from(&constraints, &sig_ty_vars);

        // Partition the orphan constraints into variant constraint substitutions and the others.
        let (mut subst, mut other_orphans) = partition_variant_constraints(&orphan_constraints);

        // Default Num types to Int or Float in other orphan constraints.
        compute_num_trait_default_types(
            &orphan_constraints,
            &mut other_orphans,
            &mut subst,
            trait_impls,
        );
        if !other_orphans.is_empty() {
            return Err(internal_compilation_error!(Internal(format!(
                "Orphan constraints found: {other_orphans:?}"
            ))));
        }
        (constraints, subst)
    };

    // Compute the quantifiers based on the function type and its constraints.
    let mut quantifiers = TypeScheme::list_ty_vars(ty, constraints.iter().map(Borrow::borrow));

    // Detect unbound type variables in the code and return error if not in unused variants only.
    // These are neither part of the function signature nor of the constraints.
    let bounds: Vec<_> = quantifiers.iter().chain(subst.keys()).cloned().collect();
    let uninstantiated_unbound = check_unbounds(unbound, &bounds)?;
    let mut constraint_subst: HashMap<_, _> = subst
        .into_iter()
        .chain(
            uninstantiated_unbound
                .into_iter()
                .map(|ty_var| (ty_var, Type::never())),
        )
        .collect();
    let mut retained_constraints: HashSet<_> =
        constraints.iter().map(|c| constraint_ptr(c)).collect();

    // In expressions, default Num types to Int or Float if not specified.
    if is_expr {
        compute_num_trait_default_types(
            &constraints,
            &mut retained_constraints,
            &mut constraint_subst,
            trait_impls,
        );
    }

    // Simplify quantifiers with substitution
    quantifiers.retain(|ty_var| !constraint_subst.contains_key(ty_var));

    Ok(ConstraintValidationOutput {
        quantifiers,
        related_constraints,
        retained_constraints,
        constraint_subst,
    })
}

fn validate_and_simplify_trait_imp_constraints(
    input_quantifiers: &[TypeVar],
    constraints: &Vec<PubTypeConstraint>,
    trait_impls: &TraitImpls,
) -> Result<(Vec<TypeVar>, TypeSubstitution), InternalCompilationError> {
    // Find constraints that are not transitively accessible from the trait signature.
    let (constraints, orphan_constraints) =
        select_constraints_accessible_from(constraints, input_quantifiers);

    // Partition the orphan constraints into variant constraint substitutions and the others.
    let (mut subst, mut other_orphans) = partition_variant_constraints(&orphan_constraints);

    // Default Num types to Int or Float in other orphan constraints.
    compute_num_trait_default_types(
        &orphan_constraints,
        &mut other_orphans,
        &mut subst,
        trait_impls,
    );
    if !other_orphans.is_empty() {
        return Err(internal_compilation_error!(Internal(format!(
            "Orphan constraints found: {other_orphans:?}"
        ))));
    }

    // Compute quantifiers based on the trait signature and its constraints.
    let mut quantifiers = input_quantifiers.to_vec();
    let mut collector = TyVarsCollector(&mut quantifiers);
    for constraint in constraints.iter() {
        constraint.visit(&mut collector);
    }
    quantifiers = quantifiers.into_iter().unique().collect();

    Ok((quantifiers, subst))
}

/// Compute which constraints in selected_constraints can be defaulted to int or float.
/// Update both selected_constraints and subst.
fn compute_num_trait_default_types(
    all_constraints: &HashSet<&PubTypeConstraint>,
    selected_constraints: &mut HashSet<PubTypeConstraintPtr>,
    subst: &mut TypeSubstitution,
    trait_impls: &TraitImpls,
) {
    // In debug, check that all_constraints contains all selected_constraints.
    #[cfg(debug_assertions)]
    {
        let all_constraints: HashSet<PubTypeConstraintPtr> = all_constraints
            .iter()
            .copied()
            .map(constraint_ptr)
            .collect();
        for constraint in selected_constraints.iter() {
            assert!(all_constraints.contains(constraint));
        }
    }

    // First, collect the type variables that are invalid for defaulting.
    // These include the ones that appear in non-trait constraints or in traits with
    // more than one input types or having output types.
    let mut invalid_ty_vars = HashSet::<TypeVar>::new();
    let mut num_ty_vars = HashSet::<TypeVar>::new();
    for constraint in all_constraints {
        if !selected_constraints.contains(&constraint_ptr(constraint)) {
            continue;
        }
        if let Some(have_trait) = constraint.as_have_trait() {
            assert!(!have_trait.1.is_empty());
            if have_trait.1.len() > 1 {
                invalid_ty_vars.extend(have_trait.1.iter().flat_map(|ty| ty.inner_ty_vars()));
            } else if have_trait.0 == &*NUM_TRAIT {
                let maybe_ty_var = have_trait.1[0].data().as_variable().cloned();
                if let Some(ty_var) = maybe_ty_var {
                    num_ty_vars.insert(ty_var);
                }
            }
            invalid_ty_vars.extend(have_trait.2.iter().flat_map(|ty| ty.inner_ty_vars()));
        } else {
            invalid_ty_vars.extend(constraint.inner_ty_vars());
        }
    }

    // Then, decide which type variables can be default and whether to int or float.
    // The value of the default_tys map holds the index of the type to default to.
    // If the index is default_tys.len(), there is no default.
    let default_tys = [int_type(), float_type()];
    let mut defaulted_ty_vars = HashMap::<TypeVar, usize>::new();
    // Process trait constraint type variables.
    for constraint in all_constraints.iter() {
        if !selected_constraints.contains(&constraint_ptr(constraint)) {
            continue;
        }
        if let Some(have_trait) = constraint.as_have_trait() {
            if have_trait.1.len() > 1 || !have_trait.2.is_empty() {
                continue;
            }
            let maybe_ty_var = have_trait.1[0].data().as_variable().cloned();
            if let Some(ty_var) = maybe_ty_var {
                if invalid_ty_vars.contains(&ty_var) {
                    continue;
                }
                if !num_ty_vars.contains(&ty_var) {
                    continue;
                }
                let mut default_index = defaulted_ty_vars.get(&ty_var).copied().unwrap_or(0);
                while default_index < default_tys.len() && {
                    let key = (have_trait.0.clone(), vec![default_tys[default_index]]);
                    !trait_impls.concrete().contains_key(&key)
                } {
                    default_index += 1;
                    if default_index >= default_tys.len() {
                        break;
                    }
                }
                defaulted_ty_vars.insert(ty_var, default_index);
            }
        }
    }

    // Finally, remove the defaulted constraints and update the substitution with the valid default types.
    for constraint in all_constraints.iter() {
        if !selected_constraints.contains(&constraint_ptr(constraint)) {
            continue;
        }
        if let Some(have_trait) = constraint.as_have_trait() {
            if have_trait.1.len() > 1 || !have_trait.2.is_empty() {
                continue;
            }
            let maybe_ty_var = have_trait.1[0].data().as_variable().cloned();
            if let Some(ty_var) = maybe_ty_var {
                if let Some(default_index) = defaulted_ty_vars.get(&ty_var) {
                    if *default_index < default_tys.len() {
                        selected_constraints.remove(&constraint_ptr(constraint));
                    }
                }
            }
        }
    }
    for (ty_var, default_ty_index) in defaulted_ty_vars {
        let default_ty = default_tys.get(default_ty_index);
        if let Some(default_ty) = default_ty {
            subst
                .entry(ty_var)
                .and_modify(|prev_ty| {
                    panic!("Type variable {ty_var} already exists in type substitution with type {prev_ty:?}, trying to use type {default_ty:?} instead")
                })
                .or_insert(*default_ty);
        }
    }
}

fn log_dropped_constraints_expr(
    all: &[PubTypeConstraint],
    retained: &HashSet<PubTypeConstraintPtr>,
    subst: &TypeSubstitution,
    module_env: ModuleEnv,
) {
    if retained.len() == all.len() {
        return;
    }
    let mut ty_vars_in_dropped = HashSet::new();
    let dropped = all
        .iter()
        .filter(|c| {
            let ptr = constraint_ptr(c);
            let dropped = !retained.contains(&ptr);
            if dropped {
                ty_vars_in_dropped.extend(c.inner_ty_vars());
            }
            dropped
        })
        .map(|c| c.format_with(&module_env));
    let dropped = iterable_to_string(dropped, " ∧ ");
    log::debug!("Dropped/resolved constraints in expr: {dropped}");
    for (ty_var, ty) in subst {
        if ty_vars_in_dropped.contains(ty_var) {
            log::debug!(
                "  Type variable {ty_var} resolved to {}",
                ty.format_with(&module_env)
            );
        }
    }
}

fn log_dropped_constraints_module(
    ctx: Ustr,
    all: &[PubTypeConstraint],
    related: &HashSet<PubTypeConstraintPtr>,
    retained: &HashSet<PubTypeConstraintPtr>,
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
