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
    FxHashMap, FxHashSet, Location, Modules,
    ast::{PExprArena, PExprId},
    compiler::{CompilationCapabilities, error::InternalCompilationError},
    desugar::desugar_expr_with_empty_ctx,
    hir::{self, UNodeArena},
    hir::{
        borrow_checker::check_elaborated_borrows,
        dictionary::DictElaborationCtx,
        elaboration::{elaborate_generated_functions, elaborate_hir},
        emit_functions::check_unbounds,
        emit_hir::{
            PendingModuleFunctions, PubTypeConstraintPtr, add_pending_function_anonymous,
            borrow_check_and_elaborate_pending_function, constraint_ptr,
            log_dropped_constraints_expr,
        },
        value_dispatch::elaborate_local_ownership_and_value_dispatches,
    },
    internal_compilation_error,
    module::{
        ELocalDecl, GENERATED_LAMBDA_PREFIX, LocalDecl, LocalDeclId, LocalFunctionId, Module,
        ModuleEnv, ModuleFunction, ModuleId, PendingGeneratedStructuralProjectionSubscripts,
        Visibility, id::Id,
    },
    types::{
        effects::EffType,
        trait_solver::{TraitSolver, trait_solver_from_module},
        r#type::{CallResultConvention, FnType, Type, TypeInstSubst, TypeVar},
        type_inference::{
            defaulting::DefaultingScope, expr::TypeInference, unify::UnifiedTypeInference,
        },
        type_like::TypeLike,
        type_mapper::BitmapInstantiationMapper,
        type_scheme::{PubTypeConstraint, TypeScheme},
        typing_env::TypingEnv,
    },
};

use log::log_enabled;

/// Expression HIR awaiting registration as a module function.
#[derive(Debug)]
struct PendingExprEntry {
    expr: hir::ENodeId,
    ty: TypeScheme<Type>,
    locals: Vec<ELocalDecl>,
}

#[derive(Debug, Clone, Copy)]
struct ExprEmissionOptions {
    capabilities: CompilationCapabilities,
    private_impl_module: Option<ModuleId>,
}

impl PendingExprEntry {
    /// Register this expression as a private function whose leading locals are runtime arguments.
    ///
    /// Expression emission still uses a small temporary result while inference and elaboration are
    /// in progress. Published compilation results expose only the returned function identity.
    fn into_entry_with_runtime_args(
        self,
        module: &mut Module,
        runtime_arg_count: usize,
    ) -> LocalFunctionId {
        use crate::{
            containers::b,
            hir::function::{ScriptFunction, arg_conventions_for_args},
        };

        let effects = module.hir_arena[self.expr].effects.clone();
        let argument_locals = &self.locals[..runtime_arg_count];
        let arguments = argument_locals
            .iter()
            .map(ELocalDecl::as_fn_arg_type)
            .collect::<Vec<_>>();
        let argument_names = argument_locals
            .iter()
            .map(|local| local.name.0)
            .collect::<Vec<_>>();
        let parameter_passing = arg_conventions_for_args(&arguments);
        let definition = hir::function::CallableDefinition::new(
            TypeScheme::new_infer_quantifiers_with_constraints(
                FnType::new(arguments, self.ty.ty, effects),
                self.ty.constraints,
            ),
            argument_names,
            None,
        );
        let function = ModuleFunction::new_elaborated(
            definition,
            b(ScriptFunction::new(self.expr, runtime_arg_count)),
            parameter_passing,
            None,
            self.locals,
        );
        module.add_function_with_visibility(ustr::ustr("<expr>"), function, Visibility::Module)
    }
}

/// Emit HIR for an expression and return its root node.
/// Note: the expression might not be safe to use if it has unbound constraints or type variables.
pub fn emit_expr_unsafe(
    source: PExprId,
    parsed_arena: &PExprArena,
    module: &mut Module,
    others: &Modules,
    locals: Vec<LocalDecl>,
) -> Result<hir::ENodeId, InternalCompilationError> {
    emit_expr_unsafe_with_options(
        source,
        parsed_arena,
        module,
        others,
        locals,
        ExprEmissionOptions {
            capabilities: CompilationCapabilities::default(),
            private_impl_module: None,
        },
    )
    .map(|pending| pending.expr)
}

fn emit_expr_unsafe_with_options(
    source: PExprId,
    parsed_arena: &PExprArena,
    module: &mut Module,
    others: &Modules,
    locals: Vec<LocalDecl>,
    options: ExprEmissionOptions,
) -> Result<PendingExprEntry, InternalCompilationError> {
    let mut expr_arena = UNodeArena::default();
    emit_expr_unsafe_inner(
        source,
        parsed_arena,
        module,
        others,
        locals,
        &mut expr_arena,
        options,
    )
}

fn emit_expr_unsafe_inner(
    source: PExprId,
    parsed_arena: &PExprArena,
    module: &mut Module,
    others: &Modules,
    mut locals: Vec<LocalDecl>,
    expr_arena: &mut UNodeArena,
    options: ExprEmissionOptions,
) -> Result<PendingExprEntry, InternalCompilationError> {
    let ExprEmissionOptions {
        capabilities,
        private_impl_module,
    } = options;
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
    let mut new_deps = FxHashSet::default();
    let mut lambda_functions = vec![];
    let mut pending_functions = PendingModuleFunctions::default();
    LocalDecl::assign_sequential_slots(&mut locals);
    let cur_locals = (0..locals.len()).map(LocalDeclId::from_index).collect();
    let mut ty_env = TypingEnv::new(
        &mut locals,
        cur_locals,
        &mut new_deps,
        module_env,
        None,
        CallResultConvention::Value,
        None,
        vec![],
        true,
        &mut lambda_functions,
        module.functions.len() as u32,
        &desugared_arena,
        expr_arena,
    );
    ty_env.compilation_capabilities = capabilities;
    let mut ty_inf = TypeInference::new_empty();
    let (node_id, _) = ty_inf.infer_expr(&mut ty_env, source)?;
    let mut locals = mem::take(&mut locals);
    ty_inf.log_debug_constraints(module_env);
    let lambda_functions = lambda_functions
        .drain(..)
        .map(|function| {
            let id = add_pending_function_anonymous(module, &mut pending_functions, function);
            module.name_function_with_visibility(
                id,
                format!("{GENERATED_LAMBDA_PREFIX}{}", id.as_index()).into(),
                Visibility::Module,
            );
            id
        })
        .collect::<Vec<_>>();
    module.deps.extend(new_deps);
    module.deps.extend(modules_used);

    // Perform the unification.
    let mut solver = trait_solver_from_module!(module, others);
    if let Some(module_id) = private_impl_module {
        solver.allow_private_impls_from(module_id);
    }
    let mut ty_inf = ty_inf.unify(&mut solver, expr_arena)?;
    let generated = solver.commit(
        &mut module.functions,
        &mut module.def_table,
        &mut pending_functions,
    );
    elaborate_generated_functions(module, others, &mut pending_functions, generated)?;
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
        ty_inf.resolve_local_storage_and_activate_value_constraints(
            &descr.code.arena,
            descr.code.entry_node_id,
            &mut descr.locals,
            value_trait_id,
        );
    }
    ty_inf.resolve_local_storage_and_activate_value_constraints(
        expr_arena,
        node_id,
        &mut locals,
        value_trait_id,
    );

    // Default constraints into the unification tables (pre-substitution).
    // For expressions, iterate defaulting and re-solving to a fixed point.
    {
        let node_ty = ty_inf.substitute_in_type(expr_arena[node_id].ty);
        let mut solver = trait_solver_from_module!(module, others);
        if let Some(module_id) = private_impl_module {
            solver.allow_private_impls_from(module_id);
        }
        let orphan_constraints = ty_inf.remaining_constraints().to_vec();
        let unit_variant_seed_tys =
            UnifiedTypeInference::collect_unit_variant_seed_types(expr_arena, node_id);
        let scope = DefaultingScope::from_constraints(&orphan_constraints)
            .with_expr_root_ty(node_ty)
            .with_unit_variant_seed_tys(unit_variant_seed_tys);
        ty_inf.resolve_defaults_to_fixed_point(&scope, &mut solver, expr_arena)?;
        let generated = solver.commit(
            &mut module.functions,
            &mut module.def_table,
            &mut pending_functions,
        );
        elaborate_generated_functions(module, others, &mut pending_functions, generated)?;
    }

    // Substitute everything using ty_inf (single pass, includes all defaults).
    ty_inf.substitute_in_node(expr_arena, node_id);
    for lambda_id in lambda_functions.iter() {
        let descr = pending_functions
            .get_mut(lambda_id)
            .expect("expected pending function body");
        ty_inf.substitute_in_pending_module_function(descr);
        module.functions[lambda_id.as_index()].definition = descr.definition.clone();
    }
    ty_inf.substitute_in_local_decls_in_place(&mut locals[initial_local_count..]);

    // Take final substituted constraints.
    let module_env = ModuleEnv::new(module, others);
    ty_inf.log_debug_constraints(module_env);
    ty_inf.normalize_remaining_constraints();
    let all_constraints = ty_inf.take_constraints();

    // Compute quantifiers from the node type and remaining constraints.
    let node_ty = expr_arena[node_id].ty;
    let mut quantifiers = TypeScheme::list_ty_vars(&node_ty, all_constraints.iter());

    // Check for unbound type variables.
    let unbound = hir::all_unbound_ty_vars(expr_arena, node_id);
    let uninstantiated_unbound = check_unbounds(unbound, &quantifiers, &module_env)?;

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
        hir::instantiate_node_in_place(expr_arena, node_id, &mut mapper);
        for lambda_id in lambda_functions.iter() {
            let descr = &mut module.functions[lambda_id.as_index()];
            descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
            let pending = pending_functions
                .get_mut(lambda_id)
                .expect("expected pending function body");
            pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
            hir::instantiate_node_in_place(
                &mut pending.code.arena,
                pending.code.entry_node_id,
                &mut mapper,
            );
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
    if let Some(module_id) = private_impl_module {
        solver.allow_private_impls_from(module_id);
    }
    let mut drop_subst = fixup_subst;
    let mut constraints: Vec<_> = all_constraints
        .iter()
        .filter_map(|constraint| {
            constraint
                .instantiate_and_drop_if_solved(&mut drop_subst, &mut solver, expr_arena)
                .transpose()
        })
        .collect::<Result<_, _>>()?;
    // Loop to drop constraints that become solved due to output type resolution.
    let mut progress = true;
    while progress {
        progress = false;
        let mut new_constraints = Vec::new();
        for constraint in constraints.iter() {
            if let Some(new_constraint) = constraint.instantiate_and_drop_if_solved(
                &mut drop_subst,
                &mut solver,
                expr_arena,
            )? {
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
        hir::instantiate_node_in_place(expr_arena, node_id, &mut mapper);
        for lambda_id in lambda_functions.iter() {
            let descr = &mut module.functions[lambda_id.as_index()];
            descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
            let pending = pending_functions
                .get_mut(lambda_id)
                .expect("expected pending function body");
            pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
            hir::instantiate_node_in_place(
                &mut pending.code.arena,
                pending.code.entry_node_id,
                &mut mapper,
            );
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
    elaborate_generated_functions(module, others, &mut pending_functions, generated)?;

    // Log dropped constraints.
    if log_enabled!(log::Level::Trace) {
        let module_env = ModuleEnv::new(module, others);
        let retained_ptrs: FxHashSet<PubTypeConstraintPtr> =
            constraints.iter().map(constraint_ptr).collect();
        log_dropped_constraints_expr(&all_constraints, &retained_ptrs, module_env);
    }

    // Normalize the type scheme.
    let node_ty = expr_arena[node_id].ty;
    let mut ty_scheme = TypeScheme {
        ty: node_ty,
        eff_quantifiers: node_ty.inner_effect_vars(),
        ty_quantifiers: quantifiers,
        constraints,
    };
    let mut subst = ty_scheme.normalize();

    // Remove output effects of the expression (i.e. not in the type of the expression).
    for effect in expr_arena[node_id].effects.iter() {
        if let Some(var) = effect.as_variable() {
            if !subst.1.contains_key(var) {
                subst.1.insert(*var, EffType::empty());
            }
        }
    }

    // Substitute the normalized types in the node, effects and locals.
    let mut mapper = BitmapInstantiationMapper::new(&subst);
    hir::instantiate_node_in_place(expr_arena, node_id, &mut mapper);
    for lambda_id in lambda_functions.iter() {
        let descr = &mut module.functions[lambda_id.as_index()];
        descr.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.map(&mut mapper);
        let pending = pending_functions
            .get_mut(lambda_id)
            .expect("expected pending function body");
        pending.definition.ty_scheme.ty = descr.definition.ty_scheme.ty.clone();
        hir::instantiate_node_in_place(
            &mut pending.code.arena,
            pending.code.entry_node_id,
            &mut mapper,
        );
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
    let generated_projection_subscripts =
        PendingGeneratedStructuralProjectionSubscripts::new(module);
    let mut solver = trait_solver_from_module!(module, &others);
    if let Some(module_id) = private_impl_module {
        solver.allow_private_impls_from(module_id);
    }
    let mut ctx = DictElaborationCtx::new_with_generated_projection_subscripts(
        &dicts,
        None,
        &mut solver,
        generated_projection_subscripts,
    );
    elaborate_local_ownership_and_value_dispatches(expr_arena, &mut locals, &mut ctx)?;
    let elaborated = elaborate_hir(expr_arena, node_id, &mut module.hir_arena, &mut ctx, locals)?;
    let expr = elaborated.root;
    check_elaborated_borrows(&module.hir_arena, expr)?;
    for lambda_id in lambda_functions.iter() {
        let function_slot = &mut module.functions[lambda_id.as_index()];
        borrow_check_and_elaborate_pending_function(
            function_slot,
            &mut module.hir_arena,
            &mut pending_functions,
            &mut ctx,
            *lambda_id,
        )?;
    }
    let generated_projection_subscripts = ctx.take_generated_projection_subscripts();
    let generated = solver.commit(
        &mut module.functions,
        &mut module.def_table,
        &mut pending_functions,
    );
    if let Some(generated_projection_subscripts) = generated_projection_subscripts {
        generated_projection_subscripts.commit(module, others);
    }
    elaborate_generated_functions(module, others, &mut pending_functions, generated)?;
    for lambda_id in lambda_functions {
        module.functions[lambda_id.as_index()].refresh_debug_info();
    }

    Ok(PendingExprEntry {
        expr,
        ty: ty_scheme,
        locals: elaborated.locals,
    })
}

/// Emit HIR for an expression, failing if there are any unbound type variables or constraints.
/// If the expression imports functions from the module graph, the module's imports are updated.
pub(crate) fn emit_expr_entry_with_capabilities(
    source: PExprId,
    parsed_arena: &PExprArena,
    module: &mut Module,
    others: &Modules,
    locals: Vec<LocalDecl>,
    capabilities: CompilationCapabilities,
) -> Result<LocalFunctionId, InternalCompilationError> {
    let pending = emit_expr_with_options(
        source,
        parsed_arena,
        module,
        others,
        locals,
        ExprEmissionOptions {
            capabilities,
            private_impl_module: None,
        },
    )?;
    Ok(pending.into_entry_with_runtime_args(module, 0))
}

/// Emit an expression with privileged access to one foreign module's private trait impls.
pub(crate) fn emit_expr_entry_with_private_impls(
    source: PExprId,
    parsed_arena: &PExprArena,
    module: &mut Module,
    others: &Modules,
    locals: Vec<LocalDecl>,
    capabilities: CompilationCapabilities,
    private_impl_module: ModuleId,
) -> Result<LocalFunctionId, InternalCompilationError> {
    let runtime_arg_count = locals.len();
    let pending = emit_expr_with_options(
        source,
        parsed_arena,
        module,
        others,
        locals,
        ExprEmissionOptions {
            capabilities,
            private_impl_module: Some(private_impl_module),
        },
    )?;
    Ok(pending.into_entry_with_runtime_args(module, runtime_arg_count))
}

fn emit_expr_with_options(
    source: PExprId,
    parsed_arena: &PExprArena,
    module: &mut Module,
    others: &Modules,
    locals: Vec<LocalDecl>,
    options: ExprEmissionOptions,
) -> Result<PendingExprEntry, InternalCompilationError> {
    let span = parsed_arena[source].span;
    let PendingExprEntry { ty, expr, locals } =
        emit_expr_unsafe_with_options(source, parsed_arena, module, others, locals, options)?;
    validate_safe_expr_type_scheme(&ty, span)?;
    Ok(PendingExprEntry { ty, expr, locals })
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
            PubTypeConstraint::ProjectionSubscriptIs { subscript_ty, .. } => {
                if let Some(unbound) = subscript_ty
                    .inner_ty_vars()
                    .first()
                    .map(|ty_var| (*ty_var, Type::subscript_type(subscript_ty.clone()), span))
                {
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
