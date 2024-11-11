use std::{
    borrow::Borrow,
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use indexmap::IndexMap;
use itertools::Itertools;
use log::log_enabled;
use ustr::Ustr;

use crate::{
    ast::{self, *},
    containers::{iterable_to_string, sorted, B},
    effects::EffType,
    error::InternalCompilationError,
    function::ScriptFunction,
    graph::{find_strongly_connected_components, topological_sort_sccs},
    internal_compilation_error,
    ir::{self, Immediate, Node},
    module::{self, FmtWithModuleEnv, Module, ModuleEnv, Modules},
    mutability::MutType,
    r#type::{FnType, Type, TypeLike, TypeSubstitution, TypeVar},
    type_inference::TypeInference,
    type_scheme::{PubTypeConstraint, TypeScheme, VariantConstraint},
    typing_env::{Local, TypingEnv},
    value::Value,
};

/// Emit IR for the given module
pub fn emit_module(
    source: &ast::Module,
    others: &Modules,
    merge_with: Option<&Module>,
) -> Result<Module, InternalCompilationError> {
    use ir::Node as N;
    use ir::NodeKind as K;

    // Prelude: get the function dependency graph, topologically sort it, and process
    // the functions starting from the leaves.
    let dependency_graph = source.get_function_dependencies();
    let sccs = find_strongly_connected_components(&dependency_graph);
    let sorted_sccs = topological_sort_sccs(&dependency_graph, &sccs);

    // Prepare target module.
    let mut output = merge_with.map_or_else(Module::default, |module| module.clone());
    for mut scc in sorted_sccs.into_iter().rev() {
        scc.sort(); // for compatibility due to bug in effect tracking

        // Process each SCC one by one.
        let functions = || scc.iter().map(|&idx| &source.functions[idx]);
        if log_enabled!(log::Level::Debug) {
            let names = functions().map(|f| f.name.0).collect::<Vec<_>>();
            log::debug!(
                "Processing circularly dependent functions: {}",
                iterable_to_string(names, ", ")
            );
        }

        // First pass, populate the function table and allocate fresh mono type variables.
        let mut ty_inf = TypeInference::default();
        for ModuleFunction {
            name,
            args,
            args_span,
            span,
            ..
        } in functions()
        {
            // Create type and mutability variables for the arguments.
            // Note: the type quantifiers and constraints are left empty.
            // They will be filled in the second pass.
            // The effect quantifiers are filled with the output effect variable.
            let args_ty = ty_inf.fresh_fn_args(args.len());
            let effect_var = ty_inf.fresh_effect_var();
            // log::debug!("Fresh effect variable for {}: {effect_var}", name.0);
            let effects = EffType::single_variable(effect_var);
            let ty_scheme = TypeScheme::new_just_type(FnType::new(
                args_ty,
                ty_inf.fresh_type_var_ty(),
                effects.clone(),
            ));
            // Create dummy code.
            let dummy_code = B::new(ScriptFunction::new(N::new(
                K::Immediate(Immediate::new(Value::unit())),
                Type::unit(),
                effects,
                *span,
            )));
            // Assemble the spans and the description
            let spans = module::ModuleFunctionSpans {
                name: name.1,
                args: args.iter().map(|(_, s)| *s).collect(),
                args_span: *args_span,
                span: *span,
            };
            let descr = module::ModuleFunction {
                ty_scheme,
                code: Rc::new(RefCell::new(dummy_code)),
                spans: Some(spans),
            };
            output.functions.insert(name.0, descr);
        }

        // Second pass, infer types and emit function bodies.
        for function in functions() {
            let name = function.name.0;
            let descr = output.functions.get(&name).unwrap();
            let module_env = ModuleEnv::new(&output, others);
            let mut ty_env = TypingEnv::new(
                descr.ty_scheme.ty.as_locals_no_bound(&function.args),
                module_env,
            );
            let expected_span = descr.spans.as_ref().unwrap().args_span;
            let fn_node = ty_inf.check_expr(
                &mut ty_env,
                &function.body,
                descr.ty_scheme.ty.ret,
                MutType::constant(),
                expected_span,
            )?;
            let descr = output.functions.get_mut(&name).unwrap();
            descr.ty_scheme.ty.effects =
                ty_inf.unify_effects(&fn_node.effects, &descr.ty_scheme.ty.effects);
            *descr.code.borrow_mut() = B::new(ScriptFunction::new(fn_node));
        }
        let module_env = ModuleEnv::new(&output, others);
        ty_inf.log_debug_constraints(module_env);

        // Third pass, perform the unification.
        let mut ty_inf = ty_inf.unify()?;
        ty_inf.log_debug_substitution_tables(module_env);
        ty_inf.log_debug_constraints(module_env);

        // Fourth pass, substitute the mono type variables with the inferred types.
        for ModuleFunction { name, .. } in functions() {
            let descr = output.functions.get_mut(&name.0).unwrap();
            ty_inf.substitute_in_module_function(descr);

            // Union duplicated effects from function arguments, and build a substitution for the
            // fully unioned effects, to removed duplications.
            ty_inf.unify_fn_arg_effects(&descr.ty_scheme.ty);
            let effect_subst = descr
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
            let mut code = descr.code.borrow_mut();
            let node = &mut code.as_script_mut().unwrap().code;
            let subst = (HashMap::new(), effect_subst);
            node.instantiate(&subst);
            descr.ty_scheme.ty = descr.ty_scheme.ty.instantiate(&subst);
        }

        // Fifth pass, get the remaining constraints and collect the free type variables.
        let all_constraints = ty_inf.constraints();
        let mut used_constraints: HashSet<&PubTypeConstraint> = HashSet::new();
        for ModuleFunction { name, .. } in functions() {
            let descr = output.functions.get_mut(&name.0).unwrap();
            let mut code = descr.code.borrow_mut();
            let node = &mut code.as_script_mut().unwrap().code;

            // Clean-up constraints and validate them.
            let ConstraintValidationOutput {
                quantifiers,
                related_constraints,
                retained_constraints,
                constraint_subst,
            } = validate_and_cleanup_constraints(&descr.ty_scheme.ty, &all_constraints, node)?;
            let constraints: Vec<_> = all_constraints
                .iter()
                .filter(|c| {
                    let ptr = constraint_ptr(c);
                    if related_constraints.contains(&ptr) {
                        used_constraints.insert(c);
                    }
                    retained_constraints.contains(&ptr)
                })
                .cloned()
                .collect();
            assert_eq!(constraints.len(), retained_constraints.len());

            // Substitute the constraint-originating types in the node.
            node.instantiate(&(constraint_subst, HashMap::new()));

            // Write the final type scheme.
            descr.ty_scheme.ty_quantifiers = quantifiers.clone();
            descr.ty_scheme.eff_quantifiers = descr.ty_scheme.ty.input_effect_vars();
            descr.ty_scheme.constraints = constraints;
            assert_eq!(
                sorted(descr.ty_scheme.ty_quantifiers_from_signature()),
                sorted(quantifiers)
            );

            // Log the dropped constraints.
            drop(code);
            let module_env = ModuleEnv::new(&output, others);
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
            .filter(|c| !used_constraints.contains(c) && !c.is_type_has_variant())
            .collect::<Vec<_>>();
        if !unused_constraints.is_empty() {
            let module_env = ModuleEnv::new(&output, others);
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
            let dicts = descr.ty_scheme.extra_parameters();
            module_inst_data.insert(fn_ptr, dicts);
        }
        for ModuleFunction { name, .. } in functions() {
            let descr = output.functions.get_mut(&name.0).unwrap();
            let mut code = descr.code.borrow_mut();
            let fn_ptr = descr.code.as_ptr();
            let dicts = module_inst_data.get(&fn_ptr).unwrap();
            let node = &mut code.as_script_mut().unwrap().code;
            node.check_borrows()?;
            node.elaborate_dictionaries(dicts, Some(&module_inst_data));
        }

        // Seventh pass, normalize the type schemes, substitute the types in the functions.
        for ModuleFunction { name, .. } in functions() {
            let descr = output.functions.get_mut(&name.0).unwrap();
            // Note: after that normalization, the functions do not share the same
            // type variables anymore.
            let subst = descr.ty_scheme.normalize();
            let mut code = descr.code.borrow_mut();
            let node = &mut code.as_script_mut().unwrap().code;
            node.instantiate(&subst);
        }
    }

    Ok(output)
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
pub fn emit_expr(
    source: &ast::Expr,
    module_env: ModuleEnv,
    locals: Vec<Local>,
) -> Result<CompiledExpr, InternalCompilationError> {
    // Infer the expression with the existing locals.
    let initial_local_count = locals.len();
    let mut ty_env = TypingEnv::new(locals, module_env);
    let mut ty_inf = TypeInference::new();
    let (mut node, _) = ty_inf.infer_expr(&mut ty_env, source)?;
    let mut locals = ty_env.get_locals_and_drop();
    ty_inf.log_debug_constraints(module_env);

    // Perform the unification.
    let mut ty_inf = ty_inf.unify()?;
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
        quantifiers,
        retained_constraints,
        constraint_subst,
        ..
    } = validate_and_cleanup_constraints(&node.ty, &constraints, &node)?;
    log_dropped_constraints_expr(&constraints, &retained_constraints, module_env);
    constraints.retain(|c| retained_constraints.contains(&constraint_ptr(c)));
    assert_eq!(constraints.len(), retained_constraints.len());

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
    subst.0.extend(constraint_subst);
    node.instantiate(&subst);
    for local in locals.iter_mut().skip(initial_local_count) {
        local.ty = local.ty.instantiate(&subst);
    }

    // Do borrow checking and dictionary elaboration.
    node.check_borrows()?;
    let dicts = ty_scheme.extra_parameters();
    node.elaborate_dictionaries(&dicts, None);

    Ok(CompiledExpr {
        expr: node,
        ty: ty_scheme,
        locals,
    })
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
        .filter(|constraint| constraint.contains_only_ty_vars(ty_vars))
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
fn partition_variant_constraints<'c>(
    constraints: impl Iterator<Item = &'c PubTypeConstraint>,
) -> (TypeSubstitution, Vec<&'c PubTypeConstraint>) {
    // Extract the variant constraints and partition them by type variable.
    let mut variants: HashMap<TypeVar, VariantConstraint> = HashMap::new();
    let mut others = Vec::new();
    for constraint in constraints {
        match constraint {
            PubTypeConstraint::TypeHasVariant {
                variant_ty,
                tag,
                payload_ty,
                ..
            } => {
                if let Some(ty_var) = variant_ty.data().as_variable() {
                    let existing = variants
                        .entry(*ty_var)
                        .or_default()
                        .insert(*tag, *payload_ty);
                    assert!(existing.is_none(), "Duplicate variant constraint for {tag}");
                } else {
                    others.push(constraint);
                }
            }
            _ => others.push(constraint),
        }
    }
    // Create minimalist variant type for them.
    let subst = variants
        .into_iter()
        .map(|(ty_var, variant)| {
            let variant_ty = Type::variant(variant.into_iter().collect());
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
) -> Result<ConstraintValidationOutput, InternalCompilationError> {
    // Filter out constraints that have types not found in our code.
    let unbound = node.all_unbound_ty_vars();
    let ty_vars = unbound.keys().cloned().collect::<Vec<_>>();
    let constraints = select_constraints_only_these_ty_vars(constraints, &ty_vars);
    let related_constraints = constraints.iter().map(|c| constraint_ptr(c)).collect();

    // Find constraints that are not transitively accessible from the fn signature
    let sig_ty_vars = ty.inner_ty_vars();
    let (constraints, orphan_constraints) =
        select_constraints_accessible_from(&constraints, &sig_ty_vars);

    // Partition the orphan constraints into variant constraint substitutions and the others.
    let (subst, other_orphans) = partition_variant_constraints(orphan_constraints.into_iter());
    if !other_orphans.is_empty() {
        return Err(internal_compilation_error!(Internal(format!(
            "Orphan constraints found: {other_orphans:?}"
        ))));
    }

    // Compute the quantifiers based on the function type and its constraints.
    let quantifiers = TypeScheme::list_ty_vars(ty, constraints.iter().map(Borrow::borrow));

    // Detect unbound type variables in the code and return error if not in unused variants only.
    // These are neither part of the function signature nor of the constraints.
    let bounds: Vec<_> = quantifiers.iter().chain(subst.keys()).cloned().collect();
    let uninstantiated_unbound = check_unbounds(unbound, &bounds)?;
    let constraint_subst = subst
        .into_iter()
        .chain(
            uninstantiated_unbound
                .into_iter()
                .map(|ty_var| (ty_var, Type::never())),
        )
        .collect();
    let retained_constraints = constraints.iter().map(|c| constraint_ptr(c)).collect();

    Ok(ConstraintValidationOutput {
        quantifiers,
        related_constraints,
        retained_constraints,
        constraint_subst,
    })
}

fn log_dropped_constraints_expr(
    all: &[PubTypeConstraint],
    retained: &HashSet<PubTypeConstraintPtr>,
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
    log::debug!("Dropped constraints in expr: {dropped}");
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
    log::debug!("Dropped constraints in {ctx}: {dropped}");
}
