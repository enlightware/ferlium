use std::{cell::RefCell, collections::HashSet, rc::Rc};

use itertools::Itertools;

use crate::{
    ast::{self, *},
    containers::B,
    error::InternalCompilationError,
    function::ScriptFunction,
    ir,
    module::{self, FmtWithModuleEnv, Module, ModuleEnv, Modules},
    r#type::{FnType, Type, TypeLike, TypeVar},
    std::logic::unit_type,
    type_inference::{Constraint, FreshTyVarGen, TypeInference, TypingEnv},
    type_scheme::{PubConstraint, TypeScheme},
    value::Value,
};

pub use crate::type_inference::Local;

/// Emit IR for the given module
pub fn emit_module(
    source: &ast::Module,
    others: &Modules,
    merge_with: Option<&Module>,
) -> Result<Module, InternalCompilationError> {
    use ir::Node as N;
    use ir::NodeKind as K;

    // First pass, populate the function table and allocate fresh mono type variables.
    let mut output = merge_with.map_or_else(Module::default, |module| module.clone());
    let mut ty_inf = TypeInference::default();
    for ModuleFunction {
        name,
        args,
        args_span,
        span,
        ..
    } in &source.functions
    {
        let args_ty = ty_inf.fresh_type_var_tys(args.len());
        let dummy_code = B::new(ScriptFunction::new(N::new(
            K::Literal(Value::unit()),
            unit_type(),
            *span,
        )));
        // Note: the type is filled with type variables, and the quantifiers and constraints
        // are left empty. They will be filled in the second pass.
        let descr = module::ModuleFunction {
            ty_scheme: TypeScheme::new_just_type(FnType::new_by_val(
                &args_ty,
                Type::variable(ty_inf.fresh_type_var()),
            )),
            code: Rc::new(RefCell::new(dummy_code)),
            spans: Some(module::ModuleFunctionSpans {
                name: name.1,
                args: args.iter().map(|(_, s)| *s).collect(),
                args_span: *args_span,
                span: *span,
            }),
        };
        output.functions.insert(name.0, descr);
    }

    // Second pass, infer types and emit function bodies.
    for function in &source.functions {
        let name = function.name.0;
        let descr = output.functions.get(&name).unwrap();
        let module_env = ModuleEnv::new(&output, others);
        let mut ty_env = TypingEnv::new(
            descr.ty_scheme.ty.as_locals_no_bound(&function.args),
            module_env,
        );
        let fn_node = ty_inf.check_expr(&mut ty_env, &function.body, descr.ty_scheme.ty.ret)?;
        let descr = output.functions.get_mut(&name).unwrap();
        *descr.code.borrow_mut() = B::new(ScriptFunction::new(fn_node));
    }
    let module_env = ModuleEnv::new(&output, others);
    ty_inf.log_debug_constraints(module_env);

    // Third pass, perform the unification.
    let mut ty_inf = ty_inf.unify(&mut invalid_outer_fresh_ty_var_gen)?;
    ty_inf.log_debug_substitution_table(module_env);
    ty_inf.log_debug_constraints(module_env);

    // Fourth pass, substitute the mono type variables with the inferred types.
    for ModuleFunction { name, .. } in &source.functions {
        let descr = output.functions.get_mut(&name.0).unwrap();
        ty_inf.substitute_module_function(descr);
    }

    // Fifth pass, get the remaining constraints and collect the free type variables.
    let (all_constraints, external_constraints) = ty_inf.constraints();
    assert!(
        external_constraints.is_empty(),
        "No external constraints shall remain at top level"
    );
    for ModuleFunction { name, .. } in &source.functions {
        // Compute the quantifiers based on the type variables in the function type and
        // the constraints referring to them.
        let descr = output.functions.get_mut(&name.0).unwrap();
        let mut quantifiers = descr.ty_scheme.ty.inner_ty_vars();
        let mut constraints;
        loop {
            // Loop because new constraints may introduce new type variables.
            let initial_count = quantifiers.len();
            constraints = filter_constraints(&all_constraints, &quantifiers);
            quantifiers = extend_with_contraint_ty_vars(&quantifiers, &constraints);
            if quantifiers.len() == initial_count {
                break;
            }
        }

        // Detect unbound type variables in the code and return error if any.
        let mut unbound = HashSet::new();
        descr.code.borrow_mut().apply_if_script(&mut |node| {
            node.unbound_ty_vars(&mut unbound, &quantifiers, 0);
        });
        if let Some((ty_var, span)) = unbound.into_iter().next() {
            let pos = span.start();
            let mut ty = None;
            descr
                .code
                .borrow_mut()
                .apply_if_script(&mut |node| ty = node.type_at(pos));
            let ty = ty.ok_or_else(|| {
                InternalCompilationError::Internal(format!(
                    "Type not found at pos {pos} while looking for unbound type variable {ty_var}"
                ))
            })?;
            return Err(InternalCompilationError::UnboundTypeVar { ty_var, ty, span });
        }

        // Write the final type scheme.
        descr.ty_scheme.quantifiers = quantifiers;
        descr.ty_scheme.constraints = constraints;
    }

    // Safety check: make sure that there are no unused constraints.
    let used_constraints: HashSet<_> = source
        .functions
        .iter()
        .flat_map(|f| output.functions[&f.name.0].ty_scheme.constraints.clone())
        .collect();
    let unused_constraints = all_constraints
        .iter()
        .filter(|c| !used_constraints.contains(c))
        .collect::<Vec<_>>();
    if !unused_constraints.is_empty() {
        let module_env = ModuleEnv::new(&output, others);
        let constraints = unused_constraints
            .iter()
            .map(|c| c.format_with(&module_env))
            .join(" ∧ ");
        return Err(InternalCompilationError::Internal(format!(
            "Unused constraints in module compilation: {}",
            constraints
        )));
    }

    // Sixth pass, normalize the type schemes and substitute the types in the functions.
    for ModuleFunction { name, .. } in &source.functions {
        let descr = output.functions.get_mut(&name.0).unwrap();
        let subst = descr.ty_scheme.normalize();
        descr.code.borrow_mut().apply_if_script(&mut |node| {
            node.substitute(&subst);
        });
    }

    Ok(output)
}

/// A compiled expression
#[derive(Debug)]
pub struct CompiledExpr {
    pub expr: ir::Node,
    pub ty: TypeScheme<Type>,
    pub locals: Vec<Local>,
}

/// Emit IR for an expression
/// Retrun the compiled expression and any remaining external constraints
/// referring to lower-generation type variables.
pub fn emit_expr(
    source: &ast::Expr,
    module_env: ModuleEnv,
    locals: Vec<Local>,
    generation: u32,
    outer_fresh_ty_var_gen: FreshTyVarGen<'_>,
) -> Result<(CompiledExpr, Vec<Constraint>), InternalCompilationError> {
    // Infer the expression with the existing locals.
    let initial_local_count = locals.len();
    let mut ty_env = TypingEnv::new(locals, module_env);
    let mut ty_inf = TypeInference::new_with_generation(generation);
    let (mut node, mut ty) = ty_inf.infer_expr(&mut ty_env, source)?;
    let mut locals = ty_env.get_locals_and_drop();
    // FIXME: we need to emit fresh variables not in the locals before us!
    // So we need some notion of generations so that fresh ones do not clash with older ones.
    ty_inf.log_debug_constraints(module_env);

    // Perform the unification.
    let mut ty_inf = ty_inf.unify(outer_fresh_ty_var_gen)?;
    ty_inf.log_debug_substitution_table(module_env);

    // Substitute the result of the unification.
    ty_inf.substitute_node(&mut node, &[]);
    ty = ty_inf.substitute_type(ty, &[]);
    for local in locals.iter_mut().skip(initial_local_count) {
        ty_inf.substitute_in_type_scheme(&mut local.ty);
    }
    ty_inf.substitute_in_external_constraints();

    // Get the remaining constraints and collect the free variables.
    ty_inf.log_debug_constraints(module_env);
    let (constraints, external_constraints) = ty_inf.constraints();
    let quantifiers = TypeScheme::<Type>::list_ty_vars(&ty, &constraints, generation);

    // Detect unbound type variables in the code and return error if any.
    let mut unbound = HashSet::new();
    node.unbound_ty_vars(&mut unbound, &quantifiers, generation);
    if let Some((ty_var, span)) = unbound.into_iter().next() {
        let pos = span.start();
        let ty = node.type_at(pos).ok_or_else(|| {
            InternalCompilationError::Internal(format!(
                "Type not found at pos {pos} while looking for unbound type variable {ty_var}"
            ))
        })?;
        return Err(InternalCompilationError::UnboundTypeVar { ty_var, ty, span });
    }

    // Detect unbound inner type variables in locals and return internal error if any.
    for local in locals.iter().skip(initial_local_count) {
        let unbounds = local.ty.unbound_ty_vars(generation);
        if let Some(&ty_var) = unbounds.first() {
            return Err(InternalCompilationError::Internal(format!(
                "Unbound type variable {ty_var} in local {} with type {}",
                local.name,
                local.ty.display_rust_style(&module_env)
            )));
        }
    }

    // Detect external constraints that contain type variables listed in the quantifiers
    for constraint in &external_constraints {
        if constraint.contains_ty_vars(&quantifiers) {
            return Err(InternalCompilationError::Internal(format!(
                "External constraint {} contains one of the internal type variables {}",
                constraint.format_with(&module_env),
                quantifiers.iter().map(|var| format!("{var}")).join(", ")
            )));
        }
    }

    // Normalize the type scheme
    let mut ty_scheme = TypeScheme {
        ty,
        quantifiers,
        constraints,
    };
    let subst = ty_scheme.normalize();
    node.substitute(&subst);

    Ok((
        CompiledExpr {
            expr: node,
            ty: ty_scheme,
            locals,
        },
        external_constraints,
    ))
}

/// Emit IR for an expression
/// Retrun the compiled expression and any remaining external constraints
/// referring to lower-generation type variables.
pub fn emit_expr_top_level(
    source: &ast::Expr,
    module_env: ModuleEnv,
    locals: Vec<Local>,
) -> Result<(CompiledExpr, Vec<Constraint>), InternalCompilationError> {
    emit_expr(
        source,
        module_env,
        locals,
        0,
        &mut invalid_outer_fresh_ty_var_gen,
    )
}

/// Filter constraints that contain type variables listed in the quantifiers
fn filter_constraints(constraints: &[PubConstraint], ty_vars: &[TypeVar]) -> Vec<PubConstraint> {
    constraints
        .iter()
        .filter(|constraint| {
            let ret = constraint.contains_ty_vars(ty_vars);
            if ret {
                log::debug!("Constraint {constraint:?} contains: {ret}");
            }
            ret
        })
        .cloned()
        .collect()
}

/// Extend a list of type variables with the type variables in the constraints
fn extend_with_contraint_ty_vars(
    ty_vars: &[TypeVar],
    constraints: &[PubConstraint],
) -> Vec<TypeVar> {
    ty_vars
        .iter()
        .cloned()
        .chain(constraints.iter().flat_map(|c| c.inner_ty_vars()))
        .unique()
        .collect()
}

fn invalid_outer_fresh_ty_var_gen() -> TypeVar {
    panic!("Already at outer-most level, cannot have an even outer fresh type variable generator.")
}
