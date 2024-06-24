use std::{
    collections::{HashMap, HashSet},
    mem,
};

use ena::unify::{EqUnifyValue, InPlaceUnificationTable, UnifyKey};
use itertools::Itertools;
use lrpar::Span;
use ustr::Ustr;

use crate::{
    ast::{Expr, ExprKind},
    containers::{SVec2, B},
    emit_ir::emit_expr,
    error::InternalCompilationError,
    function::{FunctionRef, ScriptFunction},
    ir::{self, EnvStore, Node, NodeKind},
    module::{FmtWithModuleEnv, ModuleEnv, ModuleFunction},
    r#type::{FnType, NativeType, TyVarKey, Type, TypeKind, TypeLike, TypeSubstitution, TypeVar},
    std::{array::array_type, math::int_type},
    type_scheme::{PubConstraint, TypeScheme},
    value::Value,
};

impl UnifyKey for TyVarKey {
    type Value = Option<Type>;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "TyVarKey"
    }
}

impl EqUnifyValue for Type {}

pub type FreshTyVarGen<'g> = &'g mut (dyn FnMut() -> TypeVar + 'g);

/// A constraint on types.
#[derive(Debug, Clone)]
pub enum Constraint {
    TypeEqual(Type, Type, Span), // TODO: add an optional span for the other type
    Pub(PubConstraint),
}

impl Constraint {
    pub fn contains_ty_vars(&self, vars: &[TypeVar]) -> bool {
        match self {
            Constraint::TypeEqual(ty1, ty2, _) => {
                ty1.data().contains_ty_vars(vars) || ty2.data().contains_ty_vars(vars)
            }
            Constraint::Pub(pub_constraint) => pub_constraint.contains_ty_vars(vars),
        }
    }
}

impl FmtWithModuleEnv for Constraint {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        match self {
            Constraint::TypeEqual(ty1, ty2, _) => {
                write!(f, "{} = {}", ty1.format_with(env), ty2.format_with(env))
            }
            Constraint::Pub(pub_constraint) => pub_constraint.fmt_with_module_env(f, env),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Local {
    pub name: Ustr,
    pub mutable: bool,
    pub ty: TypeScheme<Type>,
    pub span: Span,
}
impl Local {
    pub fn new(name: Ustr, mutable: bool, ty: TypeScheme<Type>, span: Span) -> Self {
        Self {
            name,
            mutable,
            ty,
            span,
        }
    }
    fn new_var(name: Ustr, ty: Type, span: Span) -> Self {
        Self {
            name,
            mutable: true,
            ty: TypeScheme::new_just_type(ty),
            span,
        }
    }
    fn new_let(name: Ustr, ty: Type, span: Span) -> Self {
        Self {
            name,
            mutable: false,
            ty: TypeScheme::new_just_type(ty),
            span,
        }
    }
}

/// A typing environment, mapping local variable names to types.
pub struct TypingEnv<'m> {
    locals: Vec<Local>,
    module_env: ModuleEnv<'m>,
}
impl<'m> TypingEnv<'m> {
    pub fn new(locals: Vec<Local>, module_env: ModuleEnv<'m>) -> Self {
        Self { locals, module_env }
    }

    pub fn get_locals_and_drop(self) -> Vec<Local> {
        self.locals
    }

    fn has_variable_name(&self, name: Ustr) -> bool {
        self.locals.iter().any(|local| local.name == name)
    }

    fn get_variable_index_and_type_scheme(
        &self,
        name: Ustr,
        span: Span,
    ) -> Result<(usize, &TypeScheme<Type>), InternalCompilationError> {
        self.locals
            .iter()
            .rev()
            .position(|local| local.name == name)
            .map(|rev_index| self.locals.len() - 1 - rev_index)
            .map(|index| (index, &self.locals[index].ty))
            .ok_or(InternalCompilationError::VariableNotFound(span))
    }

    fn get_function(
        &'m self,
        name: Ustr,
        span: Span,
    ) -> Result<&'m ModuleFunction, InternalCompilationError> {
        // TODO: add support for looking up in other modules with qualified path
        self.module_env
            .current
            .get_function(name, self.module_env.others)
            .ok_or(InternalCompilationError::FunctionNotFound(span))
    }
}

/// The type inference status, containing the unification table and the constraints
#[derive(Default, Debug)]
pub struct TypeInference {
    unification_table: InPlaceUnificationTable<TyVarKey>,
    generation: u32,
    constraints: Vec<Constraint>,
}

impl TypeInference {
    pub fn new_with_generation(generation: u32) -> Self {
        Self {
            generation,
            ..Default::default()
        }
    }

    // TODO: improve error reporting by storing the span of the expression triggering the fresh variable creation
    pub fn fresh_type_var(&mut self) -> TypeVar {
        TypeVar::new_fresh(self.unification_table.new_key(None).0, self.generation)
    }

    pub fn fresh_type_var_ty(&mut self) -> Type {
        Type::variable(self.fresh_type_var())
    }

    pub fn fresh_type_var_tys(&mut self, count: usize) -> Vec<Type> {
        (0..count).map(|_| self.fresh_type_var_ty()).collect()
    }

    pub fn fresh_type_var_subs(&mut self, source: &[TypeVar]) -> TypeSubstitution {
        source
            .iter()
            .map(|&ty_var| (ty_var, self.fresh_type_var_ty()))
            .collect()
    }

    pub fn add_pub_constraint(&mut self, pub_constraint: PubConstraint) {
        self.constraints.push(Constraint::Pub(pub_constraint));
    }

    pub fn infer_expr(
        &mut self,
        env: &mut TypingEnv,
        expr: &Expr,
    ) -> Result<(Node, Type), InternalCompilationError> {
        use ir::Node as N;
        use ir::NodeKind as K;
        use ExprKind::*;
        let (node, ty) = match &expr.kind {
            Literal(value, ty) => (K::Literal(value.clone()), *ty),
            Variable(name) => {
                // Retrieve the index and the type of the variable from the environment
                let (index, var_ty_scheme) =
                    env.get_variable_index_and_type_scheme(*name, expr.span)?;
                let (var_ty, _) = var_ty_scheme.instantiate(self);
                let node = K::EnvLoad(index);
                (node, var_ty)
            }
            LetVar((name, name_span), mutable, let_expr) => {
                let (node, ty_scheme) = if *mutable {
                    // Mutable variable, do not do generalization.
                    let (node, ty) = self.infer_expr(env, let_expr)?;
                    (node, TypeScheme::new_just_type(ty))
                } else {
                    // Read-only variable, do generalization here: infer the type of the expression and generalize it.
                    // Approach inspired from https://cs3110.github.io/textbook/chapters/interp/inference.html
                    // 1. Run a mini type inference for expr, but use our locals from the environment.
                    let env_size = env.locals.len();
                    let locals = mem::take(&mut env.locals);
                    let next_gen = self.generation + 1;
                    let fresh_ty_var_gen = &mut || self.fresh_type_var();
                    let (compiled_expr, constraints) =
                        emit_expr(let_expr, env.module_env, locals, next_gen, fresh_ty_var_gen)?;
                    env.locals = compiled_expr.locals;
                    env.locals.truncate(env_size);
                    // 2. Add the external constraints of the inner expr (e.g., dealing with our own type variables)
                    // to our constraints.
                    self.constraints.extend(constraints);
                    // 3. Collect free type variables from ty, these are our quantifiers.
                    (compiled_expr.expr, compiled_expr.ty)
                };
                env.locals
                    .push(Local::new(*name, *mutable, ty_scheme.clone(), expr.span));
                let node = K::EnvStore(B::new(EnvStore {
                    node,
                    ty_scheme,
                    name_span: *name_span,
                }));
                (node, Type::unit())
            }
            Abstract(args, body) => {
                // Allocate fresh variables for the arguments in the function's scope
                let locals = args
                    .iter()
                    .map(|(name, span)| Local::new_let(*name, self.fresh_type_var_ty(), *span))
                    .collect::<Vec<_>>();
                let args_ty = locals.iter().map(|local| local.ty.ty).collect::<Vec<_>>();
                // Build environment for typing the function's body
                let mut env = TypingEnv::new(locals, env.module_env);
                // Infer the body's type
                let (code, ret_ty) = self.infer_expr(&mut env, body)?;
                // Store and return the function's type
                let fn_ty = FnType::new_by_val(&args_ty, ret_ty);
                let value_fn = Value::function(B::new(ScriptFunction::new(code)));
                let node = K::Literal(value_fn);
                (node, Type::function_type(fn_ty))
            }
            Apply(func, args) => {
                // Do we have a global function?
                if let Variable(name) = func.kind {
                    if !env.has_variable_name(name) {
                        let (node, ty) = self.infer_static_apply(env, name, func.span, args)?;
                        return Ok((N::new(node, ty, expr.span), ty));
                    }
                }
                // No, we emit code to evaluate function
                // Infer the type of the arguments and collect their code and constraints
                // TODO: check borrow rules
                let (args_nodes, args_ty) = self.infer_exprs(env, args)?;
                // Allocate a fresh variable for the return type
                let ret_ty = self.fresh_type_var_ty();
                // Build the function type
                let func_ty = Type::function(&args_ty, ret_ty);
                // Check the function against its return type
                let func_node = self.check_expr(env, func, func_ty)?;
                // TODO: use generics for inout
                let inout = args_ty.iter().map(|_arg| false).collect();
                // Store and return the result
                let node = K::Apply(B::new(ir::Application {
                    function: func_node,
                    arguments: args_nodes,
                    inout,
                }));
                (node, ret_ty)
            }
            StaticApply(name, args) => self.infer_static_apply(env, *name, expr.span, args)?,
            Block(exprs) => {
                let env_size = env.locals.len();
                let (nodes, types) = self.infer_exprs(env, exprs)?;
                env.locals.truncate(env_size);
                let ty = types.last().copied().unwrap_or(Type::unit());
                let node = K::Block(B::new(SVec2::from_vec(nodes)));
                (node, ty)
            }
            Assign(place, value) => {
                // TODO: check if place is mutable
                let (value, value_ty) = self.infer_expr(env, value)?;
                let (place, place_ty) = self.infer_expr(env, place)?;
                self.constraints
                    .push(Constraint::TypeEqual(place_ty, value_ty, expr.span));
                let node = K::Assign(B::new(ir::Assignment { place, value }));
                (node, Type::unit())
            }
            Tuple(exprs) => {
                let (nodes, types) = self.infer_exprs(env, exprs)?;
                let node = K::Tuple(B::new(SVec2::from_vec(nodes)));
                let ty = Type::tuple(types);
                (node, ty)
            }
            Project(tuple_expr, index, index_span) => {
                let (tuple_node, tuple_ty) = self.infer_expr(env, tuple_expr)?;
                let element_ty = self.fresh_type_var_ty();
                self.constraints
                    .push(Constraint::Pub(PubConstraint::new_tuple_at_index_is(
                        tuple_ty,
                        tuple_expr.span,
                        *index,
                        *index_span,
                        element_ty,
                    )));
                let node = K::Project(B::new((tuple_node, *index)));
                (node, element_ty)
            }
            Array(exprs) => {
                if exprs.is_empty() {
                    // The element type is a fresh type variable
                    let element_ty = self.fresh_type_var_ty();
                    // Build an empty array node and return it
                    let node = K::Array(B::new(SVec2::new()));
                    (node, array_type(element_ty))
                } else {
                    // The element type is the first element's type
                    let (first_node, element_ty) = self.infer_expr(env, &exprs[0])?;
                    // Infer the type of the elements and collect their code and constraints
                    let (other_nodes, types) = self.infer_exprs(env, &exprs[1..])?;
                    // All elements must be of the first element's type
                    for (ty, expr) in types.into_iter().zip(exprs.iter().skip(1)) {
                        self.constraints
                            .push(Constraint::TypeEqual(ty, element_ty, expr.span));
                    }
                    // Build the array node and return it
                    let element_nodes = std::iter::once(first_node).chain(other_nodes).collect();
                    let node = K::Array(B::new(element_nodes));
                    (node, array_type(element_ty))
                }
            }
            Index(array, index) => {
                // New type for the array
                let element_ty = self.fresh_type_var_ty();
                let array_ty = array_type(element_ty);
                // Infer type of the array expression and make sure it is an array
                let (array_node, array_expr_ty) = self.infer_expr(env, array)?;
                self.constraints
                    .push(Constraint::TypeEqual(array_expr_ty, array_ty, array.span));
                // Check type of the index expression to be int
                let index_node = self.check_expr(env, index, int_type())?;
                // Build the index node and return it
                let node = K::Index(B::new(array_node), B::new(index_node));
                (node, element_ty)
            }
            Match(expr, alternatives, default) => {
                // Infer condition expression and get a new return type
                let (condition_node, pattern_ty) = self.infer_expr(env, expr)?;
                let return_ty = self.fresh_type_var_ty();
                // Convert optional default to mandatory one
                let node = if let Some(default) = default {
                    let default_node = self.check_expr(env, default, return_ty)?;
                    let alternatives =
                        self.check_patterns(env, alternatives, pattern_ty, return_ty)?;
                    K::Case(B::new(ir::Case {
                        value: condition_node,
                        alternatives,
                        default: default_node,
                    }))
                } else if alternatives.is_empty() {
                    panic!("empty match without default");
                } else {
                    let default_expr = &alternatives.last().unwrap().1;
                    let default_node = self.check_expr(env, default_expr, return_ty)?;

                    let alternatives = self.check_patterns(
                        env,
                        &alternatives[0..alternatives.len() - 1],
                        pattern_ty,
                        return_ty,
                    )?;
                    K::Case(B::new(ir::Case {
                        value: condition_node,
                        alternatives,
                        default: default_node,
                    }))
                };
                (node, return_ty)
            }
            Error(msg) => {
                panic!("attempted to infer type for error node: {msg}");
            }
        };
        Ok((N::new(node, ty, expr.span), ty))
    }

    fn infer_static_apply(
        &mut self,
        env: &mut TypingEnv,
        name: Ustr,
        span: Span,
        args: &[Expr],
    ) -> Result<(NodeKind, Type), InternalCompilationError> {
        // Get the function and its type
        let function = env.get_function(name, span)?;
        // Instantiate its type scheme
        let (inst_fn_ty, subst) = function.ty_scheme.instantiate(self);
        // Get the code and make sure the types of its arguments match the expected types
        let args_nodes = self.check_exprs(env, args, inst_fn_ty.args_ty())?;
        // Build and return the function node
        let function = env.get_function(name, span)?;
        // TODO: use generics for inout
        let inout = inst_fn_ty.args.iter().map(|arg| arg.inout).collect();
        let node = ir::NodeKind::StaticApply(B::new(ir::StaticApplication {
            function: FunctionRef::new_weak(&function.code),
            arguments: args_nodes,
            subst,
            inout,
        }));
        Ok((node, inst_fn_ty.ret))
    }

    fn infer_exprs(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[Expr],
    ) -> Result<(Vec<ir::Node>, Vec<Type>), InternalCompilationError> {
        exprs
            .iter()
            .map(|arg| {
                let (node, ty) = self.infer_expr(env, arg)?;
                Ok::<(ir::Node, Type), InternalCompilationError>((node, ty))
            })
            .process_results(|iter| iter.unzip::<_, _, Vec<_>, Vec<_>>())
    }

    fn check_patterns<U: std::iter::FromIterator<(Value, ir::Node)>>(
        &mut self,
        env: &mut TypingEnv,
        pairs: &[(Expr, Expr)],
        expected_pattern_type: Type,
        expected_return_type: Type,
    ) -> Result<U, InternalCompilationError> {
        pairs
            .iter()
            .map(|(pattern, expr)| {
                if let ExprKind::Literal(literal, ty) = &pattern.kind {
                    self.constraints.push(Constraint::TypeEqual(
                        *ty,
                        expected_pattern_type,
                        pattern.span,
                    ));
                    let node = self.check_expr(env, expr, expected_return_type)?;
                    Ok((literal.clone(), node))
                } else {
                    Err(InternalCompilationError::Internal(
                        "Expect literal, found another expr kind".to_string(),
                    ))
                }
            })
            .collect::<Result<U, InternalCompilationError>>()
    }

    fn check_exprs(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[Expr],
        expected_tys: impl Iterator<Item = Type>,
    ) -> Result<Vec<ir::Node>, InternalCompilationError> {
        exprs
            .iter()
            .zip(expected_tys)
            .map(|(arg, ty)| {
                let node = self.check_expr(env, arg, ty)?;
                Ok(node)
            })
            .process_results(|iter| iter.collect())
    }

    pub fn check_expr(
        &mut self,
        env: &mut TypingEnv,
        expr: &Expr,
        expected_ty: Type,
    ) -> Result<Node, InternalCompilationError> {
        use ir::Node as N;
        use ir::NodeKind as K;
        use ExprKind::*;

        // Literal of correct type, we are good
        if let Literal(value, ty) = &expr.kind {
            if *ty == expected_ty {
                return Ok(N::new(K::Literal(value.clone()), expected_ty, expr.span));
            }
        }

        // Functions call
        if let Abstract(args, body) = &expr.kind {
            let ty_data = &*expected_ty.data();
            if let TypeKind::Function(fn_ty) = ty_data {
                // Build environment for typing the function's body
                let locals = args
                    .iter()
                    .zip(&fn_ty.args)
                    .map(|((name, span), arg_ty)| Local::new_let(*name, arg_ty.ty, *span))
                    .collect::<Vec<_>>();
                let mut env = TypingEnv::new(locals, env.module_env);
                // Recursively check the function's body
                return self.check_expr(&mut env, body, fn_ty.ret);
            }
        }

        // Other cases, add constraint
        let (node, actual_ty) = self.infer_expr(env, expr)?;
        self.constraints
            .push(Constraint::TypeEqual(actual_ty, expected_ty, expr.span));
        Ok(node)
    }

    pub fn log_debug_constraints(&self, module_env: ModuleEnv) {
        log::debug!("Constraints before unification (gen {}):", self.generation);
        for constraint in &self.constraints {
            log::debug!("  {}", constraint.format_with(&module_env));
        }
    }

    pub fn unify(
        self,
        outer_fresh_ty_var_gen: FreshTyVarGen<'_>,
    ) -> Result<UnifiedTypeInference, InternalCompilationError> {
        UnifiedTypeInference::unify_type_inference(self, outer_fresh_ty_var_gen)
    }
}

/// The type inference after unification, with only public constraints remaining
#[derive(Default, Debug)]
pub struct UnifiedTypeInference {
    unification_table: InPlaceUnificationTable<TyVarKey>,
    generation: u32,
    /// Remaininig constraints that cannot be solved, will be part of the resulting type scheme
    remaining_constraints: Vec<PubConstraint>,
    /// Constraints for the outer scope, e.g., involving type variables of a previous generation
    external_constraints: Vec<Constraint>,
}

impl UnifiedTypeInference {
    pub fn unify_type_inference(
        ty_inf: TypeInference,
        outer_fresh_ty_var_gen: FreshTyVarGen<'_>,
    ) -> Result<Self, InternalCompilationError> {
        let TypeInference {
            unification_table,
            generation,
            constraints,
        } = ty_inf;
        let mut unified_ty_inf = UnifiedTypeInference {
            unification_table,
            generation,
            remaining_constraints: vec![],
            external_constraints: vec![],
        };
        let mut remaining_constraints = HashSet::new();

        // First, solve all type equalities.
        for constraint in constraints {
            match constraint {
                Constraint::TypeEqual(left, right, span) => {
                    unified_ty_inf.unify_types(left, right, span, outer_fresh_ty_var_gen)?
                }
                Constraint::Pub(cst) => {
                    remaining_constraints.insert(cst);
                }
            }
        }

        // Then, solve other constraints.
        if !remaining_constraints.is_empty() {
            loop {
                // Loop as long as we make progress.
                let mut progress = false;

                // Perform simplification.
                let mut tupes_at_index_is: HashMap<(Type, usize), Type> = HashMap::new();
                for constraint in &remaining_constraints {
                    match constraint {
                        PubConstraint::TupleAtIndexIs {
                            tuple_ty,
                            index,
                            index_span,
                            element_ty,
                            ..
                        } => {
                            let key = (*tuple_ty, *index);
                            if let Some(&expected_ty) = tupes_at_index_is.get(&key) {
                                unified_ty_inf.unify_types(
                                    expected_ty,
                                    *element_ty,
                                    *index_span,
                                    outer_fresh_ty_var_gen,
                                )?;
                            } else {
                                tupes_at_index_is.insert(key, *element_ty);
                            }
                        }
                    }
                }

                // Perform unification.
                let mut new_remaining_constraints = HashSet::new();
                for constraint in remaining_constraints {
                    let new_progress = match constraint {
                        PubConstraint::TupleAtIndexIs { .. } => unified_ty_inf
                            .unify_tuple_project(constraint.clone(), outer_fresh_ty_var_gen)?,
                    };
                    match new_progress {
                        Some(new_constraint) => {
                            new_remaining_constraints.insert(new_constraint);
                        }
                        None => progress = true,
                    }
                }
                remaining_constraints = new_remaining_constraints;

                // Break if no progress was made
                if !progress {
                    break;
                }
            }
        }

        // FIXME: think whether we should have an intermediate struct without the remaining_constraints in it.
        unified_ty_inf.remaining_constraints = remaining_constraints.into_iter().collect();
        Ok(unified_ty_inf)
    }

    pub fn constraints(self) -> (Vec<PubConstraint>, Vec<Constraint>) {
        (self.remaining_constraints, self.external_constraints)
    }

    fn normalize_type(&mut self, ty: Type) -> Type {
        let type_data = { ty.data().clone() };
        match type_data {
            TypeKind::Variable(v) => {
                if v.generation() == self.generation {
                    let id = v.as_key();
                    match self.unification_table.probe_value(id) {
                        Some(ty) => self.normalize_type(ty),
                        _ => {
                            Type::variable(self.unification_table.find(id).to_var(self.generation))
                        }
                    }
                } else {
                    ty
                }
            }
            TypeKind::Native(ty) => Type::native_type(NativeType::new(
                ty.bare_ty.clone(),
                self.normalize_types(&ty.arguments),
            )),
            TypeKind::Variant(_) => todo!("normalize variant"),
            TypeKind::Tuple(tys) => Type::tuple(self.normalize_types(&tys)),
            TypeKind::Record(_) => todo!("noramlize record"),
            TypeKind::Function(fn_ty) => Type::function_type(self.normalize_fn_type(&fn_ty)),
            TypeKind::Newtype(name, ty) => Type::new_type(name, self.normalize_type(ty)),
        }
    }

    fn normalize_types(&mut self, tys: &[Type]) -> Vec<Type> {
        tys.iter().map(|ty| self.normalize_type(*ty)).collect()
    }

    pub fn normalize_fn_type(&mut self, fn_ty: &FnType) -> FnType {
        let args = fn_ty
            .args
            .iter()
            .map(|arg| (self.normalize_type(arg.ty), arg.inout))
            .collect::<Vec<_>>();
        let ret = self.normalize_type(fn_ty.ret);
        FnType::new(&args, ret)
    }

    fn unify_types(
        &mut self,
        a: Type,
        b: Type,
        span: Span,
        outer_fresh_ty_var_gen: FreshTyVarGen<'_>,
    ) -> Result<(), InternalCompilationError> {
        let a_ty = self.normalize_type(a);
        let b_ty = self.normalize_type(b);
        let a_data = { a_ty.data().clone() };
        let b_data = { b_ty.data().clone() };
        use TypeKind::*;
        match (a_data, b_data) {
            (Variable(a), Variable(b)) => {
                let a_is_local = a.generation() == self.generation;
                let b_is_local = b.generation() == self.generation;
                match (a_is_local, b_is_local) {
                    (true, true) => {
                        // Both local, do normal unification.
                        self.unification_table
                            .unify_var_var(a.as_key(), b.as_key())
                            .map_err(|_| InternalCompilationError::TypeMismatch(a_ty, b_ty, span))
                    }
                    (false, false) => {
                        // Both external, add a constraint.
                        self.external_constraints
                            .push(Constraint::TypeEqual(a_ty, b_ty, span));
                        Ok(())
                    }
                    (true, false) => {
                        // Var a is local, b is external, assume b by to be a normal type.
                        self.unify_type_variable(a, b_ty, span, outer_fresh_ty_var_gen)
                    }
                    (false, true) => {
                        // Var a is external, b is local, assume a by to be a normal type.
                        self.unify_type_variable(b, a_ty, span, outer_fresh_ty_var_gen)
                    }
                }
            }
            (Variable(var), _) => self.unify_type_variable(var, b_ty, span, outer_fresh_ty_var_gen),
            (_, Variable(var)) => self.unify_type_variable(var, a_ty, span, outer_fresh_ty_var_gen),
            (Native(a), Native(b)) => {
                if a.bare_ty != b.bare_ty {
                    return Err(InternalCompilationError::TypeMismatch(a_ty, b_ty, span));
                }
                for (a_arg_ty, b_arg_ty) in a.arguments.iter().zip(b.arguments.iter()) {
                    self.unify_types(*a_arg_ty, *b_arg_ty, span, outer_fresh_ty_var_gen)?;
                }
                Ok(())
            }
            (Variant(_a), Variant(_b)) => todo!("implement variant unification"),
            (Tuple(a), Tuple(b)) => {
                if a.len() != b.len() {
                    return Err(InternalCompilationError::TypeMismatch(a_ty, b_ty, span));
                }
                for (a_el_ty, b_el_ty) in a.iter().zip(b.iter()) {
                    self.unify_types(*a_el_ty, *b_el_ty, span, outer_fresh_ty_var_gen)?;
                }
                Ok(())
            }
            (Record(_a), Record(_b)) => todo!("implement record unification"),
            (Function(a), Function(b)) => {
                if a.args.len() != b.args.len() {
                    return Err(InternalCompilationError::TypeMismatch(a_ty, b_ty, span));
                }
                for (a_arg, b_arg) in a.args.iter().zip(b.args.iter()) {
                    if a_arg.inout != b_arg.inout {
                        return Err(InternalCompilationError::TypeMismatch(a_ty, b_ty, span));
                    }
                    self.unify_types(a_arg.ty, b_arg.ty, span, outer_fresh_ty_var_gen)?;
                }
                self.unify_types(a.ret, b.ret, span, outer_fresh_ty_var_gen)
            }
            (Newtype(a_name, a_old_ty), Newtype(b_name, b_old_ty)) => {
                if a_name != b_name {
                    return Err(InternalCompilationError::TypeMismatch(a_ty, b_ty, span));
                }
                self.unify_types(a_old_ty, b_old_ty, span, outer_fresh_ty_var_gen)
            }
            _ => Err(InternalCompilationError::TypeMismatch(a_ty, b_ty, span)),
        }
    }

    fn unify_type_variable(
        &mut self,
        var: TypeVar,
        ty: Type,
        span: Span,
        outer_fresh_ty_var_gen: FreshTyVarGen<'_>,
    ) -> Result<(), InternalCompilationError> {
        if ty.data().contains_type_var(var) {
            Err(InternalCompilationError::InfiniteType(var, ty, span))
        } else if var.generation() != self.generation {
            // The type variable is external, so we need to make sure that the matching type has no local type variables.
            // To do so, we iterate and create one external type variable for each local type variable.
            let subst: TypeSubstitution = ty
                .inner_ty_vars()
                .iter()
                .filter(|var| var.generation() == self.generation)
                .map(|var| {
                    let ext_ty_var = outer_fresh_ty_var_gen();
                    let ext_ty = Type::variable(ext_ty_var);
                    self.unification_table
                        .unify_var_value(var.as_key(), Some(ext_ty))
                        .map_err(|(l, r)| InternalCompilationError::TypeMismatch(l, r, span))?;
                    Ok::<(TypeVar, Type), InternalCompilationError>((*var, ext_ty))
                })
                .collect::<Result<_, _>>()?;
            log::debug!("Unified external type variable {var}, created {} new external type variables and replaced local ones", subst.len());
            // Create a new type using these new variables, and add an external constraint for it.
            let new_ty = ty.instantiate(&subst);
            self.external_constraints.push(Constraint::TypeEqual(
                Type::variable(var),
                new_ty,
                span,
            ));
            Ok(())
        } else {
            // The type variable is internal, perform normal unification.
            self.unification_table
                .unify_var_value(var.as_key(), Some(ty))
                .map_err(|(l, r)| InternalCompilationError::TypeMismatch(l, r, span))
        }
    }

    fn unify_tuple_project(
        &mut self,
        PubConstraint::TupleAtIndexIs {
            tuple_ty,
            tuple_span,
            index,
            index_span,
            element_ty,
        }: PubConstraint,
        outer_fresh_ty_var_gen: FreshTyVarGen<'_>,
    ) -> Result<Option<PubConstraint>, InternalCompilationError> {
        let tuple_ty = self.normalize_type(tuple_ty);
        let element_ty = self.normalize_type(element_ty);
        let tuple_data = { tuple_ty.data().clone() };
        match tuple_data {
            // A type variable may or may not be a tuple, defer the unification
            TypeKind::Variable(_) => Ok(Some(PubConstraint::new_tuple_at_index_is(
                tuple_ty, tuple_span, index, index_span, element_ty,
            ))),
            // A tuple, verify length and element type
            TypeKind::Tuple(tys) => {
                if let Some(ty) = tys.get(index) {
                    self.unify_types(*ty, element_ty, index_span, outer_fresh_ty_var_gen)?;
                    Ok(None)
                } else {
                    Err(InternalCompilationError::InvalidTupleIndex {
                        index,
                        index_span,
                        tuple_length: tys.len(),
                        tuple_span,
                    })
                }
            }
            // Not a tuple, error
            _ => Err(InternalCompilationError::InvalidTupleProjection {
                expr_ty: tuple_ty,
                expr_span: tuple_span,
                index_span,
            }),
        }
    }

    pub(crate) fn substitute_module_function(&mut self, descr: &mut ModuleFunction) {
        // FIXME: see whether this can be unified with quantifiers and constraints setup
        descr.ty_scheme.ty = self.substitute_fn_type(&descr.ty_scheme.ty, &[]);
        descr
            .code
            .borrow_mut()
            .apply_if_script(&mut |node| self.substitute_node(node, &[]));
    }

    pub(crate) fn substitute_in_type_scheme(&mut self, ty_scheme: &mut TypeScheme<Type>) {
        ty_scheme.constraints = ty_scheme
            .constraints
            .iter()
            .map(|cst| self.substitute_constraint(cst, &ty_scheme.quantifiers))
            .collect();
        ty_scheme.ty = self.substitute_type(ty_scheme.ty, &ty_scheme.quantifiers);
    }

    pub fn substitute_type(&mut self, ty: Type, ignore: &[TypeVar]) -> Type {
        let type_data: TypeKind = { ty.data().clone() };
        use TypeKind::*;
        match type_data {
            Variable(v) => {
                if ignore.contains(&v) || v.generation() != self.generation {
                    return Type::variable(v);
                }
                let root = self.unification_table.find(v.as_key());
                match self.unification_table.probe_value(root) {
                    Some(ty) => self.substitute_type(ty, ignore),
                    _ => Type::variable(root.to_var(self.generation)),
                }
            }
            Native(ty) => Type::native_type(NativeType::new(
                ty.bare_ty.clone(),
                self.substitute_types(&ty.arguments, ignore),
            )),
            Variant(_) => todo!("substitute variant"),
            Tuple(tys) => Type::tuple(self.substitute_types(&tys, ignore)),
            Record(_) => todo!("substitute record"),
            Function(fn_ty) => Type::function_type(self.substitute_fn_type(&fn_ty, ignore)),
            Newtype(name, ty) => Type::new_type(name, self.substitute_type(ty, ignore)),
        }
    }

    fn substitute_types(&mut self, tys: &[Type], ignore: &[TypeVar]) -> Vec<Type> {
        tys.iter()
            .map(|ty| self.substitute_type(*ty, ignore))
            .collect()
    }

    pub fn substitute_fn_type(&mut self, fn_ty: &FnType, ignore: &[TypeVar]) -> FnType {
        let args = fn_ty
            .args
            .iter()
            .map(|arg| (self.substitute_type(arg.ty, ignore), arg.inout))
            .collect::<Vec<_>>();
        let ret = self.substitute_type(fn_ty.ret, ignore);
        FnType::new(&args, ret)
    }

    pub fn substitute_node(&mut self, node: &mut ir::Node, ignore: &[TypeVar]) {
        use ir::NodeKind::*;
        node.ty = self.substitute_type(node.ty, ignore);
        match &mut node.kind {
            Literal(value) => self.substitute_value(value, ignore),
            Apply(app) => {
                self.substitute_node(&mut app.function, ignore);
                self.substitute_nodes(&mut app.arguments, ignore);
            }
            StaticApply(app) => {
                // do not substitute the function because it is in a module
                self.substitute_nodes(&mut app.arguments, ignore);
            }
            EnvStore(node) => self.substitute_node(&mut node.node, &node.ty_scheme.quantifiers),
            EnvLoad(_) => {}
            Block(nodes) => self.substitute_nodes(nodes, ignore),
            Assign(assignment) => {
                self.substitute_node(&mut assignment.place, ignore);
                self.substitute_node(&mut assignment.value, ignore);
            }
            Tuple(nodes) => self.substitute_nodes(nodes, ignore),
            Project(node_and_index) => self.substitute_node(&mut node_and_index.0, ignore),
            Array(nodes) => self.substitute_nodes(nodes, ignore),
            Index(array, index) => {
                self.substitute_node(array, ignore);
                self.substitute_node(index, ignore);
            }
            Case(case) => {
                self.substitute_node(&mut case.value, ignore);
                for alternative in case.alternatives.iter_mut() {
                    self.substitute_value(&mut alternative.0, ignore);
                    self.substitute_node(&mut alternative.1, ignore);
                }
                self.substitute_node(&mut case.default, ignore);
            }
        }
    }

    fn substitute_nodes(&mut self, nodes: &mut [ir::Node], ignore: &[TypeVar]) {
        for node in nodes {
            self.substitute_node(node, ignore);
        }
    }

    fn substitute_value(&mut self, value: &mut Value, ignore: &[TypeVar]) {
        match value {
            Value::Tuple(tuple) => {
                for value in tuple.iter_mut() {
                    self.substitute_value(value, ignore);
                }
            }
            Value::Function(function) => {
                let function = function.get();
                let mut function = function.borrow_mut();
                function.apply_if_script(&mut |node| self.substitute_node(node, ignore));
            }
            _ => {}
        }
    }

    fn substitute_constraint(
        &mut self,
        constraint: &PubConstraint,
        ignore: &[TypeVar],
    ) -> PubConstraint {
        match constraint {
            PubConstraint::TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => {
                let tuple_ty = self.substitute_type(*tuple_ty, ignore);
                let element_ty = self.substitute_type(*element_ty, ignore);
                PubConstraint::new_tuple_at_index_is(
                    tuple_ty,
                    *tuple_span,
                    *index,
                    *index_span,
                    element_ty,
                )
            }
        }
    }

    pub fn substitute_in_external_constraints(&mut self) {
        let constraints = mem::take(&mut self.external_constraints);
        self.external_constraints = constraints
            .into_iter()
            .map(|constraint| {
                use Constraint::*;
                match constraint {
                    TypeEqual(left, right, span) => {
                        let left = self.substitute_type(left, &[]);
                        let right = self.substitute_type(right, &[]);
                        TypeEqual(left, right, span)
                    }
                    Pub(cst) => Pub(self.substitute_constraint(&cst, &[])),
                }
            })
            .collect();
    }

    pub fn log_debug_constraints(&self, module_env: ModuleEnv) {
        log::debug!("Constraints after unification (gen {}):", self.generation);
        if !self.remaining_constraints.is_empty() {
            log::debug!("  Internal constraints:");
            for constraint in &self.remaining_constraints {
                log::debug!("    {}", constraint.format_with(&module_env));
            }
        }
        if !self.external_constraints.is_empty() {
            log::debug!("  External constraints:");
            for constraint in &self.external_constraints {
                log::debug!("    {}", constraint.format_with(&module_env));
            }
        }
    }

    pub fn log_debug_substitution_table(&mut self, module_env: ModuleEnv) {
        log::debug!("Substitution table:");
        for i in 0..self.unification_table.len() {
            let key = TyVarKey(i as u32);
            let var = TypeVar::new(i as u32, self.generation);
            let value = self.unification_table.probe_value(key);
            match value {
                Some(value) => log::debug!("  {var} → {}", value.format_with(&module_env)),
                None => log::debug!("  {var} → {}", {
                    let key = self.unification_table.find(key);
                    TypeVar::new(key.0, self.generation)
                }),
            }
        }
    }
}
