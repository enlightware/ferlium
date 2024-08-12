use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display},
    mem,
};

use ena::unify::{EqUnifyValue, InPlaceUnificationTable, UnifyKey};
use itertools::{multiunzip, Itertools};
use lrpar::Span;
use ustr::Ustr;

use crate::{
    ast::{Expr, ExprKind},
    containers::{SVec2, B},
    emit_ir::emit_expr,
    error::{InternalCompilationError, MustBeMutableContext},
    function::{FunctionRef, ScriptFunction},
    ir::{self, EnvStore, Node, NodeKind},
    module::{FmtWithModuleEnv, ModuleEnv, ModuleFunction},
    mutability::{MutType, MutVal, MutVar, MutVarKey},
    r#type::{
        FnArgType, FnType, NativeType, TyVarKey, Type, TypeKind, TypeLike, TypeSubstitution,
        TypeVar,
    },
    std::{array::array_type, math::int_type, range::range_iterator_type},
    type_scheme::{PubTypeConstraint, TypeScheme},
    typing_env::{Local, TypingEnv},
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

impl UnifyKey for MutVarKey {
    type Value = Option<MutVal>;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "MutVarKey"
    }
}

impl EqUnifyValue for MutVal {}

pub type FreshTyVarGen<'g> = &'g mut (dyn FnMut() -> TypeVar + 'g);

/// A constraint on types.
#[derive(Debug, Clone)]
pub enum TypeConstraint {
    SubType {
        current: Type,
        current_span: Span,
        expected: Type,
        expected_span: Span,
    },
    Pub(PubTypeConstraint),
}

impl TypeConstraint {
    pub fn contains_ty_vars(&self, vars: &[TypeVar]) -> bool {
        match self {
            TypeConstraint::SubType {
                current, expected, ..
            } => current.data().contains_ty_vars(vars) || expected.data().contains_ty_vars(vars),
            TypeConstraint::Pub(pub_constraint) => pub_constraint.contains_ty_vars(vars),
        }
    }
}

impl FmtWithModuleEnv for TypeConstraint {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        match self {
            TypeConstraint::SubType {
                current, expected, ..
            } => {
                write!(
                    f,
                    "{} ≤ {}",
                    current.format_with(env),
                    expected.format_with(env)
                )
            }
            TypeConstraint::Pub(pub_constraint) => pub_constraint.fmt_with_module_env(f, env),
        }
    }
}

/// A constraint on mutability.
#[derive(Debug, Clone)]
pub enum MutConstraint {
    MutBeAtLeast {
        current: MutType,
        current_span: Span,
        target: MutType,
        reason_span: Span,
    },
}

impl Display for MutConstraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MutConstraint::MutBeAtLeast {
                current, target, ..
            } => write!(f, "{current} ≥ {target}"),
        }
    }
}

/// The type inference status, containing the unification table and the constraints
#[derive(Default, Debug)]
pub struct TypeInference {
    generation: u32,
    ty_unification_table: InPlaceUnificationTable<TyVarKey>,
    ty_constraints: Vec<TypeConstraint>,
    mut_unification_table: InPlaceUnificationTable<MutVarKey>,
    mut_constraints: Vec<MutConstraint>,
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
        TypeVar::new_fresh(self.ty_unification_table.new_key(None).0, self.generation)
    }

    pub fn fresh_type_var_ty(&mut self) -> Type {
        Type::variable(self.fresh_type_var())
    }

    pub fn fresh_mut_var(&mut self) -> MutVar {
        MutVar::new_fresh(self.mut_unification_table.new_key(None).0, self.generation)
    }

    pub fn fresh_mut_var_ty(&mut self) -> MutType {
        MutType::Variable(self.fresh_mut_var())
    }

    pub fn fresh_fn_args(&mut self, count: usize) -> Vec<FnArgType> {
        (0..count)
            .map(|_| FnArgType::new(self.fresh_type_var_ty(), self.fresh_mut_var_ty()))
            .collect()
    }

    pub fn fresh_type_var_subs(&mut self, source: &[TypeVar]) -> TypeSubstitution {
        source
            .iter()
            .map(|&ty_var| (ty_var, self.fresh_type_var_ty()))
            .collect()
    }

    pub fn add_pub_constraint(&mut self, pub_constraint: PubTypeConstraint) {
        self.ty_constraints
            .push(TypeConstraint::Pub(pub_constraint));
    }

    pub fn infer_expr(
        &mut self,
        env: &mut TypingEnv,
        expr: &Expr,
    ) -> Result<(Node, Type, MutType), InternalCompilationError> {
        use ir::Node as N;
        use ir::NodeKind as K;
        use ExprKind::*;
        let (node, ty, mut_ty) = match &expr.kind {
            Literal(value, ty) => (K::Literal(value.clone()), *ty, MutType::constant()),
            Variable(name) => {
                // Retrieve the index and the type of the variable from the environment
                let (index, ty_scheme, mut_ty) =
                    env.get_variable_index_and_type_scheme(*name, expr.span)?;
                let (var_ty, _) = ty_scheme.instantiate(self);
                let node = K::EnvLoad(index);
                (node, var_ty, mut_ty)
            }
            LetVar((name, name_span), mutable, let_expr) => {
                let (node, ty_scheme) = if mutable.into() {
                    // Mutable variable, do not do generalization.
                    let (node, ty, _) = self.infer_expr(env, let_expr)?;
                    (node, TypeScheme::new_just_type(ty))
                } else {
                    // Read-only variable, do generalization here: infer the type of the expression and generalize it.
                    // Approach inspired from https://cs3110.github.io/textbook/chapters/interp/inference.html
                    // 1. Run a mini type inference for expr, but use our locals from the environment.
                    let env_size = env.locals.len();
                    let locals = mem::take(&mut env.locals);
                    let next_gen = self.generation + 1;
                    let fresh_ty_var_gen = &mut || self.fresh_type_var();
                    let (compiled_expr, ty_constraints, mut_constraints) =
                        emit_expr(let_expr, env.module_env, locals, next_gen, fresh_ty_var_gen)?;
                    env.locals = compiled_expr.locals;
                    env.locals.truncate(env_size);
                    // 2. Add the external constraints of the inner expr (e.g., dealing with our own type variables)
                    // to our constraints.
                    self.ty_constraints.extend(ty_constraints);
                    self.mut_constraints.extend(mut_constraints);
                    // 3. Collect free type variables from ty, these are our quantifiers.
                    (compiled_expr.expr, compiled_expr.ty)
                };
                env.locals.push(Local::new(
                    *name,
                    MutType::resolved(*mutable),
                    ty_scheme.clone(),
                    expr.span,
                ));
                let node = K::EnvStore(B::new(EnvStore {
                    node,
                    ty_scheme,
                    name_span: *name_span,
                }));
                (node, Type::unit(), MutType::constant())
            }
            Abstract(args, body) => {
                // Allocate fresh type and mutability variables for the arguments in the function's scope
                let locals = args
                    .iter()
                    .map(|(name, span)| {
                        Local::new(
                            *name,
                            self.fresh_mut_var_ty(),
                            TypeScheme::new_just_type(self.fresh_type_var_ty()),
                            *span,
                        )
                    })
                    .collect::<Vec<_>>();
                let args_ty = locals.iter().map(Local::as_fn_arg_type).collect();
                // Build environment for typing the function's body
                let mut env = TypingEnv::new(locals, env.module_env);
                // Infer the body's type
                let (code, ret_ty, _) = self.infer_expr(&mut env, body)?;
                // Store and return the function's type
                let fn_ty = FnType::new(args_ty, ret_ty);
                let value_fn = Value::function(B::new(ScriptFunction::new(code)));
                let node = K::Literal(value_fn);
                (node, Type::function_type(fn_ty), MutType::constant())
            }
            Apply(func, args) => {
                // Do we have a global function?
                if let Variable(name) = func.kind {
                    if !env.has_variable_name(name) {
                        let (node, ty, mut_ty) =
                            self.infer_static_apply(env, name, func.span, args)?;
                        return Ok((N::new(node, ty, expr.span), ty, mut_ty));
                    }
                }
                // No, we emit code to evaluate function
                // Infer the type and mutability of the arguments and collect their code and constraints
                // TODO: check borrow rules
                let (args_nodes, args_tys) = self.infer_exprs_ret_arg_ty(env, args)?;
                // Allocate a fresh variable for the return type
                let ret_ty = self.fresh_type_var_ty();
                // Build the function type
                let func_ty = Type::function_type(FnType::new(args_tys, ret_ty));
                // Check the function against its function type
                let func_node =
                    self.check_expr(env, func, func_ty, MutType::constant(), expr.span)?;
                // Store and return the result
                let node = K::Apply(B::new(ir::Application {
                    function: func_node,
                    arguments: args_nodes,
                }));
                (node, ret_ty, MutType::constant())
            }
            StaticApply(name, args) => self.infer_static_apply(env, *name, expr.span, args)?,
            Block(exprs) => {
                let env_size = env.locals.len();
                let (nodes, types) = self.infer_exprs_drop_mut(env, exprs)?;
                env.locals.truncate(env_size);
                let ty = types.last().copied().unwrap_or(Type::unit());
                let node = K::Block(B::new(SVec2::from_vec(nodes)));
                (node, ty, MutType::constant())
            }
            Assign(place, sign_span, value) => {
                let (value, value_ty, _value_mut) = self.infer_expr(env, value)?;
                let (place, place_ty, place_mut) = self.infer_expr(env, place)?;
                self.add_mut_be_at_least_constraint(
                    place_mut,
                    place.span,
                    MutType::mutable(),
                    *sign_span,
                );
                self.add_sub_type_constraint(value_ty, value.span, place_ty, place.span);
                let node = K::Assign(B::new(ir::Assignment { place, value }));
                (node, Type::unit(), MutType::constant())
            }
            Tuple(exprs) => {
                let (nodes, types) = self.infer_exprs_drop_mut(env, exprs)?;
                let node = K::Tuple(B::new(SVec2::from_vec(nodes)));
                let ty = Type::tuple(types);
                (node, ty, MutType::constant())
            }
            Project(tuple_expr, index, index_span) => {
                let (tuple_node, tuple_ty, tuple_mut) = self.infer_expr(env, tuple_expr)?;
                let element_ty = self.fresh_type_var_ty();
                self.ty_constraints.push(TypeConstraint::Pub(
                    PubTypeConstraint::new_tuple_at_index_is(
                        tuple_ty,
                        tuple_expr.span,
                        *index,
                        *index_span,
                        element_ty,
                    ),
                ));
                let node = K::Project(B::new((tuple_node, *index)));
                (node, element_ty, tuple_mut)
            }
            Array(exprs) => {
                if exprs.is_empty() {
                    // The element type is a fresh type variable
                    let element_ty = self.fresh_type_var_ty();
                    // Build an empty array node and return it
                    let node = K::Array(B::new(SVec2::new()));
                    (node, array_type(element_ty), MutType::constant())
                } else {
                    // The element type is the first element's type
                    let (first_node, element_ty, _) = self.infer_expr(env, &exprs[0])?;
                    // Infer the type of the elements and collect their code and constraints
                    let (other_nodes, types) = self.infer_exprs_drop_mut(env, &exprs[1..])?;
                    // All elements must be of the first element's type
                    for (ty, expr) in types.into_iter().zip(exprs.iter().skip(1)) {
                        self.add_sub_type_constraint(ty, expr.span, element_ty, exprs[0].span);
                    }
                    // Build the array node and return it
                    let element_nodes = std::iter::once(first_node).chain(other_nodes).collect();
                    let node = K::Array(B::new(element_nodes));
                    (node, array_type(element_ty), MutType::constant())
                }
            }
            Index(array, index) => {
                // New type for the array
                let element_ty = self.fresh_type_var_ty();
                let array_ty = array_type(element_ty);
                // Infer type of the array expression and make sure it is an array
                let (array_node, array_expr_ty, array_expr_mut) = self.infer_expr(env, array)?;
                self.add_sub_type_constraint(array_expr_ty, array.span, array_ty, array.span);
                // Check type of the index expression to be int
                let index_node =
                    self.check_expr(env, index, int_type(), MutType::constant(), index.span)?;
                // Build the index node and return it
                let node = K::Index(B::new(array_node), B::new(index_node));
                (node, element_ty, array_expr_mut)
            }
            Match(expr, alternatives, default) => {
                // Infer condition expression and get a new return type
                let (condition_node, pattern_ty, _) = self.infer_expr(env, expr)?;
                // Convert optional default to mandatory one
                let (node, return_ty) = if let Some(default) = default {
                    let (default_node, return_ty, _) = self.infer_expr(env, default)?;
                    let alternatives = self.check_patterns(
                        env,
                        alternatives,
                        pattern_ty,
                        expr.span,
                        return_ty,
                        default.span,
                    )?;
                    (
                        K::Case(B::new(ir::Case {
                            value: condition_node,
                            alternatives,
                            default: default_node,
                        })),
                        return_ty,
                    )
                } else if alternatives.is_empty() {
                    panic!("empty match without default");
                } else {
                    let default_expr = &alternatives.last().unwrap().1;
                    let (default_node, return_ty, _) = self.infer_expr(env, default_expr)?;
                    let other_exprs = &alternatives[0..alternatives.len() - 1];
                    let alternatives = self.check_patterns(
                        env,
                        other_exprs,
                        pattern_ty,
                        expr.span,
                        return_ty,
                        default_expr.span,
                    )?;
                    (
                        K::Case(B::new(ir::Case {
                            value: condition_node,
                            alternatives,
                            default: default_node,
                        })),
                        return_ty,
                    )
                };
                (node, return_ty, MutType::constant())
            }
            ForLoop(var_name, iterator, body) => {
                let iterator = self.check_expr(
                    env,
                    iterator,
                    range_iterator_type(),
                    MutType::constant(),
                    iterator.span,
                )?;
                let env_size = env.locals.len();
                env.locals.push(Local::new(
                    var_name.0,
                    MutType::constant(),
                    TypeScheme::new_just_type(int_type()),
                    var_name.1,
                ));
                let body =
                    self.check_expr(env, body, Type::unit(), MutType::constant(), body.span)?;
                env.locals.truncate(env_size);
                let node = K::Iterate(B::new(ir::Iteration { iterator, body }));
                (node, Type::unit(), MutType::constant())
            }
            Error(msg) => {
                panic!("attempted to infer type for error node: {msg}");
            }
        };
        Ok((N::new(node, ty, expr.span), ty, mut_ty))
    }

    fn infer_static_apply(
        &mut self,
        env: &mut TypingEnv,
        name: Ustr,
        span: Span,
        args: &[Expr],
    ) -> Result<(NodeKind, Type, MutType), InternalCompilationError> {
        // Get the function and its type
        let function = env.get_function(name, span)?;
        // Instantiate its type scheme
        let (inst_fn_ty, _subst) = function.ty_scheme.instantiate(self);
        // Get the code and make sure the types of its arguments match the expected types
        let args_nodes = self.check_exprs(env, args, &inst_fn_ty.args, span)?;
        // Build and return the function node
        let function = env.get_function(name, span)?;
        let ret_ty = inst_fn_ty.ret;
        let node = ir::NodeKind::StaticApply(B::new(ir::StaticApplication {
            function: FunctionRef::new_weak(&function.code),
            arguments: args_nodes,
            ty: inst_fn_ty,
            // subst,
        }));
        Ok((node, ret_ty, MutType::constant()))
    }

    fn infer_exprs_drop_mut(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[Expr],
    ) -> Result<(Vec<ir::Node>, Vec<Type>), InternalCompilationError> {
        exprs
            .iter()
            .map(|arg| {
                let (node, ty, _mut_ty) = self.infer_expr(env, arg)?;
                Ok::<(ir::Node, Type), InternalCompilationError>((node, ty))
            })
            .process_results(|iter| multiunzip(iter))
    }

    fn infer_exprs_ret_arg_ty(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[Expr],
    ) -> Result<(Vec<ir::Node>, Vec<FnArgType>), InternalCompilationError> {
        exprs
            .iter()
            .map(|arg| {
                let (node, ty, mut_ty) = self.infer_expr(env, arg)?;
                Ok::<(ir::Node, FnArgType), InternalCompilationError>((
                    node,
                    FnArgType::new(ty, mut_ty),
                ))
            })
            .process_results(|iter| multiunzip(iter))
    }

    fn check_patterns<U: std::iter::FromIterator<(Value, ir::Node)>>(
        &mut self,
        env: &mut TypingEnv,
        pairs: &[(Expr, Expr)],
        expected_pattern_type: Type,
        expected_pattern_span: Span,
        expected_return_type: Type,
        expected_return_span: Span,
    ) -> Result<U, InternalCompilationError> {
        pairs
            .iter()
            .map(|(pattern, expr)| {
                if let ExprKind::Literal(literal, ty) = &pattern.kind {
                    self.add_sub_type_constraint(
                        *ty,
                        pattern.span,
                        expected_pattern_type,
                        expected_pattern_span,
                    );
                    let node = self.check_expr(
                        env,
                        expr,
                        expected_return_type,
                        MutType::constant(),
                        expected_return_span,
                    )?;
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
        expected_tys: &[FnArgType],
        expected_span: Span,
    ) -> Result<Vec<ir::Node>, InternalCompilationError> {
        exprs
            .iter()
            .zip(expected_tys)
            .map(|(arg, arg_ty)| {
                let node = self.check_expr(env, arg, arg_ty.ty, arg_ty.inout, expected_span)?;
                Ok(node)
            })
            .process_results(|iter| iter.collect())
    }

    pub fn check_expr(
        &mut self,
        env: &mut TypingEnv,
        expr: &Expr,
        expected_ty: Type,
        expected_mut: MutType,
        expected_span: Span,
    ) -> Result<Node, InternalCompilationError> {
        use ir::Node as N;
        use ir::NodeKind as K;
        use ExprKind::*;

        // Literal of correct type, we are good
        if let Literal(value, ty) = &expr.kind {
            if *ty == expected_ty {
                let node = K::Literal(value.clone());
                return Ok(N::new(node, expected_ty, expr.span));
            }
        }

        // Functions call
        if let Abstract(args, body) = &expr.kind {
            let ty_data = { expected_ty.data().clone() };
            if let TypeKind::Function(fn_ty) = ty_data {
                // Build environment for typing the function's body
                let locals = args
                    .iter()
                    .zip(&fn_ty.args)
                    .map(|((name, span), arg_ty)| {
                        Local::new(
                            *name,
                            arg_ty.inout,
                            TypeScheme::new_just_type(arg_ty.ty),
                            *span,
                        )
                    })
                    .collect::<Vec<_>>();
                // Build environment for typing the function's body
                let mut env = TypingEnv::new(locals, env.module_env);
                // Recursively check the function's body
                let code =
                    self.check_expr(&mut env, body, fn_ty.ret, MutType::constant(), body.span)?;
                // Store and return the function's type
                let value_fn = Value::function(B::new(ScriptFunction::new(code)));
                let node = K::Literal(value_fn);
                return Ok(N::new(node, expected_ty, expr.span));
            }
        }

        // Other cases, infer and add constraints
        let (node, actual_ty, actual_mut) = self.infer_expr(env, expr)?;
        self.add_sub_type_constraint(actual_ty, expr.span, expected_ty, expected_span);
        self.add_mut_be_at_least_constraint(actual_mut, expr.span, expected_mut, expected_span);
        Ok(node)
    }

    pub fn log_debug_constraints(&self, module_env: ModuleEnv) {
        if self.ty_constraints.is_empty() {
            log::debug!(
                "No type constraints before unification (gen {}).",
                self.generation
            );
        } else {
            log::debug!(
                "Type constraints before unification (gen {}):",
                self.generation
            );
            for constraint in &self.ty_constraints {
                log::debug!("  {}", constraint.format_with(&module_env));
            }
        }
        if self.mut_constraints.is_empty() {
            log::debug!(
                "No mutability constraints before unification (gen {}).",
                self.generation
            );
        } else {
            log::debug!(
                "Mutability constraints before unification (gen {}):",
                self.generation
            );
            for constraint in &self.mut_constraints {
                log::debug!("  {}", constraint);
            }
        }
    }

    fn add_sub_type_constraint(
        &mut self,
        current: Type,
        current_span: Span,
        expected: Type,
        expected_span: Span,
    ) {
        if current == expected {
            return;
        }
        self.ty_constraints.push(TypeConstraint::SubType {
            current,
            current_span,
            expected,
            expected_span,
        });
    }

    fn add_mut_be_at_least_constraint(
        &mut self,
        current: MutType,
        current_span: Span,
        target: MutType,
        reason_span: Span,
    ) {
        if target == MutType::constant() {
            // everything has at least constant mutability
            return;
        }
        if current == MutType::mutable() {
            // mutable can be used for all cases
            return;
        }
        self.mut_constraints.push(MutConstraint::MutBeAtLeast {
            current,
            current_span,
            target,
            reason_span,
        });
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
    generation: u32,
    ty_unification_table: InPlaceUnificationTable<TyVarKey>,
    /// Remaining constraints that cannot be solved, will be part of the resulting type scheme
    remaining_ty_constraints: Vec<PubTypeConstraint>,
    /// Constraints for the outer scope, e.g., involving type variables of a previous generation
    external_ty_constraints: Vec<TypeConstraint>,
    mut_unification_table: InPlaceUnificationTable<MutVarKey>,
    /// Constraints for the outer scope, e.g., involving type variables of a previous generation
    external_mut_constraints: Vec<MutConstraint>,
}

impl UnifiedTypeInference {
    pub fn unify_type_inference(
        ty_inf: TypeInference,
        outer_fresh_ty_var_gen: FreshTyVarGen<'_>,
    ) -> Result<Self, InternalCompilationError> {
        let TypeInference {
            generation,
            ty_unification_table,
            ty_constraints,
            mut_unification_table,
            mut_constraints,
        } = ty_inf;
        let mut unified_ty_inf = UnifiedTypeInference {
            generation,
            ty_unification_table,
            remaining_ty_constraints: vec![],
            external_ty_constraints: vec![],
            mut_unification_table,
            external_mut_constraints: vec![],
        };
        let mut remaining_constraints = HashSet::new();

        // First, resolve mutability constraints.
        for constraint in mut_constraints {
            use MutConstraint::*;
            match constraint {
                MutBeAtLeast {
                    current,
                    current_span,
                    target,
                    reason_span,
                } => {
                    unified_ty_inf.unify_mut_must_be_at_least(
                        current,
                        current_span,
                        target,
                        reason_span,
                        MustBeMutableContext::Value,
                    )?;
                }
            }
        }

        // Make the remaining mutability variables constant.
        for var in 0..unified_ty_inf.mut_unification_table.len() {
            let var = MutVarKey(var as u32);
            if unified_ty_inf
                .mut_unification_table
                .probe_value(var)
                .is_none()
            {
                unified_ty_inf
                    .mut_unification_table
                    .unify_var_value(var, Some(MutVal::constant()))
                    .expect("Cannot unify free mutability variable");
            }
        }

        // Then, solve all type equalities.
        for constraint in ty_constraints {
            use TypeConstraint::*;
            match constraint {
                SubType {
                    current,
                    current_span,
                    expected,
                    expected_span,
                } => unified_ty_inf.unify_sub_type(
                    current,
                    current_span,
                    expected,
                    expected_span,
                    outer_fresh_ty_var_gen,
                )?,
                Pub(cst) => {
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
                let mut tuples_at_index_is: HashMap<(Type, usize), Type> = HashMap::new();
                for constraint in &remaining_constraints {
                    use PubTypeConstraint::*;
                    match constraint {
                        TupleAtIndexIs {
                            tuple_ty,
                            tuple_span,
                            index,
                            index_span,
                            element_ty,
                            ..
                        } => {
                            let key = (*tuple_ty, *index);
                            if let Some(&expected_ty) = tuples_at_index_is.get(&key) {
                                unified_ty_inf.unify_sub_type(
                                    expected_ty,
                                    *tuple_span,
                                    *element_ty,
                                    *index_span,
                                    outer_fresh_ty_var_gen,
                                )?;
                            } else {
                                tuples_at_index_is.insert(key, *element_ty);
                            }
                        }
                    }
                }

                // Perform unification.
                let mut new_remaining_constraints = HashSet::new();
                for constraint in remaining_constraints {
                    let new_progress = match constraint {
                        PubTypeConstraint::TupleAtIndexIs { .. } => unified_ty_inf
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
        unified_ty_inf.remaining_ty_constraints = remaining_constraints.into_iter().collect();
        Ok(unified_ty_inf)
    }

    pub fn constraints(
        self,
    ) -> (
        Vec<PubTypeConstraint>,
        Vec<TypeConstraint>,
        Vec<MutConstraint>,
    ) {
        (
            self.remaining_ty_constraints,
            self.external_ty_constraints,
            self.external_mut_constraints,
        )
    }

    fn normalize_type(&mut self, ty: Type) -> Type {
        let type_data = { ty.data().clone() };
        use TypeKind::*;
        match type_data {
            Variable(v) => {
                if v.generation() == self.generation {
                    let id = v.as_key();
                    match self.ty_unification_table.probe_value(id) {
                        Some(ty) => self.normalize_type(ty),
                        _ => Type::variable(
                            self.ty_unification_table.find(id).to_var(self.generation),
                        ),
                    }
                } else {
                    ty
                }
            }
            Native(ty) => Type::native_type(NativeType::new(
                ty.bare_ty.clone(),
                self.normalize_types(&ty.arguments),
            )),
            Variant(_) => todo!("normalize variant"),
            Tuple(tys) => Type::tuple(self.normalize_types(&tys)),
            Record(_) => todo!("normalize record"),
            Function(fn_ty) => Type::function_type(self.normalize_fn_type(&fn_ty)),
            Newtype(name, ty) => Type::new_type(name, self.normalize_type(ty)),
        }
    }

    fn normalize_types(&mut self, tys: &[Type]) -> Vec<Type> {
        tys.iter().map(|ty| self.normalize_type(*ty)).collect()
    }

    pub fn normalize_fn_type(&mut self, fn_ty: &FnType) -> FnType {
        let args = fn_ty
            .args
            .iter()
            .map(|arg| {
                FnArgType::new(
                    self.normalize_type(arg.ty),
                    self.normalize_mut_type(arg.inout),
                )
            })
            .collect::<Vec<_>>();
        let ret = self.normalize_type(fn_ty.ret);
        FnType::new(args, ret)
    }

    fn normalize_mut_type(&mut self, mut_ty: MutType) -> MutType {
        match mut_ty {
            MutType::Resolved(_) => mut_ty,
            MutType::Variable(v) => {
                if v.generation() == self.generation {
                    let id = v.as_key();
                    match self.mut_unification_table.probe_value(id) {
                        Some(val) => MutType::resolved(val),
                        _ => MutType::variable(
                            self.mut_unification_table.find(id).to_var(self.generation),
                        ),
                    }
                } else {
                    mut_ty
                }
            }
        }
    }

    fn unify_sub_type(
        &mut self,
        current: Type,
        current_span: Span,
        expected: Type,
        expected_span: Span,
        outer_fresh_ty_var_gen: FreshTyVarGen<'_>,
    ) -> Result<(), InternalCompilationError> {
        let cur_ty = self.normalize_type(current);
        let exp_ty = self.normalize_type(expected);
        let cur_data = { cur_ty.data().clone() };
        let exp_data = { exp_ty.data().clone() };
        use TypeKind::*;
        match (cur_data, exp_data) {
            (Variable(cur), Variable(exp)) => {
                let cur_is_local = cur.generation() == self.generation;
                let exp_is_local = exp.generation() == self.generation;
                match (cur_is_local, exp_is_local) {
                    (true, true) => {
                        // Both local, do normal unification.
                        self.ty_unification_table
                            .unify_var_var(cur.as_key(), exp.as_key())
                            .map_err(|_| {
                                InternalCompilationError::IsNotSubtype(
                                    cur_ty,
                                    current_span,
                                    exp_ty,
                                    expected_span,
                                )
                            })
                    }
                    (false, false) => {
                        // Both external, add a constraint.
                        self.add_sub_type_external_constraint(
                            cur_ty,
                            current_span,
                            exp_ty,
                            expected_span,
                        );
                        Ok(())
                    }
                    (true, false) => {
                        // Var cur is local, exp is external, assume exp by to be a normal type.
                        self.unify_type_variable(
                            cur,
                            current_span,
                            exp_ty,
                            expected_span,
                            outer_fresh_ty_var_gen,
                        )
                    }
                    (false, true) => {
                        // Var cur is external, exp is local, assume cur by to be a normal type.
                        self.unify_type_variable(
                            exp,
                            expected_span,
                            cur_ty,
                            current_span,
                            outer_fresh_ty_var_gen,
                        )
                    }
                }
            }
            (Variable(var), _) => self.unify_type_variable(
                var,
                current_span,
                exp_ty,
                expected_span,
                outer_fresh_ty_var_gen,
            ),
            (_, Variable(var)) => self.unify_type_variable(
                var,
                expected_span,
                cur_ty,
                current_span,
                outer_fresh_ty_var_gen,
            ),
            (Native(cur), Native(exp)) => {
                // TODO: add int/float subtyping
                if cur.bare_ty != exp.bare_ty {
                    return Err(InternalCompilationError::IsNotSubtype(
                        cur_ty,
                        current_span,
                        exp_ty,
                        expected_span,
                    ));
                }
                for (cur_arg_ty, exp_arg_ty) in cur.arguments.iter().zip(exp.arguments.iter()) {
                    self.unify_sub_type(
                        *cur_arg_ty,
                        current_span,
                        *exp_arg_ty,
                        expected_span,
                        outer_fresh_ty_var_gen,
                    )?;
                }
                Ok(())
            }
            (Variant(_a), Variant(_b)) => todo!("implement variant unification"),
            (Tuple(cur), Tuple(exp)) => {
                if cur.len() != exp.len() {
                    return Err(InternalCompilationError::IsNotSubtype(
                        cur_ty,
                        current_span,
                        exp_ty,
                        expected_span,
                    ));
                }
                for (cur_el_ty, exp_el_ty) in cur.iter().zip(exp.iter()) {
                    self.unify_sub_type(
                        *cur_el_ty,
                        current_span,
                        *exp_el_ty,
                        expected_span,
                        outer_fresh_ty_var_gen,
                    )?;
                }
                Ok(())
            }
            (Record(_a), Record(_b)) => todo!("implement record unification"),
            (Function(cur), Function(exp)) => {
                if cur.args.len() != exp.args.len() {
                    return Err(InternalCompilationError::IsNotSubtype(
                        cur_ty,
                        current_span,
                        exp_ty,
                        expected_span,
                    ));
                }
                for ((index, cur_arg), exp_arg) in cur.args.iter().enumerate().zip(exp.args.iter())
                {
                    // Contravariance of argument types.
                    self.unify_mut_must_be_at_least(
                        exp_arg.inout,
                        current_span,
                        cur_arg.inout,
                        expected_span,
                        MustBeMutableContext::FnTypeArg(index),
                    )?;
                    self.unify_sub_type(
                        exp_arg.ty,
                        current_span,
                        cur_arg.ty,
                        expected_span,
                        outer_fresh_ty_var_gen,
                    )?;
                }
                // Covariance of return type.
                self.unify_sub_type(
                    cur.ret,
                    current_span,
                    exp.ret,
                    expected_span,
                    outer_fresh_ty_var_gen,
                )
            }
            (Newtype(cur_name, cur_ty), Newtype(exp_name, exp_ty)) => {
                if cur_name != exp_name {
                    return Err(InternalCompilationError::IsNotSubtype(
                        cur_ty,
                        current_span,
                        exp_ty,
                        expected_span,
                    ));
                }
                self.unify_sub_type(
                    cur_ty,
                    current_span,
                    exp_ty,
                    expected_span,
                    outer_fresh_ty_var_gen,
                )
            }
            _ => Err(InternalCompilationError::IsNotSubtype(
                cur_ty,
                current_span,
                exp_ty,
                expected_span,
            )),
        }
    }

    fn unify_type_variable(
        &mut self,
        var: TypeVar,
        var_span: Span,
        ty: Type,
        ty_span: Span,
        outer_fresh_ty_var_gen: FreshTyVarGen<'_>,
    ) -> Result<(), InternalCompilationError> {
        if ty.data().contains_type_var(var) {
            Err(InternalCompilationError::InfiniteType(var, ty, ty_span))
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
                    self.ty_unification_table
                        .unify_var_value(var.as_key(), Some(ext_ty))
                        .map_err(|(l, r)| {
                            InternalCompilationError::IsNotSubtype(l, var_span, r, ty_span)
                        })?;
                    Ok::<(TypeVar, Type), InternalCompilationError>((*var, ext_ty))
                })
                .collect::<Result<_, _>>()?;
            log::debug!("Unified external type variable {var}, created {} new external type variables and replaced local ones", subst.len());
            // Create a new type using these new variables, and add an external constraint for it.
            let new_ty = ty.instantiate(&subst);
            self.add_sub_type_external_constraint(Type::variable(var), var_span, new_ty, ty_span);
            Ok(())
        } else {
            // The type variable is internal, perform normal unification.
            self.ty_unification_table
                .unify_var_value(var.as_key(), Some(ty))
                .map_err(|(l, r)| InternalCompilationError::IsNotSubtype(l, var_span, r, ty_span))
        }
    }

    fn unify_tuple_project(
        &mut self,
        PubTypeConstraint::TupleAtIndexIs {
            tuple_ty,
            tuple_span,
            index,
            index_span,
            element_ty,
        }: PubTypeConstraint,
        outer_fresh_ty_var_gen: FreshTyVarGen<'_>,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let tuple_ty = self.normalize_type(tuple_ty);
        let element_ty = self.normalize_type(element_ty);
        let tuple_data = { tuple_ty.data().clone() };
        match tuple_data {
            // A type variable may or may not be a tuple, defer the unification
            TypeKind::Variable(_) => Ok(Some(PubTypeConstraint::new_tuple_at_index_is(
                tuple_ty, tuple_span, index, index_span, element_ty,
            ))),
            // A tuple, verify length and element type
            TypeKind::Tuple(tys) => {
                if let Some(ty) = tys.get(index) {
                    self.unify_sub_type(
                        *ty,
                        tuple_span,
                        element_ty,
                        index_span,
                        outer_fresh_ty_var_gen,
                    )?;
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

    fn unify_mut_must_be_at_least(
        &mut self,
        current: MutType,
        current_span: Span,
        target: MutType,
        reason_span: Span,
        error_ctx: MustBeMutableContext,
    ) -> Result<(), InternalCompilationError> {
        let current_mut = self.normalize_mut_type(current);
        let target_mut = self.normalize_mut_type(target);
        // Note: here is the truth table of the constant/mutable relationship between current and target:
        //            | cur cst | cur mut
        // -----------|---------|---------
        // target cst |   ok    |   ok
        // target mut |   err   |   ok
        //
        use MutType::*;
        match (current_mut, target_mut) {
            (Variable(current), Variable(target)) => {
                let cur_is_local = current.generation() == self.generation;
                let tgt_is_local = target.generation() == self.generation;
                match (cur_is_local, tgt_is_local) {
                    (true, true) => {
                        // Both local, do normal unification. Ffuse both variable as it is acceptable
                        // due to the transitivity of the "must be at least mutability" relationship.
                        self.mut_unification_table
                            .unify_var_var(current.as_key(), target.as_key())
                            .map_err(|_| {
                                InternalCompilationError::MustBeMutable(
                                    current_span,
                                    reason_span,
                                    error_ctx,
                                )
                            })
                    }
                    (true, false) => {
                        // Both external, add a constraint.
                        self.add_mut_be_at_least_external_constraint(
                            current_mut,
                            current_span,
                            target_mut,
                            reason_span,
                        );
                        Ok(())
                    }
                    (false, true) => {
                        // Var current is local, target is external, assume target by to be a normal type.
                        self.unify_mut_variable(
                            current,
                            current_span,
                            target_mut,
                            reason_span,
                            error_ctx,
                        )
                    }
                    (false, false) => {
                        // Var current is external, target is local, assume current by to be a normal type.
                        self.unify_mut_variable(
                            target,
                            reason_span,
                            current_mut,
                            current_span,
                            error_ctx,
                        )
                    }
                }
            }
            (Variable(current), Resolved(_)) => {
                self.unify_mut_variable(current, current_span, target_mut, reason_span, error_ctx)
            }
            (Resolved(_), Variable(target)) => {
                self.unify_mut_variable(target, reason_span, current_mut, current_span, error_ctx)
            }
            (Resolved(current), Resolved(target)) => {
                // Both resolved, check mutability value coercion.
                if current < target {
                    Err(InternalCompilationError::MustBeMutable(
                        current_span,
                        reason_span,
                        error_ctx,
                    ))
                } else {
                    Ok(())
                }
            }
        }
    }

    pub fn unify_mut_variable(
        &mut self,
        var: MutVar,
        current_span: Span,
        target: MutType,
        reason_span: Span,
        error_ctx: MustBeMutableContext,
    ) -> Result<(), InternalCompilationError> {
        // Target is resolved, if it is constant, we are done as anything can be used as constant.
        if target == MutType::constant() {
            Ok(())
        } else if var.generation() != self.generation {
            self.add_mut_be_at_least_external_constraint(
                MutType::Variable(var),
                current_span,
                target,
                reason_span,
            );
            Ok(())
        } else {
            // If it is mutable, current must be mutable as well.
            self.mut_unification_table
                .unify_var_value(var.as_key(), Some(MutVal::mutable()))
                .map_err(|_| {
                    InternalCompilationError::MustBeMutable(current_span, reason_span, error_ctx)
                })
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
                let root = self.ty_unification_table.find(v.as_key());
                match self.ty_unification_table.probe_value(root) {
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
            .map(|arg| {
                FnArgType::new(
                    self.substitute_type(arg.ty, ignore),
                    self.substitute_mut_type(arg.inout),
                )
            })
            .collect::<Vec<_>>();
        let ret = self.substitute_type(fn_ty.ret, ignore);
        FnType::new(args, ret)
    }

    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType {
        match mut_ty {
            MutType::Resolved(_) => mut_ty,
            MutType::Variable(v) => {
                if v.generation() != self.generation {
                    return MutType::variable(v);
                }
                let root = self.mut_unification_table.find(v.as_key());
                match self.mut_unification_table.probe_value(root) {
                    Some(val) => MutType::resolved(val),
                    _ => MutType::variable(root.to_var(self.generation)),
                }
            }
        }
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
                app.ty = self.substitute_fn_type(&app.ty, ignore);
                // app.subst
                //     .iter_mut()
                //     .for_each(|(_, ty)| *ty = self.substitute_type(*ty, ignore));
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
            Iterate(iteration) => {
                self.substitute_node(&mut iteration.iterator, ignore);
                self.substitute_node(&mut iteration.body, ignore);
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
        constraint: &PubTypeConstraint,
        ignore: &[TypeVar],
    ) -> PubTypeConstraint {
        match constraint {
            PubTypeConstraint::TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => {
                let tuple_ty = self.substitute_type(*tuple_ty, ignore);
                let element_ty = self.substitute_type(*element_ty, ignore);
                PubTypeConstraint::new_tuple_at_index_is(
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
        let constraints = mem::take(&mut self.external_ty_constraints);
        self.external_ty_constraints = constraints
            .into_iter()
            .map(|constraint| {
                use TypeConstraint::*;
                match constraint {
                    SubType {
                        current,
                        current_span,
                        expected,
                        expected_span,
                    } => {
                        let current = self.substitute_type(current, &[]);
                        let expected = self.substitute_type(expected, &[]);
                        SubType {
                            current,
                            current_span,
                            expected,
                            expected_span,
                        }
                    }
                    Pub(cst) => Pub(self.substitute_constraint(&cst, &[])),
                }
            })
            .collect();
        let constraints = mem::take(&mut self.external_mut_constraints);
        self.external_mut_constraints = constraints
            .into_iter()
            .map(|constraint| {
                use MutConstraint::*;
                match constraint {
                    MutBeAtLeast {
                        current,
                        current_span,
                        target,
                        reason_span,
                    } => {
                        let current = self.substitute_mut_type(current);
                        let target = self.substitute_mut_type(target);
                        MutBeAtLeast {
                            current,
                            current_span,
                            target,
                            reason_span,
                        }
                    }
                }
            })
            .collect();
    }

    pub fn log_debug_constraints(&self, module_env: ModuleEnv) {
        if self.remaining_ty_constraints.is_empty() && self.external_ty_constraints.is_empty() {
            log::debug!(
                "No type constraints after unification (gen {}).",
                self.generation
            );
        } else {
            log::debug!(
                "Type constraints after unification (gen {}):",
                self.generation
            );
            if !self.remaining_ty_constraints.is_empty() {
                log::debug!("  Internal constraints:");
                for constraint in &self.remaining_ty_constraints {
                    log::debug!("    {}", constraint.format_with(&module_env));
                }
            }
            if !self.external_ty_constraints.is_empty() {
                log::debug!("  External constraints:");
                for constraint in &self.external_ty_constraints {
                    log::debug!("    {}", constraint.format_with(&module_env));
                }
            }
        }
        if self.external_mut_constraints.is_empty() {
            log::debug!(
                "No mutability constraints after unification (gen {}).",
                self.generation
            );
        } else {
            log::debug!(
                "Mutability constraints (external) after unification (gen {}):",
                self.generation
            );
            for constraint in &self.external_mut_constraints {
                log::debug!("  {}", constraint);
            }
        }
    }

    pub fn log_debug_substitution_table(&mut self, module_env: ModuleEnv) {
        log::debug!("Type substitution table (gen {}):", self.generation);
        for i in 0..self.ty_unification_table.len() {
            let key = TyVarKey(i as u32);
            let var = TypeVar::new(i as u32, self.generation);
            let value = self.ty_unification_table.probe_value(key);
            match value {
                Some(value) => log::debug!("  {var} → {}", value.format_with(&module_env)),
                None => log::debug!("  {var} → {}", {
                    let key = self.ty_unification_table.find(key);
                    TypeVar::new(key.0, self.generation)
                }),
            }
        }
        log::debug!("Mutability substitution table (gen {}):", self.generation);
        for i in 0..self.mut_unification_table.len() {
            let key = MutVarKey(i as u32);
            let var = MutVar::new(i as u32, self.generation);
            let value = self.mut_unification_table.probe_value(key);
            match value {
                Some(value) => log::debug!("  {var} → {}", value),
                None => log::debug!("  {var} → {}", {
                    let key = self.mut_unification_table.find(key);
                    MutVar::new(key.0, self.generation)
                }),
            }
        }
    }

    fn add_sub_type_external_constraint(
        &mut self,
        current: Type,
        current_span: Span,
        expected: Type,
        expected_span: Span,
    ) {
        if current == expected {
            return;
        }
        self.external_ty_constraints.push(TypeConstraint::SubType {
            current,
            current_span,
            expected,
            expected_span,
        });
    }

    fn add_mut_be_at_least_external_constraint(
        &mut self,
        current: MutType,
        current_span: Span,
        target: MutType,
        reason_span: Span,
    ) {
        if target == MutType::constant() {
            // everything has at least constant mutability
            return;
        }
        if current == MutType::mutable() {
            // mutable can be used for all cases
            return;
        }
        self.external_mut_constraints
            .push(MutConstraint::MutBeAtLeast {
                current,
                current_span,
                target,
                reason_span,
            });
    }
}
