use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    fmt::{self, Display},
};

use ena::unify::{EqUnifyValue, InPlaceUnificationTable, UnifyKey};
use itertools::{multiunzip, Itertools};
use lrpar::Span;
use ustr::Ustr;

use crate::{
    ast::{Expr, ExprKind},
    containers::{SVec2, B},
    dictionary_passing::DictionaryReq,
    error::{ADTAccessType, InternalCompilationError, MustBeMutableContext},
    format_string::emit_format_string_ast,
    function::{FunctionRef, ScriptFunction},
    ir::{self, EnvStore, FnInstData, Immediate, Node, NodeKind},
    module::{FmtWithModuleEnv, ModuleEnv, ModuleFunction},
    mutability::{MutType, MutVal, MutVar, MutVarKey},
    r#type::{FnArgType, FnType, NativeType, TyVarKey, Type, TypeKind, TypeSubstitution, TypeVar},
    std::{array::array_type, math::int_type, range::range_iterator_type},
    type_scheme::PubTypeConstraint,
    typing_env::{Local, TypingEnv},
    value::Value,
};

impl UnifyKey for TyVarKey {
    type Value = Option<Type>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "TyVarKey"
    }
}

impl EqUnifyValue for Type {}

impl UnifyKey for MutVarKey {
    type Value = Option<MutVal>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "MutVarKey"
    }
}

impl EqUnifyValue for MutVal {}

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
    pub fn contains_any_ty_vars(&self, vars: &[TypeVar]) -> bool {
        use TypeConstraint::*;
        match self {
            SubType {
                current, expected, ..
            } => {
                current.data().contains_any_ty_vars(vars)
                    || expected.data().contains_any_ty_vars(vars)
            }
            Pub(pub_constraint) => pub_constraint.contains_any_ty_vars(vars),
        }
    }
}

impl FmtWithModuleEnv for TypeConstraint {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        use TypeConstraint::*;
        match self {
            SubType {
                current, expected, ..
            } => {
                write!(
                    f,
                    "{} ≤ {}",
                    current.format_with(env),
                    expected.format_with(env)
                )
            }
            Pub(pub_constraint) => pub_constraint.fmt_with_module_env(f, env),
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
    ty_unification_table: InPlaceUnificationTable<TyVarKey>,
    ty_constraints: Vec<TypeConstraint>,
    mut_unification_table: InPlaceUnificationTable<MutVarKey>,
    mut_constraints: Vec<MutConstraint>,
}

impl TypeInference {
    pub fn new() -> Self {
        Self::default()
    }

    // TODO: improve error reporting by storing the span of the expression triggering the fresh variable creation
    pub fn fresh_type_var(&mut self) -> TypeVar {
        self.ty_unification_table.new_key(None)
    }

    pub fn fresh_type_var_ty(&mut self) -> Type {
        Type::variable(self.fresh_type_var())
    }

    pub fn fresh_mut_var(&mut self) -> MutVar {
        self.mut_unification_table.new_key(None)
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
            Literal(value, ty) => (
                K::Immediate(Immediate::new(value.clone())),
                *ty,
                MutType::constant(),
            ),
            FormattedString(s) => {
                let expr = emit_format_string_ast(s, expr.span, env)?;
                return self.infer_expr(env, &expr);
            }
            Identifier(name) => {
                // Retrieve the index and the type of the variable from the environment, if it exists
                if let Some((index, ty, mut_ty)) = env.get_variable_index_and_type_scheme(name) {
                    let node = K::EnvLoad(B::new(ir::EnvLoad { index }));
                    (node, ty, mut_ty)
                }
                // Retrieve the function from the environment, if it exists
                else if let Some(function) = env.get_function(*name) {
                    let (fn_ty, inst_data) = function.ty_scheme.instantiate(self);
                    let value = Value::Function(FunctionRef::new_weak(&function.code));
                    let node = K::Immediate(B::new(ir::Immediate {
                        value,
                        inst_data,
                        substitute_in_value_fn: false,
                    }));
                    (node, Type::function_type(fn_ty), MutType::constant())
                }
                // Otherwise, the name is neither a known variable or function, assume it to be a variant constructor
                else {
                    // Create a fresh type and add a constraint for that type to include this variant.
                    let variant_ty = self.fresh_type_var_ty();
                    let payload_ty = Type::unit();
                    self.ty_constraints.push(TypeConstraint::Pub(
                        PubTypeConstraint::new_type_has_variant(
                            variant_ty, *name, payload_ty, expr.span,
                        ),
                    ));
                    // Build the variant construction node.
                    let payload_node = N::new(
                        K::Immediate(Immediate::new(Value::unit())),
                        payload_ty,
                        expr.span,
                    );
                    let node = K::Variant(B::new((*name, payload_node)));
                    (node, variant_ty, MutType::constant())
                }
            }
            LetVar((name, name_span), mutable, let_expr) => {
                // Mutable variable, do not do generalization.
                let (node, ty, _) = self.infer_expr(env, let_expr)?;
                env.locals.push(Local::new(
                    *name,
                    MutType::resolved(*mutable),
                    ty,
                    expr.span,
                ));
                let node = K::EnvStore(B::new(EnvStore {
                    node,
                    ty,
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
                            self.fresh_type_var_ty(),
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
                let node = K::Immediate(Immediate::new(value_fn));
                (node, Type::function_type(fn_ty), MutType::constant())
            }
            Apply(func, args) => {
                // Do we have a global function?
                if let Identifier(name) = func.kind {
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
            StaticApply(name, span, args) => self.infer_static_apply(env, *name, *span, args)?,
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
            Record(fields) => {
                let (exprs, names): (Vec<_>, Vec<_>) = fields
                    .iter()
                    .map(|(name, span, expr)| (expr, (*name, *span)))
                    .unzip();
                // Check that all fields are unique.
                let mut names_seen = HashMap::new();
                for (name, span) in names.iter().copied() {
                    if let Some(prev_span) = names_seen.insert(name, span) {
                        return Err(InternalCompilationError::DuplicatedRecordField {
                            first_occurrence: prev_span,
                            second_occurrence: span,
                        });
                    }
                }
                // Infer the types of the nodes.
                let (nodes, types) = self.infer_exprs_drop_mut(env, &exprs)?;
                // Reorder the names, the types and the nodes to have fields sorted by name.
                let mut names = names.into_iter().map(|(name, _)| name).collect::<Vec<_>>();
                let mut named_nodes = HashMap::new();
                for (name, node_and_ty) in
                    names.iter().zip(nodes.into_iter().zip(types.into_iter()))
                {
                    named_nodes.insert(*name, node_and_ty);
                }
                names.sort();
                let (nodes, types): (Vec<_>, Vec<_>) = names
                    .iter()
                    .map(|name| named_nodes.remove(name).unwrap())
                    .unzip();
                // Build the record node and return it.
                // Note: we assume that while building the record, if the names are sorted, they won't be shuffled.
                let node = K::Record(B::new(SVec2::from_vec(nodes)));
                let ty = Type::record(names.into_iter().zip(types).collect());
                (node, ty, MutType::constant())
            }
            FieldAccess(record_expr, field, field_span) => {
                let (record_node, record_ty, record_mut) = self.infer_expr(env, record_expr)?;
                let element_ty = self.fresh_type_var_ty();
                self.ty_constraints.push(TypeConstraint::Pub(
                    PubTypeConstraint::new_record_field_is(
                        record_ty,
                        record_expr.span,
                        *field,
                        *field_span,
                        element_ty,
                    ),
                ));
                let node = K::FieldAccess(B::new((record_node, *field)));
                (node, element_ty, record_mut)
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
            Match(cond_expr, alternatives, default) => {
                let (node, ty, mut_ty) =
                    self.infer_match(env, expr, cond_expr, alternatives, default)?;
                return Ok((N::new(node, ty, expr.span), ty, mut_ty));
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
                    int_type(),
                    var_name.1,
                ));
                let body =
                    self.check_expr(env, body, Type::unit(), MutType::constant(), body.span)?;
                env.locals.truncate(env_size);
                let var_name_span = var_name.1;
                let node = K::Iterate(B::new(ir::Iteration {
                    iterator,
                    body,
                    var_name_span,
                }));
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
        args: &[impl Borrow<Expr>],
    ) -> Result<(NodeKind, Type, MutType), InternalCompilationError> {
        use ir::Node as N;
        use ir::NodeKind as K;
        // Get the function and its type from the environment.
        Ok(if let Some(function) = env.get_function(name) {
            if function.ty_scheme.ty.args.len() != args.len() {
                let got_span = args
                    .iter()
                    .map(|arg| arg.borrow().span)
                    .reduce(|a, b| Span::new(a.start(), b.end()))
                    .unwrap_or(span);
                return Err(InternalCompilationError::WrongNumberOfArguments {
                    expected: function.ty_scheme.ty.args.len(),
                    expected_span: span,
                    got: args.len(),
                    got_span,
                });
            }
            // Instantiate its type scheme
            let (inst_fn_ty, inst_data) = function.ty_scheme.instantiate(self);
            // Get the code and make sure the types of its arguments match the expected types
            let args_nodes = self.check_exprs(env, args, &inst_fn_ty.args, span)?;
            // Build and return the function node, get back the function to avoid re-borrowing
            let function = env
                .get_function(name)
                .expect("function not found any more after checking");
            let ret_ty = inst_fn_ty.ret;
            let node = K::StaticApply(B::new(ir::StaticApplication {
                function: FunctionRef::new_weak(&function.code),
                function_name: name,
                function_span: span,
                arguments: args_nodes,
                ty: inst_fn_ty,
                inst_data,
            }));
            (node, ret_ty, MutType::constant())
        } else {
            // If it is not a known function, assume it to be a variant constructor
            // Create a fresh type and add a constraint for that type to include this variant.
            let variant_ty = self.fresh_type_var_ty();
            let (payload_nodes, payload_types) = self.infer_exprs_drop_mut(env, args)?;
            let (payload_ty, payload_node) = match payload_nodes.len() {
                0 => (
                    Type::unit(),
                    N::new(
                        K::Immediate(Immediate::new(Value::unit())),
                        Type::unit(),
                        span,
                    ),
                ),
                1 => {
                    let payload_ty = payload_types[0];
                    let payload_node = payload_nodes.into_iter().next().unwrap();
                    (payload_ty, payload_node)
                }
                _ => {
                    let payload_ty = Type::tuple(payload_types);
                    (
                        payload_ty,
                        N::new(
                            K::Tuple(B::new(SVec2::from_vec(payload_nodes))),
                            payload_ty,
                            span,
                        ),
                    )
                }
            };
            self.ty_constraints.push(TypeConstraint::Pub(
                PubTypeConstraint::new_type_has_variant(variant_ty, name, payload_ty, span),
            ));
            // Build the variant construction node.
            let node = K::Variant(B::new((name, payload_node)));
            (node, variant_ty, MutType::constant())
        })
    }

    fn infer_exprs_drop_mut(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[impl Borrow<Expr>],
    ) -> Result<(Vec<ir::Node>, Vec<Type>), InternalCompilationError> {
        exprs
            .iter()
            .map(|arg| {
                let (node, ty, _mut_ty) = self.infer_expr(env, arg.borrow())?;
                Ok::<(ir::Node, Type), InternalCompilationError>((node, ty))
            })
            .process_results(|iter| multiunzip(iter))
    }

    fn infer_exprs_ret_arg_ty(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[impl Borrow<Expr>],
    ) -> Result<(Vec<ir::Node>, Vec<FnArgType>), InternalCompilationError> {
        exprs
            .iter()
            .map(|arg| {
                let (node, ty, mut_ty) = self.infer_expr(env, arg.borrow())?;
                Ok::<(ir::Node, FnArgType), InternalCompilationError>((
                    node,
                    FnArgType::new(ty, mut_ty),
                ))
            })
            .process_results(|iter| multiunzip(iter))
    }

    fn check_exprs(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[impl Borrow<Expr>],
        expected_tys: &[FnArgType],
        expected_span: Span,
    ) -> Result<Vec<ir::Node>, InternalCompilationError> {
        exprs
            .iter()
            .zip(expected_tys)
            .map(|(arg, arg_ty)| {
                let node =
                    self.check_expr(env, arg.borrow(), arg_ty.ty, arg_ty.inout, expected_span)?;
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
                let node = K::Immediate(Immediate::new(value.clone()));
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
                    .map(|((name, span), arg_ty)| Local::new(*name, arg_ty.inout, arg_ty.ty, *span))
                    .collect::<Vec<_>>();
                // Build environment for typing the function's body
                let mut env = TypingEnv::new(locals, env.module_env);
                // Recursively check the function's body
                let code =
                    self.check_expr(&mut env, body, fn_ty.ret, MutType::constant(), body.span)?;
                // Store and return the function's type
                let value_fn = Value::function(B::new(ScriptFunction::new(code)));
                let node = K::Immediate(Immediate::new(value_fn));
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
            log::debug!("No type constraints before unification.");
        } else {
            log::debug!("Type constraints before unification:");
            for constraint in &self.ty_constraints {
                log::debug!("  {}", constraint.format_with(&module_env));
            }
        }
        if self.mut_constraints.is_empty() {
            log::debug!("No mutability constraints before unification.");
        } else {
            log::debug!("Mutability constraints before unification:");
            for constraint in &self.mut_constraints {
                log::debug!("  {}", constraint);
            }
        }
    }

    pub(crate) fn add_sub_type_constraint(
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

    pub fn unify(self) -> Result<UnifiedTypeInference, InternalCompilationError> {
        UnifiedTypeInference::unify_type_inference(self)
    }
}

/// The type inference after unification, with only public constraints remaining
#[derive(Default, Debug)]
pub struct UnifiedTypeInference {
    ty_unification_table: InPlaceUnificationTable<TyVarKey>,
    /// Remaining constraints that cannot be solved, will be part of the resulting type scheme
    remaining_ty_constraints: Vec<PubTypeConstraint>,
    mut_unification_table: InPlaceUnificationTable<MutVarKey>,
}

impl UnifiedTypeInference {
    pub fn unify_type_inference(ty_inf: TypeInference) -> Result<Self, InternalCompilationError> {
        let TypeInference {
            ty_unification_table,
            ty_constraints,
            mut_unification_table,
            mut_constraints,
        } = ty_inf;
        let mut unified_ty_inf = UnifiedTypeInference {
            ty_unification_table,
            remaining_ty_constraints: vec![],
            mut_unification_table,
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
            let var = MutVarKey::new(var as u32);
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
                } => {
                    unified_ty_inf.unify_sub_type(current, current_span, expected, expected_span)?
                }
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

                // Perform simplification for tuple and record constraints.
                // Check for incompatible constraints as well.
                let mut tuples_at_index_is: HashMap<Type, HashMap<usize, (Type, Span)>> =
                    HashMap::new();
                let mut records_field_is: HashMap<Type, HashMap<Ustr, (Type, Span)>> =
                    HashMap::new();
                let mut variants_are: HashMap<Type, HashMap<Ustr, (Type, Span)>> = HashMap::new();
                for constraint in &remaining_constraints {
                    use PubTypeConstraint::*;
                    match constraint {
                        TupleAtIndexIs {
                            tuple_ty,
                            tuple_span,
                            index,
                            index_span,
                            element_ty,
                        } => {
                            let tuple_ty = unified_ty_inf.normalize_type(*tuple_ty);
                            let element_ty = unified_ty_inf.normalize_type(*element_ty);
                            let span = Span::new(tuple_span.start(), index_span.end());
                            if let Some(variant) = variants_are.get(&tuple_ty) {
                                let variant_span = variant.iter().next().unwrap().1 .1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::Variant,
                                    variant_span,
                                    ADTAccessType::TupleProject,
                                    span,
                                ));
                            } else if let Some(record) = records_field_is.get(&tuple_ty) {
                                let field_span = record.iter().next().unwrap().1 .1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::RecordAccess,
                                    field_span,
                                    ADTAccessType::TupleProject,
                                    span,
                                ));
                            } else if let Some(tuple) = tuples_at_index_is.get_mut(&tuple_ty) {
                                if let Some((expected_ty, expected_span)) = tuple.get(index) {
                                    unified_ty_inf.unify_sub_type(
                                        element_ty,
                                        span,
                                        *expected_ty,
                                        *expected_span,
                                    )?;
                                } else {
                                    tuple.insert(*index, (element_ty, span));
                                }
                            } else {
                                let tuple = HashMap::from([(*index, (element_ty, span))]);
                                tuples_at_index_is.insert(tuple_ty, tuple);
                            }
                        }
                        RecordFieldIs {
                            record_ty,
                            field,
                            field_span,
                            element_ty,
                            record_span,
                        } => {
                            let record_ty = unified_ty_inf.normalize_type(*record_ty);
                            let element_ty = unified_ty_inf.normalize_type(*element_ty);
                            let span = Span::new(record_span.start(), field_span.end());
                            if let Some(variant) = variants_are.get(&record_ty) {
                                let variant_span = variant.iter().next().unwrap().1 .1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::Variant,
                                    variant_span,
                                    ADTAccessType::TupleProject,
                                    span,
                                ));
                            } else if let Some(tuple) = tuples_at_index_is.get(&record_ty) {
                                let index_span = tuple.iter().next().unwrap().1 .1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::TupleProject,
                                    index_span,
                                    ADTAccessType::RecordAccess,
                                    span,
                                ));
                            } else if let Some(record) = records_field_is.get_mut(&record_ty) {
                                if let Some((expected_ty, expected_span)) = record.get(field) {
                                    unified_ty_inf.unify_sub_type(
                                        element_ty,
                                        span,
                                        *expected_ty,
                                        *expected_span,
                                    )?;
                                } else {
                                    record.insert(*field, (element_ty, span));
                                }
                            } else {
                                let record = HashMap::from([(*field, (element_ty, span))]);
                                records_field_is.insert(record_ty, record);
                            }
                        }
                        TypeHasVariant {
                            variant_ty: ty,
                            tag: variant,
                            payload_ty,
                            span: variant_span,
                        } => {
                            let ty = unified_ty_inf.normalize_type(*ty);
                            let payload_ty = unified_ty_inf.normalize_type(*payload_ty);
                            if let Some(tuple) = tuples_at_index_is.get(&ty) {
                                let index_span = tuple.iter().next().unwrap().1 .1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::TupleProject,
                                    index_span,
                                    ADTAccessType::Variant,
                                    *variant_span,
                                ));
                            } else if let Some(record) = records_field_is.get(&ty) {
                                let field_span = record.iter().next().unwrap().1 .1;
                                return Err(InternalCompilationError::new_inconsistent_adt(
                                    ADTAccessType::RecordAccess,
                                    field_span,
                                    ADTAccessType::Variant,
                                    *variant_span,
                                ));
                            } else if let Some(variants) = variants_are.get_mut(&ty) {
                                if let Some((expected_ty, expected_span)) = variants.get(variant) {
                                    unified_ty_inf.unify_sub_type(
                                        payload_ty,
                                        *variant_span,
                                        *expected_ty,
                                        *expected_span,
                                    )?;
                                } else {
                                    variants.insert(*variant, (payload_ty, *variant_span));
                                }
                            } else {
                                let variant =
                                    HashMap::from([(*variant, (payload_ty, *variant_span))]);
                                variants_are.insert(ty, variant);
                            }
                        }
                    }
                }

                // Perform unification.
                let mut new_remaining_constraints = HashSet::new();
                for constraint in remaining_constraints {
                    use PubTypeConstraint::*;
                    let new_progress = match constraint {
                        TupleAtIndexIs {
                            tuple_ty,
                            tuple_span,
                            index,
                            index_span,
                            element_ty,
                        } => unified_ty_inf.unify_tuple_project(
                            tuple_ty, tuple_span, index, index_span, element_ty,
                        )?,
                        RecordFieldIs {
                            record_ty,
                            record_span,
                            field,
                            field_span,
                            element_ty,
                        } => unified_ty_inf.unify_record_field_access(
                            record_ty,
                            record_span,
                            field,
                            field_span,
                            element_ty,
                        )?,
                        TypeHasVariant {
                            variant_ty: ty,
                            tag,
                            payload_ty: variant_ty,
                            span: variant_span,
                        } => unified_ty_inf.unify_type_has_variant(
                            ty,
                            tag,
                            variant_ty,
                            variant_span,
                        )?,
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

    pub fn constraints(self) -> Vec<PubTypeConstraint> {
        self.remaining_ty_constraints
    }

    fn normalize_type(&mut self, ty: Type) -> Type {
        let type_data = { ty.data().clone() };
        use TypeKind::*;
        match type_data {
            Variable(v) => {
                let id = v;
                match self.ty_unification_table.probe_value(id) {
                    Some(ty) => self.normalize_type(ty),
                    _ => Type::variable(self.ty_unification_table.find(id)),
                }
            }
            Native(ty) => Type::native_type(NativeType::new(
                ty.bare_ty.clone(),
                self.normalize_types(&ty.arguments),
            )),
            Variant(tys) => Type::variant(
                tys.into_iter()
                    .map(|(name, ty)| (name, self.normalize_type(ty)))
                    .collect(),
            ),
            Tuple(tys) => Type::tuple(self.normalize_types(&tys)),
            Record(fields) => Type::record(
                fields
                    .into_iter()
                    .map(|(name, ty)| (name, self.normalize_type(ty)))
                    .collect(),
            ),
            Function(fn_ty) => Type::function_type(self.normalize_fn_type(&fn_ty)),
            Newtype(name, ty) => Type::new_type(name, self.normalize_type(ty)),
            Never => ty,
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
            MutType::Variable(var) => match self.mut_unification_table.probe_value(var) {
                Some(val) => MutType::resolved(val),
                _ => MutType::variable(self.mut_unification_table.find(var)),
            },
        }
    }

    fn unify_sub_type(
        &mut self,
        current: Type,
        current_span: Span,
        expected: Type,
        expected_span: Span,
    ) -> Result<(), InternalCompilationError> {
        let cur_ty = self.normalize_type(current);
        let exp_ty = self.normalize_type(expected);
        let cur_data = { cur_ty.data().clone() };
        let exp_data = { exp_ty.data().clone() };
        use TypeKind::*;
        match (cur_data, exp_data) {
            (Variable(cur), Variable(exp)) => self
                .ty_unification_table
                .unify_var_var(cur, exp)
                .map_err(|_| {
                    InternalCompilationError::IsNotSubtype(
                        cur_ty,
                        current_span,
                        exp_ty,
                        expected_span,
                    )
                }),
            (Variable(var), _) => {
                self.unify_type_variable(var, current_span, exp_ty, expected_span)
            }
            (_, Variable(var)) => {
                self.unify_type_variable(var, expected_span, cur_ty, current_span)
            }
            (Native(cur), Native(exp)) => {
                if cur.bare_ty != exp.bare_ty {
                    return Err(InternalCompilationError::IsNotSubtype(
                        cur_ty,
                        current_span,
                        exp_ty,
                        expected_span,
                    ));
                }
                for (cur_arg_ty, exp_arg_ty) in
                    cur.arguments.into_iter().zip(exp.arguments.into_iter())
                {
                    self.unify_sub_type(cur_arg_ty, current_span, exp_arg_ty, expected_span)?;
                }
                Ok(())
            }
            (Variant(cur), Variant(exp)) => {
                if cur.len() != exp.len() {
                    return Err(InternalCompilationError::IsNotSubtype(
                        cur_ty,
                        current_span,
                        exp_ty,
                        expected_span,
                    ));
                }
                for (cur_variant, exp_variant) in cur.into_iter().zip(exp.into_iter()) {
                    if cur_variant.0 != exp_variant.0 {
                        return Err(InternalCompilationError::IsNotSubtype(
                            cur_ty,
                            current_span,
                            exp_ty,
                            expected_span,
                        ));
                    }
                    self.unify_sub_type(cur_variant.1, current_span, exp_variant.1, expected_span)?;
                }
                Ok(())
            }
            (Tuple(cur), Tuple(exp)) => {
                if cur.len() != exp.len() {
                    return Err(InternalCompilationError::IsNotSubtype(
                        cur_ty,
                        current_span,
                        exp_ty,
                        expected_span,
                    ));
                }
                for (cur_el_ty, exp_el_ty) in cur.into_iter().zip(exp.into_iter()) {
                    self.unify_sub_type(cur_el_ty, current_span, exp_el_ty, expected_span)?;
                }
                Ok(())
            }
            (Record(cur), Record(exp)) => {
                for (cur_field, exp_field) in cur.into_iter().zip(exp) {
                    if cur_field.0 != exp_field.0 {
                        return Err(InternalCompilationError::IsNotSubtype(
                            cur_ty,
                            current_span,
                            exp_ty,
                            expected_span,
                        ));
                    }
                    self.unify_sub_type(cur_field.1, current_span, exp_field.1, expected_span)?;
                }
                Ok(())
            }
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
                    self.unify_sub_type(exp_arg.ty, current_span, cur_arg.ty, expected_span)?;
                }
                // Covariance of return type.
                self.unify_sub_type(cur.ret, current_span, exp.ret, expected_span)
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
                self.unify_sub_type(cur_ty, current_span, exp_ty, expected_span)
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
    ) -> Result<(), InternalCompilationError> {
        if ty.data().contains_any_type_var(var) {
            Err(InternalCompilationError::InfiniteType(var, ty, ty_span))
        } else {
            self.ty_unification_table
                .unify_var_value(var, Some(ty))
                .map_err(|(l, r)| InternalCompilationError::IsNotSubtype(l, var_span, r, ty_span))
        }
    }

    fn unify_tuple_project(
        &mut self,
        tuple_ty: Type,
        tuple_span: Span,
        index: usize,
        index_span: Span,
        element_ty: Type,
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
                    self.unify_sub_type(*ty, tuple_span, element_ty, index_span)?;
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
                tuple_ty,
                tuple_span,
                index_span,
            }),
        }
    }

    fn unify_record_field_access(
        &mut self,
        record_ty: Type,
        record_span: Span,
        field: Ustr,
        field_span: Span,
        element_ty: Type,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let record_ty = self.normalize_type(record_ty);
        let element_ty = self.normalize_type(element_ty);
        let record_data = { record_ty.data().clone() };
        match record_data {
            // A type variable may or may not be a tuple, defer the unification
            TypeKind::Variable(_) => Ok(Some(PubTypeConstraint::new_record_field_is(
                record_ty,
                record_span,
                field,
                field_span,
                element_ty,
            ))),
            // A record, verify element type
            TypeKind::Record(tys) => {
                if let Some(ty) = tys
                    .iter()
                    .find_map(|(name, ty)| if *name == field { Some(*ty) } else { None })
                {
                    self.unify_sub_type(ty, record_span, element_ty, field_span)?;
                    Ok(None)
                } else {
                    Err(InternalCompilationError::InvalidRecordField {
                        field_span,
                        record_ty,
                        record_span,
                    })
                }
            }
            // Not a record, error
            _ => Err(InternalCompilationError::InvalidRecordFieldAccess {
                record_ty,
                record_span,
                field_span,
            }),
        }
    }

    fn unify_type_has_variant(
        &mut self,
        ty: Type,
        tag: Ustr,
        variant_ty: Type,
        variant_span: Span,
    ) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
        let ty = self.normalize_type(ty);
        let variant_ty = self.normalize_type(variant_ty);
        let data = { ty.data().clone() };
        match data {
            // A type variable may or may not be a variant, defer the unification
            TypeKind::Variable(_) => Ok(Some(PubTypeConstraint::new_type_has_variant(
                ty,
                tag,
                variant_ty,
                variant_span,
            ))),
            // A variant, verify payload type
            TypeKind::Variant(variants) => {
                if let Some(ty) =
                    variants
                        .iter()
                        .find_map(|(name, ty)| if *name == tag { Some(ty) } else { None })
                {
                    self.unify_sub_type(*ty, variant_span, variant_ty, variant_span)?;
                    Ok(None)
                } else {
                    Err(InternalCompilationError::InvalidVariantName {
                        name: variant_span,
                        ty,
                    })
                }
            }
            // Not a variant, error
            _ => Err(InternalCompilationError::InvalidVariantType {
                name: variant_span,
                ty,
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
                // Do unification. Fuse both variable as it is acceptable
                // due to the transitivity of the "must be at least mutability" relationship.
                self.mut_unification_table
                    .unify_var_var(current, target)
                    .map_err(|_| {
                        InternalCompilationError::MustBeMutable(
                            current_span,
                            reason_span,
                            error_ctx,
                        )
                    })
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
        } else {
            // If it is mutable, current must be mutable as well.
            self.mut_unification_table
                .unify_var_value(var, Some(MutVal::mutable()))
                .map_err(|_| {
                    InternalCompilationError::MustBeMutable(current_span, reason_span, error_ctx)
                })
        }
    }

    pub(crate) fn substitute_in_module_function(&mut self, descr: &mut ModuleFunction) {
        descr.ty_scheme.ty = self.substitute_in_fn_type(&descr.ty_scheme.ty, &[]);
        assert!(descr.ty_scheme.constraints.is_empty());
        let mut code = descr.code.borrow_mut();
        if let Some(script_fn) = code.as_script_mut() {
            self.substitute_in_node(&mut script_fn.code, &[]);
        }
    }

    pub fn substitute_in_type(&mut self, ty: Type, ignore: &[TypeVar]) -> Type {
        let type_data: TypeKind = { ty.data().clone() };
        use TypeKind::*;
        match type_data {
            Variable(var) => {
                if ignore.contains(&var) {
                    return Type::variable(var);
                }
                let root = self.ty_unification_table.find(var);
                match self.ty_unification_table.probe_value(root) {
                    Some(ty) => self.substitute_in_type(ty, ignore),
                    _ => Type::variable(root),
                }
            }
            Native(ty) => Type::native_type(NativeType::new(
                ty.bare_ty.clone(),
                self.substitute_in_types(&ty.arguments, ignore),
            )),
            Variant(tys) => Type::variant(
                tys.into_iter()
                    .map(|(name, ty)| (name, self.substitute_in_type(ty, ignore)))
                    .collect(),
            ),
            Tuple(tys) => Type::tuple(self.substitute_in_types(&tys, ignore)),
            Record(fields) => Type::record(
                fields
                    .into_iter()
                    .map(|(name, ty)| (name, self.substitute_in_type(ty, ignore)))
                    .collect(),
            ),
            Function(fn_ty) => Type::function_type(self.substitute_in_fn_type(&fn_ty, ignore)),
            Newtype(name, ty) => Type::new_type(name, self.substitute_in_type(ty, ignore)),
            Never => ty,
        }
    }

    fn substitute_in_types(&mut self, tys: &[Type], ignore: &[TypeVar]) -> Vec<Type> {
        tys.iter()
            .map(|ty| self.substitute_in_type(*ty, ignore))
            .collect()
    }

    pub fn substitute_in_fn_type(&mut self, fn_ty: &FnType, ignore: &[TypeVar]) -> FnType {
        let args = fn_ty
            .args
            .iter()
            .map(|arg| {
                FnArgType::new(
                    self.substitute_in_type(arg.ty, ignore),
                    self.substitute_mut_type(arg.inout),
                )
            })
            .collect::<Vec<_>>();
        let ret = self.substitute_in_type(fn_ty.ret, ignore);
        FnType::new(args, ret)
    }

    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType {
        match mut_ty {
            MutType::Resolved(_) => mut_ty,
            MutType::Variable(var) => {
                let root = self.mut_unification_table.find(var);
                match self.mut_unification_table.probe_value(root) {
                    Some(val) => MutType::resolved(val),
                    _ => MutType::variable(root),
                }
            }
        }
    }

    pub fn substitute_in_node(&mut self, node: &mut ir::Node, ignore: &[TypeVar]) {
        use ir::NodeKind::*;
        node.ty = self.substitute_in_type(node.ty, ignore);
        match &mut node.kind {
            Immediate(immediate) => {
                self.substitute_in_value(&mut immediate.value, ignore);
                self.substitute_in_fn_inst_data(&mut immediate.inst_data, ignore);
            }
            BuildClosure(_) => panic!("BuildClosure should not be present at this stage"),
            Apply(app) => {
                self.substitute_in_node(&mut app.function, ignore);
                self.substitute_in_nodes(&mut app.arguments, ignore);
            }
            StaticApply(app) => {
                app.ty = self.substitute_in_fn_type(&app.ty, ignore);
                self.substitute_in_nodes(&mut app.arguments, ignore);
                self.substitute_in_fn_inst_data(&mut app.inst_data, ignore);
            }
            EnvStore(node) => {
                self.substitute_in_node(&mut node.node, ignore);
                node.ty = self.substitute_in_type(node.ty, ignore);
            }
            EnvLoad(_) => {}
            Block(nodes) => self.substitute_in_nodes(nodes, ignore),
            Assign(assignment) => {
                self.substitute_in_node(&mut assignment.place, ignore);
                self.substitute_in_node(&mut assignment.value, ignore);
            }
            Tuple(nodes) => self.substitute_in_nodes(nodes, ignore),
            Project(projection) => self.substitute_in_node(&mut projection.0, ignore),
            Record(nodes) => self.substitute_in_nodes(nodes, ignore),
            FieldAccess(node_and_field) => self.substitute_in_node(&mut node_and_field.0, ignore),
            ProjectAt(projection) => self.substitute_in_node(&mut projection.0, ignore),
            Variant(variant) => self.substitute_in_node(&mut variant.1, ignore),
            ExtractTag(node) => self.substitute_in_node(node, ignore),
            Array(nodes) => self.substitute_in_nodes(nodes, ignore),
            Index(array, index) => {
                self.substitute_in_node(array, ignore);
                self.substitute_in_node(index, ignore);
            }
            Case(case) => {
                self.substitute_in_node(&mut case.value, ignore);
                for alternative in case.alternatives.iter_mut() {
                    self.substitute_in_value(&mut alternative.0, ignore);
                    self.substitute_in_node(&mut alternative.1, ignore);
                }
                self.substitute_in_node(&mut case.default, ignore);
            }
            Iterate(iteration) => {
                self.substitute_in_node(&mut iteration.iterator, ignore);
                self.substitute_in_node(&mut iteration.body, ignore);
            }
        }
    }

    fn substitute_in_nodes(&mut self, nodes: &mut [ir::Node], ignore: &[TypeVar]) {
        for node in nodes {
            self.substitute_in_node(node, ignore);
        }
    }

    fn substitute_in_fn_inst_data(&mut self, inst_data: &mut FnInstData, ignore: &[TypeVar]) {
        inst_data.dicts_req = inst_data
            .dicts_req
            .iter()
            .map(|dict| DictionaryReq::new(self.substitute_in_type(dict.ty, ignore), dict.kind))
            .collect();
    }

    fn substitute_in_value(&mut self, value: &mut Value, ignore: &[TypeVar]) {
        match value {
            Value::Tuple(tuple) => {
                for value in tuple.iter_mut() {
                    self.substitute_in_value(value, ignore);
                }
            }
            Value::Function(function) => {
                let function = function.get();
                // Note: this can fail if we are having a recursive function used as a value, in that case do not recurse.
                let function = function.try_borrow_mut();
                if let Ok(mut function) = function {
                    if let Some(script_fn) = function.as_script_mut() {
                        self.substitute_in_node(&mut script_fn.code, ignore);
                    }
                }
            }
            _ => {}
        }
    }

    fn substitute_in_constraint(
        &mut self,
        constraint: &PubTypeConstraint,
        ignore: &[TypeVar],
    ) -> PubTypeConstraint {
        use PubTypeConstraint::*;
        match constraint {
            TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => {
                let tuple_ty = self.substitute_in_type(*tuple_ty, ignore);
                let element_ty = self.substitute_in_type(*element_ty, ignore);
                PubTypeConstraint::new_tuple_at_index_is(
                    tuple_ty,
                    *tuple_span,
                    *index,
                    *index_span,
                    element_ty,
                )
            }
            RecordFieldIs {
                record_ty,
                record_span,
                field,
                field_span,
                element_ty,
            } => {
                let record_ty = self.substitute_in_type(*record_ty, ignore);
                let element_ty = self.substitute_in_type(*element_ty, ignore);
                PubTypeConstraint::new_record_field_is(
                    record_ty,
                    *record_span,
                    *field,
                    *field_span,
                    element_ty,
                )
            }
            TypeHasVariant {
                variant_ty: ty,
                tag,
                payload_ty: variant_ty,
                span: variant_span,
            } => {
                let ty = self.substitute_in_type(*ty, ignore);
                let variant_ty = self.substitute_in_type(*variant_ty, ignore);
                PubTypeConstraint::new_type_has_variant(ty, *tag, variant_ty, *variant_span)
            }
        }
    }

    pub fn log_debug_constraints(&self, module_env: ModuleEnv) {
        if self.remaining_ty_constraints.is_empty() {
            log::debug!("No type constraints after unification.");
        } else {
            log::debug!("Type constraints after unification:");
            if !self.remaining_ty_constraints.is_empty() {
                for constraint in &self.remaining_ty_constraints {
                    log::debug!("  {}", constraint.format_with(&module_env));
                }
            }
        }
    }

    pub fn log_debug_substitution_table(&mut self, module_env: ModuleEnv) {
        log::debug!("Type substitution table:");
        for i in 0..self.ty_unification_table.len() {
            let var = TypeVar::new(i as u32);
            let value = self.ty_unification_table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {}", value.format_with(&module_env)),
                None => log::debug!("  {var} → {}", { self.ty_unification_table.find(var) }),
            }
        }
        log::debug!("Mutability substitution table:");
        for i in 0..self.mut_unification_table.len() {
            let var = MutVar::new(i as u32);
            let value = self.mut_unification_table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {}", value),
                None => log::debug!("  {var} → {}", { self.mut_unification_table.find(var) }),
            }
        }
    }
}
