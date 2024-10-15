use std::{
    borrow::Borrow,
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::{self, Display},
    iter::once,
    mem,
};

use ena::unify::{EqUnifyValue, InPlaceUnificationTable, UnifyKey, UnifyValue};
use itertools::{multiunzip, Itertools};
use lrpar::Span;
use ustr::{ustr, Ustr};

use crate::{
    ast::{Expr, ExprKind, PropertyAccess},
    containers::{SVec2, B},
    dictionary_passing::DictionaryReq,
    effects::{no_effects, EffType, Effect, EffectVar, EffectVarKey, EffectsSubstitution},
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

pub type InstSubstitution = (TypeSubstitution, EffectsSubstitution);

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

impl UnifyKey for EffectVarKey {
    type Value = Option<EffType>;

    fn index(&self) -> u32 {
        self.name()
    }

    fn from_index(u: u32) -> Self {
        Self::new(u)
    }

    fn tag() -> &'static str {
        "EffectVarKey"
    }
}

/// Effects can always be unified through the union operation
impl UnifyValue for EffType {
    type Error = ena::unify::NoError;

    fn unify_values(a: &Self, b: &Self) -> Result<Self, Self::Error> {
        Ok(a.union(b))
    }
}

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
    effect_constraints: InPlaceUnificationTable<EffectVarKey>,
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

    pub fn fresh_type_var_tys(&mut self, count: usize) -> Vec<Type> {
        (0..count).map(|_| self.fresh_type_var_ty()).collect()
    }

    pub fn fresh_mut_var(&mut self) -> MutVar {
        self.mut_unification_table.new_key(None)
    }

    pub fn fresh_mut_var_ty(&mut self) -> MutType {
        MutType::Variable(self.fresh_mut_var())
    }

    pub fn fresh_effect_var(&mut self) -> EffectVar {
        self.effect_constraints.new_key(None)
    }

    pub fn fresh_effect_var_ty(&mut self) -> EffType {
        EffType::single_variable(self.fresh_effect_var())
    }

    pub fn fresh_fn_args(&mut self, count: usize) -> Vec<FnArgType> {
        (0..count)
            .map(|_| FnArgType::new(self.fresh_type_var_ty(), self.fresh_mut_var_ty()))
            .collect()
    }

    pub fn fresh_type_var_subst(&mut self, source: &[TypeVar]) -> TypeSubstitution {
        source
            .iter()
            .map(|&ty_var| (ty_var, self.fresh_type_var_ty()))
            .collect()
    }

    pub fn fresh_effect_var_subst(&mut self, source: &HashSet<EffectVar>) -> EffectsSubstitution {
        source
            .iter()
            .map(|&eff_var| (eff_var, self.fresh_effect_var_ty()))
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
    ) -> Result<(Node, MutType), InternalCompilationError> {
        use ir::Node as N;
        use ir::NodeKind as K;
        use ExprKind::*;
        let (node, ty, mut_ty, effects) = match &expr.kind {
            Literal(value, ty) => (
                K::Immediate(Immediate::new(value.clone())),
                *ty,
                MutType::constant(),
                no_effects(),
            ),
            FormattedString(s) => {
                let expr = emit_format_string_ast(s, expr.span, env)?;
                return self.infer_expr(env, &expr);
            }
            Identifier(name) => {
                // Retrieve the index and the type of the variable from the environment, if it exists
                if let Some((index, ty, mut_ty)) = env.get_variable_index_and_type_scheme(name) {
                    let node = K::EnvLoad(B::new(ir::EnvLoad { index }));
                    (node, ty, mut_ty, no_effects())
                }
                // Retrieve the function from the environment, if it exists
                else if let Some(function) = env.get_function(name) {
                    let (fn_ty, inst_data) = function.ty_scheme.instantiate(self);
                    let value = Value::Function(FunctionRef::new_weak(&function.code));
                    let node = K::Immediate(B::new(ir::Immediate {
                        value,
                        inst_data,
                        substitute_in_value_fn: false,
                    }));
                    (
                        node,
                        Type::function_type(fn_ty),
                        MutType::constant(),
                        no_effects(),
                    )
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
                        no_effects(),
                        expr.span,
                    );
                    // FIXME: this is not enabled due to a bug in constraints dropping
                    // // Build the variant value.
                    // let node = K::Immediate(Immediate::new(Value::variant(*name, Value::unit())));
                    // (node, variant_ty, MutType::constant(), no_effects())
                    let node = K::Variant(B::new((*name, payload_node)));
                    (node, variant_ty, MutType::constant(), no_effects())
                }
            }
            Let((name, name_span), mutable, let_expr) => {
                let node = self.infer_expr_drop_mut(env, let_expr)?;
                env.locals.push(Local::new(
                    *name,
                    MutType::resolved(*mutable),
                    node.ty,
                    expr.span,
                ));
                let effects = node.effects.clone();
                let node = K::EnvStore(B::new(EnvStore {
                    node,
                    name_span: *name_span,
                }));
                (node, Type::unit(), MutType::constant(), effects)
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
                let code = self.infer_expr_drop_mut(&mut env, body)?;
                // Store and return the function's type
                let fn_ty = FnType::new(args_ty, code.ty, code.effects.clone());
                let value_fn = Value::function(B::new(ScriptFunction::new(code)));
                let node = K::Immediate(Immediate::new(value_fn));
                (
                    node,
                    Type::function_type(fn_ty),
                    MutType::constant(),
                    no_effects(),
                )
            }
            Apply(func, args) => {
                // Do we have a global function or variant?
                if let Identifier(name) = func.kind {
                    if !env.has_variable_name(name) {
                        let (node, ty, mut_ty, effects) =
                            self.infer_static_apply(env, &name, func.span, args)?;
                        return Ok((N::new(node, ty, effects, expr.span), mut_ty));
                    }
                }
                // No, we emit code to evaluate function
                // Infer the type and mutability of the arguments and collect their code and constraints
                // TODO: check borrow rules
                let (args_nodes, args_tys, args_effects) =
                    self.infer_exprs_ret_arg_ty(env, args)?;
                // Allocate a fresh variable for the return type and effects of the function
                let ret_ty = self.fresh_type_var_ty();
                let call_effects = self.fresh_effect_var_ty();
                // Build the function type
                let func_ty =
                    Type::function_type(FnType::new(args_tys, ret_ty, call_effects.clone()));
                // Check the function against its function type
                let func_node =
                    self.check_expr(env, func, func_ty, MutType::constant(), expr.span)?;
                // Unify effects
                let combined_effects =
                    self.make_dependent_effect([&args_effects, &func_node.effects, &call_effects]);
                // Store and return the result
                let node = K::Apply(B::new(ir::Application {
                    function: func_node,
                    arguments: args_nodes,
                }));
                (node, ret_ty, MutType::constant(), combined_effects)
            }
            StaticApply(name, span, args) => self.infer_static_apply(env, name, *span, args)?,
            Block(exprs) => {
                let env_size = env.locals.len();
                let (nodes, types, effects) = self.infer_exprs_drop_mut(env, exprs)?;
                env.locals.truncate(env_size);
                let node = K::Block(B::new(SVec2::from_vec(nodes)));
                let ty = types.last().copied().unwrap_or(Type::unit());
                (node, ty, MutType::constant(), effects)
            }
            Assign(place, sign_span, value) => {
                if let Some((scope, variable)) = place.kind.as_property_path() {
                    let fn_name =
                        property_to_fn_name(scope, variable, PropertyAccess::Set, expr.span, env)?;
                    let (node, ty, mut_ty, effects) =
                        self.infer_static_apply(env, &fn_name, expr.span, &[value.as_ref()])?;
                    return Ok((N::new(node, ty, effects, expr.span), mut_ty));
                }
                let value = self.infer_expr_drop_mut(env, value)?;
                let (place, place_mut) = self.infer_expr(env, place)?;
                self.add_mut_be_at_least_constraint(
                    place_mut,
                    place.span,
                    MutType::mutable(),
                    *sign_span,
                );
                self.add_sub_type_constraint(value.ty, value.span, place.ty, place.span);
                let combined_effects = self.make_dependent_effect([&value.effects, &place.effects]);
                let node = K::Assign(B::new(ir::Assignment { place, value }));
                (node, Type::unit(), MutType::constant(), combined_effects)
            }
            Tuple(exprs) => {
                let (nodes, types, effects) = self.infer_exprs_drop_mut(env, exprs)?;
                let ty = Type::tuple(types);
                let node = if let Some(values) = nodes_as_bare_immediate(&nodes) {
                    K::Immediate(Immediate::new(Value::tuple(values)))
                } else {
                    K::Tuple(B::new(SVec2::from_vec(nodes)))
                };
                (node, ty, MutType::constant(), effects)
            }
            Project(tuple_expr, index, index_span) => {
                let (tuple_node, tuple_mut) = self.infer_expr(env, tuple_expr)?;
                let element_ty = self.fresh_type_var_ty();
                self.ty_constraints.push(TypeConstraint::Pub(
                    PubTypeConstraint::new_tuple_at_index_is(
                        tuple_node.ty,
                        tuple_expr.span,
                        *index,
                        *index_span,
                        element_ty,
                    ),
                ));
                let effects = tuple_node.effects.clone();
                let node = K::Project(B::new((tuple_node, *index)));
                (node, element_ty, tuple_mut, effects)
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
                let (nodes, types, effects) = self.infer_exprs_drop_mut(env, &exprs)?;
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
                let ty = Type::record(names.into_iter().zip(types).collect());
                let node = if let Some(values) = nodes_as_bare_immediate(&nodes) {
                    K::Immediate(Immediate::new(Value::tuple(values)))
                } else {
                    K::Record(B::new(SVec2::from_vec(nodes)))
                };
                (node, ty, MutType::constant(), effects)
            }
            FieldAccess(record_expr, field, field_span) => {
                let (record_node, record_mut) = self.infer_expr(env, record_expr)?;
                let element_ty = self.fresh_type_var_ty();
                self.ty_constraints.push(TypeConstraint::Pub(
                    PubTypeConstraint::new_record_field_is(
                        record_node.ty,
                        record_expr.span,
                        *field,
                        *field_span,
                        element_ty,
                    ),
                ));
                let effects = record_node.effects.clone();
                let node = K::FieldAccess(B::new((record_node, *field)));
                (node, element_ty, record_mut, effects)
            }
            Array(exprs) => {
                use crate::std::array::Array;
                if exprs.is_empty() {
                    // The element type is a fresh type variable
                    let element_ty = self.fresh_type_var_ty();
                    // Build an empty array node and return it
                    let node = K::Immediate(Immediate::new(Value::native(Array::new())));
                    (
                        node,
                        array_type(element_ty),
                        MutType::constant(),
                        no_effects(),
                    )
                } else {
                    // The element type is the first element's type
                    let first_node = self.infer_expr_drop_mut(env, &exprs[0])?;
                    // Infer the type of the elements and collect their code and constraints
                    let (other_nodes, types, other_effects) =
                        self.infer_exprs_drop_mut(env, &exprs[1..])?;
                    // All elements must be of the first element's type
                    let element_ty = first_node.ty;
                    for (ty, expr) in types.into_iter().zip(exprs.iter().skip(1)) {
                        self.add_sub_type_constraint(ty, expr.span, element_ty, exprs[0].span);
                    }
                    // Unify effects
                    let combined_effects =
                        self.make_dependent_effect([&first_node.effects, &other_effects]);
                    // Build the array node and return it
                    let element_nodes: SVec2<_> = once(first_node).chain(other_nodes).collect();
                    let ty = array_type(element_ty);
                    // Can we build it as an immediate?
                    let node = if let Some(values) = nodes_as_bare_immediate(&element_nodes) {
                        let value = Value::native(Array::from_vec(values));
                        K::Immediate(Immediate::new(value))
                    } else {
                        K::Array(B::new(element_nodes))
                    };
                    (node, ty, MutType::constant(), combined_effects)
                }
            }
            Index(array, index) => {
                // New type for the array
                let element_ty = self.fresh_type_var_ty();
                let array_ty = array_type(element_ty);
                // Infer type of the array expression and make sure it is an array
                let (array_node, array_expr_mut) = self.infer_expr(env, array)?;
                self.add_sub_type_constraint(array_node.ty, array.span, array_ty, array.span);
                // Check type of the index expression to be int
                let index_node =
                    self.check_expr(env, index, int_type(), MutType::constant(), index.span)?;
                // Build the index node and return it
                let combined_effects =
                    self.make_dependent_effect([&array_node.effects, &index_node.effects]);
                let node = K::Index(B::new(array_node), B::new(index_node));
                (node, element_ty, array_expr_mut, combined_effects)
            }
            Match(cond_expr, alternatives, default) => {
                let (node, ty, mut_ty, effects) =
                    self.infer_match(env, expr, cond_expr, alternatives, default)?;
                (node, ty, mut_ty, effects)
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
                let combined_effects =
                    self.make_dependent_effect([&iterator.effects, &body.effects]);
                let node = K::Iterate(B::new(ir::Iteration {
                    iterator,
                    body,
                    var_name_span,
                }));
                (node, Type::unit(), MutType::constant(), combined_effects)
            }
            PropertyPath(scope, variable) => {
                let fn_name =
                    property_to_fn_name(scope, variable, PropertyAccess::Get, expr.span, env)?;
                self.infer_static_apply(env, &fn_name, expr.span, &[] as &[Expr])?
            }
            Error(msg) => {
                panic!("attempted to infer type for error node: {msg}");
            }
        };
        Ok((N::new(node, ty, effects.clone(), expr.span), mut_ty))
    }

    fn infer_expr_drop_mut(
        &mut self,
        env: &mut TypingEnv,
        expr: &Expr,
    ) -> Result<Node, InternalCompilationError> {
        Ok(self.infer_expr(env, expr)?.0)
    }

    fn infer_static_apply(
        &mut self,
        env: &mut TypingEnv,
        name: &str,
        span: Span,
        args: &[impl Borrow<Expr>],
    ) -> Result<(NodeKind, Type, MutType, EffType), InternalCompilationError> {
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
            let (args_nodes, args_effects) = self.check_exprs(env, args, &inst_fn_ty.args, span)?;
            // Build and return the function node, get back the function to avoid re-borrowing
            let function = env
                .get_function(name)
                .expect("function not found any more after checking");
            let ret_ty = inst_fn_ty.ret;
            let combined_effects = self.make_dependent_effect([&args_effects, &inst_fn_ty.effects]);
            let node = K::StaticApply(B::new(ir::StaticApplication {
                function: FunctionRef::new_weak(&function.code),
                function_name: ustr(name),
                function_span: span,
                arguments: args_nodes,
                ty: inst_fn_ty,
                inst_data,
            }));
            (node, ret_ty, MutType::constant(), combined_effects)
        } else {
            // If it is not a known function, assume it to be a variant constructor
            // Create a fresh type and add a constraint for that type to include this variant.
            let variant_ty = self.fresh_type_var_ty();
            let (payload_nodes, payload_types, effects) = self.infer_exprs_drop_mut(env, args)?;
            let (payload_ty, payload_node) = match payload_nodes.len() {
                0 => (
                    Type::unit(),
                    N::new(
                        K::Immediate(Immediate::new(Value::unit())),
                        Type::unit(),
                        no_effects(),
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
                    let node = if let Some(values) = nodes_as_bare_immediate(&payload_nodes) {
                        K::Immediate(Immediate::new(Value::tuple(values)))
                    } else {
                        K::Tuple(B::new(SVec2::from_vec(payload_nodes)))
                    };
                    let payload_node = N::new(node, payload_ty, effects.clone(), span);
                    (payload_ty, payload_node)
                }
            };
            let name = ustr(name);
            self.ty_constraints.push(TypeConstraint::Pub(
                PubTypeConstraint::new_type_has_variant(variant_ty, name, payload_ty, span),
            ));
            // Build the variant construction node.
            let node = if let Some(values) = nodes_as_bare_immediate(&[&payload_node]) {
                let value = values.first().unwrap().clone();
                K::Immediate(Immediate::new(Value::variant(name, value)))
            } else {
                K::Variant(B::new((name, payload_node)))
            };
            (node, variant_ty, MutType::constant(), effects)
        })
    }

    fn infer_exprs_drop_mut(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[impl Borrow<Expr>],
    ) -> Result<(Vec<ir::Node>, Vec<Type>, EffType), InternalCompilationError> {
        let (nodes, tys, effects): (_, _, Vec<_>) = exprs
            .iter()
            .map(|arg| {
                let node = self.infer_expr_drop_mut(env, arg.borrow())?;
                let ty = node.ty;
                let effects = node.effects.clone();
                Ok::<(ir::Node, Type, EffType), InternalCompilationError>((node, ty, effects))
            })
            .process_results(|iter| multiunzip(iter))?;

        let combined_effects = self.make_dependent_effect(&effects);
        Ok((nodes, tys, combined_effects))
    }

    fn infer_exprs_ret_arg_ty(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[impl Borrow<Expr>],
    ) -> Result<(Vec<ir::Node>, Vec<FnArgType>, EffType), InternalCompilationError> {
        let (nodes, tys, effects): (_, _, Vec<_>) = exprs
            .iter()
            .map(|arg| {
                let (node, mut_ty) = self.infer_expr(env, arg.borrow())?;
                let ty = node.ty;
                let effects = node.effects.clone();
                Ok::<(ir::Node, FnArgType, EffType), InternalCompilationError>((
                    node,
                    FnArgType::new(ty, mut_ty),
                    effects,
                ))
            })
            .process_results(|iter| multiunzip(iter))?;
        let combined_effects = self.make_dependent_effect(&effects);
        Ok((nodes, tys, combined_effects))
    }

    fn check_exprs(
        &mut self,
        env: &mut TypingEnv,
        exprs: &[impl Borrow<Expr>],
        expected_tys: &[FnArgType],
        expected_span: Span,
    ) -> Result<(Vec<ir::Node>, EffType), InternalCompilationError> {
        let (nodes, effects): (_, Vec<_>) = exprs
            .iter()
            .zip(expected_tys)
            .map(|(arg, arg_ty)| {
                let node =
                    self.check_expr(env, arg.borrow(), arg_ty.ty, arg_ty.inout, expected_span)?;
                let effects = node.effects.clone();
                Ok((node, effects))
            })
            .process_results(|iter| multiunzip(iter))?;
        let combined_effects = self.make_dependent_effect(&effects);
        Ok((nodes, combined_effects))
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
                return Ok(N::new(node, expected_ty, no_effects(), expr.span));
            }
        }

        // Functions abstraction
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
                self.unify_effects(&code.effects, &fn_ty.effects);
                // Store and return the function's type
                let value_fn = Value::function(B::new(ScriptFunction::new(code)));
                let node = K::Immediate(Immediate::new(value_fn));
                return Ok(N::new(node, expected_ty, no_effects(), expr.span));
            }
        }

        // Other cases, infer and add constraints
        let (node, actual_mut) = self.infer_expr(env, expr)?;
        self.add_sub_type_constraint(node.ty, expr.span, expected_ty, expected_span);
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

    #[allow(dead_code)]
    fn log_debug_effect_constraints(&mut self) {
        log::debug!("Effect substitution table:");
        for i in 0..self.effect_constraints.len() {
            let var = EffectVar::new(i as u32);
            let value = self.effect_constraints.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {}", value),
                None => log::debug!("  {var} → {} (unbound)", {
                    self.effect_constraints.find(var)
                }),
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

    /// Make a new effect depending on the given effects
    pub fn make_dependent_effect<T: Borrow<EffType> + Clone>(
        &mut self,
        deps: impl AsRef<[T]>,
    ) -> EffType {
        let deps = deps.as_ref();

        // Handle the trivial cases.
        if deps.is_empty() {
            return EffType::empty();
        } else if deps.len() == 1 {
            return deps[0].borrow().clone();
        }

        // Partition the effects into primitive and unresolved ones.
        let (primitives, variables) = deps
            .iter()
            .flat_map(|eff| eff.borrow().iter())
            .partition::<HashSet<_>, _>(|eff| eff.is_primitive());

        // If all effects are primitive, we can just return them.
        if variables.is_empty() {
            return EffType::from_iter(primitives);
        } else if variables.len() == 1 && primitives.is_empty() {
            // If there is only one variable and no primitive, we can just return it.
            return EffType::single(*variables.iter().next().unwrap());
        }

        // Otherwise, we need to create a new effect variable.
        let effects = EffType::from_iter(variables.into_iter().chain(primitives).unique());
        let effect_var = self.effect_constraints.new_key(Some(effects));
        EffType::single_variable(effect_var)
    }

    /// Make the two effects equal and fuse their dependencies
    pub fn unify_effects(&mut self, eff1: &EffType, eff2: &EffType) -> EffType {
        let var1 = eff1.to_single_variable();
        let var2 = eff2.to_single_variable();
        match (var1, var2) {
            (None, None) => eff1.union(eff2),
            (None, Some(var)) => {
                self.effect_constraints.union_value(var, Some(eff1.clone()));
                eff1.clone()
            }
            (Some(var), None) => {
                self.effect_constraints.union_value(var, Some(eff2.clone()));
                eff2.clone()
            }
            (Some(var1), Some(var2)) => {
                self.effect_constraints.union(var1, var2);
                eff1.clone()
            }
        }
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
    effect_constraints: InPlaceUnificationTable<EffectVarKey>,
    effect_constraints_inv: HashMap<EffType, EffectVarKey>,
}

impl UnifiedTypeInference {
    pub fn unify_type_inference(ty_inf: TypeInference) -> Result<Self, InternalCompilationError> {
        let TypeInference {
            ty_unification_table,
            ty_constraints,
            mut_unification_table,
            mut_constraints,
            effect_constraints,
        } = ty_inf;
        let mut unified_ty_inf = UnifiedTypeInference {
            ty_unification_table,
            remaining_ty_constraints: vec![],
            mut_unification_table,
            effect_constraints,
            effect_constraints_inv: HashMap::new(),
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

        // Flatten inverted effect constraints into normal constraints
        let effect_constraints_inv = mem::take(&mut unified_ty_inf.effect_constraints_inv);
        for (eff, var) in effect_constraints_inv {
            unified_ty_inf.expand_inv_effect_dep(eff, var);
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
        let effects = fn_ty.effects.clone();
        FnType::new(args, ret, effects)
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
            (Never, _) => Ok(()),
            (_, Never) => Ok(()),
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
                // Covariant effects.
                self.add_effect_dep(&cur.effects, current_span, &exp.effects, expected_span)?;
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

    pub fn add_effect_dep(
        &mut self,
        current: &EffType,
        current_span: Span,
        target: &EffType,
        target_span: Span,
    ) -> Result<(), InternalCompilationError> {
        if current.is_empty() || current == target {
            return Ok(());
        }
        let cur_single = current.as_single();
        let cur_var = cur_single.and_then(|eff| eff.as_variable().cloned());
        let tgt_single = target.as_single();
        let tgt_var = tgt_single.and_then(|eff| eff.as_variable().cloned());
        if let Some(var) = cur_var {
            // Left is a variable, put the effect dependency on the right.
            self.effect_constraints
                .union_value(var, Some(target.clone()));
        } else if let Some(var) = tgt_var {
            // Right is a variable, put the effect dependency to the inverted constraints,
            // to be resolved later.
            self.effect_constraints_inv.insert(current.clone(), var);
        } else {
            return Err(InternalCompilationError::InvalidEffectDependency {
                source: current.clone(),
                source_span: current_span,
                target: target.clone(),
                target_span,
            });
        }
        Ok(())
    }

    pub fn expand_inv_effect_dep(&mut self, current: EffType, target: EffectVarKey) {
        if let Some(existing_effects) = self.effect_constraints.probe_value(target) {
            for eff in existing_effects.iter() {
                if let Some(var) = eff.as_variable() {
                    self.expand_inv_effect_dep(current.clone(), *var);
                }
            }
        } else {
            self.effect_constraints.union_value(
                target,
                Some(current.union(&EffType::single_variable(target))),
            );
        }
    }

    pub(crate) fn substitute_in_module_function(&mut self, descr: &mut ModuleFunction) {
        descr.ty_scheme.ty = self.substitute_in_fn_type(&descr.ty_scheme.ty);
        assert!(descr.ty_scheme.constraints.is_empty());
        let mut code = descr.code.borrow_mut();
        if let Some(script_fn) = code.as_script_mut() {
            self.substitute_in_node(&mut script_fn.code);
        }
    }

    pub fn substitute_in_type(&mut self, ty: Type) -> Type {
        let type_data: TypeKind = { ty.data().clone() };
        use TypeKind::*;
        match type_data {
            Variable(var) => {
                // if ignore.contains(&var) {
                //     return Type::variable(var);
                // }
                let root = self.ty_unification_table.find(var);
                match self.ty_unification_table.probe_value(root) {
                    Some(ty) => self.substitute_in_type(ty),
                    _ => Type::variable(root),
                }
            }
            Native(ty) => Type::native_type(NativeType::new(
                ty.bare_ty.clone(),
                self.substitute_in_types(&ty.arguments),
            )),
            Variant(tys) => Type::variant(
                tys.into_iter()
                    .map(|(name, ty)| (name, self.substitute_in_type(ty)))
                    .collect(),
            ),
            Tuple(tys) => Type::tuple(self.substitute_in_types(&tys)),
            Record(fields) => Type::record(
                fields
                    .into_iter()
                    .map(|(name, ty)| (name, self.substitute_in_type(ty)))
                    .collect(),
            ),
            Function(fn_ty) => Type::function_type(self.substitute_in_fn_type(&fn_ty)),
            Newtype(name, ty) => Type::new_type(name, self.substitute_in_type(ty)),
            Never => ty,
        }
    }

    fn substitute_in_types(&mut self, tys: &[Type]) -> Vec<Type> {
        tys.iter().map(|ty| self.substitute_in_type(*ty)).collect()
    }

    pub fn substitute_in_fn_type(&mut self, fn_ty: &FnType) -> FnType {
        let args = fn_ty
            .args
            .iter()
            .map(|arg| {
                FnArgType::new(
                    self.substitute_in_type(arg.ty),
                    self.substitute_mut_type(arg.inout),
                )
            })
            .collect::<Vec<_>>();
        let ret = self.substitute_in_type(fn_ty.ret);
        let effects = self.substitute_effect_type(&fn_ty.effects);
        FnType::new(args, ret, effects)
    }

    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType {
        match mut_ty {
            MutType::Resolved(_) => mut_ty,
            MutType::Variable(var) => {
                let root = self.mut_unification_table.find(var);
                match self.mut_unification_table.probe_value(root) {
                    Some(val) => MutType::resolved(val),
                    _ => panic!("Unresolved mutability variable"),
                }
            }
        }
    }

    /// Substitute the effect type by flattening the effect variables.
    pub fn substitute_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        use Effect::*;

        // Thread-local hash-map for cycle detection
        thread_local! {
            static VAR_VISITED: RefCell<HashSet<EffectVar>> = RefCell::new(HashSet::new());
        }

        let res = EffType::from_iter(eff_ty.iter().flat_map(|eff| {
            EffType::into_iter(match eff {
                Primitive(effect) => EffType::single_primitive(*effect),
                Variable(var) => {
                    let cycle_detected = VAR_VISITED.with(|visited| {
                        let mut visited = visited.borrow_mut();
                        if visited.contains(var) {
                            true // Cycle detected
                        } else {
                            visited.insert(*var);
                            false
                        }
                    });

                    if cycle_detected {
                        return EffType::empty().into_iter();
                    }

                    let mut effects = match self.effect_constraints.probe_value(*var) {
                        Some(effects) => self.substitute_effect_type(&effects),
                        None => EffType::single_variable(*var),
                    };

                    // add back the variable itself
                    effects = effects.union(&EffType::single_variable(*var));

                    VAR_VISITED.with(|visited| {
                        visited.borrow_mut().remove(var);
                    });

                    effects
                }
            } as EffType)
        }));
        res
    }

    pub fn substitute_in_node(&mut self, node: &mut ir::Node) {
        use ir::NodeKind::*;
        node.ty = self.substitute_in_type(node.ty);
        node.effects = self.substitute_effect_type(&node.effects);
        match &mut node.kind {
            Immediate(immediate) => {
                self.substitute_in_value(&mut immediate.value);
                self.substitute_in_fn_inst_data(&mut immediate.inst_data);
            }
            BuildClosure(_) => panic!("BuildClosure should not be present at this stage"),
            Apply(app) => {
                self.substitute_in_node(&mut app.function);
                self.substitute_in_nodes(&mut app.arguments);
            }
            StaticApply(app) => {
                app.ty = self.substitute_in_fn_type(&app.ty);
                self.substitute_in_nodes(&mut app.arguments);
                self.substitute_in_fn_inst_data(&mut app.inst_data);
            }
            EnvStore(node) => {
                self.substitute_in_node(&mut node.node);
            }
            EnvLoad(_) => {}
            Block(nodes) => self.substitute_in_nodes(nodes),
            Assign(assignment) => {
                self.substitute_in_node(&mut assignment.place);
                self.substitute_in_node(&mut assignment.value);
            }
            Tuple(nodes) => self.substitute_in_nodes(nodes),
            Project(projection) => self.substitute_in_node(&mut projection.0),
            Record(nodes) => self.substitute_in_nodes(nodes),
            FieldAccess(node_and_field) => self.substitute_in_node(&mut node_and_field.0),
            ProjectAt(projection) => self.substitute_in_node(&mut projection.0),
            Variant(variant) => self.substitute_in_node(&mut variant.1),
            ExtractTag(node) => self.substitute_in_node(node),
            Array(nodes) => self.substitute_in_nodes(nodes),
            Index(array, index) => {
                self.substitute_in_node(array);
                self.substitute_in_node(index);
            }
            Case(case) => {
                self.substitute_in_node(&mut case.value);
                for alternative in case.alternatives.iter_mut() {
                    self.substitute_in_value(&mut alternative.0);
                    self.substitute_in_node(&mut alternative.1);
                }
                self.substitute_in_node(&mut case.default);
            }
            Iterate(iteration) => {
                self.substitute_in_node(&mut iteration.iterator);
                self.substitute_in_node(&mut iteration.body);
            }
        }
    }

    fn substitute_in_nodes(&mut self, nodes: &mut [ir::Node]) {
        for node in nodes {
            self.substitute_in_node(node);
        }
    }

    fn substitute_in_fn_inst_data(&mut self, inst_data: &mut FnInstData) {
        inst_data.dicts_req = inst_data
            .dicts_req
            .iter()
            .map(|dict| DictionaryReq::new(self.substitute_in_type(dict.ty), dict.kind))
            .collect();
    }

    fn substitute_in_value(&mut self, value: &mut Value) {
        match value {
            Value::Tuple(tuple) => {
                for value in tuple.iter_mut() {
                    self.substitute_in_value(value);
                }
            }
            Value::Function(function) => {
                let function = function.get();
                // Note: this can fail if we are having a recursive function used as a value, in that case do not recurse.
                let function = function.try_borrow_mut();
                if let Ok(mut function) = function {
                    if let Some(script_fn) = function.as_script_mut() {
                        self.substitute_in_node(&mut script_fn.code);
                    }
                }
            }
            _ => {}
        }
    }

    #[allow(dead_code)]
    fn substitute_in_constraint(&mut self, constraint: &PubTypeConstraint) -> PubTypeConstraint {
        use PubTypeConstraint::*;
        match constraint {
            TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => {
                let tuple_ty = self.substitute_in_type(*tuple_ty);
                let element_ty = self.substitute_in_type(*element_ty);
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
                let record_ty = self.substitute_in_type(*record_ty);
                let element_ty = self.substitute_in_type(*element_ty);
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
                let ty = self.substitute_in_type(*ty);
                let variant_ty = self.substitute_in_type(*variant_ty);
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

    pub fn log_debug_substitution_tables(&mut self, module_env: ModuleEnv) {
        log::debug!("Type substitution table:");
        for i in 0..self.ty_unification_table.len() {
            let var = TypeVar::new(i as u32);
            let value = self.ty_unification_table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {}", value.format_with(&module_env)),
                None => log::debug!("  {var} → {} (unbound)", {
                    self.ty_unification_table.find(var)
                }),
            }
        }
        log::debug!("Mutability substitution table:");
        for i in 0..self.mut_unification_table.len() {
            let var = MutVar::new(i as u32);
            let value = self.mut_unification_table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {}", value),
                None => log::debug!("  {var} → {} (unbound)", {
                    self.mut_unification_table.find(var)
                }),
            }
        }
        self.log_debug_effect_constraints();
    }

    fn log_debug_effect_constraints(&mut self) {
        log::debug!("Effect substitution table:");
        for i in 0..self.effect_constraints.len() {
            let var = EffectVar::new(i as u32);
            let value = self.effect_constraints.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {}", value),
                None => log::debug!("  {var} → {} (unbound)", {
                    self.effect_constraints.find(var)
                }),
            }
        }
        if !self.effect_constraints_inv.is_empty() {
            log::debug!("Inverted effect constraints:");
            for (eff, var) in &self.effect_constraints_inv {
                log::debug!("  {} → {var}", eff);
            }
        }
    }
}

fn property_to_fn_name(
    scope: &str,
    variable: &str,
    access: PropertyAccess,
    span: Span,
    env: &TypingEnv,
) -> Result<String, InternalCompilationError> {
    let mut scope_parts = scope.rsplitn(2, "::");
    let scope = scope_parts.next().unwrap(); // safe to unwrap, as we have at least one part
    let path = scope_parts
        .next()
        .map_or("".into(), |path| format!("{path}::"));
    let fn_name = format!("{}@{} {}.{}", path, access.as_prefix(), scope, variable);
    if env.get_function(&fn_name).is_none() {
        Err(InternalCompilationError::UnknownProperty {
            scope: ustr(scope),
            variable: ustr(variable),
            cause: access,
            span,
        })
    } else {
        Ok(fn_name)
    }
}

/// Return a list of cloned values if all nodes are immediate values and have no effects.
fn nodes_as_bare_immediate(nodes: &[impl Borrow<Node>]) -> Option<Vec<Value>> {
    let nodes = nodes
        .iter()
        .map(|node| {
            let node = node.borrow();
            match &node.kind {
                NodeKind::Immediate(immediate) => {
                    // For now, do not support function values for transformation into composed immediates.
                    // The reason is that different functions might hav different instantiation requirements.
                    if node.effects.any()
                        || immediate.inst_data.any()
                        || node.ty.data().is_function()
                    {
                        None
                    } else {
                        Some(&immediate.value)
                    }
                }
                _ => None,
            }
        })
        .collect::<Option<Vec<&Value>>>()?;
    Some(nodes.into_iter().cloned().collect())
}
