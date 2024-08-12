use std::{
    collections::{HashSet, VecDeque},
    fmt::Display,
};

use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use lrpar::Span;

use crate::{
    containers::{SVec1, SVec2, B},
    error::RuntimeError,
    format::{write_with_separator, FormatWith},
    function::FunctionRef,
    module::{FmtWithModuleEnv, ModuleEnv},
    r#type::{FnArgType, FnType, Type, TypeLike, TypeVar, TypeVarSubstitution},
    std::{array, range},
    type_scheme::{DisplayStyle, TypeScheme},
    value::{NativeValue, Value},
};

/// Along with the Rust native stack, corresponds to the Zinc Abstract Machine of Caml language family
/// with the addition of Mutable Value Semantics through references to earlier stack frames
pub struct EvalCtx {
    /// all values or mutable references of all stack frames
    pub environment: Vec<ValOrMut>,
    /// base of current stack frame in `environment`
    pub frame_base: usize,
}

impl EvalCtx {
    #[allow(clippy::new_without_default)]
    pub fn new() -> EvalCtx {
        EvalCtx {
            environment: Vec::new(),
            frame_base: 0,
        }
    }
}

type FormatWithEvalCtx<'a, T> = FormatWith<'a, T, EvalCtx>;

/// A place in the environment (absolute position), with a path to a compound value
/// This behaves like a global address to a Value given our Mutable Value Semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Place {
    // index of target variable, absolute in the environment, to allow to access parent frames
    pub target: usize,
    // path within the compound value located at `target`
    pub path: Vec<isize>,
}

impl Place {
    /// Return a path and an index of a variable in the environment that is for sure a Value
    fn resolved_path_and_index(&self, ctx: &EvalCtx) -> (VecDeque<isize>, usize) {
        let mut path = self.path.iter().copied().collect::<VecDeque<_>>();
        let mut index = self.target;
        loop {
            match &ctx.environment[index] {
                ValOrMut::Val(_target) => {
                    break;
                }
                ValOrMut::Mut(place) => {
                    index = place.target;
                    for &index in place.path.iter().rev() {
                        path.push_front(index);
                    }
                }
            };
        }
        (path, index)
    }

    /// Get a mutable reference to the target value
    pub fn target_mut<'c>(&self, ctx: &'c mut EvalCtx) -> Result<&'c mut Value, RuntimeError> {
        let (path, index) = self.resolved_path_and_index(ctx);
        let mut target = ctx.environment[index].as_val_mut().unwrap();
        for &index in path.iter() {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get_mut(index as usize).unwrap(),
                Native(primitive) => {
                    // iif the primitive is our standard Array, we can access its elements
                    let array = primitive
                        .as_mut_any()
                        .downcast_mut::<array::Array>()
                        .unwrap();
                    let len = array.len();
                    match array.get_mut_signed(index) {
                        Some(target) => target,
                        None => return Err(RuntimeError::ArrayAccessOutOfBounds { index, len }),
                    }
                }
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }

    /// Get a shared reference to the target value
    pub fn target_ref<'c>(&self, ctx: &'c EvalCtx) -> Result<&'c Value, RuntimeError> {
        let (path, index) = self.resolved_path_and_index(ctx);
        let mut target = ctx.environment[index].as_val().unwrap();
        for &index in path.iter() {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get(index as usize).unwrap(),
                Native(primitive) => {
                    // iif the primitive is our standard Array, we can access its elements
                    let array = NativeValue::as_any(&**primitive)
                        .downcast_ref::<array::Array>()
                        .unwrap();
                    let len = array.len();
                    match array.get_signed(index) {
                        Some(target) => target,
                        None => return Err(RuntimeError::ArrayAccessOutOfBounds { index, len }),
                    }
                }
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }
}

impl Display for FormatWithEvalCtx<'_, Place> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Place { target, path } = self.value;
        let ctx = self.data;
        let relative_index = *target as isize - ctx.frame_base as isize;
        write!(f, "@{relative_index}")?;
        if !path.is_empty() {
            write!(f, ".")?;
        }
        write_with_separator(path, ".", f)?;
        if relative_index < 0 {
            write!(f, " (in a previous frame)")?;
        }
        Ok(())
    }
}

/// Either a value or a unique mutable reference to a value.
/// This allows to implement the mutable value semantics.
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum ValOrMut {
    /// A value, itself
    Val(Value),
    /// A mutable reference, index in the environment plus path within the value
    Mut(Place),
}

impl ValOrMut {
    pub fn into_primitive<T: 'static>(self) -> Option<T> {
        match self {
            ValOrMut::Val(val) => val.into_primitive_ty::<T>(),
            ValOrMut::Mut(_) => None,
        }
    }

    pub fn as_mut_primitive<T: 'static>(
        self,
        ctx: &mut EvalCtx,
    ) -> Result<Option<&mut T>, RuntimeError> {
        Ok(match self {
            ValOrMut::Val(_) => None,
            ValOrMut::Mut(place) => place.target_mut(ctx)?.as_primitive_ty_mut::<T>(),
        })
    }

    pub fn as_value(&self, ctx: &EvalCtx) -> Result<Value, RuntimeError> {
        Ok(match self {
            ValOrMut::Val(value) => value.clone(),
            ValOrMut::Mut(place) => place.target_ref(ctx)?.clone(),
        })
    }

    pub fn as_place(&self) -> &Place {
        match self {
            ValOrMut::Val(_) => panic!("Cannot get a place from a value"),
            ValOrMut::Mut(place) => place,
        }
    }
}

impl Display for FormatWithEvalCtx<'_, ValOrMut> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            ValOrMut::Val(value) => write!(f, "value {value}"),
            ValOrMut::Mut(place) => write!(f, "mut. ref. {}", FormatWith::new(place, self.data)),
        }
    }
}

/// The result of evaluating an IR node, either a Value or a runtime error.
pub type EvalResult = Result<Value, RuntimeError>;

#[derive(Debug, Clone)]
pub struct Application {
    pub function: Node,
    pub arguments: Vec<Node>,
}

#[derive(Debug, Clone)]
pub struct StaticApplication {
    pub function: FunctionRef,
    pub arguments: Vec<Node>,
    pub ty: FnType,
    // substitution for the type variable of the function in the context of the application
    // pub subst: TypeSubstitution,
}

#[derive(Debug, Clone)]
pub struct EnvStore {
    pub node: Node,
    pub ty_scheme: TypeScheme<Type>,
    pub name_span: Span,
}
impl EnvStore {
    pub fn substitute(&mut self, subst: &TypeVarSubstitution) {
        self.node.substitute(subst);
        self.ty_scheme.substitute(subst);
    }
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub place: Node,
    pub value: Node,
}

#[derive(Debug, Clone)]
pub struct Case {
    pub value: Node,
    pub alternatives: SVec1<(Value, Node)>,
    pub default: Node,
}

#[derive(Debug, Clone)]
pub struct Iteration {
    pub iterator: Node,
    pub body: Node,
}

/// The kind-specific part of the expression-based execution tree
#[derive(Debug, Clone)]
pub enum NodeKind {
    Literal(Value),
    Apply(B<Application>),
    StaticApply(B<StaticApplication>),
    EnvStore(B<EnvStore>),
    EnvLoad(usize),
    Block(B<SVec2<Node>>),
    Assign(B<Assignment>),
    Tuple(B<SVec2<Node>>),
    Project(B<(Node, usize)>),
    Array(B<SVec2<Node>>),
    Index(B<Node>, B<Node>),
    Case(B<Case>),
    Iterate(B<Iteration>),
}

/// A node of the expression-based execution tree
#[derive(Debug, Clone)]
pub struct Node {
    pub kind: NodeKind,
    pub ty: Type,
    pub span: Span,
}

impl Node {
    pub fn new(kind: NodeKind, ty: Type, span: Span) -> Self {
        Self { kind, ty, span }
    }

    pub fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "⎸ ".repeat(indent);
        use NodeKind::*;
        match &self.kind {
            Literal(value) => value.format_ind(f, env, indent)?,
            Apply(app) => {
                writeln!(f, "{indent_str}eval")?;
                app.function.format_ind(f, env, indent + 1)?;
                if app.arguments.is_empty() {
                    writeln!(f, "{indent_str}and apply to ()")?;
                } else {
                    writeln!(f, "{indent_str}and apply to (")?;
                    for arg in &app.arguments {
                        arg.format_ind(f, env, indent + 1)?;
                    }
                    writeln!(f, ")")?;
                }
            }
            StaticApply(app) => {
                writeln!(f, "{indent_str}apply")?;
                let function = app.function.get();
                let name = env.function_name(&function);
                match app.function.get().try_borrow() {
                    Ok(function) => {
                        let ty = app.ty.format_with(env);
                        match name {
                            Some(name) => writeln!(f, "{indent_str}⎸ {name}: {ty}")?,
                            None => {
                                writeln!(f, "{indent_str}⎸ unknown fn at {:p}: {ty}", *function)?
                            }
                        }
                    }
                    Err(_) => writeln!(f, "{indent_str}⎸ self")?,
                }
                if app.arguments.is_empty() {
                    writeln!(f, "{indent_str}to ()")?;
                } else {
                    writeln!(f, "{indent_str}to (")?;
                    for arg in &app.arguments {
                        arg.format_ind(f, env, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")?;
                }
            }
            EnvStore(node) => {
                writeln!(f, "{indent_str}push")?;
                node.node.format_ind(f, env, indent + 1)?;
            }
            EnvLoad(index) => writeln!(f, "{indent_str}load {index}")?,
            Block(nodes) => {
                for node in nodes.iter() {
                    node.format_ind(f, env, indent)?;
                }
            }
            Assign(assignment) => {
                writeln!(f, "{indent_str}assign")?;
                assignment.place.format_ind(f, env, indent + 1)?;
                assignment.value.format_ind(f, env, indent + 1)?;
            }
            Tuple(nodes) => {
                writeln!(f, "{indent_str}tuple")?;
                for node in nodes.iter() {
                    node.format_ind(f, env, indent + 1)?;
                }
            }
            Project(projection) => {
                writeln!(f, "{indent_str}project")?;
                projection.0.format_ind(f, env, indent + 1)?;
                writeln!(f, "{indent_str}at {index}", index = projection.1)?;
            }
            Array(nodes) => {
                writeln!(f, "{indent_str}array")?;
                for node in nodes.iter() {
                    node.format_ind(f, env, indent + 1)?;
                }
            }
            Index(array, index) => {
                writeln!(f, "{indent_str}index")?;
                array.format_ind(f, env, indent + 1)?;
                index.format_ind(f, env, indent + 1)?;
            }
            Case(case) => {
                writeln!(f, "{indent_str}match")?;
                case.value.format_ind(f, env, indent + 1)?;
                for (alternative, node) in &case.alternatives {
                    writeln!(f, "{indent_str}case {alternative}",)?;
                    node.format_ind(f, env, indent + 1)?;
                }
                writeln!(f, "{indent_str}default")?;
                case.default.format_ind(f, env, indent + 1)?;
            }
            Iterate(iteration) => {
                writeln!(f, "{indent_str}iterate from")?;
                iteration.iterator.format_ind(f, env, indent + 1)?;
                writeln!(f, "{indent_str}in")?;
                iteration.body.format_ind(f, env, indent + 1)?;
            }
        };
        writeln!(f, "{indent_str}↳ {}", self.ty.format_with(env))
    }

    pub fn type_at(&self, pos: usize) -> Option<Type> {
        // Early exit if the position is outside the node's span.
        if pos < self.span.start() || pos >= self.span.end() {
            return None;
        }

        // Look into children.
        use NodeKind::*;
        match &self.kind {
            Literal(_) => {}
            Apply(app) => {
                if let Some(ty) = app.function.type_at(pos) {
                    return Some(ty);
                }
                for arg in &app.arguments {
                    if let Some(ty) = arg.type_at(pos) {
                        return Some(ty);
                    }
                }
            }
            StaticApply(app) => {
                for arg in &app.arguments {
                    if let Some(ty) = arg.type_at(pos) {
                        return Some(ty);
                    }
                }
            }
            EnvStore(node) => {
                if let Some(ty) = node.node.type_at(pos) {
                    return Some(ty);
                }
            }
            EnvLoad(_) => {}
            Block(nodes) => {
                for node in nodes.iter() {
                    if let Some(ty) = node.type_at(pos) {
                        return Some(ty);
                    }
                }
            }
            Assign(assignment) => {
                if let Some(ty) = assignment.place.type_at(pos) {
                    return Some(ty);
                }
                if let Some(ty) = assignment.value.type_at(pos) {
                    return Some(ty);
                }
            }
            Tuple(nodes) => {
                for node in nodes.iter() {
                    if let Some(ty) = node.type_at(pos) {
                        return Some(ty);
                    }
                }
            }
            Project(projection) => {
                if let Some(ty) = projection.0.type_at(pos) {
                    return Some(ty);
                }
            }
            Array(nodes) => {
                for node in nodes.iter() {
                    if let Some(ty) = node.type_at(pos) {
                        return Some(ty);
                    }
                }
            }
            Index(array, index) => {
                if let Some(ty) = array.type_at(pos) {
                    return Some(ty);
                }
                if let Some(ty) = index.type_at(pos) {
                    return Some(ty);
                }
            }
            Case(case) => {
                if let Some(ty) = case.value.type_at(pos) {
                    return Some(ty);
                }
                for (_, node) in &case.alternatives {
                    if let Some(ty) = node.type_at(pos) {
                        return Some(ty);
                    }
                }
                if let Some(ty) = case.default.type_at(pos) {
                    return Some(ty);
                }
            }
            Iterate(iteration) => {
                if let Some(ty) = iteration.iterator.type_at(pos) {
                    return Some(ty);
                }
                if let Some(ty) = iteration.body.type_at(pos) {
                    return Some(ty);
                }
            }
        }

        // No children has this position, return our type.
        Some(self.ty)
    }

    pub fn variable_type_annotations(
        &self,
        style: DisplayStyle,
        result: &mut Vec<(usize, String)>,
        env: &ModuleEnv,
    ) {
        use NodeKind::*;
        match &self.kind {
            Literal(_) => {}
            Apply(app) => {
                app.function.variable_type_annotations(style, result, env);
                for arg in &app.arguments {
                    arg.variable_type_annotations(style, result, env);
                }
            }
            StaticApply(app) => {
                for arg in &app.arguments {
                    arg.variable_type_annotations(style, result, env);
                }
            }
            EnvStore(node) => {
                result.push((
                    node.name_span.end(),
                    match style {
                        DisplayStyle::Mathematical => {
                            format!(": {}", node.ty_scheme.display_math_style(env))
                        }
                        DisplayStyle::Rust => {
                            format!(": {}", node.ty_scheme.display_rust_style(env))
                        }
                    },
                ));
                node.node.variable_type_annotations(style, result, env);
            }
            EnvLoad(_) => {}
            Block(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(style, result, env)),
            Assign(assignment) => {
                assignment
                    .place
                    .variable_type_annotations(style, result, env);
                assignment
                    .value
                    .variable_type_annotations(style, result, env);
            }
            Tuple(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(style, result, env)),
            Project(projection) => projection.0.variable_type_annotations(style, result, env),
            Array(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(style, result, env)),
            Index(array, index) => {
                array.variable_type_annotations(style, result, env);
                index.variable_type_annotations(style, result, env);
            }
            Case(case) => {
                case.value.variable_type_annotations(style, result, env);
                for (_, node) in &case.alternatives {
                    node.variable_type_annotations(style, result, env);
                }
                case.default.variable_type_annotations(style, result, env);
            }
            Iterate(iteration) => {
                iteration
                    .iterator
                    .variable_type_annotations(style, result, env);
                iteration.body.variable_type_annotations(style, result, env);
            }
        }
    }

    pub fn unbound_ty_vars(
        &self,
        result: &mut HashSet<(TypeVar, Span)>,
        ignore: &[TypeVar],
        generation: u32,
    ) {
        use NodeKind::*;
        // Add type variables for this node.
        self.unbound_ty_vars_in_ty(&self.ty, result, ignore, generation);
        // Recurse.
        match &self.kind {
            Literal(_) => {} // no need to look into the value's type as it is already in this node's type
            Apply(app) => {
                app.function.unbound_ty_vars(result, ignore, generation);
                for arg in &app.arguments {
                    arg.unbound_ty_vars(result, ignore, generation);
                }
            }
            StaticApply(app) => {
                self.unbound_ty_vars_in_ty(&app.ty, result, ignore, generation);
                for arg in &app.arguments {
                    arg.unbound_ty_vars(result, ignore, generation);
                }
            }
            EnvStore(node) => {
                let new_ignore = node
                    .ty_scheme
                    .quantifiers
                    .iter()
                    .chain(ignore)
                    .copied()
                    .unique()
                    .collect::<Vec<_>>();
                node.node.unbound_ty_vars(result, &new_ignore, generation)
            }
            EnvLoad(_) => {}
            Block(nodes) => nodes
                .iter()
                .for_each(|node| node.unbound_ty_vars(result, ignore, generation)),
            Assign(assignment) => {
                assignment.place.unbound_ty_vars(result, ignore, generation);
                assignment.value.unbound_ty_vars(result, ignore, generation);
            }
            Tuple(nodes) => nodes
                .iter()
                .for_each(|node| node.unbound_ty_vars(result, ignore, generation)),
            Project(projection) => projection.0.unbound_ty_vars(result, ignore, generation),
            Array(nodes) => nodes
                .iter()
                .for_each(|node| node.unbound_ty_vars(result, ignore, generation)),
            Index(array, index) => {
                array.unbound_ty_vars(result, ignore, generation);
                index.unbound_ty_vars(result, ignore, generation);
            }
            Case(case) => {
                case.value.unbound_ty_vars(result, ignore, generation);
                case.alternatives.iter().for_each(|(_alternative, node)| {
                    node.unbound_ty_vars(result, ignore, generation);
                });
                case.default.unbound_ty_vars(result, ignore, generation);
            }
            Iterate(iteration) => {
                iteration
                    .iterator
                    .unbound_ty_vars(result, ignore, generation);
                iteration.body.unbound_ty_vars(result, ignore, generation);
            }
        }
    }

    pub fn unbound_ty_vars_in_ty(
        &self,
        ty: &impl TypeLike,
        result: &mut HashSet<(TypeVar, Span)>,
        ignore: &[TypeVar],
        generation: u32,
    ) {
        ty.inner_ty_vars().iter().for_each(|ty_var| {
            if ty_var.generation() == generation && !ignore.contains(ty_var) {
                result.insert((*ty_var, self.span));
            }
        });
    }

    pub fn substitute(&mut self, subst: &TypeVarSubstitution) {
        use NodeKind::*;
        match &mut self.kind {
            Literal(value) => value.substitute(subst),
            Apply(app) => {
                app.function.substitute(subst);
                substitute_nodes(&mut app.arguments, subst);
            }
            StaticApply(app) => {
                app.ty = app.ty.substitute(subst);
                substitute_nodes(&mut app.arguments, subst);
            }
            EnvStore(node) => node.substitute(subst),
            EnvLoad(_) => {}
            Block(nodes) => substitute_nodes(nodes, subst),
            Assign(assignment) => {
                assignment.place.substitute(subst);
                assignment.value.substitute(subst);
            }
            Tuple(nodes) => substitute_nodes(nodes, subst),
            Project(node_and_index) => node_and_index.0.substitute(subst),
            Array(nodes) => substitute_nodes(nodes, subst),
            Index(array, index) => {
                array.substitute(subst);
                index.substitute(subst);
            }
            Case(case) => {
                case.value.substitute(subst);
                for alternative in case.alternatives.iter_mut() {
                    alternative.0.substitute(subst);
                    alternative.1.substitute(subst);
                }
                case.default.substitute(subst);
            }
            Iterate(iteration) => {
                iteration.iterator.substitute(subst);
                iteration.body.substitute(subst);
            }
        }
        self.ty = self.ty.substitute(subst);
    }

    /// Evaluate this node given the environment and return the result.
    pub fn eval(&self, ctx: &mut EvalCtx) -> EvalResult {
        use NodeKind::*;
        match &self.kind {
            Literal(value) => Ok(value.clone()),
            Apply(app) => {
                let args_ty = {
                    app.function
                        .ty
                        .data()
                        .as_function()
                        .expect("Apply needs a function type")
                        .args
                        .clone()
                };
                let function_value = app.function.eval(ctx)?;
                let function = function_value.as_function().unwrap().get();
                let function = function.borrow();
                let arguments = eval_args(&app.arguments, &args_ty, ctx)?;
                function.call(arguments, ctx)
            }
            StaticApply(app) => {
                let args_ty = &app.ty.args;
                let function = app.function.get();
                let function = function.borrow();
                let arguments = eval_args(&app.arguments, args_ty, ctx)?;
                function.call(arguments, ctx)
            }
            EnvStore(node) => {
                let value = node.node.eval(ctx)?;
                ctx.environment.push(ValOrMut::Val(value));
                Ok(Value::unit())
            }
            EnvLoad(index) => {
                let index = ctx.frame_base + index;
                Ok(ctx.environment[index].as_value(ctx)?)
            }
            Block(nodes) => {
                let env_size = ctx.environment.len();
                let return_value = nodes
                    .iter()
                    .try_fold(None, |_, node| Ok(Some(node.eval(ctx)?)))?
                    .unwrap_or(Value::unit());
                ctx.environment.truncate(env_size);
                Ok(return_value)
            }
            Assign(assignment) => {
                let value = assignment.value.eval(ctx)?;
                let target_ref = assignment.place.as_place(ctx)?.target_mut(ctx)?;
                *target_ref = value;
                Ok(Value::unit())
            }
            Tuple(nodes) => {
                let values = nodes.iter().try_fold(SVec2::new(), |mut nodes, node| {
                    nodes.push(node.eval(ctx)?);
                    Ok(nodes)
                })?;
                Ok(Value::Tuple(B::new(values)))
            }
            Project(node_and_index) => {
                let value = node_and_index.0.eval(ctx)?;
                Ok(match value {
                    Value::Tuple(tuple) => tuple.into_iter().nth(node_and_index.1).unwrap(),
                    Value::Variant(variant) => variant.value,
                    _ => panic!("Cannot project from a non-compound value"),
                })
            }
            Array(nodes) => {
                let values = eval_nodes(nodes, ctx)?;
                Ok(Value::native(array::Array::from_vec(values)))
            }
            Index(array, index) => {
                let index = index.eval(ctx)?.into_primitive_ty::<isize>().unwrap();
                let mut array = array
                    .eval(ctx)?
                    .into_primitive_ty::<array::Array>()
                    .unwrap();
                match array.get_mut_signed(index) {
                    Some(value) => Ok(value.clone()),
                    None => {
                        let len = array.len();
                        Err(RuntimeError::ArrayAccessOutOfBounds { index, len })
                    }
                }
            }
            Case(case) => {
                let value = case.value.eval(ctx)?;
                for (alternative, node) in &case.alternatives {
                    if value == *alternative {
                        return node.eval(ctx);
                    }
                }
                case.default.eval(ctx)
            }
            Iterate(iteration) => {
                let mut iterator = iteration
                    .iterator
                    .eval(ctx)?
                    .into_primitive_ty::<range::RangeIterator>()
                    .unwrap();
                while let Some(value) = iterator.next() {
                    ctx.environment.push(ValOrMut::Val(Value::native(value)));
                    _ = iteration.body.eval(ctx)?;
                    ctx.environment.pop();
                }
                Ok(Value::unit())
            }
        }
    }

    /// Evaluate this node given the environment and print the result.
    pub fn eval_and_print(&self, ctx: &mut EvalCtx, env: &ModuleEnv) {
        match self.eval(ctx) {
            Ok(value) => println!("{value}: {}", self.ty.format_with(env)),
            Err(error) => println!("Runtime error: {error:?}"),
        }
    }

    /// Return this node as a place in the environment.
    pub fn as_place(&self, ctx: &mut EvalCtx) -> Result<Place, RuntimeError> {
        fn resolve_node(node: &Node, ctx: &mut EvalCtx) -> Result<Place, RuntimeError> {
            use NodeKind::*;
            Ok(match &node.kind {
                Project(projection) => {
                    let (ref node, index) = **projection;
                    let mut place = resolve_node(node, ctx)?;
                    place.path.push(index as isize);
                    place
                }
                Index(array, index) => {
                    let mut place = resolve_node(array, ctx)?;
                    let index_value = index.eval(ctx)?;
                    let index = index_value.into_primitive_ty::<isize>().unwrap();
                    place.path.push(index);
                    place
                }
                EnvLoad(index) => Place {
                    // By using frame_base here, we allow to access parent frames
                    // when the ResolvedPlace is used in a child function.
                    target: ctx.frame_base + *index,
                    path: Vec::new(),
                },
                _ => panic!("Cannot resolve a non-place node"),
            })
        }
        resolve_node(self, ctx)
    }
}

impl FmtWithModuleEnv for Node {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        self.format_ind(f, env, 0)
    }
}

fn eval_nodes(nodes: &[Node], ctx: &mut EvalCtx) -> Result<Vec<Value>, RuntimeError> {
    eval_nodes_with(nodes.iter(), |node, ctx| node.eval(ctx), ctx)
}

fn eval_args(
    args: &[Node],
    args_ty: &[FnArgType],
    ctx: &mut EvalCtx,
) -> Result<Vec<ValOrMut>, RuntimeError> {
    // Automatically cast mutable references to values if the function expects values.
    let f = |(arg, ty): &(&Node, &FnArgType), ctx: &mut EvalCtx| {
        let is_mutable = ty
            .inout
            .as_resolved()
            .expect("Unresolved mutability variable found during execution")
            .is_mutable();
        Ok(if is_mutable {
            ValOrMut::Mut(arg.as_place(ctx)?)
        } else {
            ValOrMut::Val(arg.eval(ctx)?)
        })
    };
    eval_nodes_with(args.iter().zip(args_ty), f, ctx)
}

fn eval_nodes_with<F, I, O, It>(
    mut inputs: It,
    f: F,
    ctx: &mut EvalCtx,
) -> Result<Vec<O>, RuntimeError>
where
    It: Iterator<Item = I>,
    F: Fn(&I, &mut EvalCtx) -> Result<O, RuntimeError>,
{
    inputs.try_fold(vec![], |mut output, input| {
        output.push(f(&input, ctx)?);
        Ok(output)
    })
}

pub(crate) fn substitute_nodes(nodes: &mut [Node], subst: &TypeVarSubstitution) {
    for node in nodes {
        node.substitute(subst);
    }
}
