use indexmap::IndexMap;
use lrpar::Span;
use ustr::Ustr;

use crate::{
    containers::{SVec1, SVec2, B},
    dictionary_passing::DictionariesTyReq,
    function::FunctionRef,
    module::{FmtWithModuleEnv, ModuleEnv},
    r#type::{CastableToType, FnType, Type, TypeLike, TypeSubstitution, TypeVar},
    std::math::int_type,
    value::Value,
};

/// Function instantiation data that are needed to fill dictionaries
#[derive(Debug, Clone)]
pub struct FnInstData {
    pub dicts_req: DictionariesTyReq,
}
impl FnInstData {
    pub fn new(dicts_req: DictionariesTyReq) -> Self {
        Self { dicts_req }
    }
    pub fn none() -> Self {
        Self { dicts_req: vec![] }
    }
    pub fn any(&self) -> bool {
        !self.dicts_req.is_empty()
    }
    pub fn instantiate(&mut self, subst: &TypeSubstitution) {
        self.dicts_req = self
            .dicts_req
            .iter()
            .map(|req| req.instantiate(subst))
            .collect();
    }
}

/// A type variable that is not bound in the current scope
#[derive(Debug, Clone)]
pub(crate) struct UnboundTyCtx {
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct UnboundTyCtxs(Vec<UnboundTyCtx>);
impl UnboundTyCtxs {
    pub fn push(&mut self, ty: Type, span: Span) {
        self.0.push(UnboundTyCtx { ty, span });
    }

    pub fn first(&self) -> (Type, Span) {
        let ctx = &self.0[0];
        (ctx.ty, ctx.span)
    }

    pub fn seen_only_in_variants(&self, ty_var: TypeVar) -> bool {
        self.0
            .iter()
            .all(|ctx| ctx.ty.data().is_ty_var_only_in_variants(ty_var))
    }
}

/// A map of unbound type variables to the context of their first appearance
pub(crate) type UnboundTyVars = IndexMap<TypeVar, UnboundTyCtxs>;

#[derive(Debug, Clone)]
pub struct Immediate {
    pub value: Value,
    pub inst_data: FnInstData,
    pub substitute_in_value_fn: bool,
}
impl Immediate {
    pub fn new(value: Value) -> B<Self> {
        B::new(Self {
            value,
            inst_data: FnInstData::none(),
            substitute_in_value_fn: true,
        })
    }
}

#[derive(Debug, Clone)]
pub struct BuildClosure {
    pub function: Node,
    pub captures: Vec<Node>,
}

#[derive(Debug, Clone)]
pub struct Application {
    pub function: Node,
    pub arguments: Vec<Node>,
}

#[derive(Debug, Clone)]
pub struct StaticApplication {
    pub function: FunctionRef,
    pub function_name: Ustr,
    pub function_span: Span,
    pub arguments: Vec<Node>,
    pub ty: FnType,
    pub inst_data: FnInstData,
}

#[derive(Debug, Clone)]
pub struct EnvStore {
    pub node: Node,
    pub ty: Type,
    pub name_span: Span,
}
impl EnvStore {
    pub fn instantiate(&mut self, subst: &TypeSubstitution) {
        self.node.instantiate(subst);
        self.ty = self.ty.instantiate(subst);
    }
}

#[derive(Debug, Clone)]
pub struct EnvLoad {
    pub index: usize,
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
    pub var_name_span: Span,
}

/// The kind-specific part of the expression-based execution tree
#[derive(Debug, Clone)]
pub enum NodeKind {
    Immediate(B<Immediate>),
    BuildClosure(B<BuildClosure>),
    Apply(B<Application>),
    StaticApply(B<StaticApplication>),
    EnvStore(B<EnvStore>),
    EnvLoad(B<EnvLoad>),
    Block(B<SVec2<Node>>),
    Assign(B<Assignment>),
    Tuple(B<SVec2<Node>>),
    Project(B<(Node, usize)>),
    Record(B<SVec2<Node>>),
    // Note: this should only exist transiently in the IR and never be executed
    FieldAccess(B<(Node, Ustr)>),
    /// Access a tuple value using a local variable as index, after dictionary passing phase
    ProjectAt(B<(Node, usize)>),
    /// Build a variant (tagged union) with a name and a value
    Variant(B<(Ustr, Node)>),
    /// Extract the tag of a variant as an isize, by casting the pointer to the string
    ExtractTag(B<Node>),
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
            Immediate(immediate) => {
                writeln!(f, "{indent_str}immediate")?;
                immediate.value.format_ind(f, env, indent + 1)?
            }
            BuildClosure(build_closure) => {
                writeln!(f, "{indent_str}build closure of")?;
                build_closure.function.format_ind(f, env, indent + 1)?;
                writeln!(f, "{indent_str}by capturing [")?;
                for capture in &build_closure.captures {
                    capture.format_ind(f, env, indent + 1)?;
                }
                writeln!(f, "{indent_str}]")?;
            }
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
                    writeln!(f, "{indent_str})")?;
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
                writeln!(f, "{indent_str}store")?;
                node.node.format_ind(f, env, indent + 1)?;
            }
            EnvLoad(node) => writeln!(f, "{indent_str}load {}", node.index)?,
            Block(nodes) => {
                writeln!(f, "{indent_str}block {{")?;
                for node in nodes.iter() {
                    node.format_ind(f, env, indent + 1)?;
                }
                writeln!(f, "{indent_str}}}")?;
            }
            Assign(assignment) => {
                writeln!(f, "{indent_str}assign")?;
                assignment.place.format_ind(f, env, indent + 1)?;
                assignment.value.format_ind(f, env, indent + 1)?;
            }
            Tuple(nodes) => {
                writeln!(f, "{indent_str}build tuple (")?;
                for node in nodes.iter() {
                    node.format_ind(f, env, indent + 1)?;
                }
                writeln!(f, "{indent_str})")?;
            }
            Project(projection) => {
                writeln!(f, "{indent_str}project")?;
                projection.0.format_ind(f, env, indent + 1)?;
                writeln!(f, "{indent_str}at {index}", index = projection.1)?;
            }
            Record(nodes) => {
                writeln!(f, "{indent_str}build record {{")?;
                let fields: Vec<_> = self
                    .ty
                    .data()
                    .as_record()
                    .unwrap()
                    .iter()
                    .map(|(name, _)| *name)
                    .collect();
                for (node, field) in nodes.iter().zip(fields) {
                    writeln!(f, "{indent_str}⎸ {field}:")?;
                    node.format_ind(f, env, indent + 2)?;
                }
                writeln!(f, "{indent_str}}}")?;
            }
            FieldAccess(access) => {
                writeln!(f, "{indent_str}access")?;
                access.0.format_ind(f, env, indent + 1)?;
                writeln!(f, "{indent_str}at field {}", access.1)?;
            }
            ProjectAt(access) => {
                writeln!(f, "{indent_str}access")?;
                access.0.format_ind(f, env, indent + 1)?;
                writeln!(f, "{indent_str}at field referenced by local {}", access.1)?;
            }
            Variant(variant) => {
                writeln!(f, "{indent_str}variant with tag: {}", variant.0)?;
                variant.1.format_ind(f, env, indent + 1)?;
            }
            ExtractTag(node) => {
                writeln!(f, "{indent_str}extract tag of")?;
                node.format_ind(f, env, indent + 1)?;
            }
            Array(nodes) => {
                writeln!(f, "{indent_str}build array [")?;
                for node in nodes.iter() {
                    node.format_ind(f, env, indent + 1)?;
                }
                writeln!(f, "{indent_str}]")?;
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
            Immediate(_) => {}
            BuildClosure(build_closure) => {
                if let Some(ty) = build_closure.function.type_at(pos) {
                    return Some(ty);
                }
                // We do not look into captures as they are generated code.
            }
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
            Record(nodes) => {
                for node in nodes.iter() {
                    if let Some(ty) = node.type_at(pos) {
                        return Some(ty);
                    }
                }
            }
            FieldAccess(access) => {
                if let Some(ty) = access.0.type_at(pos) {
                    return Some(ty);
                }
            }
            ProjectAt(access) => {
                if let Some(ty) = access.0.type_at(pos) {
                    return Some(ty);
                }
            }
            Variant(variant) => {
                if let Some(ty) = variant.1.type_at(pos) {
                    return Some(ty);
                }
            }
            ExtractTag(node) => {
                if let Some(ty) = node.type_at(pos) {
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

    pub fn variable_type_annotations(&self, result: &mut Vec<(usize, String)>, env: &ModuleEnv) {
        use NodeKind::*;
        match &self.kind {
            Immediate(_) => {}
            BuildClosure(build_closure) => {
                build_closure
                    .function
                    .variable_type_annotations(result, env);
                // We do not look into captures as they are generated code.
            }
            Apply(app) => {
                app.function.variable_type_annotations(result, env);
                for arg in &app.arguments {
                    arg.variable_type_annotations(result, env);
                }
            }
            StaticApply(app) => {
                for arg in &app.arguments {
                    arg.variable_type_annotations(result, env);
                }
            }
            EnvStore(node) => {
                // Note: synthesized let nodes have empty name span, so we ignore these.
                if node.name_span.end() != node.name_span.start() {
                    result.push((
                        node.name_span.end(),
                        format!(": {}", node.ty.format_with(env)),
                    ));
                }
                node.node.variable_type_annotations(result, env);
            }
            EnvLoad(_) => {}
            Block(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(result, env)),
            Assign(assignment) => {
                assignment.place.variable_type_annotations(result, env);
                assignment.value.variable_type_annotations(result, env);
            }
            Tuple(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(result, env)),
            Project(projection) => projection.0.variable_type_annotations(result, env),
            Record(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(result, env)),
            FieldAccess(access) => access.0.variable_type_annotations(result, env),
            ProjectAt(access) => access.0.variable_type_annotations(result, env),
            Variant(variant) => variant.1.variable_type_annotations(result, env),
            ExtractTag(node) => node.variable_type_annotations(result, env),
            Array(nodes) => nodes
                .iter()
                .for_each(|node| node.variable_type_annotations(result, env)),
            Index(array, index) => {
                array.variable_type_annotations(result, env);
                index.variable_type_annotations(result, env);
            }
            Case(case) => {
                case.value.variable_type_annotations(result, env);
                for (_, node) in &case.alternatives {
                    node.variable_type_annotations(result, env);
                }
                case.default.variable_type_annotations(result, env);
            }
            Iterate(iteration) => {
                // TODO: once the iterator is generalized, get the type from it!
                result.push((
                    iteration.var_name_span.end(),
                    format!(": {}", int_type().format_with(env)),
                ));
                iteration.iterator.variable_type_annotations(result, env);
                iteration.body.variable_type_annotations(result, env);
            }
        }
    }

    pub(crate) fn all_unbound_ty_vars(&self) -> UnboundTyVars {
        let mut unbound = IndexMap::new();
        self.unbound_ty_vars(&mut unbound, &[]);
        unbound
    }

    pub(crate) fn unbound_ty_vars(&self, result: &mut UnboundTyVars, ignore: &[TypeVar]) {
        use NodeKind::*;
        // Add type variables for this node.
        self.unbound_ty_vars_in_ty(&self.ty, result, ignore);
        // Recurse.
        match &self.kind {
            Immediate(_) => {} // no need to look into the value's type as it is already in this node's type
            BuildClosure(_) => {
                panic!("BuildClosure should not be in the IR at this point");
            }
            Apply(app) => {
                app.function.unbound_ty_vars(result, ignore);
                for arg in &app.arguments {
                    arg.unbound_ty_vars(result, ignore);
                }
            }
            StaticApply(app) => {
                self.unbound_ty_vars_in_ty(&app.ty, result, ignore);
                for arg in &app.arguments {
                    arg.unbound_ty_vars(result, ignore);
                }
            }
            EnvStore(node) => node.node.unbound_ty_vars(result, ignore),
            EnvLoad(_) => {}
            Block(nodes) => nodes
                .iter()
                .for_each(|node| node.unbound_ty_vars(result, ignore)),
            Assign(assignment) => {
                assignment.place.unbound_ty_vars(result, ignore);
                assignment.value.unbound_ty_vars(result, ignore);
            }
            Tuple(nodes) => nodes
                .iter()
                .for_each(|node| node.unbound_ty_vars(result, ignore)),
            Project(projection) => projection.0.unbound_ty_vars(result, ignore),
            Record(nodes) => nodes
                .iter()
                .for_each(|node| node.unbound_ty_vars(result, ignore)),
            FieldAccess(access) => access.0.unbound_ty_vars(result, ignore),
            ProjectAt(_) => {
                panic!("ProjectAt should not be in the IR at this point");
            }
            Variant(variant) => variant.1.unbound_ty_vars(result, ignore),
            ExtractTag(node) => node.unbound_ty_vars(result, ignore),
            Array(nodes) => nodes
                .iter()
                .for_each(|node| node.unbound_ty_vars(result, ignore)),
            Index(array, index) => {
                array.unbound_ty_vars(result, ignore);
                index.unbound_ty_vars(result, ignore);
            }
            Case(case) => {
                case.value.unbound_ty_vars(result, ignore);
                case.alternatives.iter().for_each(|(_alternative, node)| {
                    node.unbound_ty_vars(result, ignore);
                });
                case.default.unbound_ty_vars(result, ignore);
            }
            Iterate(iteration) => {
                iteration.iterator.unbound_ty_vars(result, ignore);
                iteration.body.unbound_ty_vars(result, ignore);
            }
        }
    }

    pub(crate) fn unbound_ty_vars_in_ty(
        &self,
        ty: &impl CastableToType,
        result: &mut UnboundTyVars,
        ignore: &[TypeVar],
    ) {
        ty.inner_ty_vars().iter().for_each(|ty_var| {
            if !ignore.contains(ty_var) {
                result
                    .entry(*ty_var)
                    .or_default()
                    .push(ty.to_type(), self.span);
            }
        });
    }

    pub fn instantiate(&mut self, subst: &TypeSubstitution) {
        use NodeKind::*;
        match &mut self.kind {
            Immediate(immediate) => {
                // If the value is a top-level function, do not instantiate in its code.
                if immediate.substitute_in_value_fn {
                    immediate.value.instantiate(subst);
                }
                immediate.inst_data.instantiate(subst);
            }
            BuildClosure(_) => {
                // Note: at the moment build closure is used only for dictionary
                // passing so we can ignore the substitution here.
            }
            Apply(app) => {
                app.function.instantiate(subst);
                instantiate_nodes(&mut app.arguments, subst);
            }
            StaticApply(app) => {
                app.ty = app.ty.instantiate(subst);
                app.inst_data.instantiate(subst);
                instantiate_nodes(&mut app.arguments, subst);
            }
            EnvStore(node) => node.instantiate(subst),
            EnvLoad(_) => {}
            Block(nodes) => instantiate_nodes(nodes, subst),
            Assign(assignment) => {
                assignment.place.instantiate(subst);
                assignment.value.instantiate(subst);
            }
            Tuple(nodes) => instantiate_nodes(nodes, subst),
            Project(projection) => projection.0.instantiate(subst),
            Record(nodes) => instantiate_nodes(nodes, subst),
            FieldAccess(access) => access.0.instantiate(subst),
            ProjectAt(projection) => projection.0.instantiate(subst),
            Variant(variant) => variant.1.instantiate(subst),
            ExtractTag(node) => node.instantiate(subst),
            Array(nodes) => instantiate_nodes(nodes, subst),
            Index(array, index) => {
                array.instantiate(subst);
                index.instantiate(subst);
            }
            Case(case) => {
                case.value.instantiate(subst);
                for alternative in case.alternatives.iter_mut() {
                    alternative.0.instantiate(subst);
                    alternative.1.instantiate(subst);
                }
                case.default.instantiate(subst);
            }
            Iterate(iteration) => {
                iteration.iterator.instantiate(subst);
                iteration.body.instantiate(subst);
            }
        }
        self.ty = self.ty.instantiate(subst);
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

pub(crate) fn instantiate_nodes(nodes: &mut [Node], subst: &TypeSubstitution) {
    for node in nodes {
        node.instantiate(subst);
    }
}
