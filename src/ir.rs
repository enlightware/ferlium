// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    Location,
    ast::{self, UnnamedArg},
    format::FormatWith,
    module::{FunctionId, LocalDecl, LocalDeclId, TraitImplId, id::Id},
    r#trait::TraitRef,
    r#type::TypeKind,
    type_like::{CastableToType, TypeLike},
};
use derive_new::new;
use enum_as_inner::EnumAsInner;
use indexmap::IndexMap;
use la_arena::{Arena, Idx};
use ustr::Ustr;

use crate::{
    containers::{B, SVec2, SVec4, b},
    dictionary_passing::DictionariesReq,
    effects::EffType,
    module::ModuleEnv,
    r#type::{FnType, Type, TypeVar},
    type_inference::InstSubstitution,
    value::Value,
};

/// An index to a node in the IR arena
pub type NodeId = Idx<Node>;

/// An arena of IR nodes
pub type NodeArena = Arena<Node>;

/// A self-contained IR body with its arena and root node
#[derive(Debug, Clone, new)]
pub struct IrBody {
    pub arena: NodeArena,
    pub root: NodeId,
}

/// Function instantiation data that are needed to fill dictionaries
#[derive(Debug, Clone, new)]
pub struct FnInstData {
    pub dicts_req: DictionariesReq,
}
impl FnInstData {
    pub fn none() -> Self {
        Self { dicts_req: vec![] }
    }
    pub fn any(&self) -> bool {
        !self.dicts_req.is_empty()
    }
    pub fn instantiate(&mut self, subst: &InstSubstitution) {
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
    pub span: Location,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct UnboundTyCtxs(Vec<UnboundTyCtx>);
impl UnboundTyCtxs {
    pub fn push(&mut self, ty: Type, span: Location) {
        self.0.push(UnboundTyCtx { ty, span });
    }

    pub fn first(&self) -> (Type, Location) {
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
}
impl Immediate {
    pub fn new(value: Value) -> B<Self> {
        b(Self { value })
    }
}

// TODO: add TraitFnImmediate for trait functions

#[derive(Debug, Clone)]
pub struct BuildClosure {
    pub function: NodeId,
    pub captures: Vec<NodeId>,
}

#[derive(Debug, Clone)]
pub struct Application {
    pub function: NodeId,
    pub arguments: Vec<NodeId>,
}

#[derive(Debug, Clone)]
pub struct StaticApplication {
    pub function: FunctionId,
    pub function_path: Option<ast::Path>,
    pub function_span: Location,
    pub arguments: Vec<NodeId>,
    pub argument_names: Vec<Ustr>,
    pub ty: FnType,
    pub inst_data: FnInstData,
}

#[derive(Debug, Clone)]
pub struct TraitFnApplication {
    pub trait_ref: TraitRef,
    pub function_index: usize,
    pub function_path: ast::Path,
    pub function_span: Location,
    pub arguments: Vec<NodeId>,
    pub arguments_unnamed: UnnamedArg,
    pub ty: FnType,
    pub input_tys: Vec<Type>,
    pub inst_data: FnInstData,
}
impl TraitFnApplication {
    pub fn argument_names(&self) -> &[Ustr] {
        &self.trait_ref.functions[self.function_index].1.arg_names
    }
}

#[derive(Debug, Clone)]
pub struct EnvStore {
    pub value: NodeId,
    pub index: u32,
    pub id: LocalDeclId,
}

#[derive(Debug, Clone)]
pub struct EnvLoad {
    pub index: u32,
    pub id: LocalDeclId,
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub place: NodeId,
    pub value: NodeId,
}

#[derive(Debug, Clone)]
pub struct Case {
    pub value: NodeId,
    pub alternatives: Vec<(Value, NodeId)>,
    pub default: NodeId,
}

#[derive(Debug, Clone)]
pub struct GetFunction {
    pub function: FunctionId,
    pub function_path: ast::Path,
    pub function_span: Location,
    pub inst_data: FnInstData,
}

#[derive(Debug, Clone)]
pub struct GetDictionary {
    pub dictionary: TraitImplId,
}

/// The kind-specific part of the expression-based execution tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum NodeKind {
    Immediate(B<Immediate>),
    BuildClosure(B<BuildClosure>),
    Apply(B<Application>),
    StaticApply(B<StaticApplication>),
    /// Note: this should only exist transiently in the IR and never be executed
    TraitFnApply(B<TraitFnApplication>),
    GetFunction(B<GetFunction>),
    GetDictionary(GetDictionary),
    EnvStore(EnvStore),
    EnvLoad(EnvLoad),
    Return(NodeId),
    Block(B<SVec2<NodeId>>),
    Assign(Assignment),
    Tuple(B<SVec2<NodeId>>),
    Project(NodeId, usize),
    Record(B<SVec2<NodeId>>),
    // Note: this should only exist transiently in the IR and never be executed
    FieldAccess(NodeId, Ustr),
    /// Access a tuple value using a local variable as index, after dictionary passing phase
    ProjectAt(NodeId, usize),
    /// Build a variant (tagged union) with a name and a value
    Variant(Ustr, NodeId),
    /// Extract the tag of a variant as an isize, by casting the pointer to the string
    ExtractTag(NodeId),
    Array(B<SVec2<NodeId>>),
    Index(NodeId, NodeId),
    Case(B<Case>),
    Loop(NodeId),
    SoftBreak,
    Unimplemented,
}

impl NodeKind {
    pub fn child_node_ids(&self) -> SVec4<NodeId> {
        use NodeKind::*;
        use smallvec::smallvec;
        match self {
            Immediate(_) | GetFunction(_) | GetDictionary(_) | EnvLoad(_) | SoftBreak
            | Unimplemented => smallvec![],
            BuildClosure(bc) => {
                let mut v: SVec4<NodeId> = smallvec![bc.function];
                v.extend_from_slice(&bc.captures);
                v
            }
            Apply(app) => {
                let mut v: SVec4<NodeId> = smallvec![app.function];
                v.extend_from_slice(&app.arguments);
                v
            }
            StaticApply(app) => app.arguments.iter().copied().collect(),
            TraitFnApply(app) => app.arguments.iter().copied().collect(),
            EnvStore(store) => smallvec![store.value],
            Return(node) | ExtractTag(node) | Loop(node) => smallvec![*node],
            Block(nodes) | Tuple(nodes) | Record(nodes) | Array(nodes) => {
                nodes.iter().copied().collect()
            }
            Assign(a) => smallvec![a.place, a.value],
            Project(n, _) | ProjectAt(n, _) => smallvec![*n],
            FieldAccess(fa, _) => smallvec![*fa],
            Variant(_, n) => smallvec![*n],
            Index(a, b) => smallvec![*a, *b],
            Case(case) => {
                let mut v: SVec4<NodeId> = SVec4::with_capacity(2 + case.alternatives.len());
                v.push(case.value);
                v.extend(case.alternatives.iter().map(|(_, n)| *n));
                v.push(case.default);
                v
            }
        }
    }
}

/// A node of the expression-based execution tree
#[derive(Debug, Clone, new)]
pub struct Node {
    /// The actual content of this node
    pub kind: NodeKind,
    /// The type of the returned value when this node is evaluated
    pub ty: Type,
    /// The effects of evaluating this node
    pub effects: EffType,
    /// The span of the source code that generated this node
    pub span: Location,
}

pub fn format_ind(
    arena: &NodeArena,
    id: NodeId,
    f: &mut std::fmt::Formatter,
    locals: &[LocalDecl],
    env: &ModuleEnv<'_>,
    spacing: usize,
    indent: usize,
) -> std::fmt::Result {
    arena[id].format_ind(arena, f, locals, env, spacing, indent)
}

pub fn type_at(arena: &NodeArena, node_id: NodeId, pos: usize) -> Option<Type> {
    arena[node_id].type_at(arena, pos)
}

pub(crate) fn all_unbound_ty_vars(arena: &NodeArena, id: NodeId) -> UnboundTyVars {
    let mut unbound = IndexMap::new();
    unbound_ty_vars(arena, id, &mut unbound, &[]);
    unbound
}

pub(crate) fn unbound_ty_vars(
    arena: &NodeArena,
    node_id: NodeId,
    result: &mut UnboundTyVars,
    ignore: &[TypeVar],
) {
    arena[node_id].unbound_ty_vars(arena, result, ignore)
}

impl Node {
    pub fn format_ind(
        &self,
        arena: &NodeArena,
        f: &mut std::fmt::Formatter,
        locals: &[LocalDecl],
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        use NodeKind::*;
        match &self.kind {
            Immediate(immediate) => {
                writeln!(f, "{indent_str}immediate")?;
                immediate
                    .value
                    .format_ind_repr(f, env, spacing, indent + 1)?
            }
            BuildClosure(build_closure) => {
                writeln!(f, "{indent_str}build closure of")?;
                format_ind(
                    arena,
                    build_closure.function,
                    f,
                    locals,
                    env,
                    spacing,
                    indent + 1,
                )?;
                writeln!(f, "{indent_str}by capturing [")?;
                for &capture in &build_closure.captures {
                    format_ind(arena, capture, f, locals, env, spacing, indent + 1)?;
                }
                writeln!(f, "{indent_str}]")?;
            }
            Apply(app) => {
                writeln!(f, "{indent_str}eval")?;
                format_ind(arena, app.function, f, locals, env, spacing, indent + 1)?;
                if app.arguments.is_empty() {
                    writeln!(f, "{indent_str}and apply to ()")?;
                } else {
                    writeln!(f, "{indent_str}and apply to (")?;
                    for &arg in &app.arguments {
                        format_ind(arena, arg, f, locals, env, spacing, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")?;
                }
            }
            StaticApply(app) => {
                writeln!(f, "{indent_str}static apply")?;
                let ty = app.ty.format_with(env);
                writeln!(f, "{indent_str}  {}: {ty}", app.function.format_with(env))?;
                if app.arguments.is_empty() {
                    writeln!(f, "{indent_str}to ()")?;
                } else {
                    writeln!(f, "{indent_str}to (")?;
                    for (name, &arg) in app.argument_names.iter().zip(app.arguments.iter()) {
                        if !name.is_empty() {
                            writeln!(f, "{indent_str}  {name}:")?;
                        }
                        format_ind(arena, arg, f, locals, env, spacing, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")?;
                }
            }
            TraitFnApply(app) => {
                let fn_data = &app.trait_ref.functions[app.function_index];
                let fn_name = fn_data.0;
                let fn_def = &fn_data.1;
                let trait_name = app.trait_ref.name;
                writeln!(
                    f,
                    "{indent_str}trait fn apply {fn_name} (from {trait_name})"
                )?;
                if app.arguments.is_empty() {
                    writeln!(f, "{indent_str}to ()")?;
                } else {
                    writeln!(f, "{indent_str}to (")?;
                    for (name, &arg) in fn_def.arg_names.iter().zip(app.arguments.iter()) {
                        writeln!(f, "{indent_str}  {name}:")?;
                        format_ind(arena, arg, f, locals, env, spacing, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")?;
                }
            }
            GetFunction(get_fn) => {
                writeln!(f, "{indent_str}get {}", get_fn.function.format_with(env))?;
            }
            GetDictionary(get_dict) => {
                writeln!(
                    f,
                    "{indent_str}get {}",
                    get_dict.dictionary.format_with(env)
                )?;
            }
            EnvStore(node) => {
                let name = locals[node.id.as_index()].name.0;
                writeln!(
                    f,
                    "{indent_str}store {} at {} as \"{}\"",
                    arena[node.value].ty.format_with(env),
                    node.index,
                    name,
                )?;
                format_ind(arena, node.value, f, locals, env, spacing, indent + 1)?;
            }
            EnvLoad(node) => {
                let name = locals[node.id.as_index()].name.0;
                writeln!(f, "{indent_str}load {} as \"{}\"", node.index, name)?;
            }
            Return(node) => {
                writeln!(f, "{indent_str}return")?;
                format_ind(arena, *node, f, locals, env, spacing, indent + 1)?;
            }
            Block(nodes) => {
                writeln!(f, "{indent_str}block {{")?;
                for &node in nodes.iter() {
                    format_ind(arena, node, f, locals, env, spacing, indent + 1)?;
                }
                writeln!(f, "{indent_str}}}")?;
            }
            Assign(assignment) => {
                writeln!(f, "{indent_str}assign")?;
                format_ind(arena, assignment.place, f, locals, env, spacing, indent + 1)?;
                format_ind(arena, assignment.value, f, locals, env, spacing, indent + 1)?;
            }
            Tuple(nodes) => {
                writeln!(f, "{indent_str}build tuple (")?;
                for &node in nodes.iter() {
                    format_ind(arena, node, f, locals, env, spacing, indent + 1)?;
                }
                writeln!(f, "{indent_str})")?;
            }
            Project(data, index) => {
                writeln!(f, "{indent_str}project")?;
                format_ind(arena, *data, f, locals, env, spacing, indent + 1)?;
                writeln!(f, "{indent_str}at {}", *index)?;
            }
            Record(nodes) => {
                let inner_ty = if let TypeKind::Named(named) = &*self.ty.data() {
                    named.def.shape
                } else {
                    self.ty
                };
                writeln!(f, "{indent_str}build record {{")?;
                let fields: Vec<_> = inner_ty
                    .data()
                    .as_record()
                    .unwrap()
                    .iter()
                    .map(|(name, _)| *name)
                    .collect();
                for (&node, field) in nodes.iter().zip(fields) {
                    writeln!(f, "{indent_str}⎸ {field}:")?;
                    format_ind(arena, node, f, locals, env, spacing, indent + 2)?;
                }
                writeln!(f, "{indent_str}}}")?;
            }
            FieldAccess(data, field) => {
                writeln!(f, "{indent_str}access")?;
                format_ind(arena, *data, f, locals, env, spacing, indent + 1)?;
                writeln!(f, "{indent_str}at field {}", field)?;
            }
            ProjectAt(data, index) => {
                writeln!(f, "{indent_str}access")?;
                format_ind(arena, *data, f, locals, env, spacing, indent + 1)?;
                writeln!(f, "{indent_str}at field referenced by local {}", *index)?;
            }
            Variant(tag, payload) => {
                writeln!(f, "{indent_str}variant with tag: {}", *tag)?;
                format_ind(arena, *payload, f, locals, env, spacing, indent + 1)?;
            }
            ExtractTag(node) => {
                writeln!(f, "{indent_str}extract tag of")?;
                format_ind(arena, *node, f, locals, env, spacing, indent + 1)?;
            }
            Array(nodes) => {
                writeln!(f, "{indent_str}build array [")?;
                for &node in nodes.iter() {
                    format_ind(arena, node, f, locals, env, spacing, indent + 1)?;
                }
                writeln!(f, "{indent_str}]")?;
            }
            Index(array, index) => {
                writeln!(f, "{indent_str}index")?;
                format_ind(arena, *array, f, locals, env, spacing, indent + 1)?;
                format_ind(arena, *index, f, locals, env, spacing, indent + 1)?;
            }
            Case(case) => {
                writeln!(f, "{indent_str}match")?;
                format_ind(arena, case.value, f, locals, env, spacing, indent + 1)?;
                for (alternative, node) in &case.alternatives {
                    write!(f, "{indent_str}case ",)?;
                    alternative.format_as_string_repr(f)?;
                    writeln!(f)?;
                    format_ind(arena, *node, f, locals, env, spacing, indent + 1)?;
                }
                writeln!(f, "{indent_str}default")?;
                format_ind(arena, case.default, f, locals, env, spacing, indent + 1)?;
            }
            Loop(body) => {
                writeln!(f, "{indent_str}loop")?;
                format_ind(arena, *body, f, locals, env, spacing, indent + 1)?;
            }
            SoftBreak => {
                writeln!(f, "{indent_str}soft break")?;
            }
            Unimplemented => {
                writeln!(f, "{indent_str}unimplemented")?;
            }
        };
        write!(f, "{indent_str}↳ {}", self.ty.format_with(env))?;
        if !self.effects.is_empty() {
            write!(f, " ! {}", self.effects)?;
        }
        writeln!(f)
    }

    pub fn type_at(&self, arena: &NodeArena, pos: usize) -> Option<Type> {
        // Early exit if the position is outside the node's span.
        if pos < self.span.start_usize() || pos >= self.span.end_usize() {
            return None;
        }

        // Look into children.
        use NodeKind::*;
        match &self.kind {
            Immediate(_) => {}
            BuildClosure(build_closure) => {
                if let Some(ty) = type_at(arena, build_closure.function, pos) {
                    return Some(ty);
                }
                // We do not look into captures as they are generated code.
            }
            Apply(app) => {
                if let Some(ty) = type_at(arena, app.function, pos) {
                    return Some(ty);
                }
                for &arg in &app.arguments {
                    if let Some(ty) = type_at(arena, arg, pos) {
                        return Some(ty);
                    }
                }
            }
            StaticApply(app) => {
                for &arg in &app.arguments {
                    if let Some(ty) = type_at(arena, arg, pos) {
                        return Some(ty);
                    }
                }
            }
            TraitFnApply(app) => {
                for &arg in &app.arguments {
                    if let Some(ty) = type_at(arena, arg, pos) {
                        return Some(ty);
                    }
                }
            }
            GetFunction(_) => {
                // GetFunction nodes don't contain child expressions with types
            }
            GetDictionary(_) => {
                // GetDictionary nodes don't contain child expressions with types
            }
            EnvStore(store) => {
                if let Some(ty) = type_at(arena, store.value, pos) {
                    return Some(ty);
                }
            }
            EnvLoad(_) => {}
            Return(node) => {
                if let Some(ty) = type_at(arena, *node, pos) {
                    return Some(ty);
                }
            }
            Block(nodes) => {
                for &child in nodes.iter() {
                    if let Some(ty) = type_at(arena, child, pos) {
                        return Some(ty);
                    }
                }
            }
            Assign(assignment) => {
                if let Some(ty) = type_at(arena, assignment.place, pos) {
                    return Some(ty);
                }
                if let Some(ty) = type_at(arena, assignment.value, pos) {
                    return Some(ty);
                }
            }
            Tuple(nodes) => {
                for &child in nodes.iter() {
                    if let Some(ty) = type_at(arena, child, pos) {
                        return Some(ty);
                    }
                }
            }
            Project(data, _) => {
                if let Some(ty) = type_at(arena, *data, pos) {
                    return Some(ty);
                }
            }
            Record(nodes) => {
                for &child in nodes.iter() {
                    if let Some(ty) = type_at(arena, child, pos) {
                        return Some(ty);
                    }
                }
            }
            FieldAccess(data, _) => {
                if let Some(ty) = type_at(arena, *data, pos) {
                    return Some(ty);
                }
            }
            ProjectAt(data, _) => {
                if let Some(ty) = type_at(arena, *data, pos) {
                    return Some(ty);
                }
            }
            Variant(_, payload) => {
                if let Some(ty) = type_at(arena, *payload, pos) {
                    return Some(ty);
                }
            }
            ExtractTag(node) => {
                if let Some(ty) = type_at(arena, *node, pos) {
                    return Some(ty);
                }
            }
            Array(nodes) => {
                for &node in nodes.iter() {
                    if let Some(ty) = type_at(arena, node, pos) {
                        return Some(ty);
                    }
                }
            }
            Index(array, index) => {
                if let Some(ty) = type_at(arena, *array, pos) {
                    return Some(ty);
                }
                if let Some(ty) = type_at(arena, *index, pos) {
                    return Some(ty);
                }
            }
            Case(case) => {
                if let Some(ty) = type_at(arena, case.value, pos) {
                    return Some(ty);
                }
                for (_, node) in &case.alternatives {
                    if let Some(ty) = type_at(arena, *node, pos) {
                        return Some(ty);
                    }
                }
                if let Some(ty) = type_at(arena, case.default, pos) {
                    return Some(ty);
                }
            }
            Loop(body) => {
                if let Some(ty) = type_at(arena, *body, pos) {
                    return Some(ty);
                }
            }
            SoftBreak | Unimplemented => {}
        }

        // No children has this position, return our type.
        Some(self.ty)
    }

    pub(crate) fn unbound_ty_vars(
        &self,
        arena: &NodeArena,
        result: &mut UnboundTyVars,
        ignore: &[TypeVar],
    ) {
        use NodeKind::*;
        // Add type variables for this node.
        self.unbound_ty_vars_in_ty(&self.ty, result, ignore);
        // Recurse.
        match &self.kind {
            Immediate(_) => {} // no need to look into the value's type as it is already in this node's type
            BuildClosure(_) => {
                // no need to look into the value's type as it is already in this node's type
            }
            Apply(app) => {
                unbound_ty_vars(arena, app.function, result, ignore);
                for &arg in &app.arguments {
                    unbound_ty_vars(arena, arg, result, ignore);
                }
            }
            StaticApply(app) => {
                self.unbound_ty_vars_in_ty(&app.ty, result, ignore);
                for &arg in &app.arguments {
                    unbound_ty_vars(arena, arg, result, ignore);
                }
            }
            TraitFnApply(app) => {
                self.unbound_ty_vars_in_ty(&app.ty, result, ignore);
                for &arg in &app.arguments {
                    unbound_ty_vars(arena, arg, result, ignore);
                }
            }
            GetFunction(_) => {
                // no need to look into the value's type as it is already in this node's type
            }
            GetDictionary(_) => {
                // no need to look into the dictionary's type as it is already in this node's type
            }
            EnvStore(node) => unbound_ty_vars(arena, node.value, result, ignore),
            EnvLoad(_) => {}
            Return(node) => unbound_ty_vars(arena, *node, result, ignore),
            Block(nodes) => nodes
                .iter()
                .for_each(|&node| unbound_ty_vars(arena, node, result, ignore)),
            Assign(assignment) => {
                unbound_ty_vars(arena, assignment.place, result, ignore);
                unbound_ty_vars(arena, assignment.value, result, ignore);
            }
            Tuple(nodes) => nodes
                .iter()
                .for_each(|&node| unbound_ty_vars(arena, node, result, ignore)),
            Project(data, _) => unbound_ty_vars(arena, *data, result, ignore),
            Record(nodes) => nodes
                .iter()
                .for_each(|&node| unbound_ty_vars(arena, node, result, ignore)),
            FieldAccess(data, _) => unbound_ty_vars(arena, *data, result, ignore),
            ProjectAt(_, _) => {
                panic!("ProjectAt should not be in the IR at this point");
            }
            Variant(_, payload) => unbound_ty_vars(arena, *payload, result, ignore),
            ExtractTag(node) => unbound_ty_vars(arena, *node, result, ignore),
            Array(nodes) => nodes
                .iter()
                .for_each(|&node| unbound_ty_vars(arena, node, result, ignore)),
            Index(array, index) => {
                unbound_ty_vars(arena, *array, result, ignore);
                unbound_ty_vars(arena, *index, result, ignore);
            }
            Case(case) => {
                unbound_ty_vars(arena, case.value, result, ignore);
                case.alternatives.iter().for_each(|(_, node)| {
                    unbound_ty_vars(arena, *node, result, ignore);
                });
                unbound_ty_vars(arena, case.default, result, ignore);
            }
            Loop(body) => {
                unbound_ty_vars(arena, *body, result, ignore);
            }
            SoftBreak | Unimplemented => {}
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
}

pub fn instantiate_node(arena: &mut NodeArena, id: NodeId, subst: &InstSubstitution) {
    use NodeKind::*;
    // Instantiate children first
    let children = arena[id].kind.child_node_ids();
    for child in children {
        instantiate_node(arena, child, subst);
    }
    // Then modify this node's kind-specific data
    match &mut arena[id].kind {
        StaticApply(app) => {
            app.ty = app.ty.instantiate(subst);
            app.inst_data.instantiate(subst);
        }
        TraitFnApply(app) => {
            app.ty = app.ty.instantiate(subst);
            app.input_tys = app
                .input_tys
                .iter()
                .map(|ty| ty.instantiate(subst))
                .collect();
            app.inst_data.instantiate(subst);
        }
        GetFunction(get_fn) => {
            get_fn.inst_data.instantiate(subst);
        }
        _ => {}
    }
    arena[id].ty = arena[id].ty.instantiate(subst);
    arena[id].effects = arena[id].effects.instantiate(&subst.1);
}

#[derive(new)]
pub struct IrBodyDisplay<'a> {
    pub body: &'a IrBody,
    pub locals: &'a [LocalDecl],
}

impl FormatWith<ModuleEnv<'_>> for IrBodyDisplay<'_> {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        format_ind(&self.body.arena, self.body.root, f, self.locals, env, 0, 0)
    }
}
