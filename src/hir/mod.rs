// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
pub(crate) mod borrow_checker;
pub(crate) mod dictionary_passing;
pub(crate) mod emit_associated_consts;
pub mod emit_ir;
pub(crate) mod emit_value_impl;
pub mod function;
pub(crate) mod hir_syn;
pub(crate) mod r#match;
pub mod value;

use crate::{
    Location,
    ast::{self, UnnamedArg},
    format::FormatWith,
    hir::function::ArgPassing,
    module::{
        ExtraParameterId, FunctionId, LocalClone, LocalDecl, LocalDeclId, LocalDrop,
        ProjectionIndex, ResolvedLocalClone, TakeLocalValueMode, TraitId, TraitImplId, id::Id,
    },
    types::r#trait::{TraitAssociatedConstIndex, TraitDictionaryEntryIndex, TraitMethodIndex},
    types::type_like::{CastableToType, TypeLike, instantiate_types_in_place},
    types::type_mapper::TypeMapper,
};
use derive_new::new;
use enum_as_inner::EnumAsInner;
use indexmap::IndexMap;
use la_arena::{Arena, Idx};
use ustr::Ustr;

use crate::{
    containers::{B, SVec2, SVec4},
    hir::dictionary_passing::DictionariesReq,
    hir::value::LiteralValue,
    module::ModuleEnv,
    types::effects::EffType,
    types::r#type::{FnType, Type, TypeVar},
};

/// An index to a node in the HIR arena
pub type NodeId = Idx<Node>;

/// A compact ordered list of HIR node IDs.
pub type NodeIds = B<SVec2<NodeId>>;

/// An arena of HIR nodes
pub type NodeArena = Arena<Node>;

pub(crate) fn node_is_place_reference(arena: &NodeArena, node_id: NodeId) -> bool {
    use NodeKind::*;

    match &arena[node_id].kind {
        LoadLocal(_) => true,
        GetTraitMethod(method) => !method.input_tys.iter().all(Type::is_constant),
        Project(_) | FieldAccess(_) | ProjectAt(_) => true,
        Apply(app) => app.returns_place,
        StaticApply(app) => app.returns_place,
        _ => false,
    }
}

pub(crate) fn place_resolution_may_create_temp(arena: &NodeArena, node_id: NodeId) -> bool {
    use NodeKind::*;

    match &arena[node_id].kind {
        LoadLocal(_) => false,
        GetTraitMethod(_) => false,
        Project(project) => {
            !node_is_place_reference(arena, project.value)
                || place_resolution_may_create_temp(arena, project.value)
        }
        FieldAccess(field_access) => {
            !node_is_place_reference(arena, field_access.value)
                || place_resolution_may_create_temp(arena, field_access.value)
        }
        ProjectAt(project) => {
            !node_is_place_reference(arena, project.value)
                || place_resolution_may_create_temp(arena, project.value)
        }
        Apply(app) if app.returns_place => {
            !node_is_place_reference(arena, app.function)
                || place_resolution_may_create_temp(arena, app.function)
                || place_result_base_argument_index(arena, &app.arguments).is_some_and(
                    |base_index| !node_is_place_reference(arena, app.arguments[base_index].value),
                )
                || app
                    .arguments
                    .iter()
                    .any(|arg| place_resolution_may_create_temp(arena, arg.value))
        }
        StaticApply(app) if app.returns_place => {
            place_result_base_argument_index(arena, &app.arguments).is_some_and(|base_index| {
                !node_is_place_reference(arena, app.arguments[base_index].value)
            }) || app
                .arguments
                .iter()
                .any(|arg| place_resolution_may_create_temp(arena, arg.value))
        }
        _ => false,
    }
}

/// Resolve a deferred let-binding storage decision once mutability inference is complete.
pub(crate) fn resolve_deferred_local_storage_shape(
    arena: &NodeArena,
    local: &mut LocalDecl,
) -> bool {
    let crate::module::LocalStorage::Deferred(deferred) = local.storage.clone() else {
        return false;
    };

    let initializer_is_known_immutable = deferred
        .initializer_mut_ty
        .as_resolved()
        .is_some_and(|mut_ty| !mut_ty.is_mutable());
    let can_alias_initializer = !deferred.binding_mutable
        && initializer_is_known_immutable
        && node_is_place_reference(arena, deferred.initializer)
        && !place_resolution_may_create_temp(arena, deferred.initializer);

    if local.ty == Type::never() || can_alias_initializer {
        local.set_non_owning_storage();
        false
    } else {
        if node_is_place_reference(arena, deferred.initializer)
            && !place_resolution_may_create_temp(arena, deferred.initializer)
        {
            local.clone = Some(LocalClone::Unknown);
        }
        local.set_owned_storage(LocalDrop::Unknown);
        true
    }
}

pub(crate) fn place_result_base_argument_index(
    arena: &NodeArena,
    arguments: &[CallArgument],
) -> Option<usize> {
    arguments
        .iter()
        .position(|argument| !is_evidence_node(&arena[argument.value].kind))
}

fn is_evidence_node(kind: &NodeKind) -> bool {
    matches!(
        kind,
        NodeKind::GetDictionary(_) | NodeKind::LoadDictionary(_) | NodeKind::LoadFieldIndex(_)
    )
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
    /// Instantiate the dictionary requirements in place with the caller-supplied mapper.
    pub(crate) fn instantiate_in_place<M: TypeMapper>(&mut self, mapper: &mut M) {
        for req in &mut self.dicts_req {
            req.instantiate_in_place(mapper);
        }
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

// Value construction payloads.

/// Build a runtime closure value from a function and captured values.
#[derive(Debug, Clone)]
pub struct BuildClosure {
    pub function: NodeId,
    pub dictionary_captures: Vec<NodeId>,
    pub captures: Vec<NodeId>,
    pub captures_value_dictionary: Option<NodeId>,
}

/// Build a variant value with a tag and payload.
#[derive(Debug, Clone, Copy, new)]
pub struct Variant {
    pub tag: Ustr,
    pub payload: NodeId,
}

// Value access payloads.

/// Project a tuple-like value at a statically known index.
#[derive(Debug, Clone, Copy, new)]
pub struct Project {
    pub value: NodeId,
    pub index: ProjectionIndex,
}

/// Access a record-like value at a statically known field.
#[derive(Debug, Clone, Copy, new)]
pub struct FieldAccess {
    pub value: NodeId,
    pub field: Ustr,
}

/// Project a tuple-like value using a hidden field-index parameter.
#[derive(Debug, Clone, Copy, new)]
pub struct ProjectAt {
    pub value: NodeId,
    pub index: ExtraParameterId,
}

// Local storage and ownership payloads.

/// Load a local as a place or borrowed value.
#[derive(Debug, Clone, Copy)]
pub struct LoadLocal {
    pub id: LocalDeclId,
}

/// Store a value into local storage.
#[derive(Debug, Clone, Copy)]
pub struct StoreLocal {
    pub value: NodeId,
    pub id: LocalDeclId,
}

/// Take a local value as an owned result.
#[derive(Debug, Clone, Copy)]
pub struct TakeLocalValue {
    pub id: LocalDeclId,
    pub mode: TakeLocalValueMode,
}

/// Drop the owned value stored in a local.
#[derive(Debug, Clone, Copy)]
pub struct DropLocal {
    pub id: LocalDeclId,
}

/// Assign a new value into an existing place.
#[derive(Debug, Clone, Copy)]
pub struct Assignment {
    pub place: NodeId,
    pub value: NodeId,
    /// Dispatch used to drop the old destination value before overwriting it.
    /// `None` is used only when the destination storage is uninitialized.
    pub drop: Option<LocalDrop>,
}

/// Materialize a value as an owned result, using the cheapest valid copy mode.
#[derive(Debug, Clone, Copy)]
pub struct CloneValue {
    pub source: NodeId,
    pub clone: LocalClone,
}

/// Clone the closure environment of `source` into already allocated `target` storage.
#[derive(Debug, Clone, Copy)]
pub struct FunctionClone {
    pub source: NodeId,
    pub target: NodeId,
}

/// Drop the owned closure environment stored in `target`.
#[derive(Debug, Clone, Copy)]
pub struct FunctionDrop {
    pub target: NodeId,
}

// Calls and function value payloads.

/// A visible call argument together with its resolved or deferred passing mode.
#[derive(Debug, Clone, Copy)]
pub struct CallArgument {
    pub value: NodeId,
    pub passing: ArgPassing,
}

impl CallArgument {
    pub(crate) fn from_values_and_passing(
        values: Vec<NodeId>,
        passing: Vec<ArgPassing>,
    ) -> Vec<Self> {
        assert_eq!(values.len(), passing.len());
        values
            .into_iter()
            .zip(passing)
            .map(|(value, passing)| Self { value, passing })
            .collect()
    }

    pub(crate) fn from_value_slice_and_passing(
        values: &[NodeId],
        passing: Vec<ArgPassing>,
    ) -> Vec<Self> {
        assert_eq!(values.len(), passing.len());
        values
            .iter()
            .copied()
            .zip(passing)
            .map(|(value, passing)| Self { value, passing })
            .collect()
    }
}

/// Load a statically known function as a first-class value.
#[derive(Debug, Clone)]
pub struct GetFunction {
    pub function: FunctionId,
    pub function_path: ast::Path,
    pub function_span: Location,
    pub inst_data: FnInstData,
}

/// Call a first-class function value.
#[derive(Debug, Clone)]
pub struct Application {
    pub function: NodeId,
    pub arguments: Vec<CallArgument>,
    pub returns_place: bool,
}

/// Call a statically known function.
#[derive(Debug, Clone)]
pub struct StaticApplication {
    pub function: FunctionId,
    pub function_path: Option<ast::Path>,
    pub function_span: Location,
    pub extra_arguments: Vec<NodeId>,
    pub arguments: Vec<CallArgument>,
    /// Optional source/debug names for visible arguments; same length as `arguments`.
    pub argument_names: Vec<Ustr>,
    pub ty: FnType,
    pub inst_data: FnInstData,
    pub returns_place: bool,
}

/// Call a trait method before dictionary passing resolves it.
#[derive(Debug, Clone)]
pub struct TraitMethodApplication {
    pub trait_id: TraitId,
    pub method_index: TraitMethodIndex,
    pub method_path: ast::Path,
    pub method_span: Location,
    pub arguments: Vec<CallArgument>,
    pub arguments_unnamed: UnnamedArg,
    pub ty: FnType,
    pub input_tys: Vec<Type>,
    pub inst_data: FnInstData,
}
impl TraitMethodApplication {
    pub fn argument_names<'a>(&self, env: &'a crate::module::ModuleEnv<'_>) -> &'a [Ustr] {
        &env.trait_def(self.trait_id)
            .method(self.method_index)
            .1
            .arg_names
    }
}

// Trait and evidence operation payloads.

/// Load a trait method as a first-class value before dictionary passing.
#[derive(Debug, Clone)]
pub struct GetTraitMethod {
    pub trait_id: TraitId,
    pub method_index: TraitMethodIndex,
    pub method_path: ast::Path,
    pub method_span: Location,
    pub input_tys: Vec<Type>,
    pub output_tys: Vec<Type>,
    pub inst_data: FnInstData,
}

/// Load a trait associated const before dictionary passing resolves it.
#[derive(Debug, Clone)]
pub struct GetTraitAssociatedConst {
    pub trait_id: TraitId,
    pub associated_const_index: TraitAssociatedConstIndex,
    pub associated_const_name: Ustr,
    pub associated_const_span: Location,
    pub input_tys: Vec<Type>,
    pub output_tys: Vec<Type>,
}

/// Load a trait dictionary before dictionary passing resolves it.
#[derive(Debug, Clone)]
pub struct GetTraitDictionary {
    pub trait_id: TraitId,
    pub input_tys: Vec<Type>,
    pub output_tys: Vec<Type>,
}

/// Get a trait dictionary selected by static trait resolution.
#[derive(Debug, Clone, Copy)]
pub struct GetDictionary {
    pub dictionary: TraitImplId,
}

/// Load a trait dictionary from a function hidden argument.
#[derive(Debug, Clone, Copy)]
pub struct LoadDictionary {
    pub extra_parameter: ExtraParameterId,
}

/// Load a structural field index from a function hidden argument.
#[derive(Debug, Clone, Copy)]
pub struct LoadFieldIndex {
    pub extra_parameter: ExtraParameterId,
}

/// Look up a method function value from a trait dictionary.
#[derive(Debug, Clone, Copy)]
pub struct GetDictionaryMethod {
    pub dictionary: NodeId,
    pub entry_index: TraitDictionaryEntryIndex,
}

/// Look up an associated const value from a trait dictionary.
#[derive(Debug, Clone, Copy)]
pub struct GetDictionaryAssociatedConst {
    pub dictionary: NodeId,
    pub entry_index: TraitDictionaryEntryIndex,
}

/// Call a method entry through a trait dictionary.
#[derive(Debug, Clone)]
pub struct CallDictionaryMethod {
    pub dictionary: NodeId,
    pub entry_index: TraitDictionaryEntryIndex,
    pub arguments: Vec<CallArgument>,
    pub ty: FnType,
}

// Control flow payloads.

/// Branch on a literal value with a default alternative.
#[derive(Debug, Clone)]
pub struct Case {
    pub value: NodeId,
    pub alternatives: Vec<(LiteralValue, NodeId)>,
    pub default: NodeId,
}

/// The kind-specific part of the expression-based execution tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum NodeKind {
    // Internal placeholders.
    /// Compiler-only uninitialized storage used while generated `Value::clone` code fills a target.
    Uninit,
    /// Placeholder used while temporarily moving a node kind out of the arena.
    Unimplemented,

    // Value construction.
    /// Return a literal value.
    Immediate(LiteralValue),
    /// Build a tuple value.
    Tuple(NodeIds),
    /// Build a record value.
    Record(NodeIds),
    /// Build an array value.
    Array(NodeIds),
    /// Build a variant value with a tag and payload.
    Variant(Variant),
    /// Build a runtime closure value from a function and captured values.
    BuildClosure(B<BuildClosure>),

    // Value access.
    /// Project a tuple-like value at a statically known index.
    Project(Project),
    /// Access a record-like value at a statically known field.
    FieldAccess(FieldAccess),
    /// Project a tuple-like value using a hidden field-index parameter.
    ProjectAt(ProjectAt),
    /// Extract the tag of a variant as an isize, by casting the pointer to the string.
    ExtractTag(NodeId),

    // Local storage and ownership.
    /// Load a local as a place or borrowed value.
    LoadLocal(LoadLocal),
    /// Store a value into local storage.
    StoreLocal(StoreLocal),
    /// Take a local value as an owned result.
    TakeLocalValue(TakeLocalValue),
    /// Drop the owned value stored in a local.
    DropLocal(DropLocal),
    /// Assign a new value into an existing place.
    Assign(Assignment),
    /// Materialize a value as an owned result, using the cheapest valid copy mode.
    CloneValue(CloneValue),
    /// Clone the closure environment of `source` into already allocated `target` storage.
    FunctionClone(FunctionClone),
    /// Drop the owned closure environment stored in `target`.
    FunctionDrop(FunctionDrop),

    // Calls and function values.
    /// Load a statically known function as a first-class value.
    GetFunction(B<GetFunction>),
    /// Call a first-class function value.
    Apply(B<Application>),
    /// Call a statically known function.
    StaticApply(B<StaticApplication>),
    /// Call a trait method before dictionary passing resolves it.
    TraitMethodApply(B<TraitMethodApplication>),

    // Trait and evidence operations.
    /// Load a trait method as a first-class value before dictionary passing.
    GetTraitMethod(B<GetTraitMethod>),
    /// Load a trait associated const before dictionary passing resolves it.
    GetTraitAssociatedConst(B<GetTraitAssociatedConst>),
    /// Load a trait dictionary before dictionary passing resolves it.
    GetTraitDictionary(B<GetTraitDictionary>),
    /// Get a trait dictionary selected by static trait resolution.
    GetDictionary(GetDictionary),
    /// Load a trait dictionary from a function hidden argument.
    LoadDictionary(LoadDictionary),
    /// Load a structural field index from a function hidden argument.
    LoadFieldIndex(LoadFieldIndex),
    /// Look up a method function value from a trait dictionary.
    GetDictionaryMethod(GetDictionaryMethod),
    /// Look up an associated const value from a trait dictionary.
    GetDictionaryAssociatedConst(GetDictionaryAssociatedConst),
    /// Call a method entry through a trait dictionary.
    CallDictionaryMethod(B<CallDictionaryMethod>),

    // Control flow.
    /// Evaluate a sequence of nodes.
    Block(NodeIds),
    /// Return from the current function.
    Return(NodeId),
    /// Branch on a literal value with a default alternative.
    Case(B<Case>),
    /// Loop forever until a return or soft break is reached.
    Loop(NodeId),
    /// Break out of the nearest loop without returning from the function.
    SoftBreak,
}

impl NodeKind {
    pub fn child_node_ids(&self) -> SVec4<NodeId> {
        use NodeKind::*;
        use smallvec::smallvec;
        match self {
            Immediate(_)
            | Uninit
            | GetFunction(_)
            | GetTraitMethod(_)
            | GetTraitAssociatedConst(_)
            | GetTraitDictionary(_)
            | GetDictionary(_)
            | LoadDictionary(_)
            | LoadFieldIndex(_)
            | DropLocal(_)
            | TakeLocalValue(_)
            | LoadLocal(_)
            | SoftBreak
            | Unimplemented => smallvec![],
            BuildClosure(bc) => {
                let mut v: SVec4<NodeId> = smallvec![bc.function];
                v.extend_from_slice(&bc.dictionary_captures);
                v.extend_from_slice(&bc.captures);
                if let Some(dict) = bc.captures_value_dictionary {
                    v.push(dict);
                }
                v
            }
            Apply(app) => {
                let mut v: SVec4<NodeId> = smallvec![app.function];
                v.extend(app.arguments.iter().map(|arg| arg.value));
                v
            }
            FunctionClone(node) => smallvec![node.source, node.target],
            FunctionDrop(node) => smallvec![node.target],
            CloneValue(node) => smallvec![node.source],
            StaticApply(app) => app
                .extra_arguments
                .iter()
                .copied()
                .chain(app.arguments.iter().map(|arg| arg.value))
                .collect(),
            GetDictionaryMethod(node) => smallvec![node.dictionary],
            GetDictionaryAssociatedConst(node) => smallvec![node.dictionary],
            CallDictionaryMethod(node) => {
                let mut v: SVec4<NodeId> = smallvec![node.dictionary];
                v.extend(node.arguments.iter().map(|arg| arg.value));
                v
            }
            TraitMethodApply(app) => app.arguments.iter().map(|arg| arg.value).collect(),
            StoreLocal(store) => smallvec![store.value],
            Return(node) | ExtractTag(node) | Loop(node) => smallvec![*node],
            Block(nodes) | Tuple(nodes) | Record(nodes) | Array(nodes) => {
                nodes.iter().copied().collect()
            }
            Assign(a) => smallvec![a.place, a.value],
            Project(node) => smallvec![node.value],
            FieldAccess(node) => smallvec![node.value],
            ProjectAt(node) => smallvec![node.value],
            Variant(node) => smallvec![node.payload],
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
    node_id: NodeId,
    f: &mut std::fmt::Formatter,
    locals: &[LocalDecl],
    env: &ModuleEnv<'_>,
    spacing: usize,
    indent: usize,
) -> std::fmt::Result {
    arena[node_id].format_ind(arena, f, locals, env, spacing, indent)
}

pub fn type_at(arena: &NodeArena, node_id: NodeId, pos: usize) -> Option<Type> {
    arena[node_id].type_at(arena, pos)
}

pub(crate) fn all_unbound_ty_vars(arena: &NodeArena, node_id: NodeId) -> UnboundTyVars {
    let mut unbound = IndexMap::new();
    unbound_ty_vars(arena, node_id, &mut unbound, &[]);
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
                writeln!(f, "{indent_str}⎸ {immediate}")?
            }
            Uninit => {
                writeln!(f, "{indent_str}uninitialized")?;
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
                if !build_closure.dictionary_captures.is_empty() {
                    writeln!(f, "{indent_str}with dictionary/evidence captures [")?;
                    for &capture in &build_closure.dictionary_captures {
                        format_ind(arena, capture, f, locals, env, spacing, indent + 1)?;
                    }
                    writeln!(f, "{indent_str}]")?;
                }
                writeln!(f, "{indent_str}by capturing [")?;
                for &capture in &build_closure.captures {
                    format_ind(arena, capture, f, locals, env, spacing, indent + 1)?;
                }
                writeln!(f, "{indent_str}]")?;
                if let Some(dict) = build_closure.captures_value_dictionary {
                    writeln!(f, "{indent_str}using capture Value dictionary")?;
                    format_ind(arena, dict, f, locals, env, spacing, indent + 1)?;
                }
            }
            Apply(app) => {
                writeln!(f, "{indent_str}eval")?;
                format_ind(arena, app.function, f, locals, env, spacing, indent + 1)?;
                if app.arguments.is_empty() {
                    writeln!(f, "{indent_str}and apply to ()")?;
                } else {
                    writeln!(f, "{indent_str}and apply to (")?;
                    for arg in &app.arguments {
                        format_ind(arena, arg.value, f, locals, env, spacing, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")?;
                }
            }
            FunctionClone(node) => {
                writeln!(f, "{indent_str}function clone")?;
                format_ind(arena, node.source, f, locals, env, spacing, indent + 1)?;
                writeln!(f, "{indent_str}into")?;
                format_ind(arena, node.target, f, locals, env, spacing, indent + 1)?;
            }
            FunctionDrop(node) => {
                writeln!(f, "{indent_str}function drop")?;
                format_ind(arena, node.target, f, locals, env, spacing, indent + 1)?;
            }
            CloneValue(node) => {
                match node.clone {
                    LocalClone::Unknown => {
                        writeln!(f, "{indent_str}clone value with unknown mode")?;
                    }
                    LocalClone::Resolved(ResolvedLocalClone::TrivialCopy) => {
                        writeln!(f, "{indent_str}clone value with trivial copy")?;
                    }
                    LocalClone::Resolved(
                        ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_),
                    ) => {
                        writeln!(f, "{indent_str}clone value with Value::clone")?;
                    }
                }
                format_ind(arena, node.source, f, locals, env, spacing, indent + 1)?;
            }
            StaticApply(app) => {
                writeln!(f, "{indent_str}static apply")?;
                let ty = app.ty.format_with(env);
                writeln!(f, "{indent_str}  {}: {ty}", app.function.format_with(env))?;
                if !app.extra_arguments.is_empty() {
                    writeln!(f, "{indent_str}with dictionary/evidence (")?;
                    for &arg in &app.extra_arguments {
                        format_ind(arena, arg, f, locals, env, spacing, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")?;
                }
                if app.arguments.is_empty() {
                    writeln!(f, "{indent_str}to ()")?;
                } else {
                    writeln!(f, "{indent_str}to (")?;
                    for (name, arg) in app.argument_names.iter().zip(app.arguments.iter()) {
                        if !name.is_empty() {
                            writeln!(f, "{indent_str}  {name}:")?;
                        }
                        format_ind(arena, arg.value, f, locals, env, spacing, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")?;
                }
            }
            TraitMethodApply(app) => {
                let trait_def = env.trait_def(app.trait_id);
                let method_data = trait_def.method(app.method_index);
                let method_name = method_data.0;
                let method_def = &method_data.1;
                let trait_name = trait_def.name;
                writeln!(
                    f,
                    "{indent_str}trait method apply {method_name} (from {trait_name})"
                )?;
                if app.arguments.is_empty() {
                    writeln!(f, "{indent_str}to ()")?;
                } else {
                    writeln!(f, "{indent_str}to (")?;
                    for (name, arg) in method_def.arg_names.iter().zip(app.arguments.iter()) {
                        writeln!(f, "{indent_str}  {name}:")?;
                        format_ind(arena, arg.value, f, locals, env, spacing, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")?;
                }
            }
            GetFunction(get_fn) => {
                writeln!(f, "{indent_str}get {}", get_fn.function.format_with(env))?;
            }
            GetTraitMethod(get_method) => {
                let trait_def = env.trait_def(get_method.trait_id);
                let method_name = trait_def.method(get_method.method_index).0;
                let trait_name = trait_def.name;
                writeln!(
                    f,
                    "{indent_str}get trait method {method_name} (from {trait_name})"
                )?;
            }
            GetTraitAssociatedConst(get_const) => {
                let trait_name = env.trait_def(get_const.trait_id).name;
                let const_name = get_const.associated_const_name;
                writeln!(
                    f,
                    "{indent_str}get trait associated const {const_name} (from {trait_name})"
                )?;
            }
            GetTraitDictionary(get_dict) => {
                let trait_name = env.trait_def(get_dict.trait_id).name;
                writeln!(f, "{indent_str}get trait dictionary (from {trait_name})")?;
            }
            GetDictionary(get_dict) => {
                writeln!(
                    f,
                    "{indent_str}get {}",
                    get_dict.dictionary.format_with(env)
                )?;
            }
            LoadDictionary(load) => {
                writeln!(
                    f,
                    "{indent_str}load dictionary extra parameter {}",
                    load.extra_parameter.as_index()
                )?;
            }
            LoadFieldIndex(load) => {
                writeln!(
                    f,
                    "{indent_str}load field index extra parameter {}",
                    load.extra_parameter.as_index()
                )?;
            }
            GetDictionaryMethod(get_method) => {
                writeln!(
                    f,
                    "{indent_str}get dictionary method entry {}",
                    usize::from(get_method.entry_index)
                )?;
                format_ind(
                    arena,
                    get_method.dictionary,
                    f,
                    locals,
                    env,
                    spacing,
                    indent + 1,
                )?;
            }
            GetDictionaryAssociatedConst(get_const) => {
                writeln!(
                    f,
                    "{indent_str}get dictionary associated const entry {}",
                    usize::from(get_const.entry_index)
                )?;
                format_ind(
                    arena,
                    get_const.dictionary,
                    f,
                    locals,
                    env,
                    spacing,
                    indent + 1,
                )?;
            }
            CallDictionaryMethod(call) => {
                writeln!(
                    f,
                    "{indent_str}call dictionary method entry {}",
                    usize::from(call.entry_index)
                )?;
                writeln!(f, "{indent_str}with dictionary")?;
                format_ind(arena, call.dictionary, f, locals, env, spacing, indent + 1)?;
                if call.arguments.is_empty() {
                    writeln!(f, "{indent_str}to ()")?;
                } else {
                    writeln!(f, "{indent_str}to (")?;
                    for arg in &call.arguments {
                        format_ind(arena, arg.value, f, locals, env, spacing, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")?;
                }
            }
            StoreLocal(node) => {
                let local = &locals[node.id.as_index()];
                let name = local.name.0;
                let clone_suffix = if local.clone.is_some() {
                    " with Value::clone"
                } else {
                    ""
                };
                writeln!(
                    f,
                    "{indent_str}store {} at {} as \"{}\"{}",
                    arena[node.value].ty.format_with(env),
                    local.slot,
                    name,
                    clone_suffix,
                )?;
                format_ind(arena, node.value, f, locals, env, spacing, indent + 1)?;
            }
            DropLocal(node) => {
                let local = &locals[node.id.as_index()];
                let name = local.name.0;
                writeln!(
                    f,
                    "{indent_str}drop {} at {} as \"{}\"",
                    local.ty.format_with(env),
                    local.slot,
                    name,
                )?;
            }
            TakeLocalValue(node) => {
                let local = &locals[node.id.as_index()];
                let mode = match node.mode {
                    TakeLocalValueMode::Unknown => "unknown",
                    TakeLocalValueMode::MoveOwned => "move",
                    TakeLocalValueMode::CloneBorrowed(ResolvedLocalClone::TrivialCopy) => {
                        "trivial copy"
                    }
                    TakeLocalValueMode::CloneBorrowed(
                        ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_),
                    ) => "Value::clone",
                };
                writeln!(
                    f,
                    "{indent_str}take local {} as \"{}\" with {mode}",
                    local.slot, local.name.0
                )?;
            }
            LoadLocal(node) => {
                let local = &locals[node.id.as_index()];
                writeln!(f, "{indent_str}load {} as \"{}\"", local.slot, local.name.0)?;
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
            Project(node) => {
                writeln!(f, "{indent_str}project")?;
                format_ind(arena, node.value, f, locals, env, spacing, indent + 1)?;
                writeln!(f, "{indent_str}at {}", node.index.as_index())?;
            }
            Record(nodes) => {
                let ty_data = self.ty.data();
                let inner_ty = if ty_data.is_named() {
                    let named = ty_data.as_named().unwrap().clone();
                    drop(ty_data);
                    named.instantiated_shape(env)
                } else {
                    drop(ty_data);
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
            FieldAccess(node) => {
                writeln!(f, "{indent_str}access")?;
                format_ind(arena, node.value, f, locals, env, spacing, indent + 1)?;
                writeln!(f, "{indent_str}at field {}", node.field)?;
            }
            ProjectAt(node) => {
                writeln!(f, "{indent_str}access")?;
                format_ind(arena, node.value, f, locals, env, spacing, indent + 1)?;
                writeln!(
                    f,
                    "{indent_str}at field referenced by extra parameter {}",
                    node.index.as_index()
                )?;
            }
            Variant(node) => {
                writeln!(f, "{indent_str}variant with tag: {}", node.tag)?;
                format_ind(arena, node.payload, f, locals, env, spacing, indent + 1)?;
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
            Case(case) => {
                writeln!(f, "{indent_str}match")?;
                format_ind(arena, case.value, f, locals, env, spacing, indent + 1)?;
                for (alternative, node) in &case.alternatives {
                    write!(f, "{indent_str}case ",)?;
                    write!(f, "{alternative}")?;
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
            Immediate(_) | Uninit => {}
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
                for arg in &app.arguments {
                    if let Some(ty) = type_at(arena, arg.value, pos) {
                        return Some(ty);
                    }
                }
            }
            FunctionClone(node) => {
                if let Some(ty) = type_at(arena, node.source, pos) {
                    return Some(ty);
                }
                if let Some(ty) = type_at(arena, node.target, pos) {
                    return Some(ty);
                }
            }
            FunctionDrop(node) => {
                if let Some(ty) = type_at(arena, node.target, pos) {
                    return Some(ty);
                }
            }
            CloneValue(node) => {
                if let Some(ty) = type_at(arena, node.source, pos) {
                    return Some(ty);
                }
            }
            StaticApply(app) => {
                for arg in &app.arguments {
                    if let Some(ty) = type_at(arena, arg.value, pos) {
                        return Some(ty);
                    }
                }
            }
            TraitMethodApply(app) => {
                for arg in &app.arguments {
                    if let Some(ty) = type_at(arena, arg.value, pos) {
                        return Some(ty);
                    }
                }
            }
            GetFunction(_) => {
                // GetFunction nodes don't contain child expressions with types
            }
            GetTraitMethod(_) => {
                // GetTraitMethod nodes don't contain child expressions with types
            }
            GetTraitAssociatedConst(_) => {
                // GetTraitAssociatedConst nodes don't contain child expressions with types
            }
            GetTraitDictionary(_) => {
                // GetTraitDictionary nodes don't contain child expressions with types
            }
            GetDictionary(_) => {
                // GetDictionary nodes don't contain child expressions with types
            }
            LoadDictionary(_) | LoadFieldIndex(_) => {}
            GetDictionaryMethod(node) => {
                if let Some(ty) = type_at(arena, node.dictionary, pos) {
                    return Some(ty);
                }
            }
            GetDictionaryAssociatedConst(node) => {
                if let Some(ty) = type_at(arena, node.dictionary, pos) {
                    return Some(ty);
                }
            }
            CallDictionaryMethod(node) => {
                if let Some(ty) = type_at(arena, node.dictionary, pos) {
                    return Some(ty);
                }
                for arg in &node.arguments {
                    if let Some(ty) = type_at(arena, arg.value, pos) {
                        return Some(ty);
                    }
                }
            }
            StoreLocal(store) => {
                if let Some(ty) = type_at(arena, store.value, pos) {
                    return Some(ty);
                }
            }
            DropLocal(_) => {}
            TakeLocalValue(_) => {}
            LoadLocal(_) => {}
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
            Project(node) => {
                if let Some(ty) = type_at(arena, node.value, pos) {
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
            FieldAccess(node) => {
                if let Some(ty) = type_at(arena, node.value, pos) {
                    return Some(ty);
                }
            }
            ProjectAt(node) => {
                if let Some(ty) = type_at(arena, node.value, pos) {
                    return Some(ty);
                }
            }
            Variant(node) => {
                if let Some(ty) = type_at(arena, node.payload, pos) {
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
            Immediate(_) | Uninit => {} // no need to look into the value's type as it is already in this node's type
            BuildClosure(_) => {
                // no need to look into the value's type as it is already in this node's type
            }
            Apply(app) => {
                unbound_ty_vars(arena, app.function, result, ignore);
                for arg in &app.arguments {
                    unbound_ty_vars(arena, arg.value, result, ignore);
                }
            }
            FunctionClone(node) => {
                unbound_ty_vars(arena, node.source, result, ignore);
                unbound_ty_vars(arena, node.target, result, ignore);
            }
            FunctionDrop(node) => unbound_ty_vars(arena, node.target, result, ignore),
            CloneValue(node) => unbound_ty_vars(arena, node.source, result, ignore),
            StaticApply(app) => {
                self.unbound_ty_vars_in_ty(&app.ty, result, ignore);
                for arg in &app.arguments {
                    unbound_ty_vars(arena, arg.value, result, ignore);
                }
            }
            TraitMethodApply(app) => {
                self.unbound_ty_vars_in_ty(&app.ty, result, ignore);
                for arg in &app.arguments {
                    unbound_ty_vars(arena, arg.value, result, ignore);
                }
            }
            GetFunction(_) => {
                // no need to look into the value's type as it is already in this node's type
            }
            GetTraitMethod(_) => {}
            GetTraitAssociatedConst(get_const) => {
                for ty in &get_const.input_tys {
                    self.unbound_ty_vars_in_ty(ty, result, ignore);
                }
                for ty in &get_const.output_tys {
                    self.unbound_ty_vars_in_ty(ty, result, ignore);
                }
            }
            GetTraitDictionary(get_dict) => {
                for ty in &get_dict.input_tys {
                    self.unbound_ty_vars_in_ty(ty, result, ignore);
                }
                for ty in &get_dict.output_tys {
                    self.unbound_ty_vars_in_ty(ty, result, ignore);
                }
            }
            GetDictionary(_) => {
                // no need to look into the dictionary's type as it is already in this node's type
            }
            LoadDictionary(_) | LoadFieldIndex(_) => {}
            GetDictionaryMethod(node) => {
                unbound_ty_vars(arena, node.dictionary, result, ignore);
            }
            GetDictionaryAssociatedConst(node) => {
                unbound_ty_vars(arena, node.dictionary, result, ignore);
            }
            CallDictionaryMethod(node) => {
                self.unbound_ty_vars_in_ty(&node.ty, result, ignore);
                unbound_ty_vars(arena, node.dictionary, result, ignore);
                for arg in &node.arguments {
                    unbound_ty_vars(arena, arg.value, result, ignore);
                }
            }
            StoreLocal(node) => unbound_ty_vars(arena, node.value, result, ignore),
            DropLocal(_) => {}
            TakeLocalValue(_) => {}
            LoadLocal(_) => {}
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
            Project(node) => unbound_ty_vars(arena, node.value, result, ignore),
            Record(nodes) => nodes
                .iter()
                .for_each(|&node| unbound_ty_vars(arena, node, result, ignore)),
            FieldAccess(node) => unbound_ty_vars(arena, node.value, result, ignore),
            ProjectAt(_) => {
                panic!("ProjectAt should not be in the HIR at this point");
            }
            Variant(node) => unbound_ty_vars(arena, node.payload, result, ignore),
            ExtractTag(node) => unbound_ty_vars(arena, *node, result, ignore),
            Array(nodes) => nodes
                .iter()
                .for_each(|&node| unbound_ty_vars(arena, node, result, ignore)),
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

/// Instantiate a node and its children in place with a type mapper.
pub(crate) fn instantiate_node_in_place<M: TypeMapper>(
    arena: &mut NodeArena,
    node_id: NodeId,
    mapper: &mut M,
) {
    use NodeKind::*;
    // Instantiate children first
    let children = arena[node_id].kind.child_node_ids();
    for child in children {
        instantiate_node_in_place(arena, child, mapper);
    }
    // Then modify this node's kind-specific data
    match &mut arena[node_id].kind {
        StaticApply(app) => {
            app.ty = app.ty.map(mapper);
            app.inst_data.instantiate_in_place(mapper);
        }
        TraitMethodApply(app) => {
            app.ty = app.ty.map(mapper);
            instantiate_types_in_place(&mut app.input_tys, mapper);
            app.inst_data.instantiate_in_place(mapper);
        }
        GetFunction(get_fn) => {
            get_fn.inst_data.instantiate_in_place(mapper);
        }
        GetTraitMethod(get_method) => {
            instantiate_types_in_place(&mut get_method.input_tys, mapper);
            instantiate_types_in_place(&mut get_method.output_tys, mapper);
            get_method.inst_data.instantiate_in_place(mapper);
        }
        GetTraitAssociatedConst(get_const) => {
            instantiate_types_in_place(&mut get_const.input_tys, mapper);
            instantiate_types_in_place(&mut get_const.output_tys, mapper);
        }
        GetTraitDictionary(get_dict) => {
            instantiate_types_in_place(&mut get_dict.input_tys, mapper);
            instantiate_types_in_place(&mut get_dict.output_tys, mapper);
        }
        CallDictionaryMethod(call) => {
            call.ty = call.ty.map(mapper);
        }
        _ => {}
    }
    arena[node_id].ty = arena[node_id].ty.map(mapper);
    arena[node_id].effects = mapper.map_effect_type(&arena[node_id].effects);
}

#[derive(new)]
pub struct ExprDisplay<'a> {
    pub body: NodeId,
    pub locals: &'a [LocalDecl],
}

impl FormatWith<ModuleEnv<'_>> for ExprDisplay<'_> {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        format_ind(&env.current.ir_arena, self.body, f, self.locals, env, 0, 0)
    }
}
