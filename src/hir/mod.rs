// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
pub(crate) mod borrow_checker;
pub(crate) mod dictionary;
pub(crate) mod elaboration;
pub(crate) mod emit_associated_consts;
pub(crate) mod emit_expr;
pub(crate) mod emit_functions;
pub(crate) mod emit_hir;
pub(crate) mod emit_value_impl;
pub mod function;
pub(crate) mod hir_syn;
pub(crate) mod r#match;
pub mod value;
pub(crate) mod value_dispatch;

pub use emit_expr::CompiledExpr;

#[doc(hidden)]
pub mod test_support {
    pub use crate::hir::emit_expr::emit_expr_unsafe;
    pub use crate::hir::emit_hir::{EmitModuleFrom, emit_module};
}

use crate::{
    Location,
    ast::{self, UnnamedArg},
    format::FormatWith,
    hir::function::{PendingArgPassing, ResolvedArgPassing},
    module::{
        ExtraParameterId, FunctionId, LocalCloneMetadata, LocalDecl, LocalDeclId,
        PendingLocalClone, PendingLocalDrop, PendingTakeLocalValueMode, ProjectionIndex,
        ResolvedLocalClone, ResolvedLocalDrop, ResolvedTakeLocalValueMode,
        TakeLocalValueModeMetadata, TraitId, TraitImplId, id::Id,
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
    hir::dictionary::DictionariesReq,
    hir::value::LiteralValue,
    module::ModuleEnv,
    types::effects::EffType,
    types::never::Never,
    types::r#type::{FnType, Type, TypeVar},
};

/// A phase of HIR compilation.
pub trait HirPhase: Sized + std::fmt::Debug + Clone {
    type FieldAccess: HirPayload<Self>;
    type TraitMethodApplication: HirPayload<Self>;
    type GetTraitMethod: HirPayload<Self>;
    type GetTraitAssociatedConst: HirPayload<Self>;
    type GetTraitDictionary: HirPayload<Self>;
    /// Clone metadata carried by local declarations and clone nodes in this phase.
    type LocalClone: std::fmt::Debug + Clone + Copy + LocalCloneMetadata;
    /// Drop metadata carried by local declarations and assignment nodes in this phase.
    type LocalDrop: std::fmt::Debug + Clone + Copy;
    /// Take-local mode carried by `TakeLocalValue` nodes in this phase.
    type TakeLocalValueMode: std::fmt::Debug + Clone + Copy + TakeLocalValueModeMetadata;
    /// Argument-passing metadata carried by call arguments in this phase.
    type CallArgPassing: std::fmt::Debug + Clone + Copy;
    /// Deferred local-storage payload carried by local declarations in this phase.
    type DeferredLocalStorage: std::fmt::Debug + Clone + Copy;
}

/// HIR before dictionary passing and final ownership/call elaboration.
#[derive(Debug, Clone, Default)]
pub struct Unelaborated;

/// HIR after dictionary passing and final ownership/call elaboration.
#[derive(Debug, Clone, Default)]
pub struct Elaborated;

impl HirPhase for Unelaborated {
    type FieldAccess = FieldAccess<Self>;
    type TraitMethodApplication = B<TraitMethodApplication<Self>>;
    type GetTraitMethod = B<GetTraitMethod>;
    type GetTraitAssociatedConst = B<GetTraitAssociatedConst>;
    type GetTraitDictionary = B<GetTraitDictionary>;
    type LocalClone = PendingLocalClone;
    type LocalDrop = PendingLocalDrop;
    type TakeLocalValueMode = PendingTakeLocalValueMode;
    type CallArgPassing = PendingArgPassing;
    type DeferredLocalStorage = crate::module::DeferredLocalStorage;
}

impl HirPhase for Elaborated {
    type FieldAccess = Never;
    type TraitMethodApplication = Never;
    type GetTraitMethod = Never;
    type GetTraitAssociatedConst = Never;
    type GetTraitDictionary = Never;
    type LocalClone = ResolvedLocalClone;
    type LocalDrop = ResolvedLocalDrop;
    type TakeLocalValueMode = ResolvedTakeLocalValueMode;
    type CallArgPassing = ResolvedArgPassing;
    type DeferredLocalStorage = Never;
}

/// An index to a node in the HIR arena.
pub type NodeId<P = Unelaborated> = Idx<Node<P>>;

crate::define_id_type!(
    /// A unique loop identifier within a function.
    LoopId
);

/// A compact ordered list of HIR node IDs.
pub type NodeIds<P = Unelaborated> = B<SVec2<NodeId<P>>>;

/// An arena of HIR nodes.
pub type NodeArena<P = Unelaborated> = Arena<Node<P>>;

/// A HIR node before elaboration.
pub type UNode = Node<Unelaborated>;

/// A HIR node after elaboration.
pub type ENode = Node<Elaborated>;

/// A HIR node kind before elaboration.
pub type UNodeKind = NodeKind<Unelaborated>;

/// A HIR node kind after elaboration.
pub type ENodeKind = NodeKind<Elaborated>;

/// A HIR node id before elaboration.
pub type UNodeId = NodeId<Unelaborated>;

/// A HIR node id after elaboration.
pub type ENodeId = NodeId<Elaborated>;

/// A HIR arena before elaboration.
pub type UNodeArena = NodeArena<Unelaborated>;

/// A HIR arena after elaboration.
pub type ENodeArena = NodeArena<Elaborated>;

pub(crate) fn node_is_place_reference(arena: &NodeArena, node_id: NodeId) -> bool {
    use NodeKind::*;

    match &arena[node_id].kind {
        LoadLocal(_) => true,
        // Borrow-like only while still dispatched through a dictionary: a non-constant input
        // type means the method is resolved at runtime; a fully-constant receiver lowers to a
        // freshly produced static function value, which is not a place.
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
    local: &mut LocalDecl<Unelaborated>,
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
            local.clone = Some(PendingLocalClone::Unknown);
        }
        local.set_owned_storage(PendingLocalDrop::Unknown);
        true
    }
}

pub(crate) fn place_result_base_argument_index(
    arena: &NodeArena,
    arguments: &[CallArgument],
) -> Option<usize> {
    let base = arguments
        .iter()
        .position(|argument| !is_evidence_node(&arena[argument.value].kind));
    // The place-producing receiver is the first non-evidence argument; this relies on hidden
    // evidence arguments forming a contiguous prefix of the argument list. Verify in debug builds.
    debug_assert!(
        base.map(|base| arguments[base..]
            .iter()
            .all(|argument| !is_evidence_node(&arena[argument.value].kind)))
            .unwrap_or(true),
        "evidence arguments must form a contiguous prefix of the argument list"
    );
    base
}

/// Whether `kind` is a hidden evidence argument (trait dictionary or field index) rather than a value argument.
/// Evidence arguments are expected to form a contiguous prefix of a call's argument list; see [`place_result_base_argument_index`].
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
pub struct BuildClosure<P: HirPhase = Unelaborated> {
    pub function: NodeId<P>,
    pub dictionary_captures: Vec<NodeId<P>>,
    pub captures: Vec<NodeId<P>>,
    pub captures_value_dictionary: Option<NodeId<P>>,
}

/// Build a variant value with a tag and payload.
#[derive(Debug, Clone, Copy, new)]
pub struct Variant<P: HirPhase = Unelaborated> {
    pub tag: Ustr,
    pub payload: NodeId<P>,
}

// Value access payloads.

/// Project a tuple-like value at a statically known index.
#[derive(Debug, Clone, Copy, new)]
pub struct Project<P: HirPhase = Unelaborated> {
    pub value: NodeId<P>,
    pub index: ProjectionIndex,
}

/// Access a record-like value at a statically known field.
#[derive(Debug, Clone, Copy, new)]
pub struct FieldAccess<P: HirPhase = Unelaborated> {
    pub value: NodeId<P>,
    pub field: Ustr,
}

/// Project a tuple-like value using a hidden field-index parameter.
#[derive(Debug, Clone, Copy, new)]
pub struct ProjectAt<P: HirPhase = Unelaborated> {
    pub value: NodeId<P>,
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
pub struct StoreLocal<P: HirPhase = Unelaborated> {
    pub value: NodeId<P>,
    pub id: LocalDeclId,
}

/// Take a local value as an owned result.
#[derive(Debug, Clone, Copy)]
pub struct TakeLocalValue<P: HirPhase = Unelaborated> {
    pub id: LocalDeclId,
    pub mode: P::TakeLocalValueMode,
}

/// Assign a new value into an existing place.
#[derive(Debug, Clone, Copy)]
pub struct Assignment<P: HirPhase = Unelaborated> {
    pub place: NodeId<P>,
    pub value: NodeId<P>,
    /// Dispatch used to drop the old destination value before overwriting it.
    /// `None` is used only when the destination storage is uninitialized.
    pub drop: Option<P::LocalDrop>,
}

/// Materialize a value as an owned result, using the cheapest valid copy mode.
#[derive(Debug, Clone, Copy)]
pub struct CloneValue<P: HirPhase = Unelaborated> {
    pub source: NodeId<P>,
    pub clone: P::LocalClone,
}

/// Evaluate a sequence of nodes.
///
/// `cleanup` lists the block's cleanup obligations in declaration order.
/// Cleanup runs in reverse order on exits from the block, but an implementation
/// must only drop obligations whose storage is live and initialized at that exit.
#[derive(Debug, Clone)]
pub struct Block<P: HirPhase = Unelaborated> {
    pub body: NodeIds<P>,
    /// Locals in declaration order.
    pub cleanup: Vec<LocalDeclId>,
}

/// A loop with an explicit label used as the target for loop control flow.
#[derive(Debug, Clone, Copy, new)]
pub struct Loop<P: HirPhase = Unelaborated> {
    pub label: LoopId,
    pub body: NodeId<P>,
}

/// A value-carrying break targeting a resolved loop label.
#[derive(Debug, Clone, Copy, new)]
pub struct Break<P: HirPhase = Unelaborated> {
    pub label: LoopId,
    pub value: NodeId<P>,
}

/// A continue targeting a resolved loop label.
#[derive(Debug, Clone, Copy, new)]
pub struct Continue {
    pub label: LoopId,
}

/// Clone the closure environment of `source` into already allocated `target` storage.
#[derive(Debug, Clone, Copy)]
pub struct CloneClosureEnv<P: HirPhase = Unelaborated> {
    pub source: NodeId<P>,
    pub target: NodeId<P>,
}

/// Drop the owned closure environment stored in `target`.
#[derive(Debug, Clone, Copy)]
pub struct DropClosureEnv<P: HirPhase = Unelaborated> {
    pub target: NodeId<P>,
}

// Calls and function value payloads.

/// A visible call argument together with its resolved or deferred passing mode.
#[derive(Debug, Clone, Copy)]
pub struct CallArgument<P: HirPhase = Unelaborated> {
    pub value: NodeId<P>,
    pub passing: P::CallArgPassing,
}

impl<P: HirPhase> CallArgument<P> {
    pub(crate) fn from_values_and_passing(
        values: Vec<NodeId<P>>,
        passing: Vec<P::CallArgPassing>,
    ) -> Vec<Self> {
        assert_eq!(values.len(), passing.len());
        values
            .into_iter()
            .zip(passing)
            .map(|(value, passing)| Self { value, passing })
            .collect()
    }

    pub(crate) fn from_value_slice_and_passing(
        values: &[NodeId<P>],
        passing: Vec<P::CallArgPassing>,
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
pub struct Application<P: HirPhase = Unelaborated> {
    pub function: NodeId<P>,
    pub arguments: Vec<CallArgument<P>>,
    pub returns_place: bool,
}

/// Call a statically known function.
#[derive(Debug, Clone)]
pub struct StaticApplication<P: HirPhase = Unelaborated> {
    pub function: FunctionId,
    pub function_path: Option<ast::Path>,
    pub function_span: Location,
    pub extra_arguments: Vec<NodeId<P>>,
    pub arguments: Vec<CallArgument<P>>,
    /// Optional source/debug names for visible arguments; same length as `arguments`.
    pub argument_names: Vec<Ustr>,
    pub ty: FnType,
    pub inst_data: FnInstData,
    pub returns_place: bool,
}

/// Call a trait method before dictionary passing resolves it.
#[derive(Debug, Clone)]
pub struct TraitMethodApplication<P: HirPhase = Unelaborated> {
    pub trait_id: TraitId,
    pub method_index: TraitMethodIndex,
    pub method_path: ast::Path,
    pub method_span: Location,
    pub arguments: Vec<CallArgument<P>>,
    pub arguments_unnamed: UnnamedArg,
    pub ty: FnType,
    pub input_tys: Vec<Type>,
    pub inst_data: FnInstData,
}
impl<P: HirPhase> TraitMethodApplication<P> {
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
pub struct GetDictionaryMethod<P: HirPhase = Unelaborated> {
    pub dictionary: NodeId<P>,
    pub entry_index: TraitDictionaryEntryIndex,
}

/// Look up an associated const value from a trait dictionary.
#[derive(Debug, Clone, Copy)]
pub struct GetDictionaryAssociatedConst<P: HirPhase = Unelaborated> {
    pub dictionary: NodeId<P>,
    pub entry_index: TraitDictionaryEntryIndex,
}

/// Call a method entry through a trait dictionary.
#[derive(Debug, Clone)]
pub struct CallDictionaryMethod<P: HirPhase = Unelaborated> {
    pub dictionary: NodeId<P>,
    pub entry_index: TraitDictionaryEntryIndex,
    pub arguments: Vec<CallArgument<P>>,
    pub ty: FnType,
}

// Control flow payloads.

/// Branch on a literal value with a default alternative.
#[derive(Debug, Clone)]
pub struct Case<P: HirPhase = Unelaborated> {
    pub value: NodeId<P>,
    pub alternatives: Vec<(LiteralValue, NodeId<P>)>,
    pub default: NodeId<P>,
}

/// The kind-specific part of the expression-based execution tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum NodeKind<P: HirPhase = Unelaborated> {
    // Internal placeholders.
    /// Compiler-only uninitialized storage used while generated `Value::clone` code fills a target.
    Uninit,

    // Value construction.
    /// Return a literal value.
    Immediate(LiteralValue),
    /// Build a tuple value.
    Tuple(NodeIds<P>),
    /// Build a record value.
    Record(NodeIds<P>),
    /// Build an array value.
    Array(NodeIds<P>),
    /// Build a variant value with a tag and payload.
    Variant(Variant<P>),
    /// Build a runtime closure value from a function and captured values.
    BuildClosure(B<BuildClosure<P>>),

    // Value access.
    /// Project a tuple-like value at a statically known index.
    Project(Project<P>),
    /// Access a record-like value at a statically known field.
    FieldAccess(P::FieldAccess),
    /// Project a tuple-like value using a hidden field-index parameter.
    ProjectAt(ProjectAt<P>),
    /// Extract the tag of a variant as an isize, by casting the pointer to the string.
    ExtractTag(NodeId<P>),

    // Local storage and ownership.
    /// Load a local as a place or borrowed value.
    LoadLocal(LoadLocal),
    /// Store a value into local storage.
    StoreLocal(StoreLocal<P>),
    /// Take a local value as an owned result.
    TakeLocalValue(TakeLocalValue<P>),
    /// Assign a new value into an existing place.
    Assign(Assignment<P>),
    /// Materialize a value as an owned result, using the cheapest valid copy mode.
    CloneValue(CloneValue<P>),
    /// Clone the closure environment of `source` into already allocated `target` storage.
    CloneClosureEnv(CloneClosureEnv<P>),
    /// Drop the owned closure environment stored in `target`.
    DropClosureEnv(DropClosureEnv<P>),

    // Calls and function values.
    /// Load a statically known function as a first-class value.
    GetFunction(B<GetFunction>),
    /// Call a first-class function value.
    Apply(B<Application<P>>),
    /// Call a statically known function.
    StaticApply(B<StaticApplication<P>>),
    /// Call a trait method before dictionary passing resolves it.
    TraitMethodApply(P::TraitMethodApplication),

    // Trait and evidence operations.
    /// Load a trait method as a first-class value before dictionary passing.
    GetTraitMethod(P::GetTraitMethod),
    /// Load a trait associated const before dictionary passing resolves it.
    GetTraitAssociatedConst(P::GetTraitAssociatedConst),
    /// Load a trait dictionary before dictionary passing resolves it.
    GetTraitDictionary(P::GetTraitDictionary),
    /// Get a trait dictionary selected by static trait resolution.
    GetDictionary(GetDictionary),
    /// Load a trait dictionary from a function hidden argument.
    LoadDictionary(LoadDictionary),
    /// Load a structural field index from a function hidden argument.
    LoadFieldIndex(LoadFieldIndex),
    /// Look up a method function value from a trait dictionary.
    GetDictionaryMethod(GetDictionaryMethod<P>),
    /// Look up an associated const value from a trait dictionary.
    GetDictionaryAssociatedConst(GetDictionaryAssociatedConst<P>),
    /// Call a method entry through a trait dictionary.
    CallDictionaryMethod(B<CallDictionaryMethod<P>>),

    // Runtime checks.
    /// Check the current function call depth against the runtime limit.
    CheckCallDepth,
    /// Consume one unit of execution fuel from the runtime context.
    CheckFuel,

    // Control flow.
    /// Evaluate a sequence of nodes with optional cleanup on every exit path.
    Block(B<Block<P>>),
    /// Return from the current function.
    Return(NodeId<P>),
    /// Branch on a literal value with a default alternative.
    Case(B<Case<P>>),
    /// Loop forever until a return or break targeting this loop is reached.
    Loop(Loop<P>),
    /// Break out of the targeted loop with a result value.
    Break(Break<P>),
    /// Continue the targeted loop.
    Continue(Continue),
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
            | TakeLocalValue(_)
            | LoadLocal(_)
            | CheckCallDepth
            | CheckFuel
            | Continue(_) => smallvec![],
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
            CloneClosureEnv(node) => smallvec![node.source, node.target],
            DropClosureEnv(node) => smallvec![node.target],
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
            Return(node) | ExtractTag(node) => smallvec![*node],
            Loop(node) => smallvec![node.body],
            Break(node) => smallvec![node.value],
            Block(block) => block.body.iter().copied().collect(),
            Tuple(nodes) | Record(nodes) | Array(nodes) => nodes.iter().copied().collect(),
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
pub struct Node<P: HirPhase = Unelaborated> {
    /// The actual content of this node
    pub kind: NodeKind<P>,
    /// The type of the returned value when this node is evaluated
    pub ty: Type,
    /// The effects of evaluating this node
    pub effects: EffType,
    /// The span of the source code that generated this node
    pub span: Location,
}

pub trait HirPayload<P: HirPhase>: std::fmt::Debug + Clone {
    #[allow(clippy::too_many_arguments)]
    fn format_ind(
        &self,
        arena: &NodeArena<P>,
        f: &mut std::fmt::Formatter,
        locals: &[LocalDecl<P>],
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
        indent_str: &str,
    ) -> std::fmt::Result;

    fn type_at(&self, arena: &NodeArena<P>, pos: usize) -> Option<Type> {
        let _ = (arena, pos);
        None
    }
}

impl<P: HirPhase> HirPayload<P> for Never {
    fn format_ind(
        &self,
        _arena: &NodeArena<P>,
        _f: &mut std::fmt::Formatter,
        _locals: &[LocalDecl<P>],
        _env: &ModuleEnv<'_>,
        _spacing: usize,
        _indent: usize,
        _indent_str: &str,
    ) -> std::fmt::Result {
        match *self {}
    }

    fn type_at(&self, _arena: &NodeArena<P>, _pos: usize) -> Option<Type> {
        match *self {}
    }
}

impl<P: HirPhase> HirPayload<P> for FieldAccess<P> {
    fn format_ind(
        &self,
        arena: &NodeArena<P>,
        f: &mut std::fmt::Formatter,
        locals: &[LocalDecl<P>],
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
        indent_str: &str,
    ) -> std::fmt::Result {
        writeln!(f, "{indent_str}access")?;
        format_ind(arena, self.value, f, locals, env, spacing, indent + 1)?;
        writeln!(f, "{indent_str}at field {}", self.field)
    }

    fn type_at(&self, arena: &NodeArena<P>, pos: usize) -> Option<Type> {
        type_at(arena, self.value, pos)
    }
}

impl<P: HirPhase> HirPayload<P> for B<TraitMethodApplication<P>> {
    fn format_ind(
        &self,
        arena: &NodeArena<P>,
        f: &mut std::fmt::Formatter,
        locals: &[LocalDecl<P>],
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
        indent_str: &str,
    ) -> std::fmt::Result {
        let trait_def = env.trait_def(self.trait_id);
        let method_data = trait_def.method(self.method_index);
        let method_name = method_data.0;
        let method_def = &method_data.1;
        let trait_name = trait_def.name;
        writeln!(
            f,
            "{indent_str}trait method apply {method_name} (from {trait_name})"
        )?;
        if self.arguments.is_empty() {
            writeln!(f, "{indent_str}to ()")?;
        } else {
            writeln!(f, "{indent_str}to (")?;
            for (name, arg) in method_def.arg_names.iter().zip(self.arguments.iter()) {
                writeln!(f, "{indent_str}  {name}:")?;
                format_ind(arena, arg.value, f, locals, env, spacing, indent + 1)?;
            }
            writeln!(f, "{indent_str})")?;
        }
        Ok(())
    }

    fn type_at(&self, arena: &NodeArena<P>, pos: usize) -> Option<Type> {
        for arg in &self.arguments {
            if let Some(ty) = type_at(arena, arg.value, pos) {
                return Some(ty);
            }
        }
        None
    }
}

impl<P: HirPhase> HirPayload<P> for B<GetTraitMethod> {
    fn format_ind(
        &self,
        _arena: &NodeArena<P>,
        f: &mut std::fmt::Formatter,
        _locals: &[LocalDecl<P>],
        env: &ModuleEnv<'_>,
        _spacing: usize,
        _indent: usize,
        indent_str: &str,
    ) -> std::fmt::Result {
        let trait_def = env.trait_def(self.trait_id);
        let method_name = trait_def.method(self.method_index).0;
        let trait_name = trait_def.name;
        writeln!(
            f,
            "{indent_str}get trait method {method_name} (from {trait_name})"
        )
    }
}

impl<P: HirPhase> HirPayload<P> for B<GetTraitAssociatedConst> {
    fn format_ind(
        &self,
        _arena: &NodeArena<P>,
        f: &mut std::fmt::Formatter,
        _locals: &[LocalDecl<P>],
        env: &ModuleEnv<'_>,
        _spacing: usize,
        _indent: usize,
        indent_str: &str,
    ) -> std::fmt::Result {
        let trait_name = env.trait_def(self.trait_id).name;
        let const_name = self.associated_const_name;
        writeln!(
            f,
            "{indent_str}get trait associated const {const_name} (from {trait_name})"
        )
    }
}

impl<P: HirPhase> HirPayload<P> for B<GetTraitDictionary> {
    fn format_ind(
        &self,
        _arena: &NodeArena<P>,
        f: &mut std::fmt::Formatter,
        _locals: &[LocalDecl<P>],
        env: &ModuleEnv<'_>,
        _spacing: usize,
        _indent: usize,
        indent_str: &str,
    ) -> std::fmt::Result {
        let trait_name = env.trait_def(self.trait_id).name;
        writeln!(f, "{indent_str}get trait dictionary (from {trait_name})")
    }
}

pub(crate) fn format_ind<P: HirPhase>(
    arena: &NodeArena<P>,
    node_id: NodeId<P>,
    f: &mut std::fmt::Formatter,
    locals: &[LocalDecl<P>],
    env: &ModuleEnv<'_>,
    spacing: usize,
    indent: usize,
) -> std::fmt::Result {
    arena[node_id].format_ind(arena, f, locals, env, spacing, indent)
}

pub(crate) fn type_at<P: HirPhase>(
    arena: &NodeArena<P>,
    node_id: NodeId<P>,
    pos: usize,
) -> Option<Type> {
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

impl<P: HirPhase> Node<P> {
    pub(crate) fn format_ind(
        &self,
        arena: &NodeArena<P>,
        f: &mut std::fmt::Formatter,
        locals: &[LocalDecl<P>],
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
            CloneClosureEnv(node) => {
                writeln!(f, "{indent_str}clone closure env")?;
                format_ind(arena, node.source, f, locals, env, spacing, indent + 1)?;
                writeln!(f, "{indent_str}into")?;
                format_ind(arena, node.target, f, locals, env, spacing, indent + 1)?;
            }
            DropClosureEnv(node) => {
                writeln!(f, "{indent_str}drop closure env")?;
                format_ind(arena, node.target, f, locals, env, spacing, indent + 1)?;
            }
            CloneValue(node) => {
                writeln!(
                    f,
                    "{indent_str}clone value with {}",
                    node.clone.format_label()
                )?;
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
                app.format_ind(arena, f, locals, env, spacing, indent, &indent_str)?
            }
            GetFunction(get_fn) => {
                writeln!(f, "{indent_str}get {}", get_fn.function.format_with(env))?;
            }
            GetTraitMethod(get_method) => {
                get_method.format_ind(arena, f, locals, env, spacing, indent, &indent_str)?;
            }
            GetTraitAssociatedConst(get_const) => {
                get_const.format_ind(arena, f, locals, env, spacing, indent, &indent_str)?;
            }
            GetTraitDictionary(get_dict) => {
                get_dict.format_ind(arena, f, locals, env, spacing, indent, &indent_str)?;
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
            TakeLocalValue(node) => {
                let local = &locals[node.id.as_index()];
                let mode = node.mode.format_label();
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
            Block(block) => {
                writeln!(f, "{indent_str}block {{")?;
                for &node in block.body.iter() {
                    format_ind(arena, node, f, locals, env, spacing, indent + 1)?;
                }
                if !block.cleanup.is_empty() {
                    writeln!(f, "{indent_str}cleanup [")?;
                    for id in &block.cleanup {
                        let local = &locals[id.as_index()];
                        writeln!(
                            f,
                            "{indent_str}⎸ drop {} at {} as \"{}\"",
                            local.ty.format_with(env),
                            local.slot,
                            local.name.0,
                        )?;
                    }
                    writeln!(f, "{indent_str}]")?;
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
                node.format_ind(arena, f, locals, env, spacing, indent, &indent_str)?;
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
            Loop(node) => {
                writeln!(f, "{indent_str}loop {}", node.label)?;
                format_ind(arena, node.body, f, locals, env, spacing, indent + 1)?;
            }
            Break(node) => {
                writeln!(f, "{indent_str}break {}", node.label)?;
                format_ind(arena, node.value, f, locals, env, spacing, indent + 1)?;
            }
            Continue(node) => {
                writeln!(f, "{indent_str}continue {}", node.label)?;
            }
            CheckCallDepth => {
                writeln!(f, "{indent_str}check call depth")?;
            }
            CheckFuel => {
                writeln!(f, "{indent_str}check fuel")?;
            }
        };
        write!(f, "{indent_str}↳ {}", self.ty.format_with(env))?;
        if !self.effects.is_empty() {
            write!(f, " ! {}", self.effects)?;
        }
        writeln!(f)
    }

    pub(crate) fn type_at(&self, arena: &NodeArena<P>, pos: usize) -> Option<Type> {
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
            CloneClosureEnv(node) => {
                if let Some(ty) = type_at(arena, node.source, pos) {
                    return Some(ty);
                }
                if let Some(ty) = type_at(arena, node.target, pos) {
                    return Some(ty);
                }
            }
            DropClosureEnv(node) => {
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
                if let Some(ty) = app.type_at(arena, pos) {
                    return Some(ty);
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
            TakeLocalValue(_) => {}
            LoadLocal(_) => {}
            Return(node) => {
                if let Some(ty) = type_at(arena, *node, pos) {
                    return Some(ty);
                }
            }
            Block(block) => {
                for &child in block.body.iter() {
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
                if let Some(ty) = node.type_at(arena, pos) {
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
            Loop(node) => {
                if let Some(ty) = type_at(arena, node.body, pos) {
                    return Some(ty);
                }
            }
            Break(node) => {
                if let Some(ty) = type_at(arena, node.value, pos) {
                    return Some(ty);
                }
            }
            CheckCallDepth | CheckFuel | Continue(_) => {}
        }

        // No children has this position, return our type.
        Some(self.ty)
    }
}

impl Node {
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
            CloneClosureEnv(node) => {
                unbound_ty_vars(arena, node.source, result, ignore);
                unbound_ty_vars(arena, node.target, result, ignore);
            }
            DropClosureEnv(node) => unbound_ty_vars(arena, node.target, result, ignore),
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
            TakeLocalValue(_) => {}
            LoadLocal(_) => {}
            Return(node) => unbound_ty_vars(arena, *node, result, ignore),
            Block(block) => block
                .body
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
            Loop(node) => {
                unbound_ty_vars(arena, node.body, result, ignore);
            }
            Break(node) => {
                unbound_ty_vars(arena, node.value, result, ignore);
            }
            CheckCallDepth | CheckFuel | Continue(_) => {}
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
    pub body: ENodeId,
    pub locals: &'a [LocalDecl<Elaborated>],
}

impl FormatWith<ModuleEnv<'_>> for ExprDisplay<'_> {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        format_ind(&env.current.hir_arena, self.body, f, self.locals, env, 0, 0)
    }
}
