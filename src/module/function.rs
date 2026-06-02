// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

//! Functions within a module

use crate::{
    Location,
    ast::UstrSpan,
    compiler::error::InternalCompilationError,
    containers::b,
    define_id_type,
    format::FormatWith,
    hir::borrow_checker::check_borrows,
    hir::function::{Function, FunctionDefinition, PendingScriptFunction},
    hir::{
        ENodeArena, ENodeId, Elaborated, HirPhase, NodeId, UNodeArena, UNodeId, Unelaborated,
        function::ScriptFunction,
    },
    hir::{
        dictionary::DictElaborationCtx,
        elaboration::{ElaboratedHir, elaborate_hir},
        value_dispatch::elaborate_local_ownership_and_value_dispatches,
    },
    module::{FunctionDebugInfo, ModuleEnv, ModuleId, TraitKey, format_impl_header_by_key, id::Id},
    types::mutability::MutType,
    types::r#trait::TraitMethodIndex,
    types::r#type::{FnArgType, Type},
};

use derive_new::new;
use ustr::Ustr;

define_id_type!(
    /// Local function ID within a module
    LocalFunctionId
);

define_id_type!(
    /// Import slot ID for cross-module function references
    ImportFunctionSlotId
);

define_id_type!(
    /// Slot offset within a function call's local runtime frame.
    LocalFrameSlot
);

/// An identifier for a function
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FunctionId {
    /// Local function in a module
    Local(LocalFunctionId),
    /// Imported function through an import slot
    Import(ImportFunctionSlotId),
}

impl FormatWith<ModuleEnv<'_>> for FunctionId {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        match *self {
            FunctionId::Local(id) => {
                let name = env.current.get_function_name_by_id(id).unwrap();
                write!(f, "local function {name} (#{id})")
            }
            FunctionId::Import(id) => {
                let slot = &env.current.get_import_fn_slot(id).unwrap();
                let module_id = slot.module;
                let module_name = env
                    .modules
                    .get_name(module_id)
                    .expect("imported module not found");
                write!(f, "imported function {module_name}::")?;
                let function_name = match &slot.target {
                    ImportFunctionTarget::TraitImplMethod { key, index } => {
                        let name = env.trait_def(key.trait_id()).method(*index).0;
                        let imp = env
                            .modules
                            .get(module_id)
                            .expect("imported module not found")
                            .module
                            .as_ref()
                            .expect("compiled module not found")
                            .get_impl_data_by_trait_key(key)
                            .expect("imported trait impl not found");
                        write!(f, "<")?;
                        format_impl_header_by_key(f, key, imp, env)?;
                        write!(f, ">::")?;
                        name
                    }
                    ImportFunctionTarget::NamedFunction(name) => *name,
                };
                write!(f, "{function_name} (slot #{id})")
            }
        }
    }
}

/// Target of a function import slot
#[derive(Debug, Clone)]
pub enum ImportFunctionTarget {
    /// Name of the function in the target module
    NamedFunction(Ustr),
    /// Trait method to import
    TraitImplMethod {
        /// The concrete trait implementation key
        key: TraitKey,
        /// Index of the method in the trait
        index: TraitMethodIndex,
    },
}

/// Import slot that can be resolved to a function from another module
#[derive(Debug, Clone)]
pub struct ImportFunctionSlot {
    /// ID of the module to import from
    pub module: ModuleId,
    /// The target function in that module
    pub target: ImportFunctionTarget,
}

/// A module function argument span, with the span of the optional type ascription.
pub type ModuleFunctionArgSpan = (Location, Option<(Location, bool)>);

/// If the module function is from code, this struct contains the spans of the function.
#[derive(Debug, Clone)]
pub struct ModuleFunctionSpans {
    pub name: Location,
    pub args: Vec<ModuleFunctionArgSpan>,
    pub args_span: Location,
    pub ret_ty: Option<(Location, bool)>,
    pub span: Location,
}

/// Local variable declaration within a function.
#[derive(Debug, Clone, new)]
pub struct LocalDecl<P: HirPhase = Unelaborated> {
    pub name: UstrSpan,
    pub mut_ty: MutType,
    pub ty: Type,
    /// Span of the type ascription (only for let), if any, and whether it is complete (i.e. not an inferred type)
    pub ty_span: Option<(Location, bool)>,
    pub scope: Location,
    /// Whether this local aliases existing storage or owns storage with lexical cleanup.
    #[new(default)]
    pub storage: LocalStorage<P>,
    /// Slot offset within this function call's local runtime frame.
    #[new(default)]
    pub slot: LocalFrameSlot,
    /// How assignment through this local should treat the previous destination storage.
    #[new(default)]
    pub assignment_mode: LocalAssignmentMode,
    /// Clone dispatch used when initializing owned mutable-binding storage.
    #[new(default)]
    pub clone: Option<P::LocalClone>,
}

/// A local declaration before local ownership/value elaboration.
pub type ULocalDecl = LocalDecl<Unelaborated>;

/// A local declaration after local ownership/value elaboration.
pub type ELocalDecl = LocalDecl<Elaborated>;
impl<P: HirPhase> LocalDecl<P> {
    pub fn as_fn_arg_type(&self) -> FnArgType {
        FnArgType::new(self.ty, self.mut_ty)
    }

    pub fn push_with_next_slot(
        locals: &mut Vec<LocalDecl<P>>,
        mut local: LocalDecl<P>,
    ) -> LocalDeclId {
        let id = LocalDeclId::from_index(locals.len());
        local.slot = LocalFrameSlot::from_index(id.as_index());
        locals.push(local);
        id
    }

    pub fn assign_sequential_slots(locals: &mut [LocalDecl<P>]) {
        Self::assign_slots_with_prefix(locals, 0);
    }

    /// Assign slots `[prefix_count, prefix_count + locals.len())` to `locals`.
    pub fn assign_slots_with_prefix(locals: &mut [LocalDecl<P>], prefix_count: usize) {
        for (index, local) in locals.iter_mut().enumerate() {
            local.slot = LocalFrameSlot::from_index(prefix_count + index);
        }
    }

    pub fn owns_storage(&self) -> bool {
        matches!(self.storage, LocalStorage::Owned { .. })
    }

    pub fn may_own_storage(&self) -> bool {
        matches!(
            self.storage,
            LocalStorage::Owned { .. } | LocalStorage::Deferred(_)
        )
    }

    pub fn local_drop(&self) -> Option<&P::LocalDrop> {
        match &self.storage {
            LocalStorage::Owned { drop } => Some(drop),
            LocalStorage::NonOwning | LocalStorage::Deferred(_) => None,
        }
    }

    pub fn local_drop_mut(&mut self) -> Option<&mut P::LocalDrop> {
        match &mut self.storage {
            LocalStorage::Owned { drop } => Some(drop),
            LocalStorage::NonOwning | LocalStorage::Deferred(_) => None,
        }
    }

    pub fn set_non_owning_storage(&mut self) {
        self.storage = LocalStorage::NonOwning;
        self.clone = None;
    }

    pub fn set_owned_storage(&mut self, drop: P::LocalDrop) {
        self.storage = LocalStorage::Owned { drop };
    }

    pub fn set_deferred_storage(&mut self, deferred: P::DeferredLocalStorage) {
        self.storage = LocalStorage::Deferred(deferred);
    }
}

impl LocalDecl<Unelaborated> {
    pub fn into_elaborated(self) -> LocalDecl<Elaborated> {
        LocalDecl {
            name: self.name,
            mut_ty: self.mut_ty,
            ty: self.ty,
            ty_span: self.ty_span,
            scope: self.scope,
            storage: self.storage.into_elaborated(),
            slot: self.slot,
            assignment_mode: self.assignment_mode,
            clone: self.clone.map(PendingLocalClone::into_elaborated),
        }
    }
}

/// Whether a local aliases existing storage, owns storage, or must wait for final inference facts.
#[derive(Debug, Clone, Default)]
pub enum LocalStorage<P: HirPhase = Unelaborated> {
    /// The local aliases existing storage and does not need lexical cleanup.
    #[default]
    NonOwning,
    /// The local owns storage that is released with the given drop mode.
    Owned { drop: P::LocalDrop },
    /// The local's storage mode depends on final inferred mutability.
    Deferred(P::DeferredLocalStorage),
}

impl LocalStorage<Unelaborated> {
    pub fn into_elaborated(self) -> LocalStorage<Elaborated> {
        match self {
            LocalStorage::NonOwning => LocalStorage::NonOwning,
            LocalStorage::Owned { drop } => LocalStorage::Owned {
                drop: drop.into_elaborated(),
            },
            LocalStorage::Deferred(_) => {
                panic!("deferred local storage should have been resolved before elaboration")
            }
        }
    }
}

/// Deferred storage decision for a `let` binding initialized from a place.
#[derive(Debug, Clone, Copy)]
pub struct DeferredLocalStorage {
    pub initializer: NodeId,
    pub initializer_mut_ty: MutType,
    pub binding_mutable: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LocalAssignmentMode {
    #[default]
    Overwrite,
    InitializeStorage,
}

define_id_type!(
    /// Hidden extra parameter ID within a lowered function frame.
    ExtraParameterId
);

define_id_type!(
    /// Known projection index into a tuple-like runtime value.
    ProjectionIndex
);

/// Clone dispatch before local ownership/value elaboration.
#[derive(Debug, Clone, Copy)]
pub enum PendingLocalClone {
    /// Clone mode must be selected after type inference has finished.
    Unknown,
    /// Clone mode has been resolved.
    Resolved(ResolvedLocalClone),
}

impl PendingLocalClone {
    pub fn into_elaborated(self) -> ResolvedLocalClone {
        match self {
            Self::Unknown => panic!("local clone should have been resolved before elaboration"),
            Self::Resolved(clone) => clone,
        }
    }
}

/// Formatting behavior shared by pending and elaborated clone metadata.
pub trait LocalCloneMetadata: Copy {
    fn format_label(self) -> &'static str;
}

impl LocalCloneMetadata for PendingLocalClone {
    fn format_label(self) -> &'static str {
        match self {
            Self::Unknown => "unknown mode",
            Self::Resolved(ResolvedLocalClone::TrivialCopy) => "trivial copy",
            Self::Resolved(ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_)) => {
                "Value::clone"
            }
        }
    }
}

impl LocalCloneMetadata for ResolvedLocalClone {
    fn format_label(self) -> &'static str {
        match self {
            Self::TrivialCopy => "trivial copy",
            Self::Static(_) | Self::Dictionary(_) => "Value::clone",
        }
    }
}

/// Take mode before local ownership/value elaboration.
#[derive(Debug, Clone, Copy)]
pub enum PendingTakeLocalValueMode {
    /// Decide after local storage resolution whether taking this local moves or clones.
    Unknown,
    /// Move out of an owned local.
    MoveOwned,
    /// Clone or copy from a non-owning local alias.
    CloneBorrowed(ResolvedLocalClone),
}

impl PendingTakeLocalValueMode {
    pub fn into_elaborated(self) -> ResolvedTakeLocalValueMode {
        match self {
            Self::Unknown => panic!("take-local mode should have been resolved before elaboration"),
            Self::MoveOwned => ResolvedTakeLocalValueMode::MoveOwned,
            Self::CloneBorrowed(clone) => ResolvedTakeLocalValueMode::CloneBorrowed(clone),
        }
    }
}

/// Formatting behavior shared by pending and elaborated take-local metadata.
pub trait TakeLocalValueModeMetadata: Copy {
    fn format_label(self) -> &'static str;
}

impl TakeLocalValueModeMetadata for PendingTakeLocalValueMode {
    fn format_label(self) -> &'static str {
        match self {
            Self::Unknown => "unknown",
            Self::MoveOwned => "move",
            Self::CloneBorrowed(ResolvedLocalClone::TrivialCopy) => "trivial copy",
            Self::CloneBorrowed(
                ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_),
            ) => "Value::clone",
        }
    }
}

impl TakeLocalValueModeMetadata for ResolvedTakeLocalValueMode {
    fn format_label(self) -> &'static str {
        match self {
            Self::MoveOwned => "move",
            Self::CloneBorrowed(ResolvedLocalClone::TrivialCopy) => "trivial copy",
            Self::CloneBorrowed(
                ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_),
            ) => "Value::clone",
        }
    }
}

/// How an elaborated local should be taken when an owned result is required.
#[derive(Debug, Clone, Copy)]
pub enum ResolvedTakeLocalValueMode {
    /// Move out of an owned local.
    MoveOwned,
    /// Clone or copy from a non-owning local alias.
    CloneBorrowed(ResolvedLocalClone),
}

/// Resolved implementation for a local clone/copy operation.
#[derive(Debug, Clone, Copy)]
pub enum ResolvedLocalClone {
    /// Copy a concrete `TrivialCopy` value.
    TrivialCopy,
    /// Call this concrete `Value` implementation.
    Static(FunctionId),
    /// Load the `Value` method from this hidden trait dictionary extra parameter.
    Dictionary(ExtraParameterId),
}

/// Drop dispatch before local ownership/value elaboration.
#[derive(Debug, Clone, Copy)]
pub enum PendingLocalDrop {
    /// Drop mode must be selected after type inference has finished.
    Unknown,
    /// Drop mode has been resolved.
    Resolved(ResolvedLocalDrop),
}

impl PendingLocalDrop {
    pub fn into_elaborated(self) -> ResolvedLocalDrop {
        match self {
            Self::Unknown => panic!("local drop should have been resolved before elaboration"),
            Self::Resolved(drop) => drop,
        }
    }
}

/// Resolved implementation for a local drop operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolvedLocalDrop {
    /// No semantic `Value::drop` is needed.
    Skip,
    /// Call this concrete `Value` implementation.
    Static(FunctionId),
    /// Load the `Value` method from this hidden trait dictionary extra parameter.
    Dictionary(ExtraParameterId),
}

define_id_type!(
    /// Local variable ID within a function
    LocalDeclId
);

/// A local function whose body has not yet been elaborated into final HIR.
#[derive(Debug, Clone)]
pub struct PendingModuleFunction {
    pub definition: FunctionDefinition,
    pub code: PendingScriptFunction,
    pub spans: Option<ModuleFunctionSpans>,
    /// Local variable declarations for the function body, including arguments and any variables declared within the function.
    pub locals: Vec<ULocalDecl>,
}

/// A module function before HIR elaboration.
pub type UModuleFunction = PendingModuleFunction;

/// Unelaborated HIR owned by one pending function body.
#[derive(Debug, Clone)]
pub(crate) struct PendingFunctionBody {
    pub(crate) arena: UNodeArena,
    pub(crate) entry_node_id: UNodeId,
}

impl PendingFunctionBody {
    pub(crate) fn new(arena: UNodeArena, entry_node_id: UNodeId) -> Self {
        Self {
            arena,
            entry_node_id,
        }
    }

    pub(crate) fn into_script_function(self, runtime_arg_count: usize) -> PendingScriptFunction {
        PendingScriptFunction::new(self.arena, self.entry_node_id, runtime_arg_count)
    }
}

/// A local function inside a module after HIR elaboration.
#[derive(Debug, Clone)]
pub struct ModuleFunction {
    pub definition: FunctionDefinition,
    pub code: Function,
    pub spans: Option<ModuleFunctionSpans>,
    /// Local variable declarations for the function body, including arguments and any variables declared within the function.
    pub locals: Vec<ELocalDecl>,
    pub debug_info: FunctionDebugInfo,
}

/// A module function after HIR elaboration.
pub type EModuleFunction = ModuleFunction;

impl PendingModuleFunction {
    pub fn new(
        definition: FunctionDefinition,
        code: PendingScriptFunction,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ULocalDecl>,
    ) -> Self {
        Self {
            definition,
            code,
            spans,
            locals,
        }
    }

    pub(crate) fn from_body(
        definition: FunctionDefinition,
        body: PendingFunctionBody,
        runtime_arg_count: usize,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ULocalDecl>,
    ) -> Self {
        Self::new(
            definition,
            body.into_script_function(runtime_arg_count),
            spans,
            locals,
        )
    }

    pub fn assign_local_slots(&mut self) {
        LocalDecl::assign_sequential_slots(&mut self.locals);
    }

    pub fn placeholder(&self) -> EModuleFunction {
        ModuleFunction::new_without_debug_info(
            self.definition.clone(),
            b(crate::hir::function::VoidFunction),
            self.spans.clone(),
            Vec::new(),
        )
    }

    pub fn check_borrows_and_elaborate_hir(
        mut self,
        dst_arena: &mut ENodeArena,
        ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ) -> Result<(EModuleFunction, ElaboratedHir), InternalCompilationError> {
        let root = self.code.entry_node_id;
        LocalDecl::assign_sequential_slots(&mut self.locals);
        elaborate_local_ownership_and_value_dispatches(
            &mut self.code.arena,
            &mut self.locals,
            ctx,
        )?;
        check_borrows(&self.code.arena, root)?;
        let elaborated = elaborate_hir(&self.code.arena, root, dst_arena, ctx, &self.locals)?;
        let locals = self
            .locals
            .into_iter()
            .map(ULocalDecl::into_elaborated)
            .collect();
        let function = ModuleFunction::new_elaborated(
            self.definition,
            b(ScriptFunction::new(
                elaborated.root,
                self.code.runtime_arg_count,
            )),
            self.spans,
            locals,
        );
        Ok((function, elaborated))
    }
}

impl ModuleFunction {
    pub fn new_elaborated(
        definition: FunctionDefinition,
        code: Function,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ELocalDecl>,
    ) -> Self {
        let debug_info = FunctionDebugInfo::from_locals(&locals);
        Self {
            definition,
            code,
            spans,
            locals,
            debug_info,
        }
    }

    pub fn new(
        definition: FunctionDefinition,
        code: Function,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ULocalDecl>,
    ) -> Self {
        let locals = locals
            .into_iter()
            .map(ULocalDecl::into_elaborated)
            .collect();
        Self::new_elaborated(definition, code, spans, locals)
    }

    /// Constructs a function whose debug info will be populated by a later `refresh_debug_info` call after locals have reached their final form.
    pub fn new_without_debug_info(
        definition: FunctionDefinition,
        code: Function,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ULocalDecl>,
    ) -> Self {
        let locals = locals
            .into_iter()
            .map(ULocalDecl::into_elaborated)
            .collect();
        Self {
            definition,
            code,
            spans,
            locals,
            debug_info: FunctionDebugInfo::default(),
        }
    }

    pub fn new_without_spans_nor_locals(definition: FunctionDefinition, code: Function) -> Self {
        Self::new_without_debug_info(definition, code, None, Vec::new())
    }

    pub fn refresh_debug_info(&mut self) {
        self.debug_info = FunctionDebugInfo::from_locals(&self.locals);
    }

    pub(crate) fn assign_local_slots(&mut self) {
        LocalDecl::assign_sequential_slots(&mut self.locals);
    }

    pub fn get_code_entry(&self) -> Option<ENodeId> {
        self.code.as_script().map(|s| s.entry_node_id)
    }

    /// Span of the function definition, or synthesized if not available.
    pub fn function_span(&self) -> Location {
        self.spans
            .as_ref()
            .map_or_else(Location::new_synthesized, |s| s.span)
    }

    /// Generate, from the definition and the spans, the local variable declarations for the function arguments.
    pub fn gen_locals_no_bounds(&self) -> Vec<ULocalDecl> {
        let (arg_locations, scope): (Box<dyn Iterator<Item = Location>>, Location) =
            if let Some(spans) = &self.spans {
                (b(spans.args.iter().map(|&(span, _)| span)), spans.span)
            } else {
                (
                    b(self
                        .definition
                        .arg_names
                        .iter()
                        .map(|_| Location::new_synthesized())),
                    Location::new_synthesized(),
                )
            };
        self.definition.gen_locals_no_bounds(arg_locations, scope)
    }

    pub(crate) fn fmt_code(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
    ) -> std::fmt::Result {
        let requirements = self
            .definition
            .ty_scheme
            .extra_parameters(*env)
            .requirements;
        let requirement_count = requirements.len();
        if requirement_count > 0 {
            writeln!(
                f,
                "⎸ {requirement_count} extra argument{} for dictionaries: {}",
                if requirement_count == 1 { "" } else { "s" },
                requirements.format_with(env)
            )?;
        }
        self.fmt_code_ind(f, env, 0, 1)
    }

    pub(crate) fn fmt_code_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
        self.code.format_ind(f, &self.locals, env, spacing, indent)
    }
}

impl FormatWith<ModuleEnv<'_>> for (&ModuleFunction, Ustr) {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        self.0
            .definition
            .fmt_with_name_and_module_env(f, self.1, "", env)?;
        writeln!(f)?;
        self.0.fmt_code(f, env)
    }
}
