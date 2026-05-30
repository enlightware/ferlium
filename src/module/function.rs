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
    hir::function::{Function, FunctionDefinition},
    hir::{ENodeArena, ENodeId, NodeId, UNodeArena, UNodeId, function::ScriptFunction},
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

impl Default for LocalFrameSlot {
    fn default() -> Self {
        Self::from_index(0)
    }
}

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

/// Local variable declaration within a function
#[derive(Debug, Clone, new)]
pub struct LocalDecl {
    pub name: UstrSpan,
    pub mut_ty: MutType,
    pub ty: Type,
    /// Span of the type ascription (only for let), if any, and whether it is complete (i.e. not an inferred type)
    pub ty_span: Option<(Location, bool)>,
    pub scope: Location,
    /// Whether this local aliases existing storage or owns storage with lexical cleanup.
    #[new(default)]
    pub storage: LocalStorage,
    /// Slot offset within this function call's local runtime frame.
    #[new(default)]
    pub slot: LocalFrameSlot,
    /// How assignment through this local should treat the previous destination storage.
    #[new(default)]
    pub assignment_mode: LocalAssignmentMode,
    /// Clone dispatch used when initializing owned mutable-binding storage.
    #[new(default)]
    pub clone: Option<LocalClone>,
}
impl LocalDecl {
    pub fn as_fn_arg_type(&self) -> FnArgType {
        FnArgType::new(self.ty, self.mut_ty)
    }

    pub fn push_with_next_slot(locals: &mut Vec<LocalDecl>, mut local: LocalDecl) -> LocalDeclId {
        let id = LocalDeclId::from_index(locals.len());
        local.slot = LocalFrameSlot::from_index(id.as_index());
        locals.push(local);
        id
    }

    pub fn assign_sequential_slots(locals: &mut [LocalDecl]) {
        Self::assign_slots_with_prefix(locals, 0);
    }

    /// Assign slots `[prefix_count, prefix_count + locals.len())` to `locals`.
    pub fn assign_slots_with_prefix(locals: &mut [LocalDecl], prefix_count: usize) {
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

    pub fn local_drop(&self) -> Option<&LocalDrop> {
        match &self.storage {
            LocalStorage::Owned { drop } => Some(drop),
            LocalStorage::NonOwning | LocalStorage::Deferred(_) => None,
        }
    }

    pub fn local_drop_mut(&mut self) -> Option<&mut LocalDrop> {
        match &mut self.storage {
            LocalStorage::Owned { drop } => Some(drop),
            LocalStorage::NonOwning | LocalStorage::Deferred(_) => None,
        }
    }

    pub fn set_non_owning_storage(&mut self) {
        self.storage = LocalStorage::NonOwning;
        self.clone = None;
    }

    pub fn set_owned_storage(&mut self, drop: LocalDrop) {
        self.storage = LocalStorage::Owned { drop };
    }

    pub fn set_deferred_storage(&mut self, deferred: DeferredLocalStorage) {
        self.storage = LocalStorage::Deferred(deferred);
    }
}

/// Whether a local aliases existing storage, owns storage, or must wait for final inference facts.
#[derive(Debug, Clone, Default)]
pub enum LocalStorage {
    /// The local aliases existing storage and does not need lexical cleanup.
    #[default]
    NonOwning,
    /// The local owns storage that is released with the given drop mode.
    Owned { drop: LocalDrop },
    /// The local's storage mode depends on final inferred mutability.
    Deferred(DeferredLocalStorage),
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

/// How generated HIR clones into owned storage.
#[derive(Debug, Clone, Copy)]
pub enum LocalClone {
    /// Clone mode must be selected after type inference has finished.
    Unknown,
    /// Clone mode has been resolved.
    Resolved(ResolvedLocalClone),
}

/// How a local should be taken when an owned result is required.
#[derive(Debug, Clone, Copy)]
pub enum TakeLocalValueMode {
    /// Decide after local storage resolution whether taking this local moves or clones.
    Unknown,
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

/// How generated HIR drops owned storage.
#[derive(Debug, Clone, Copy)]
pub enum LocalDrop {
    /// Drop mode must be selected after type inference has finished.
    Unknown,
    /// Drop mode has been resolved.
    Resolved(ResolvedLocalDrop),
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

/// A local function inside a module.
#[derive(Debug, Clone)]
pub struct ModuleFunction {
    pub definition: FunctionDefinition,
    pub code: Function,
    pub spans: Option<ModuleFunctionSpans>,
    /// Local variable declarations for the function body, including arguments and any variables declared within the function.
    pub locals: Vec<LocalDecl>,
    pub debug_info: FunctionDebugInfo,
}
impl ModuleFunction {
    pub fn new(
        definition: FunctionDefinition,
        code: Function,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<LocalDecl>,
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

    /// Constructs a function whose debug info will be populated by a later `refresh_debug_info` call after locals have reached their final form.
    pub fn new_without_debug_info(
        definition: FunctionDefinition,
        code: Function,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<LocalDecl>,
    ) -> Self {
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

    pub fn locals_ids(&self) -> Vec<LocalDeclId> {
        (0..self.locals.len())
            .map(LocalDeclId::from_index)
            .collect()
    }

    pub fn get_code_entry(&self) -> Option<ENodeId> {
        self.code.as_script().map(|s| s.entry_node_id)
    }

    pub(crate) fn get_pending_code_entry(&self) -> Option<UNodeId> {
        self.code.as_pending_script().map(|s| s.entry_node_id)
    }

    pub(crate) fn finalize_pending_code(&mut self, entry_node_id: ENodeId) {
        let pending = self
            .code
            .as_pending_script()
            .expect("finalizing a non-pending function");
        self.code = Box::new(ScriptFunction::new(
            entry_node_id,
            pending.runtime_arg_count,
        ));
    }

    /// Span of the function definition, or synthesized if not available.
    pub fn function_span(&self) -> Location {
        self.spans
            .as_ref()
            .map_or_else(Location::new_synthesized, |s| s.span)
    }

    /// Generate, from the definition and the spans, the local variable declarations for the function arguments.
    pub fn gen_locals_no_bounds(&self) -> Vec<LocalDecl> {
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

    pub fn check_borrows_and_elaborate_hir(
        &mut self,
        src_arena: &mut UNodeArena,
        dst_arena: &mut ENodeArena,
        ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ) -> Result<ElaboratedHir, InternalCompilationError> {
        let root = self.get_pending_code_entry().unwrap();
        LocalDecl::assign_sequential_slots(&mut self.locals);
        elaborate_local_ownership_and_value_dispatches(src_arena, &mut self.locals, ctx)?;
        check_borrows(src_arena, root)?;
        let elaborated = elaborate_hir(src_arena, root, dst_arena, ctx, &self.locals)?;
        self.finalize_pending_code(elaborated.root);
        Ok(elaborated)
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
        self.code.format_ind(f, &self.locals, env, 0, 1)
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
