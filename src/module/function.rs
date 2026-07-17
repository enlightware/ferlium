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
    compiler::error::{
        InternalCompilationError, InvalidSubscriptDefinitionKind, SubscriptDefinitionSubject,
    },
    containers::b,
    define_id_type,
    format::FormatWith,
    hir::borrow_checker::{
        check_elaborated_borrows, check_elaborated_literal_invariants,
        check_elaborated_place_return_roots, check_elaborated_yield_roots,
    },
    hir::function::{
        ArgConvention, CallableDefinition, Function, PendingScriptFunction,
        arg_conventions_for_args,
    },
    hir::{
        ENodeArena, ENodeId, Elaborated, HirPhase, NodeId, UNodeArena, UNodeId, Unelaborated,
        function::ScriptFunction,
    },
    hir::{
        dictionary::DictElaborationCtx, elaboration::elaborate_hir,
        value_dispatch::elaborate_local_ownership_and_value_dispatches,
    },
    internal_compilation_error,
    module::{FunctionDebugInfo, ModuleEnv, ModuleId, id::Id},
    types::mutability::MutType,
    types::r#type::{FnArgType, Type},
};

use derive_new::new;
use ustr::Ustr;

define_id_type!(
    /// Local function ID within a module
    LocalFunctionId
);

define_id_type!(
    /// Slot offset within a function call's local runtime frame.
    LocalFrameSlot
);

/// An identifier for a function
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, new)]
pub struct FunctionId {
    /// Module owning the function.
    pub module: ModuleId,
    /// Function index within the owning module.
    pub function: LocalFunctionId,
}

impl FormatWith<ModuleEnv<'_>> for FunctionId {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        let module = if self.module == env.current.module_id() {
            env.current
        } else {
            env.modules
                .get(self.module)
                .and_then(|entry| entry.module())
                .expect("function module not found")
        };
        let name = module
            .get_function_name_by_id(self.function)
            .unwrap_or_else(|| Ustr::from("<anonymous>"));
        let module_name = env
            .modules
            .get_name(self.module)
            .map(ToString::to_string)
            .unwrap_or_else(|| format!("#{}", self.module));
        write!(f, "function {module_name}::{name} (#{})", self.function)
    }
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

/// Concrete runtime layout needed to copy a value by representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResolvedValueLayout {
    pub size: u32,
    pub align: u32,
}

impl ResolvedValueLayout {
    pub const fn native<T>() -> Self {
        Self {
            size: std::mem::size_of::<T>() as u32,
            align: std::mem::align_of::<T>() as u32,
        }
    }
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
    pub name: Option<Ustr>,
    pub subscript_member_name: Option<Ustr>,
    pub definition: CallableDefinition,
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
    pub(crate) yield_node_id: Option<UNodeId>,
}

impl PendingFunctionBody {
    pub(crate) fn new(arena: UNodeArena, entry_node_id: UNodeId) -> Self {
        Self {
            arena,
            entry_node_id,
            yield_node_id: None,
        }
    }

    pub(crate) fn with_yield_node_id(mut self, yield_node_id: Option<UNodeId>) -> Self {
        self.yield_node_id = yield_node_id;
        self
    }

    pub(crate) fn into_script_function(self, runtime_arg_count: usize) -> PendingScriptFunction {
        let mut function =
            PendingScriptFunction::new(self.arena, self.entry_node_id, runtime_arg_count);
        function.yield_node_id = self.yield_node_id;
        function
    }
}

/// A local function inside a module after HIR elaboration.
#[derive(Debug, Clone)]
pub struct ModuleFunction {
    pub definition: CallableDefinition,
    pub code: Function,
    /// High-level argument passing requirements for each visible parameter.
    ///
    /// HIR bodies set this during elaboration with the trait solver. Native/interpreter-only
    /// bodies provide it through `Callable::visible_parameter_passing`.
    pub parameter_passing: Vec<ArgConvention>,
    pub spans: Option<ModuleFunctionSpans>,
    /// Local variable declarations for the function body, including arguments and any variables declared within the function.
    pub locals: Vec<ELocalDecl>,
    pub debug_info: FunctionDebugInfo,
}

/// A module function after HIR elaboration.
pub type EModuleFunction = ModuleFunction;

fn parameter_passing_from_code(
    definition: &CallableDefinition,
    code: &Function,
) -> Vec<ArgConvention> {
    let parameter_passing = code
        .visible_parameter_passing()
        .expect("module function code should expose visible parameter passing")
        .to_vec();
    check_parameter_passing_len(definition, &parameter_passing);
    parameter_passing
}

fn check_parameter_passing_len(
    definition: &CallableDefinition,
    parameter_passing: &[ArgConvention],
) {
    let expected = definition.arg_names.len();
    assert_eq!(
        parameter_passing.len(),
        expected,
        "function has {} visible parameters but {} parameter-passing entries",
        expected,
        parameter_passing.len()
    );
}

impl PendingModuleFunction {
    pub fn new(
        definition: CallableDefinition,
        code: PendingScriptFunction,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ULocalDecl>,
    ) -> Self {
        Self::new_with_name(None, definition, code, spans, locals)
    }

    pub fn new_with_name(
        name: Option<Ustr>,
        definition: CallableDefinition,
        code: PendingScriptFunction,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ULocalDecl>,
    ) -> Self {
        Self {
            name,
            subscript_member_name: None,
            definition,
            code,
            spans,
            locals,
        }
    }

    pub(crate) fn from_body(
        definition: CallableDefinition,
        body: PendingFunctionBody,
        runtime_arg_count: usize,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ULocalDecl>,
    ) -> Self {
        Self::from_body_with_name(None, definition, body, runtime_arg_count, spans, locals)
    }

    pub(crate) fn from_body_with_name(
        name: Option<Ustr>,
        definition: CallableDefinition,
        body: PendingFunctionBody,
        runtime_arg_count: usize,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ULocalDecl>,
    ) -> Self {
        Self::new_with_name(
            name,
            definition,
            body.into_script_function(runtime_arg_count),
            spans,
            locals,
        )
    }

    pub(crate) fn with_subscript_member_name(mut self, subscript_name: Ustr) -> Self {
        self.subscript_member_name = Some(subscript_name);
        self
    }

    pub fn assign_local_slots(&mut self) {
        LocalDecl::assign_sequential_slots(&mut self.locals);
    }

    pub fn placeholder(&self) -> EModuleFunction {
        ModuleFunction::placeholder(self.definition.clone(), self.spans.clone())
    }

    pub fn check_borrows_and_elaborate_hir(
        mut self,
        dst_arena: &mut ENodeArena,
        ctx: &mut DictElaborationCtx<'_, '_, '_>,
    ) -> Result<EModuleFunction, InternalCompilationError> {
        let root = self.code.entry_node_id;
        LocalDecl::assign_sequential_slots(&mut self.locals);
        elaborate_local_ownership_and_value_dispatches(
            &mut self.code.arena,
            &mut self.locals,
            ctx,
        )?;
        // Record the source-level conventions of visible parameters for later
        // elaboration and lowering.
        let arg_count = self.definition.arg_names.len();
        let parameter_passing =
            arg_conventions_for_args(&self.definition.ty_scheme.ty.args[..arg_count]);
        let place_return_check = if self.definition.returns_place() {
            if self.code.arena[root].ty != Type::never() {
                return Err(internal_compilation_error!(InvalidSubscriptDefinition {
                    subject: self.subscript_definition_subject(),
                    kind: InvalidSubscriptDefinitionKind::AddressorMustReturnExplicitly,
                    span: self.code.arena[root].span,
                }));
            }
            let visible_arg_count = self.definition.arg_names.len();
            let base_parameter_index = if visible_arg_count == 0 {
                None
            } else {
                // This assumes runtime_arg_count includes every hidden runtime
                // local allocated before visible parameters. Dictionary/bound
                // evidence is not stored in this locals prefix today.
                Some(
                    self.code
                        .runtime_arg_count
                        .checked_sub(visible_arg_count)
                        .expect("runtime argument count should include visible arguments"),
                )
            };
            Some((base_parameter_index, self.subscript_definition_subject()))
        } else {
            None
        };
        let elaborated = elaborate_hir(&self.code.arena, root, dst_arena, ctx, self.locals)?;
        if self.code.yield_node_id.is_some() {
            check_elaborated_yield_roots(dst_arena, elaborated.root, &elaborated.locals)?;
        }
        if let Some((base_parameter_index, subject)) = place_return_check {
            check_elaborated_place_return_roots(
                dst_arena,
                elaborated.root,
                &elaborated.locals,
                base_parameter_index,
                subject,
            )?;
        }
        check_elaborated_literal_invariants(dst_arena, elaborated.root, ctx.trait_solver)?;
        check_elaborated_borrows(dst_arena, elaborated.root)?;
        let function = ModuleFunction::new_elaborated(
            self.definition,
            b(ScriptFunction {
                entry_node_id: elaborated.root,
                yield_node_id: self.code.yield_node_id.map(|node| elaborated.remap[&node]),
                runtime_arg_count: self.code.runtime_arg_count,
            }),
            parameter_passing,
            self.spans,
            elaborated.locals,
        );
        Ok(function)
    }

    fn subscript_definition_subject(&self) -> SubscriptDefinitionSubject {
        self.subscript_member_name.map_or(
            SubscriptDefinitionSubject::AddressorFunction(self.name),
            SubscriptDefinitionSubject::SubscriptMember,
        )
    }
}

impl ModuleFunction {
    pub fn new_elaborated(
        definition: CallableDefinition,
        code: Function,
        parameter_passing: Vec<ArgConvention>,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ELocalDecl>,
    ) -> Self {
        check_parameter_passing_len(&definition, &parameter_passing);
        let debug_info = FunctionDebugInfo::from_locals(&locals);
        Self {
            definition,
            code,
            parameter_passing,
            spans,
            locals,
            debug_info,
        }
    }

    pub fn new(
        definition: CallableDefinition,
        code: Function,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ULocalDecl>,
    ) -> Self {
        let locals = locals
            .into_iter()
            .map(ULocalDecl::into_elaborated)
            .collect::<Vec<_>>();
        let parameter_passing = parameter_passing_from_code(&definition, &code);
        let debug_info = FunctionDebugInfo::from_locals(&locals);
        Self {
            definition,
            code,
            parameter_passing,
            spans,
            locals,
            debug_info,
        }
    }

    /// Constructs a function whose debug info will be populated by a later `refresh_debug_info` call after locals have reached their final form.
    pub fn new_without_debug_info(
        definition: CallableDefinition,
        code: Function,
        spans: Option<ModuleFunctionSpans>,
        locals: Vec<ULocalDecl>,
    ) -> Self {
        let locals = locals
            .into_iter()
            .map(ULocalDecl::into_elaborated)
            .collect::<Vec<_>>();
        let parameter_passing = parameter_passing_from_code(&definition, &code);
        Self {
            definition,
            code,
            parameter_passing,
            spans,
            locals,
            debug_info: FunctionDebugInfo::default(),
        }
    }

    pub fn new_without_spans_nor_locals(definition: CallableDefinition, code: Function) -> Self {
        Self::new_without_debug_info(definition, code, None, Vec::new())
    }

    pub fn placeholder(definition: CallableDefinition, spans: Option<ModuleFunctionSpans>) -> Self {
        Self {
            definition,
            code: b(crate::hir::function::VoidFunction),
            // Placeholders are transient module slots installed before their
            // pending function body is elaborated and replaced.
            parameter_passing: Vec::new(),
            spans,
            locals: Vec::new(),
            debug_info: FunctionDebugInfo::default(),
        }
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
