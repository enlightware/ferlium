// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    any::type_name,
    fmt::{self, Debug},
    hash::DefaultHasher,
    mem, ptr,
};

use derive_new::new;
use dyn_clone::DynClone;
use ustr::Ustr;

use super::native_functions::{NativeEntry, NativeResultKnowledge};
use crate::{
    Location,
    ast::{Attribute, MetaItem, UstrSpan},
    compiler::error::SourceFailureKind,
    eval::{
        ControlFlow, EvalControlFlowResult, EvalCtx, PlaceResult, RuntimeError, ValOrMut, cont,
        drop_frame_owned_locals_on_error, eval_node_with_ctx,
    },
    format::{FormatWith, escape_identifier, format_generic_param_list, write_identifier},
    hir::{
        self, ENodeId, UNodeArena, UNodeId,
        value::{LiteralNativeValue, LiteralValue, Value, ValueRef},
    },
    module::{ELocalDecl, ModuleEnv, ProjectionIndex, ULocalDecl},
    std::{math::Float, string::StaticStr},
    types::{
        r#type::{
            CallImplType, CallResultConvention, FnArgType, FnType, Type,
            fmt_call_impl_type_with_arg_names,
        },
        type_like::TypeLike,
        type_mapper::TypeMapper,
        type_scheme::{PubTypeConstraint, TypeScheme},
        type_visitor::TypeInnerVisitor,
    },
};

pub(crate) struct FunctionDisplayContext<'a, 'm> {
    module_env: &'a ModuleEnv<'m>,
    generic_effect_params: &'a [UstrSpan],
}

impl<'a, 'm> FunctionDisplayContext<'a, 'm> {
    pub(crate) fn new(
        module_env: &'a ModuleEnv<'m>,
        generic_effect_params: &'a [UstrSpan],
    ) -> Self {
        Self {
            module_env,
            generic_effect_params,
        }
    }
}

/// The definition of a function, to be used in modules, traits and IDEs.
#[derive(Debug, Clone)]
pub struct CallableDefinition {
    pub ty_scheme: TypeScheme<FnType>,
    pub result_convention: CallResultConvention,
    /// For an `AddressorPlace` native, which **visible argument** the place it returns points into.
    ///
    /// An index into `arg_names` and `ty_scheme`'s argument list, deliberately not a MIR parameter
    /// index: MIR counts hidden evidence first, so the two differ for any callable that takes a
    /// dictionary. They happen to coincide for every std native today — no std native takes a
    /// dictionary — and depending on that silently is how a local index without its context becomes
    /// a bug.
    ///
    /// Only natives set this. A function with a MIR body has it *derived* from that body instead
    /// (`mir::pass::provenance`), which is both cheaper to keep true and checkable; a native
    /// computes its address in Rust, so the fact has nowhere to be derived from and is asserted
    /// here. `None` means "not stated", which every consumer reads as unknown.
    pub result_rooted_in: Option<u32>,
    /// Whether a native `AddressorPlace` call is a repeatable address computation.
    ///
    /// A repeatable addressor neither reads nor writes the external environment, does not mutate
    /// its visible arguments before returning, and selects the same place for identical inputs
    /// until their structural storage changes. This is independent of `result_rooted_in`, but a
    /// consumer needs both facts to reuse the returned address and invalidate it soundly. Script
    /// addressors have both properties derived from their MIR body; a native has no body to
    /// inspect, so it must assert them explicitly.
    pub repeatable_addressor: bool,
    /// Adapter-derived result domain; it does not imply effects or laws about the arguments.
    pub(crate) native_result_knowledge: NativeResultKnowledge,
    pub generic_params: Vec<UstrSpan>,
    pub generic_effect_params: Vec<UstrSpan>,
    pub arg_names: Vec<Ustr>,
    pub doc: Option<String>,
    pub attributes: Vec<Attribute>,
}

impl CallableDefinition {
    /// Values guaranteed by a native adapter on normal return. Third-party hosts obtain this
    /// metadata through typed constructors such as `from_rust_ordering_code`.
    pub fn native_result_knowledge(&self) -> NativeResultKnowledge {
        self.native_result_knowledge
    }

    /// Whether this source function carries the optimizer-control attribute `#[inline(never)]`.
    ///
    /// The syntax is validated while functions are emitted. Keeping the query on the retained HIR
    /// definition lets MIR passes resolve it through a callee `FunctionId` without copying source
    /// annotations into every MIR body.
    pub(crate) fn is_inline_never(&self) -> bool {
        self.attributes.iter().any(|attribute| {
            attribute.path.0 == "inline"
                && matches!(
                    attribute.items.as_slice(),
                    [MetaItem::Flag(value)] if value.0 == "never"
                )
        })
    }

    pub fn new(ty_scheme: TypeScheme<FnType>, arg_names: Vec<Ustr>, doc: Option<String>) -> Self {
        Self {
            ty_scheme,
            result_convention: CallResultConvention::Value,
            result_rooted_in: None,
            repeatable_addressor: false,
            native_result_knowledge: NativeResultKnowledge::Unknown,
            generic_params: vec![],
            generic_effect_params: vec![],
            arg_names,
            doc,
            attributes: vec![],
        }
    }

    pub fn new_with_generic_params(
        ty_scheme: TypeScheme<FnType>,
        generic_params: Vec<UstrSpan>,
        arg_names: Vec<Ustr>,
        doc: Option<String>,
    ) -> Self {
        Self {
            ty_scheme,
            result_convention: CallResultConvention::Value,
            result_rooted_in: None,
            repeatable_addressor: false,
            native_result_knowledge: NativeResultKnowledge::Unknown,
            generic_params,
            generic_effect_params: vec![],
            arg_names,
            doc,
            attributes: vec![],
        }
    }

    pub fn new_with_generic_params_and_attributes(
        ty_scheme: TypeScheme<FnType>,
        generic_params: Vec<UstrSpan>,
        generic_effect_params: Vec<UstrSpan>,
        arg_names: Vec<Ustr>,
        doc: Option<String>,
        attributes: Vec<Attribute>,
    ) -> Self {
        Self {
            ty_scheme,
            result_convention: CallResultConvention::Value,
            result_rooted_in: None,
            repeatable_addressor: false,
            native_result_knowledge: NativeResultKnowledge::Unknown,
            generic_params,
            generic_effect_params,
            arg_names,
            doc,
            attributes,
        }
    }

    pub fn new_infer_quantifiers<'s>(
        fn_ty: FnType,
        arg_names: impl IntoIterator<Item = &'s str>,
        doc: &str,
    ) -> Self {
        let arg_names = arg_names.into_iter().map(Ustr::from).collect();
        CallableDefinition {
            ty_scheme: TypeScheme::new_infer_quantifiers(fn_ty),
            result_convention: CallResultConvention::Value,
            result_rooted_in: None,
            repeatable_addressor: false,
            native_result_knowledge: NativeResultKnowledge::Unknown,
            generic_params: vec![],
            generic_effect_params: vec![],
            arg_names,
            doc: Some(String::from(doc)),
            attributes: vec![],
        }
    }

    pub fn new_infer_quantifiers_with_constraints<'s>(
        fn_ty: FnType,
        constraints: impl Into<Vec<PubTypeConstraint>>,
        arg_names: impl IntoIterator<Item = &'s str>,
        doc: &str,
    ) -> Self {
        let arg_names = arg_names.into_iter().map(Ustr::from).collect();
        CallableDefinition {
            ty_scheme: TypeScheme::new_infer_quantifiers_with_constraints(
                fn_ty,
                constraints.into(),
            ),
            result_convention: CallResultConvention::Value,
            result_rooted_in: None,
            repeatable_addressor: false,
            native_result_knowledge: NativeResultKnowledge::Unknown,
            generic_params: vec![],
            generic_effect_params: vec![],
            arg_names,
            doc: Some(String::from(doc)),
            attributes: vec![],
        }
    }

    pub fn return_convention(&self) -> CallResultConvention {
        self.result_convention
    }

    pub fn returns_place(&self) -> bool {
        self.return_convention().returns_place()
    }

    pub fn with_result_convention(mut self, result_convention: CallResultConvention) -> Self {
        self.result_convention = result_convention;
        self
    }

    /// Declares which visible argument the returned place points into, for a native whose address
    /// computation MIR cannot see.
    pub fn with_result_rooted_in(mut self, argument: u32) -> Self {
        assert_eq!(
            self.result_convention,
            CallResultConvention::ADDRESSOR_PLACE,
            "only an AddressorPlace callable can return a caller-rooted place"
        );
        assert!(
            (argument as usize) < self.arg_names.len(),
            "addressor result root must name a visible argument"
        );
        self.result_rooted_in = Some(argument);
        self
    }

    /// Declares that this native addressor only computes and returns its address.
    pub fn with_repeatable_addressor(mut self) -> Self {
        assert_eq!(
            self.result_convention,
            CallResultConvention::ADDRESSOR_PLACE,
            "only an AddressorPlace callable can be a repeatable addressor"
        );
        assert!(
            self.result_rooted_in.is_some(),
            "a repeatable native addressor must first declare its result root"
        );
        self.repeatable_addressor = true;
        self
    }

    /// The signature of the callable is the type scheme, result convention, and argument names.
    /// Strictly speaking, the argument names are not part of the signature,
    /// but we assume that the semantics of the callable changes if they are changed.
    pub fn signature(&self) -> (&TypeScheme<FnType>, CallResultConvention, &[Ustr]) {
        (&self.ty_scheme, self.result_convention, &self.arg_names)
    }

    /// Get a hash of the function signature for quick comparison of interfaces.
    pub fn signature_hash(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        self.signature().hash(&mut hasher);
        hasher.finish()
    }

    /// Generate the local variable declarations for the function arguments.
    pub fn gen_locals_no_bounds(
        &self,
        arg_spans: impl Iterator<Item = Location>,
        scope: Location,
    ) -> Vec<ULocalDecl> {
        let mut locals = self
            .ty_scheme
            .ty
            .args
            .iter()
            .zip(self.arg_names.iter().copied().zip(arg_spans))
            .map(|(arg, name)| ULocalDecl::new(name, arg.mut_ty, arg.ty, None, scope))
            .collect::<Vec<_>>();
        ULocalDecl::assign_sequential_slots(&mut locals);
        locals
    }

    pub fn fmt_with_name_and_module_env(
        &self,
        f: &mut fmt::Formatter,
        name: Ustr,
        prefix: &str,
        env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        let context = FunctionDisplayContext::new(env, &self.generic_effect_params);
        self.fmt_with_name_and_display_context(f, name, prefix, &context)
    }

    pub(crate) fn fmt_with_name_and_display_context(
        &self,
        f: &mut fmt::Formatter,
        name: Ustr,
        prefix: &str,
        context: &FunctionDisplayContext<'_, '_>,
    ) -> fmt::Result {
        if let Some(doc) = &self.doc {
            for line in doc.split("\n") {
                writeln!(f, "{prefix}/// {line}")?;
            }
        }
        write!(f, "{prefix}fn ")?;
        write_identifier(f, name.as_str())?;
        let ty_var_names = self
            .ty_scheme
            .display_ty_var_names_with_source_params(&self.generic_params);
        let eff_var_names = self
            .ty_scheme
            .display_eff_var_names_with_source_params(context.generic_effect_params);
        let type_quantifiers = self
            .ty_scheme
            .display_ty_quantifiers_with_source_params(&self.generic_params)
            .into_iter()
            .map(|q| {
                ty_var_names
                    .get(&q)
                    .map_or_else(|| format!("{q}"), |name| escape_identifier(name.as_str()))
            })
            .collect::<Vec<_>>();
        let effect_quantifiers = self
            .ty_scheme
            .display_eff_quantifiers_with_source_params(context.generic_effect_params)
            .into_iter()
            .map(|q| {
                eff_var_names
                    .get(&q)
                    .map_or_else(|| format!("{q}"), |name| escape_identifier(name.as_str()))
            })
            .collect::<Vec<_>>();
        if let Some(generic_params) =
            format_generic_param_list(&type_quantifiers, &effect_quantifiers)
        {
            write!(f, "{generic_params}")?;
        }
        let type_env = self
            .ty_scheme
            .type_display_env(context.module_env, &ty_var_names)
            .with_eff_var_names(&eff_var_names);
        fmt_call_impl_type_with_arg_names(
            &CallImplType::new(self.ty_scheme.ty.clone(), self.result_convention),
            &self.arg_names,
            f,
            &type_env,
        )?;
        if !self.ty_scheme.is_just_type_and_effects() {
            write!(f, " ")?;
            self.ty_scheme
                .format_constraints_with_type_env(f, &type_env)
        } else {
            Ok(())
        }
    }
}

impl TypeLike for CallableDefinition {
    fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
        self.ty_scheme.visit(visitor);
    }

    fn map(&self, f: &mut impl TypeMapper) -> Self {
        CallableDefinition {
            ty_scheme: self.ty_scheme.map(f),
            result_convention: self.result_convention,
            result_rooted_in: self.result_rooted_in,
            repeatable_addressor: self.repeatable_addressor,
            native_result_knowledge: self.native_result_knowledge,
            generic_params: self.generic_params.clone(),
            generic_effect_params: self.generic_effect_params.clone(),
            arg_names: self.arg_names.clone(),
            doc: self.doc.clone(),
            attributes: self.attributes.clone(),
        }
    }
}

impl FormatWith<ModuleEnv<'_>> for (&CallableDefinition, Ustr) {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        self.0.fmt_with_name_and_module_env(f, self.1, "", env)?;
        Ok(())
    }
}

type CallCtx<'a> = EvalCtx<'a>;

/// A function that can be called
pub trait Callable: DynClone {
    /// Native entry address and ABI contract, when available.
    ///
    /// Backend lowering retains the contract; runtime linking resolves the address.
    /// Interpreter-only callbacks provide no native entry.
    fn native_entry(&self) -> Option<&NativeEntry> {
        None
    }
    /// Execute a script or host callback. Compiler intrinsics are dispatched by `EvalCtx`
    /// before this hook and provide only callable metadata.
    fn call(
        &self,
        args: Vec<ValOrMut>,
        _ctx: &mut CallCtx,
        locals: &[ELocalDecl],
    ) -> EvalControlFlowResult;
    fn as_script(&self) -> Option<&ScriptFunction> {
        // Default implementation, which is reimplemented in `ScriptFunction`.
        None
    }
    /// Passing convention for the runtime adapter argument vector, including hidden evidence.
    fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
        None
    }
    /// Passing convention for source-visible callee parameters only.
    fn visible_parameter_passing(&self) -> Option<&[ArgConvention]> {
        self.runtime_argument_passing()
    }
    /// Concrete Rust payload type written by an output-last native optional-result entry.
    ///
    /// The Ferlium result convention is deliberately not duplicated here. Registration and
    /// physical lowering derive it from the result type's resolved `Repr` and verify that this
    /// payload type matches its `Some((T,))` member.
    fn native_optional_payload_type(&self) -> Option<Type> {
        None
    }
    fn as_script_mut(&mut self) -> Option<&mut ScriptFunction> {
        // Default implementation, which is reimplemented in `ScriptFunction`.
        None
    }

    fn into_script(self: Box<Self>) -> Option<ScriptFunction> {
        // Default implementation, which is reimplemented in `ScriptFunction`.
        None
    }

    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        locals: &[ELocalDecl],
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result;
}

impl Debug for dyn Callable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn @ {self:p}")
    }
}

dyn_clone::clone_trait_object!(Callable);

/// Owns prepared call arguments until they are borrowed or transferred into a frame.
pub(super) struct CallArgsStorageGuard {
    pub(super) args: Vec<ValOrMut>,
}

impl CallArgsStorageGuard {
    pub(super) fn new(args: Vec<ValOrMut>) -> Self {
        Self { args }
    }

    fn into_vec(mut self) -> Vec<ValOrMut> {
        mem::take(&mut self.args)
    }
}

impl Drop for CallArgsStorageGuard {
    fn drop(&mut self) {
        for arg in self.args.drain(..) {
            arg.discard_storage();
        }
    }
}

// Function access types

pub type Function = Box<dyn Callable>;

/// The semantic access convention of a call argument.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArgConvention {
    /// Give the callee exclusive mutable access to the argument place.
    MutableRef,
    /// Give the callee immutable, non-escaping access for the duration of the call.
    Let,
}

/// Formatting behavior for call-argument metadata.
pub trait CallArgConventionMetadata: Copy {
    fn format_label(self) -> &'static str;
}

impl CallArgConventionMetadata for ArgConvention {
    fn format_label(self) -> &'static str {
        match self {
            Self::MutableRef => "by mut",
            Self::Let => "by let",
        }
    }
}

fn arg_convention_for_arg(arg: &FnArgType) -> ArgConvention {
    if arg
        .mut_ty
        .as_resolved()
        .is_some_and(|mut_ty| mut_ty.is_mutable())
    {
        ArgConvention::MutableRef
    } else {
        ArgConvention::Let
    }
}

pub fn arg_conventions_for_args(args: &[FnArgType]) -> Vec<ArgConvention> {
    args.iter().map(arg_convention_for_arg).collect()
}

/// An empty dummy function returning (), used as placeholder
#[derive(Clone)]
pub struct VoidFunction;

impl Callable for VoidFunction {
    fn call(
        &self,
        _args: Vec<ValOrMut>,
        _ctx: &mut CallCtx,
        _locals: &[ELocalDecl],
    ) -> EvalControlFlowResult {
        Ok(ControlFlow::Continue(Value::unit()))
    }

    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        _locals: &[ELocalDecl],
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        write!(f, "{indent_str}VoidFunction")
    }
}

/// A function holding user-defined code.
#[derive(Debug, Clone, new)]
pub struct ScriptFunction {
    /// Entry node for normal function execution.
    pub entry_node_id: ENodeId,
    /// Suspension node for yielded-once functions, if the body yields a place.
    #[new(default)]
    pub yield_node_id: Option<ENodeId>,
    /// Number of ordinary runtime arguments expected by this body.
    ///
    /// This includes closure-environment slots prepended when calling a function value, but not
    /// dictionary/evidence parameters, which are passed separately through the extra-parameter frame.
    pub runtime_arg_count: usize,
    // pub monomorphised: HashMap<Vec<Type>, hir::Node>,
}

impl Callable for ScriptFunction {
    fn call(
        &self,
        args: Vec<ValOrMut>,
        ctx: &mut CallCtx,
        locals_arg: &[ELocalDecl],
    ) -> EvalControlFlowResult {
        let args = CallArgsStorageGuard::new(args);
        let arg_count = args.args.len();
        #[cfg(debug_assertions)]
        if args.args.len() != self.runtime_arg_count {
            eprintln!(
                "BUG\ngot {} runtime args: {:?}\nexpected {}",
                args.args.len(),
                args.args,
                self.runtime_arg_count,
            );
        }
        assert_eq!(args.args.len(), self.runtime_arg_count);
        let arena = &ctx
            .compiler_session()
            .expect_fresh_module(ctx.module_id)
            .hir_arena;
        if ctx.environment.len().saturating_add(arg_count) > ctx.environment_cell_limit {
            return Err(ctx.environment_cell_limit_error(Some(arena[self.entry_node_id].span)));
        }

        let old_frame_base = ctx.frame_base;
        ctx.frame_base = ctx.environment.len();
        ctx.environment.extend(args.into_vec());
        ctx.call_depth += 1;

        let ret = match eval_node_with_ctx(arena, self.entry_node_id, ctx, locals_arg) {
            Ok(ret) => Ok(ret),
            Err(error) => Err(ctx.cleanup_after_error(error, |ctx| {
                drop_frame_owned_locals_on_error(ctx, locals_arg, arena[self.entry_node_id].span)
            })),
        };

        ctx.call_depth -= 1;
        if ret.is_ok() {
            let expected_len = ctx.frame_base + arg_count;
            if ctx.environment.len() > expected_len
                && ctx.environment[expected_len..]
                    .iter()
                    .all(|entry| matches!(entry, ValOrMut::Val(Value::Uninit)))
            {
                ctx.truncate_environment_storage(expected_len);
            }
            assert_eq!(ctx.environment.len(), expected_len);
        }
        ctx.truncate_environment_storage(ctx.frame_base);
        ctx.frame_base = old_frame_base;

        let ret = ret?;
        // Convert Return to Continue at function boundary
        // (return statements should only escape the current function, not propagate to callers)
        Ok(ControlFlow::Continue(ret.into_value()))
    }
    fn as_script(&self) -> Option<&ScriptFunction> {
        Some(self)
    }
    fn as_script_mut(&mut self) -> Option<&mut ScriptFunction> {
        Some(self)
    }
    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        locals: &[ELocalDecl],
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result {
        hir::format_ind(
            &env.current.hir_arena,
            self.entry_node_id,
            f,
            locals,
            env,
            spacing,
            indent,
        )
    }
}

/// A script function emitted before HIR elaboration has been finalized.
#[derive(Debug, Clone)]
pub struct PendingScriptFunction {
    pub arena: UNodeArena,
    /// Entry node for normal function execution.
    pub entry_node_id: UNodeId,
    /// Suspension node for yielded-once functions, if the body yields a place.
    pub yield_node_id: Option<UNodeId>,
    /// Runtime arity to preserve while the entry node still points into the unelaborated arena.
    pub runtime_arg_count: usize,
}

impl PendingScriptFunction {
    pub fn new(arena: UNodeArena, entry_node_id: UNodeId, runtime_arg_count: usize) -> Self {
        Self {
            arena,
            entry_node_id,
            yield_node_id: None,
            runtime_arg_count,
        }
    }

    pub fn new_with_yield(
        arena: UNodeArena,
        entry_node_id: UNodeId,
        yield_node_id: UNodeId,
        runtime_arg_count: usize,
    ) -> Self {
        Self {
            arena,
            entry_node_id,
            yield_node_id: Some(yield_node_id),
            runtime_arg_count,
        }
    }
}

impl PartialEq for Box<ScriptFunction> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.as_ref(), other.as_ref())
    }
}

impl Eq for Box<ScriptFunction> {}

/// Compiler-generated addressor for a structural projection with a fixed field index.
#[derive(Debug, Clone)]
pub struct StructuralFieldAddressor {
    index: ProjectionIndex,
    runtime_argument_passing: Vec<ArgConvention>,
}

impl StructuralFieldAddressor {
    pub fn new(index: ProjectionIndex, hidden_argument_count: usize) -> Self {
        let mut runtime_argument_passing = vec![ArgConvention::Let; hidden_argument_count];
        runtime_argument_passing.push(ArgConvention::MutableRef);
        Self {
            index,
            runtime_argument_passing,
        }
    }
}

impl Callable for StructuralFieldAddressor {
    fn call(
        &self,
        mut args: Vec<ValOrMut>,
        _ctx: &mut CallCtx,
        _locals: &[ELocalDecl],
    ) -> EvalControlFlowResult {
        debug_assert_eq!(args.len(), self.runtime_argument_passing.len());
        let receiver = args.pop().expect("structural field receiver should exist");
        debug_assert!(
            args.iter()
                .all(|argument| matches!(argument, ValOrMut::Dictionary(_))),
            "structural layout evidence must consist of Value dictionaries"
        );
        let mut place = match receiver {
            ValOrMut::Mut(place) => place,
            ValOrMut::Val(value) => {
                value.discard_storage();
                return Err(RuntimeError::new_native(
                    SourceFailureKind::InvalidArgument("structural projection receiver".into()),
                ));
            }
            ValOrMut::Ref(_) | ValOrMut::Dictionary(_) => {
                return Err(RuntimeError::new_native(
                    SourceFailureKind::InvalidArgument("structural projection receiver".into()),
                ));
            }
        };
        place.push_index(
            isize::try_from(self.index.as_u32())
                .expect("structural projection index fits the interpreter place path"),
        );
        cont(Value::native(PlaceResult::new(place)))
    }

    fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
        Some(&self.runtime_argument_passing)
    }

    fn visible_parameter_passing(&self) -> Option<&[ArgConvention]> {
        Some(&self.runtime_argument_passing[self.runtime_argument_passing.len() - 1..])
    }

    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        _locals: &[ELocalDecl],
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        write!(f, "{}structural field addressor {}", indent_str, self.index)
    }
}

pub(crate) mod trivial_copy_private {
    pub trait Sealed {}
}

/// Marker for native Rust values whose representation can be copied to produce
/// a semantically independent Ferlium value. Physical argument passing is a
/// separate target-ABI decision.
///
/// # Safety
///
/// Implementors must be concrete, non-generic native types whose copied
/// representation is a valid independent value in Ferlium native adapters.
pub unsafe trait NativeTrivialCopy: Copy + 'static + trivial_copy_private::Sealed {}

impl trivial_copy_private::Sealed for () {}
unsafe impl NativeTrivialCopy for () {}
impl trivial_copy_private::Sealed for bool {}
unsafe impl NativeTrivialCopy for bool {}
impl trivial_copy_private::Sealed for isize {}
unsafe impl NativeTrivialCopy for isize {}
impl trivial_copy_private::Sealed for Float {}
unsafe impl NativeTrivialCopy for Float {}

fn literal_of_trivial_copy_native_typed<T: NativeTrivialCopy + LiteralNativeValue>(
    value: ValueRef<'_>,
) -> Option<LiteralValue> {
    value
        .as_primitive_ty::<T>()
        .map(|value| LiteralValue::new_native(*value))
}

/// Freeze one of the boxed interpreter's native `TrivialCopy` representations into the immutable
/// literal form a MIR constant pool holds.
///
/// A boxed native is a `dyn NativeValue`, which carries no way to recover its
/// Rust type, so this is a downcast chain over the sealed opt-ins above rather
/// than a cast. Keeping the chain beside them makes adding a native leaf a
/// single Rust-side change. Language-level trait registration remains explicit
/// in the standard module.
///
/// This is the leaf half of reifying a compile-time value into MIR (see `src/mir/reify.rs`), and
/// the inverse of [`LiteralValue::into_value`].
pub(crate) fn literal_of_trivial_copy_native<'a>(
    value: impl Into<ValueRef<'a>>,
) -> Option<LiteralValue> {
    let value = value.into();
    literal_of_trivial_copy_native_typed::<()>(value)
        .or_else(|| literal_of_trivial_copy_native_typed::<bool>(value))
        .or_else(|| literal_of_trivial_copy_native_typed::<isize>(value))
        .or_else(|| literal_of_trivial_copy_native_typed::<Float>(value))
        .or_else(|| literal_of_trivial_copy_native_typed::<StaticStr>(value))
}

/// Copy one of the boxed interpreter's native `TrivialCopy` representations.
///
/// Copying such a leaf *is* freezing it and thawing it again: both rebuild the same concrete Rust
/// value into a fresh box, and `into_value` reuses the box the freeze allocated. Defining it that
/// way keeps one downcast chain for the sealed set instead of two that can drift apart.
pub(crate) fn copy_boxed_trivial_copy_native<'a>(value: impl Into<ValueRef<'a>>) -> Option<Value> {
    literal_of_trivial_copy_native(value).map(LiteralValue::into_value)
}

pub fn extract_trivial_native_input<T: NativeTrivialCopy>(
    arg: &ValOrMut,
    ctx: &mut CallCtx,
) -> Result<T, SourceFailureKind> {
    match arg.as_primitive::<T>(ctx)? {
        Some(value) => Ok(*value),
        None => panic!(
            "Expected a primitive of type {}, found {}",
            type_name::<T>(),
            arg.format_with(ctx)
        ),
    }
}

pub fn extract_native_ref<'m, T: 'static>(
    arg: &'m ValOrMut,
    ctx: &'m mut CallCtx,
) -> Result<&'m T, SourceFailureKind> {
    match arg.as_primitive::<T>(ctx)? {
        Some(value) => Ok(value),
        None => panic!(
            "Expected a primitive of type {}, found {}",
            type_name::<T>(),
            arg.format_with(ctx)
        ),
    }
}

#[cfg(test)]
mod tests {
    use std::{
        mem::size_of,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use super::*;
    use crate::{
        CompilerSession,
        eval::ControlFlow,
        hir::{CallArgument, Elaborated, native_functions::NativeFnR, value::NativeValueType},
        module::{ModuleId, id::Id},
    };

    static NATIVE_ARG_DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[derive(Debug)]
    struct NativeArgDropTracked;

    impl NativeValueType for NativeArgDropTracked {}

    impl Drop for NativeArgDropTracked {
        fn drop(&mut self) {
            NATIVE_ARG_DROP_COUNT.fetch_add(1, Ordering::Relaxed);
        }
    }

    extern "C" fn observe_value(_: &NativeArgDropTracked) {}

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn argument_convention_stays_compact() {
        assert_eq!(
            size_of::<ArgConvention>(),
            1,
            "ArgConvention should remain a compact semantic classification"
        );
        assert_eq!(
            size_of::<CallArgument<Elaborated>>(),
            8,
            "CallArgument should remain one compact node ID plus its convention"
        );
    }

    #[test]
    fn native_adapter_discards_owned_argument_storage() {
        NATIVE_ARG_DROP_COUNT.store(0, Ordering::Relaxed);
        let session = CompilerSession::new();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        let function = NativeFnR::new(observe_value);

        let result = function
            .call(
                vec![ValOrMut::Val(Value::native(NativeArgDropTracked))],
                &mut ctx,
                &[],
            )
            .unwrap();
        let ControlFlow::Continue(value) = result else {
            panic!("native test function should not return early");
        };
        value.discard_storage();

        assert_eq!(NATIVE_ARG_DROP_COUNT.load(Ordering::Relaxed), 1);
    }
}
