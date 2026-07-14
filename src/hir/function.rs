// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    fmt::{self, Debug},
    hash::DefaultHasher,
    marker::PhantomData,
};

use dyn_clone::DynClone;

use derive_new::new;
use ustr::Ustr;

use ferlium_macros::declare_native_fn_aliases;

use crate::{
    Location,
    ast::{Attribute, UstrSpan},
    compiler::error::RuntimeErrorKind,
    eval::{
        ControlFlow, EvalControlFlowResult, EvalCtx, PlaceResult, RuntimeError, ValOrMut,
        ValOrMutArgs, cont, drop_frame_owned_locals_on_error, eval_node_with_ctx,
    },
    format::{FormatWith, escape_identifier, format_generic_param_list, write_identifier},
    hir::value::{NativeValue, Value},
    hir::{self, ENodeId, UNodeArena, UNodeId},
    module::{ELocalDecl, ModuleEnv, ModuleFunction, ULocalDecl},
    types::effects::EffType,
    types::r#type::{
        CallImplType, CallResultConvention, FnArgType, FnType, Type,
        fmt_call_impl_type_with_arg_names,
    },
    types::type_like::TypeLike,
    types::type_mapper::TypeMapper,
    types::type_scheme::{PubTypeConstraint, TypeScheme},
    types::type_visitor::TypeInnerVisitor,
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
    pub generic_params: Vec<UstrSpan>,
    pub generic_effect_params: Vec<UstrSpan>,
    pub arg_names: Vec<Ustr>,
    pub doc: Option<String>,
    pub attributes: Vec<Attribute>,
}

impl CallableDefinition {
    pub fn new(ty_scheme: TypeScheme<FnType>, arg_names: Vec<Ustr>, doc: Option<String>) -> Self {
        Self {
            ty_scheme,
            result_convention: CallResultConvention::Value,
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
            generic_params: self.generic_params.clone(),
            generic_effect_params: self.generic_effect_params.clone(),
            arg_names: self.arg_names.clone(),
            doc: self.doc.clone(),
            attributes: self.attributes.clone(),
        }
    }
}

impl FormatWith<ModuleEnv<'_>> for (&CallableDefinition, Ustr) {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        self.0.fmt_with_name_and_module_env(f, self.1, "", env)?;
        Ok(())
    }
}

type CallCtx<'a> = EvalCtx<'a>;

/// A function that can be called
pub trait Callable: DynClone {
    fn call(
        &self,
        args: Vec<ValOrMut>,
        _ctx: &mut CallCtx,
        locals: &[ELocalDecl],
    ) -> EvalControlFlowResult;
    fn as_script(&self) -> Option<&ScriptFunction> {
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
    fn as_script_mut(&mut self) -> Option<&mut ScriptFunction> {
        None
    }
    fn into_script(self: Box<Self>) -> Option<ScriptFunction> {
        None
    }
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        locals: &[ELocalDecl],
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result;
}

impl Debug for dyn Callable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn @ {self:p}")
    }
}

dyn_clone::clone_trait_object!(Callable);

/// Owns prepared call arguments until they are borrowed or transferred into a frame.
struct CallArgsStorageGuard {
    args: Vec<ValOrMut>,
}

impl CallArgsStorageGuard {
    fn new(args: Vec<ValOrMut>) -> Self {
        Self { args }
    }

    fn iter(&self) -> std::slice::Iter<'_, ValOrMut> {
        self.args.iter()
    }

    fn into_vec(mut self) -> Vec<ValOrMut> {
        std::mem::take(&mut self.args)
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
        f: &mut std::fmt::Formatter,
        _locals: &[ELocalDecl],
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
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
        if ctx.environment.len().saturating_add(arg_count) > ctx.stack_limit {
            return Err(RuntimeError::new(
                RuntimeErrorKind::StackLimitExceeded {
                    limit: ctx.stack_limit,
                },
                Some(arena[self.entry_node_id].span),
            ));
        }

        let old_frame_base = ctx.frame_base;
        ctx.frame_base = ctx.environment.len();
        ctx.environment.extend(args.into_vec());
        ctx.call_depth += 1;

        let ret = eval_node_with_ctx(arena, self.entry_node_id, ctx, locals_arg);
        let cleanup = if ret.is_err() {
            drop_frame_owned_locals_on_error(ctx, locals_arg, arena[self.entry_node_id].span)
        } else {
            Ok(())
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

        cleanup?;
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
        f: &mut std::fmt::Formatter,
        locals: &[ELocalDecl],
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
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
        std::ptr::eq(self.as_ref(), other.as_ref())
    }
}

impl Eq for Box<ScriptFunction> {}

/// Native callable wrapper for primitives that need direct access to the evaluation context.
///
/// Context-native functions take ownership of their argument vector. Unlike the
/// generated native wrappers below, they must consume or explicitly discard any
/// `ValOrMut::Val` they remove from that vector.
#[derive(Debug, Clone)]
pub struct ContextNativeFn {
    /// Debug name used when formatting the native callable.
    name: &'static str,
    /// Runtime adapter passing, including hidden evidence followed by visible parameters.
    runtime_argument_passing: Vec<ArgConvention>,
    /// Visible Ferlium parameter passing, excluding hidden runtime evidence.
    visible_parameter_passing: &'static [ArgConvention],
    /// Rust callback implementing the context-native operation.
    function: for<'a> fn(ValOrMutArgs, &mut CallCtx<'a>) -> EvalControlFlowResult,
}

impl ContextNativeFn {
    pub(crate) fn new(
        name: &'static str,
        hidden_argument_passing: &'static [ArgConvention],
        visible_parameter_passing: &'static [ArgConvention],
        function: for<'a> fn(ValOrMutArgs, &mut CallCtx<'a>) -> EvalControlFlowResult,
    ) -> Self {
        let runtime_argument_passing = hidden_argument_passing
            .iter()
            .chain(visible_parameter_passing)
            .copied()
            .collect();
        Self {
            name,
            runtime_argument_passing,
            visible_parameter_passing,
            function,
        }
    }
}

impl Callable for ContextNativeFn {
    fn call(
        &self,
        args: Vec<ValOrMut>,
        ctx: &mut CallCtx,
        _locals: &[ELocalDecl],
    ) -> EvalControlFlowResult {
        (self.function)(ValOrMutArgs::new(args), ctx)
    }

    fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
        Some(&self.runtime_argument_passing)
    }

    fn visible_parameter_passing(&self) -> Option<&[ArgConvention]> {
        Some(self.visible_parameter_passing)
    }

    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _locals: &[ELocalDecl],
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        write!(f, "{}{} @ {:p}", indent_str, self.name, self.function)
    }
}

/// Compiler-generated addressor for a structural projection with a fixed field index.
#[derive(Debug, Clone)]
pub struct StructuralFieldAddressor {
    index: isize,
    runtime_argument_passing: Vec<ArgConvention>,
}

impl StructuralFieldAddressor {
    pub fn new(index: usize) -> Self {
        Self {
            index: index as isize,
            runtime_argument_passing: vec![ArgConvention::MutableRef],
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
        debug_assert_eq!(args.len(), 1);
        let receiver = args.pop().expect("structural field receiver should exist");
        let mut place = match receiver {
            ValOrMut::Mut(place) => place,
            ValOrMut::Val(value) => {
                value.discard_storage();
                return Err(RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(
                    "structural projection receiver".into(),
                )));
            }
            ValOrMut::Ref(_) | ValOrMut::Dictionary(_) => {
                return Err(RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(
                    "structural projection receiver".into(),
                )));
            }
        };
        place.path.push(self.index);
        cont(Value::native(PlaceResult::new(place)))
    }

    fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
        Some(&self.runtime_argument_passing)
    }

    fn visible_parameter_passing(&self) -> Option<&[ArgConvention]> {
        Some(&self.runtime_argument_passing)
    }

    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _locals: &[ELocalDecl],
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        write!(f, "{}structural field addressor {}", indent_str, self.index)
    }
}

// Helper traits and structs for defining native functions

/// A trait that must be satisfied by the output of a native function.
/// This is used to ensure that the output can be converted to a `Value`.
pub trait NativeOutput: NativeValue {}
impl<T: NativeValue> NativeOutput for T {}

/// Marker selecting owned Rust-value extraction for a native `Let` argument.
pub struct NatVal<T> {
    _marker: PhantomData<T>,
}

/// Marker selecting shared Rust-reference extraction for a native `Let` argument.
pub struct NatRef<T> {
    _marker: PhantomData<T>,
}

/// Marker selecting mutable Rust-reference extraction for a native `MutableRef` argument.
pub struct NatMut<T> {
    _marker: PhantomData<T>,
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
impl trivial_copy_private::Sealed for crate::std::math::Float {}
unsafe impl NativeTrivialCopy for crate::std::math::Float {}

fn copy_boxed_trivial_copy_native_typed<T: NativeTrivialCopy + NativeValue>(
    value: &Value,
) -> Option<Value> {
    value
        .as_primitive_ty::<T>()
        .map(|value| Value::native(*value))
}

/// Copy one of the boxed interpreter's native `TrivialCopy` representations.
///
/// Keeping this dispatch beside the sealed Rust opt-ins makes adding a native
/// leaf a single Rust-side change. Language-level trait registration remains
/// explicit in the standard module.
pub(crate) fn copy_boxed_trivial_copy_native(value: &Value) -> Option<Value> {
    copy_boxed_trivial_copy_native_typed::<()>(value)
        .or_else(|| copy_boxed_trivial_copy_native_typed::<bool>(value))
        .or_else(|| copy_boxed_trivial_copy_native_typed::<isize>(value))
        .or_else(|| copy_boxed_trivial_copy_native_typed::<crate::std::math::Float>(value))
        .or_else(|| copy_boxed_trivial_copy_native_typed::<crate::std::string::StaticStr>(value))
}

pub fn extract_trivial_native_input<T: NativeTrivialCopy>(
    arg: &ValOrMut,
    ctx: &mut CallCtx,
) -> Result<T, RuntimeErrorKind> {
    match arg.as_primitive::<T>(ctx)? {
        Some(value) => Ok(*value),
        None => panic!(
            "Expected a primitive of type {}, found {}",
            std::any::type_name::<T>(),
            arg.format_with(ctx)
        ),
    }
}

pub fn extract_native_ref<'m, T: 'static>(
    arg: &'m ValOrMut,
    ctx: &'m mut CallCtx,
) -> Result<&'m T, RuntimeErrorKind> {
    match arg.as_primitive::<T>(ctx)? {
        Some(value) => Ok(value),
        None => panic!(
            "Expected a primitive of type {}, found {}",
            std::any::type_name::<T>(),
            arg.format_with(ctx)
        ),
    }
}

/// A trait that can extract an argument from a `ValOrMut` and a `CallCtx`.
/// This is necessary due to the lack of specialization in stable Rust.
pub trait ArgExtractor {
    type Output<'a>;
    const PASSING: ArgConvention;
    fn extract<'m>(
        arg: &'m ValOrMut,
        ctx: &'m mut CallCtx,
    ) -> Result<Self::Output<'m>, RuntimeErrorKind>;
    fn default_ty() -> Type;
}

impl ArgExtractor for Value {
    type Output<'a> = &'a Value;
    const PASSING: ArgConvention = ArgConvention::Let;
    fn extract<'m>(
        arg: &'m ValOrMut,
        ctx: &'m mut CallCtx,
    ) -> Result<Self::Output<'m>, RuntimeErrorKind> {
        arg.as_value_ref(ctx)
    }
    fn default_ty() -> Type {
        Type::variable_id(0)
    }
}

impl ArgExtractor for &'_ mut Value {
    type Output<'a> = &'a mut Value;
    const PASSING: ArgConvention = ArgConvention::MutableRef;
    fn extract<'m>(
        arg: &'m ValOrMut,
        ctx: &'m mut CallCtx,
    ) -> Result<Self::Output<'m>, RuntimeErrorKind> {
        arg.as_place().target_mut(ctx)
    }
    fn default_ty() -> Type {
        Type::variable_id(0)
    }
}

impl<T: NativeTrivialCopy> ArgExtractor for NatVal<T> {
    type Output<'a> = T;
    const PASSING: ArgConvention = ArgConvention::Let;
    fn extract<'m>(
        arg: &'m ValOrMut,
        ctx: &'m mut CallCtx,
    ) -> Result<Self::Output<'m>, RuntimeErrorKind> {
        extract_trivial_native_input(arg, ctx)
    }
    fn default_ty() -> Type {
        Type::primitive::<T>()
    }
}

impl<T: 'static> ArgExtractor for NatRef<T> {
    type Output<'a> = &'a T;
    const PASSING: ArgConvention = ArgConvention::Let;
    fn extract<'m>(
        arg: &'m ValOrMut,
        ctx: &'m mut CallCtx,
    ) -> Result<Self::Output<'m>, RuntimeErrorKind> {
        extract_native_ref(arg, ctx)
    }
    fn default_ty() -> Type {
        Type::primitive::<T>()
    }
}

impl<T: 'static> ArgExtractor for NatMut<T> {
    type Output<'a> = &'a mut T;
    const PASSING: ArgConvention = ArgConvention::MutableRef;
    fn extract<'m>(
        arg: &'m ValOrMut,
        ctx: &'m mut CallCtx,
    ) -> Result<Self::Output<'m>, RuntimeErrorKind> {
        Ok(arg.as_mut_primitive::<T>(ctx)?.unwrap())
    }
    fn default_ty() -> Type {
        Type::primitive::<T>()
    }
}

/// Marker struct to declare the output of a native function as a fallible value.
pub struct Fallible<T> {
    _marker: PhantomData<T>,
}

/// A trait to dispatch over the fallibility of a native function
pub trait OutputBuilder {
    type Input;
    fn build(result: Self::Input) -> EvalControlFlowResult;
    fn default_ty() -> Type;
}

impl<O: NativeOutput> OutputBuilder for NatVal<O> {
    type Input = O;
    fn build(result: Self::Input) -> EvalControlFlowResult {
        cont(Value::native(result))
    }
    fn default_ty() -> Type {
        Type::primitive::<O>()
    }
}

impl<O: NativeOutput> OutputBuilder for Fallible<NatVal<O>> {
    type Input = Result<O, RuntimeErrorKind>;
    fn build(result: Self::Input) -> EvalControlFlowResult {
        cont(Value::native(result.map_err(RuntimeError::new_native)?))
    }
    fn default_ty() -> Type {
        Type::primitive::<O>()
    }
}

impl OutputBuilder for Value {
    type Input = Value;
    fn build(result: Self::Input) -> EvalControlFlowResult {
        cont(result)
    }
    fn default_ty() -> Type {
        Type::variable_id(0)
    }
}

impl OutputBuilder for Fallible<Value> {
    type Input = Result<Value, RuntimeErrorKind>;
    fn build(result: Self::Input) -> EvalControlFlowResult {
        cont(result.map_err(RuntimeError::new_native)?)
    }
    fn default_ty() -> Type {
        Type::variable_id(0)
    }
}

// Native functions of various arities

macro_rules! count {
    () => (0usize);
    ( $x:tt $($xs:tt)* ) => (1usize + count!($($xs)*));
}

macro_rules! n_ary_native_fn {
    // Entry point for generating n-ary function structures
    ($struct_name:ident $(, $arg:ident)*) => {
        #[allow(unused_parens)]
        pub struct $struct_name<
            $($arg: ArgExtractor + 'static,)*
            O: OutputBuilder + 'static,
        >(
            for<'a> fn($($arg::Output<'a>),*) -> O::Input,
            PhantomData<($($arg,)* O)>,
        );

        impl<
            $($arg: ArgExtractor + 'static,)*
            O: OutputBuilder + 'static,
        > Clone for $struct_name<$($arg,)* O>
        {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<
            $($arg: ArgExtractor + 'static,)*
            O: OutputBuilder + 'static,
        > Copy for $struct_name<$($arg,)* O> {}

        impl<
            $($arg: ArgExtractor + 'static,)*
            O: OutputBuilder + 'static,
        > std::fmt::Debug for $struct_name<$($arg,)* O>
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{} @ {:p}", stringify!($struct_name), &self.0)
            }
        }

        impl<
            $($arg: ArgExtractor + 'static,)*
            O: OutputBuilder + 'static,
        > $struct_name<$($arg,)* O>
        {
            pub fn new(f: for<'a> fn($($arg::Output<'a>),*) -> O::Input) -> Self {
                $struct_name(f, PhantomData)
            }

            pub fn description_with_ty_scheme(f: for<'a> fn($($arg::Output<'a>),*) -> O::Input, arg_names: [&'static str; count!($($arg)*)], doc: &'static str, ty_scheme: TypeScheme<FnType>) -> ModuleFunction {
                ModuleFunction::new(
                    CallableDefinition::new(
                        ty_scheme,
                        arg_names.into_iter().map(Ustr::from).collect(),
                        Some(String::from(doc)),
                    ),
                    Box::new(Self::new(f)),
                    None,
                    Vec::new(),
                )
            }

            paste::paste! {
            #[allow(clippy::too_many_arguments)]
            pub fn description_with_ty(f: for<'a> fn($($arg::Output<'a>),*) -> O::Input, arg_names: [&'static str; count!($($arg)*)], doc: &'static str, $([<$arg:lower _ty>]: Type,)* o_ty: Type, effects: EffType) -> ModuleFunction {
                let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
                    [$(([<$arg:lower _ty>], $arg::PASSING == ArgConvention::MutableRef)), *],
                    o_ty,
                    effects,
                ));
                Self::description_with_ty_scheme(f, arg_names, doc, ty_scheme)
            }
            }

            paste::paste! {
                #[allow(clippy::too_many_arguments)]
                pub fn description_with_in_ty(f: for<'a> fn($($arg::Output<'a>),*) -> O::Input, arg_names: [&'static str; count!($($arg)*)], doc: &'static str, $([<$arg:lower _ty>]: Type,)* effects: EffType) -> ModuleFunction {
                    let o_ty = O::default_ty();
                    Self::description_with_ty(f, arg_names, doc, $([<$arg:lower _ty>],)* o_ty, effects)
                }
                }

            pub fn description_with_default_ty(f: for<'a> fn($($arg::Output<'a>),*) -> O::Input, arg_names: [&'static str; count!($($arg)*)], doc: &'static str, effects: EffType) -> ModuleFunction {
                Self::description_with_in_ty(f, arg_names, doc, $($arg::default_ty(),)* effects)
            }
        }

        impl<$($arg,)* O> Callable for $struct_name<$($arg,)* O>
        where
            $($arg: ArgExtractor + 'static,)*
            O: OutputBuilder + 'static,
        {
            paste::paste! {
            #[allow(unused_variables)]
            fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx, _locals: &[ELocalDecl]) -> EvalControlFlowResult {
                let args = CallArgsStorageGuard::new(args);
                // Extract arguments by applying repetition for each ArgExtractor
                #[allow(unused_variables, unused_mut)]
                let mut args_iter = args.iter();
                $(
                    let [<$arg:lower>] = args_iter.next().unwrap();
                    // SAFETY: the borrow checker ensures that all mutable references are disjoint
                    let arg_ctx = unsafe { &mut *(ctx as *mut CallCtx) };
                    let [<$arg:lower>] = $arg::extract([<$arg:lower>], arg_ctx).map_err(RuntimeError::new_native)?;
                )*

                // Call the function using the extracted arguments
                O::build((self.0)($([<$arg:lower>]),*))
            }
            }

            fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
                Some(&[$($arg::PASSING),*])
            }

            fn format_ind(
                &self,
                f: &mut std::fmt::Formatter,
                _locals: &[ELocalDecl],
                _env: &ModuleEnv<'_>,
                spacing: usize,
                indent: usize,
            ) -> std::fmt::Result {
                let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
                writeln!(f, "{}{} @ {:p}", indent_str, stringify!($struct_name), &self.0)
            }
        }
    };
}

// Declare aliases for native functions of various arities

// Shorthand names for native functions type aliases:
// arguments:
// - N: Val<T> (native value)
// - M: Mut<T> (native mutable reference)
// - V: Value (generic value)
// - W: &mut Value (mutable reference to a runtime value slot)
// outputs:
// - N: native
// - V: value
// - FN: native, fallible
// - FV: value, fallible

// Note: the proc macro declare_native_fn_aliases defined in ferlium_macros generates
// typedefs with the combinations of aliases.

n_ary_native_fn!(NullaryNativeFn);
declare_native_fn_aliases!(0);

impl<O: OutputBuilder + 'static> NullaryNativeFn<O> {
    pub fn description(f: fn() -> O::Input, doc: &'static str, effects: EffType) -> ModuleFunction {
        Self::description_with_in_ty(f, [], doc, effects)
    }
}

n_ary_native_fn!(UnaryNativeFn, A0);
declare_native_fn_aliases!(1);

n_ary_native_fn!(BinaryNativeFn, A0, A1);
declare_native_fn_aliases!(2);

n_ary_native_fn!(TernaryNativeFn, A0, A1, A2);
declare_native_fn_aliases!(3);

// Beyond size 3, we do not define aliases

n_ary_native_fn!(QuaternaryNativeFn, A0, A1, A2, A3);
n_ary_native_fn!(QuinaryNativeFn, A0, A1, A2, A3, A4);
n_ary_native_fn!(SenaryNativeFn, A0, A1, A2, A3, A4, A5);
n_ary_native_fn!(SeptenaryNativeFn, A0, A1, A2, A3, A4, A5, A6);
n_ary_native_fn!(OctonaryNativeFn, A0, A1, A2, A3, A4, A5, A6, A7);

#[cfg(test)]
mod tests {
    use std::mem::size_of;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crate::{
        CompilerSession,
        eval::ControlFlow,
        hir::{CallArgument, Elaborated, value::NativeValueType},
        module::{ModuleId, id::Id},
    };

    use super::*;

    static NATIVE_ARG_DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[derive(Debug)]
    struct NativeArgDropTracked;

    impl NativeValueType for NativeArgDropTracked {}

    impl Drop for NativeArgDropTracked {
        fn drop(&mut self) {
            NATIVE_ARG_DROP_COUNT.fetch_add(1, Ordering::Relaxed);
        }
    }

    fn observe_value(_: &Value) {}

    #[test]
    fn argument_convention_stays_compact() {
        assert_eq!(
            size_of::<ArgConvention>(),
            1,
            "ArgConvention should remain a compact semantic classification"
        );
        assert!(
            size_of::<CallArgument<Elaborated>>() <= size_of::<usize>(),
            "CallArgument should remain pointer-sized after removing the layout payload"
        );
    }

    #[test]
    fn generated_native_wrapper_discards_owned_argument_storage() {
        NATIVE_ARG_DROP_COUNT.store(0, Ordering::Relaxed);
        let session = CompilerSession::new();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        let function = UnaryNativeFnVN::new(observe_value);

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
