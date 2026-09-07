// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Typed native C entries. Only the boxed executor adapter deals in `Value` and `Place`.
//!
//! Input aliases select passing modes: `N` for scalar values, `R` for shared references,
//! and `M` for mutable references. Concrete input and result types are inferred:
//! ```
//! use ferlium::hir::native_functions::{NativeFnNN, NativeFnMN};
//! extern "C" fn add(lhs: isize, rhs: isize) -> isize { lhs.wrapping_add(rhs) }
//! extern "C" fn assign(target: &mut isize, source: isize) { *target = source; }
//! let _ = NativeFnNN::new(add);
//! let _ = NativeFnMN::new(assign);
//! ```
//! The same suffixes apply to `NativeOutFn`, `NativeFallibleFn`, `NativeFallibleOutFn`,
//! and unary `NativeOptionalFn`. They select [`ByValue`], [`Shared`], and [`Mutable`]
//! markers over the shared arity-based adapters; result protocols remain separate.
//! Floating-point inputs accept `Float` or `f64`; results use `Float` so its finite-value
//! invariant holds at the C entry itself, including output-pointer and optional results.
//!
//! Use `from_rust` for an existing Rust function item or stateless closure. It generates a
//! monomorphized C entry; inputs and results are inferred without repeating the signature:
//! ```
//! use ferlium::hir::native_functions::{NativeFnNN, NativeOutFnR};
//! use ferlium::std::string::String;
//! let _ = NativeFnNN::from_rust(<bool as std::ops::BitAnd>::bitand);
//! let _ = NativeOutFnR::from_rust(String::trim);
//! ```
//! Output, fallible, and optional families adapt ordinary `T`, `Result<T, SourceFailureKind>`,
//! and `Option<T>` results to their C protocols. All bodies execute inside the C boundary and
//! must not panic. `native_fn!` remains useful for bodies that need conversions or several steps.
//! Fallible families also offer `from_rust_infallible` for implementations returning ordinary
//! values: it preserves the fallible ABI but always reports success on normal return.
//! ```
//! use ferlium::hir::native_functions::NativeFallibleOutFnR;
//! use ferlium::std::string::String;
//! let _ = NativeFallibleOutFnR::from_rust_infallible(String::clone);
//! ```
//! `from_rust_never` accepts `Result<Never, SourceFailureKind>` for source-level `never`,
//! using [`crate::types::never::Never`].
//!
//! The entry carries no callback state. Stateful captures and erased function pointers are rejected:
//! ```compile_fail
//! use ferlium::hir::native_functions::NativeFnN;
//! let offset = 3isize;
//! let _ = NativeFnN::from_rust(move |value: isize| value + offset);
//! ```
//! ```compile_fail
//! use ferlium::hir::native_functions::NativeFnN;
//! let function: fn(isize) -> isize = std::convert::identity;
//! let _ = NativeFnN::from_rust(function);
//! ```
//! Borrowing remains call-scoped through the Rust wrapper too:
//! ```compile_fail
//! use ferlium::hir::native_functions::NativeFnR;
//! fn needs_static(_: &'static isize) -> bool { true }
//! let _ = NativeFnR::from_rust(needs_static);
//! ```
//!
//! Register functions and methods directly when their signatures match the transport. Rust
//! rejects an entry that omits `extern "C"`, even when its argument and result types match:
//! ```compile_fail
//! use ferlium::hir::native_functions::NativeFnN;
//! fn identity(value: isize) -> isize { value }
//! let _ = NativeFnN::new(identity);
//! ```

use std::{any::TypeId, fmt, mem::MaybeUninit};

use super::function::{self, ArgConvention, CallArgsStorageGuard, Callable, CallableDefinition};
use crate::{
    compiler::error::SourceFailureKind,
    eval::{EvalControlFlowResult, EvalCtx, RuntimeError, ValOrMut, cont},
    hir::value::{NativeValue, Value},
    module::{ELocalDecl, ModuleEnv, ModuleFunction},
    std::math::Float,
    types::{
        effects::{EffType, Effect, PrimitiveEffect},
        mutability::MutType,
        never::Never,
        r#type::{CallResultConvention, FnType, Type},
        type_like::TypeLike,
        type_scheme::TypeScheme,
    },
};

/// Invocation-owned diagnostic storage. C entries borrow this opaque runtime object; no Rust
/// error layout crosses the ABI. Empty state allocates nothing, and nested host invocations own
/// separate states. The boxed adapters take each error into their existing cleanup/backtrace flow.
#[derive(Debug, Default)]
pub struct NativeFailureState {
    pending: Option<SourceFailureKind>,
}

impl NativeFailureState {
    pub fn is_empty(&self) -> bool {
        self.pending.is_none()
    }

    /// Record a new source failure and return its nonzero ABI status. Propagating an existing
    /// failure must preserve the cell; cleanup must first take and retain the original cause.
    pub fn fail(&mut self, error: SourceFailureKind) -> u32 {
        assert!(
            self.is_empty(),
            "native failure would overwrite an unhandled diagnostic"
        );
        self.pending = Some(error);
        1
    }

    /// Move the diagnostic into the host executor, freeing this cell for subsequent cleanup calls.
    pub fn take(&mut self) -> Option<SourceFailureKind> {
        self.pending.take()
    }

    /// Adapt a Rust result into success-only output initialization and a status return.
    pub fn write_result<T>(
        &mut self,
        result: Result<T, SourceFailureKind>,
        output: &mut MaybeUninit<T>,
    ) -> u32 {
        match result {
            Ok(value) => {
                output.write(value);
                0
            }
            Err(error) => self.fail(error),
        }
    }

    pub fn write_unit_result(&mut self, result: Result<(), SourceFailureKind>) -> u32 {
        match result {
            Ok(()) => 0,
            Err(error) => self.fail(error),
        }
    }

    fn finish(&mut self, status: u32) -> Result<(), RuntimeError> {
        if status == 0 {
            assert!(
                self.is_empty(),
                "successful native call left a failure diagnostic"
            );
            Ok(())
        } else {
            Err(RuntimeError::new_native(
                self.take()
                    .expect("failed native call omitted its diagnostic"),
            ))
        }
    }
}

/// Physical transport of source failure, independent of the target's pointer width.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NativeFailureConvention {
    Infallible,
    /// Leading state pointer and a `u32` return: zero succeeds, nonzero propagates source failure.
    StatusWithState,
}

/// Layout of a concrete Rust value in the matching runtime, derived from its registered type.
/// This is not a promise of layout compatibility with another Rust build.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NativeLayout {
    pub ty: Type,
    pub rust_type: TypeId,
    pub size: usize,
    pub align: usize,
}

impl NativeLayout {
    pub fn of<T: 'static>() -> Self {
        Self {
            ty: Type::primitive::<T>(),
            rust_type: TypeId::of::<T>(),
            size: size_of::<T>(),
            align: align_of::<T>(),
        }
    }

    fn requires_direct_transport(self) -> bool {
        [
            TypeId::of::<bool>(),
            TypeId::of::<isize>(),
            TypeId::of::<Float>(),
        ]
        .contains(&self.rust_type)
    }
}

/// C scalar transport. `Int` has the target's pointer width, independently of `Float`.
/// Rust `Float` and `f64` share this scalar ABI through `Float`'s transparent representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NativeScalar {
    Bool,
    Int,
    Float,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NativeParameter {
    Scalar(NativeLayout, NativeScalar),
    Shared(NativeLayout),
    Mutable(NativeLayout),
    /// Initialized on entry, absent afterwards; reserved for native `Value::drop`.
    Consuming(NativeLayout),
}

impl NativeParameter {
    pub fn layout(self) -> NativeLayout {
        match self {
            Self::Scalar(layout, _)
            | Self::Shared(layout)
            | Self::Mutable(layout)
            | Self::Consuming(layout) => layout,
        }
    }

    pub fn passing(self) -> ArgConvention {
        if matches!(self, Self::Mutable(_) | Self::Consuming(_)) {
            ArgConvention::MutableRef
        } else {
            ArgConvention::Let
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NativeResult {
    Unit,
    /// Source-level `never`: the status-only entry must always report failure.
    Never,
    Scalar(NativeLayout, NativeScalar),
    /// Trailing pointer, initialized exactly once on normal return.
    Output(NativeLayout),
    /// Boolean presence return and trailing storage for the payload.
    Optional {
        payload: NativeLayout,
        ty: Type,
    },
}

impl NativeResult {
    pub fn ty(self) -> Type {
        match self {
            Self::Unit => Type::primitive::<()>(),
            Self::Never => Type::never(),
            Self::Optional { ty, .. } => ty,
            Self::Scalar(layout, _) | Self::Output(layout) => layout.ty,
        }
    }
}

/// Target-independent transport roles; C lowering chooses the target's machine signature.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NativeSignature {
    pub failure: NativeFailureConvention,
    pub parameters: Vec<NativeParameter>,
    pub result: NativeResult,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeContractError {
    NotClosed,
    Fallibility,
    ResultConvention,
    ArgumentCount,
    Argument { index: usize },
    ArgumentTransport { index: usize },
    ResultType,
    ResultTransport,
    ConsumingSignature,
}

impl fmt::Display for NativeContractError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotClosed => {
                f.write_str("typed native entries require a closed, unconstrained signature")
            }
            Self::Fallibility => f.write_str(
                "native entry failure convention differs from its source-failure effects",
            ),
            Self::ResultConvention => {
                f.write_str("native value entry declared with a non-value result convention")
            }
            Self::ArgumentCount => {
                f.write_str("native entry argument count differs from its declaration")
            }
            Self::Argument { index } => write!(
                f,
                "native entry argument {index} differs in type or mutability"
            ),
            Self::ArgumentTransport { index } => {
                write!(f, "native entry argument {index} requires direct transport")
            }
            Self::ResultType => {
                f.write_str("native entry result type differs from its declaration")
            }
            Self::ResultTransport => f.write_str("native entry result requires direct transport"),
            Self::ConsumingSignature => {
                f.write_str("native destruction requires one consuming argument and a unit result")
            }
        }
    }
}
impl std::error::Error for NativeContractError {}

impl NativeSignature {
    /// Check a registration's semantic declaration against its typed entry before execution.
    pub fn validate(&self, definition: &CallableDefinition) -> Result<(), NativeContractError> {
        if self
            .parameters
            .iter()
            .any(|arg| matches!(arg, NativeParameter::Consuming(_)))
            && (!matches!(self.parameters.as_slice(), [NativeParameter::Consuming(_)])
                || self.result != NativeResult::Unit
                || self.failure != NativeFailureConvention::Infallible)
        {
            return Err(NativeContractError::ConsumingSignature);
        }
        let ty = &definition.ty_scheme.ty;
        if !ty.is_constant() || !definition.ty_scheme.constraints.is_empty() {
            return Err(NativeContractError::NotClosed);
        }
        let may_fail = ty
            .effects
            .contains(Effect::Primitive(PrimitiveEffect::Fallible));
        if may_fail != (self.failure == NativeFailureConvention::StatusWithState) {
            return Err(NativeContractError::Fallibility);
        }
        if definition.result_convention != CallResultConvention::Value {
            return Err(NativeContractError::ResultConvention);
        }
        if self.parameters.len() != ty.args.len() {
            return Err(NativeContractError::ArgumentCount);
        }
        for (index, (entry, declared)) in self.parameters.iter().zip(&ty.args).enumerate() {
            let mutable = entry.passing() == ArgConvention::MutableRef;
            if entry.layout().ty != declared.ty || declared.mut_ty != MutType::from(mutable) {
                return Err(NativeContractError::Argument { index });
            }
            if matches!(entry, NativeParameter::Shared(layout) if layout.requires_direct_transport())
            {
                return Err(NativeContractError::ArgumentTransport { index });
            }
        }
        if self.result.ty() != ty.ret {
            return Err(NativeContractError::ResultType);
        }
        if matches!(self.result, NativeResult::Output(layout)
            if layout.rust_type == TypeId::of::<()>()
                || (self.failure == NativeFailureConvention::Infallible && layout.requires_direct_transport()))
            || (self.failure == NativeFailureConvention::StatusWithState
                && matches!(
                    self.result,
                    NativeResult::Scalar(..) | NativeResult::Optional { .. }
                ))
            || (self.failure == NativeFailureConvention::Infallible
                && self.result == NativeResult::Never)
        {
            return Err(NativeContractError::ResultTransport);
        }
        Ok(())
    }
}

/// Address and contract of the existing callable's entry, not a second function identity.
#[derive(Clone, Debug)]
pub struct NativeEntry {
    address: *const (),
    signature: NativeSignature,
}

impl NativeEntry {
    /// The entry's code pointer in the matching runtime, including a table pointer on Wasm.
    pub fn address(&self) -> *const () {
        self.address
    }

    /// Read-only: safe code cannot replace the contract independently of its entry address.
    pub fn signature(&self) -> &NativeSignature {
        &self.signature
    }
}

mod sealed {
    pub trait Argument {}
    pub trait Result {}
    pub trait Entry {}
    pub trait StoredResult {}
}

/// Rust argument kinds accepted by the typed bridge. Reference type parameters describe a
/// borrow kind; the entry receives a fresh, call-scoped lifetime, never a `'static` reference.
/// Implementations are sealed so extraction and signature metadata cannot disagree.
///
/// An entry cannot require a borrow that outlives the call:
/// ```compile_fail
/// use ferlium::{hir::native_functions::NativeFnR, std::string::String};
/// extern "C" fn needs_static(_: &'static String) -> bool { true }
/// let _ = NativeFnR::new(needs_static);
/// ```
pub trait NativeArgument: sealed::Argument + 'static {
    type Extracted;
    type Borrowed<'a>;

    fn parameter() -> NativeParameter;
    fn extract(arg: &ValOrMut, ctx: &mut EvalCtx) -> Result<Self::Extracted, SourceFailureKind>;

    /// Materialize the argument only after all interpreter lookups have finished.
    ///
    /// # Safety
    /// Extracted pointees must remain initialized and live for the borrow, with shared or
    /// exclusive access as declared. No interpreter access may invalidate those borrows.
    unsafe fn borrow(value: &mut Self::Extracted) -> Self::Borrowed<'_>;
}

// Implement by-value extraction and ABI metadata for a supported C scalar. `$native` is the
// boxed Ferlium type, `$rust` is the entry's argument type, and `$convert` bridges them (for
// example, Float -> f64). Extraction copies the value, so borrowing needs no pointer or lifetime.
macro_rules! scalar_argument {
    ($rust:ty, $native:ty, $kind:ident, $convert:expr) => {
        impl sealed::Argument for $rust {}
        impl NativeArgument for $rust {
            type Extracted = Self;
            type Borrowed<'a> = Self;

            fn parameter() -> NativeParameter {
                NativeParameter::Scalar(NativeLayout::of::<$native>(), NativeScalar::$kind)
            }
            fn extract(arg: &ValOrMut, ctx: &mut EvalCtx) -> Result<Self, SourceFailureKind> {
                let value = function::extract_trivial_native_input::<$native>(arg, ctx)?;
                Ok(($convert)(value))
            }
            unsafe fn borrow(value: &mut Self) -> Self {
                *value
            }
        }
    };
}
scalar_argument!(bool, bool, Bool, |value| value);
scalar_argument!(isize, isize, Int, |value| value);
scalar_argument!(f64, Float, Float, Float::into_inner);
scalar_argument!(Float, Float, Float, |value| value);

impl<T: NativeValue> sealed::Argument for &T {}
impl<T: NativeValue> NativeArgument for &'static T {
    type Extracted = *const T;
    type Borrowed<'a> = &'a T;

    fn parameter() -> NativeParameter {
        NativeParameter::Shared(NativeLayout::of::<T>())
    }
    fn extract(arg: &ValOrMut, ctx: &mut EvalCtx) -> Result<Self::Extracted, SourceFailureKind> {
        Ok(function::extract_native_ref::<T>(arg, ctx)? as *const T)
    }
    unsafe fn borrow(value: &mut Self::Extracted) -> &T {
        // SAFETY: the caller establishes a live shared pointee for this call.
        unsafe { &**value }
    }
}

impl<T: NativeValue> sealed::Argument for &mut T {}
impl<T: NativeValue> NativeArgument for &'static mut T {
    type Extracted = *mut T;
    type Borrowed<'a> = &'a mut T;

    fn parameter() -> NativeParameter {
        NativeParameter::Mutable(NativeLayout::of::<T>())
    }
    fn extract(arg: &ValOrMut, ctx: &mut EvalCtx) -> Result<Self::Extracted, SourceFailureKind> {
        Ok(arg
            .as_mut_primitive::<T>(ctx)?
            .expect("typed native mutable argument") as *mut T)
    }
    unsafe fn borrow(value: &mut Self::Extracted) -> &mut T {
        // SAFETY: the caller establishes exclusive access to a live pointee for this call.
        unsafe { &mut **value }
    }
}

/// Select scalar value passing while allowing the concrete type to be inferred.
pub struct ByValue<T>(::std::marker::PhantomData<T>);
/// Select shared reference passing with a fresh lifetime for each call.
pub struct Shared<T>(::std::marker::PhantomData<T>);
/// Select mutable reference passing with a fresh lifetime for each call.
/// ```compile_fail
/// use ferlium::hir::native_functions::NativeFnM;
/// extern "C" fn needs_static(_: &'static mut isize) {}
/// let _ = NativeFnM::new(needs_static);
/// ```
pub struct Mutable<T>(::std::marker::PhantomData<T>);

// Explicit Borrowed mappings let Rust infer T from the entry signature. Extraction still
// delegates to the same sealed implementations used by native_fn!'s explicit Rust types.
macro_rules! argument_marker {
    ($marker:ident, $source:ty, $borrowed:ty) => {
        impl<T: 'static> sealed::Argument for $marker<T> where
            for<'a> $source: NativeArgument<Borrowed<'a> = $borrowed>
        {
        }
        impl<T: 'static> NativeArgument for $marker<T>
        where
            for<'a> $source: NativeArgument<Borrowed<'a> = $borrowed>,
        {
            type Extracted = <$source as NativeArgument>::Extracted;
            type Borrowed<'a> = $borrowed;

            fn parameter() -> NativeParameter {
                <$source as NativeArgument>::parameter()
            }
            fn extract(
                arg: &ValOrMut,
                ctx: &mut EvalCtx,
            ) -> Result<Self::Extracted, SourceFailureKind> {
                <$source as NativeArgument>::extract(arg, ctx)
            }
            unsafe fn borrow(value: &mut Self::Extracted) -> Self::Borrowed<'_> {
                // SAFETY: forwarding preserves the underlying argument's borrowing contract.
                unsafe { <$source as NativeArgument>::borrow(value) }
            }
        }
    };
}
argument_marker!(ByValue, T, T);
argument_marker!(Shared, &'static T, &'a T);
argument_marker!(Mutable, &'static mut T, &'a mut T);

pub trait NativeDirectResult: sealed::Result + 'static {
    fn result() -> NativeResult;
    fn boxed(self) -> Value;
}

macro_rules! scalar_result {
    ($rust:ty, $native:ty, $kind:ident, $convert:expr) => {
        impl sealed::Result for $rust {}
        impl NativeDirectResult for $rust {
            fn result() -> NativeResult {
                NativeResult::Scalar(NativeLayout::of::<$native>(), NativeScalar::$kind)
            }
            fn boxed(self) -> Value {
                Value::native(($convert)(self))
            }
        }
    };
}
scalar_result!(bool, bool, Bool, |value| value);
scalar_result!(isize, isize, Int, |value| value);
scalar_result!(Float, Float, Float, |value| value);

impl sealed::Result for () {}
impl NativeDirectResult for () {
    fn result() -> NativeResult {
        NativeResult::Unit
    }
    fn boxed(self) -> Value {
        Value::unit()
    }
}

/// Values written through result pointers. Scalars use storage only for optional or fallible
/// results. Floating-point results use `Float`, preserving finiteness before interpreter boxing.
pub trait NativeStoredResult: sealed::StoredResult + 'static {
    fn layout() -> NativeLayout;
    fn boxed(self) -> Value;
}

impl<T: NativeValue> sealed::StoredResult for T {}
impl<T: NativeValue> NativeStoredResult for T {
    fn layout() -> NativeLayout {
        NativeLayout::of::<T>()
    }
    fn boxed(self) -> Value {
        Value::native(self)
    }
}

/// Implementation detail shared by every typed arity and result protocol.
pub trait EntryFunction: sealed::Entry + Clone + 'static {
    fn entry(&self) -> NativeEntry;
    fn invoke(&self, args: &[ValOrMut], ctx: &mut EvalCtx) -> EvalControlFlowResult;
}

#[derive(Clone)]
pub struct NativeCallable<E: EntryFunction> {
    function: E,
    entry: NativeEntry,
    passing: Vec<ArgConvention>,
}

impl<E: EntryFunction> NativeCallable<E> {
    fn new(function: E) -> Self {
        let entry = function.entry();
        let passing = entry
            .signature
            .parameters
            .iter()
            .map(|arg| arg.passing())
            .collect();
        Self {
            function,
            entry,
            passing,
        }
    }

    pub fn description(
        self,
        arg_names: impl IntoIterator<Item = &'static str>,
        doc: &'static str,
        effects: EffType,
    ) -> ModuleFunction {
        let signature = &self.entry.signature;
        let ty = FnType::new_mut_resolved(
            signature
                .parameters
                .iter()
                .map(|arg| (arg.layout().ty, arg.passing() == ArgConvention::MutableRef)),
            signature.result.ty(),
            effects,
        );
        self.description_with_ty_scheme(arg_names, doc, TypeScheme::new_just_type(ty))
    }

    /// Supply a declaration explicitly, for named representations and registration validation.
    pub fn description_with_ty_scheme(
        self,
        arg_names: impl IntoIterator<Item = &'static str>,
        doc: &'static str,
        ty_scheme: TypeScheme<FnType>,
    ) -> ModuleFunction {
        let definition = CallableDefinition::new(
            ty_scheme,
            arg_names.into_iter().map(ustr::Ustr::from).collect(),
            Some(doc.to_owned()),
        );
        self.entry
            .signature
            .validate(&definition)
            .expect("invalid typed native declaration");
        ModuleFunction::new(definition, Box::new(self), None, Vec::new())
    }
}

impl<E: EntryFunction> Callable for NativeCallable<E> {
    fn native_entry(&self) -> Option<&NativeEntry> {
        Some(&self.entry)
    }
    fn native_optional_payload_type(&self) -> Option<Type> {
        match self.entry.signature.result {
            NativeResult::Optional { payload, .. } => Some(payload.ty),
            _ => None,
        }
    }
    fn call(
        &self,
        args: Vec<ValOrMut>,
        ctx: &mut EvalCtx,
        _locals: &[ELocalDecl],
    ) -> EvalControlFlowResult {
        let args = CallArgsStorageGuard::new(args);
        assert_eq!(
            args.args.len(),
            self.passing.len(),
            "typed native argument count"
        );
        self.function.invoke(&args.args, ctx)
    }
    fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
        Some(&self.passing)
    }
    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        _locals: &[ELocalDecl],
        _env: &ModuleEnv,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result {
        write!(
            f,
            "{}{}NativeEntry @ {:p}",
            "  ".repeat(spacing),
            "⎸ ".repeat(indent),
            self.entry.address
        )
    }
}

// A C entry has no context argument in which to carry a Rust callback. Function items and
// captureless closures encode their behavior entirely in their zero-sized type.
fn check_stateless_rust_function<F: Copy + 'static>(_: F) {
    const {
        assert!(
            size_of::<F>() == 0,
            "from_rust requires a function item or stateless closure, not a function pointer or captured state",
        );
    }
}

/// Recover the stateless callable inside its monomorphized C entry.
///
/// # Safety
/// F must have been supplied as a live value to check_stateless_rust_function before the
/// entry became callable. This proves F is inhabited and zero-sized; Copy rules out drop glue.
unsafe fn stateless_rust_function<F: Copy>() -> F {
    // SAFETY: the caller proves F is inhabited and has no representation bytes. Reconstructing
    // those zero bytes reproduces the supplied value, including any type-encoded function identity.
    unsafe { MaybeUninit::<F>::zeroed().assume_init() }
}

macro_rules! entries {
    ($direct:ident, $output:ident $(, $arg:ident : $value:ident : $index:tt)*) => {
        pub struct $direct<$($arg: NativeArgument,)* R: NativeDirectResult>(for<'a> extern "C" fn($($arg::Borrowed<'a>),*) -> R);
        impl<$($arg: NativeArgument,)* R: NativeDirectResult> Clone for $direct<$($arg,)* R> {
            fn clone(&self) -> Self { Self(self.0) }
        }
        impl<$($arg: NativeArgument,)* R: NativeDirectResult> $direct<$($arg,)* R> {
            /// Register a scalar/unit C entry.
            pub fn new(function: for<'a> extern "C" fn($($arg::Borrowed<'a>),*) -> R) -> NativeCallable<Self> {
                NativeCallable::new(Self(function))
            }

            /// Generate a C entry for a Rust function item or stateless closure, inferring its
            /// signature through the input aliases. The function must not panic across the C boundary.
            pub fn from_rust<F>(function: F) -> NativeCallable<Self>
            where F: for<'a> Fn($($arg::Borrowed<'a>),*) -> R + Copy + 'static {
                check_stateless_rust_function(function);
                #[allow(clippy::extra_unused_lifetimes)] // The zero-argument expansion has no input borrow.
                extern "C" fn entry<'a, $($arg: NativeArgument,)* R: NativeDirectResult, F>($($value: $arg::Borrowed<'a>),*) -> R
                where F: for<'b> Fn($($arg::Borrowed<'b>),*) -> R + Copy + 'static {
                    // SAFETY: from_rust validated a live, stateless F before exposing this entry.
                    let function = unsafe { stateless_rust_function::<F>() };
                    function($($value),*)
                }
                Self::new(entry::<$($arg,)* R, F>)
            }
        }
        impl<$($arg: NativeArgument,)* R: NativeDirectResult> sealed::Entry for $direct<$($arg,)* R> {}
        impl<$($arg: NativeArgument,)* R: NativeDirectResult> EntryFunction for $direct<$($arg,)* R> {
            fn entry(&self) -> NativeEntry {
                NativeEntry { address: self.0 as *const (), signature: NativeSignature {
                    failure: NativeFailureConvention::Infallible,
                    parameters: vec![$($arg::parameter()),*], result: R::result(),
                }}
            }
            #[allow(unused_variables)]
            fn invoke(&self, args: &[ValOrMut], ctx: &mut EvalCtx) -> EvalControlFlowResult {
                $(let mut $value = $arg::extract(&args[$index], ctx).map_err(RuntimeError::new_native)?;)*
                // SAFETY: the guarded arguments remain live; Ferlium borrowing establishes
                // disjoint mutable pointees. Extraction holds no EvalCtx borrow across the call.
                let result = (self.0)($(unsafe { $arg::borrow(&mut $value) }),*);
                cont(result.boxed())
            }
        }

        pub struct $output<$($arg: NativeArgument,)* O: NativeStoredResult>(for<'a> extern "C" fn($($arg::Borrowed<'a>,)* &mut MaybeUninit<O>));
        impl<$($arg: NativeArgument,)* O: NativeStoredResult> Clone for $output<$($arg,)* O> {
            fn clone(&self) -> Self { Self(self.0) }
        }
        impl<$($arg: NativeArgument,)* O: NativeStoredResult> $output<$($arg,)* O> {
            /// Register a C entry with trailing result storage.
            ///
            /// # Safety
            /// On normal return, the entry must leave an initialized output. It must not
            /// overwrite an initialized output without first destroying its value.
            pub unsafe fn new(function: for<'a> extern "C" fn($($arg::Borrowed<'a>,)* &mut MaybeUninit<O>)) -> NativeCallable<Self> {
                NativeCallable::new(Self(function))
            }

            /// Generate a C output entry for a stateless Rust function returning its result by value.
            /// The wrapper writes the output, so registration needs no unsafe initialization promise.
            pub fn from_rust<F>(function: F) -> NativeCallable<Self>
            where F: for<'a> Fn($($arg::Borrowed<'a>),*) -> O + Copy + 'static {
                check_stateless_rust_function(function);
                #[allow(clippy::extra_unused_lifetimes)] // The zero-argument expansion has no input borrow.
                extern "C" fn entry<'a, $($arg: NativeArgument,)* O: NativeStoredResult, F>($($value: $arg::Borrowed<'a>,)* output: &mut MaybeUninit<O>)
                where F: for<'b> Fn($($arg::Borrowed<'b>),*) -> O + Copy + 'static {
                    // SAFETY: from_rust validated a live, stateless F before exposing this entry.
                    let function = unsafe { stateless_rust_function::<F>() };
                    output.write(function($($value),*));
                }
                // SAFETY: the generated entry initializes exactly one output on normal return.
                unsafe { Self::new(entry::<$($arg,)* O, F>) }
            }
        }
        impl<$($arg: NativeArgument,)* O: NativeStoredResult> sealed::Entry for $output<$($arg,)* O> {}
        impl<$($arg: NativeArgument,)* O: NativeStoredResult> EntryFunction for $output<$($arg,)* O> {
            fn entry(&self) -> NativeEntry {
                NativeEntry { address: self.0 as *const (), signature: NativeSignature {
                    failure: NativeFailureConvention::Infallible,
                    parameters: vec![$($arg::parameter()),*], result: NativeResult::Output(O::layout()),
                }}
            }
            #[allow(unused_variables)]
            fn invoke(&self, args: &[ValOrMut], ctx: &mut EvalCtx) -> EvalControlFlowResult {
                $(let mut $value = $arg::extract(&args[$index], ctx).map_err(RuntimeError::new_native)?;)*
                let mut output = MaybeUninit::uninit();
                // SAFETY: arguments remain live and satisfy Ferlium borrowing; all interpreter
                // lookups finish before creating these call-scoped references.
                (self.0)($(unsafe { $arg::borrow(&mut $value) },)* &mut output);
                // SAFETY: the registered entry leaves an initialized output on normal return.
                cont(NativeStoredResult::boxed(unsafe { output.assume_init() }))
            }
        }
    };
}

entries!(NativeFn0, NativeOutFn0);
entries!(NativeFn1, NativeOutFn1, A: a: 0);
entries!(NativeFn2, NativeOutFn2, A: a: 0, B: b: 1);
entries!(NativeFn3, NativeOutFn3, A: a: 0, B: b: 1, C: c: 2);

macro_rules! fallible_entries {
    ($unit:ident, $output:ident $(, $arg:ident : $value:ident : $index:tt)*) => {
        pub struct $unit<$($arg: NativeArgument),*> {
            function: for<'a> extern "C" fn(&mut NativeFailureState $(, $arg::Borrowed<'a>)*) -> u32,
            result: NativeResult,
        }
        impl<$($arg: NativeArgument),*> Clone for $unit<$($arg),*> {
            fn clone(&self) -> Self { Self { function: self.function, result: self.result } }
        }
        impl<$($arg: NativeArgument),*> $unit<$($arg),*> {
            /// Register a source-fallible unit entry with no output pointer.
            pub fn new(function: for<'a> extern "C" fn(&mut NativeFailureState $(, $arg::Borrowed<'a>)*) -> u32) -> NativeCallable<Self> {
                NativeCallable::new(Self { function, result: NativeResult::Unit })
            }
            /// Generate a C status entry for a stateless Rust function returning Result<(), SourceFailureKind>.
            pub fn from_rust<F>(function: F) -> NativeCallable<Self>
            where F: for<'a> Fn($($arg::Borrowed<'a>),*) -> Result<(), SourceFailureKind> + Copy + 'static {
                check_stateless_rust_function(function);
                #[allow(clippy::extra_unused_lifetimes)] // The zero-argument expansion has no input borrow.
                extern "C" fn entry<'a, $($arg: NativeArgument,)* F>(failure: &mut NativeFailureState $(, $value: $arg::Borrowed<'a>)*) -> u32
                where F: for<'b> Fn($($arg::Borrowed<'b>),*) -> Result<(), SourceFailureKind> + Copy + 'static {
                    // SAFETY: from_rust validated a live, stateless F before exposing this entry.
                    let function = unsafe { stateless_rust_function::<F>() };
                    failure.write_unit_result(function($($value),*))
                }
                Self::new(entry::<$($arg,)* F>)
            }
            /// Adapt a stateless Rust function returning `()` to the fallible ABI.
            /// Normal return reports success; this does not catch Rust panics.
            pub fn from_rust_infallible<F>(function: F) -> NativeCallable<Self>
            where F: for<'a> Fn($($arg::Borrowed<'a>),*) + Copy + 'static {
                Self::from_rust(move |$($value: $arg::Borrowed<'_>),*| {
                    function($($value),*);
                    Ok(())
                })
            }
            /// Generate a C failure entry for a stateless Rust function that cannot succeed.
            /// `Never` encodes the source-level `never` result without output storage.
            pub fn from_rust_never<F>(function: F) -> NativeCallable<Self>
            where F: for<'a> Fn($($arg::Borrowed<'a>),*) -> Result<Never, SourceFailureKind> + Copy + 'static {
                check_stateless_rust_function(function);
                #[allow(clippy::extra_unused_lifetimes)] // The zero-argument expansion has no input borrow.
                extern "C" fn entry<'a, $($arg: NativeArgument,)* F>(failure: &mut NativeFailureState $(, $value: $arg::Borrowed<'a>)*) -> u32
                where F: for<'b> Fn($($arg::Borrowed<'b>),*) -> Result<Never, SourceFailureKind> + Copy + 'static {
                    // SAFETY: from_rust_never validated a live, stateless F before exposing this entry.
                    let function = unsafe { stateless_rust_function::<F>() };
                    match function($($value),*) {
                        Ok(never) => match never {},
                        Err(error) => failure.fail(error),
                    }
                }
                Self::new_never(entry::<$($arg,)* F>)
            }
            /// Register a source-level `never` entry using status-only failure transport.
            ///
            /// A successful return is rejected by the executor.
            pub fn new_never(function: for<'a> extern "C" fn(&mut NativeFailureState $(, $arg::Borrowed<'a>)*) -> u32) -> NativeCallable<Self> {
                NativeCallable::new(Self { function, result: NativeResult::Never })
            }
        }
        impl<$($arg: NativeArgument),*> sealed::Entry for $unit<$($arg),*> {}
        impl<$($arg: NativeArgument),*> EntryFunction for $unit<$($arg),*> {
            fn entry(&self) -> NativeEntry {
                NativeEntry { address: self.function as *const (), signature: NativeSignature {
                    failure: NativeFailureConvention::StatusWithState,
                    parameters: vec![$($arg::parameter()),*], result: self.result,
                } }
            }
            fn invoke(&self, args: &[ValOrMut], ctx: &mut EvalCtx) -> EvalControlFlowResult {
                let _ = args;
                $(let mut $value = $arg::extract(&args[$index], ctx).map_err(RuntimeError::new_native)?;)*
                assert!(ctx.native_failure.is_empty(), "native call started with an unhandled failure");
                // SAFETY: all lookups have finished; argument pointees remain live and obey
                // Ferlium borrowing. The failure cell is separate from argument storage.
                let status = (self.function)(&mut ctx.native_failure $(, unsafe { $arg::borrow(&mut $value) })*);
                ctx.native_failure.finish(status)?;
                assert_ne!(self.result, NativeResult::Never, "never native entry returned success");
                cont(Value::unit())
            }
        }

        pub struct $output<$($arg: NativeArgument,)* O: NativeStoredResult>(
            for<'a> extern "C" fn(&mut NativeFailureState, $($arg::Borrowed<'a>,)* &mut MaybeUninit<O>) -> u32
        );
        impl<$($arg: NativeArgument,)* O: NativeStoredResult> Clone for $output<$($arg,)* O> {
            fn clone(&self) -> Self { Self(self.0) }
        }
        impl<$($arg: NativeArgument,)* O: NativeStoredResult> $output<$($arg,)* O> {
            /// Register a status-returning entry with leading failure state and trailing output.
            ///
            /// # Safety
            /// Success must leave one initialized output (finite for Float). Failure must leave
            /// no live output, cleaning any partial construction before returning.
            pub unsafe fn new(function: for<'a> extern "C" fn(&mut NativeFailureState, $($arg::Borrowed<'a>,)* &mut MaybeUninit<O>) -> u32) -> NativeCallable<Self> {
                NativeCallable::new(Self(function))
            }

            /// Generate a C status/output entry for a stateless Rust function returning Result<O, SourceFailureKind>.
            pub fn from_rust<F>(function: F) -> NativeCallable<Self>
            where F: for<'a> Fn($($arg::Borrowed<'a>),*) -> Result<O, SourceFailureKind> + Copy + 'static {
                check_stateless_rust_function(function);
                #[allow(clippy::extra_unused_lifetimes)] // The zero-argument expansion has no input borrow.
                extern "C" fn entry<'a, $($arg: NativeArgument,)* O: NativeStoredResult, F>(failure: &mut NativeFailureState, $($value: $arg::Borrowed<'a>,)* output: &mut MaybeUninit<O>) -> u32
                where F: for<'b> Fn($($arg::Borrowed<'b>),*) -> Result<O, SourceFailureKind> + Copy + 'static {
                    // SAFETY: from_rust validated a live, stateless F before exposing this entry.
                    let function = unsafe { stateless_rust_function::<F>() };
                    failure.write_result(function($($value),*), output)
                }
                // SAFETY: write_result initializes output exactly on success.
                unsafe { Self::new(entry::<$($arg,)* O, F>) }
            }

            /// Adapt a stateless Rust function returning `O` to the fallible ABI.
            /// Normal return initializes the output and reports success; Rust panics are not caught.
            pub fn from_rust_infallible<F>(function: F) -> NativeCallable<Self>
            where F: for<'a> Fn($($arg::Borrowed<'a>),*) -> O + Copy + 'static {
                Self::from_rust(move |$($value: $arg::Borrowed<'_>),*| Ok(function($($value),*)))
            }
        }
        impl<$($arg: NativeArgument,)* O: NativeStoredResult> sealed::Entry for $output<$($arg,)* O> {}
        impl<$($arg: NativeArgument,)* O: NativeStoredResult> EntryFunction for $output<$($arg,)* O> {
            fn entry(&self) -> NativeEntry {
                NativeEntry { address: self.0 as *const (), signature: NativeSignature {
                    failure: NativeFailureConvention::StatusWithState,
                    parameters: vec![$($arg::parameter()),*], result: NativeResult::Output(O::layout()),
                } }
            }
            fn invoke(&self, args: &[ValOrMut], ctx: &mut EvalCtx) -> EvalControlFlowResult {
                let _ = args;
                $(let mut $value = $arg::extract(&args[$index], ctx).map_err(RuntimeError::new_native)?;)*
                let mut output = MaybeUninit::uninit();
                assert!(ctx.native_failure.is_empty(), "native call started with an unhandled failure");
                // SAFETY: lookups have finished and arguments satisfy Ferlium borrowing. Both
                // the invocation's failure cell and fresh output storage are disjoint from them.
                let status = (self.0)(&mut ctx.native_failure, $(unsafe { $arg::borrow(&mut $value) },)* &mut output);
                ctx.native_failure.finish(status)?;
                // SAFETY: only success reaches here, and registration guarantees initialization.
                cont(NativeStoredResult::boxed(unsafe { output.assume_init() }))
            }
        }
    };
}

fallible_entries!(NativeFallibleFn0, NativeFallibleOutFn0);
fallible_entries!(NativeFallibleFn1, NativeFallibleOutFn1, A: a: 0);
fallible_entries!(NativeFallibleFn2, NativeFallibleOutFn2, A: a: 0, B: b: 1);
fallible_entries!(NativeFallibleFn3, NativeFallibleOutFn3, A: a: 0, B: b: 1, C: c: 2);

// Generate only type aliases, not adapters: N = scalar value, R = shared, M = mutable.
// Fixing the input markers exposes concrete argument types to Rust's type inference.
macro_rules! input_aliases {
    (@expand $arity:tt [$($code:ident $marker:ident $ty:ident,)*] []) => {
        paste::paste! {
            pub type [<NativeFn $($code)*>]<$($ty,)* R> =
                [<NativeFn $arity>]<$($marker<$ty>,)* R>;
            pub type [<NativeOutFn $($code)*>]<$($ty,)* O> =
                [<NativeOutFn $arity>]<$($marker<$ty>,)* O>;
            pub type [<NativeFallibleFn $($code)*>]<$($ty),*> =
                [<NativeFallibleFn $arity>]<$($marker<$ty>),*>;
            pub type [<NativeFallibleOutFn $($code)*>]<$($ty,)* O> =
                [<NativeFallibleOutFn $arity>]<$($marker<$ty>,)* O>;
        }
    };
    (@expand $arity:tt [$($done:tt)*] [$next:ident $($rest:ident)*]) => {
        input_aliases!(@expand $arity [$($done)* N ByValue $next,] [$($rest)*]);
        input_aliases!(@expand $arity [$($done)* R Shared $next,] [$($rest)*]);
        input_aliases!(@expand $arity [$($done)* M Mutable $next,] [$($rest)*]);
    };
}
input_aliases!(@expand 1 [] [A]);
input_aliases!(@expand 2 [] [A B]);
input_aliases!(@expand 3 [] [A B C]);

pub type NativeOptionalFnN<A, O> = NativeOptionalFn1<ByValue<A>, O>;
pub type NativeOptionalFnR<A, O> = NativeOptionalFn1<Shared<A>, O>;
pub type NativeOptionalFnM<A, O> = NativeOptionalFn1<Mutable<A>, O>;

/// Consuming C entry for the compiler-owned native `Value::drop(&mut T)` method.
///
/// Before invoking the entry, the boxed adapter invalidates the target slot and detaches its
/// payload, ending the slot borrow. A re-entrant observer cannot recover or re-drop that payload
/// through the original place. Reclamation sees `Uninit` and cannot destroy it a second time.
pub struct NativeDropFn<T: 'static>(unsafe extern "C" fn(*mut T));

impl<T: 'static> Clone for NativeDropFn<T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T: 'static> NativeDropFn<T> {
    /// Register a destructor without changing Ferlium's parameter type system.
    ///
    /// # Safety
    /// The entry must destroy exactly one initialized pointee without freeing its storage or
    /// retaining the pointer. Register it only as `Value::drop` for T: ordinary mutable arguments
    /// must remain initialized after a call. Rust panics must not unwind across the C boundary.
    pub unsafe fn new(function: unsafe extern "C" fn(*mut T)) -> NativeCallable<Self> {
        NativeCallable::new(Self(function))
    }
}

impl<T: 'static> sealed::Entry for NativeDropFn<T> {}
impl<T: 'static> EntryFunction for NativeDropFn<T> {
    fn entry(&self) -> NativeEntry {
        NativeEntry {
            address: self.0 as *const (),
            signature: NativeSignature {
                failure: NativeFailureConvention::Infallible,
                parameters: vec![NativeParameter::Consuming(NativeLayout::of::<T>())],
                result: NativeResult::Unit,
            },
        }
    }

    fn invoke(&self, args: &[ValOrMut], ctx: &mut EvalCtx) -> EvalControlFlowResult {
        let mut storage =
            take_native_drop_target::<T>(&args[0], ctx).map_err(RuntimeError::new_native)?;
        // SAFETY: the payload is initialized, aligned, exclusively owned and detached from ctx.
        // Registration guarantees consumption without freeing this stack storage.
        unsafe { (self.0)(storage.as_mut_ptr()) };
        cont(Value::unit())
    }
}

/// Detach before running any destructor. The returned storage owns the payload but deliberately
/// has no drop glue, so even a partially unwound Rust destructor cannot be attempted again.
fn take_native_drop_target<T: 'static>(
    arg: &ValOrMut,
    ctx: &mut EvalCtx,
) -> Result<MaybeUninit<T>, SourceFailureKind> {
    let target = arg.as_place().target_mut(ctx)?;
    assert!(
        target
            .as_native()
            .is_some_and(|native| NativeValue::as_any(native.as_ref()).is::<T>()),
        "native drop target must contain an initialized {}",
        std::any::type_name::<T>(),
    );
    let value = std::mem::replace(target, Value::uninit());
    let native = value
        .into_native()
        .expect("validated native drop target")
        .into_any()
        .downcast::<T>()
        .expect("validated native drop type");
    // Moving out of the box also reclaims its allocation, without destroying its payload.
    Ok(MaybeUninit::new(*native))
}

/// Define a small C entry inline when adapting a Rust operation. `-> out T` writes the
/// Rust expression into trailing result storage; ordinary `-> T` returns a scalar or unit.
/// The body executes inside the C boundary and must not unwind.
#[macro_export]
macro_rules! native_fn {
    (($($name:ident : $ty:ty),* $(,)?) -> fallible out $result:ty $body:block) => {{
        extern "C" fn entry(failure: &mut $crate::hir::native_functions::NativeFailureState, $($name: $ty,)* output: &mut ::std::mem::MaybeUninit<$result>) -> u32 {
            #[allow(clippy::redundant_closure_call)]
            let value: Result<$result, $crate::compiler::error::SourceFailureKind> = (|| $body)();
            failure.write_result(value, output)
        }
        // SAFETY: write_result initializes output exactly on success.
        unsafe { $crate::native_fn!(@fallible entry; $($ty),*) }
    }};
    (@fallible $entry:ident;) => { $crate::hir::native_functions::NativeFallibleOutFn0::new($entry) };
    (@fallible $entry:ident; $a:ty) => { $crate::hir::native_functions::NativeFallibleOutFn1::<$a, _>::new($entry) };
    (@fallible $entry:ident; $a:ty, $b:ty) => { $crate::hir::native_functions::NativeFallibleOutFn2::<$a, $b, _>::new($entry) };
    (@fallible $entry:ident; $a:ty, $b:ty, $c:ty) => { $crate::hir::native_functions::NativeFallibleOutFn3::<$a, $b, $c, _>::new($entry) };
    (($($name:ident : $ty:ty),* $(,)?) -> out $result:ty $body:block) => {{
        extern "C" fn entry($($name: $ty,)* output: &mut ::std::mem::MaybeUninit<$result>) {
            #[allow(clippy::redundant_closure_call)]
            let value: $result = (|| $body)();
            output.write(value);
        }
        // SAFETY: the generated entry writes exactly one result before returning.
        unsafe { $crate::native_fn!(@out entry; $($ty),*) }
    }};
    (($($name:ident : $ty:ty),* $(,)?) -> $result:ty $body:block) => {{
        extern "C" fn entry($($name: $ty),*) -> $result { $body }
        $crate::native_fn!(@direct entry; $($ty),*)
    }};
    (@out $entry:ident;) => { $crate::hir::native_functions::NativeOutFn0::new($entry) };
    (@out $entry:ident; $a:ty) => { $crate::hir::native_functions::NativeOutFn1::<$a, _>::new($entry) };
    (@out $entry:ident; $a:ty, $b:ty) => { $crate::hir::native_functions::NativeOutFn2::<$a, $b, _>::new($entry) };
    (@out $entry:ident; $a:ty, $b:ty, $c:ty) => { $crate::hir::native_functions::NativeOutFn3::<$a, $b, $c, _>::new($entry) };
    (@direct $entry:ident;) => { $crate::hir::native_functions::NativeFn0::new($entry) };
    (@direct $entry:ident; $a:ty) => { $crate::hir::native_functions::NativeFn1::<$a, _>::new($entry) };
    (@direct $entry:ident; $a:ty, $b:ty) => { $crate::hir::native_functions::NativeFn2::<$a, $b, _>::new($entry) };
    (@direct $entry:ident; $a:ty, $b:ty, $c:ty) => { $crate::hir::native_functions::NativeFn3::<$a, $b, $c, _>::new($entry) };
}

/// Store an optional payload, leaving output untouched on `None`.
pub fn write_native_optional_output<T>(value: Option<T>, output: &mut MaybeUninit<T>) -> bool {
    match value {
        Some(value) => {
            output.write(value);
            true
        }
        None => false,
    }
}

/// Unary C entry returning presence and writing an optional payload into trailing storage.
pub struct NativeOptionalFn1<A: NativeArgument, O: NativeStoredResult> {
    function: for<'a> extern "C" fn(A::Borrowed<'a>, &mut MaybeUninit<O>) -> bool,
    result_ty: Type,
}
impl<A: NativeArgument, O: NativeStoredResult> Clone for NativeOptionalFn1<A, O> {
    fn clone(&self) -> Self {
        Self {
            function: self.function,
            result_ty: self.result_ty,
        }
    }
}
impl<A: NativeArgument, O: NativeStoredResult> NativeOptionalFn1<A, O> {
    /// Generate a C presence/output entry for a stateless Rust function returning Option<O>.
    pub fn from_rust<F>(function: F, result_type: Type) -> NativeCallable<Self>
    where
        F: for<'a> Fn(A::Borrowed<'a>) -> Option<O> + Copy + 'static,
    {
        check_stateless_rust_function(function);
        extern "C" fn entry<'a, A: NativeArgument, O: NativeStoredResult, F>(
            value: A::Borrowed<'a>,
            output: &mut MaybeUninit<O>,
        ) -> bool
        where
            F: for<'b> Fn(A::Borrowed<'b>) -> Option<O> + Copy + 'static,
        {
            // SAFETY: from_rust validated a live, stateless F before exposing this entry.
            let function = unsafe { stateless_rust_function::<F>() };
            write_native_optional_output(function(value), output)
        }
        // SAFETY: the generated entry initializes output exactly when it returns true.
        unsafe { Self::new(entry::<A, O, F>, result_type) }
    }

    /// Registration checks that `result_ty` resolves to `None(()) | Some((O,))`.
    ///
    /// # Safety
    /// The entry must initialize output exactly when returning true, and leave no live output
    /// on false.
    pub unsafe fn new(
        function: for<'a> extern "C" fn(A::Borrowed<'a>, &mut MaybeUninit<O>) -> bool,
        result_ty: Type,
    ) -> NativeCallable<Self> {
        NativeCallable::new(Self {
            function,
            result_ty,
        })
    }
}
impl<A: NativeArgument, O: NativeStoredResult> sealed::Entry for NativeOptionalFn1<A, O> {}
impl<A: NativeArgument, O: NativeStoredResult> EntryFunction for NativeOptionalFn1<A, O> {
    fn entry(&self) -> NativeEntry {
        NativeEntry {
            address: self.function as *const (),
            signature: NativeSignature {
                failure: NativeFailureConvention::Infallible,
                parameters: vec![A::parameter()],
                result: NativeResult::Optional {
                    payload: O::layout(),
                    ty: self.result_ty,
                },
            },
        }
    }
    fn invoke(&self, args: &[ValOrMut], ctx: &mut EvalCtx) -> EvalControlFlowResult {
        let mut arg = A::extract(&args[0], ctx).map_err(RuntimeError::new_native)?;
        let mut output = MaybeUninit::uninit();
        // SAFETY: all lookups are complete and the guarded argument remains live and borrowed.
        let present = (self.function)(unsafe { A::borrow(&mut arg) }, &mut output);
        cont(if present {
            // SAFETY: registration guarantees initialization exactly on true.
            let value = NativeStoredResult::boxed(unsafe { output.assume_init() });
            Value::tuple_variant(ustr::ustr("Some"), [value])
        } else {
            Value::unit_variant(ustr::ustr("None"))
        })
    }
}

/// Define a C optional entry from a Rust operation returning `Option<T>`.
#[macro_export]
macro_rules! native_optional_entry {
    ($(#[$meta:meta])* $vis:vis fn $entry:ident($($arg:ident : $ty:ty),* $(,)?) -> $payload:ty = $implementation:path) => {
        $(#[$meta])* $vis extern "C" fn $entry($($arg: $ty,)* output: &mut ::std::mem::MaybeUninit<$payload>) -> bool {
            $crate::hir::native_functions::write_native_optional_output($implementation($($arg),*), output)
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession,
        eval::ControlFlow,
        hir::value::NativeValueType,
        module::{Module, ModuleId, id::Id},
        std::math::int_type,
        types::effects::{effect, no_effects},
    };
    use std::{cell::Cell, rc::Rc};

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn native_drop_consumes_the_slot_before_storage_reclamation() {
        use std::{cell::Cell, rc::Rc};

        #[derive(Debug)]
        struct DropTracked(Rc<Cell<usize>>);
        impl NativeValueType for DropTracked {}
        impl Drop for DropTracked {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }

        let count = Rc::new(Cell::new(0));
        let session = CompilerSession::new_empty_for_tests();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        ctx.environment.push(ValOrMut::Val(Value::tuple([
            Value::native(DropTracked(count.clone())),
            Value::native(42isize),
        ])));
        let function = crate::std::value::native_value_drop_function::<DropTracked>();
        let entry = function.native_entry().expect("typed destructor entry");
        assert_eq!(
            entry.signature.parameters,
            [NativeParameter::Consuming(NativeLayout::of::<DropTracked>())],
        );
        assert_eq!(entry.signature.result, NativeResult::Unit);
        assert_eq!(
            function.runtime_argument_passing(),
            Some(&[ArgConvention::MutableRef][..]),
        );
        let place = crate::eval::Place {
            root: 0,
            path: vec![0],
        };
        function
            .call(vec![ValOrMut::Mut(place.clone())], &mut ctx, &[])
            .unwrap()
            .into_value()
            .discard_storage();

        assert_eq!(count.get(), 1, "destruction must run during Value::drop");
        assert!(matches!(place.target_mut(&mut ctx).unwrap(), Value::Uninit));
        let sibling = crate::eval::Place {
            root: 0,
            path: vec![1],
        };
        assert_eq!(
            sibling.target_ref(&ctx).unwrap().as_primitive_ty::<isize>(),
            Some(&42),
        );
        ctx.environment.pop().unwrap().discard_storage();
        assert_eq!(count.get(), 1, "storage reclamation must not destroy twice");
    }

    #[test]
    #[should_panic(expected = "native drop target must contain an initialized")]
    fn native_drop_diagnoses_an_uninitialized_target() {
        let session = CompilerSession::new_empty_for_tests();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        ctx.environment.push(ValOrMut::Val(Value::uninit()));
        let function = crate::std::value::native_value_drop_function::<isize>();
        let _ = function.call(
            vec![ValOrMut::Mut(crate::eval::Place {
                root: 0,
                path: vec![],
            })],
            &mut ctx,
            &[],
        );
    }

    #[test]
    #[cfg(all(not(target_arch = "wasm32"), panic = "unwind"))]
    fn native_drop_unwinding_does_not_repeat_destruction() {
        use std::{cell::Cell, panic::AssertUnwindSafe, rc::Rc};

        #[derive(Debug)]
        struct PanickingDrop(Rc<Cell<usize>>);
        impl NativeValueType for PanickingDrop {}
        impl Drop for PanickingDrop {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
                panic!("test native destructor panic");
            }
        }

        let count = Rc::new(Cell::new(0));
        let session = CompilerSession::new_empty_for_tests();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        ctx.environment
            .push(ValOrMut::Val(Value::native(PanickingDrop(count.clone()))));

        let place = crate::eval::Place {
            root: 0,
            path: vec![],
        };
        let mut storage =
            take_native_drop_target::<PanickingDrop>(&ValOrMut::Mut(place.clone()), &mut ctx)
                .unwrap();
        assert!(matches!(place.target_mut(&mut ctx).unwrap(), Value::Uninit));
        // Test Rust unwinding below the non-unwinding C boundary. The actual C entry's
        // abort behavior is checked separately in a subprocess.
        let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
            // SAFETY: detached storage contains one live payload; never retry its destruction.
            unsafe { storage.assume_init_drop() };
        }));
        assert!(result.is_err());
        assert_eq!(count.get(), 1);
        assert_eq!(
            Rc::strong_count(&count),
            1,
            "Rust must still drop the fields"
        );
        assert!(matches!(place.target_mut(&mut ctx).unwrap(), Value::Uninit));
        ctx.environment.pop().unwrap().discard_storage();
        assert_eq!(
            count.get(),
            1,
            "reclamation must not retry a panicking drop"
        );
    }

    #[test]
    #[cfg(all(unix, not(target_arch = "wasm32")))]
    fn native_drop_panics_abort_at_c_boundary() {
        use std::{os::unix::process::ExitStatusExt, process::Command};

        const CHILD: &str = "FERLIUM_NATIVE_DROP_ABORT_CHILD";
        if std::env::var_os(CHILD).is_some() {
            #[derive(Debug)]
            struct Field;
            impl Drop for Field {
                fn drop(&mut self) {
                    eprintln!("native destructor field reclaimed");
                }
            }
            #[derive(Debug)]
            struct PanickingDrop {
                _field: Field,
            }
            impl NativeValueType for PanickingDrop {}
            impl Drop for PanickingDrop {
                fn drop(&mut self) {
                    panic!("native C destructor test panic");
                }
            }
            let session = CompilerSession::new_empty_for_tests();
            let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
            ctx.environment
                .push(ValOrMut::Val(Value::native(PanickingDrop {
                    _field: Field,
                })));
            let function = crate::std::value::native_value_drop_function::<PanickingDrop>();
            let _ = function.call(
                vec![ValOrMut::Mut(crate::eval::Place {
                    root: 0,
                    path: vec![],
                })],
                &mut ctx,
                &[],
            );
            return;
        }

        // Disable core files for this deliberately aborting child; arguments are passed literally.
        let (_, module) = module_path!().split_once("::").unwrap();
        let test_name = format!("{module}::native_drop_panics_abort_at_c_boundary");
        let output = Command::new("sh")
            .args(["-c", "ulimit -c 0; exec \"$@\"", "native-drop-abort-test"])
            .arg(std::env::current_exe().unwrap())
            .args(["--exact", &test_name, "--nocapture"])
            .env(CHILD, "1")
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.signal().is_some(),
            "expected abort, got {}: {stderr}",
            output.status
        );
        assert!(
            stderr.contains("native C destructor test panic"),
            "{stderr}"
        );
        // With unwinding enabled, Rust cleans the fields before reaching the aborting C boundary.
        #[cfg(panic = "unwind")]
        assert!(
            stderr.contains("native destructor field reclaimed"),
            "{stderr}"
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn typed_native_clone_uses_concrete_transport() {
        use crate::std::value::native_value_clone_function;
        let cases = [
            (
                native_value_clone_function::<bool>(),
                Value::native(true),
                NativeParameter::Scalar(NativeLayout::of::<bool>(), NativeScalar::Bool),
                NativeResult::Scalar(NativeLayout::of::<bool>(), NativeScalar::Bool),
            ),
            (
                native_value_clone_function::<isize>(),
                Value::native(42isize),
                NativeParameter::Scalar(NativeLayout::of::<isize>(), NativeScalar::Int),
                NativeResult::Scalar(NativeLayout::of::<isize>(), NativeScalar::Int),
            ),
            (
                native_value_clone_function::<Float>(),
                Value::native(Float::new(1.25).unwrap()),
                NativeParameter::Scalar(NativeLayout::of::<Float>(), NativeScalar::Float),
                NativeResult::Scalar(NativeLayout::of::<Float>(), NativeScalar::Float),
            ),
            (
                native_value_clone_function::<()>(),
                Value::unit(),
                NativeParameter::Shared(NativeLayout::of::<()>()),
                NativeResult::Unit,
            ),
        ];
        let session = CompilerSession::new_empty_for_tests();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        for (function, value, parameter, result) in cases {
            let entry = function.native_entry().unwrap();
            assert_eq!(entry.signature.parameters, [parameter]);
            assert_eq!(entry.signature.result, result);
            ctx.environment.push(ValOrMut::Val(value));
            let arg = ValOrMut::Mut(crate::eval::Place {
                root: 0,
                path: vec![],
            });
            let value = function
                .call(vec![arg], &mut ctx, &[])
                .unwrap()
                .into_value();
            assert_eq!(
                function::literal_of_trivial_copy_native(&value).unwrap(),
                function::literal_of_trivial_copy_native(ctx.environment[0].as_val().unwrap())
                    .unwrap(),
            );
            value.discard_storage();
            ctx.environment.pop().unwrap().discard_storage();
        }
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn infallible_rust_bodies_preserve_the_fallible_abi() {
        use crate::std::string::String;

        let mut failure = NativeFailureState::default();
        let unit = NativeFallibleFn0::from_rust_infallible(|| ());
        assert_eq!(
            unit.entry.signature.failure,
            NativeFailureConvention::StatusWithState
        );
        assert_eq!(unit.entry.signature.result, NativeResult::Unit);
        assert_eq!((unit.function.function)(&mut failure), 0);

        fn assign(target: &mut isize, source: &isize) {
            *target = *source;
        }
        let assign = NativeFallibleFnMR::from_rust_infallible(assign);
        let mut target = 0isize;
        assert_eq!(
            (assign.function.function)(&mut failure, &mut target, &42),
            0
        );
        assert_eq!(target, 42);

        let constant = NativeFallibleOutFn0::from_rust_infallible(|| 17isize);
        let mut scalar_output = MaybeUninit::uninit();
        assert_eq!((constant.function.0)(&mut failure, &mut scalar_output), 0);
        // SAFETY: the adapter reported success and initialized the output.
        assert_eq!(unsafe { scalar_output.assume_init() }, 17);

        let clone = NativeFallibleOutFnR::from_rust_infallible(String::clone);
        assert_eq!(
            clone.entry.signature.failure,
            NativeFailureConvention::StatusWithState
        );
        assert_eq!(
            clone.entry.signature.result,
            NativeResult::Output(NativeLayout::of::<String>())
        );
        let input = String::new("payload");
        let mut output = MaybeUninit::uninit();
        assert_eq!((clone.function.0)(&mut failure, &input, &mut output), 0);
        // SAFETY: the adapter reported success and initialized the output.
        let result = unsafe { output.assume_init() };
        assert_eq!(result, input);

        fn assign_sum(target: &mut isize, source: &isize, offset: isize) -> isize {
            *target = source.wrapping_add(offset);
            *target
        }
        let sum = NativeFallibleOutFnMRN::from_rust_infallible(assign_sum);
        let mut output = MaybeUninit::uninit();
        assert_eq!(
            (sum.function.0)(&mut failure, &mut target, &40, 2, &mut output),
            0
        );
        // SAFETY: the adapter reported success and initialized the output.
        assert_eq!(unsafe { output.assume_init() }, 42);
        assert_eq!(target, 42);
        assert!(failure.is_empty());

        // The interpreter marshals through the same entry and receives an owned result.
        let session = CompilerSession::new_empty_for_tests();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        let result = clone
            .call(
                vec![ValOrMut::Val(Value::native(input.clone()))],
                &mut ctx,
                &[],
            )
            .unwrap()
            .into_value();
        assert_eq!(result.into_primitive_ty::<String>().unwrap(), input);
        assert!(ctx.native_failure.is_empty());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn native_rust_function_items_produce_independent_c_entries() {
        let and = NativeFnNN::from_rust(<bool as std::ops::BitAnd>::bitand);
        let xor = NativeFnNN::from_rust(<bool as std::ops::BitXor>::bitxor);
        // Invoke the actual typed C pointers without an interpreter or a callback registry.
        assert!((and.function.0)(true, true));
        assert!(!(xor.function.0)(true, true));
        assert_eq!(and.entry.address(), and.function.0 as *const ());

        fn assign(target: &mut isize, source: &isize) {
            *target = *source;
        }
        let assign = NativeFnMR::from_rust(assign);
        let mut target = 0;
        (assign.function.0)(&mut target, &42);
        assert_eq!(target, 42);
        assert_eq!(
            assign.entry.signature.parameters,
            [
                NativeParameter::Mutable(NativeLayout::of::<isize>()),
                NativeParameter::Shared(NativeLayout::of::<isize>()),
            ]
        );

        let checked = NativeFallibleFnN::from_rust(|succeed: bool| {
            if succeed {
                Ok(())
            } else {
                Err(SourceFailureKind::Aborted(None))
            }
        });
        let mut failure = NativeFailureState::default();
        assert_eq!((checked.function.function)(&mut failure, true), 0);
        assert!(failure.is_empty());
        assert_ne!((checked.function.function)(&mut failure, false), 0);
        assert_eq!(failure.take(), Some(SourceFailureKind::Aborted(None)));

        fn reject(value: &isize) -> Result<Never, SourceFailureKind> {
            Err(SourceFailureKind::InvalidArgument(value.to_string()))
        }
        let never = NativeFallibleFnR::from_rust_never(reject);
        assert_eq!(never.entry.signature.result, NativeResult::Never);
        assert_ne!((never.function.function)(&mut failure, &42), 0);
        assert_eq!(
            failure.take(),
            Some(SourceFailureKind::InvalidArgument("42".into()))
        );
    }

    extern "C" fn identity(value: isize) -> isize {
        value
    }
    extern "C" fn double(value: f64) -> Float {
        Float::new_saturating(value * 2.0)
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn native_float_entries_share_f64_abi() {
        extern "C" fn float_identity(value: Float) -> Float {
            value
        }
        extern "C" fn raw_identity(value: f64) -> Float {
            Float::new(value).expect("the adapter supplies a finite float")
        }
        let raw = NativeFnN::new(raw_identity);
        let session = CompilerSession::new_empty_for_tests();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        for function in [
            NativeFnN::new(float_identity),
            NativeFnN::from_rust(std::convert::identity::<Float>),
        ] {
            assert_eq!(function.entry.signature, raw.entry.signature);
            // SAFETY: Float and NotNan<f64> are both repr(transparent), preserving f64's
            // calling ABI. All inputs below are finite and satisfy Float's invariant.
            let call = unsafe {
                std::mem::transmute::<extern "C" fn(Float) -> Float, extern "C" fn(f64) -> f64>(
                    std::hint::black_box(function.function.0),
                )
            };
            for value in [-0.0, 1.25, f64::MIN, f64::MAX] {
                assert_eq!(call(value).to_bits(), value.to_bits());
                let result = function
                    .call(
                        vec![ValOrMut::Val(Value::native(Float::new(value).unwrap()))],
                        &mut ctx,
                        &[],
                    )
                    .unwrap()
                    .into_value();
                assert_eq!(
                    result
                        .as_primitive_ty::<Float>()
                        .unwrap()
                        .into_inner()
                        .to_bits(),
                    value.to_bits()
                );
                result.discard_storage();
            }
        }

        fn checked(value: Float) -> Result<Float, SourceFailureKind> {
            if value.into_inner() < 0.0 {
                Err(SourceFailureKind::InvalidArgument("negative float".into()))
            } else {
                Ok(value)
            }
        }
        let checked = NativeFallibleOutFnN::from_rust(checked);
        assert_eq!(
            checked.entry.signature.failure,
            NativeFailureConvention::StatusWithState
        );
        assert_eq!(
            checked.entry.signature.result,
            NativeResult::Output(NativeLayout::of::<Float>())
        );
        type FloatEntry =
            extern "C" fn(&mut NativeFailureState, Float, &mut MaybeUninit<Float>) -> u32;
        type RawEntry = extern "C" fn(&mut NativeFailureState, f64, &mut MaybeUninit<f64>) -> u32;
        // SAFETY: the scalar input has the same ABI, and MaybeUninit<Float> has the same
        // layout as MaybeUninit<f64>. The input is finite; the output holds a Float on success.
        let call = unsafe {
            std::mem::transmute::<FloatEntry, RawEntry>(std::hint::black_box(checked.function.0))
        };
        let mut failure = NativeFailureState::default();
        let mut output = MaybeUninit::new(7.0);
        assert_ne!(call(&mut failure, -1.0, &mut output), 0);
        assert_eq!(
            failure.take(),
            Some(SourceFailureKind::InvalidArgument("negative float".into()))
        );
        // SAFETY: failure preserves the initialized sentinel.
        assert_eq!(unsafe { output.assume_init() }, 7.0);
        assert_eq!(call(&mut failure, 1.25, &mut output), 0);
        assert!(failure.is_empty());
        // SAFETY: success initialized the output with a finite Float.
        assert_eq!(unsafe { output.assume_init() }, 1.25);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn typed_native_scalar_metadata_and_marshalling() {
        let session = CompilerSession::new_empty_for_tests();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        let integer = NativeFnN::new(identity);
        assert_eq!(
            integer.native_entry().unwrap().address,
            identity as *const ()
        );
        assert_eq!(
            integer.native_entry().unwrap().signature.parameters,
            [NativeParameter::Scalar(
                NativeLayout::of::<isize>(),
                NativeScalar::Int
            )]
        );
        let float = NativeFnN::new(double);
        assert_eq!(
            float.native_entry().unwrap().signature.parameters,
            [NativeParameter::Scalar(
                NativeLayout::of::<Float>(),
                NativeScalar::Float
            )]
        );
        let result = float
            .call(
                vec![ValOrMut::Val(Value::native(Float::new(1.25).unwrap()))],
                &mut ctx,
                &[],
            )
            .unwrap();
        let ControlFlow::Continue(value) = result else {
            panic!("native returned control flow")
        };
        assert_eq!(value.as_primitive_ty::<Float>().unwrap().into_inner(), 2.5);
        value.discard_storage();
    }

    #[derive(Clone, Debug)]
    struct Owned {
        text: String,
        drops: Rc<Cell<usize>>,
    }
    impl NativeValueType for Owned {}
    impl Drop for Owned {
        fn drop(&mut self) {
            self.drops.set(self.drops.get() + 1);
        }
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn native_adapter_borrows_disjoint_places_during_failure() {
        fn update(
            source: &Owned,
            left: &mut Owned,
            right: &mut Owned,
        ) -> Result<(), SourceFailureKind> {
            left.text.push_str(&source.text);
            right.text.push_str(&source.text);
            Err(SourceFailureKind::Aborted(None))
        }
        let session = CompilerSession::new_empty_for_tests();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        let drops = Rc::new(Cell::new(0));
        ctx.environment.push(ValOrMut::Val(Value::tuple(
            ["source", "left:", "right:"].map(|text| {
                Value::native(Owned {
                    text: text.into(),
                    drops: drops.clone(),
                })
            }),
        )));
        let place = |index: usize| crate::eval::Place {
            root: 0,
            path: vec![index as isize],
        };
        let function = NativeFallibleFnRMM::from_rust(update);
        let error = function
            .call(
                (0..3).map(|index| ValOrMut::Mut(place(index))).collect(),
                &mut ctx,
                &[],
            )
            .unwrap_err();
        assert_eq!(
            error.kind(),
            crate::compiler::error::RuntimeErrorKind::SourceFailure(SourceFailureKind::Aborted(
                None
            ),)
        );
        assert!(ctx.native_failure.is_empty());
        for (index, expected) in ["source", "left:source", "right:source"]
            .into_iter()
            .enumerate()
        {
            assert_eq!(
                place(index)
                    .target_ref(&ctx)
                    .unwrap()
                    .as_primitive_ty::<Owned>()
                    .unwrap()
                    .text,
                expected
            );
        }
        assert_eq!(drops.get(), 0);
        ctx.environment.pop().unwrap().discard_storage();
        assert_eq!(drops.get(), 3);
        assert_eq!(Rc::strong_count(&drops), 1);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn typed_native_output_and_argument_ownership() {
        for function in [
            crate::std::value::native_value_clone_function::<Owned>(),
            Box::new(NativeOutFnR::from_rust(Owned::clone)) as crate::hir::function::Function,
        ] {
            let session = CompilerSession::new_empty_for_tests();
            let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
            let drops = Rc::new(Cell::new(0));
            let input = Owned {
                text: "native storage".into(),
                drops: drops.clone(),
            };
            assert_eq!(
                function.native_entry().unwrap().signature.result,
                NativeResult::Output(NativeLayout::of::<Owned>())
            );
            let result = function
                .call(vec![ValOrMut::Val(Value::native(input))], &mut ctx, &[])
                .unwrap();
            assert_eq!(
                drops.get(),
                1,
                "owned call argument must be reclaimed after the entry returns"
            );
            let ControlFlow::Continue(value) = result else {
                panic!("native returned control flow")
            };
            assert_eq!(
                value.as_primitive_ty::<Owned>().unwrap().text,
                "native storage"
            );
            assert_eq!(Rc::strong_count(&drops), 2);
            value.discard_storage();
            assert_eq!(drops.get(), 2);
            assert_eq!(Rc::strong_count(&drops), 1);
        }
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn typed_native_contract_rejects_declaration_mismatches() {
        let function = NativeFnN::new(identity).description(["value"], "identity", no_effects());
        let signature = &function.code.native_entry().unwrap().signature;
        let mut definition = function.definition.clone();
        definition.ty_scheme.ty.args[0].mut_ty = MutType::mutable();
        assert!(
            signature
                .validate(&definition)
                .unwrap_err()
                .to_string()
                .contains("mutability")
        );
        definition = function.definition.clone();
        definition.ty_scheme.ty.ret = Type::primitive::<bool>();
        assert!(
            signature
                .validate(&definition)
                .unwrap_err()
                .to_string()
                .contains("result type")
        );
        definition = function.definition.clone();
        definition.ty_scheme.ty.effects = effect(PrimitiveEffect::Fallible);
        assert!(
            signature
                .validate(&definition)
                .unwrap_err()
                .to_string()
                .contains("source-failure")
        );
        definition = function.definition.clone();
        definition.ty_scheme.ty.args[0].ty = Type::variable_id(0);
        assert!(
            signature
                .validate(&definition)
                .unwrap_err()
                .to_string()
                .contains("closed")
        );
        definition = function.definition.clone();
        definition.ty_scheme.ty.effects = EffType::single_variable_id(0);
        assert_eq!(
            signature.validate(&definition),
            Err(NativeContractError::NotClosed)
        );
        assert_eq!(signature.result.ty(), int_type());
        let mut wrong_transport = signature.clone();
        wrong_transport.parameters[0] = NativeParameter::Shared(NativeLayout::of::<isize>());
        assert_eq!(
            wrong_transport.validate(&function.definition),
            Err(NativeContractError::ArgumentTransport { index: 0 })
        );
        wrong_transport = signature.clone();
        wrong_transport.result = NativeResult::Output(NativeLayout::of::<isize>());
        assert_eq!(
            wrong_transport.validate(&function.definition),
            Err(NativeContractError::ResultTransport)
        );
        wrong_transport = signature.clone();
        wrong_transport.parameters[0] = NativeParameter::Consuming(NativeLayout::of::<isize>());
        assert_eq!(
            wrong_transport.validate(&function.definition),
            Err(NativeContractError::ConsumingSignature)
        );
    }

    extern "C" fn checked_clone(
        failure: &mut NativeFailureState,
        source: &Owned,
        succeed: bool,
        output: &mut MaybeUninit<Owned>,
    ) -> u32 {
        let partial = source.clone();
        if succeed {
            output.write(partial);
            0
        } else {
            drop(partial);
            failure.fail(SourceFailureKind::InvalidArgument("clone rejected".into()))
        }
    }

    fn checked_clone_rust(source: &Owned, succeed: bool) -> Result<Owned, SourceFailureKind> {
        let partial = source.clone();
        if succeed {
            Ok(partial)
        } else {
            Err(SourceFailureKind::InvalidArgument("clone rejected".into()))
        }
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn native_failure_preserves_output_ownership_and_reuses_state() {
        for function in [
            // SAFETY: checked_clone initializes exactly on success and cleans partial output on failure.
            unsafe { NativeFallibleOutFnRN::new(checked_clone) },
            NativeFallibleOutFnRN::from_rust(checked_clone_rust),
        ] {
            let session = CompilerSession::new_empty_for_tests();
            let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
            let drops = Rc::new(Cell::new(0));
            let definition = function
                .clone()
                .description(
                    ["source", "succeed"],
                    "test",
                    effect(PrimitiveEffect::Fallible),
                )
                .definition;
            let signature = function.native_entry().unwrap().signature();
            assert_eq!(signature.failure, NativeFailureConvention::StatusWithState);
            let mut wrong = definition.clone();
            wrong.ty_scheme.ty.effects = no_effects();
            assert_eq!(
                signature.validate(&wrong),
                Err(NativeContractError::Fallibility)
            );
            for succeed in [false, true, false] {
                let before = drops.get();
                let input = Owned {
                    text: "payload".into(),
                    drops: drops.clone(),
                };
                let result = function.call(
                    vec![
                        ValOrMut::Val(Value::native(input)),
                        ValOrMut::Val(Value::native(succeed)),
                    ],
                    &mut ctx,
                    &[],
                );
                if succeed {
                    assert_eq!(
                        drops.get(),
                        before + 1,
                        "the input is reclaimed before returning"
                    );
                    let output = result.unwrap().into_value();
                    assert_eq!(output.as_primitive_ty::<Owned>().unwrap().text, "payload");
                    output.discard_storage();
                } else {
                    assert_eq!(
                        result.unwrap_err().kind(),
                        crate::compiler::error::RuntimeErrorKind::SourceFailure(
                            SourceFailureKind::InvalidArgument("clone rejected".into())
                        )
                    );
                }
                assert_eq!(drops.get(), before + 2);
                assert!(
                    ctx.native_failure.is_empty(),
                    "error ownership moved into RuntimeError"
                );
                assert_eq!(Rc::strong_count(&drops), 1);
            }
        }
    }

    extern "C" fn nested_state(
        failure: &mut NativeFailureState,
        expected: isize,
        output: &mut MaybeUninit<isize>,
    ) -> u32 {
        extern "C" fn inner(
            failure: &mut NativeFailureState,
            expected: isize,
            output: &mut MaybeUninit<isize>,
        ) -> u32 {
            let address = failure as *mut NativeFailureState as isize;
            if address == expected {
                output.write(42);
                0
            } else {
                failure.fail(SourceFailureKind::InvalidArgument(
                    "wrong failure state".into(),
                ))
            }
        }
        inner(failure, expected, output)
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn native_failure_state_is_shared_within_an_invocation_and_isolated_between_invocations() {
        let session = CompilerSession::new_empty_for_tests();
        let mut outer = EvalCtx::new(ModuleId::from_index(0), &session);
        let mut nested = EvalCtx::new(ModuleId::from_index(0), &session);
        let outer_address = &mut outer.native_failure as *mut NativeFailureState as isize;
        let nested_address = &mut nested.native_failure as *mut NativeFailureState as isize;
        assert_ne!(outer_address, nested_address);
        // SAFETY: nested_state initializes the scalar output exactly on success.
        let function = unsafe { NativeFallibleOutFnN::new(nested_state) };
        for (ctx, address) in [(&mut outer, outer_address), (&mut nested, nested_address)] {
            let result = function
                .call(vec![ValOrMut::Val(Value::native(address))], ctx, &[])
                .unwrap()
                .into_value();
            assert_eq!(result.as_primitive_ty::<isize>(), Some(&42));
            result.discard_storage();
        }
        outer.native_failure.fail(SourceFailureKind::Aborted(None));
        assert!(nested.native_failure.is_empty());
        assert_eq!(
            outer.native_failure.take(),
            Some(SourceFailureKind::Aborted(None))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn native_optional_managed_output_is_only_initialized_when_present() {
        extern "C" fn optional(source: &Owned, output: &mut MaybeUninit<Owned>) -> bool {
            write_native_optional_output((!source.text.is_empty()).then(|| source.clone()), output)
        }
        fn optional_rust(source: &Owned) -> Option<Owned> {
            (!source.text.is_empty()).then(|| source.clone())
        }
        let result_type = crate::std::option::option_type(Type::primitive::<Owned>());
        for function in [
            // SAFETY: optional writes exactly on Some through the shared helper.
            unsafe { NativeOptionalFnR::new(optional, result_type) },
            NativeOptionalFnR::from_rust(optional_rust, result_type),
        ] {
            let session = CompilerSession::new_empty_for_tests();
            let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
            let drops = Rc::new(Cell::new(0));
            for (text, expected_drops) in [("", 1), ("payload", 3)] {
                let input = Owned {
                    text: text.into(),
                    drops: drops.clone(),
                };
                let result = function
                    .call(vec![ValOrMut::Val(Value::native(input))], &mut ctx, &[])
                    .unwrap()
                    .into_value();
                result.discard_storage();
                assert_eq!(drops.get(), expected_drops);
                assert_eq!(Rc::strong_count(&drops), 1);
            }
        }
    }

    #[test]
    #[should_panic(expected = "invalid typed native registration")]
    fn typed_native_registration_checks_manually_declared_functions() {
        let mut module = Module::new(
            ModuleId::from_index(1),
            crate::module::Path::single_str("typed"),
        );
        let mut function =
            NativeFnN::new(identity).description(["value"], "identity", no_effects());
        function.definition.ty_scheme.ty.ret = Type::primitive::<bool>();
        module.add_function(ustr::ustr("wrong"), function);
    }
}
