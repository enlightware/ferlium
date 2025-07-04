// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{
    cell::RefCell,
    fmt::{self, Debug},
    marker::PhantomData,
    rc::{Rc, Weak},
};

use ustr::Ustr;

use ferlium_macros::declare_native_fn_aliases;

use crate::{
    effects::EffType,
    error::RuntimeError,
    eval::{EvalCtx, EvalResult, ValOrMut},
    format::FormatWith,
    ir::{self},
    module::{FmtWithModuleEnv, ModuleEnv, ModuleFunction},
    r#type::{FnType, Type},
    type_scheme::{PubTypeConstraint, TypeScheme},
    value::{NativeDisplay, Value},
};

/// The definition of a function, to be used in modules, traits and IDEs.
#[derive(Debug, Clone)]
pub struct FunctionDefinition {
    pub ty_scheme: TypeScheme<FnType>,
    pub arg_names: Vec<Ustr>,
    pub doc: Option<String>,
}

impl FunctionDefinition {
    pub fn new(ty_scheme: TypeScheme<FnType>, arg_names: Vec<Ustr>, doc: Option<String>) -> Self {
        FunctionDefinition {
            ty_scheme,
            arg_names,
            doc,
        }
    }

    pub fn new_infer_quantifiers<'s>(
        fn_ty: FnType,
        arg_names: impl IntoIterator<Item = &'s str>,
        doc: &str,
    ) -> Self {
        let arg_names = arg_names.into_iter().map(Ustr::from).collect();
        FunctionDefinition {
            ty_scheme: TypeScheme::new_infer_quantifiers(fn_ty),
            arg_names,
            doc: Some(String::from(doc)),
        }
    }

    pub fn new_infer_quantifiers_with_constraints<'s>(
        fn_ty: FnType,
        constraints: impl Into<Vec<PubTypeConstraint>>,
        arg_names: impl IntoIterator<Item = &'s str>,
        doc: &str,
    ) -> Self {
        let arg_names = arg_names.into_iter().map(Ustr::from).collect();
        FunctionDefinition {
            ty_scheme: TypeScheme::new_infer_quantifiers_with_constraints(
                fn_ty,
                constraints.into(),
            ),
            arg_names,
            doc: Some(String::from(doc)),
        }
    }

    pub fn fmt_with_name_and_module_env(
        &self,
        f: &mut fmt::Formatter,
        name: &str,
        prefix: &str,
        env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        // function.ty_scheme.format_quantifiers(f)?; write!(f, ". ")?;
        if let Some(doc) = &self.doc {
            writeln!(f, "{prefix}/// {doc}")?;
        }
        write!(f, "{prefix}fn {name}")?;
        let mut quantifiers = self
            .ty_scheme
            .ty_quantifiers
            .iter()
            .map(|q| format!("{q}"))
            .chain(
                self.ty_scheme
                    .eff_quantifiers
                    .iter()
                    .map(|q| format!("{q}")),
            )
            .peekable();
        if quantifiers.peek().is_some() {
            write!(f, "<{}>", quantifiers.collect::<Vec<_>>().join(", "))?;
        }
        write!(f, "{}", self.ty_scheme.ty.format_with(env))?;
        if !self.ty_scheme.is_just_type_and_effects() {
            writeln!(f, " {}", self.ty_scheme.display_constraints_rust_style(env),)
        } else {
            writeln!(f)
        }
    }
}

type CallCtx = EvalCtx;

/// A function that can be called
pub trait Callable {
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult;
    fn as_script(&self) -> Option<&ScriptFunction> {
        None
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

// Function access types

pub type Function = Box<dyn Callable>;
pub type FunctionPtr = *mut Function;
pub type FunctionRc = Rc<RefCell<Function>>;
pub type FunctionWeak = Weak<RefCell<Function>>;

/// A reference to a function
#[derive(Clone)]
pub enum FunctionRef {
    /// Strong references are used for first-class functions, that cannot be recursive
    Strong(FunctionRc),
    /// Weak references are used to avoid cycles in recursive functions
    Weak(FunctionWeak),
}

impl FunctionRef {
    pub fn new_strong(function: &FunctionRc) -> Self {
        FunctionRef::Strong(function.clone())
    }
    pub fn new_weak(function: &FunctionRc) -> Self {
        FunctionRef::Weak(Rc::downgrade(function))
    }
    pub fn get(&self) -> FunctionRc {
        match self {
            FunctionRef::Strong(function) => function.clone(),
            FunctionRef::Weak(function) => function
                .upgrade()
                .expect("Failed to upgrade weak function ref"),
        }
    }
    pub fn weak_ref(&self) -> FunctionWeak {
        match self {
            FunctionRef::Strong(function) => Rc::downgrade(function),
            FunctionRef::Weak(function) => function.clone(),
        }
    }
}

impl Debug for FunctionRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.get().try_borrow() {
            Ok(func) => write!(f, "{func:?}"),
            Err(_) => write!(f, "self"),
        }
    }
}

impl PartialEq for FunctionRef {
    fn eq(&self, other: &Self) -> bool {
        Weak::ptr_eq(&self.weak_ref(), &other.weak_ref())
    }
}
impl Eq for FunctionRef {}

/// A function holding user-defined code.
/// If captured is non-empty it is a closure, and these will be passed
/// as extra first arguments to the environment of the function.
#[derive(Debug, Clone)]
pub struct ScriptFunction {
    pub code: ir::Node,
    // pub monomorphised: HashMap<Vec<Type>, ir::Node>,
}
impl ScriptFunction {
    pub fn new(code: ir::Node) -> Self {
        ScriptFunction { code }
    }
}

impl Callable for ScriptFunction {
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult {
        let old_frame_base = ctx.frame_base;
        ctx.frame_base = ctx.environment.len();
        ctx.environment.extend(args);
        ctx.recursion += 1;
        if ctx.recursion >= ctx.recursion_limit {
            return Err(RuntimeError::RecursionLimitExceeded {
                limit: ctx.recursion_limit,
            });
        }
        let ret = self.code.eval_with_ctx(ctx)?;
        ctx.recursion -= 1;
        ctx.environment.truncate(ctx.frame_base);
        ctx.frame_base = old_frame_base;
        Ok(ret)
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
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
        self.code.format_ind(f, env, spacing, indent)
    }
}

pub struct Closure {
    pub function: FunctionRef,
    pub captured: Vec<Value>,
}
impl Closure {
    pub fn new(function: FunctionRef, captured: Vec<Value>) -> Self {
        Closure { function, captured }
    }
}
impl Callable for Closure {
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult {
        let args = self
            .captured
            .iter()
            .cloned()
            .map(ValOrMut::Val)
            .chain(args)
            .collect();
        self.function.get().borrow().call(args, ctx)
    }

    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        writeln!(f, "{indent_str}closure of")?;
        self.function
            .get()
            .borrow()
            .format_ind(f, env, spacing, indent + 1)?;
        writeln!(f, "{indent_str}with captured [")?;
        for captured in &self.captured {
            captured.format_ind(f, env, spacing, indent + 1)?;
        }
        writeln!(f, "{indent_str}]")
    }
}

// Helper traits and structs for defining native functions

/// A trait that must be satisfied by the output of a native function.
/// This is used to ensure that the output can be converted to a `Value`.
pub trait NativeOutput: Debug + Clone + Eq + NativeDisplay + 'static {}
impl<T: Debug + Clone + Eq + NativeDisplay + 'static> NativeOutput for T {}

/// Marker struct to declare argument by value to native functions.
pub struct NatVal<T> {
    _marker: PhantomData<T>,
}

/// Marker struct to declare argument by mutable reference to native functions.
pub struct NatMut<T> {
    _marker: PhantomData<T>,
}

/// A trait that can extract an argument from a `ValOrMut` and a `CallCtx`.
/// This is necessary due to the lack of specialization in stable Rust.
pub trait ArgExtractor {
    type Output<'a>;
    const MUTABLE: bool;
    fn extract(arg: ValOrMut, ctx: &mut CallCtx) -> Result<Self::Output<'_>, RuntimeError>;
    fn default_ty() -> Type;
}

impl ArgExtractor for Value {
    type Output<'a> = Value;
    const MUTABLE: bool = false;
    fn extract(arg: ValOrMut, _ctx: &mut CallCtx) -> Result<Self::Output<'_>, RuntimeError> {
        Ok(arg.into_val().unwrap())
    }
    fn default_ty() -> Type {
        Type::variable_id(0)
    }
}

impl ArgExtractor for &'_ mut Value {
    type Output<'a> = &'a mut Value;
    const MUTABLE: bool = true;
    fn extract(arg: ValOrMut, ctx: &mut CallCtx) -> Result<Self::Output<'_>, RuntimeError> {
        arg.as_place().target_mut(ctx)
    }
    fn default_ty() -> Type {
        Type::variable_id(0)
    }
}

impl<T: Clone + 'static> ArgExtractor for NatVal<T> {
    type Output<'a> = T;
    const MUTABLE: bool = false;
    fn extract(arg: ValOrMut, ctx: &mut CallCtx) -> Result<Self::Output<'_>, RuntimeError> {
        let arg2 = arg.clone();
        Ok(arg.into_primitive::<T>().unwrap_or_else(|| {
            panic!(
                "Expected a primitive of type {}, found {}",
                std::any::type_name::<T>(),
                FormatWith::new(&arg2, ctx)
            )
        }))
    }
    fn default_ty() -> Type {
        Type::primitive::<T>()
    }
}

impl<T: Clone + 'static> ArgExtractor for NatMut<T> {
    type Output<'a> = &'a mut T;
    const MUTABLE: bool = true;
    fn extract(arg: ValOrMut, ctx: &mut CallCtx) -> Result<Self::Output<'_>, RuntimeError> {
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
    fn build(result: Self::Input) -> EvalResult;
    fn default_ty() -> Type;
}

impl<O: NativeOutput> OutputBuilder for NatVal<O> {
    type Input = O;
    fn build(result: Self::Input) -> EvalResult {
        Ok(Value::Native(Box::new(result)))
    }
    fn default_ty() -> Type {
        Type::primitive::<O>()
    }
}

impl<O: NativeOutput> OutputBuilder for Fallible<NatVal<O>> {
    type Input = Result<O, RuntimeError>;
    fn build(result: Self::Input) -> EvalResult {
        result.map(|o| Value::Native(Box::new(o)))
    }
    fn default_ty() -> Type {
        Type::primitive::<O>()
    }
}

impl OutputBuilder for Value {
    type Input = Value;
    fn build(result: Self::Input) -> EvalResult {
        Ok(result)
    }
    fn default_ty() -> Type {
        Type::variable_id(0)
    }
}

impl OutputBuilder for Fallible<Value> {
    type Input = Result<Value, RuntimeError>;
    fn build(result: Self::Input) -> EvalResult {
        result
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
            F: for<'a> Fn($($arg::Output<'a>),*) -> O::Input + 'static,
        >(F, PhantomData<($($arg,)* O)>);

        impl<
            $($arg: ArgExtractor + 'static,)*
            O: OutputBuilder + 'static,
            F: for<'a> Fn($($arg::Output<'a>),*) -> O::Input + 'static,
        > $struct_name<$($arg,)* O, F>
        {
            pub fn new(f: F) -> Self {
                $struct_name(f, PhantomData)
            }

            pub fn description_with_ty_scheme(f: F, arg_names: [&'static str; count!($($arg)*)], doc: Option<&'static str>, ty_scheme: TypeScheme<FnType>) -> ModuleFunction {
                ModuleFunction {
                    definition: FunctionDefinition::new(
                        ty_scheme,
                        arg_names.into_iter().map(Ustr::from).collect(),
                        doc.map(String::from),
                    ),
                    code: Rc::new(RefCell::new(Box::new(Self::new(f)))),
                    spans: None,
                }
            }

            paste::paste! {
            #[allow(clippy::too_many_arguments)]
            pub fn description_with_ty(f: F, arg_names: [&'static str; count!($($arg)*)], doc: Option<&'static str>, $([<$arg:lower _ty>]: Type,)* o_ty: Type, effects: EffType) -> ModuleFunction {
                let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
                    [$(([<$arg:lower _ty>], $arg::MUTABLE)), *],
                    o_ty,
                    effects,
                ));
                Self::description_with_ty_scheme(f, arg_names, doc, ty_scheme)
            }
            }

            paste::paste! {
                #[allow(clippy::too_many_arguments)]
                pub fn description_with_in_ty(f: F, arg_names: [&'static str; count!($($arg)*)], doc: Option<&'static str>, $([<$arg:lower _ty>]: Type,)* effects: EffType) -> ModuleFunction {
                    let o_ty = O::default_ty();
                    Self::description_with_ty(f, arg_names, doc, $([<$arg:lower _ty>],)* o_ty, effects)
                }
                }

            pub fn description_with_default_ty(f: F, arg_names: [&'static str; count!($($arg)*)], doc: Option<&'static str>, effects: EffType) -> ModuleFunction {
                Self::description_with_in_ty(f, arg_names, doc, $($arg::default_ty(),)* effects)
            }
        }

        impl<$($arg,)* O, F> Callable for $struct_name<$($arg,)* O, F>
        where
            $($arg: ArgExtractor + 'static,)*
            O: OutputBuilder + 'static,
            F: for<'a> Fn($($arg::Output<'a>),*) -> O::Input + 'static,
        {
            paste::paste! {
            #[allow(unused_variables)]
            fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult {
                // Extract arguments by applying repetition for each ArgExtractor
                #[allow(unused_variables, unused_mut)]
                let mut args_iter = args.into_iter();
                $(
                    let [<$arg:lower>] = args_iter.next().unwrap();
                    // SAFETY: the borrow checker ensures that all mutable references are disjoint
                    let arg_ctx = unsafe { &mut *(ctx as *mut CallCtx) };
                    let [<$arg:lower>] = $arg::extract([<$arg:lower>], arg_ctx)?;
                )*

                // Call the function using the extracted arguments
                O::build((self.0)($([<$arg:lower>]),*))
            }
            }

            fn format_ind(
                &self,
                f: &mut std::fmt::Formatter,
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
// - W: &mut Value (mutable reference to generic value)
// outputs:
// - N: native
// - V: value
// - FN: native, fallible
// - FV: value, fallible

// Note: the proc macro declare_native_fn_aliases defined in ferlium_macros generates
// typedefs with the combinations of aliases.

n_ary_native_fn!(NullaryNativeFn);
declare_native_fn_aliases!(0);

impl<O: OutputBuilder + 'static, F: Fn() -> O::Input + 'static> NullaryNativeFn<O, F> {
    pub fn description(f: F, doc: Option<&'static str>, effects: EffType) -> ModuleFunction {
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
