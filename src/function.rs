use std::{
    cell::RefCell,
    fmt::{self, Debug},
    marker::PhantomData,
    rc::{Rc, Weak},
};

use crate::{
    error::RuntimeError,
    eval::{EvalCtx, EvalResult, ValOrMut},
    format::FormatWith,
    ir::{self},
    module::{ModuleEnv, ModuleFunction},
    r#type::{FnType, Type},
    type_scheme::TypeScheme,
    value::{NativeDisplay, Value},
};

type CallCtx = EvalCtx;

/// A function that can be called
pub trait Callable {
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult;
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
        indent: usize,
    ) -> std::fmt::Result;
}

impl Debug for dyn Callable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn @ {:p}", self)
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
            Ok(func) => write!(f, "{:?}", func),
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
    fn as_script_mut(&mut self) -> Option<&mut ScriptFunction> {
        Some(self)
    }
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        self.code.format_ind(f, env, indent)
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
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "⎸ ".repeat(indent);
        writeln!(f, "{indent_str}closure of")?;
        self.function
            .get()
            .borrow()
            .format_ind(f, env, indent + 1)?;
        writeln!(f, "{indent_str}with captured [")?;
        for captured in &self.captured {
            captured.format_ind(f, env, indent + 1)?;
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

/// Marker struct to declare the output of a native function as raw (the native type itself).
pub struct Plain<T> {
    _marker: PhantomData<T>,
}

/// Marker struct to declare the output of a native function as a fallible result.
pub struct Fallible<T> {
    _marker: PhantomData<T>,
}

/// A trait to dispatch over the fallibility of a native function
pub trait OutputBuilder {
    type NativeTy: Clone;
    type Input;
    fn build_output(result: Self::Input) -> EvalResult;
}

impl<O: NativeOutput> OutputBuilder for Plain<O> {
    type NativeTy = O;
    type Input = O;
    fn build_output(result: Self::Input) -> EvalResult {
        Ok(Value::Native(Box::new(result)))
    }
}

impl<O: NativeOutput> OutputBuilder for Fallible<O> {
    type NativeTy = O;
    type Input = Result<O, RuntimeError>;
    fn build_output(result: Self::Input) -> EvalResult {
        result.map(|o| Value::Native(Box::new(o)))
    }
}

// Shorthand names for native functions type aliases:
// - N: Val<T> (native value)
// - M: Mut<T> (native mutable reference)
// - V: Value (generic value)
// - W: &mut Value (mutable reference to generic value)
// - I: infallible result
// - F: fallible result

// Native functions of various arities

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

            pub fn description_with_ty_scheme(f: F, ty_scheme: TypeScheme<FnType>) -> ModuleFunction {
                ModuleFunction {
                    ty_scheme,
                    code: Rc::new(RefCell::new(Box::new(Self::new(f)))),
                    spans: None,
                }
            }

            paste::paste! {
            pub fn description_with_ty(f: F, $([<$arg:lower _ty>]: Type),*) -> ModuleFunction {
                let o_ty = Type::primitive::<O::NativeTy>();
                let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
                    &[$(([<$arg:lower _ty>], $arg::MUTABLE)), *],
                    o_ty,
                ));
                Self::description_with_ty_scheme(f, ty_scheme)
            }
            }

            pub fn description_with_default_ty(f: F) -> ModuleFunction {
                Self::description_with_ty(f, $($arg::default_ty()),*)
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
                O::build_output((self.0)($([<$arg:lower>]),*))
            }
            }

            fn format_ind(
                &self,
                f: &mut std::fmt::Formatter,
                _env: &ModuleEnv<'_>,
                indent: usize,
            ) -> std::fmt::Result {
                let indent_str = "⎸ ".repeat(indent);
                writeln!(f, "{}{} @ {:p}", indent_str, stringify!($struct_name), &self.0)
            }
        }
    };
}

// Nullary

n_ary_native_fn!(NullaryNativeFn);

impl<O: OutputBuilder + 'static, F: Fn() -> O::Input + 'static> NullaryNativeFn<O, F> {
    pub fn description(f: F) -> ModuleFunction {
        Self::description_with_ty(f)
    }
}

pub type NullaryNativeFnI<O, F> = NullaryNativeFn<Plain<O>, F>;
pub type NullaryNativeFnF<O, F> = NullaryNativeFn<Fallible<O>, F>;

// Unary

n_ary_native_fn!(UnaryNativeFn, A);

// The arguments are by native value
pub type UnaryNativeFnNI<A, O, F> = UnaryNativeFn<NatVal<A>, Plain<O>, F>;
pub type UnaryNativeFnVI<O, F> = UnaryNativeFn<Value, Plain<O>, F>;

// Binary

n_ary_native_fn!(BinaryNativeFn, A, B);

// See above for shorthand names
pub type BinaryNativeFnNNI<A, B, O, F> = BinaryNativeFn<NatVal<A>, NatVal<B>, Plain<O>, F>;
pub type BinaryNativeFnNNF<A, B, O, F> = BinaryNativeFn<NatVal<A>, NatVal<B>, Fallible<O>, F>;
pub type BinaryNativeFnNVI<A, O, F> = BinaryNativeFn<NatVal<A>, Value, Plain<O>, F>;
pub type BinaryNativeFnMVI<A, O, F> = BinaryNativeFn<NatMut<A>, Value, Plain<O>, F>;
pub type BinaryNativeFnMNI<A, B, O, F> = BinaryNativeFn<NatMut<A>, NatVal<B>, Plain<O>, F>;
pub type BinaryNativeFnVVI<O, F> = BinaryNativeFn<Value, Value, Plain<O>, F>;

// Ternary

n_ary_native_fn!(TernaryNativeFn, A, B, C);

// See above for shorthand names
pub type TernaryNativeFnNNNI<A, B, C, O, F> =
    TernaryNativeFn<NatVal<A>, NatVal<B>, NatVal<C>, Plain<O>, F>;
pub type TernaryNativeFnNNVI<A, B, O, F> =
    TernaryNativeFn<NatVal<A>, NatVal<B>, Value, Plain<O>, F>;
