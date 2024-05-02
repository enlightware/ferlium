use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    marker::PhantomData,
    rc::{Rc, Weak},
};

use ustr::Ustr;

use crate::{
    error::RuntimeError,
    ir::{self, EvalCtx, EvalResult},
    r#type::{FnType, Type, TypeOfNativeValue},
    value::{ValOrMut, Value},
};

type CallCtx = EvalCtx;

/// A function that can be called
pub trait FunctionCall {
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult;
    fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result;
}

impl fmt::Debug for dyn FunctionCall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn @ {:p}", self)
    }
}
// TODO: add display by downcasting to a concrete type and calling its display

// script functions

/// A description of a function, to be used in type checking and execution
#[derive(Debug)]
pub struct FunctionDescription {
    pub ty: FnType,
    pub code: Box<dyn FunctionCall>,
}

impl FunctionDescription {
    pub fn ty(&self) -> Type {
        Type::function_type(self.ty.clone())
    }
}

pub type FunctionDescriptionRc = Rc<RefCell<FunctionDescription>>;
pub type FunctionDescriptionWeak = Weak<RefCell<FunctionDescription>>;

pub type FunctionsMap = HashMap<Ustr, FunctionDescriptionRc>;

/// A reference to a function
#[derive(Clone)]
pub enum FunctionRef {
    /// Strong references are used for first-class functions, that cannot be recursive
    Strong(FunctionDescriptionRc),
    /// Weak references are used to avoid cycles in recursive functions
    Weak(FunctionDescriptionWeak),
}

impl FunctionRef {
    pub fn new_strong(function: &FunctionDescriptionRc) -> Self {
        FunctionRef::Strong(function.clone())
    }
    pub fn new_weak(function: &FunctionDescriptionRc) -> Self {
        FunctionRef::Weak(Rc::downgrade(function))
    }
    pub fn get(&self) -> FunctionDescriptionRc {
        match self {
            FunctionRef::Strong(function) => function.clone(),
            FunctionRef::Weak(function) => function.upgrade().unwrap(),
        }
    }
    pub fn weak_ref(&self) -> FunctionDescriptionWeak {
        match self {
            FunctionRef::Strong(function) => Rc::downgrade(function),
            FunctionRef::Weak(function) => function.clone(),
        }
    }
}

impl std::fmt::Debug for FunctionRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.get().try_borrow() {
            Ok(descr) => write!(f, "{:?}", descr.code),
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

/// A function holding user-defined code
#[derive(Debug, Clone)]
pub struct ScriptFunction {
    pub code: ir::Node,
}
impl ScriptFunction {
    pub fn new(code: ir::Node) -> Self {
        ScriptFunction { code }
    }
}

impl FunctionCall for ScriptFunction {
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult {
        let old_frame_base = ctx.frame_base;
        ctx.frame_base = ctx.environment.len();
        ctx.environment
            .extend(args.into_iter().map(|arg| arg.into_val().unwrap()));
        let ret = self.code.eval(ctx)?;
        ctx.environment.truncate(ctx.frame_base);
        ctx.frame_base = old_frame_base;
        Ok(ret)
    }
    fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        self.code.format_ind(f, indent)
    }
}

// native functions

pub struct NullaryNativeFn<O: fmt::Debug + Clone + std::cmp::Eq + 'static, F: Fn() -> O + 'static>(
    F,
    PhantomData<O>,
);

impl<O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static, F: Fn() -> O + 'static> NullaryNativeFn<O, F> {
    pub fn new(f: F) -> Self {
        NullaryNativeFn(f, PhantomData)
    }

    pub fn description(f: F) -> FunctionDescription {
        let o_ty = Type::primitive::<O>();
        FunctionDescription {
            ty: FnType::new_by_val(&[], o_ty),
            code: Box::new(NullaryNativeFn(f, PhantomData)),
        }
    }
}

impl<O, F> FunctionCall for NullaryNativeFn<O, F>
where
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
    F: Fn() -> O,
{
    fn call(&self, _: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        Ok(Value::Native(Box::new((self.0)())))
    }
    fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct UnaryNativeFn<
    A: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
    F: Fn(A) -> O + 'static,
>(F, PhantomData<(A, O)>);

impl<
        A: Clone + 'static,
        O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
        F: Fn(A) -> O + 'static,
    > UnaryNativeFn<A, O, F>
{
    pub fn new(f: F) -> Self {
        UnaryNativeFn(f, PhantomData)
    }

    pub fn description(f: F) -> FunctionDescription {
        let a_ty = Type::primitive::<A>();
        let o_ty = Type::primitive::<O>();
        FunctionDescription {
            ty: FnType::new_by_val(&[a_ty], o_ty),
            code: Box::new(UnaryNativeFn(f, PhantomData)),
        }
    }
}

impl<A, O, F> FunctionCall for UnaryNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
    F: Fn(A) -> O,
{
    fn call(&self, args: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        let a = args
            .into_iter()
            .next()
            .unwrap()
            .into_primitive::<A>()
            .unwrap();

        Ok(Value::Native(Box::new((self.0)(a))))
    }
    fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct UnaryMutNativeFn<A, O, F>(F, PhantomData<(A, O)>);

impl<A, O, F> UnaryMutNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + 'static,
    F: Fn(&mut A) -> O + 'static,
{
    pub fn new(f: F) -> Self {
        UnaryMutNativeFn(f, PhantomData)
    }
}

impl<A, O, F> FunctionCall for UnaryMutNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
    F: Fn(&mut A) -> O,
{
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap().as_mut_primitive::<A>(ctx)?.unwrap();
        Ok(Value::Native(Box::new((self.0)(a))))
    }
    fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct BinaryNativeFn<
    A: Clone + 'static,
    B: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
    F: Fn(A, B) -> O + 'static,
>(F, PhantomData<(A, B, O)>);

impl<
        A: Clone + 'static,
        B: Clone + 'static,
        O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
        F: Fn(A, B) -> O + 'static,
    > BinaryNativeFn<A, B, O, F>
{
    pub fn new(f: F) -> Self {
        BinaryNativeFn(f, PhantomData)
    }

    pub fn description(f: F) -> FunctionDescription {
        let a_ty = Type::primitive::<A>();
        let b_ty = Type::primitive::<B>();
        let o_ty = Type::primitive::<O>();
        FunctionDescription {
            ty: FnType::new_by_val(&[a_ty, b_ty], o_ty),
            code: Box::new(BinaryNativeFn(f, PhantomData)),
        }
    }
}

impl<A, B, O, F> FunctionCall for BinaryNativeFn<A, B, O, F>
where
    A: Clone + 'static,
    B: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
    F: Fn(A, B) -> O,
{
    fn call(&self, args: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap().into_primitive::<A>().unwrap();
        let b = args.next().unwrap().into_primitive::<B>().unwrap();

        Ok(Value::Native(Box::new((self.0)(a, b))))
    }
    fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct TryBinaryNativeFn<
    A: Clone + 'static,
    B: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
    F: Fn(A, B) -> Result<O, RuntimeError> + 'static,
>(F, PhantomData<(A, B, O)>);

impl<
        A: Clone + 'static,
        B: Clone + 'static,
        O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
        F: Fn(A, B) -> Result<O, RuntimeError> + 'static,
    > TryBinaryNativeFn<A, B, O, F>
{
    pub fn new(f: F) -> Self {
        TryBinaryNativeFn(f, PhantomData)
    }

    pub fn description(f: F) -> FunctionDescription {
        let a_ty = Type::primitive::<A>();
        let b_ty = Type::primitive::<B>();
        let o_ty = Type::primitive::<O>();
        FunctionDescription {
            ty: FnType::new_by_val(&[a_ty, b_ty], o_ty),
            code: Box::new(TryBinaryNativeFn(f, PhantomData)),
        }
    }
}

impl<A, B, O, F> FunctionCall for TryBinaryNativeFn<A, B, O, F>
where
    A: Clone + 'static,
    B: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
    F: Fn(A, B) -> Result<O, RuntimeError>,
{
    fn call(&self, args: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap().into_primitive::<A>().unwrap();
        let b = args.next().unwrap().into_primitive::<B>().unwrap();

        (self.0)(a, b).map(|o| Value::Native(Box::new(o)))
    }
    fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct BinaryPartialNativeFn<A, O, F>(F, PhantomData<(A, O)>);

impl<
        A: Clone + 'static,
        O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
        F: Fn(A, Value) -> O + 'static,
    > BinaryPartialNativeFn<A, O, F>
{
    pub fn new(f: F) -> Self {
        BinaryPartialNativeFn(f, PhantomData)
    }
}

impl<A, O, F> FunctionCall for BinaryPartialNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
    F: Fn(A, Value) -> O,
{
    fn call(&self, args: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap().into_primitive::<A>().unwrap();
        let b = args.next().unwrap().into_val().unwrap();

        Ok(Value::Native(Box::new((self.0)(a, b))))
    }
    fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct BinaryPartialMutNativeFn<A, O, F>(F, PhantomData<(A, O)>);

impl<
        A: Clone + 'static,
        O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
        F: Fn(&mut A, Value) -> O + 'static,
    > BinaryPartialMutNativeFn<A, O, F>
{
    pub fn new(f: F) -> Self {
        BinaryPartialMutNativeFn(f, PhantomData)
    }
}

impl<A, O, F> FunctionCall for BinaryPartialMutNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
    F: Fn(&mut A, Value) -> O,
{
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap().as_mut_primitive::<A>(ctx)?.unwrap();
        let b = args.next().unwrap().into_val().unwrap();
        Ok(Value::Native(Box::new((self.0)(a, b))))
    }
    fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct BinaryNativeFnVVP<O, F>(F, PhantomData<O>);

impl<F, O> BinaryNativeFnVVP<O, F>
where
    F: Fn(&Value, &Value) -> O + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
{
    pub fn new(f: F) -> Self {
        BinaryNativeFnVVP(f, PhantomData)
    }

    pub fn description(f: F) -> FunctionDescription {
        let arg_ty = Type::variable_id(0);
        let o_ty = Type::primitive::<O>();
        FunctionDescription {
            ty: FnType::new_by_val(&[arg_ty, arg_ty], o_ty),
            code: Box::new(BinaryNativeFnVVP(f, PhantomData)),
        }
    }
}

impl<O, F> FunctionCall for BinaryNativeFnVVP<O, F>
where
    F: Fn(&Value, &Value) -> O,
    O: fmt::Debug + Clone + std::cmp::Eq + TypeOfNativeValue + 'static,
{
    fn call(&self, args: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap();
        let a = a.as_val().unwrap();
        let b = args.next().unwrap();
        let b = b.as_val().unwrap();
        let o = self.0(a, b);

        Ok(Value::Native(Box::new(o)))
    }
    fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}
