use std::{
    fmt,
    marker::PhantomData,
    rc::{Rc, Weak},
};

use crate::{
    ir,
    r#type::{FunctionType, Type},
    value::Value,
};

type CallCtx = ();

/// A function that can be called
pub trait FunctionCall {
    fn call(&self, args: Vec<Value>, ctx: &CallCtx) -> Value;
}

impl fmt::Debug for dyn FunctionCall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn @ {:p}", self)
    }
}

// script functions

/// A description of a function, to be used in type checking and execution
pub struct FunctionDescription {
    pub ty: FunctionType,
    pub code: Box<dyn FunctionCall>,
}

impl FunctionDescription {
    pub fn ty(&self) -> Type {
        Type::function_type(self.ty.clone())
    }
}

#[derive(Clone)]
pub struct FunctionKey(Weak<FunctionDescription>);

impl FunctionKey {
    pub fn new(function: &Rc<FunctionDescription>) -> Self {
        FunctionKey(Rc::downgrade(function))
    }
    pub fn get(&self) -> Rc<FunctionDescription> {
        self.0.upgrade().unwrap()
    }
}

impl std::fmt::Debug for FunctionKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.get().code)
    }
}

impl PartialEq for FunctionKey {
    fn eq(&self, other: &Self) -> bool {
        Weak::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for FunctionKey {}

/// A function holding user-defined code
#[derive(Debug, Clone)]
pub struct ScriptFunction {
    pub code: ir::Node,
}

impl FunctionCall for ScriptFunction {
    fn call(&self, args: Vec<Value>, _ctx: &CallCtx) -> Value {
        let mut ctx = ir::Context::new();
        ctx.environment.extend(args);
        self.code.eval(&mut ctx)
    }
}

// native functions

pub struct NullaryNativeFn<O: fmt::Debug + Clone + std::cmp::Eq + 'static, F: Fn() -> O + 'static>(
    F,
    PhantomData<O>,
);

impl<O: fmt::Debug + Clone + std::cmp::Eq + 'static, F: Fn() -> O + 'static> NullaryNativeFn<O, F> {
    pub fn new(f: F) -> Self {
        NullaryNativeFn(f, PhantomData)
    }

    pub fn description(f: F) -> FunctionDescription {
        let o_ty = Type::primitive::<O>();
        FunctionDescription {
            ty: FunctionType::new(&[], o_ty),
            code: Box::new(NullaryNativeFn(f, PhantomData)),
        }
    }
}

impl<O, F> FunctionCall for NullaryNativeFn<O, F>
where
    O: fmt::Debug + Clone + std::cmp::Eq + 'static,
    F: Fn() -> O,
{
    fn call(&self, _: Vec<Value>, _: &CallCtx) -> Value {
        Value::Primitive(Box::new((self.0)()))
    }
}

pub struct UnaryNativeFn<
    A: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + 'static,
    F: Fn(A) -> O + 'static,
>(F, PhantomData<(A, O)>);

impl<
        A: Clone + 'static,
        O: fmt::Debug + Clone + std::cmp::Eq + 'static,
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
            ty: FunctionType::new(&[a_ty], o_ty),
            code: Box::new(UnaryNativeFn(f, PhantomData)),
        }
    }
}

impl<A, O, F> FunctionCall for UnaryNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + 'static,
    F: Fn(A) -> O,
{
    fn call(&self, args: Vec<Value>, _: &CallCtx) -> Value {
        let a_primitive = args.into_iter().next().unwrap().into_primitive().unwrap();
        let a = a_primitive.into_any().downcast::<A>().unwrap();

        Value::Primitive(Box::new((self.0)(*a)))
    }
}

pub struct BinaryNativeFn<
    A: Clone + 'static,
    B: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + 'static,
    F: Fn(A, B) -> O + 'static,
>(F, PhantomData<(A, B, O)>);

impl<
        A: Clone + 'static,
        B: Clone + 'static,
        O: fmt::Debug + Clone + std::cmp::Eq + 'static,
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
            ty: FunctionType::new(&[a_ty, b_ty], o_ty),
            code: Box::new(BinaryNativeFn(f, PhantomData)),
        }
    }
}

impl<A, B, O, F> FunctionCall for BinaryNativeFn<A, B, O, F>
where
    A: Clone + 'static,
    B: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + 'static,
    F: Fn(A, B) -> O,
{
    fn call(&self, args: Vec<Value>, _: &CallCtx) -> Value {
        let mut args = args.into_iter();
        let a_primitive = args.next().unwrap().into_primitive().unwrap();
        let a = a_primitive.into_any().downcast::<A>().unwrap();
        let b_primitive = args.next().unwrap().into_primitive().unwrap();
        let b = b_primitive.into_any().downcast::<B>().unwrap();

        Value::Primitive(Box::new((self.0)(*a, *b)))
    }
}

pub struct BinaryPartialNativeFn<A, O, F>(F, PhantomData<(A, O)>);

impl<
        A: Clone + 'static,
        O: fmt::Debug + Clone + std::cmp::Eq + 'static,
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
    O: fmt::Debug + Clone + std::cmp::Eq + 'static,
    F: Fn(A, Value) -> O,
{
    fn call(&self, args: Vec<Value>, _: &CallCtx) -> Value {
        let mut args = args.into_iter();
        let a_primitive = args.next().unwrap().into_primitive().unwrap();
        let a = a_primitive.into_any().downcast::<A>().unwrap();
        let b = args.next().unwrap();

        Value::Primitive(Box::new((self.0)(*a, b)))
    }
}