use std::{fmt, rc::{Rc, Weak}};

use crate::{
    ir::{self},
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
        Type::Function(Box::new(self.ty.clone()))
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

pub trait BinaryNativeFunction:
    Fn(
    <Self as BinaryNativeFunction>::A,
    <Self as BinaryNativeFunction>::B,
) -> <Self as BinaryNativeFunction>::O
{
    type A: Clone + 'static;
    type B: Clone + 'static;
    type O: Clone + 'static;

    fn ty() -> FunctionType {
        FunctionType {
            arg_ty: vec![Type::primitive::<Self::A>(), Type::primitive::<Self::B>()],
            return_ty: Type::primitive::<Self::O>(),
        }
    }
}

impl<
        A: Clone + 'static,
        B: Clone + 'static,
        O: fmt::Debug + Clone + std::cmp::Eq + 'static,
        F: BinaryNativeFunction<A = A, B = B, O = O> + Clone + 'static,
    > FunctionCall for F
{
    fn call(&self, args: Vec<Value>, _: &CallCtx) -> Value {
        let mut args = args.into_iter();
        let a_primitive = args.next().unwrap().into_primitive().unwrap();
        let a = a_primitive.into_any().downcast::<A>().unwrap();
        let b_primitive = args.next().unwrap().into_primitive().unwrap();
        let b = b_primitive.into_any().downcast::<B>().unwrap();

        Value::Primitive(Box::new(self(*a, *b)))
    }
}

impl BinaryNativeFunction for fn(i32, i32) -> i32 {
    type A = i32;
    type B = i32;
    type O = i32;
}

pub fn binary_native_function<
    A: Clone + 'static,
    B: Clone + 'static,
    O: fmt::Debug + Clone + std::cmp::Eq + 'static,
    F: Fn(A, B) -> O + Clone + BinaryNativeFunction<A = A, B = B, O = O> + 'static,
>(
    f: F,
) -> FunctionDescription {
    FunctionDescription {
        ty: F::ty(),
        code: Box::new(f),
    }
}
