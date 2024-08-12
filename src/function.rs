use std::{
    cell::RefCell,
    fmt::{self, Debug},
    marker::PhantomData,
    rc::{Rc, Weak},
};

use crate::{
    error::RuntimeError,
    ir::{self, EvalCtx, EvalResult, ValOrMut},
    module::{ModuleEnv, ModuleFunction},
    r#type::{FnType, Type},
    type_scheme::TypeScheme,
    value::{NativeDisplay, Value},
};

type CallCtx = EvalCtx;

/// A function that can be called
pub trait Callable {
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult;
    fn apply_if_script(&mut self, f: &mut dyn FnMut(&mut ir::Node));
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

impl Callable for ScriptFunction {
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult {
        let old_frame_base = ctx.frame_base;
        ctx.frame_base = ctx.environment.len();
        ctx.environment.extend(args);
        let ret = self.code.eval(ctx)?;
        ctx.environment.truncate(ctx.frame_base);
        ctx.frame_base = old_frame_base;
        Ok(ret)
    }
    fn apply_if_script(&mut self, f: &mut dyn FnMut(&mut ir::Node)) {
        f(&mut self.code);
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

// native functions

pub struct NullaryNativeFn<O: Debug + Clone + Eq + NativeDisplay + 'static, F: Fn() -> O + 'static>(
    F,
    PhantomData<O>,
);

impl<O: Debug + Clone + Eq + NativeDisplay + 'static, F: Fn() -> O + 'static>
    NullaryNativeFn<O, F>
{
    pub fn new(f: F) -> Self {
        NullaryNativeFn(f, PhantomData)
    }

    pub fn description(f: F) -> ModuleFunction {
        let o_ty = Type::primitive::<O>();
        ModuleFunction {
            ty_scheme: TypeScheme::new_just_type(FnType::new_by_val(&[], o_ty)),
            code: Rc::new(RefCell::new(Box::new(NullaryNativeFn(f, PhantomData)))),
            spans: None,
        }
    }
}

impl<O, F> Callable for NullaryNativeFn<O, F>
where
    O: Debug + Clone + Eq + NativeDisplay + 'static,
    F: Fn() -> O,
{
    fn call(&self, _: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        Ok(Value::Native(Box::new((self.0)())))
    }
    fn apply_if_script(&mut self, _f: &mut dyn FnMut(&mut ir::Node)) {}
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct UnaryNativeFn<
    A: Clone + 'static,
    O: Debug + Clone + Eq + 'static,
    F: Fn(A) -> O + 'static,
>(F, PhantomData<(A, O)>);

impl<
        A: Clone + 'static,
        O: Debug + Clone + Eq + NativeDisplay + 'static,
        F: Fn(A) -> O + 'static,
    > UnaryNativeFn<A, O, F>
{
    pub fn new(f: F) -> Self {
        UnaryNativeFn(f, PhantomData)
    }

    pub fn description(f: F) -> ModuleFunction {
        let a_ty = Type::primitive::<A>();
        let o_ty = Type::primitive::<O>();
        let ty_scheme = TypeScheme::new_just_type(FnType::new_by_val(&[a_ty], o_ty));
        Self::description_with_ty_scheme(f, ty_scheme)
    }

    pub fn description_with_ty_scheme(f: F, ty_scheme: TypeScheme<FnType>) -> ModuleFunction {
        ModuleFunction {
            ty_scheme,
            code: Rc::new(RefCell::new(Box::new(UnaryNativeFn::new(f)))),
            spans: None,
        }
    }
}

impl<A, O, F> Callable for UnaryNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
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
    fn apply_if_script(&mut self, _f: &mut dyn FnMut(&mut ir::Node)) {}
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct UnaryMutNativeFn<A, O, F>(F, PhantomData<(A, O)>);

impl<A, O, F> UnaryMutNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
    F: Fn(&mut A) -> O + 'static,
{
    pub fn new(f: F) -> Self {
        UnaryMutNativeFn(f, PhantomData)
    }

    pub fn description(f: F) -> ModuleFunction {
        let a_ty = Type::primitive::<A>();
        let o_ty = Type::primitive::<O>();
        let ty_scheme = TypeScheme::new_just_type(FnType::new_mut_resolved(&[(a_ty, true)], o_ty));
        Self::description_with_ty_scheme(f, ty_scheme)
    }

    fn description_with_ty_scheme(f: F, ty_scheme: TypeScheme<FnType>) -> ModuleFunction {
        ModuleFunction {
            ty_scheme,
            code: Rc::new(RefCell::new(Box::new(UnaryMutNativeFn::new(f)))),
            spans: None,
        }
    }
}

impl<A, O, F> Callable for UnaryMutNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
    F: Fn(&mut A) -> O,
{
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap().as_mut_primitive::<A>(ctx)?.unwrap();
        Ok(Value::Native(Box::new((self.0)(a))))
    }
    fn apply_if_script(&mut self, _f: &mut dyn FnMut(&mut ir::Node)) {}
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct UnaryNativeFnVP<O, F>(F, PhantomData<O>);

impl<F, O> UnaryNativeFnVP<O, F>
where
    F: Fn(&Value) -> O + 'static,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
{
    pub fn new(f: F) -> Self {
        UnaryNativeFnVP(f, PhantomData)
    }

    pub fn description(f: F) -> ModuleFunction {
        let arg_ty = Type::variable_id(0);
        let o_ty = Type::primitive::<O>();
        ModuleFunction {
            ty_scheme: TypeScheme::new_infer_quantifiers(FnType::new_by_val(
                &[arg_ty],
                o_ty,
            )),
            code: Rc::new(RefCell::new(Box::new(UnaryNativeFnVP(f, PhantomData)))),
            spans: None,
        }
    }
}

impl<O, F> Callable for UnaryNativeFnVP<O, F>
where
    F: Fn(&Value) -> O,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
{
    fn call(&self, args: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap();
        let a = a.as_val().unwrap();
        let o = self.0(a);

        Ok(Value::Native(Box::new(o)))
    }
    fn apply_if_script(&mut self, _f: &mut dyn FnMut(&mut ir::Node)) {}
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}


pub struct BinaryNativeFn<
    A: Clone + 'static,
    B: Clone + 'static,
    O: Debug + Clone + Eq + 'static,
    F: Fn(A, B) -> O + 'static,
>(F, PhantomData<(A, B, O)>);

impl<
        A: Clone + 'static,
        B: Clone + 'static,
        O: Debug + Clone + Eq + NativeDisplay + 'static,
        F: Fn(A, B) -> O + 'static,
    > BinaryNativeFn<A, B, O, F>
{
    pub fn new(f: F) -> Self {
        BinaryNativeFn(f, PhantomData)
    }

    pub fn description(f: F) -> ModuleFunction {
        let a_ty = Type::primitive::<A>();
        let b_ty = Type::primitive::<B>();
        let o_ty = Type::primitive::<O>();
        let ty_scheme = TypeScheme::new_just_type(FnType::new_by_val(&[a_ty, b_ty], o_ty));
        Self::description_with_ty_scheme(f, ty_scheme)
    }

    pub fn description_with_ty_scheme(f: F, ty_scheme: TypeScheme<FnType>) -> ModuleFunction {
        ModuleFunction {
            ty_scheme,
            code: Rc::new(RefCell::new(Box::new(BinaryNativeFn::new(f)))),
            spans: None,
        }
    }
}

impl<A, B, O, F> Callable for BinaryNativeFn<A, B, O, F>
where
    A: Clone + 'static,
    B: Clone + 'static,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
    F: Fn(A, B) -> O,
{
    fn call(&self, args: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap().into_primitive::<A>().unwrap();
        let b = args.next().unwrap().into_primitive::<B>().unwrap();

        Ok(Value::Native(Box::new((self.0)(a, b))))
    }
    fn apply_if_script(&mut self, _f: &mut dyn FnMut(&mut ir::Node)) {}
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct TryBinaryNativeFn<
    A: Clone + 'static,
    B: Clone + 'static,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
    F: Fn(A, B) -> Result<O, RuntimeError> + 'static,
>(F, PhantomData<(A, B, O)>);

impl<
        A: Clone + 'static,
        B: Clone + 'static,
        O: Debug + Clone + Eq + NativeDisplay + 'static,
        F: Fn(A, B) -> Result<O, RuntimeError> + 'static,
    > TryBinaryNativeFn<A, B, O, F>
{
    pub fn new(f: F) -> Self {
        TryBinaryNativeFn(f, PhantomData)
    }

    pub fn description(f: F) -> ModuleFunction {
        let a_ty = Type::primitive::<A>();
        let b_ty = Type::primitive::<B>();
        let o_ty = Type::primitive::<O>();
        ModuleFunction {
            ty_scheme: TypeScheme::new_just_type(FnType::new_by_val(&[a_ty, b_ty], o_ty)),
            code: Rc::new(RefCell::new(Box::new(TryBinaryNativeFn(f, PhantomData)))),
            spans: None,
        }
    }
}

impl<A, B, O, F> Callable for TryBinaryNativeFn<A, B, O, F>
where
    A: Clone + 'static,
    B: Clone + 'static,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
    F: Fn(A, B) -> Result<O, RuntimeError>,
{
    fn call(&self, args: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap().into_primitive::<A>().unwrap();
        let b = args.next().unwrap().into_primitive::<B>().unwrap();

        (self.0)(a, b).map(|o| Value::Native(Box::new(o)))
    }
    fn apply_if_script(&mut self, _f: &mut dyn FnMut(&mut ir::Node)) {}
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct BinaryPartialNativeFn<A, O, F>(F, PhantomData<(A, O)>);

impl<
        A: Clone + 'static,
        O: Debug + Clone + Eq + NativeDisplay + 'static,
        F: Fn(A, Value) -> O + 'static,
    > BinaryPartialNativeFn<A, O, F>
{
    pub fn new(f: F) -> Self {
        BinaryPartialNativeFn(f, PhantomData)
    }

    pub fn description_with_ty_scheme(f: F, ty_scheme: TypeScheme<FnType>) -> ModuleFunction {
        ModuleFunction {
            ty_scheme,
            code: Rc::new(RefCell::new(Box::new(BinaryPartialNativeFn::new(f)))),
            spans: None,
        }
    }
}

impl<A, O, F> Callable for BinaryPartialNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
    F: Fn(A, Value) -> O,
{
    fn call(&self, args: Vec<ValOrMut>, _: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap().into_primitive::<A>().unwrap();
        let b = args.next().unwrap().into_val().unwrap();

        Ok(Value::Native(Box::new((self.0)(a, b))))
    }
    fn apply_if_script(&mut self, _f: &mut dyn FnMut(&mut ir::Node)) {}
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct BinaryPartialMutNativeFn<A, O, F>(F, PhantomData<(A, O)>);

impl<
        A: Clone + 'static,
        O: Debug + Clone + Eq + NativeDisplay + 'static,
        F: Fn(&mut A, Value) -> O + 'static,
    > BinaryPartialMutNativeFn<A, O, F>
{
    pub fn new(f: F) -> Self {
        BinaryPartialMutNativeFn(f, PhantomData)
    }

    pub fn description_with_ty_scheme(f: F, ty_scheme: TypeScheme<FnType>) -> ModuleFunction {
        ModuleFunction {
            ty_scheme,
            code: Rc::new(RefCell::new(Box::new(BinaryPartialMutNativeFn::new(f)))),
            spans: None,
        }
    }
}

impl<A, O, F> Callable for BinaryPartialMutNativeFn<A, O, F>
where
    A: Clone + 'static,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
    F: Fn(&mut A, Value) -> O,
{
    fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult {
        let mut args = args.into_iter();
        let a = args.next().unwrap().as_mut_primitive::<A>(ctx)?.unwrap();
        let b = args.next().unwrap().into_val().unwrap();
        Ok(Value::Native(Box::new((self.0)(a, b))))
    }
    fn apply_if_script(&mut self, _f: &mut dyn FnMut(&mut ir::Node)) {}
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

pub struct BinaryNativeFnVVP<O, F>(F, PhantomData<O>);

impl<F, O> BinaryNativeFnVVP<O, F>
where
    F: Fn(&Value, &Value) -> O + 'static,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
{
    pub fn new(f: F) -> Self {
        BinaryNativeFnVVP(f, PhantomData)
    }

    pub fn description_gen0_gen0(f: F) -> ModuleFunction {
        let arg_ty = Type::variable_id(0);
        let o_ty = Type::primitive::<O>();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
            &[arg_ty, arg_ty],
            o_ty,
        ));
        Self::description_with_ty_scheme(f, ty_scheme)
    }

    pub fn description_with_ty_scheme(f: F, ty_scheme: TypeScheme<FnType>) -> ModuleFunction {
        ModuleFunction {
            ty_scheme,
            code: Rc::new(RefCell::new(Box::new(BinaryNativeFnVVP(f, PhantomData)))),
            spans: None,
        }
    }
}

impl<O, F> Callable for BinaryNativeFnVVP<O, F>
where
    F: Fn(&Value, &Value) -> O,
    O: Debug + Clone + Eq + NativeDisplay + 'static,
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
    fn apply_if_script(&mut self, _f: &mut dyn FnMut(&mut ir::Node)) {}
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{}native @ {:p}", indent_str, &self.0)
    }
}

// Note: disabled for now until we have a borrow checker

// pub struct BinaryNativeFnMMP<O, F>(F, PhantomData<O>);

// impl<F, O> BinaryNativeFnMMP<O, F>
// where
//     F: Fn(&mut Value, &mut Value) -> O + 'static,
//     O: Debug + Clone + Eq + NativeDisplay + 'static,
// {
//     pub fn new(f: F) -> Self {
//         BinaryNativeFnMMP(f, PhantomData)
//     }

//     pub fn description_gen0_gen0(f: F) -> ModuleFunction {
//         let arg_ty = Type::variable_id(0);
//         let o_ty = Type::primitive::<O>();
//         let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
//             &[arg_ty, arg_ty],
//             o_ty,
//         ));
//         Self::description_with_ty_scheme(f, ty_scheme)
//     }

//     pub fn description_with_ty_scheme(f: F, ty_scheme: TypeScheme<FnType>) -> ModuleFunction {
//         ModuleFunction {
//             ty_scheme,
//             code: Rc::new(RefCell::new(Box::new(BinaryNativeFnMMP::new(f)))),
//             spans: None,
//         }
//     }
// }

// impl<O, F> Callable for BinaryNativeFnMMP<O, F>
// where
//     F: Fn(&mut Value, &mut Value) -> O,
//     O: Debug + Clone + Eq + NativeDisplay + 'static,
// {
//     fn call(&self, args: Vec<ValOrMut>, ctx: &mut CallCtx) -> EvalResult {
//         let mut args = args.into_iter();
//         let a = args.next().unwrap();
//         let a = a.as_place().target_mut(ctx)?;
//         let b = args.next().unwrap();
//         let b = b.as_place().target_mut(ctx)?;
//         let o = self.0(a, b);

//         Ok(Value::Native(Box::new(o)))
//     }
//     fn apply_if_script(&mut self, _f: &mut dyn FnMut(&mut ir::Node)) {}
//     fn format_ind(
//         &self,
//         f: &mut std::fmt::Formatter,
//         _env: &ModuleEnv<'_>,
//         indent: usize,
//     ) -> std::fmt::Result {
//         let indent_str = "  ".repeat(indent);
//         writeln!(f, "{}native @ {:p}", indent_str, &self.0)
//     }
// }
