// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ferlium::{
    ModuleAndExpr,
    containers::IntoSVec2,
    effects::{PrimitiveEffect, effect, effects, no_effects},
    error::{CompilationError, RuntimeError},
    eval::{ControlFlow, EvalResult},
    function::{
        BinaryNativeFnNNV, FunctionDefinition, NullaryNativeFnN, UnaryNativeFnNN, UnaryNativeFnNV,
        UnaryNativeFnVN,
    },
    module::{Module, Modules},
    std::{
        array::{Array, array_type},
        math::int_type,
        new_std_modules,
        option::option_type,
    },
    r#type::{FnType, Type, variant_type},
    value::Value,
};
use std::{cell::RefCell, sync::atomic::AtomicIsize};
use ustr::ustr;

#[derive(Debug)]
pub enum Error {
    Compilation(CompilationError),
    Runtime(RuntimeError),
}

pub type CompileRunResult = Result<Value, Error>;

fn testing_module() -> Module {
    let mut module: Module = Default::default();
    module.add_named_function(
        "some_int".into(),
        UnaryNativeFnNV::description_with_ty(
            |v: isize| Value::tuple_variant(ustr("Some"), [Value::native(v)]),
            ["option"],
            "Wraps an integer into an Option variant.",
            int_type(),
            option_type(int_type()),
            no_effects(),
        ),
    );
    let pair_variant_type = variant_type([("Pair", Type::tuple([int_type(), int_type()]))]);
    module.add_named_function(
        "pair".into(),
        BinaryNativeFnNNV::description_with_ty(
            |a: isize, b: isize| {
                Value::tuple_variant(ustr("Pair"), [Value::native(a), Value::native(b)])
            },
            ["first", "second"],
            "Creates a Pair variant from two integers.",
            int_type(),
            int_type(),
            pair_variant_type,
            no_effects(),
        ),
    );
    module
}

fn test_effect_module() -> Module {
    let mut module: Module = Default::default();
    module.add_named_function(
        "read".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            "Performs a read effect.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_named_function(
        "write".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            "Performs a write effect.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_named_function(
        "read_write".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            "Performs both read and write effects.",
            effects(&[PrimitiveEffect::Read, PrimitiveEffect::Write]),
        ),
    );
    module.add_named_function(
        "take_read".into(),
        UnaryNativeFnVN::description_with_in_ty(
            |_value: Value| (),
            ["value"],
            "Takes a first-class function that performs a read effect, and fake call it.",
            Type::function_type(FnType::new(
                vec![],
                Type::unit(),
                effect(PrimitiveEffect::Read),
            )),
            effect(PrimitiveEffect::Read),
        ),
    );
    module
}

static INT_PROPERTY_VALUE: AtomicIsize = AtomicIsize::new(0);

pub fn set_property_value(value: isize) {
    INT_PROPERTY_VALUE.store(value, std::sync::atomic::Ordering::Relaxed);
}

pub fn get_property_value() -> isize {
    INT_PROPERTY_VALUE.load(std::sync::atomic::Ordering::Relaxed)
}

thread_local! {
    static INT_ARRAY_PROPERTY_VALUE: RefCell<Array> = RefCell::new(Array::new());
}

pub fn set_array_property_value(value: Array) {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| *cell.borrow_mut() = value);
}

pub fn get_array_property_value() -> Array {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| cell.borrow().clone())
}

fn test_property_module() -> Module {
    let mut module: Module = Default::default();
    module.add_named_function(
        "@get my_scope.my_var".into(),
        NullaryNativeFnN::description_with_default_ty(
            get_property_value,
            [],
            "Gets the value of my_scope.my_var.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_named_function(
        "@set my_scope.my_var".into(),
        UnaryNativeFnNN::description_with_default_ty(
            set_property_value,
            ["value"],
            "Sets the value of my_scope.my_var.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_named_function(
        "@get my_scope.my_array".into(),
        NullaryNativeFnN::description_with_ty(
            get_array_property_value,
            [],
            "Gets the value of my_scope.my_array.",
            array_type(int_type()),
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_named_function(
        "@set my_scope.my_array".into(),
        UnaryNativeFnNN::description_with_in_ty(
            set_array_property_value,
            ["value"],
            "Sets the value of my_scope.my_array.",
            array_type(int_type()),
            effect(PrimitiveEffect::Write),
        ),
    );
    module
}

/// Compile and run the src and return its module and expression
pub fn try_compile(src: &str) -> Result<(ModuleAndExpr, Modules), CompilationError> {
    let mut other_modules = new_std_modules();
    other_modules.register_module(ustr("testing"), testing_module());
    other_modules.register_module(ustr("effects"), test_effect_module());
    other_modules.register_module(ustr("props"), test_property_module());
    Ok((ferlium::compile(src, &other_modules, &[])?, other_modules))
}

/// Compile the src and return its module and expression
pub fn compile(src: &str) -> (ModuleAndExpr, Modules) {
    try_compile(src).unwrap_or_else(|error| panic!("Compilation error: {error:?}"))
}

/// Compile and get a specific function definition
pub fn compile_and_get_fn_def(src: &str, fn_name: &str) -> FunctionDefinition {
    compile(src)
        .0
        .module
        .get_own_function(ustr(fn_name))
        .expect("Function not found")
        .definition
        .clone()
}

/// Compile and run the src and return its execution result (either a value or an error)
pub fn try_compile_and_run(src: &str) -> CompileRunResult {
    // Compile the source.
    let (ModuleAndExpr { module, expr }, ..) = try_compile(src).map_err(Error::Compilation)?;

    // Run the expression if any.
    if let Some(expr) = expr {
        expr.expr
            .eval(module)
            .map(ControlFlow::into_value)
            .map_err(Error::Runtime)
    } else {
        Ok(Value::unit())
    }
}

/// Compile and run the src and return its execution result (either a value or an error)
pub fn try_run(src: &str) -> EvalResult {
    try_compile_and_run(src).map_err(|error| match error {
        Error::Compilation(error) => panic!("Compilation error: {error:?}"),
        Error::Runtime(error) => error,
    })
}

/// Compile and run the src and return its value
pub fn run(src: &str) -> Value {
    try_run(src).unwrap_or_else(|error| panic!("Runtime error: {error:?}"))
}

/// Compile and run the src and expect a runtime error
pub fn fail_run(src: &str) -> RuntimeError {
    match try_run(src) {
        Ok(value) => panic!(
            "Expected runtime error, got value: {}",
            value.to_string_repr()
        ),
        Err(error) => error,
    }
}

/// Compile and expect a check error
pub fn fail_compilation(src: &str) -> CompilationError {
    match try_compile_and_run(src) {
        Ok(value) => panic!(
            "Expected compilation error, got value: {}",
            value.to_string_repr()
        ),
        Err(error) => match error {
            Error::Compilation(error) => error,
            _ => panic!("Expected compilation error, got {error:?}"),
        },
    }
}

// helper functions to construct values easily to make tests more readable

/// The value of type unit
pub fn unit() -> Value {
    Value::unit()
}

/// A primitive boolean value
pub fn bool(b: bool) -> Value {
    Value::native(b)
}

/// A primitive integer value
pub fn int(n: isize) -> Value {
    Value::native(n)
}

/// A primitive float value
pub fn float(f: f64) -> Value {
    Value::native(ferlium::std::math::Float::new(f).unwrap())
}

/// A primitive string value
pub fn string(s: &str) -> Value {
    use std::str::FromStr;
    Value::native(ferlium::std::string::String::from_str(s).unwrap())
}
/// A variant value of given tag and no values
pub fn variant_0(tag: &str) -> Value {
    Value::unit_variant(ustr(tag))
}

/// A variant value of given tag and exactly 1 value
pub fn variant_t1(tag: &str, value: Value) -> Value {
    Value::tuple_variant(ustr(tag), [value])
}

/// A variant value of given tag and N values
pub fn variant_tn(tag: &str, values: impl IntoSVec2<Value>) -> Value {
    Value::tuple_variant(ustr(tag), values)
}

// macros to construct values easily to make tests more readable

/// An array of boolean values
#[macro_export]
macro_rules! bool_a {
    [] => {
        Value::native(Array::new())
    };
    [$($elem:expr),+ $(,)?] => {
        Value::native(ferlium::std::array::Array::from_vec(vec![
            $(Value::native::<bool>($elem)),+
        ]))
    };
}

/// An array of integer values
#[macro_export]
macro_rules! int_a {
    [] => {
        Value::native(ferlium::std::array::Array::new())
    };
    [$($elem:expr),+ $(,)?] => {
        Value::native(ferlium::std::array::Array::from_vec(vec![
            $(Value::native::<ferlium::std::math::Int>($elem)),+
        ]))
    };
}

/// An array of float values
#[macro_export]
macro_rules! float_a {
    [] => {
        Value::native(ferlium::std::array::Array::new())
    };
    [$($elem:expr),+ $(,)?] => {
        Value::native(ferlium::std::array::Array::from_vec(vec![
            $(Value::native::<ferlium::std::math::Float>(ferlium::std::math::Float::new($elem).unwrap())),+
        ]))
    };
}

/// A tuple of integer values
#[macro_export]
macro_rules! int_tuple {
    () => {
        Value::tuple(vec![])
    };
    ($($elem:expr),+ $(,)?) => {
        Value::tuple(vec![
            $(Value::native::<ferlium::std::math::Int>($elem)),+
        ])
    };
}

/// An tuple of values
#[macro_export]
macro_rules! tuple {
    () => {
        Value::tuple([])
    };
    ($($elem:expr),+ $(,)?) => {
        Value::tuple(vec![
            $($elem),+
        ])
    };
}

/// An array of values
#[macro_export]
macro_rules! array {
    [] => {
        Value::native(ferlium::std::array::Array::new())
    };
    [$($elem:expr),+ $(,)?] => {
        Value::native(ferlium::std::array::Array::from_vec(vec![
            $($elem),+
        ]))
    };
}
