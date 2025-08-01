// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ferlium::{
    containers::IntoSVec2,
    effects::{effect, effects, no_effects, PrimitiveEffect},
    error::{CompilationError, RuntimeError},
    eval::EvalResult,
    function::{
        BinaryNativeFnNNV, FunctionDefinition, NullaryNativeFnN, UnaryNativeFnNN, UnaryNativeFnNV,
        UnaryNativeFnVN,
    },
    module::{Module, Modules},
    r#type::{variant_type, FnType, Type},
    std::{math::int_type, new_std_modules, option::option_type},
    value::Value,
    ModuleAndExpr,
};
use std::{rc::Rc, sync::atomic::AtomicIsize};
use ustr::ustr;

#[derive(Debug)]
pub enum Error {
    Compilation(CompilationError),
    Runtime(RuntimeError),
}

pub type CompileRunResult = Result<Value, Error>;

fn testing_module() -> Module {
    let mut module: Module = Default::default();
    module.functions.insert(
        "some_int".into(),
        UnaryNativeFnNV::description_with_ty(
            |v: isize| Value::tuple_variant(ustr("Some"), [Value::native(v)]),
            ["option"],
            None,
            int_type(),
            option_type(int_type()),
            no_effects(),
        ),
    );
    let pair_variant_type = variant_type([("Pair", Type::tuple([int_type(), int_type()]))]);
    module.functions.insert(
        "pair".into(),
        BinaryNativeFnNNV::description_with_ty(
            |a: isize, b: isize| {
                Value::tuple_variant(ustr("Pair"), [Value::native(a), Value::native(b)])
            },
            ["first", "second"],
            None,
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
    module.functions.insert(
        "read".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            None,
            effect(PrimitiveEffect::Read),
        ),
    );
    module.functions.insert(
        "write".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            None,
            effect(PrimitiveEffect::Write),
        ),
    );
    module.functions.insert(
        "read_write".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            None,
            effects(&[PrimitiveEffect::Read, PrimitiveEffect::Write]),
        ),
    );
    module.functions.insert(
        "take_read".into(),
        UnaryNativeFnVN::description_with_in_ty(
            |_value: Value| 0,
            ["value"],
            None,
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

static PROPERTY_VALUE: AtomicIsize = AtomicIsize::new(0);

pub fn set_property_value(value: isize) {
    PROPERTY_VALUE.store(value, std::sync::atomic::Ordering::Relaxed);
}

pub fn get_property_value() -> isize {
    PROPERTY_VALUE.load(std::sync::atomic::Ordering::Relaxed)
}

fn test_property_module() -> Module {
    use std::sync::atomic::Ordering;
    let mut module: Module = Default::default();
    module.functions.insert(
        "@get my_scope.my_var".into(),
        NullaryNativeFnN::description_with_default_ty(
            || PROPERTY_VALUE.load(Ordering::Relaxed),
            [],
            None,
            effect(PrimitiveEffect::Read),
        ),
    );
    module.functions.insert(
        "@set my_scope.my_var".into(),
        UnaryNativeFnNN::description_with_default_ty(
            |value: isize| PROPERTY_VALUE.store(value, Ordering::Relaxed),
            ["value"],
            None,
            effect(PrimitiveEffect::Write),
        ),
    );
    module
}

/// Compile and run the src and return its module and expression
pub fn try_compile(src: &str) -> Result<(ModuleAndExpr, Modules), CompilationError> {
    let mut other_modules = new_std_modules();
    other_modules.insert("testing".into(), Rc::new(testing_module()));
    other_modules.insert("effects".into(), Rc::new(test_effect_module()));
    other_modules.insert("props".into(), Rc::new(test_property_module()));
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
        .functions
        .get(&ustr(fn_name))
        .expect("Function not found")
        .definition
        .clone()
}

/// Compile and run the src and return its execution result (either a value or an error)
pub fn try_compile_and_run(src: &str) -> CompileRunResult {
    // Compile the source.
    let (ModuleAndExpr { module, expr }, others) = try_compile(src).map_err(Error::Compilation)?;

    // Run the expression if any.
    if let Some(expr) = expr {
        let result = expr.expr.eval().map_err(Error::Runtime)?;
        // ensure that the modules will live during eval, as it holds the strong references to the functions referred in the expression
        drop(module);
        drop(others);
        Ok(result)
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
        Ok(value) => panic!("Expected runtime error, got value: {value}"),
        Err(error) => error,
    }
}

/// Compile and expect a check error
pub fn fail_compilation(src: &str) -> CompilationError {
    match try_compile_and_run(src) {
        Ok(value) => panic!("Expected compilation error, got value: {value}"),
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
