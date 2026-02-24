// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ferlium::{
    CompilerSession, ModuleAndExpr, Modules, SourceTable,
    containers::IntoSVec2,
    effects::{PrimitiveEffect, effect, effects, no_effects},
    error::{CompilationError, RuntimeErrorKind},
    eval::{ControlFlow, EvalResult, RuntimeError},
    function::{
        BinaryNativeFnNNV, FunctionDefinition, NullaryNativeFnN, UnaryNativeFnNN, UnaryNativeFnNV,
        UnaryNativeFnVN,
    },
    module::{Module, ModuleEnv, ModuleId, Path},
    std::{
        array::{Array, array_type},
        math::int_type,
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

fn testing_module(module_id: ModuleId) -> Module {
    let mut module = Module::new(module_id);
    module.add_function(
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
    module.add_function(
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

fn test_effect_module(module_id: ModuleId) -> Module {
    let mut module = Module::new(module_id);
    module.add_function(
        "read".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            "Performs a read effect.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "write".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            "Performs a write effect.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_function(
        "read_write".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            "Performs both read and write effects.",
            effects(&[PrimitiveEffect::Read, PrimitiveEffect::Write]),
        ),
    );
    module.add_function(
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

fn test_property_module(module_id: ModuleId) -> Module {
    let mut module = Module::new(module_id);
    module.add_function(
        "@get my_scope.my_var".into(),
        NullaryNativeFnN::description_with_default_ty(
            get_property_value,
            [],
            "Gets the value of my_scope.my_var.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "@set my_scope.my_var".into(),
        UnaryNativeFnNN::description_with_default_ty(
            set_property_value,
            ["value"],
            "Sets the value of my_scope.my_var.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_function(
        "@get my_scope.my_array".into(),
        NullaryNativeFnN::description_with_ty(
            get_array_property_value,
            [],
            "Gets the value of my_scope.my_array.",
            array_type(int_type()),
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
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

macro_rules! ferlium {
    ($name:expr, $file:literal) => {
        ($name, $file, include_str!($file))
    };
}

fn add_deep_modules(session: &mut CompilerSession) {
    for (name, file, code) in [
        ferlium!("deep::level1", "deep_module1.fer"),
        ferlium!("deep::deeper::level2", "deep_module2.fer"),
    ] {
        let path = Path::new(name.split("::").map(ustr).collect());
        session.compile(code, file, path.clone()).unwrap();
    }
}

/// A test session with std, testing, effects and props modules
#[derive(Debug)]
pub struct TestSession {
    session: CompilerSession,
}
impl TestSession {
    /// Create a new test session with std, testing, effects and props modules registered.
    pub fn new() -> Self {
        let mut compiler_session = CompilerSession::new();
        compiler_session.register_module(
            Path::single_str("testing"),
            testing_module(compiler_session.modules().next_id()),
        );
        compiler_session.register_module(
            Path::single_str("effects"),
            test_effect_module(compiler_session.modules().next_id()),
        );
        compiler_session.register_module(
            Path::single_str("props"),
            test_property_module(compiler_session.modules().next_id()),
        );
        add_deep_modules(&mut compiler_session);
        Self {
            session: compiler_session,
        }
    }

    /// Get the modules of this compilation session.
    pub fn modules(&self) -> &Modules {
        self.session.modules()
    }

    /// Get a module environment, with an empty module including the standard library
    /// for debugging purposes.
    pub fn std_module_env(&self) -> ModuleEnv<'_> {
        self.session.module_env()
    }

    /// Get the source table for this compilation session.
    pub fn source_table(&self) -> &SourceTable {
        &self.session.source_table()
    }

    /// Parse a type from a source code and return the corresponding fully-defined Type.
    pub fn resolve_defined_type(&mut self, src: &str) -> Result<Type, CompilationError> {
        self.session.resolve_defined_type_with_std("<test>", src)
    }

    /// Resolve a generic type from a source code and return the corresponding Type,
    /// with placeholder filled with first generic variable.
    pub fn resolve_holed_type(&mut self, src: &str) -> Result<Type, CompilationError> {
        self.session.resolve_holed_type_with_std("<test>", src)
    }

    /// Compile and run the src and return its module and expression
    pub fn try_compile(&mut self, src: &str) -> Result<ModuleAndExpr, CompilationError> {
        self.session
            .compile(src, "<test>", Path::single_str("test"))
    }

    /// Compile the src and return its module and expression
    pub fn compile(&mut self, src: &str) -> ModuleAndExpr {
        self.try_compile(src)
            .unwrap_or_else(|error| panic!("Compilation error: {error:?}"))
    }

    /// Compile and get the module of the src
    pub fn compile_and_get_module(&mut self, src: &str) -> &Module {
        let module_id = self.compile(src).module_id;
        self.session.modules().get(module_id).unwrap()
    }

    /// Compile and get a specific function definition
    pub fn compile_and_get_fn_def(&mut self, src: &str, fn_name: &str) -> FunctionDefinition {
        let module = self.compile_and_get_module(src);
        module
            .get_function(ustr(fn_name))
            .expect("Function not found")
            .definition
            .clone()
    }

    /// Compile and run the src and return its execution result (either a value or an error)
    pub fn try_compile_and_run(&mut self, src: &str) -> CompileRunResult {
        // Compile the source.
        let ModuleAndExpr {
            module_id: module,
            expr,
        } = self.try_compile(src).map_err(Error::Compilation)?;

        // Run the expression if any.
        if let Some(expr) = expr {
            expr.expr
                .eval(module, &self.session)
                .map(ControlFlow::into_value)
                .map_err(Error::Runtime)
        } else {
            Ok(Value::unit())
        }
    }

    /// Compile and run the src and return its execution result (either a value or an error)
    pub fn try_run(&mut self, src: &str) -> EvalResult {
        self.try_compile_and_run(src).map_err(|error| match error {
            Error::Compilation(error) => panic!("Compilation error: {error:?}"),
            Error::Runtime(error) => error,
        })
    }

    /// Compile and run the src and return its value
    pub fn run(&mut self, src: &str) -> Value {
        self.try_run(src)
            .unwrap_or_else(|error| panic!("Runtime error: {error:?}"))
    }

    /// Compile and run the src and expect a runtime error
    pub fn fail_run(&mut self, src: &str) -> RuntimeErrorKind {
        match self.try_run(src) {
            Ok(value) => panic!(
                "Expected runtime error, got value: {}",
                value.to_string_repr()
            ),
            Err(error) => error.kind(),
        }
    }

    /// Compile and expect a check error
    pub fn fail_compilation(&mut self, src: &str) -> CompilationError {
        match self.try_compile_and_run(src) {
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
