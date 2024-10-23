use std::sync::atomic::AtomicIsize;

use painturscript::{
    effects::{effect, effects, PrimitiveEffect},
    error::{CompilationError, RuntimeError},
    eval::EvalResult,
    function::{NullaryNativeFnN, UnaryNativeFnNN, UnaryNativeFnVN},
    module::{Module, Modules},
    r#type::{FnType, Type},
    std::new_std_module_env,
    value::Value,
    ModuleAndExpr,
};

#[derive(Debug)]
pub enum Error {
    Compilation(CompilationError),
    Runtime(RuntimeError),
}

pub type CompileRunResult = Result<Value, Error>;

fn test_effect_module() -> Module {
    let mut module: Module = Default::default();
    module.functions.insert(
        "read".into(),
        NullaryNativeFnN::description_with_default_ty(|| (), effect(PrimitiveEffect::Read)),
    );
    module.functions.insert(
        "write".into(),
        NullaryNativeFnN::description_with_default_ty(|| (), effect(PrimitiveEffect::Write)),
    );
    module.functions.insert(
        "read_write".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            effects(&[PrimitiveEffect::Read, PrimitiveEffect::Write]),
        ),
    );
    module.functions.insert(
        "take_read".into(),
        UnaryNativeFnVN::description_with_ty(
            |_x: Value| 0,
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
            effect(PrimitiveEffect::Read),
        ),
    );
    module.functions.insert(
        "@set my_scope.my_var".into(),
        UnaryNativeFnNN::description_with_default_ty(
            |value: isize| PROPERTY_VALUE.store(value, Ordering::Relaxed),
            effect(PrimitiveEffect::Write),
        ),
    );
    module
}

/// Compile and run the src and return its module and expression
pub fn try_compile(src: &str) -> Result<(ModuleAndExpr, Modules), CompilationError> {
    let mut other_modules = new_std_module_env();
    other_modules.insert("effects".into(), test_effect_module());
    other_modules.insert("props".into(), test_property_module());
    Ok((
        painturscript::compile(src, &other_modules, &[])?,
        other_modules,
    ))
}

/// Compile the src and return its module and expression
pub fn compile(src: &str) -> (ModuleAndExpr, Modules) {
    try_compile(src).unwrap_or_else(|error| panic!("Compilation error: {error:?}"))
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

/// The value of type unit
pub fn unit() -> Value {
    Value::unit()
}

// macros to construct value easily to make tests more readable

/// A primitive boolean value
#[macro_export]
macro_rules! bool {
    ($b:expr) => {
        Value::native($b)
    };
}

/// A primitive integer value
#[macro_export]
macro_rules! int {
    ($n:expr) => {
        Value::native::<isize>($n)
    };
}

/// An array of integer values
#[macro_export]
macro_rules! int_a {
    [] => {
        Value::native(Array::new())
    };
    [$($elem:expr),+ $(,)?] => {
        Value::native(painturscript::std::array::Array::from_vec(vec![
            $(Value::native::<isize>($elem)),+
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
            $(Value::native::<isize>($elem)),+
        ])
    };
}

/// A primitive string value
#[macro_export]
macro_rules! string {
    ($s:expr) => {{
        use std::str::FromStr;
        Value::native(painturscript::std::string::String::from_str($s).unwrap())
    }};
}
