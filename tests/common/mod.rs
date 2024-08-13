use painturscript::{
    compile,
    error::{CompilationError, RuntimeError},
    ir::EvalResult,
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

/// Compile and run the src and return its execution result (either a value or an error)
pub fn try_compile_and_run(src: &str) -> CompileRunResult {
    // Compile the source.
    let other_modules = new_std_module_env();
    let ModuleAndExpr { module, expr } =
        compile(src, &other_modules).map_err(Error::Compilation)?;

    // Run the expression if any.
    if let Some(expr) = expr {
        let result = expr.expr.eval().map_err(Error::Runtime)?;
        drop(module); // ensure that the module will live during eval, as it holds the strong references to the functions refered in the expression
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
