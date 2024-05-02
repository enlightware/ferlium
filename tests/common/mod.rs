use painturscript::{
    emit_ir::{EmitIrEnv, ModuleEnv},
    error::RuntimeError,
    ir::{EvalCtx, EvalResult},
    parser::parse,
    std::{new_module_with_prelude, new_std_module_env},
    value::Value,
};

/// Compile and run the src and return its execution result (either a value or an error)
pub fn try_run(src: &str) -> EvalResult {
    // parse the source code
    println!("Input: {src}");
    let (module_ast, expr_ast) = parse(src);
    println!("Module AST\n{module_ast}");
    assert_eq!(module_ast.errors(), &[]);
    if let Some(expr) = expr_ast.as_ref() {
        println!("Expr AST\n{expr}");
        assert_eq!(expr.errors(), &[]);
    }

    // setup a module with the prelude
    let other_modules = new_std_module_env();

    // emit IR for the module
    let current_module = new_module_with_prelude();
    let current_module = EmitIrEnv::emit_module(&module_ast, &other_modules, Some(current_module))
        .expect("Error during module IR emission");
    if !current_module.is_empty() {
        println!("Module IR\n{current_module}");
    }

    // emit IR for the expression, and execute it
    let mut emit_env = EmitIrEnv::with_module_env(ModuleEnv::new(&current_module, &other_modules));
    if let Some(expr) = expr_ast {
        let expr_ir = emit_env
            .emit_expr(&expr)
            .expect("Error during expr IR emission");
        println!("Expr IR\n{expr_ir}");
        let mut eval_ctx = EvalCtx::new();
        expr_ir.eval(&mut eval_ctx)
    } else {
        Ok(Value::unit())
    }
}

/// Compile and run the src and return its value
pub fn run(src: &str) -> Value {
    try_run(src).unwrap_or_else(|e| panic!("Runtime error: {e:?}"))
}

/// Compile and run the src and expect a runtime error
pub fn fail_run(src: &str) -> RuntimeError {
    match try_run(src) {
        Ok(value) => panic!("Expected runtime error, got value: {value}"),
        Err(error) => error,
    }
}

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
