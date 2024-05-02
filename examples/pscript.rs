use painturscript::emit_ir::ModuleEnv;
use painturscript::std::{new_module_with_prelude, new_std_module_env};
use rustyline::DefaultEditor;
use rustyline::{config::Configurer, error::ReadlineError};

use painturscript::{emit_ir::EmitIrEnv, ir::EvalCtx};

fn main() {
    // Painturscript emission and evaluation contexts
    let other_modules = new_std_module_env();
    let mut module = new_module_with_prelude();
    let mut locals = vec![];
    let mut eval_ctx = EvalCtx::new();

    // REPL loop
    let mut rl = DefaultEditor::new().unwrap();
    rl.set_max_history_size(256).unwrap();
    let history_filename = "pscript_history.txt";
    if rl.load_history(history_filename).is_err() {
        println!("No previous history.");
    }
    loop {
        // Read input
        let readline = rl.readline(">> ");
        let src = match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str()).unwrap();
                line
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                return;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                return;
            }
            Err(err) => {
                println!("Readline Error: {:?}", err);
                return;
            }
        };

        // Parse input
        let (module_ast, expr_ast) = painturscript::parser::parse(&src);
        if !module_ast.is_empty() {
            println!("Module AST:\n{module_ast}");
        }
        if let Some(expr_ast) = expr_ast.as_ref() {
            println!("Expr AST:\n{expr_ast}");
        }
        let parse_errors = module_ast.errors();
        if !parse_errors.is_empty() {
            println!("Parse errors:");
            for e in parse_errors {
                println!("{}", e.0);
            }
            continue;
        }

        // Compile module
        if !module_ast.is_empty() {
            module = match EmitIrEnv::emit_module(&module_ast, &other_modules, Some(module.clone()))
            {
                Ok(module) => module,
                Err(e) => {
                    println!("Module emission error: {:?}", e);
                    continue;
                }
            };
            println!("Module IR:\n{module}");
        }

        // Compile and evaluate expression
        let expr = match expr_ast {
            Some(expr) => expr,
            None => {
                println!("No expression to evaluate.");
                continue;
            }
        };
        let mut emit_env = EmitIrEnv::new(locals, ModuleEnv::new(&module, &other_modules));
        let expr_ir = emit_env.emit_expr(&expr);
        locals = emit_env.get_locals_and_drop();
        let ir = match expr_ir {
            Ok(ir) => ir,
            Err(e) => {
                println!("Emission error: {:?}", e);
                continue;
            }
        };
        println!("Expr IR:\n{ir}");

        // Evaluate and print result
        let result = ir.eval(&mut eval_ctx);
        match result {
            Ok(value) => println!("{value}"),
            Err(error) => println!("Runtime error: {error:?}"),
        }

        if let Err(e) = rl.save_history(history_filename) {
            println!("Failed to save history: {:?}", e);
        }
    }
}
