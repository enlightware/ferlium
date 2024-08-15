use ariadne::Label;
use lrpar::Span;
use painturscript::emit_ir::{emit_expr_top_level, emit_module};
use painturscript::error::{resolve_must_be_mutable_ctx, InternalCompilationError};
use painturscript::format::FormatWith;
use painturscript::module::{FmtWithModuleEnv, ModuleEnv};
use painturscript::std::{new_module_with_prelude, new_std_module_env};
use painturscript::typing_env::Local;
use rustyline::DefaultEditor;
use rustyline::{config::Configurer, error::ReadlineError};

use painturscript::ir::EvalCtx;

fn start_of_line_of(src: &str, pos: usize) -> usize {
    if pos >= src.len() {
        // FIXME: handle better cross-input error references
        return src.len();
    }
    src[..pos].rfind('\n').map_or(0, |i| i + 1)
}

fn span_range(span: Span) -> std::ops::Range<usize> {
    span.start()..span.end()
}

fn pretty_print_checking_error(error: &InternalCompilationError, data: &(ModuleEnv<'_>, &str)) {
    use ariadne::{Color, Fmt, Report, ReportKind, Source};
    use InternalCompilationError::*;
    let env = &data.0;
    let src = data.1;
    match error {
        SymbolNotFound(span) => {
            let offset = start_of_line_of(src, span.start());
            let name = &data.1[span_range(*span)];
            Report::build(ReportKind::Error, "input", offset)
                .with_message(format!(
                    "Variable or function {} not found.",
                    name.fg(Color::Blue)
                ))
                .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        FunctionNotFound(span) => {
            let offset = start_of_line_of(src, span.start());
            let name = &data.1[span_range(*span)];
            Report::build(ReportKind::Error, "input", offset)
                .with_message(format!("Function {} not found.", name.fg(Color::Blue)))
                .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        MustBeMutable(cur_span, reason_span, ctx) => {
            let (cur_span, reason_span) =
                resolve_must_be_mutable_ctx(*cur_span, *reason_span, *ctx, src);
            let min_pos = cur_span.start().min(reason_span.start());
            let offset = start_of_line_of(src, min_pos);
            let cur = &data.1[span_range(cur_span)];
            Report::build(ReportKind::Error, "input", offset)
                .with_message(format!(
                    "Expression {} must be mutable.",
                    cur.fg(Color::Blue),
                ))
                .with_label(
                    Label::new(("input", span_range(cur_span)))
                        .with_message("This expression is just a value.")
                        .with_color(Color::Blue),
                )
                .with_label(
                    Label::new(("input", span_range(reason_span)))
                        .with_message("But it must be mutable due to this.")
                        .with_color(Color::Green)
                        .with_order(1),
                )
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        IsNotSubtype(cur, cur_span, exp, exp_span) => {
            let min_pos = cur_span.start().min(exp_span.start());
            let offset = start_of_line_of(src, min_pos);
            Report::build(ReportKind::Error, "input", offset)
                .with_message(format!(
                    "Type {} is incompatible with type {} (i.e. not a sub-type).",
                    cur.format_with(env).fg(Color::Blue),
                    exp.format_with(env).fg(Color::Blue)
                ))
                .with_label(Label::new(("input", span_range(*cur_span))).with_color(Color::Blue))
                .with_label(Label::new(("input", span_range(*exp_span))).with_color(Color::Blue))
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        UnboundTypeVar { ty_var, ty, span } => {
            let offset = start_of_line_of(src, span.start());
            Report::build(ReportKind::Error, "input", offset)
                .with_message(format!(
                    "Unbound type variable {} in type {}.",
                    ty_var.fg(Color::Blue),
                    ty.format_with(env).fg(Color::Blue)
                ))
                .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        InvalidTupleIndex {
            index,
            index_span,
            tuple_length,
            tuple_span,
        } => {
            let offset = start_of_line_of(src, tuple_span.start());
            let colored_index = (*index).fg(Color::Blue);
            Report::build(ReportKind::Error, "input", offset)
                .with_message(format!("Tuple index {} is out of bounds.", colored_index))
                .with_label(
                    Label::new(("input", span_range(*index_span)))
                        .with_message(format!("Index is {}.", colored_index))
                        .with_color(Color::Blue),
                )
                .with_label(
                    Label::new(("input", span_range(*tuple_span)))
                        .with_message(format!(
                            "But tuple has only {} elements.",
                            (*tuple_length).fg(Color::Blue)
                        ))
                        .with_color(Color::Green)
                        .with_order(1),
                )
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        InvalidTupleProjection {
            expr_ty,
            expr_span,
            index_span,
        } => {
            let offset = start_of_line_of(src, expr_span.start());
            let colored_ty = expr_ty.format_with(env).fg(Color::Blue);
            Report::build(ReportKind::Error, "input", offset)
                .with_message(format!(
                    "Type {} cannot be projected as a tuple.",
                    colored_ty
                ))
                .with_label(
                    Label::new(("input", span_range(*expr_span)))
                        .with_message(format!("This expression has type {}.", colored_ty))
                        .with_color(Color::Blue),
                )
                .with_label(
                    Label::new(("input", span_range(*index_span)))
                        .with_message(format!(
                            "But a tuple is needed due to projection {}.",
                            "here".fg(Color::Green)
                        ))
                        .with_color(Color::Green)
                        .with_order(1),
                )
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        MutablePathsOverlap {
            a_span,
            b_span,
            fn_span,
        } => {
            let min_pos = a_span.start().min(b_span.start());
            let offset = start_of_line_of(src, min_pos);
            let a_name = &data.1[span_range(*a_span)];
            let b_name = &data.1[span_range(*b_span)];
            let fn_name = &data.1[span_range(*fn_span)];
            Report::build(ReportKind::Error, "input", offset)
                .with_message(format!(
                    "Mutable paths {} and {} overlap when calling {}.",
                    a_name.fg(Color::Blue),
                    b_name.fg(Color::Blue),
                    fn_name.fg(Color::Green)
                ))
                .with_label(Label::new(("input", span_range(*a_span))).with_color(Color::Blue))
                .with_label(Label::new(("input", span_range(*b_span))).with_color(Color::Blue))
                .with_label(Label::new(("input", span_range(*fn_span))).with_color(Color::Green))
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        UndefinedVarInStringFormatting {
            var_span,
            string_span,
        } => {
            let offset = start_of_line_of(src, string_span.start());
            let var_name = &data.1[span_range(*var_span)];
            let string = &data.1[span_range(*string_span)];
            Report::build(ReportKind::Error, "input", offset)
                .with_message(format!(
                    "Undefined variable {} used in string formatting {}.",
                    var_name.fg(Color::Blue),
                    string.fg(Color::Blue)
                ))
                .with_label(Label::new(("input", span_range(*var_span))).with_color(Color::Blue))
                .with_label(Label::new(("input", span_range(*string_span))))
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        _ => println!(
            "Module emission error: {}",
            FormatWith { value: error, data }
        ),
    }
}

fn main() {
    // Logging
    env_logger::init();

    // Painturscript emission and evaluation contexts
    let other_modules = new_std_module_env();
    let mut module = new_module_with_prelude();
    let mut locals: Vec<Local> = vec![];
    let mut eval_ctx = EvalCtx::new();

    // REPL loop
    let mut rl = DefaultEditor::new().unwrap();
    rl.set_max_history_size(256).unwrap();
    let history_filename = "pscript_history.txt";
    if rl.load_history(history_filename).is_err() {
        println!("No previous history.");
    }
    loop {
        // Show locals
        println!();
        if locals.is_empty() {
            println!("No locals.");
        } else {
            println!("Locals:");
            for (i, local) in locals.iter().enumerate() {
                println!(
                    "{} {}: {} = {}",
                    local
                        .mutable
                        .as_resolved()
                        .expect("unresolved mutability in local")
                        .var_def_string(),
                    local.name,
                    local
                        .ty
                        .display_rust_style(&ModuleEnv::new(&module, &other_modules)),
                    eval_ctx.environment[eval_ctx.frame_base + i]
                        .as_val()
                        .expect("reference found in REPL locals"),
                );
            }
        }

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
        if src.is_empty() {
            continue;
        }

        // Parse input
        let (module_ast, expr_ast) = painturscript::parser::parse(&src);
        if !module_ast.is_empty() {
            let env = ModuleEnv::new(&module, &other_modules);
            println!("Module AST:\n{}", module_ast.format_with(&env));
        }
        if let Some(expr_ast) = expr_ast.as_ref() {
            println!("Expr AST:\n{expr_ast}");
        }

        // Validate module AST
        let parse_errors = module_ast.errors();
        if !parse_errors.is_empty() {
            println!("Module parse errors:");
            for e in parse_errors {
                println!("{}", e.0);
            }
            continue;
        }

        // Compile module
        if !module_ast.is_empty() {
            module = match emit_module(&module_ast, &other_modules, Some(&module)) {
                Ok(module) => module,
                Err(e) => {
                    let env = ModuleEnv::new(&module, &other_modules);
                    pretty_print_checking_error(&e, &(env, src.as_str()));
                    continue;
                }
            };
            println!("Module IR:\n{}", FormatWith::new(&module, &other_modules));
        }

        // Is there an expression?
        let expr_ast = match expr_ast {
            Some(expr) => expr,
            None => {
                println!("No expression to evaluate.");
                continue;
            }
        };

        // Validate expression AST
        let expr_errors = expr_ast.errors();
        if !expr_errors.is_empty() {
            println!("Expression parse errors:");
            for e in expr_errors {
                println!("{}", e.0);
            }
            continue;
        }

        // Compile and evaluate expression
        let module_env = ModuleEnv::new(&module, &other_modules);
        let expr_ir = emit_expr_top_level(&expr_ast, module_env, locals.clone());
        let compiled_expr = match expr_ir {
            Ok(res) => res,
            Err(e) => {
                pretty_print_checking_error(&e, &(module_env, src.as_str()));
                continue;
            }
        };
        locals = compiled_expr.locals;
        println!("Expr IR:\n{}", compiled_expr.expr.format_with(&module_env));

        // Evaluate and print result
        let old_size = eval_ctx.environment.len();
        let old_frame_base = eval_ctx.frame_base;
        let result = compiled_expr.expr.eval_with_ctx(&mut eval_ctx);
        match result {
            Ok(value) => println!(
                "{value}: {}",
                compiled_expr.ty.display_rust_style(&module_env)
            ),
            Err(error) => {
                // We must restore the context as before starting the evaluation
                eval_ctx.environment.truncate(old_size);
                eval_ctx.frame_base = old_frame_base;
                println!("Runtime error: {error:?}")
            }
        }

        if let Err(e) = rl.save_history(history_filename) {
            println!("Failed to save history: {:?}", e);
        }
    }
}
