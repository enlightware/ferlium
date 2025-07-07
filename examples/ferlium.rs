// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::env;
use std::io::{self, IsTerminal, Read};
use std::ops::Deref;

use ariadne::Label;
use ferlium::emit_ir::{emit_expr, emit_module};
use ferlium::error::{
    resolve_must_be_mutable_ctx, InternalCompilationError, InternalCompilationErrorImpl,
    LocatedError, MutabilityMustBeWhat,
};
use ferlium::format::FormatWith;
use ferlium::module::{FmtWithModuleEnv, ModuleEnv};
use ferlium::std::{new_module_using_std, new_std_modules};
use ferlium::typing_env::Local;
use ferlium::Location;
use ferlium::{parse_module_and_expr, SubOrSameType};
use rustyline::DefaultEditor;
use rustyline::{config::Configurer, error::ReadlineError};
use ustr::ustr;

use ferlium::eval::EvalCtx;

fn span_range(span: Location) -> std::ops::Range<usize> {
    span.start()..span.end()
}

fn span_union_range(span1: Location, span2: Location) -> std::ops::Range<usize> {
    span1.start().min(span2.start())..span1.end().max(span2.end())
}

fn pretty_print_parse_errors(src: &str, errors: &[LocatedError]) {
    use ariadne::{Color, Report, ReportKind, Source};
    for (text, span) in errors {
        Report::build(ReportKind::Error, ("input", span_range(*span)))
            .with_message(format!("Parse error: {text}.",))
            .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
            .finish()
            .print(("input", Source::from(src)))
            .unwrap();
    }
}

fn pretty_print_checking_error(error: &InternalCompilationError, data: &(ModuleEnv<'_>, &str)) {
    use ariadne::{Color, Fmt, Report, ReportKind, Source};
    use InternalCompilationErrorImpl::*;
    let env = &data.0;
    let src = data.1;
    match error.deref() {
        SymbolNotFound(span) => {
            let name = &data.1[span_range(*span)];
            Report::build(ReportKind::Error, ("input", span_range(*span)))
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
            let name = &data.1[span_range(*span)];
            Report::build(ReportKind::Error, ("input", span_range(*span)))
                .with_message(format!("Function {} not found.", name.fg(Color::Blue)))
                .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        WrongNumberOfArguments {
            expected,
            expected_span,
            got,
            got_span,
        } => {
            Report::build(ReportKind::Error, ("input", span_range(*expected_span)))
                .with_message(format!(
                    "Wrong number of arguments: expected {} but found {}.",
                    expected.fg(Color::Blue),
                    got.fg(Color::Magenta)
                ))
                .with_label(
                    Label::new(("input", span_range(*expected_span))).with_color(Color::Blue),
                )
                .with_label(Label::new(("input", span_range(*got_span))).with_color(Color::Magenta))
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        MutabilityMustBe {
            source_span,
            reason_span,
            what,
            ctx,
        } => {
            let (source_span, reason_span) =
                resolve_must_be_mutable_ctx(*source_span, *reason_span, *ctx, src);
            let span = span_union_range(source_span, reason_span);
            let source = &data.1[span_range(source_span)];
            let reason = &data.1[span_range(reason_span)];
            use MutabilityMustBeWhat::*;
            match what {
                Mutable => Report::build(ReportKind::Error, ("input", span))
                    .with_message(format!(
                        "Expression {} must be mutable.",
                        source.fg(Color::Blue),
                    ))
                    .with_label(
                        Label::new(("input", span_range(source_span)))
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
                    .unwrap(),
                Constant => Report::build(ReportKind::Error, ("input", span))
                    .with_message(format!(
                        "Expression {} must be constant.",
                        source.fg(Color::Blue),
                    ))
                    .with_label(
                        Label::new(("input", span_range(source_span)))
                            .with_message("This expression is mutable.")
                            .with_color(Color::Blue),
                    )
                    .with_label(
                        Label::new(("input", span_range(reason_span)))
                            .with_message("But it must be constant due to this.")
                            .with_color(Color::Green)
                            .with_order(1),
                    )
                    .finish()
                    .print(("input", Source::from(src)))
                    .unwrap(),
                Equal => Report::build(ReportKind::Error, ("input", span))
                    .with_message(format!(
                        "Expressions {} and {} must have the same mutability.",
                        source.fg(Color::Blue),
                        reason.fg(Color::Green),
                    ))
                    .with_label(
                        Label::new(("input", span_range(source_span)))
                            .with_message("There.")
                            .with_color(Color::Blue),
                    )
                    .with_label(
                        Label::new(("input", span_range(reason_span)))
                            .with_message("And here.")
                            .with_color(Color::Green)
                            .with_order(1),
                    )
                    .finish()
                    .print(("input", Source::from(src)))
                    .unwrap(),
            }
        }
        TypeMismatch {
            current_ty,
            current_span,
            expected_ty,
            expected_span,
            sub_or_same,
        } => {
            let span = span_union_range(*current_span, *expected_span);
            use SubOrSameType::*;
            let extra_reason = match sub_or_same {
                SubType => "not a subtype",
                SameType => "not the same type",
            };
            Report::build(ReportKind::Error, ("input", span))
                .with_message(format!(
                    "Type {} is incompatible with type {} (i.e. {}).",
                    current_ty.format_with(env).fg(Color::Magenta),
                    expected_ty.format_with(env).fg(Color::Blue),
                    extra_reason
                ))
                .with_label(
                    Label::new(("input", span_range(*current_span))).with_color(Color::Magenta),
                )
                .with_label(
                    Label::new(("input", span_range(*expected_span))).with_color(Color::Blue),
                )
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        UnboundTypeVar { ty_var, ty, span } => {
            Report::build(ReportKind::Error, ("input", span_range(*span)))
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
            let span = span_union_range(*index_span, *tuple_span);
            let colored_index = (*index).fg(Color::Blue);
            Report::build(ReportKind::Error, ("input", span))
                .with_message(format!("Tuple index {colored_index} is out of bounds."))
                .with_label(
                    Label::new(("input", span_range(*index_span)))
                        .with_message(format!("Index is {colored_index}."))
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
            tuple_ty: expr_ty,
            tuple_span,
            index_span,
        } => {
            let span = span_union_range(*tuple_span, *index_span);
            let colored_ty = expr_ty.format_with(env).fg(Color::Blue);
            Report::build(ReportKind::Error, ("input", span))
                .with_message(format!(
                    "Type {colored_ty} cannot be projected as a tuple."
                ))
                .with_label(
                    Label::new(("input", span_range(*tuple_span)))
                        .with_message(format!("This expression has type {colored_ty}."))
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
        DuplicatedRecordField {
            first_occurrence,
            second_occurrence,
            ..
        } => {
            let span = span_union_range(*first_occurrence, *second_occurrence);
            let name = &data.1[span_range(*first_occurrence)];
            Report::build(ReportKind::Error, ("input", span))
                .with_message(format!(
                    "Duplicated field \"{}\" in record.",
                    name.fg(Color::Blue)
                ))
                .with_label(
                    Label::new(("input", span_range(*first_occurrence))).with_color(Color::Blue),
                )
                .with_label(
                    Label::new(("input", span_range(*second_occurrence))).with_color(Color::Blue),
                )
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        InvalidVariantConstructor { span } => {
            let name = &data.1[span_range(*span)];
            Report::build(ReportKind::Error, ("input", span_range(*span)))
                .with_message(format!(
                    "Variant constructor cannot be a path, but {} is.",
                    name.fg(Color::Blue)
                ))
                .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
                .finish()
                .print(("input", Source::from(src)))
                .unwrap();
        }
        InconsistentADT {
            a_type,
            a_span,
            b_type,
            b_span,
        } => {
            let span = span_union_range(*a_span, *b_span);
            let a_ty = a_type.adt_kind().fg(Color::Blue);
            let b_ty = b_type.adt_kind().fg(Color::Magenta);
            Report::build(ReportKind::Error, ("input", span))
                .with_message(format!(
                    "Data type {a_ty} is different than data type {b_ty}."
                ))
                .with_label(
                    Label::new(("input", span_range(*a_span)))
                        .with_message(format!("type is {a_ty} here"))
                        .with_color(Color::Blue),
                )
                .with_label(
                    Label::new(("input", span_range(*b_span)))
                        .with_message(format!("but type is {b_ty} here"))
                        .with_color(Color::Magenta),
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
            let span = span_union_range(*a_span, *b_span);
            let a_name = &data.1[span_range(*a_span)];
            let b_name = &data.1[span_range(*b_span)];
            let fn_name = &data.1[span_range(*fn_span)];
            Report::build(ReportKind::Error, ("input", span))
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
            let span = span_union_range(*var_span, *string_span);
            let var_name = &data.1[span_range(*var_span)];
            let string = &data.1[span_range(*string_span)];
            Report::build(ReportKind::Error, ("input", span))
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
        Unsupported { span, reason } => {
            Report::build(ReportKind::Error, ("input", span_range(*span)))
                .with_message(format!("Unsupported feature: {reason}."))
                .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
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

fn print_help() {
    println!("Available commands:");
    println!("\\help: Show this help message.");
    println!("\\module: Show the current module.");
    println!("CTRL-D: Exit the REPL.");
}

/// Process a single input: parse, compile module, and evaluate expression if present.
/// Returns Ok(true) if successful, Ok(false) if there was an error but we should continue,
/// and Err(exit_code) if we should exit with the given code.
fn process_input(
    input: &str,
    module: &mut ferlium::module::Module,
    other_modules: &ferlium::module::Modules,
    locals: &mut Vec<Local>,
    eval_ctx: &mut EvalCtx,
    is_repl: bool,
) -> Result<bool, i32> {
    // Parse input
    let parse_result = parse_module_and_expr(input, true);
    let (module_ast, expr_ast) = match parse_result {
        Ok(result) => result,
        Err(errors) => {
            if is_repl {
                pretty_print_parse_errors(input, &errors);
                return Ok(false);
            } else {
                eprintln!("Parse errors:");
                pretty_print_parse_errors(input, &errors);
                return Err(1);
            }
        }
    };

    // Debug output for REPL
    if is_repl {
        let env = ModuleEnv::new(module, other_modules);
        if !module_ast.is_empty() {
            println!("Module AST:\n{}", module_ast.format_with(&env));
        }
        if let Some(expr_ast) = expr_ast.as_ref() {
            println!("Expr AST:\n{}", expr_ast.format_with(&env));
        }
    }

    // Compile module if present
    if !module_ast.is_empty() {
        *module = match emit_module(module_ast, other_modules, Some(module)) {
            Ok(new_module) => new_module,
            Err(e) => {
                let env = ModuleEnv::new(module, other_modules);
                if is_repl {
                    pretty_print_checking_error(&e, &(env, input));
                    return Ok(false);
                } else {
                    eprintln!("Module compilation error:");
                    pretty_print_checking_error(&e, &(env, input));
                    return Err(1);
                }
            }
        };
        if is_repl {
            println!("Module IR:\n{}", FormatWith::new(module, other_modules));
        }
    }
    module.source = Some(input.to_string());

    // If there's an expression, compile and evaluate it
    if let Some(expr_ast) = expr_ast {
        let module_env = ModuleEnv::new(module, other_modules);
        let expr_ir = emit_expr(expr_ast, module_env, locals.clone());
        let compiled_expr = match expr_ir {
            Ok(res) => res,
            Err(e) => {
                if is_repl {
                    pretty_print_checking_error(&e, &(module_env, input));
                    return Ok(false);
                } else {
                    eprintln!("Expression compilation error:");
                    pretty_print_checking_error(&e, &(module_env, input));
                    return Err(1);
                }
            }
        };

        *locals = compiled_expr.locals;
        if is_repl {
            println!("Expr IR:\n{}", compiled_expr.expr.format_with(&module_env));
        }

        // Evaluate expression
        let old_size = eval_ctx.environment.len();
        let old_frame_base = eval_ctx.frame_base;
        let result = compiled_expr.expr.eval_with_ctx(eval_ctx);
        match result {
            Ok(value) => {
                println!(
                    "{value}: {}",
                    compiled_expr.ty.display_rust_style(&module_env)
                );
                Ok(true)
            }
            Err(error) => {
                if is_repl {
                    // Restore the context as before starting the evaluation
                    eval_ctx.environment.truncate(old_size);
                    eval_ctx.frame_base = old_frame_base;
                    println!("Runtime error: {error}");
                    Ok(false)
                } else {
                    eprintln!("Runtime error: {error}");
                    Err(1)
                }
            }
        }
    } else {
        // No expression, just module definitions - that's successful
        if !is_repl {
            // In pipe mode, if there's no expression to evaluate, that's fine
            Ok(true)
        } else {
            println!("No expression to evaluate.");
            Ok(true)
        }
    }
}

fn process_pipe_input() -> i32 {
    // Read all input from stdin
    let mut input = String::new();
    if let Err(e) = io::stdin().read_to_string(&mut input) {
        eprintln!("Error reading from stdin: {e}");
        return 1;
    }

    if input.trim().is_empty() {
        eprintln!("No input provided");
        return 1;
    }

    // Initialize ferlium contexts
    let other_modules = new_std_modules();
    let mut module = new_module_using_std();
    let mut locals: Vec<Local> = vec![];
    let mut eval_ctx = EvalCtx::new();

    // Process the input
    match process_input(
        &input,
        &mut module,
        &other_modules,
        &mut locals,
        &mut eval_ctx,
        false,
    ) {
        Ok(_) => 0, // Success (either expression evaluated or just module definitions)
        Err(exit_code) => exit_code,
    }
}

fn main() {
    // Check if we're being used in pipe mode (stdin is not a terminal)
    if !io::stdin().is_terminal() {
        // Pipe mode: read from stdin, process, and exit
        std::process::exit(process_pipe_input());
    }

    // Check for help flag
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 && (args[1] == "--help" || args[1] == "-h") {
        println!("Ferlium REPL - A functional programming language interpreter");
        println!();
        println!("Usage:");
        println!("  {} [--help|-h]", args[0]);
        println!("  echo 'code' | {}", args[0]);
        println!();
        println!("Modes:");
        println!("  Interactive: Run without arguments to start the REPL");
        println!("  Pipe: Pipe ferlium code to stdin for batch processing");
        println!();
        println!("Examples:");
        println!("  {}                     # Start interactive REPL", args[0]);
        println!(
            "  echo '1 + 2' | {}      # Evaluate expression from pipe",
            args[0]
        );
        return;
    }

    // Interactive REPL mode
    run_interactive_repl();
}

fn run_interactive_repl() {
    // Logging
    env_logger::init();

    // ferlium emission and evaluation contexts
    let other_modules = new_std_modules();
    let mut module = new_module_using_std();
    let mut locals: Vec<Local> = vec![];
    let mut eval_ctx = EvalCtx::new();

    // REPL loop
    let mut rl = DefaultEditor::new().unwrap();
    rl.set_max_history_size(256).unwrap();
    let history_filename = "ferlium_history.txt";
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
            let env = ModuleEnv::new(&module, &other_modules);
            for (i, local) in locals.iter().enumerate() {
                println!(
                    "{} {}: {} = {}",
                    local
                        .mutable
                        .as_resolved()
                        .expect("unresolved mutability in local")
                        .var_def_string(),
                    local.name,
                    local.ty.format_with(&env),
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
                if line.is_empty() {
                    continue;
                }
                if let Some(command) = line.strip_prefix('\\') {
                    // a meta command
                    let args: Vec<_> = command.split(" ").collect();
                    let store = match args[0] {
                        "help" => {
                            print_help();
                            true
                        }
                        "module" => {
                            let module = if let Some(arg) = args.get(1) {
                                if let Some(module) = other_modules.get(&ustr(arg)) {
                                    module.deref()
                                } else {
                                    println!("Module {arg} not found.");
                                    continue;
                                }
                            } else {
                                &module
                            };
                            println!("\n{}", FormatWith::new(module, &other_modules));
                            true
                        }
                        _ => {
                            println!("Unknown command \"{command}\". Type \\help for help.");
                            false
                        }
                    };
                    if store {
                        rl.add_history_entry(line.as_str()).unwrap();
                    }
                    continue;
                }
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
                println!("Readline Error: {err:?}");
                return;
            }
        };

        // Process the input using the shared function
        match process_input(
            &src,
            &mut module,
            &other_modules,
            &mut locals,
            &mut eval_ctx,
            true,
        ) {
            Ok(_) => {}  // Success, continue the REPL
            Err(_) => {} // Error handled by process_input, continue the REPL
        }

        if let Err(e) = rl.save_history(history_filename) {
            println!("Failed to save history: {e:?}");
        }
    }
}
