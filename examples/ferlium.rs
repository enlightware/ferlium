// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::collections::HashMap;
use std::env;
use std::io::{self, IsTerminal, Read};
use std::ops::Deref;
use std::rc::Rc;

use ariadne::Label;
use ferlium::error::{CompilationError, CompilationErrorImpl, LocatedError, MutabilityMustBeWhat};
use ferlium::format::FormatWith;
use ferlium::module::{Module, ModuleEnv, ModuleRc, Modules, ShowModuleDetails, Use, UseSome};
use ferlium::std::{new_module_using_std, new_std_modules};
use ferlium::typing_env::Local;
use ferlium::{Location, ModuleAndExpr, SubOrSameType, ast, compile_to};
use rustyline::DefaultEditor;
use rustyline::{config::Configurer, error::ReadlineError};
use ustr::{Ustr, ustr};

use ferlium::eval::{EvalCtx, ValOrMut};

fn span_range(span: Location) -> std::ops::Range<usize> {
    span.start()..span.end()
}

fn span_union_range(span1: Location, span2: Location) -> std::ops::Range<usize> {
    assert_eq!(span1.module(), span2.module());
    span1.start().min(span2.start())..span1.end().max(span2.end())
}

fn pretty_print_parse_errors(src: &str, errors: &[LocatedError]) {
    use ariadne::{Color, Report, ReportKind, Source};
    for (text, span) in errors {
        Report::build(ReportKind::Error, ("input", span_range(*span)))
            .with_message(format!("Parse error: {text}.",))
            .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
            .finish()
            .eprint(("input", Source::from(src)))
            .unwrap();
    }
}

fn pretty_print_checking_error(error: &CompilationError, src: &str) {
    use CompilationErrorImpl::*;
    use ariadne::{Color, Fmt, Report, ReportKind, Source};
    match error.deref() {
        ParsingFailed(errors) => {
            pretty_print_parse_errors(src, errors);
        }
        TypeNotFound(span) => {
            let name = &src[span_range(*span)];
            Report::build(ReportKind::Error, ("input", span_range(*span)))
                .with_message(format!(
                    "Cannot find type `{}` in this scope.",
                    name.fg(Color::Blue)
                ))
                .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
                .finish()
                .eprint(("input", Source::from(src)))
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
                .eprint(("input", Source::from(src)))
                .unwrap();
        }
        MutabilityMustBe {
            source_span,
            reason_span,
            what,
            ..
        } => {
            let source_span = *source_span;
            let reason_span = *reason_span;
            let span = span_union_range(source_span, reason_span);
            let source = &src[span_range(source_span)];
            let reason = &src[span_range(reason_span)];
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
                    .eprint(("input", Source::from(src)))
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
                    .eprint(("input", Source::from(src)))
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
                    .eprint(("input", Source::from(src)))
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
                    current_ty.fg(Color::Magenta),
                    expected_ty.fg(Color::Blue),
                    extra_reason
                ))
                .with_label(
                    Label::new(("input", span_range(*current_span))).with_color(Color::Magenta),
                )
                .with_label(
                    Label::new(("input", span_range(*expected_span))).with_color(Color::Blue),
                )
                .finish()
                .eprint(("input", Source::from(src)))
                .unwrap();
        }
        UnboundTypeVar { ty_var, ty, span } => {
            Report::build(ReportKind::Error, ("input", span_range(*span)))
                .with_message(format!(
                    "Unbound type variable {} in type {}.",
                    ty_var.fg(Color::Blue),
                    ty.fg(Color::Blue)
                ))
                .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
                .finish()
                .eprint(("input", Source::from(src)))
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
                .eprint(("input", Source::from(src)))
                .unwrap();
        }
        InvalidTupleProjection {
            expr_ty,
            expr_span,
            index_span,
        } => {
            let span = span_union_range(*expr_span, *index_span);
            let colored_ty = expr_ty.fg(Color::Blue);
            Report::build(ReportKind::Error, ("input", span))
                .with_message(format!("Type {colored_ty} cannot be projected as a tuple."))
                .with_label(
                    Label::new(("input", span_range(*expr_span)))
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
                .eprint(("input", Source::from(src)))
                .unwrap();
        }
        DuplicatedField {
            first_occurrence,
            second_occurrence,
            ctx,
            ..
        } => {
            let span = span_union_range(*first_occurrence, *second_occurrence);
            let name = &src[span_range(*first_occurrence)];
            Report::build(ReportKind::Error, ("input", span))
                .with_message(format!(
                    "Duplicated field \"{}\" in {}.",
                    name.fg(Color::Blue),
                    ctx.as_str(),
                ))
                .with_label(
                    Label::new(("input", span_range(*first_occurrence))).with_color(Color::Blue),
                )
                .with_label(
                    Label::new(("input", span_range(*second_occurrence))).with_color(Color::Blue),
                )
                .finish()
                .eprint(("input", Source::from(src)))
                .unwrap();
        }
        InvalidVariantConstructor { span } => {
            let name = &src[span_range(*span)];
            Report::build(ReportKind::Error, ("input", span_range(*span)))
                .with_message(format!(
                    "Variant constructor cannot be a path, but {} is.",
                    name.fg(Color::Blue)
                ))
                .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
                .finish()
                .eprint(("input", Source::from(src)))
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
                .eprint(("input", Source::from(src)))
                .unwrap();
        }
        MutablePathsOverlap {
            a_span,
            b_span,
            fn_span,
        } => {
            let span = span_union_range(*a_span, *b_span);
            let a_name = &src[span_range(*a_span)];
            let b_name = &src[span_range(*b_span)];
            let fn_name = &src[span_range(*fn_span)];
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
                .eprint(("input", Source::from(src)))
                .unwrap();
        }
        UndefinedVarInStringFormatting {
            var_span,
            string_span,
        } => {
            let span = span_union_range(*var_span, *string_span);
            let var_name = &src[span_range(*var_span)];
            let string = &src[span_range(*string_span)];
            Report::build(ReportKind::Error, ("input", span))
                .with_message(format!(
                    "Undefined variable {} used in string formatting {}.",
                    var_name.fg(Color::Blue),
                    string.fg(Color::Blue)
                ))
                .with_label(Label::new(("input", span_range(*var_span))).with_color(Color::Blue))
                .with_label(Label::new(("input", span_range(*string_span))))
                .finish()
                .eprint(("input", Source::from(src)))
                .unwrap();
        }
        Unsupported { span, reason } => {
            Report::build(ReportKind::Error, ("input", span_range(*span)))
                .with_message(format!("Unsupported feature: {reason}."))
                .with_label(Label::new(("input", span_range(*span))).with_color(Color::Blue))
                .finish()
                .eprint(("input", Source::from(src)))
                .unwrap();
        }
        _ => eprintln!("Module emission error: {}", error.format_with(&src)),
    }
}

fn print_help() {
    println!("Available commands:");
    println!("\\help: Show this help message.");
    println!(
        "\\module MOD_NAME?: Show a module by name, or the current module if no name is given."
    );
    println!(
        "\\function FN_NAME_OR_INDEX MOD_NAME?: Shows the code of a function given by its name or index, in a given module."
    );
    println!("\\history: Show the modules in this session's history.");
    println!("CTRL-D: Exit the REPL.");
}

/// Process a single input: parse, compile module, and evaluate expression if present.
/// Returns Ok(true) if successful, Ok(false) if there was an error but we should continue,
/// and Err(exit_code) if we should exit with the given code.
fn process_input(
    input: &str,
    reverse_uses: HashMap<Ustr, Ustr>,
    other_modules: &Modules,
    locals: &mut Vec<Local>,
    environment: &mut Vec<ValOrMut>,
    is_repl: bool,
) -> Result<ModuleRc, i32> {
    // Initialize module with use directives
    let mut module = new_module_using_std();
    for (sym_name, mod_name) in reverse_uses {
        module
            .uses
            .push(Use::Some(UseSome::new(mod_name, vec![sym_name])));
    }

    // AST debug output for REPL
    let dbg_module = module.clone();
    let ast_inspector = |module_ast: &ast::PModule, expr_ast: &Option<ast::PExpr>| {
        if !is_repl {
            return;
        }
        let module_env = ModuleEnv::new(&dbg_module, other_modules, false);
        if !module_ast.is_empty() {
            println!("Module AST:\n{}", module_ast.format_with(&module_env));
        }
        if let Some(expr_ast) = expr_ast.as_ref() {
            println!("Expr AST:\n{}", expr_ast.format_with(&module_env));
        }
    };

    // Compile the input to a module and an expression (if any)
    let ModuleAndExpr { module, expr } =
        compile_to(input, module, other_modules, Some(&ast_inspector)).map_err(|e| {
            eprintln!("Compilation error:");
            pretty_print_checking_error(&e, input);
            1
        })?;

    // Show IR
    if is_repl {
        let module: &Module = &module;
        println!(
            "Module IR:\n{}",
            module.format_with(&ShowModuleDetails(other_modules))
        );
        if let Some(expr) = expr.as_ref() {
            let module_env = ModuleEnv::new(&module, other_modules, false);
            println!("Expr IR:\n{}", expr.expr.format_with(&module_env));
        }
    }

    // If there's an expression, evaluate it
    if let Some(compiled_expr) = expr {
        *locals = compiled_expr.locals;

        // Evaluate expression
        let mut eval_ctx = EvalCtx::with_environment(module.clone(), environment.clone());
        let old_size = eval_ctx.environment.len();
        let result = compiled_expr.expr.eval_with_ctx(&mut eval_ctx);
        match result {
            Ok(value) => {
                let value = value.into_value();
                let module_env = ModuleEnv::new(&module, other_modules, false);
                println!(
                    "{}: {}",
                    value.display_pretty(&compiled_expr.ty.ty),
                    compiled_expr.ty.display_rust_style(&module_env)
                );
            }
            Err(error) => {
                eprintln!("Runtime error: {error}");
                if cfg!(debug_assertions) {
                    eval_ctx.print_environment();
                }
                if is_repl {
                    // Restore the context as before starting the evaluation
                    eval_ctx.environment.truncate(old_size);
                    *environment = eval_ctx.environment;
                }
                return Err(2);
            }
        }
    } else {
        // No expression, just module definitions - that's successful
        if !is_repl {
            println!("No expression to evaluate.");
        }
    }

    Ok(module)
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
    let mut locals: Vec<Local> = vec![];
    let mut environment: Vec<ValOrMut> = vec![];

    // Process the input
    process_input(
        &input,
        HashMap::new(),
        &other_modules,
        &mut locals,
        &mut environment,
        false,
    )
    .map_or_else(|code| code, |_| 0)
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
    let mut other_modules = new_std_modules();
    let mut last_module = Rc::new(new_module_using_std());
    let mut locals: Vec<Local> = vec![];
    let mut environment: Vec<ValOrMut> = vec![];
    let mut counter: usize = 0;

    // REPL loop
    println!("Ferlium REPL - Type \\help for help.");
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
            let env = ModuleEnv::new(&last_module, &other_modules, false);
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
                    environment[i]
                        .as_val()
                        .expect("reference found in REPL locals")
                        .to_string_repr(),
                );
            }
        }

        // Read input
        let readline = rl.readline(&format!("repl{counter} >> "));
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
                                &last_module
                            };
                            println!("\n{}", module.format_with(&other_modules));
                            true
                        }
                        "function" => {
                            let (module, module_name): (&Module, &str) =
                                if let Some(arg) = args.get(2) {
                                    let name = *arg;
                                    if let Some(module) = other_modules.get(&ustr(arg)) {
                                        (&module, name)
                                    } else {
                                        println!("Module {arg} not found.");
                                        continue;
                                    }
                                } else {
                                    (&last_module, "current")
                                };
                            let index = if let Some(arg) = args.get(1) {
                                match arg.parse::<usize>() {
                                    Ok(id) => id,
                                    Err(_) => {
                                        // not a number, attempt to find by name
                                        match module.function_name_to_id.get(&ustr(arg)) {
                                            Some(id) => id.as_index(),
                                            None => {
                                                println!(
                                                    "Function name {arg} not found in module {module_name}."
                                                );
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                println!("Function id is required.");
                                continue;
                            };
                            let local_fn = if let Some(local_fn) = module.functions.get(index) {
                                local_fn
                            } else {
                                println!("Function id {index} not found in module {module_name}.");
                                continue;
                            };
                            let env = ModuleEnv::new(&module, &other_modules, false);
                            println!("{}", (&local_fn.function, local_fn.name).format_with(&env));
                            true
                        }
                        "history" => {
                            for i in 0..counter {
                                let name = ustr(&format!("repl{i}"));
                                if let Some(module) = other_modules.get(&name) {
                                    println!("{}: {}", name, module.list_stats());
                                }
                            }
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

        // Build use directives to import last modules as repl<counter>
        let mut reverse_uses = HashMap::new();
        for i in 0..counter {
            let index = counter - i - 1;
            let mod_name = ustr(&format!("repl{index}"));
            let module = other_modules
                .get(&mod_name)
                .expect("missing repl<counter> module");
            for sym in module.own_symbols() {
                if !reverse_uses.contains_key(&sym) {
                    reverse_uses.insert(sym, mod_name);
                }
            }
        }

        // Process the input using the shared function
        let result = process_input(
            &src,
            reverse_uses,
            &other_modules,
            &mut locals,
            &mut environment,
            true,
        );
        if let Ok(module) = result {
            last_module = module;
            let name = ustr(&format!("repl{counter}"));
            other_modules.register_module_rc(name, last_module.clone());
            counter += 1;
        }

        if let Err(e) = rl.save_history(history_filename) {
            println!("Failed to save history: {e:?}");
        }
    }
}
