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

use ariadne::{Label, Source};
use ferlium::error::{CompilationError, CompilationErrorImpl, LocatedError, MutabilityMustBeWhat};
use ferlium::format::FormatWith;
use ferlium::module::{
    Module, ModuleEnv, ModuleRc, Modules, Path, ShowModuleDetails, Use, UseSome,
};
use ferlium::std::new_module_using_std;
use ferlium::typing_env::Local;
use ferlium::{
    CompilerSession, Location, ModuleAndExpr, SourceId, SourceTable, SubOrSameType, ast,
};
use rustyline::DefaultEditor;
use rustyline::{config::Configurer, error::ReadlineError};
use ustr::{Ustr, ustr};

use ferlium::eval::{EvalCtx, ValOrMut};

/// A wrapper around location to implement ariadne::Span
#[derive(Debug, Clone, Copy)]
struct Span(Location);
impl ariadne::Span for Span {
    type SourceId = SourceId;

    fn source(&self) -> &Self::SourceId {
        &self.0.source_id_ref()
    }

    fn start(&self) -> usize {
        self.0.start_usize()
    }

    fn end(&self) -> usize {
        self.0.end_usize()
    }
}

/// A wrapper around SourceTable to implement ariadne::Cache
struct Cache<'src> {
    cache: HashMap<SourceId, Source<&'src String>>,
    source_table: &'src SourceTable,
}
impl Cache<'_> {
    pub fn new(source_table: &SourceTable) -> Cache<'_> {
        Cache {
            cache: HashMap::new(),
            source_table,
        }
    }
}
impl<'src> ariadne::Cache<SourceId> for Cache<'src> {
    type Storage = &'src String;

    fn fetch(&mut self, id: &SourceId) -> Result<&Source<Self::Storage>, impl std::fmt::Debug> {
        let entry = self.cache.entry(*id).or_insert_with(|| {
            let source = self
                .source_table
                .get_source_text(*id)
                .expect("Source not found in source table for ariadne cache");
            Source::from(source)
        });
        Ok::<&Source<Self::Storage>, std::convert::Infallible>(entry)
    }

    fn display<'id>(&self, id: &'id SourceId) -> Option<impl std::fmt::Display + 'id> {
        self.source_table.get_source_name(*id).cloned()
    }
}

fn span_union_range(span1: Location, span2: Location) -> Span {
    assert_eq!(span1.source_id(), span2.source_id());
    Span(Location::new(
        span1.start().min(span2.start()),
        span1.end().max(span2.end()),
        span1.source_id(),
    ))
}

fn pretty_print_parse_errors(errors: &[LocatedError], source_table: &SourceTable) {
    use ariadne::{Color, Report, ReportKind};
    let mut cache = Cache::new(source_table);
    for (text, span) in errors {
        let span = Span(*span);
        Report::build(ReportKind::Error, span)
            .with_message(format!("Parse error: {text}.",))
            .with_label(Label::new(span).with_color(Color::Blue))
            .finish()
            .eprint(&mut cache)
            .unwrap();
    }
}

fn pretty_print_checking_error(error: &CompilationError, src: &str, source_table: &SourceTable) {
    use CompilationErrorImpl::*;
    use ariadne::{Color, Fmt, Report, ReportKind};
    let mut cache = Cache::new(source_table);
    match error.deref() {
        ParsingFailed(errors) => {
            pretty_print_parse_errors(errors, source_table);
        }
        TypeNotFound(span) => {
            let name = &src[span.as_range()];
            let span = Span(*span);
            Report::build(ReportKind::Error, span)
                .with_message(format!(
                    "Cannot find type `{}` in this scope.",
                    name.fg(Color::Blue)
                ))
                .with_label(Label::new(span).with_color(Color::Blue))
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        WrongNumberOfArguments {
            expected,
            expected_span,
            got,
            got_span,
        } => {
            let expected_span = Span(*expected_span);
            let got_span = Span(*got_span);
            Report::build(ReportKind::Error, expected_span)
                .with_message(format!(
                    "Wrong number of arguments: expected {} but found {}.",
                    expected.fg(Color::Blue),
                    got.fg(Color::Magenta)
                ))
                .with_label(Label::new(expected_span).with_color(Color::Blue))
                .with_label(Label::new(got_span).with_color(Color::Magenta))
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        MutabilityMustBe {
            source_span,
            reason_span,
            what,
            ..
        } => {
            let source = &src[source_span.as_range()];
            let reason = &src[reason_span.as_range()];
            let span = span_union_range(*source_span, *reason_span);
            let source_span = Span(*source_span);
            let reason_span = Span(*reason_span);
            use MutabilityMustBeWhat::*;
            match what {
                Mutable => Report::build(ReportKind::Error, span)
                    .with_message(format!(
                        "Expression {} must be mutable.",
                        source.fg(Color::Blue),
                    ))
                    .with_label(
                        Label::new(source_span)
                            .with_message("This expression is just a value.")
                            .with_color(Color::Blue),
                    )
                    .with_label(
                        Label::new(reason_span)
                            .with_message("But it must be mutable due to this.")
                            .with_color(Color::Green)
                            .with_order(1),
                    )
                    .finish()
                    .eprint(&mut cache)
                    .unwrap(),
                Constant => Report::build(ReportKind::Error, span)
                    .with_message(format!(
                        "Expression {} must be constant.",
                        source.fg(Color::Blue),
                    ))
                    .with_label(
                        Label::new(source_span)
                            .with_message("This expression is mutable.")
                            .with_color(Color::Blue),
                    )
                    .with_label(
                        Label::new(reason_span)
                            .with_message("But it must be constant due to this.")
                            .with_color(Color::Green)
                            .with_order(1),
                    )
                    .finish()
                    .eprint(&mut cache)
                    .unwrap(),
                Equal => Report::build(ReportKind::Error, span)
                    .with_message(format!(
                        "Expressions {} and {} must have the same mutability.",
                        source.fg(Color::Blue),
                        reason.fg(Color::Green),
                    ))
                    .with_label(
                        Label::new(source_span)
                            .with_message("There.")
                            .with_color(Color::Blue),
                    )
                    .with_label(
                        Label::new(reason_span)
                            .with_message("And here.")
                            .with_color(Color::Green)
                            .with_order(1),
                    )
                    .finish()
                    .eprint(&mut cache)
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
            let current_span = Span(*current_span);
            let expected_span = Span(*expected_span);
            use SubOrSameType::*;
            let extra_reason = match sub_or_same {
                SubType => "not a subtype",
                SameType => "not the same type",
            };
            Report::build(ReportKind::Error, span)
                .with_message(format!(
                    "Type {} is incompatible with type {} (i.e. {}).",
                    current_ty.fg(Color::Magenta),
                    expected_ty.fg(Color::Blue),
                    extra_reason
                ))
                .with_label(Label::new(current_span).with_color(Color::Magenta))
                .with_label(Label::new(expected_span).with_color(Color::Blue))
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        UnboundTypeVar { ty_var, ty, span } => {
            let span = Span(*span);
            Report::build(ReportKind::Error, span)
                .with_message(format!(
                    "Unbound type variable {} in type {}.",
                    ty_var.fg(Color::Blue),
                    ty.fg(Color::Blue)
                ))
                .with_label(Label::new(span).with_color(Color::Blue))
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        InvalidTupleIndex {
            index,
            index_span,
            tuple_length,
            tuple_span,
        } => {
            let span = span_union_range(*index_span, *tuple_span);
            let index_span = Span(*index_span);
            let tuple_span = Span(*tuple_span);
            let colored_index = (*index).fg(Color::Blue);
            Report::build(ReportKind::Error, span)
                .with_message(format!("Tuple index {colored_index} is out of bounds."))
                .with_label(
                    Label::new(index_span)
                        .with_message(format!("Index is {colored_index}."))
                        .with_color(Color::Blue),
                )
                .with_label(
                    Label::new(tuple_span)
                        .with_message(format!(
                            "But tuple has only {} elements.",
                            (*tuple_length).fg(Color::Blue)
                        ))
                        .with_color(Color::Green)
                        .with_order(1),
                )
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        InvalidTupleProjection {
            expr_ty,
            expr_span,
            index_span,
        } => {
            let span = span_union_range(*expr_span, *index_span);
            let expr_span = Span(*expr_span);
            let index_span = Span(*index_span);
            let colored_ty = expr_ty.fg(Color::Blue);
            Report::build(ReportKind::Error, span)
                .with_message(format!("Type {colored_ty} cannot be projected as a tuple."))
                .with_label(
                    Label::new(expr_span)
                        .with_message(format!("This expression has type {colored_ty}."))
                        .with_color(Color::Blue),
                )
                .with_label(
                    Label::new(index_span)
                        .with_message(format!(
                            "But a tuple is needed due to projection {}.",
                            "here".fg(Color::Green)
                        ))
                        .with_color(Color::Green)
                        .with_order(1),
                )
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        DuplicatedField {
            first_occurrence,
            second_occurrence,
            ctx,
            ..
        } => {
            let name = &src[first_occurrence.as_range()];
            let span = span_union_range(*first_occurrence, *second_occurrence);
            let first_occurrence = Span(*first_occurrence);
            let second_occurrence = Span(*second_occurrence);
            Report::build(ReportKind::Error, span)
                .with_message(format!(
                    "Duplicated field \"{}\" in {}.",
                    name.fg(Color::Blue),
                    ctx.as_str(),
                ))
                .with_label(Label::new(first_occurrence).with_color(Color::Blue))
                .with_label(Label::new(second_occurrence).with_color(Color::Blue))
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        InvalidVariantConstructor { span } => {
            let name = &src[span.as_range()];
            let span = Span(*span);
            Report::build(ReportKind::Error, span)
                .with_message(format!(
                    "Variant constructor cannot be a path, but {} is.",
                    name.fg(Color::Blue)
                ))
                .with_label(Label::new(span).with_color(Color::Blue))
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        InconsistentADT {
            a_type,
            a_span,
            b_type,
            b_span,
        } => {
            let span = span_union_range(*a_span, *b_span);
            let a_span = Span(*a_span);
            let b_span = Span(*b_span);
            let a_ty = a_type.adt_kind().fg(Color::Blue);
            let b_ty = b_type.adt_kind().fg(Color::Magenta);
            Report::build(ReportKind::Error, span)
                .with_message(format!(
                    "Data type {a_ty} is different than data type {b_ty}."
                ))
                .with_label(
                    Label::new(a_span)
                        .with_message(format!("type is {a_ty} here"))
                        .with_color(Color::Blue),
                )
                .with_label(
                    Label::new(b_span)
                        .with_message(format!("but type is {b_ty} here"))
                        .with_color(Color::Magenta),
                )
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        MutablePathsOverlap {
            a_span,
            b_span,
            fn_span,
        } => {
            let a_name = &src[a_span.as_range()];
            let b_name = &src[b_span.as_range()];
            let fn_name = &src[fn_span.as_range()];
            let span = span_union_range(*a_span, *b_span);
            let a_span = Span(*a_span);
            let b_span = Span(*b_span);
            let fn_span = Span(*fn_span);
            Report::build(ReportKind::Error, span)
                .with_message(format!(
                    "Mutable paths {} and {} overlap when calling {}.",
                    a_name.fg(Color::Blue),
                    b_name.fg(Color::Blue),
                    fn_name.fg(Color::Green)
                ))
                .with_label(Label::new(a_span).with_color(Color::Blue))
                .with_label(Label::new(b_span).with_color(Color::Blue))
                .with_label(Label::new(fn_span).with_color(Color::Green))
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        UndefinedVarInStringFormatting {
            var_span,
            string_span,
        } => {
            let var_name = &src[var_span.as_range()];
            let string = &src[string_span.as_range()];
            let span = span_union_range(*var_span, *string_span);
            let var_span = Span(*var_span);
            let string_span = Span(*string_span);
            Report::build(ReportKind::Error, span)
                .with_message(format!(
                    "Undefined variable {} used in string formatting {}.",
                    var_name.fg(Color::Blue),
                    string.fg(Color::Blue)
                ))
                .with_label(Label::new(var_span).with_color(Color::Blue))
                .with_label(Label::new(string_span))
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        Unsupported { span, reason } => {
            let span = Span(*span);
            Report::build(ReportKind::Error, span)
                .with_message(format!("Unsupported feature: {reason}."))
                .with_label(Label::new(span).with_color(Color::Blue))
                .finish()
                .eprint(&mut cache)
                .unwrap();
        }
        _ => eprintln!("Module emission error: {}", error.format_with(source_table)),
    }
}

fn print_help() {
    println!("Available commands:");
    println!("\\help: Shows this help message.");
    println!(
        "\\module MOD_NAME?: Shows a module by name, or the current module if no name is given."
    );
    println!(
        "\\function FN_NAME_OR_INDEX MOD_NAME?: Shows the code of a function given by its name or index, in a given module."
    );
    println!("\\history: Shows the modules in this session's history.");
    println!("CTRL-D: Exits the REPL.");
}

/// Process a single input: parse, compile module, and evaluate expression if present.
/// Returns Ok(module) if successful and Err(exit_code) if there was a failure.
fn process_input(
    name: &str,
    input: &str,
    reverse_uses: HashMap<Ustr, Path>,
    other_modules: &Modules,
    locals: &mut Vec<Local>,
    environment: &mut Vec<ValOrMut>,
    session: &mut CompilerSession,
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
    let ModuleAndExpr { module, expr } = session
        .compile_to(name, input, module, other_modules, Some(&ast_inspector))
        .map_err(|e| {
            eprintln!("Compilation error:");
            pretty_print_checking_error(&e, input, session.source_table());
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
                let mut modules = other_modules.clone();
                modules.register_module_rc(Path::single_str(name), module.clone());
                eprintln!("{}", error.format_with(&(session.source_table(), &modules)));
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

fn process_pipe_input(print_module: bool) -> i32 {
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
    let mut session = CompilerSession::new();
    let other_modules = session.new_std_modules();
    let mut locals: Vec<Local> = vec![];
    let mut environment: Vec<ValOrMut> = vec![];

    // Process the input
    process_input(
        "<stdin>",
        &input,
        HashMap::new(),
        &other_modules,
        &mut locals,
        &mut environment,
        &mut session,
        false,
    )
    .map_or_else(
        |code| code,
        |module| {
            if print_module {
                println!("{}", module.format_with(&other_modules));
            }
            0
        },
    )
}

fn main() {
    // Check if we're being used in pipe mode (stdin is not a terminal)
    if !io::stdin().is_terminal() {
        // Pipe mode: read from stdin, process, and exit
        let print_module = env::args().any(|arg| arg == "--print-module");
        std::process::exit(process_pipe_input(print_module));
    }

    // Check for help flag
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 && (args[1] == "--help" || args[1] == "-h") {
        println!("Ferlium REPL - A functional programming language interpreter");
        println!();
        println!("Usage:");
        println!("  {} [--help|-h]      Show the help.", args[0]);
        println!(
            "  {} [--print-std]    Print the standard library module (interactive mode only).",
            args[0]
        );
        println!(
            "  {} [--print-module] Print the provided-code module (pipe mode only).",
            args[0]
        );
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

    // Check for print-std flag
    if args.len() > 1 && args[1] == "--print-std" {
        let session = CompilerSession::new();
        if let Some(module) = session.std_modules().get(&Path::single_str("std")) {
            println!("{}", module.format_with(session.std_modules()));
        } else {
            eprintln!("Module std not found.");
        }
        return;
    }

    // Interactive REPL mode
    run_interactive_repl();
}

fn run_interactive_repl() {
    // Logging
    env_logger::init();

    // ferlium emission and evaluation contexts
    let mut session = CompilerSession::new();
    let mut other_modules = session.new_std_modules();
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
                                if let Some(module) = other_modules.get(&Path::single_str(arg)) {
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
                            let (module, module_name): (&Module, &str) = if let Some(arg) =
                                args.get(2)
                            {
                                let name = *arg;
                                if let Some(module) = other_modules.get(&Path::single_str(arg)) {
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
                                        match module.get_unique_local_function_id(ustr(arg)) {
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
                                let name = format!("repl{i}");
                                if let Some(module) = other_modules.get(&Path::single_str(&name)) {
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
            let mod_name = format!("repl{index}");
            if let Some(module) = other_modules.get(&Path::single_str(&mod_name)) {
                for sym in module.own_symbols() {
                    if !reverse_uses.contains_key(&sym) {
                        reverse_uses.insert(sym, Path::single_str(&mod_name));
                    }
                }
            }
        }

        // Process the input using the shared function
        let name = &format!("repl{counter}");
        let result = process_input(
            &name,
            &src,
            reverse_uses,
            &other_modules,
            &mut locals,
            &mut environment,
            &mut session,
            true,
        );
        if let Ok(module) = result {
            last_module = module;
            other_modules.register_module_rc(Path::single_str(name), last_module.clone());
        }
        counter += 1;
        if let Err(e) = rl.save_history(history_filename) {
            println!("Failed to save history: {e:?}");
        }
    }
}
