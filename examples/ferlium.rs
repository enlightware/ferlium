// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ferlium::hir;
use ferlium::{FxHashMap, FxHashSet};
use std::env;
use std::io::{self, IsTerminal, Read};
use std::ops::Deref;

use ariadne::{Label, Source};
use ferlium::ast;
use ferlium::compiler::error::{
    CompilationError, CompilationErrorImpl, LocatedError, MutabilityMustBeWhat,
};
use ferlium::format::FormatWith;
use ferlium::hir::function::UnaryNativeFnRN;
use ferlium::ide::{AnnotationData, Compiler as IdeCompiler};
use ferlium::module::id::Id;
use ferlium::module::{
    LocalFunctionId, Module, ModuleId, Path, ShowModuleWithOptions, UseData, Uses,
};
use ferlium::std::new_module_using_std;
use ferlium::std::string::String as FerliumString;
use ferlium::types::effects::{PrimitiveEffect, effect};
use ferlium::{
    CompilerSession, Location, ModuleAndExpr, SourceId, SourceTable, SubOrSameType,
    parse_module_and_expr,
};
use rustyline::DefaultEditor;
use rustyline::{config::Configurer, error::ReadlineError};
use ustr::ustr;

use ferlium::eval::{DEFAULT_INTERACTIVE_FUEL_LIMIT, EvalCtx, eval_node_with_ctx};

/// A wrapper around location to implement ariadne::Span
#[derive(Debug, Clone, Copy)]
struct Span(Location);
impl ariadne::Span for Span {
    type SourceId = SourceId;

    fn source(&self) -> &Self::SourceId {
        self.0.source_id_ref()
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
    cache: FxHashMap<SourceId, Source<&'src String>>,
    source_table: &'src SourceTable,
}
impl Cache<'_> {
    pub fn new(source_table: &SourceTable) -> Cache<'_> {
        Cache {
            cache: FxHashMap::default(),
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
                SameTypeWithSubEffects => "not the same type",
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
                    "Invalid variant constructor path {}.",
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
        "\\fuel N|off: Shows or sets the execution fuel limit (default {DEFAULT_INTERACTIVE_FUEL_LIMIT})."
    );
    println!(
        "\\module MOD_NAME?: Shows a module by name, or the current module if no name is given."
    );
    println!(
        "\\function FN_NAME_OR_INDEX MOD_NAME?: Shows the code of a function given by its name or index, in a given module."
    );
    println!("\\function MOD_NAME::FN_NAME: Shows the code of a function using a qualified name.");
    println!("\\history: Shows the modules in this session's history.");
    println!("CTRL-D: Exits the REPL.");
    println!("\nNote: expression locals do not persist across REPL inputs.");
}

fn console_print(message: &FerliumString) {
    println!("{}", message.as_ref());
}

fn console_module(module_id: ModuleId) -> Module {
    let mut module = new_module_using_std(module_id, Path::single_str("$console"));
    module.add_function(
        ustr("print"),
        UnaryNativeFnRN::description_with_default_ty(
            console_print,
            ["message"],
            "Prints `message` to the REPL console.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module
}

fn repl_show_module_options(session: &CompilerSession) -> ShowModuleWithOptions<'_> {
    ShowModuleWithOptions {
        modules: session.modules(),
        show_details: false,
        show_all_functions: true,
        show_private_items: true,
    }
}

fn parse_repl_module_path(name: &str) -> Path {
    Path::new(name.split("::").map(ustr).collect())
}

fn split_qualified_function_name(name: &str) -> Option<(Path, &str)> {
    let (module, function) = name.rsplit_once("::")?;
    (!module.is_empty() && !function.is_empty()).then(|| (parse_repl_module_path(module), function))
}

/// Process a single input: parse, compile module, and evaluate expression if present.
/// Returns Ok(module) if successful and Err(exit_code) if there was a failure.
fn process_input(
    name: &str,
    input: &str,
    fill_use_until: usize,
    session: &mut CompilerSession,
    is_repl: bool,
    fuel_limit: Option<usize>,
) -> Result<ModuleId, i32> {
    // Parse the input once to get the list of symbols this module defines.
    let source_id = session.source_table().next_id();
    let parsed = parse_module_and_expr(input, source_id, false);
    let local_symbols = parsed.as_ref().map_or_else(
        |_| FxHashSet::default(),
        |(module, _, _)| module.own_symbols().map(|(sym, _)| sym).collect(),
    );

    // Build use directives to import last modules as repl<counter>
    let mut reverse_uses = FxHashMap::default();
    for i in 0..fill_use_until {
        let index = fill_use_until - i - 1;
        let mod_name = format!("repl{index}");
        if let Some((_, module)) = session.modules().get_by_path(&Path::single_str(&mod_name)) {
            for sym in module.own_symbols() {
                if !local_symbols.contains(&sym)
                    && !reverse_uses.contains_key(&sym)
                    // exclude lambda functions
                    && !sym.starts_with("$")
                    // exclude trait implementations
                    && !sym.contains("::")
                {
                    reverse_uses.insert(sym, Path::single_str(&mod_name));
                }
            }
        }
    }

    // Initialize module with use directives
    let mut uses = Uses::new_with_std();
    if is_repl {
        uses.wildcards.push(UseData::new(
            Path::single_str("console"),
            Location::new_synthesized(),
        ));
    }
    for (sym, path) in reverse_uses {
        uses.explicits
            .insert(sym, UseData::new(path, Location::new_synthesized()));
    }

    // AST debug output for REPL
    if is_repl {
        if let Ok((module_ast, expr_ast, arena)) = &parsed {
            let dbg_module =
                new_module_using_std(session.modules().next_id(), Path::single_str("$debug"));
            let module_env = session.modules().env_for(&dbg_module);
            if !module_ast.is_empty() {
                println!(
                    "Module AST:\n{}",
                    ast::ModuleDisplay::new(module_ast, arena).format_with(&module_env)
                );
            }
            if let Some(expr_ast) = expr_ast {
                println!(
                    "Expr AST:\n{}",
                    ast::ExprDisplay::new(*expr_ast, arena).format_with(&module_env)
                );
            }
        }
    }

    // Compile the input to a module and an expression (if any)
    let ModuleAndExpr { module_id, expr } = session
        .compile_to(input, name, Path::single_str(name), uses)
        .map_err(|e| {
            eprintln!("Compilation error:");
            pretty_print_checking_error(&e, input, session.source_table());
            1
        })?;

    // Show HIR
    if is_repl {
        let module = session.expect_fresh_module(module_id);
        println!(
            "Module HIR:\n{}",
            module.format_with(&repl_show_module_options(session))
        );
        if let Some(expr) = expr.as_ref() {
            let module_env = session.modules().env_for(module);
            println!(
                "Expr HIR:\n{}",
                hir::ExprDisplay::new(expr.expr, &expr.locals).format_with(&module_env)
            );
        }
    }

    // If there's an expression, evaluate it
    if let Some(expr) = expr {
        // Evaluate expression
        let result = {
            let mut eval_ctx = EvalCtx::new(module_id, session);
            eval_ctx.set_fuel_limit(fuel_limit);
            let arena = &eval_ctx
                .compiler_session()
                .expect_fresh_module(module_id)
                .hir_arena;
            eval_node_with_ctx(arena, expr.expr, &mut eval_ctx, &expr.locals)
        };
        match result {
            Ok(value) => {
                let value = value.into_value();
                let rendered = match session
                    .value_to_inspect_text_with_fuel(module_id, value, expr.ty.ty, fuel_limit)
                {
                    Ok(rendered) => rendered,
                    Err(error) => {
                        eprintln!("Formatting error:\n{error}");
                        return Err(2);
                    }
                };
                let module = session.expect_fresh_module(module_id);
                let module_env = session.modules().env_for(module);
                println!("{}: {}", rendered, expr.ty.display(&module_env));
            }
            Err(error) => {
                eprintln!(
                    "{}",
                    error.format_with(&(session.source_table(), session.modules()))
                );
                return Err(2);
            }
        }
    } else {
        // No expression, just module definitions - that's successful
        if !is_repl {
            println!("No expression to evaluate.");
        }
    }

    let print_ssa: bool = env::args().any(|arg| arg == "--print-ssa");

    if print_ssa {
        let ssa = session.emit_ssa_module(module_id);
        println!("{}", ssa);
    }

    Ok(module_id)
}

fn annotated_source(input: &str, annotations: &[AnnotationData]) -> String {
    let char_to_byte = |char_pos: usize| {
        input
            .char_indices()
            .map(|(index, _)| index)
            .nth(char_pos)
            .unwrap_or(input.len())
    };
    let mut grouped = Vec::<(usize, String)>::new();
    for annotation in annotations {
        if let Some((_, hint)) = grouped.last_mut().filter(|(pos, _)| *pos == annotation.pos) {
            hint.push_str(&annotation.hint);
        } else {
            grouped.push((annotation.pos, annotation.hint.clone()));
        }
    }
    let mut output = input.to_string();
    for (pos, hint) in grouped.into_iter().rev() {
        output.insert_str(char_to_byte(pos), &hint);
    }
    output
}

fn print_pipe_annotations(input: &str, allow_experimental: bool) -> i32 {
    let mut compiler = IdeCompiler::new();
    compiler.set_allow_experimental(allow_experimental);
    if let Some(errors) = compiler.compile(input) {
        for error in errors {
            eprintln!("{error}");
        }
        return 1;
    }
    let annotations = compiler.get_annotations();
    println!("{}", annotated_source(input, &annotations));
    0
}

fn process_pipe_input(
    print_module: bool,
    print_annotations: bool,
    allow_experimental: bool,
) -> i32 {
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

    if print_annotations {
        return print_pipe_annotations(&input, allow_experimental);
    }

    // Initialize ferlium contexts
    let mut session = CompilerSession::new();
    session.set_allow_experimental(allow_experimental);

    // Process the input
    process_input("<stdin>", &input, 0, &mut session, false, None).map_or_else(
        |code| code,
        |module_id| {
            if print_module {
                let module = session.expect_fresh_module(module_id);
                println!("{}", module.format_with(&session.modules()));
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
        let print_annotations = env::args().any(|arg| arg == "--print-annotations");
        let allow_experimental = env::args().any(|arg| arg == "--allow-experimental");
        std::process::exit(process_pipe_input(
            print_module,
            print_annotations,
            allow_experimental,
        ));
    }

    // Check for help flag
    let args: Vec<String> = env::args().collect();
    let allow_experimental = args.iter().any(|arg| arg == "--allow-experimental");
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        println!("Ferlium REPL - A functional programming language interpreter");
        println!();
        println!("Usage:");
        println!("  {} [--help|-h]        Show the help.", args[0]);
        println!("  {} [--print-ssa]      Print the ssa output", args[0]);
        println!(
            "  {} [--print-std]      Print the standard library module (interactive mode only).",
            args[0]
        );
        println!(
            "  {} [--print-std-all]  Print the standard library module with all functions (interactive mode only).",
            args[0]
        );
        println!(
            "  {} [--print-std-full] Print the standard library module with all functions and their HIR (interactive mode only).",
            args[0]
        );
        println!(
            "  {} [--print-module]   Print the provided-code module (pipe mode only).",
            args[0]
        );
        println!(
            "  {} [--print-annotations] Print the IDE-annotated source (pipe mode only).",
            args[0]
        );
        println!(
            "  {} [--allow-experimental] Enable safe experimental language features.",
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

    // Check for print-std flags
    if args.len() > 1 {
        if args.iter().any(|arg| arg == "--print-std") {
            let session = CompilerSession::new();
            println!(
                "{}",
                session
                    .std_module()
                    .format_with(&ShowModuleWithOptions::public(session.modules()))
            );
            return;
        }
        if args.iter().any(|arg| arg == "--print-std-all") {
            let session = CompilerSession::new();
            println!(
                "{}",
                session
                    .std_module()
                    .format_with(&ShowModuleWithOptions::new(session.modules(), false, true))
            );
            return;
        }
        if args.iter().any(|arg| arg == "--print-std-full") {
            let session = CompilerSession::new();
            println!(
                "{}",
                session
                    .std_module()
                    .format_with(&ShowModuleWithOptions::new(session.modules(), true, true))
            );
            return;
        }
    }

    // Interactive REPL mode
    run_interactive_repl(allow_experimental);
}

fn run_interactive_repl(allow_experimental: bool) {
    // Logging
    env_logger::init();

    // ferlium emission and evaluation contexts
    let mut session = CompilerSession::new();
    session.set_allow_experimental(allow_experimental);
    session.register_module(
        Path::single_str("console"),
        console_module(session.modules().next_id()),
    );
    // Last module that compiled successfully, start with the std module.
    let mut last_module = ModuleId::from_index(0);
    let mut counter: usize = 0;
    let mut fuel_limit = Some(DEFAULT_INTERACTIVE_FUEL_LIMIT);

    // REPL loop
    println!("Ferlium REPL - Type \\help for help.");
    let mut rl = DefaultEditor::new().unwrap();
    rl.set_max_history_size(256).unwrap();
    let history_filename = "ferlium_history.txt";
    if rl.load_history(history_filename).is_err() {
        println!("No previous history.");
    }
    loop {
        println!();

        // Read input
        let readline = rl.readline(&format!("repl{counter} >> "));
        let src = match readline {
            Ok(line) => {
                if line.is_empty() {
                    continue;
                }
                if let Some(command) = line.strip_prefix('\\') {
                    // a meta command
                    let args: Vec<_> = command.split_whitespace().collect();
                    if args.is_empty() {
                        println!("Unknown command \"{command}\". Type \\help for help.");
                        continue;
                    }
                    let store = match args[0] {
                        "help" => {
                            print_help();
                            true
                        }
                        "fuel" => match args.get(1).copied() {
                            None => {
                                match fuel_limit {
                                    Some(limit) => println!("Execution fuel limit: {limit}"),
                                    None => println!("Execution fuel limit: off"),
                                }
                                true
                            }
                            Some("off" | "none" | "unlimited") => {
                                fuel_limit = None;
                                println!("Execution fuel limit disabled.");
                                true
                            }
                            Some(value) => match value.parse::<usize>() {
                                Ok(limit) => {
                                    fuel_limit = Some(limit);
                                    println!("Execution fuel limit: {limit}");
                                    true
                                }
                                _ => {
                                    println!(
                                        "Invalid fuel limit \"{value}\". Use a non-negative integer or off."
                                    );
                                    false
                                }
                            },
                        },
                        "module" => {
                            let module_id = if let Some(arg) = args.get(1) {
                                if let Some(module_id) =
                                    session.modules().id_by_path(&Path::single_str(arg))
                                {
                                    module_id
                                } else {
                                    println!("Module {arg} not found.");
                                    continue;
                                }
                            } else {
                                last_module
                            };
                            let module = session.modules().get(module_id);
                            if let Some(module) = module {
                                println!(
                                    "\n{}",
                                    module.format_with(&repl_show_module_options(&session))
                                );
                            } else {
                                println!(
                                    "Module never compiled succesfully and is thus not available for inspection."
                                );
                            }
                            true
                        }
                        "function" => {
                            let Some(function_arg) = args.get(1).copied() else {
                                println!("Function id or name is required.");
                                continue;
                            };
                            let qualified = split_qualified_function_name(function_arg);
                            let (module_id, module_name, function_name): (ModuleId, String, &str) =
                                if let Some(module_arg) = args.get(2) {
                                    let module_path = parse_repl_module_path(module_arg);
                                    if let Some(module_id) =
                                        session.modules().id_by_path(&module_path)
                                    {
                                        (module_id, module_arg.to_string(), function_arg)
                                    } else {
                                        println!("Module {module_arg} not found.");
                                        continue;
                                    }
                                } else if let Some((module_path, function_name)) = qualified {
                                    let module_name = module_path.to_string();
                                    if let Some(module_id) =
                                        session.modules().id_by_path(&module_path)
                                    {
                                        (module_id, module_name, function_name)
                                    } else {
                                        println!("Module {module_name} not found.");
                                        continue;
                                    }
                                } else {
                                    (last_module, String::from("current"), function_arg)
                                };
                            let module = session.modules().get(module_id);
                            let module = match module {
                                None => {
                                    println!(
                                        "Module never compiled succesfully and is thus not available for inspection."
                                    );
                                    continue;
                                }
                                Some(module) => module,
                            };
                            let fn_id = match function_name.parse::<usize>() {
                                Ok(index) => LocalFunctionId::from_index(index),
                                Err(_) => {
                                    // not a number, attempt to find by name
                                    match module.get_local_function_id(ustr(function_name)) {
                                        Some(id) => id,
                                        None => {
                                            println!(
                                                "Function name {function_name} not found in module {module_name}."
                                            );
                                            continue;
                                        }
                                    }
                                }
                            };
                            let function = if let Some(function) = module.get_function_by_id(fn_id)
                            {
                                function
                            } else {
                                println!("Function id {fn_id} not found in module {module_name}.");
                                continue;
                            };
                            let env = session.modules().env_for(module);
                            let fn_name = module
                                .get_function_name_by_id(fn_id)
                                .unwrap_or_else(|| ustr("<anonymous function>"));
                            println!("{}", (function, fn_name).format_with(&env));
                            true
                        }
                        "history" => {
                            for i in 0..counter {
                                let name = format!("repl{i}");
                                if let Some((_, module)) =
                                    session.modules().get_by_path(&Path::single_str(&name))
                                {
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

        // Process the input using the shared function
        let name = &format!("repl{counter}");
        let result = process_input(name, &src, counter, &mut session, true, fuel_limit);
        if let Ok(module) = result {
            last_module = module;
        }
        counter += 1;
        if let Err(e) = rl.save_history(history_filename) {
            println!("Failed to save history: {e:?}");
        }
    }
}
