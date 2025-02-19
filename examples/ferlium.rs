// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::ops::Deref;

use ariadne::Label;
use ferlium::emit_ir::{emit_expr, emit_module};
use ferlium::error::{
    resolve_must_be_mutable_ctx, InternalCompilationError, InternalCompilationErrorImpl,
    LocatedError, MutabilityMustBeWhat,
};
use ferlium::format::FormatWith;
use ferlium::module::{FmtWithModuleEnv, ModuleEnv};
use ferlium::std::{new_module_with_prelude, new_std_module_env};
use ferlium::typing_env::Local;
use ferlium::Location;
use ferlium::{parse_module_and_expr, SubOrSameType};
use rustyline::DefaultEditor;
use rustyline::{config::Configurer, error::ReadlineError};

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
            tuple_ty: expr_ty,
            tuple_span,
            index_span,
        } => {
            let span = span_union_range(*tuple_span, *index_span);
            let colored_ty = expr_ty.format_with(env).fg(Color::Blue);
            Report::build(ReportKind::Error, ("input", span))
                .with_message(format!(
                    "Type {} cannot be projected as a tuple.",
                    colored_ty
                ))
                .with_label(
                    Label::new(("input", span_range(*tuple_span)))
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
        DuplicatedRecordField {
            first_occurrence,
            second_occurrence,
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
                    "Data type {} is different than data type {}.",
                    a_ty, b_ty
                ))
                .with_label(
                    Label::new(("input", span_range(*a_span)))
                        .with_message(format!("type is {} here", a_ty))
                        .with_color(Color::Blue),
                )
                .with_label(
                    Label::new(("input", span_range(*b_span)))
                        .with_message(format!("but type is {} here", b_ty))
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
                .with_message(format!("Unsupported feature: {}.", reason))
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

fn main() {
    // Logging
    env_logger::init();

    // ferlium emission and evaluation contexts
    let other_modules = new_std_module_env();
    let mut module = new_module_with_prelude();
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
        let parse_result = parse_module_and_expr(&src);
        let (module_ast, expr_ast) = match parse_result {
            Ok(result) => result,
            Err(errors) => {
                pretty_print_parse_errors(&src, &errors);
                continue;
            }
        };
        {
            let env = ModuleEnv::new(&module, &other_modules);
            if !module_ast.is_empty() {
                println!("Module AST:\n{}", module_ast.format_with(&env));
            }
            if let Some(expr_ast) = expr_ast.as_ref() {
                println!("Expr AST:\n{}", expr_ast.format_with(&env));
            }
        }

        // Compile module
        if !module_ast.is_empty() {
            module = match emit_module(module_ast, &other_modules, Some(&module)) {
                Ok(module) => module,
                Err(e) => {
                    let env = ModuleEnv::new(&module, &other_modules);
                    pretty_print_checking_error(&e, &(env, src.as_str()));
                    continue;
                }
            };
            println!("Module IR:\n{}", FormatWith::new(&module, &other_modules));
        }
        module.source = Some(src.clone());

        // Is there an expression?
        let expr_ast = match expr_ast {
            Some(expr) => expr,
            None => {
                println!("No expression to evaluate.");
                continue;
            }
        };

        // Compile and evaluate expression
        let module_env = ModuleEnv::new(&module, &other_modules);
        let expr_ir = emit_expr(expr_ast, module_env, locals.clone());
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
                println!("Runtime error: {error}")
            }
        }

        if let Err(e) = rl.save_history(history_filename) {
            println!("Failed to save history: {:?}", e);
        }
    }
}
