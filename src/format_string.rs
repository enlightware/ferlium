use std::{str::FromStr, sync::LazyLock};

use crate::{internal_compilation_error, Location};
use regex::Regex;
use ustr::ustr;

use crate::containers::B;
use crate::mutability::MutVal;
use crate::std::string::String;
use crate::{
    ast::{Expr, ExprKind},
    error::InternalCompilationError,
    std::string::string_type,
    typing_env::TypingEnv,
    value::Value,
};

fn string_literal(string: &str, span: Location) -> Expr {
    let string = String::from_str(string).unwrap();
    Expr::new(
        ExprKind::Literal(Value::native(string), string_type()),
        span,
    )
}

fn variable_to_string(
    var_name: &str,
    var_span: Location,
    string_span: Location,
    env: &TypingEnv,
) -> Result<Expr, InternalCompilationError> {
    if env.get_variable_index_and_type_scheme(var_name).is_none() {
        return Err(internal_compilation_error!(
            UndefinedVarInStringFormatting {
                var_span,
                string_span,
            }
        ));
    };
    let var_expr = Expr::new(ExprKind::Identifier(ustr(var_name)), var_span);
    Ok(Expr::new(
        ExprKind::StaticApply((ustr("std::to_string"), var_span), vec![var_expr]),
        var_span,
    ))
}

pub fn emit_format_string_ast(
    input: &str,
    span: Location,
    env: &TypingEnv,
) -> Result<Expr, InternalCompilationError> {
    static REGEX: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"\{([\p{L}_][\p{L}\p{N}_]*)\}").unwrap());

    // Start with an empty mutable string.
    let start_span = Location::new_local(span.start(), span.start());
    let mut exprs = vec![Expr::new(
        ExprKind::Let(
            (ustr("@s"), start_span),
            MutVal::mutable(),
            B::new(Expr::new(
                ExprKind::Literal(Value::native(String::new()), string_type()),
                start_span,
            )),
        ),
        start_span,
    )];
    let start_pos = span.start() + 2; // starting of input in source code

    // Helper to extend that string with another one.
    let mut extend_exprs_with = |expr: Expr| {
        let span = expr.span;
        let extend_expr = Expr::new(
            ExprKind::StaticApply(
                (ustr("std::string_push_str"), span),
                vec![Expr::new(ExprKind::Identifier(ustr("@s")), span), expr],
            ),
            span,
        );
        exprs.push(extend_expr);
    };

    // Iterate over all captures and assemble the AST.
    let mut last_end = 0;
    for caps in REGEX.captures_iter(input) {
        let cap = caps.get(0).unwrap();
        let match_start = cap.start();
        let match_end = cap.end();

        // Push the literal text before the match.
        if match_start > last_end {
            // Push the literal text before the match.
            let string_span = Location::new_local(start_pos + last_end, start_pos + match_start);
            let string = &input[last_end..match_start];
            let expr = string_literal(string, string_span);
            extend_exprs_with(expr);
        }

        // Push the variable name found within the braces.
        let var_span = Location::new_local(start_pos + match_start + 1, start_pos + match_end - 1);
        let var_name = &input[match_start + 1..match_end - 1];
        let expr = variable_to_string(var_name, var_span, span, env)?;
        extend_exprs_with(expr);

        last_end = match_end;
    }
    // Append remaining literal text after the last match.
    if last_end < input.len() {
        let string_span = Location::new_local(start_pos + last_end, start_pos + input.len());
        let string = &input[last_end..];
        let expr = string_literal(string, string_span);
        extend_exprs_with(expr);
    }

    // Evaluate the mutable string and return it.
    let end_span = Location::new_local(span.end(), span.end());
    exprs.push(Expr::new(ExprKind::Identifier(ustr("@s")), end_span));

    Ok(Expr::new(ExprKind::Block(exprs), span))
}
