// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{str::FromStr, sync::LazyLock};

use crate::parser_helpers::syn_static_apply_path;
use crate::{Location, internal_compilation_error};
use regex::Regex;
use ustr::{Ustr, ustr};

use crate::containers::b;
use crate::mutability::MutVal;
use crate::std::string::String;
use crate::{
    ast::{DExpr as Expr, DExprKind as ExprKind},
    error::InternalCompilationError,
    std::string::string_type,
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
    locals: &[Ustr],
) -> Result<Expr, InternalCompilationError> {
    if !locals.iter().rev().any(|&name| name == var_name) {
        return Err(internal_compilation_error!(
            UndefinedVarInStringFormatting {
                var_span,
                string_span,
            }
        ));
    };
    let var_expr = Expr::single_identifier(ustr(var_name), var_span);
    Ok(Expr::new(
        syn_static_apply_path(["std", "to_string"], var_span, vec![var_expr]),
        var_span,
    ))
}

pub fn emit_format_string_ast(
    input: &str,
    span: Location,
    locals: &[Ustr],
) -> Result<ExprKind, InternalCompilationError> {
    static REGEX: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"\{([\p{L}_][\p{L}\p{N}_]*)\}").unwrap());

    // Start with an empty mutable string.
    let mut exprs = vec![Expr::new(
        ExprKind::Let(
            (ustr("@s"), span),
            MutVal::mutable(),
            b(Expr::new(
                ExprKind::Literal(Value::native(String::new()), string_type()),
                span,
            )),
            None,
        ),
        span,
    )];
    let start_pos = span.start_usize() + 2; // starting of input in source code

    // Helper to extend that string with another one.
    let mut extend_exprs_with = |expr: Expr| {
        let span = expr.span;
        let extend_expr = Expr::new(
            syn_static_apply_path(
                ["std", "string_push_str"],
                span,
                vec![Expr::single_identifier(ustr("@s"), span), expr],
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
            let string_span = Location::new_usize(
                start_pos + last_end,
                start_pos + match_start,
                span.source_id(),
            );
            let string = &input[last_end..match_start];
            let expr = string_literal(string, string_span);
            extend_exprs_with(expr);
        }

        // Push the variable name found within the braces.
        let var_span = Location::new_usize(
            start_pos + match_start + 1,
            start_pos + match_end - 1,
            span.source_id(),
        );
        let var_name = &input[match_start + 1..match_end - 1];
        let expr = variable_to_string(var_name, var_span, span, locals)?;
        extend_exprs_with(expr);

        last_end = match_end;
    }
    // Append remaining literal text after the last match.
    if last_end < input.len() {
        let string_span = Location::new_usize(
            start_pos + last_end,
            start_pos + input.len(),
            span.source_id(),
        );
        let string = &input[last_end..];
        let expr = string_literal(string, string_span);
        extend_exprs_with(expr);
    }

    // Evaluate the mutable string and return it.
    let end_span = Location::new(span.end(), span.end(), span.source_id());
    exprs.push(Expr::single_identifier(ustr("@s"), end_span));

    Ok(ExprKind::Block(exprs))
}
