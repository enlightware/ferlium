// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{str::FromStr, sync::LazyLock};

use crate::ast::{DExprArena, DExprId, DLetPattern as LetPattern};
use crate::parser::helpers::syn_static_apply_path;
use crate::{Location, internal_compilation_error};
use regex::Regex;
use ustr::{Ustr, ustr};

use crate::std::string::String;
use crate::types::mutability::MutVal;
use crate::{
    ast::{DExpr as Expr, DExprKind as ExprKind},
    compiler::error::InternalCompilationError,
    hir::value::Value,
    std::string::string_type,
};

fn string_literal(string: &str, span: Location, arena: &mut DExprArena) -> DExprId {
    let string = String::from_str(string).unwrap();
    arena.alloc(Expr::new(
        ExprKind::literal(Value::native(string), string_type()),
        span,
    ))
}

fn variable_to_string(
    var_name: &str,
    var_span: Location,
    string_span: Location,
    locals: &[Ustr],
    arena: &mut DExprArena,
) -> Result<DExprId, InternalCompilationError> {
    if !locals.iter().rev().any(|&name| name == var_name) {
        return Err(internal_compilation_error!(
            UndefinedVarInStringFormatting {
                var_span,
                string_span,
            }
        ));
    };
    let var_expr = arena.alloc(Expr::new(
        ExprKind::Identifier(crate::ast::Path::single(ustr(var_name), var_span)),
        var_span,
    ));
    let kind = syn_static_apply_path(["std", "to_string"], var_span, vec![var_expr], arena);
    Ok(arena.alloc(Expr::new(kind, var_span)))
}

pub fn emit_format_string_ast(
    input: &str,
    span: Location,
    locals: &[Ustr],
    arena: &mut DExprArena,
) -> Result<ExprKind, InternalCompilationError> {
    static REGEX: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"\{([\p{L}_][\p{L}\p{N}_]*)\}").unwrap());

    // Start with an empty mutable string.
    let empty_string = arena.alloc(Expr::new(
        ExprKind::literal(Value::native(String::default()), string_type()),
        span,
    ));
    let let_stmt = arena.alloc(Expr::new(
        ExprKind::let_(
            LetPattern::binding((ustr("@s"), span), MutVal::mutable()),
            empty_string,
            None,
        ),
        span,
    ));
    let mut exprs = vec![let_stmt];
    let start_pos = span.start_usize() + 2; // starting of input in source code

    // Helper to extend that string with another one.
    let mut extend_exprs_with = |expr_id: DExprId, arena: &mut DExprArena| {
        let expr_span = arena[expr_id].span;
        let s_id = arena.alloc(Expr::single_identifier(ustr("@s"), span));
        let kind = syn_static_apply_path(
            ["std", "string_push_str"],
            expr_span,
            vec![s_id, expr_id],
            arena,
        );
        let extend_id = arena.alloc(Expr::new(kind, expr_span));
        exprs.push(extend_id);
    };

    // Iterate over all captures and assemble the AST.
    let mut last_end = 0;
    for caps in REGEX.captures_iter(input) {
        let cap = caps.get(0).unwrap();
        let match_start = cap.start();
        let match_end = cap.end();

        // Push the literal text before the match.
        if match_start > last_end {
            let string_span = Location::new_usize(
                start_pos + last_end,
                start_pos + match_start,
                span.source_id(),
            );
            let string = &input[last_end..match_start];
            let expr = string_literal(string, string_span, arena);
            extend_exprs_with(expr, arena);
        }

        // Push the variable name found within the braces.
        let var_span = Location::new_usize(
            start_pos + match_start + 1,
            start_pos + match_end - 1,
            span.source_id(),
        );
        let var_name = &input[match_start + 1..match_end - 1];
        let expr = variable_to_string(var_name, var_span, span, locals, arena)?;
        extend_exprs_with(expr, arena);

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
        let expr = string_literal(string, string_span, arena);
        extend_exprs_with(expr, arena);
    }

    // Evaluate the mutable string and return it.
    let end_span = Location::new(span.end(), span.end(), span.source_id());
    let get_s = arena.alloc(Expr::single_identifier(ustr("@s"), end_span));
    exprs.push(get_s);

    Ok(ExprKind::block(exprs))
}
