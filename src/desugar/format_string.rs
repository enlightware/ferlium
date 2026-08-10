// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::sync::LazyLock;

use crate::ast::{DExprArena, DExprId, DLetPattern as LetPattern};
use crate::parser::helpers::syn_static_apply_path;
use crate::{Location, internal_compilation_error};
use regex::Regex;
use ustr::{Ustr, ustr};

use crate::std::string::StaticStr;
use crate::types::mutability::MutVal;
use crate::{
    ast::{DExpr as Expr, DExprKind as ExprKind},
    compiler::error::InternalCompilationError,
    hir::value::LiteralValue,
    std::string::{
        STRING_PUSH_STATIC_STR_FUNCTION_NAME, STRING_PUSH_STR_FUNCTION_NAME, static_str_type,
        string_type,
    },
};

/// A literal segment, kept as constant data rather than as an owned `string`.
///
/// Materializing it would allocate and copy the text on every execution only to append and free it.
/// The desugaring is the author of these segments, so no analysis is needed to know they are
/// constant: they are slices of the source being desugared, and interpolations take the separate
/// [`variable_to_string`] path regardless of what they evaluate to.
fn static_str_literal(string: &str, span: Location, arena: &mut DExprArena) -> DExprId {
    arena.alloc(Expr::new(
        ExprKind::literal(
            LiteralValue::new_native(StaticStr::new(string)),
            static_str_type(),
        ),
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
    let kind = syn_static_apply_path(
        ["std", "Value", "to_string"],
        var_span,
        vec![var_expr],
        arena,
    );
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
        ExprKind::literal(LiteralValue::new_native(StaticStr::new("")), string_type()),
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

    // Helper to extend that string, through whichever appender suits the segment's representation.
    let mut extend_exprs_with = |appender: &'static str,
                                 expr_id: DExprId,
                                 arena: &mut DExprArena| {
        let expr_span = arena[expr_id].span;
        let s_id = arena.alloc(Expr::single_identifier(ustr("@s"), span));
        let kind = syn_static_apply_path(["std", appender], expr_span, vec![s_id, expr_id], arena);
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
            let expr = static_str_literal(string, string_span, arena);
            extend_exprs_with(STRING_PUSH_STATIC_STR_FUNCTION_NAME, expr, arena);
        }

        // Push the variable name found within the braces.
        let var_span = Location::new_usize(
            start_pos + match_start + 1,
            start_pos + match_end - 1,
            span.source_id(),
        );
        let var_name = &input[match_start + 1..match_end - 1];
        let expr = variable_to_string(var_name, var_span, span, locals, arena)?;
        extend_exprs_with(STRING_PUSH_STR_FUNCTION_NAME, expr, arena);

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
        let expr = static_str_literal(string, string_span, arena);
        extend_exprs_with(STRING_PUSH_STATIC_STR_FUNCTION_NAME, expr, arena);
    }

    // Evaluate the mutable string and return it.
    let end_span = Location::new(span.end(), span.end(), span.source_id());
    let get_s = arena.alloc(Expr::single_identifier(ustr("@s"), end_span));
    exprs.push(get_s);

    Ok(ExprKind::block(exprs))
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn raw_mir(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        session.emit_mir("format_string", src)
    }

    /// Literal segments must reach the builder as constant data. Materializing them would allocate,
    /// copy and free a `string` per segment per execution, which no later pass can recover because
    /// the appended value is indistinguishable from any other by then.
    #[test]
    fn literal_segments_are_appended_without_materializing_a_string() {
        let body = raw_mir("fn greet(n: int) -> string { f\"item {n} of list\" }");

        assert_eq!(
            body.matches("call std::string_push_static_str").count(),
            2,
            "both literal segments must append from constant data:\n{body}"
        );
        assert_eq!(
            body.matches("call std::string_push_str").count(),
            1,
            "only the interpolation must append a materialized string:\n{body}"
        );
        assert_eq!(
            body.matches("call std::string_from_static").count(),
            1,
            "only the empty builder may still be materialized:\n{body}"
        );
    }
}
