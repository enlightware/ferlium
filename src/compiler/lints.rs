use crate::{
    Location,
    ast::{DExprArena, DExprId, ExprKind},
    compiler::diagnostics::CompilationWarning,
};

fn is_synthesized_unit_expr(arena: &DExprArena, expr: DExprId) -> bool {
    let expr = &arena[expr];
    expr.span.is_synthesized()
        && matches!(
            &expr.kind,
            ExprKind::Literal(value, _) if value.as_primitive_ty::<()>().is_some()
        )
}

/// Report returns whose value can flow directly from the enclosing function's tail position.
///
/// A semicolon-terminated return is followed in the AST by a synthesized unit tail. Only a return
/// immediately before that unit is needless: recursively inspecting any other statement there
/// could incorrectly classify an early return inside a discarded nested expression.
pub(crate) fn report_needless_returns_in_tail(
    arena: &DExprArena,
    expr: DExprId,
    warnings: &mut Vec<CompilationWarning>,
) {
    let node = &arena[expr];
    match &node.kind {
        ExprKind::Return(value) => {
            if !node.span.is_synthesized() {
                let value_span = arena[*value].span;
                debug_assert_eq!(node.span.source_id(), value_span.source_id());
                warnings.push(CompilationWarning::needless_return(Location::new(
                    node.span.start(),
                    value_span.end(),
                    node.span.source_id(),
                )));
            }
        }
        ExprKind::Block(exprs) => {
            let Some(&tail) = exprs.last() else {
                return;
            };
            if is_synthesized_unit_expr(arena, tail) {
                if let Some(&statement) = exprs.iter().rev().nth(1)
                    && matches!(arena[statement].kind, ExprKind::Return(_))
                {
                    report_needless_returns_in_tail(arena, statement, warnings);
                }
            } else {
                report_needless_returns_in_tail(arena, tail, warnings);
            }
        }
        ExprKind::Match(data) => {
            for (_, branch) in &data.alternatives {
                report_needless_returns_in_tail(arena, *branch, warnings);
            }
            if let Some(default) = data.default {
                report_needless_returns_in_tail(arena, default, warnings);
            }
        }
        ExprKind::EffectsUnsafe(expr) => {
            report_needless_returns_in_tail(arena, *expr, warnings);
        }
        ExprKind::TypeAscription(data) => {
            report_needless_returns_in_tail(arena, data.expr, warnings);
        }
        ExprKind::PatternConstraint(data) => {
            report_needless_returns_in_tail(arena, data.expr, warnings);
        }
        _ => {}
    }
}
