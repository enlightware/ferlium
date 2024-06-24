use lrlex::lrlex_mod;
use lrpar::{lrpar_mod, Span};

use crate::ast::{Expr, ExprKind, Module};

lrlex_mod!("lexer.l");
lrpar_mod!("parser.y");

pub fn parse(src: &str) -> (Module, Option<Expr>) {
    if src.trim().is_empty() {
        return (Module::default(), None);
    }
    let lexerdef = lexer_l::lexerdef();
    let lexer = lexerdef.lexer(src);
    let (res, errs) = parser_y::parse(&lexer);
    if let Some(_err) = errs.first() {
        let expr = Expr::new(
            ExprKind::Error("General parse error".into()),
            Span::new(0, src.len()),
        );
        return (Module::default(), Some(expr));
    }
    res.unwrap_or_default()
}
