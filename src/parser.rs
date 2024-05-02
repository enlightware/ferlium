use lrlex::lrlex_mod;
use lrpar::{lrpar_mod, Span};

use crate::ast::{Expr, ExprKind, Module};

lrlex_mod!("lexer.l");
lrpar_mod!("parser.y");

pub fn parse(src: &str) -> (Module, Option<Expr>) {
    let lexerdef = lexer_l::lexerdef();
    let lexer = lexerdef.lexer(src);
    let (res, _errs) = parser_y::parse(&lexer);
    // for e in errs {
    //     println!("{}", e.pp(&lexer, &parser_y::token_epp));
    // }
    match res {
        Some(ast) => ast,
        None => (
            Module::default(),
            Some(Expr::new(
                ExprKind::Error("Parse error".into()),
                Span::new(0, src.len()),
            )),
        ),
    }
}
