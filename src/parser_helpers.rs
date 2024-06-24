use crate::ast::Expr;
use crate::ast::ExprKind::*;
use crate::containers::SVec2;
use crate::containers::B;
use crate::r#type::Type;
use crate::value::NativeDisplay;
use crate::value::Value;
use cfgrammar::span::Span;
use core::str::FromStr;
use lrlex::DefaultLexeme;
use lrlex::DefaultLexerTypes;
use lrpar::Lexeme;
use lrpar::NonStreamingLexer;
use num_traits::bounds::Bounded;
use ordered_float::NotNan;
use std::any::Any;
use std::fmt::{Debug, Display};
use ustr::{ustr, Ustr};

type LexemeResult = Result<DefaultLexeme, DefaultLexeme>;
type DefaultLexer<'i, 'l> = &'l (dyn NonStreamingLexer<'i, DefaultLexerTypes> + 'l);

/// Take the span of a lexeme, regardless its result
pub(crate) fn lex_span(lexeme: LexemeResult) -> Span {
    match lexeme {
        Ok(lexeme) => lexeme.span(),
        Err(lexeme) => lexeme.span(),
    }
}

/// Take a lexeme, make sure it is correct, and get its string
pub(crate) fn s(lexeme: LexemeResult, lexer: DefaultLexer) -> Ustr {
    ustr(lexer.span_str(lex_span(lexeme)))
}

/// Make a syntax error.
pub(crate) fn error(text: &str, span: Span) -> Expr {
    Expr::new(Error(text.into()), span)
}

/// Make a literal
pub(crate) fn literal<T>(value: T, span: Span) -> Expr
where
    T: Any + Clone + Debug + Eq + NativeDisplay + 'static,
{
    Expr::new(Literal(Value::native(value), Type::primitive::<T>()), span)
}

/// Parse an integer, if it is too big, return an error
pub(crate) fn parse_num<F>(s: &str, span: Span) -> Expr
where
    F: FromStr + Bounded + Display + Clone + Debug + Eq + NativeDisplay + 'static,
{
    match s.parse::<F>() {
        Ok(value) => literal(value, span),
        Err(_) => Expr::new(
            Error(format!(
                "integer {s} too large to fit in the range [{}, {}]",
                F::min_value(),
                F::max_value()
            )),
            span,
        ),
    }
}

/// Depending on the context, create a projection or a float
pub(crate) fn make_proj_or_float(
    lhs: Expr,
    rhs: LexemeResult,
    lexer: DefaultLexer,
    span: Span,
) -> Expr {
    let rhs_span = rhs.unwrap().span();
    let rhs = s(rhs, lexer);
    // see if we actually have a float
    if let Literal(literal, _ty) = &lhs.kind {
        if let Some(value) = literal.clone().into_primitive_ty::<isize>() {
            let float_value = format!("{value}.{rhs}");
            return parse_num::<NotNan<f64>>(&float_value, span);
        }
    }
    let index = match rhs.parse::<usize>() {
        Ok(index) => index,
        Err(_) => return Expr::new(Error(format!("invalid index: {rhs}")), rhs_span),
    };
    Expr::new(Project(B::new(lhs), index, rhs_span), span)
}

/// If all expressions are literals, create a literal tuple, otherwise create a tuple constructor
pub(crate) fn make_tuple(args: Vec<Expr>, span: Span) -> Expr {
    let mut values_and_tys = Vec::new();
    for arg in &args {
        if let Literal(val, ty) = &arg.kind {
            values_and_tys.push((val.clone(), ty));
        } else {
            return Expr::new(Tuple(args), span);
        }
    }
    let (values, tys): (SVec2<_>, _) = values_and_tys.into_iter().unzip();
    Expr::new(Literal(Value::tuple(values), Type::tuple(tys)), span)
}

/// Create a block node with the two expressions, if these are also blocks, merge them.
pub(crate) fn make_block(lhs: Expr, rhs: Expr, span: Span) -> Expr {
    use crate::ast::ExprKind;
    let mut exprs = Vec::new();
    if let ExprKind::Block(mut block) = lhs.kind {
        exprs.append(&mut block);
    } else {
        exprs.push(lhs);
    }
    if let ExprKind::Block(mut block) = rhs.kind {
        exprs.append(&mut block);
    } else {
        exprs.push(rhs);
    }
    Expr::new(ExprKind::Block(exprs), span)
}

/// Create an if else block.
pub(crate) fn make_if_else(cond: Expr, if_true: Expr, if_false: Expr, span: Span) -> Expr {
    let cond_span = cond.span;
    Expr::new(
        Match(
            B::new(cond),
            vec![(literal(true, cond_span), if_true)],
            Some(B::new(if_false)),
        ),
        span,
    )
}

/// Create an if block without an else, make it return ().
pub(crate) fn make_if_without_else(cond: Expr, if_true: Expr, span: Span) -> Expr {
    let cond_span = cond.span;
    let if_true_span = if_true.span;
    let unit_val = Expr::new(Literal(Value::native(()), Type::unit()), if_true_span);
    let if_true = make_block(if_true, unit_val.clone(), if_true_span);
    Expr::new(
        Match(
            B::new(cond),
            vec![(literal(true, cond_span), if_true)],
            Some(B::new(unit_val)),
        ),
        span,
    )
}
