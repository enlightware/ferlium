use crate::ast::Expr;
use crate::ast::ExprKind;
use crate::ast::Pattern;
use crate::ast::PatternKind;
use crate::containers::SVec2;
use crate::containers::B;
use crate::escapes::apply_string_escapes;
use crate::r#type::Type;
use crate::std::string::String as MyString;
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

/// Take a lexeme, make sure it is correct, and get its string as ustr
pub(crate) fn us(lexeme: LexemeResult, lexer: DefaultLexer) -> Ustr {
    ustr(s(lexeme, lexer))
}

/// Take a lexeme, make sure it is correct, and get its string
pub(crate) fn s<'i>(lexeme: LexemeResult, lexer: DefaultLexer<'_, 'i>) -> &'i str {
    lexer.span_str(lex_span(lexeme))
}

/// Make a syntax error.
pub(crate) fn error(text: &str, span: Span) -> Expr {
    Expr::new(ExprKind::Error(text.into()), span)
}

/// Make a literal
pub(crate) fn literal_value<T>(value: T) -> (Value, Type)
where
    T: Any + Clone + Debug + Eq + NativeDisplay + 'static,
{
    (Value::native(value), Type::primitive::<T>())
}

/// Make a literal
pub(crate) fn literal_expr<T>(value: T, span: Span) -> Expr
where
    T: Any + Clone + Debug + Eq + NativeDisplay + 'static,
{
    Expr::new(
        ExprKind::Literal(Value::native(value), Type::primitive::<T>()),
        span,
    )
}

/// Make a literal
pub(crate) fn literal_pattern<T>(value: T, span: Span) -> Pattern
where
    T: Any + Clone + Debug + Eq + NativeDisplay + 'static,
{
    Pattern::new(
        PatternKind::Literal(Value::native(value), Type::primitive::<T>()),
        span,
    )
}

/// Make a string literal
pub(crate) fn string_literal(s: &str) -> Value {
    let s = apply_string_escapes(&s[1..s.len()-1]);
    Value::native(MyString::from_str(&s).unwrap())
}

/// Make formatted string
pub(crate) fn formatted_string(s: &str) -> ExprKind {
    let s = apply_string_escapes(&s[2..s.len()-1]);
    ExprKind::FormattedString(s.to_string())
}

/// Parse a number, if it is too big, return an error
pub(crate) fn parse_num<F>(s: &str) -> Result<(Value, Type), String>
where
    F: FromStr + Bounded + Display + Clone + Debug + Eq + NativeDisplay + 'static,
{
    match s.parse::<F>() {
        Ok(value) => Ok(literal_value(value)),
        Err(_) => Err(format!(
            "value {s} too large to fit in the range [{}, {}]",
            F::min_value(),
            F::max_value()
        )),
    }
}

/// Parse a number into an expression, if it is too big, return an error
pub(crate) fn parse_num_expr<F>(s: &str, span: Span) -> Expr
where
    F: FromStr + Bounded + Display + Clone + Debug + Eq + NativeDisplay + 'static,
{
    use ExprKind::*;
    match parse_num::<F>(s) {
        Ok((value, ty)) => Expr::new(Literal(value, ty), span),
        Err(err) => Expr::new(Error(err), span),
    }
}

/// Parse a number into a pattern, if it is too big, return an error
pub(crate) fn parse_num_pattern<F>(s: &str, span: Span) -> Pattern
where
    F: FromStr + Bounded + Display + Clone + Debug + Eq + NativeDisplay + 'static,
{
    use PatternKind::*;
    match parse_num::<F>(s) {
        Ok((value, ty)) => Pattern::new(Literal(value, ty), span),
        Err(err) => Pattern::new(Error(err), span),
    }
}

/// Depending on the context, create a projection or a float
pub(crate) fn make_proj_or_float(
    lhs: Expr,
    rhs: LexemeResult,
    lexer: DefaultLexer,
    span: Span,
) -> Expr {
    use ExprKind::*;
    let rhs_span = rhs.unwrap().span();
    let rhs = us(rhs, lexer);
    // see if we actually have a float
    if let Literal(literal, _ty) = &lhs.kind {
        if let Some(value) = literal.clone().into_primitive_ty::<isize>() {
            let float_value = format!("{value}.{rhs}");
            return parse_num_expr::<NotNan<f64>>(&float_value, span);
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
    use ExprKind::*;
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
    use ExprKind::*;
    let cond_span = cond.span;
    Expr::new(
        Match(
            B::new(cond),
            vec![(literal_pattern(true, cond_span), if_true)],
            Some(B::new(if_false)),
        ),
        span,
    )
}

/// Create an if block without an else, make it return ().
pub(crate) fn make_if_without_else(cond: Expr, if_true: Expr, span: Span) -> Expr {
    use ExprKind::*;
    let cond_span = cond.span;
    let if_true_span = if_true.span;
    let unit_val = Expr::new(Literal(Value::native(()), Type::unit()), if_true_span);
    let if_true = make_block(if_true, unit_val.clone(), if_true_span);
    Expr::new(
        Match(
            B::new(cond),
            vec![(literal_pattern(true, cond_span), if_true)],
            Some(B::new(unit_val)),
        ),
        span,
    )
}

pub(crate) fn make_iteration(
    var: LexemeResult,
    start: Expr,
    end: Expr,
    body: Expr,
    lexer: DefaultLexer,
    span: Span,
) -> Expr {
    use ExprKind::*;
    let iterator_span = Span::new(start.span.start(), end.span.end());
    let iterator = Expr::new(
        StaticApply(ustr("range_iterator_new"), iterator_span, vec![start, end]),
        iterator_span,
    );
    Expr::new(
        ForLoop(
            (us(var, lexer), lex_span(var)),
            B::new(iterator),
            B::new(body),
        ),
        span,
    )
}
