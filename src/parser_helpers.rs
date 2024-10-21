use crate::ast::Expr;
use crate::ast::ExprKind;
use crate::ast::Pattern;
use crate::ast::PatternKind;
use crate::containers::SVec2;
use crate::containers::B;
use crate::error::LocatedError;
use crate::escapes::apply_string_escapes;
use crate::r#type::Type;
use crate::std::string::String as MyString;
use crate::value::NativeDisplay;
use crate::value::Value;
use crate::Span;
use core::str::FromStr;
use lalrpop_util::lexer::Token;
use lalrpop_util::ParseError;
use num_traits::bounds::Bounded;
use ordered_float::NotNan;
use std::any::Any;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::sync::LazyLock;
use ustr::{ustr, Ustr};

/// Create a span from two numbers
pub(crate) fn span(l: usize, r: usize) -> Span {
    Span::new(l, r)
}

/// Make a custom parse error
pub(crate) fn parse_error<L, T>(msg: String, span: Span) -> ParseError<L, T, LocatedError> {
    ParseError::User { error: (msg, span) }
}

/// Make a custom parse error as part of a parsing result
pub(crate) fn error<R, L, T>(msg: String, span: Span) -> Result<R, ParseError<L, T, LocatedError>> {
    Err(parse_error(msg, span))
}

/// Make a literal
pub(crate) fn literal_value<T>(value: T) -> (Value, Type)
where
    T: Any + Clone + Debug + Eq + NativeDisplay + 'static,
{
    (Value::native(value), Type::primitive::<T>())
}

/// Make a unit literal
pub(crate) fn unit_literal_expr(span: Span) -> Expr {
    Expr::new(ExprKind::Literal(Value::native(()), Type::unit()), span)
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
    let s = apply_string_escapes(&s[1..s.len() - 1]);
    Value::native(MyString::from_str(&s).unwrap())
}

/// Make formatted string
pub(crate) fn formatted_string(s: &str) -> ExprKind {
    let s = apply_string_escapes(&s[2..s.len() - 1]);
    ExprKind::FormattedString(s.to_string())
}

/// Parse a number, if it is too big, return an error
pub(crate) fn parse_num<F>(s: &str) -> Result<F, String>
where
    F: FromStr + Bounded + Display,
{
    match s.parse::<F>() {
        Ok(value) => Ok(value),
        Err(_) => Err(format!(
            "value {s} too large to fit in the range [{}, {}]",
            F::min_value(),
            F::max_value()
        )),
    }
}

/// Parse a number, if it is too big, return an error
pub(crate) fn parse_num_value<F>(s: &str) -> Result<(Value, Type), String>
where
    F: FromStr + Bounded + Display + Clone + Debug + Eq + NativeDisplay + 'static,
{
    parse_num::<F>(s).map(|value| literal_value(value))
}

/// Parse a number, if it is too big, return an error
pub(crate) fn parse_num_literal<F, L, T>(
    s: &str,
    span: Span,
) -> Result<ExprKind, ParseError<L, T, LocatedError>>
where
    F: FromStr + Bounded + Display + Clone + Debug + Eq + NativeDisplay + 'static,
{
    use ExprKind::*;
    match parse_num_value::<F>(s) {
        Ok((value, ty)) => Ok(Literal(value, ty)),
        Err(msg) => error(msg, span),
    }
}

/// Create a projection, or a float literal if the lhs is a number
pub(crate) fn proj_or_float<L, T>(
    lhs: Expr,
    rhs: (usize, Span),
) -> Result<ExprKind, ParseError<L, T, LocatedError>> {
    use ExprKind::*;
    if let Literal(literal, _ty) = &lhs.kind {
        if let Some(value) = literal.clone().into_primitive_ty::<isize>() {
            let index = rhs.0;
            let float_value = format!("{value}.{index}");
            return parse_num_literal::<NotNan<f64>, L, T>(&float_value, rhs.1);
        }
    }
    Ok(Project(B::new(lhs), rhs))
}

/// If all expressions are literals, create a literal tuple, otherwise create a tuple constructor
pub(crate) fn tuple(args: Vec<Expr>) -> ExprKind {
    use ExprKind::*;
    let mut values_and_tys = Vec::new();
    for arg in &args {
        if let Literal(val, ty) = &arg.kind {
            values_and_tys.push((val.clone(), ty));
        } else {
            return Tuple(args);
        }
    }
    let (values, tys): (SVec2<_>, _) = values_and_tys.into_iter().unzip();
    Literal(Value::tuple(values), Type::tuple(tys))
}

/// Create an if else block.
pub(crate) fn cond_if_else(cond: Expr, if_true: Expr, if_false: Expr) -> ExprKind {
    use ExprKind::*;
    let cond_span = cond.span;
    Match(
        B::new(cond),
        vec![(literal_pattern(true, cond_span), if_true)],
        Some(B::new(if_false)),
    )
}

/// Create an if block without an else, make it return ().
pub(crate) fn cond_if(cond: Expr, if_true: Expr) -> ExprKind {
    use ExprKind::*;
    let cond_span = cond.span;
    let if_true_span = if_true.span;
    let unit_val = unit_literal_expr(if_true_span);
    Match(
        B::new(cond),
        vec![(literal_pattern(true, cond_span), if_true)],
        Some(B::new(unit_val)),
    )
}

/// Create a for loop
pub(crate) fn for_loop(var: (Ustr, Span), start: Expr, end: Expr, body: Expr) -> ExprKind {
    use ExprKind::*;
    let iterator_span = Span::new(start.span.start(), end.span.end());
    let iterator = Expr::new(
        StaticApply(
            (ustr("range_iterator_new"), iterator_span),
            vec![start, end],
        ),
        iterator_span,
    );
    ForLoop(var, B::new(iterator), B::new(body))
}

/// Extend v with a single element e at the end
pub(crate) fn ext_b<T>(v: Vec<T>, e: T) -> Vec<T> {
    let mut result = v;
    result.push(e);
    result
}

/// Extend v with a single element e at the beginning
pub(crate) fn ext_f<T>(e: T, v: Vec<T>) -> Vec<T> {
    let mut result = vec![e];
    result.extend(v);
    result
}

/// Resolve token names using a static map
/// TODO: Go through intermediate data structure to allow for translation
fn resolve_token_names(names: Vec<String>) -> Vec<String> {
    static NAME_MAP: LazyLock<HashMap<&'static str, &'static str>> = LazyLock::new(|| {
        let mut m = HashMap::new();
        m.insert(r##"r#"[1-9][0-9]*|0"#"##, "natural number");
        m.insert(r##"r#"[\\p{L}_][\\p{L}\\p{N}_]*"#"##, "identifier");
        m.insert(r##"r#"\\\"([^\\\\\\\"]|\\\\.)*\\\""#"##, "string literal");
        m.insert(
            r##"r#"f\\\"([^\\\\\\\"]|\\\\.)*\\\""#"##,
            "formatted string literal",
        );
        m
    });
    names
        .into_iter()
        .map(|name| {
            NAME_MAP
                .get(name.as_str())
                .unwrap_or(&name.as_str())
                .to_string()
        })
        .collect()
}

/// Extract the name and the span from an error recovery data structure
pub(crate) fn describe_parse_error(
    error: ParseError<usize, Token<'_>, LocatedError>,
) -> LocatedError {
    use ParseError::*;
    match error {
        InvalidToken { location } => ("invalid token".to_string(), span(location, location + 1)),
        UnrecognizedEof { location, expected } => (
            if expected.len() > 1 {
                format!(
                    "expected one of {}, found EOF",
                    resolve_token_names(expected).join(", ")
                )
            } else {
                format!(
                    "expected {}, found EOF",
                    resolve_token_names(expected).join("")
                )
            },
            span(location, location),
        ),
        UnrecognizedToken { token, expected } => (
            if expected.len() > 1 {
                format!(
                    "expected one of {}, found \"{}\"",
                    resolve_token_names(expected).join(", "),
                    token.1,
                )
            } else {
                format!(
                    "expected {}, found \"{}\"",
                    resolve_token_names(expected).join(""),
                    token.1
                )
            },
            span(token.0, token.2),
        ),
        ExtraToken { token } => (
            format!("unexpected \"{}\"", token.1),
            span(token.0, token.2),
        ),
        User { error } => error,
    }
}
