// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::Location;
use crate::ast::Expr;
use crate::ast::ExprKind;
use crate::ast::PExpr;
use crate::ast::PExprKind;
use crate::ast::Pattern;
use crate::ast::PatternKind;
use crate::ast::Phase;
use crate::ast::UnnamedArg;
use crate::ast::UstrSpan;
use crate::containers::SVec2;
use crate::containers::b;
use crate::error::LocatedError;
use crate::escapes::apply_string_escapes;
use crate::std::string::String as MyString;
use crate::r#type::Type;
use crate::value::LiteralValue;
use crate::value::NativeDisplay;
use crate::value::Value;
use core::str::FromStr;
use lalrpop_util::ParseError;
use lalrpop_util::lexer::Token;
use num_traits::bounds::Bounded;
use ordered_float::NotNan;
use std::any::Any;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::LazyLock;
use ustr::{Ustr, ustr};

/// Create a span from two numbers (used by lalrpop with @L/@R positions)
pub(crate) fn span(l: usize, r: usize) -> Location {
    Location::new_local_usize(l, r)
}

/// Create a span from two u32 values (used when combining locations)
pub(crate) fn span_u32(l: u32, r: u32) -> Location {
    Location::new_local(l, r)
}

/// Make a custom parse error
pub(crate) fn parse_error<L, T>(msg: String, span: Location) -> ParseError<L, T, LocatedError> {
    ParseError::User { error: (msg, span) }
}

/// Make a custom parse error as part of a parsing result
pub(crate) fn error<R, L, T>(
    msg: String,
    span: Location,
) -> Result<R, ParseError<L, T, LocatedError>> {
    Err(parse_error(msg, span))
}

/// Make a literal
pub(crate) fn literal_value<T>(value: T) -> (LiteralValue, Type)
where
    T: Any + Clone + Debug + Eq + Hash + NativeDisplay + 'static,
{
    (LiteralValue::new_native(value), Type::primitive::<T>())
}

/// Make a literal expression
pub(crate) fn literal_expr<T>(value: T, span: Location) -> PExpr
where
    T: Any + Clone + Debug + Eq + Hash + NativeDisplay + 'static,
{
    PExpr::new(
        PExprKind::Literal(Value::native(value), Type::primitive::<T>()),
        span,
    )
}

/// Make a unit literal
pub(crate) fn unit_literal_expr(span: Location) -> PExpr {
    PExpr::new(PExprKind::Literal(Value::native(()), Type::unit()), span)
}

/// Make a literal
pub(crate) fn literal_pattern<T>(value: T, span: Location) -> Pattern
where
    T: Any + Clone + Debug + Eq + Hash + NativeDisplay + 'static,
{
    Pattern::new(
        PatternKind::Literal(LiteralValue::new_native(value), Type::primitive::<T>()),
        span,
    )
}

/// Parse a string literal, handling escapes
pub(crate) fn parse_string(s: &str) -> String {
    apply_string_escapes(&s[1..s.len() - 1])
}

/// Make a string literal
pub(crate) fn string_literal(s: &str) -> LiteralValue {
    let s = apply_string_escapes(&s[1..s.len() - 1]);
    LiteralValue::new_native(MyString::from_str(&s).unwrap())
}

/// Make formatted string
pub(crate) fn formatted_string(s: &str) -> PExprKind {
    let s = apply_string_escapes(&s[2..s.len() - 1]);
    PExprKind::FormattedString(s.to_string())
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
fn parse_num_value<F>(s: &str) -> Result<(LiteralValue, Type), String>
where
    F: FromStr + Bounded + Display + Clone + Debug + Eq + Hash + NativeDisplay + 'static,
{
    parse_num::<F>(s).map(|value| literal_value(value))
}

/// Parse a number, if it is too big, return an error
fn parse_num_literal<F, L, T>(
    s: &str,
    span: Location,
) -> Result<PExprKind, ParseError<L, T, LocatedError>>
where
    F: FromStr + Bounded + Display + Clone + Debug + Eq + Hash + NativeDisplay + 'static,
{
    use ExprKind::*;
    match parse_num_value::<F>(s) {
        Ok((value, ty)) => Ok(Literal(value.into_value(), ty)),
        Err(msg) => error(msg, span),
    }
}

/// Create a projection, or a float literal if the lhs is a number
pub(crate) fn proj_or_float<L, T>(
    lhs: PExpr,
    rhs: (usize, Location),
) -> Result<PExprKind, ParseError<L, T, LocatedError>> {
    use ExprKind::*;
    if let Literal(literal, _ty) = &lhs.kind {
        if let Some(value) = literal.clone().into_primitive_ty::<isize>() {
            let index = rhs.0;
            let float_value = format!("{value}.{index}");
            return parse_num_literal::<NotNan<f64>, L, T>(&float_value, rhs.1);
        }
    }
    Ok(Project(b(lhs), rhs))
}

pub(crate) fn syn_static_apply<P: Phase>(identifier: UstrSpan, args: Vec<Expr<P>>) -> ExprKind<P> {
    let identifier = Expr::<P>::new(ExprKind::Identifier(identifier.0), identifier.1);
    ExprKind::Apply(b(identifier), args, UnnamedArg::All)
}

pub(crate) fn assign_op(op: UstrSpan, lhs: PExpr, rhs: PExpr) -> PExprKind {
    let span = Location::new_local(lhs.span.start(), rhs.span.end());
    let apply = Expr::new(syn_static_apply(op, vec![lhs.clone(), rhs]), span);
    ExprKind::Assign(b(lhs), op.1, b(apply))
}

/// If all expressions are literals, create a literal tuple, otherwise create a tuple constructor
pub(crate) fn tuple(args: Vec<PExpr>) -> PExprKind {
    use ExprKind::*;
    let mut values_and_tys = Vec::new();
    for arg in &args {
        if let Literal(val, ty) = &arg.kind {
            values_and_tys.push((val.clone(), ty));
        } else {
            return Tuple(args);
        }
    }
    let (values, tys): (SVec2<_>, Vec<_>) = values_and_tys.into_iter().unzip();
    Literal(Value::tuple(values), Type::tuple(tys))
}

/// Create an if else block.
pub(crate) fn cond_if_else(cond: PExpr, if_true: PExpr, if_false: PExpr) -> PExprKind {
    use ExprKind::*;
    let cond_span = cond.span;
    Match(
        b(cond),
        vec![(literal_pattern(true, cond_span), if_true)],
        Some(b(if_false)),
    )
}

/// Create an if block without an else, make it return ().
pub(crate) fn cond_if(cond: PExpr, if_true: PExpr) -> PExprKind {
    use ExprKind::*;
    let cond_span = cond.span;
    let if_true_span = if_true.span;
    let unit_val = unit_literal_expr(if_true_span);
    Match(
        b(cond),
        vec![(literal_pattern(true, cond_span), if_true)],
        Some(b(unit_val)),
    )
}

/// Create a for loop
pub(crate) fn for_loop(var_name: UstrSpan, seq: PExpr, body: PExpr) -> PExprKind {
    let seq_span = seq.span;
    let seq_span_start = Location::new_local(seq.span.start(), seq.span.start());
    let iterator = PExpr::new(
        syn_static_apply((ustr("iter"), seq_span_start), vec![seq]),
        seq_span,
    );
    ExprKind::ForLoop(crate::ast::ForLoop::new(var_name, iterator, body))
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

/// Parse a single-line, Rust-style doc comment
pub(crate) fn parse_doc_comments(comment: Option<&str>) -> Option<String> {
    comment.map(|comment| comment.trim_start_matches("///").trim().to_string())
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

pub(crate) static EMPTY_USTR: LazyLock<Ustr> = LazyLock::new(|| ustr(""));
