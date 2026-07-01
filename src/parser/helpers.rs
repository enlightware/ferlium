// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::Location;
use crate::SourceId;
use crate::ast::Attribute;
use crate::ast::Expr;
use crate::ast::ExprArena;
use crate::ast::ExprId;
use crate::ast::ExprKind;
use crate::ast::ForLoopData;
use crate::ast::GenericParams;
use crate::ast::MapLiteralEntry;
use crate::ast::PEffect;
use crate::ast::PExpr;
use crate::ast::PExprArena;
use crate::ast::PExprId;
use crate::ast::PExprKind;
use crate::ast::PLetPattern;
use crate::ast::PType;
use crate::ast::PTypeConstraintInput;
use crate::ast::PTypeConstraintOutput;
use crate::ast::PTypeSpan;
use crate::ast::Path;
use crate::ast::Pattern;
use crate::ast::PatternKind;
use crate::ast::Phase;
use crate::ast::TypeConstraintEffectOutput;
use crate::ast::UnnamedArg;
use crate::ast::UstrSpan;
use crate::compiler::error::LocatedError;
use crate::containers::SVec2;
use crate::containers::b;
use crate::hir::value::{LiteralNativeValue, LiteralValue};
use crate::parser::escapes::apply_string_escapes;
use crate::std::math::{Float, int_type};
use crate::std::string::String as MyString;
use crate::types::r#type::{Type, TypeDefProductDocs, TypeDefShapeDocs, TypeDefVariantDocs};
use core::str::FromStr;
use lalrpop_util::ParseError;
use lalrpop_util::lexer::Token;
use num_traits::bounds::Bounded;
use std::fmt::{Debug, Display};

use crate::FxHashMap;
use std::sync::LazyLock;
use ustr::{Ustr, ustr};

/// One item in a neutral `<...>` type/trait argument list.
#[derive(Debug)]
pub(crate) enum AngleTypeArg {
    Positional(PTypeSpan),
    Named { name: UstrSpan, ty: PTypeSpan },
}

/// Neutral representation for `Path<...>` contents.
///
/// The parser intentionally does not decide whether `Path<...>` is a type
/// application or a trait constraint head. That is context-sensitive: in
/// `MapIterator<I ! E>` the `! E` section is a type effect argument, while in
/// `Iterator<Self = I |-> Item = T ! NextEffect = E>` the `!` section belongs
/// to associated effect outputs.
#[derive(Debug, Default)]
pub(crate) struct AngleArgs {
    pub(crate) inputs: Vec<AngleTypeArg>,
    pub(crate) output_types: Vec<PTypeConstraintOutput>,
    pub(crate) output_effects: Vec<TypeConstraintEffectOutput>,
    pub(crate) effect_args: Vec<PEffect>,
}

pub(crate) type TypeApplicationArgsResult<L, T> =
    Result<(Vec<PTypeSpan>, Vec<PEffect>), ParseError<L, T, LocatedError>>;

pub(crate) type TraitHeadArgsResult<L, T> = Result<
    (
        Vec<PTypeConstraintInput>,
        Vec<PTypeConstraintOutput>,
        Vec<TypeConstraintEffectOutput>,
    ),
    ParseError<L, T, LocatedError>,
>;

pub(crate) type ParsedSubscriptHeader = (Option<PTypeSpan>, UstrSpan, GenericParams);
pub(crate) type ParsedSubscriptHeaderTail = (Option<UstrSpan>, GenericParams, Option<Location>);
pub(crate) type ParsedSubscriptHeaderAngleTail = (Option<UstrSpan>, GenericParams, Option<usize>);

pub(crate) fn subscript_header(
    name: UstrSpan,
    tail: Option<ParsedSubscriptHeaderTail>,
) -> ParsedSubscriptHeader {
    let (field, generic_params, receiver_args_span) =
        tail.unwrap_or((None, GenericParams::default(), None));
    match field {
        Some(field) => {
            let receiver_span = receiver_args_span
                .and_then(|span| Location::fuse([name.1, span]))
                .unwrap_or(name.1);
            let receiver_ty = if generic_params.type_params().is_empty() {
                (PType::Path(Path::new(vec![name])), receiver_span)
            } else {
                let receiver_args = generic_params
                    .type_params()
                    .iter()
                    .map(|arg| (PType::Path(Path::new(vec![*arg])), arg.1))
                    .collect();
                (
                    PType::path_with_args(Path::new(vec![name]), receiver_args),
                    receiver_span,
                )
            };
            (Some(receiver_ty), field, generic_params)
        }
        None => (None, name, generic_params),
    }
}

pub(crate) fn subscript_header_tail_with_generic_span(
    left: usize,
    tail: ParsedSubscriptHeaderAngleTail,
    source_id: SourceId,
) -> ParsedSubscriptHeaderTail {
    let (field, generic_params, end) = tail;
    (
        field,
        generic_params,
        end.map(|end| span(left, end, source_id)),
    )
}

pub(crate) fn validate_type_application_args<L, T>(
    args: AngleArgs,
) -> TypeApplicationArgsResult<L, T> {
    let AngleArgs {
        inputs,
        output_types,
        output_effects,
        effect_args,
    } = args;
    if let Some(named) = inputs.iter().find_map(|arg| match arg {
        AngleTypeArg::Named { name, .. } => Some(name),
        AngleTypeArg::Positional(_) => None,
    }) {
        return error(
            "named type arguments are only valid in trait constraints".into(),
            named.1,
        );
    }
    if let Some(output) = output_types.first() {
        return error(
            "associated type bindings are only valid in trait constraints".into(),
            output.name.1,
        );
    }
    if let Some(output) = output_effects.first() {
        return error(
            "associated effect bindings are only valid in trait constraints".into(),
            output.name.1,
        );
    }
    Ok((
        inputs
            .into_iter()
            .map(|arg| match arg {
                AngleTypeArg::Positional(ty) => ty,
                AngleTypeArg::Named { .. } => unreachable!(),
            })
            .collect(),
        effect_args,
    ))
}

pub(crate) fn validate_trait_head_args<L, T>(args: AngleArgs) -> TraitHeadArgsResult<L, T> {
    let AngleArgs {
        inputs,
        output_types,
        output_effects,
        effect_args,
    } = args;
    if let Some(effect) = effect_args.first() {
        return error(
            "bare effect arguments are only valid in type applications".into(),
            effect.name.1,
        );
    }
    Ok((
        inputs
            .into_iter()
            .map(|arg| match arg {
                AngleTypeArg::Positional(ty) => PTypeConstraintInput { name: None, ty },
                AngleTypeArg::Named { name, ty } => PTypeConstraintInput {
                    name: Some(name),
                    ty,
                },
            })
            .collect(),
        output_types,
        output_effects,
    ))
}

/// Create a span from two numbers (used by lalrpop with @L/@R positions)
pub(crate) fn span(l: usize, r: usize, source_id: SourceId) -> Location {
    Location::new_usize(l, r, source_id)
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
    T: LiteralNativeValue + 'static,
{
    (LiteralValue::new_native(value), Type::primitive::<T>())
}

/// Make a literal expression and allocate it in the arena
pub(crate) fn literal_expr<T>(value: T, span: Location, arena: &mut PExprArena) -> PExprId
where
    T: LiteralNativeValue + 'static,
{
    arena.alloc(PExpr::new(
        PExprKind::Literal(LiteralValue::new_native(value), Type::primitive::<T>()),
        span,
    ))
}

/// Make a unit literal and allocate it in the arena
pub(crate) fn unit_literal_expr(span: Location, arena: &mut PExprArena) -> PExprId {
    arena.alloc(PExpr::new(
        PExprKind::Literal(LiteralValue::new_native(()), Type::unit()),
        span,
    ))
}

/// Make a literal
pub(crate) fn literal_pattern<T>(value: T, span: Location) -> Pattern
where
    T: LiteralNativeValue + 'static,
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

/// Parse a binary integer literal like "0b1010" into an isize.
pub(crate) fn parse_bin_int(s: &str) -> Result<isize, String> {
    let digits = s.strip_prefix("0b").unwrap_or(s);
    isize::from_str_radix(digits, 2).map_err(|_| {
        format!(
            "value {s} too large to fit in the range [{}, {}]",
            isize::MIN,
            isize::MAX
        )
    })
}

/// Parse a hexadecimal integer literal like "0xff" into an isize.
pub(crate) fn parse_hex_int(s: &str) -> Result<isize, String> {
    let digits = s.strip_prefix("0x").unwrap_or(s);
    isize::from_str_radix(digits, 16).map_err(|_| {
        format!(
            "value {s} too large to fit in the range [{}, {}]",
            isize::MIN,
            isize::MAX
        )
    })
}

/// Parse a number, if it is too big, return an error
fn parse_num_value<F>(s: &str) -> Result<(LiteralValue, Type), String>
where
    F: FromStr + Bounded + Display + LiteralNativeValue + 'static,
{
    parse_num::<F>(s).map(|value| literal_value(value))
}

/// Parse a number, if it is too big, return an error
fn parse_num_literal<F, L, T>(
    s: &str,
    span: Location,
) -> Result<PExprKind, ParseError<L, T, LocatedError>>
where
    F: FromStr + Bounded + Display + LiteralNativeValue + 'static,
{
    match parse_num_value::<F>(s) {
        Ok((value, ty)) => Ok(ExprKind::literal(value, ty)),
        Err(msg) => error(msg, span),
    }
}

/// Create a projection, or a float literal if the lhs is a number
pub(crate) fn proj_or_float<L, T>(
    lhs: PExprId,
    rhs: (usize, Location),
    arena: &PExprArena,
) -> Result<PExprKind, ParseError<L, T, LocatedError>> {
    use ExprKind::*;
    // Extract the integer literal value without holding a borrow across the match
    let int_val = if let Literal(literal, _ty) = &arena[lhs].kind {
        literal.clone().into_value().into_primitive_ty::<isize>()
    } else {
        None
    };
    if let Some(value) = int_val {
        let index = rhs.0;
        let float_value = format!("{value}.{index}");
        return parse_num_literal::<Float, L, T>(&float_value, rhs.1);
    }
    Ok(ExprKind::project(lhs, rhs))
}

pub(crate) enum PExprSuffixTail {
    Field(UstrSpan),
    TupleIndex((usize, Location)),
    Index(PExprId, Location),
    Apply(Vec<PExprId>, Location),
    NamedSubscript(UstrSpan, Vec<PExprId>, Location),
}

impl PExprSuffixTail {
    fn span(&self) -> Location {
        match self {
            Self::Field((_, span)) | Self::TupleIndex((_, span)) => *span,
            Self::Index(_, span) | Self::Apply(_, span) | Self::NamedSubscript(_, _, span) => *span,
        }
    }
}

pub(crate) fn fold_suffix_expr<L, T>(
    base: PExprId,
    tails: Vec<PExprSuffixTail>,
    arena: &mut PExprArena,
) -> Result<PExprKind, ParseError<L, T, LocatedError>> {
    let Some((last, prefix)) = tails.split_last() else {
        return Ok(arena[base].kind.clone());
    };

    let mut current = base;
    for tail in prefix {
        current = alloc_suffix_tail(current, tail, arena)?;
    }
    suffix_tail_kind(current, last, arena)
}

fn alloc_suffix_tail<L, T>(
    receiver: PExprId,
    tail: &PExprSuffixTail,
    arena: &mut PExprArena,
) -> Result<PExprId, ParseError<L, T, LocatedError>> {
    let span = Location::fuse([arena[receiver].span, tail.span()])
        .expect("suffix tail should have a source span");
    let kind = suffix_tail_kind(receiver, tail, arena)?;
    Ok(arena.alloc(PExpr::new(kind, span)))
}

fn suffix_tail_kind<L, T>(
    receiver: PExprId,
    tail: &PExprSuffixTail,
    arena: &mut PExprArena,
) -> Result<PExprKind, ParseError<L, T, LocatedError>> {
    match tail {
        PExprSuffixTail::Field(field) => Ok(ExprKind::field_access(receiver, *field)),
        PExprSuffixTail::TupleIndex(index) => proj_or_float(receiver, *index, arena),
        PExprSuffixTail::Index(index, _) => Ok(ExprKind::index(receiver, *index)),
        PExprSuffixTail::Apply(args, _) => {
            Ok(ExprKind::apply(receiver, args.clone(), UnnamedArg::None))
        }
        PExprSuffixTail::NamedSubscript(name, args, _) => {
            Ok(ExprKind::named_subscript(receiver, *name, args.clone()))
        }
    }
}

pub(crate) fn syn_static_apply<P: Phase>(
    identifier: UstrSpan,
    args: Vec<ExprId<P>>,
    arena: &mut ExprArena<P>,
) -> ExprKind<P> {
    let func = arena.alloc(Expr::<P>::single_identifier(identifier.0, identifier.1));
    ExprKind::apply(func, args, UnnamedArg::All)
}

pub(crate) fn syn_static_apply_path<P: Phase>(
    identifiers: impl Into<Vec<&'static str>>,
    identifier_span: Location,
    args: Vec<ExprId<P>>,
    arena: &mut ExprArena<P>,
) -> ExprKind<P> {
    let path = Path::new(
        identifiers
            .into()
            .into_iter()
            .map(|s| (ustr(s), identifier_span))
            .collect(),
    );
    let func = arena.alloc(Expr::new(ExprKind::identifier(path), identifier_span));
    ExprKind::apply(func, args, UnnamedArg::All)
}

pub(crate) fn assign_op(
    identifiers: impl Into<Vec<&'static str>>,
    identifier_span: Location,
    lhs: PExprId,
    rhs: PExprId,
) -> PExprKind {
    let path = Path::new(
        identifiers
            .into()
            .into_iter()
            .map(|s| (ustr(s), identifier_span))
            .collect(),
    );
    ExprKind::assign_op(lhs, identifier_span, path, rhs)
}

pub(crate) fn build_range(
    identifiers: impl Into<Vec<&'static str>>,
    identifier_span: Location,
    start: PExprId,
    end: PExprId,
    arena: &mut PExprArena,
) -> PExprKind {
    // Forces not using the from_int method when int literals are used
    let start_span = arena[start].span;
    let start_asc = arena.alloc(PExpr::new(
        ExprKind::type_ascription(start, PType::Resolved(int_type()), start_span),
        start_span,
    ));
    let end_span = arena[end].span;
    let end_asc = arena.alloc(PExpr::new(
        ExprKind::type_ascription(end, PType::Resolved(int_type()), end_span),
        end_span,
    ));
    let path = Path::new(
        identifiers
            .into()
            .into_iter()
            .map(|s| (ustr(s), identifier_span))
            .collect(),
    );
    ExprKind::struct_literal(
        path,
        vec![
            ((ustr("start"), start_span), start_asc),
            ((ustr("end"), end_span), end_asc),
        ],
    )
}

/// Build a tuple constructor. Constant folding belongs in later partial evaluation.
pub(crate) fn tuple(args: Vec<PExprId>, arena: &PExprArena) -> PExprKind {
    let _ = arena;
    ExprKind::tuple(args)
}

/// Build a record constructor. Constant folding belongs in later partial evaluation.
pub(crate) fn record(fields: Vec<(UstrSpan, PExprId)>, arena: &PExprArena) -> PExprKind {
    let _ = arena;
    ExprKind::record(fields)
}

/// Build a record literal pattern from a list of `(name, (value, type))` pairs.
/// Fields are sorted by name to match how records are stored internally.
pub(crate) fn record_literal_pattern(
    fields: Vec<(UstrSpan, (LiteralValue, Type))>,
) -> (LiteralValue, Type) {
    let mut fields: Vec<(Ustr, LiteralValue, Type)> = fields
        .into_iter()
        .map(|((name, _span), (val, ty))| (name, val, ty))
        .collect();
    fields.sort_by_key(|(name, _, _)| *name);
    let vals: SVec2<LiteralValue> = fields.iter().map(|(_, val, _)| val.clone()).collect();
    let names_tys: Vec<(Ustr, Type)> = fields.into_iter().map(|(name, _, ty)| (name, ty)).collect();
    let val = LiteralValue::new_tuple(vals);
    let ty = Type::record(names_tys);
    (val, ty)
}

pub(crate) enum PathBraceItem {
    Field((UstrSpan, PExprId)),
    Expr(PExprId),
    MapEntry(MapLiteralEntry),
}

fn is_single_segment_path(path: &Path, name: &str) -> bool {
    path.segments.len() == 1 && path.segments[0].0 == ustr(name)
}

pub(crate) fn path_brace_expr<L, T>(
    path: Path,
    items: Vec<PathBraceItem>,
    span: Location,
    arena: &mut PExprArena,
) -> Result<PExprKind, ParseError<L, T, LocatedError>> {
    if is_single_segment_path(&path, "set") {
        let mut elements = Vec::with_capacity(items.len());
        for item in items {
            match item {
                PathBraceItem::Expr(expr) => elements.push(expr),
                PathBraceItem::Field(_) | PathBraceItem::MapEntry(_) => {
                    return error("set literal entries must be expressions".into(), span);
                }
            }
        }
        return Ok(PExprKind::set_literal(elements));
    }

    if is_single_segment_path(&path, "map") {
        let mut entries = Vec::with_capacity(items.len());
        for item in items {
            match item {
                PathBraceItem::MapEntry(entry) => entries.push(entry),
                PathBraceItem::Field(_) | PathBraceItem::Expr(_) => {
                    return error(
                        "map literal entries must use `key => value` syntax".into(),
                        span,
                    );
                }
            }
        }
        return Ok(PExprKind::map_literal(entries));
    }

    let mut fields = Vec::with_capacity(items.len());
    for item in items {
        match item {
            PathBraceItem::Field(field) => fields.push(field),
            PathBraceItem::Expr(expr) => match &arena[expr].kind {
                PExprKind::Identifier(path) if path.segments.len() == 1 => {
                    fields.push((path.segments[0], expr));
                }
                _ => {
                    return error(
                        "struct literal shorthand fields must be identifiers".into(),
                        span,
                    );
                }
            },
            PathBraceItem::MapEntry(_) => {
                return error(
                    "map entry syntax is only supported in map literals".into(),
                    span,
                );
            }
        }
    }
    Ok(PExprKind::struct_literal(path, fields))
}

/// Create an if else block.
pub(crate) fn cond_if_else(
    cond: PExprId,
    if_true: PExprId,
    if_false: PExprId,
    arena: &PExprArena,
) -> PExprKind {
    let cond_span = arena[cond].span;
    ExprKind::match_(
        cond,
        vec![(literal_pattern(true, cond_span), if_true)],
        Some(if_false),
    )
}

/// Create an if block without an else, make it return ().
pub(crate) fn cond_if(cond: PExprId, if_true: PExprId, arena: &mut PExprArena) -> PExprKind {
    let cond_span = arena[cond].span;
    let if_true_span = arena[if_true].span;
    let unit_val = unit_literal_expr(if_true_span, arena);
    ExprKind::match_(
        cond,
        vec![(literal_pattern(true, cond_span), if_true)],
        Some(unit_val),
    )
}

/// Create a for loop
pub(crate) fn for_loop(
    pattern: PLetPattern,
    seq: PExprId,
    body: PExprId,
    arena: &mut PExprArena,
) -> PExprKind {
    let seq_span = arena[seq].span;
    let seq_span_start = seq_span.start_location();
    let iter_kind = syn_static_apply((ustr("iter"), seq_span_start), vec![seq], arena);
    let iterator = arena.alloc(PExpr::new(iter_kind, seq_span));
    ExprKind::for_loop(b(ForLoopData::new(pattern, iterator, body)))
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

/// Parse one or more consecutive Rust-style doc comment lines and join them with newlines.
pub(crate) fn parse_doc_comments(comments: Vec<&str>) -> Option<String> {
    if comments.is_empty() {
        None
    } else {
        Some(
            comments
                .iter()
                .map(|c| c.trim_start_matches("///").trim())
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }
}

pub(crate) type DocTypeSpan = (PTypeSpan, Option<String>);
pub(crate) type DocRecordField = (UstrSpan, PTypeSpan, Option<String>);
pub(crate) type TypeDefProduct = (PType, TypeDefProductDocs);
pub(crate) type ParsedEnumVariant = (UstrSpan, PTypeSpan, Vec<Attribute>, TypeDefVariantDocs);

pub(crate) fn type_def_unit_product() -> TypeDefProduct {
    (PType::Unit, TypeDefProductDocs::Unit)
}

pub(crate) fn type_def_record_product(fields: Vec<DocRecordField>) -> TypeDefProduct {
    let docs = TypeDefProductDocs::Record(
        fields
            .iter()
            .map(|(name, _, doc)| (name.0, doc.clone()))
            .collect(),
    );
    let ty = PType::Record(fields.into_iter().map(|(name, ty, _)| (name, ty)).collect());
    (ty, docs)
}

pub(crate) fn type_def_tuple_product(fields: Vec<DocTypeSpan>) -> TypeDefProduct {
    let docs = TypeDefProductDocs::Tuple(fields.iter().map(|(_, doc)| doc.clone()).collect());
    let ty = PType::Tuple(fields.into_iter().map(|(ty, _)| ty).collect());
    (ty, docs)
}

pub(crate) fn enum_unit_variant(
    doc: Vec<&str>,
    attributes: Vec<Attribute>,
    name: UstrSpan,
) -> ParsedEnumVariant {
    let docs = TypeDefVariantDocs {
        name: name.0,
        doc: parse_doc_comments(doc),
        payload: TypeDefProductDocs::Unit,
    };
    (name, (PType::Unit, name.1), attributes, docs)
}

pub(crate) fn enum_tuple_variant(
    doc: Vec<&str>,
    attributes: Vec<Attribute>,
    name: UstrSpan,
    fields: Vec<DocTypeSpan>,
    span: Location,
) -> ParsedEnumVariant {
    let (ty, payload) = type_def_tuple_product(fields);
    let docs = TypeDefVariantDocs {
        name: name.0,
        doc: parse_doc_comments(doc),
        payload,
    };
    (name, (ty, span), attributes, docs)
}

pub(crate) fn enum_record_variant(
    doc: Vec<&str>,
    attributes: Vec<Attribute>,
    name: UstrSpan,
    fields: Vec<DocRecordField>,
    span: Location,
) -> ParsedEnumVariant {
    let (ty, payload) = type_def_record_product(fields);
    let docs = TypeDefVariantDocs {
        name: name.0,
        doc: parse_doc_comments(doc),
        payload,
    };
    (name, (ty, span), attributes, docs)
}

pub(crate) fn enum_type_from_variants(
    variants: Vec<ParsedEnumVariant>,
) -> (PType, Vec<Vec<Attribute>>, TypeDefShapeDocs) {
    let mut variant_attributes = Vec::with_capacity(variants.len());
    let mut variant_docs = Vec::with_capacity(variants.len());
    let variants = variants
        .into_iter()
        .map(|(name, ty, attrs, docs)| {
            variant_attributes.push(attrs);
            variant_docs.push(docs);
            (name, ty)
        })
        .collect();
    (
        PType::Variant(variants),
        variant_attributes,
        TypeDefShapeDocs::Enum(variant_docs),
    )
}

/// Resolve token names using a static map
/// TODO: Go through intermediate data structure to allow for translation
fn resolve_token_names(names: Vec<String>) -> Vec<String> {
    static NAME_MAP: LazyLock<FxHashMap<&'static str, &'static str>> = LazyLock::new(|| {
        let mut m = FxHashMap::default();
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
    source_id: SourceId,
) -> LocatedError {
    use ParseError::*;
    match error {
        InvalidToken { location } => (
            "invalid token".to_string(),
            span(location, location + 1, source_id),
        ),
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
            span(location, location, source_id),
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
            span(token.0, token.2, source_id),
        ),
        ExtraToken { token } => (
            format!("unexpected \"{}\"", token.1),
            span(token.0, token.2, source_id),
        ),
        User { error } => error,
    }
}

pub(crate) static EMPTY_USTR: LazyLock<Ustr> = LazyLock::new(|| ustr(""));
