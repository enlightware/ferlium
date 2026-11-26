// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The limit on how deeply source code nests.
//!
//! The compiler's passes recurse over expressions, patterns, types and `use` trees, so bounding
//! their nesting bounds the stack that compilation needs. Each of them nests at most
//! [`NESTING_LIMIT`] levels, a node being a level. None of these checks recurses.
//!
//! Types, patterns and `use` trees are trees of boxes, which drop recursively. So the parser checks
//! each of their nodes as it builds it, and builds none beyond the limit. Expressions are in an
//! arena, which drops flat, so they are checked once parsed.

use lalrpop_util::ParseError;

use crate::{
    Location,
    ast::{
        ExprKind, LetPatternKind, MapLiteralEntry, PExprArena, PExprId, PExprKind, PFnType,
        PLetPattern, PSubscriptType, PType, UseTree,
    },
    compiler::error::LocatedError,
    hir::value::LiteralValue,
    types::r#type::Type,
};

/// The deepest that expressions, patterns, types and `use` trees each nest, a node being a level.
pub const NESTING_LIMIT: usize = 128;

type Checked<N, L, T> = Result<N, ParseError<L, T, LocatedError>>;

fn too_deep<N, L, T>(span: Location) -> Checked<N, L, T> {
    Err(ParseError::User {
        error: too_deep_error(span),
    })
}

fn too_deep_error(span: Location) -> LocatedError {
    (
        format!("Nesting is too deep: the limit is {NESTING_LIMIT} levels"),
        span,
    )
}

/// The parser's check of a type node it has just built, whose children it has already checked.
/// The error points at the child that is at the limit.
pub(crate) fn nested_type<L, T>(ty: PType) -> Checked<PType, L, T> {
    let mut deepest = None;
    for_each_type_child(&ty, &mut |(child, span)| {
        deepest = deeper(deepest, height(child, type_children), *span);
    });
    match deepest {
        Some((height, span)) if height >= NESTING_LIMIT => too_deep(span),
        _ => Ok(ty),
    }
}

/// As [`nested_type`], for a `let` pattern.
pub(crate) fn nested_pattern<L, T>(pattern: PLetPattern) -> Checked<PLetPattern, L, T> {
    let mut deepest = None;
    pattern_children(&pattern, &mut |child| {
        deepest = deeper(deepest, height(child, pattern_children), child.span);
    });
    match deepest {
        Some((height, span)) if height >= NESTING_LIMIT => too_deep(span),
        _ => Ok(pattern),
    }
}

/// As [`nested_type`], for a tuple or record literal in a `match` pattern, spanning `span`.
pub(crate) fn nested_literal<L, T>(
    literal: (LiteralValue, Type),
    span: Location,
) -> Checked<(LiteralValue, Type), L, T> {
    if height(&literal.0, literal_children) > NESTING_LIMIT {
        too_deep(span)
    } else {
        Ok(literal)
    }
}

/// As [`nested_type`], for a group of a `use` tree, spanning `span`.
pub(crate) fn nested_use_tree<L, T>(tree: UseTree, span: Location) -> Checked<UseTree, L, T> {
    if height(&tree, use_tree_children) > NESTING_LIMIT {
        too_deep(span)
    } else {
        Ok(tree)
    }
}

/// The deeper of the deepest child so far and a child of `height` at `span`.
fn deeper(
    deepest: Option<(usize, Location)>,
    height: usize,
    span: Location,
) -> Option<(usize, Location)> {
    match deepest {
        Some((deepest_height, _)) if deepest_height >= height => deepest,
        _ => Some((height, span)),
    }
}

/// The height of a tree, walked with an explicit stack: `children` calls its argument on the
/// children of a node.
fn height<'a, N>(root: &'a N, children: fn(&'a N, &mut dyn FnMut(&'a N))) -> usize {
    let mut height = 0;
    let mut stack = vec![(root, 1)];
    while let Some((node, depth)) = stack.pop() {
        height = height.max(depth);
        children(node, &mut |child| stack.push((child, depth + 1)));
    }
    height
}

fn for_each_type_child<'a>(ty: &'a PType, f: &mut dyn FnMut(&'a (PType, Location))) {
    use PType::*;
    match ty {
        Never | Unit | Resolved(_) | Infer | Path(_) => {}
        AppliedPath { args, .. } | Tuple(args) => args.iter().for_each(f),
        Variant(fields) | Record(fields) => fields.iter().for_each(|(_, ty)| f(ty)),
        Array(element) => f(element.as_ref()),
        Function(fn_type) => {
            let PFnType { args, ret, .. } = &**fn_type;
            args.iter().for_each(|arg| f(&arg.ty));
            f(ret);
        }
        Subscript(subscript_type) => {
            let PSubscriptType { args, ret, .. } = &**subscript_type;
            args.iter().for_each(|arg| f(&arg.ty));
            f(ret);
        }
    }
}

fn type_children<'a>(ty: &'a PType, f: &mut dyn FnMut(&'a PType)) {
    for_each_type_child(ty, &mut |(child, _)| f(child));
}

fn pattern_children<'a>(pattern: &'a PLetPattern, f: &mut dyn FnMut(&'a PLetPattern)) {
    match &pattern.kind {
        LetPatternKind::Binding { .. } | LetPatternKind::Ignore => {}
        LetPatternKind::Tuple { elements, .. } => elements.iter().for_each(f),
        LetPatternKind::Record { fields, .. } => fields.iter().for_each(|field| f(&field.pattern)),
    }
}

fn literal_children<'a>(literal: &'a LiteralValue, f: &mut dyn FnMut(&'a LiteralValue)) {
    match literal {
        LiteralValue::Native(_) | LiteralValue::VariantTag(_) => {}
        LiteralValue::Tuple(values) => values.iter().for_each(f),
    }
}

fn use_tree_children<'a>(tree: &'a UseTree, f: &mut dyn FnMut(&'a UseTree)) {
    match tree {
        UseTree::Glob(..) | UseTree::Name(_) => {}
        UseTree::Group(_, trees) => trees.iter().for_each(f),
    }
}

/// Check that the expressions of `arena` nest at most [`NESTING_LIMIT`] deep. The error points at
/// the first expression beyond the limit.
pub(crate) fn check_expr_nesting(arena: &PExprArena) -> Result<(), Vec<LocatedError>> {
    // The parser allocates an expression after its children, so walking the arena backwards sees
    // each expression after all its parents, and knows its depth before passing it on.
    let index = |id: PExprId| u32::from(id.into_raw()) as usize;
    let mut depths = vec![1; arena.len()];
    for (id, expr) in arena.iter().rev() {
        let depth = depths[index(id)];
        if depth > NESTING_LIMIT {
            return Err(vec![too_deep_error(source_span(arena, id))]);
        }
        for_each_expr_child(&expr.kind, &mut |child| {
            debug_assert!(
                index(child) < index(id),
                "an expression precedes its children"
            );
            depths[index(child)] = depths[index(child)].max(depth + 1);
        });
    }
    Ok(())
}

/// The span of `id`, or, if the parser synthesized it, such as the unit value of an empty block, the
/// span of its nearest ancestor in the source.
fn source_span(arena: &PExprArena, mut id: PExprId) -> Location {
    while arena[id].span.is_synthesized() {
        let parent = arena.iter().find_map(|(parent, expr)| {
            let mut is_parent = false;
            for_each_expr_child(&expr.kind, &mut |child| is_parent |= child == id);
            is_parent.then_some(parent)
        });
        match parent {
            Some(parent) => id = parent,
            None => break,
        }
    }
    arena[id].span
}

/// Call `f` on the child expressions of an expression.
fn for_each_expr_child(kind: &PExprKind, f: &mut impl FnMut(PExprId)) {
    use ExprKind::*;
    match kind {
        Literal(..)
        | FormattedString(_)
        | Identifier(_)
        | PropertyPath(_)
        | TraitAssociatedConst(_)
        | Continue(_)
        | Error => {}
        Return(expr) | Yield(expr) | EffectsUnsafe(expr) => f(*expr),
        Let(data) => f(data.expr),
        Abstract(data) => f(data.body),
        Apply(data) => {
            f(data.func);
            data.args.iter().copied().for_each(f);
        }
        NamedSubscript(data) => {
            f(data.receiver);
            data.args.iter().copied().for_each(f);
        }
        Block(ids) | Tuple(ids) | Array(ids) | SetLiteral(ids) => ids.iter().copied().for_each(f),
        Assign(data) => {
            f(data.place);
            f(data.value);
        }
        AssignOp(data) => {
            f(data.place);
            f(data.value);
        }
        Project(data) => f(data.expr),
        Record(fields) => fields.iter().for_each(|(_, id)| f(*id)),
        StructLiteral(data) => data.fields.iter().for_each(|(_, id)| f(*id)),
        FieldAccess(data) => f(data.expr),
        MapLiteral(entries) => {
            for MapLiteralEntry { key, value } in entries {
                f(*key);
                f(*value);
            }
        }
        Index(data) => {
            f(data.array);
            f(data.index);
        }
        Match(data) => {
            f(data.cond_expr);
            data.alternatives.iter().for_each(|(_, id)| f(*id));
            data.default.into_iter().for_each(f);
        }
        ForLoop(data) => {
            f(data.iterator);
            f(data.body);
        }
        Loop(data) => f(data.body),
        Break(data) => data.value.into_iter().for_each(f),
        PatternConstraint(never) => match *never {},
        TypeAscription(data) => f(data.expr),
    }
}
