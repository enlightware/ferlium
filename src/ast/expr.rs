// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use derive_new::new;
use enum_as_inner::EnumAsInner;
use std::fmt::{self, Display};

use ustr::Ustr;

use crate::{
    Location,
    compiler::error::LocatedError,
    containers::{B, b},
    format::FormatWith,
    hir::value::Value,
    module::ModuleEnv,
    parser::helpers::EMPTY_USTR,
    types::r#type::Type as IrType,
};

use super::{
    Desugared, ExprArena, ExprId, ExprVisitor, FormatWithIndent, LetPattern, PLetPattern, Parsed,
    Path, Pattern, PatternConstraintKind, Phase, UstrSpan, VisitExpr,
};

#[derive(Debug, Clone, Copy, new)]
pub struct MapLiteralEntry {
    pub key: PExprId,
    pub value: PExprId,
}

impl FormatWithIndent<Parsed> for MapLiteralEntry {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv,
        arena: &ExprArena<Parsed>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent.saturating_sub(1));
        arena[self.key].format_ind(f, env, arena, indent)?;
        writeln!(f, "{indent_str}=>")?;
        arena[self.value].format_ind(f, env, arena, indent)
    }
}

impl VisitExpr<Parsed> for MapLiteralEntry {
    fn visit<V: ExprVisitor<Parsed>>(&self, visitor: &mut V, arena: &ExprArena<Parsed>) {
        arena[self.key].visit(visitor, arena);
        arena[self.value].visit(visitor, arena);
    }
}

/// The data of a for loop
#[derive(Clone, Debug)]
pub struct ForLoopData {
    pub pattern: PLetPattern,
    pub iterator: PExprId,
    pub body: PExprId,
}

impl ForLoopData {
    pub fn new(pattern: PLetPattern, iterator: PExprId, body: PExprId) -> Self {
        Self {
            pattern,
            iterator,
            body,
        }
    }
}

impl FormatWithIndent<Parsed> for B<ForLoopData> {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv,
        arena: &PExprArena,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{indent_str}for {} in", self.pattern)?;
        arena[self.iterator].format_ind(f, env, arena, indent + 1)?;
        writeln!(f, "{indent_str}do")?;
        arena[self.body].format_ind(f, env, arena, indent + 1)
    }
}

impl VisitExpr<Parsed> for B<ForLoopData> {
    fn visit<V: ExprVisitor<Parsed>>(&self, visitor: &mut V, arena: &PExprArena) {
        arena[self.iterator].visit(visitor, arena);
        arena[self.body].visit(visitor, arena);
    }
}
pub type RecordField<P> = (UstrSpan, ExprId<P>);

/// A collection of record fields in an expression
pub type RecordFields<P> = Vec<RecordField<P>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnnamedArg {
    All,
    None,
    First,
}
impl UnnamedArg {
    pub fn filter_args(&self, args: &[Ustr]) -> Vec<Ustr> {
        use UnnamedArg::*;
        match self {
            All => args.iter().map(|_| *EMPTY_USTR).collect(),
            None => args.to_vec(),
            First => args
                .iter()
                .enumerate()
                .map(|(i, name)| if i == 0 { *EMPTY_USTR } else { *name })
                .collect(),
        }
    }
}

/// Data for the [`ExprKind::Let`] variant: variable binding
#[derive(Debug, Clone)]
pub struct LetData<P: Phase> {
    pub pattern: LetPattern<P>,
    pub expr: ExprId<P>,
    pub ty_ascription: Option<(Location, P::LetTyAscriptionComplete)>,
}

/// Data for the [`ExprKind::Abstract`] variant: anonymous function
#[derive(Debug, Clone)]
pub struct AbstractData<P: Phase> {
    pub args: Vec<UstrSpan>,
    pub body: ExprId<P>,
}

/// Data for the [`ExprKind::Apply`] variant: function application
#[derive(Debug, Clone)]
pub struct ApplyData<P: Phase> {
    pub func: ExprId<P>,
    pub args: Vec<ExprId<P>>,
    pub unnamed_arg: UnnamedArg,
}

/// Data for the [`ExprKind::Assign`] variant: assignment
#[derive(Debug, Clone)]
pub struct AssignData<P: Phase> {
    pub place: ExprId<P>,
    pub sign_span: Location,
    pub value: ExprId<P>,
}

/// Data for the [`ExprKind::Project`] variant: tuple projection
#[derive(Debug, Clone)]
pub struct ProjectData<P: Phase> {
    pub expr: ExprId<P>,
    pub index: (usize, Location),
}

/// Data for the [`ExprKind::StructLiteral`] variant: struct construction
#[derive(Debug, Clone)]
pub struct StructLiteralData<P: Phase> {
    pub path: Path,
    pub fields: RecordFields<P>,
}

/// Data for the [`ExprKind::FieldAccess`] variant: record field access
#[derive(Debug, Clone)]
pub struct FieldAccessData<P: Phase> {
    pub expr: ExprId<P>,
    pub name: UstrSpan,
}

/// Data for the [`ExprKind::Index`] variant: array indexing
#[derive(Debug, Clone)]
pub struct IndexData<P: Phase> {
    pub array: ExprId<P>,
    pub index: ExprId<P>,
}

/// Data for the [`ExprKind::Match`] variant: pattern matching
#[derive(Debug, Clone)]
pub struct MatchData<P: Phase> {
    pub cond_expr: ExprId<P>,
    pub alternatives: Vec<(Pattern, ExprId<P>)>,
    pub default: Option<ExprId<P>>,
}

/// Data for the [`ExprKind::TypeAscription`] variant: type annotation
#[derive(Debug, Clone)]
pub struct TypeAscriptionData<P: Phase> {
    pub expr: ExprId<P>,
    pub ty: P::Type,
    pub span: Location,
}

/// Data for the [`ExprKind::PatternConstraint`] variant: internal pattern-induced constraint.
#[derive(Debug, Clone, new)]
pub struct PatternConstraintData {
    pub expr: ExprId<Desugared>,
    pub constraint: PatternConstraintKind,
    pub span: Location,
}

impl Display for PatternConstraintData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.constraint, f)
    }
}

impl FormatWithIndent<Desugared> for PatternConstraintData {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv,
        arena: &ExprArena<Desugared>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{indent_str}pattern constraint {}", self.constraint)?;
        arena[self.expr].format_ind(f, env, arena, indent + 1)
    }
}

impl VisitExpr<Desugared> for PatternConstraintData {
    fn visit<V: ExprVisitor<Desugared>>(&self, visitor: &mut V, arena: &ExprArena<Desugared>) {
        arena[self.expr].visit(visitor, arena);
    }
}

/// Data for the [`ExprKind::PropertyPath`] variant: scoped property path
#[derive(Debug, Clone)]
pub struct PropertyPathData {
    pub path: Path,
    pub name: Ustr,
}

/// The kind-specific part of an expression as an Abstract Syntax Tree.
#[derive(Debug, Clone, EnumAsInner)]
pub enum ExprKind<P: Phase> {
    Literal(Value, IrType),
    FormattedString(P::FormattedString),
    /// A variable, or a function from the module environment, or a null-ary variant constructor
    Identifier(Path),
    Let(B<LetData<P>>),
    Return(ExprId<P>),
    Abstract(B<AbstractData<P>>),
    Apply(B<ApplyData<P>>),
    Block(Vec<ExprId<P>>),
    Assign(B<AssignData<P>>),
    PropertyPath(B<PropertyPathData>),
    Tuple(Vec<ExprId<P>>),
    Project(B<ProjectData<P>>),
    Record(RecordFields<P>),
    StructLiteral(B<StructLiteralData<P>>),
    FieldAccess(B<FieldAccessData<P>>),
    Array(Vec<ExprId<P>>),
    SetLiteral(Vec<P::SetLiteralElement>),
    MapLiteral(Vec<P::MapLiteralEntry>),
    Index(IndexData<P>),
    EffectsUnsafe(ExprId<P>),
    Match(B<MatchData<P>>),
    ForLoop(P::ForLoop),
    Loop(ExprId<P>),
    SoftBreak,
    PatternConstraint(P::PatternConstraint),
    TypeAscription(B<TypeAscriptionData<P>>),
    Error,
}

impl<P: Phase> ExprKind<P> {
    /// Construct a [`Literal`](ExprKind::Literal) expression.
    pub fn literal(value: Value, ty: IrType) -> Self {
        ExprKind::Literal(value, ty)
    }

    /// Construct a [`FormattedString`](ExprKind::FormattedString) expression.
    pub fn formatted_string(s: P::FormattedString) -> Self {
        ExprKind::FormattedString(s)
    }

    /// Construct an [`Identifier`](ExprKind::Identifier) expression.
    pub fn identifier(path: Path) -> Self {
        ExprKind::Identifier(path)
    }

    /// Construct a [`Let`](ExprKind::Let) expression.
    pub fn let_(
        pattern: LetPattern<P>,
        expr: ExprId<P>,
        ty_ascription: Option<(Location, P::LetTyAscriptionComplete)>,
    ) -> Self {
        ExprKind::Let(b(LetData {
            pattern,
            expr,
            ty_ascription,
        }))
    }

    /// Construct a [`Return`](ExprKind::Return) expression.
    pub fn return_(expr: ExprId<P>) -> Self {
        ExprKind::Return(expr)
    }

    /// Construct an [`Abstract`](ExprKind::Abstract) expression (anonymous function / lambda).
    pub fn abstract_(args: Vec<UstrSpan>, body: ExprId<P>) -> Self {
        ExprKind::Abstract(b(AbstractData { args, body }))
    }

    /// Construct an [`Apply`](ExprKind::Apply) expression (function application).
    pub fn apply(func: ExprId<P>, args: Vec<ExprId<P>>, unnamed_arg: UnnamedArg) -> Self {
        ExprKind::Apply(b(ApplyData {
            func,
            args,
            unnamed_arg,
        }))
    }

    /// Construct a [`Block`](ExprKind::Block) expression.
    pub fn block(stmts: Vec<ExprId<P>>) -> Self {
        ExprKind::Block(stmts)
    }

    /// Construct an [`Assign`](ExprKind::Assign) expression.
    pub fn assign(place: ExprId<P>, sign_span: Location, value: ExprId<P>) -> Self {
        ExprKind::Assign(b(AssignData {
            place,
            sign_span,
            value,
        }))
    }

    /// Construct a [`PropertyPath`](ExprKind::PropertyPath) expression.
    pub fn property_path(path: Path, name: Ustr) -> Self {
        ExprKind::PropertyPath(b(PropertyPathData { path, name }))
    }

    /// Construct a [`Tuple`](ExprKind::Tuple) expression.
    pub fn tuple(elements: Vec<ExprId<P>>) -> Self {
        ExprKind::Tuple(elements)
    }

    /// Construct a [`Project`](ExprKind::Project) expression (tuple element projection).
    pub fn project(expr: ExprId<P>, index: (usize, Location)) -> Self {
        ExprKind::Project(b(ProjectData { expr, index }))
    }

    /// Construct a [`Record`](ExprKind::Record) expression.
    pub fn record(fields: RecordFields<P>) -> Self {
        ExprKind::Record(fields)
    }

    /// Construct a [`StructLiteral`](ExprKind::StructLiteral) expression.
    pub fn struct_literal(path: Path, fields: RecordFields<P>) -> Self {
        ExprKind::StructLiteral(b(StructLiteralData { path, fields }))
    }

    /// Construct a [`FieldAccess`](ExprKind::FieldAccess) expression.
    pub fn field_access(expr: ExprId<P>, name: UstrSpan) -> Self {
        ExprKind::FieldAccess(b(FieldAccessData { expr, name }))
    }

    /// Construct an [`Array`](ExprKind::Array) expression.
    pub fn array(elements: Vec<ExprId<P>>) -> Self {
        ExprKind::Array(elements)
    }

    /// Construct a set literal expression.
    pub fn set_literal(elements: Vec<P::SetLiteralElement>) -> Self {
        ExprKind::SetLiteral(elements)
    }

    /// Construct a map literal expression.
    pub fn map_literal(entries: Vec<P::MapLiteralEntry>) -> Self {
        ExprKind::MapLiteral(entries)
    }

    /// Construct an [`Index`](ExprKind::Index) expression (array indexing).
    pub fn index(array: ExprId<P>, index: ExprId<P>) -> Self {
        ExprKind::Index(IndexData { array, index })
    }

    /// Construct an [`EffectsUnsafe`](ExprKind::EffectsUnsafe) expression.
    pub fn effects_unsafe(expr: ExprId<P>) -> Self {
        ExprKind::EffectsUnsafe(expr)
    }

    /// Construct a [`Match`](ExprKind::Match) expression.
    pub fn match_(
        expr: ExprId<P>,
        alternatives: Vec<(Pattern, ExprId<P>)>,
        default: Option<ExprId<P>>,
    ) -> Self {
        ExprKind::Match(b(MatchData {
            cond_expr: expr,
            alternatives,
            default,
        }))
    }

    /// Construct a [`ForLoop`](ExprKind::ForLoop) expression.
    pub fn for_loop(for_loop: P::ForLoop) -> Self {
        ExprKind::ForLoop(for_loop)
    }

    /// Construct a [`Loop`](ExprKind::Loop) expression.
    pub fn loop_(body: ExprId<P>) -> Self {
        ExprKind::Loop(body)
    }

    /// Construct a [`SoftBreak`](ExprKind::SoftBreak) expression.
    pub fn soft_break() -> Self {
        ExprKind::SoftBreak
    }

    /// Construct a [`TypeAscription`](ExprKind::TypeAscription) expression.
    pub fn type_ascription(expr: ExprId<P>, ty: P::Type, span: Location) -> Self {
        ExprKind::TypeAscription(b(TypeAscriptionData { expr, ty, span }))
    }

    /// Construct an [`Error`](ExprKind::Error) expression.
    pub fn error() -> Self {
        ExprKind::Error
    }
}

impl<P: Phase> Expr<P> {
    pub fn single_identifier(name: Ustr, span: Location) -> Self {
        Expr::new(ExprKind::Identifier(Path::single(name, span)), span)
    }
}

/// An expression as an Abstract Syntax Tree
#[derive(Debug, Clone, new)]
pub struct Expr<P: Phase> {
    pub kind: ExprKind<P>,
    pub span: Location,
}

impl<P: Phase> Expr<P> {}

impl<P: Phase> FormatWithIndent<P> for Expr<P> {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
        arena: &ExprArena<P>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        use ExprKind::*;
        match &self.kind {
            Literal(value, ty) => writeln!(f, "{indent_str}{}", value.display_pretty(ty)),
            FormattedString(string) => writeln!(f, "{indent_str}f\"{string}\""),
            Identifier(path) => writeln!(f, "{indent_str}{path}"),
            Let(data) => {
                writeln!(f, "{indent_str}let {} =", data.pattern)?;
                arena[data.expr].format_ind(f, env, arena, indent + 1)
            }
            Return(expr) => {
                writeln!(f, "{indent_str}return")?;
                arena[*expr].format_ind(f, env, arena, indent + 1)
            }
            Abstract(data) => {
                write!(f, "{indent_str}|")?;
                for (arg, _) in &data.args {
                    write!(f, "{arg}, ")?;
                }
                writeln!(f, "|")?;
                arena[data.body].format_ind(f, env, arena, indent + 1)
            }
            Apply(data) => {
                writeln!(f, "{indent_str}eval")?;
                arena[data.func].format_ind(f, env, arena, indent + 1)?;
                if data.args.is_empty() {
                    writeln!(f, "{indent_str}and apply to ()")
                } else {
                    writeln!(f, "{indent_str}and apply to (")?;
                    for &arg in &data.args {
                        arena[arg].format_ind(f, env, arena, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")
                }
            }
            Block(exprs) => {
                for &expr in exprs.iter() {
                    arena[expr].format_ind(f, env, arena, indent)?;
                }
                Ok(())
            }
            Assign(data) => {
                writeln!(f, "{indent_str}assign")?;
                arena[data.place].format_ind(f, env, arena, indent + 1)?;
                arena[data.value].format_ind(f, env, arena, indent + 1)
            }
            Tuple(args) => {
                writeln!(f, "{indent_str}(")?;
                for &arg in args.iter() {
                    arena[arg].format_ind(f, env, arena, indent + 1)?;
                }
                writeln!(f, "{indent_str})")
            }
            Project(data) => {
                arena[data.expr].format_ind(f, env, arena, indent)?;
                writeln!(f, "{indent_str}  .{}", data.index.0)
            }
            StructLiteral(data) => {
                writeln!(f, "{indent_str}{} {{", data.path)?;
                for ((name, _), value) in data.fields.iter() {
                    writeln!(f, "{indent_str}  {name}:")?;
                    arena[*value].format_ind(f, env, arena, indent + 2)?;
                    writeln!(f, "{indent_str}  ,")?;
                }
                writeln!(f, "{indent_str}}}")
            }
            Record(fields) => {
                writeln!(f, "{indent_str}{{")?;
                for ((name, _), value) in fields.iter() {
                    writeln!(f, "{indent_str}  {name}:")?;
                    arena[*value].format_ind(f, env, arena, indent + 2)?;
                    writeln!(f, "{indent_str}  ,")?;
                }
                writeln!(f, "{indent_str}}}")
            }
            FieldAccess(data) => {
                arena[data.expr].format_ind(f, env, arena, indent)?;
                writeln!(f, "{indent_str}  .{}", data.name.0)
            }
            Array(args) => {
                if args.is_empty() {
                    writeln!(f, "{indent_str}[]")
                } else {
                    writeln!(f, "{indent_str}[")?;
                    for &arg in args.iter() {
                        arena[arg].format_ind(f, env, arena, indent + 1)?;
                    }
                    writeln!(f, "{indent_str}]")
                }
            }
            SetLiteral(args) => {
                writeln!(f, "{indent_str}set {{")?;
                for arg in args.iter() {
                    arg.format_ind(f, env, arena, indent + 1)?;
                }
                writeln!(f, "{indent_str}}}")
            }
            MapLiteral(entries) => {
                writeln!(f, "{indent_str}map {{")?;
                for entry in entries.iter() {
                    entry.format_ind(f, env, arena, indent + 1)?;
                }
                writeln!(f, "{indent_str}}}")
            }
            Index(data) => {
                arena[data.array].format_ind(f, env, arena, indent)?;
                writeln!(f, "{indent_str}[")?;
                arena[data.index].format_ind(f, env, arena, indent + 1)?;
                writeln!(f, "{indent_str}]")
            }
            EffectsUnsafe(expr) => {
                writeln!(f, "{indent_str}effects_unsafe")?;
                arena[*expr].format_ind(f, env, arena, indent + 1)
            }
            Match(data) => {
                writeln!(f, "{indent_str}match")?;
                arena[data.cond_expr].format_ind(f, env, arena, indent + 1)?;
                for (value, case) in data.alternatives.iter() {
                    writeln!(f, "{indent_str}case")?;
                    value.format_ind(f, indent + 1)?;
                    writeln!(f, "{indent_str}=>")?;
                    arena[*case].format_ind(f, env, arena, indent + 1)?;
                }
                if let Some(default) = data.default {
                    writeln!(f, "{indent_str}case _ =>")?;
                    arena[default].format_ind(f, env, arena, indent + 1)?;
                }
                Ok(())
            }
            ForLoop(for_loop) => for_loop.format_ind(f, env, arena, indent),
            Loop(body) => {
                writeln!(f, "{indent_str}loop")?;
                arena[*body].format_ind(f, env, arena, indent + 1)
            }
            SoftBreak => writeln!(f, "{indent_str}SoftBreak"),
            PropertyPath(data) => writeln!(f, "{indent_str}@{}.{}", data.path, data.name),
            PatternConstraint(data) => data.format_ind(f, env, arena, indent),
            TypeAscription(data) => {
                arena[data.expr].format_ind(f, env, arena, indent)?;
                writeln!(f, "{indent_str}: {}", data.ty.format_with(env))
            }
            Error => writeln!(f, "{indent_str}Error"),
        }
    }
}

impl<P: Phase> VisitExpr<P> for Expr<P> {
    /// Visit all nodes of the expression tree
    fn visit<V: ExprVisitor<P>>(&self, visitor: &mut V, arena: &ExprArena<P>) {
        visitor.visit_start(self);
        use ExprKind::*;
        match &self.kind {
            Let(data) => arena[data.expr].visit(visitor, arena),
            Abstract(data) => arena[data.body].visit(visitor, arena),
            Apply(data) => {
                arena[data.func].visit(visitor, arena);
                visitor.visit_exprs(data.args.iter().copied(), arena);
            }
            Block(exprs) => visitor.visit_exprs(exprs.iter().copied(), arena),
            Assign(data) => {
                arena[data.place].visit(visitor, arena);
                arena[data.value].visit(visitor, arena);
            }
            Tuple(args) => visitor.visit_exprs(args.iter().copied(), arena),
            Project(data) => arena[data.expr].visit(visitor, arena),
            StructLiteral(data) => {
                visitor.visit_exprs(data.fields.iter().map(|(_, expr)| *expr), arena)
            }
            Record(fields) => visitor.visit_exprs(fields.iter().map(|(_, id)| *id), arena),
            FieldAccess(data) => arena[data.expr].visit(visitor, arena),
            Array(args) => visitor.visit_exprs(args.iter().copied(), arena),
            SetLiteral(args) => {
                for arg in args {
                    arg.visit(visitor, arena);
                }
            }
            MapLiteral(entries) => {
                for entry in entries {
                    entry.visit(visitor, arena);
                }
            }
            Index(data) => {
                arena[data.array].visit(visitor, arena);
                arena[data.index].visit(visitor, arena);
            }
            EffectsUnsafe(expr) => arena[*expr].visit(visitor, arena),
            Match(data) => {
                arena[data.cond_expr].visit(visitor, arena);
                visitor.visit_exprs(data.alternatives.iter().map(|(_, expr)| *expr), arena);
                if let Some(default) = data.default {
                    arena[default].visit(visitor, arena);
                }
            }
            ForLoop(for_loop) => for_loop.visit(visitor, arena),
            Return(expr) => arena[*expr].visit(visitor, arena),
            Loop(body) => arena[*body].visit(visitor, arena),
            PatternConstraint(data) => data.visit(visitor, arena),
            TypeAscription(data) => arena[data.expr].visit(visitor, arena),
            _ => {}
        }
        visitor.visit_end(self);
    }
}

/// A wrapper for displaying an expression with its expression arena
#[derive(new)]
pub struct ExprDisplay<'a, P: Phase> {
    pub id: ExprId<P>,
    pub arena: &'a ExprArena<P>,
}

impl<'a, P: Phase> FormatWith<ModuleEnv<'_>> for ExprDisplay<'a, P> {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
        self.arena[self.id].format_ind(f, env, self.arena, 0)
    }
}

/// An AST expression kind just after parsing
pub type PExprKind = ExprKind<Parsed>;

/// An AST expression just after parsing
pub type PExpr = Expr<Parsed>;

/// An AST node id just after parsing
pub type PExprId = ExprId<Parsed>;

/// An AST arena just after parsing
pub type PExprArena = ExprArena<Parsed>;

/// An AST expression kind after desugaring
pub type DExprKind = ExprKind<Desugared>;

/// An AST expression after desugaring
pub type DExpr = Expr<Desugared>;

/// An AST node id after desugaring
pub type DExprId = ExprId<Desugared>;

/// An AST arena after desugaring
pub type DExprArena = ExprArena<Desugared>;

#[derive(Default)]
pub(super) struct ErrorCollector(pub(super) Vec<LocatedError>);
impl<P: Phase> ExprVisitor<P> for ErrorCollector {
    fn visit_start(&mut self, expr: &Expr<P>) {
        if let ExprKind::Error = expr.kind {
            self.0.push(("parse error".into(), expr.span));
        }
    }
}

#[derive(Default)]
pub(crate) struct UnstableCollector(pub(crate) Vec<Location>);
impl<P: Phase> ExprVisitor<P> for UnstableCollector {
    fn visit_start(&mut self, expr: &Expr<P>) {
        use ExprKind::*;
        match expr.kind {
            SoftBreak | Loop(_) => self.0.push(expr.span),
            _ => {}
        }
    }
}
