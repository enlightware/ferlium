// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use std::fmt::{Debug, Display};

use ustr::Ustr;

use crate::{
    containers::{b, B},
    error::LocatedError,
    format::write_with_separator,
    module::FmtWithModuleEnv,
    mutability::{MutType, MutVal},
    never::Never,
    r#type::Type,
    value::{LiteralValue, Value},
    Location,
};

/// A spanned Ustr
pub type UstrSpan = (Ustr, Location);

/// A spanned Type
pub type TypeSpan = (Type, Location);

/// A spanned (MutType, Type)
pub type MutTypeTypeSpan = (MutType, Type, Location);

/// A phase in the AST processing pipeline
pub trait Phase: Sized {
    type FormattedString: Debug + Clone + Display;
    type ForLoop: Debug + Clone + FormatWithIndent + VisitExpr<Self>;
}

/// The AST after parsing
#[derive(Default, Clone, Debug)]
pub struct Parsed;

/// The AST after desugaring
#[derive(Default, Clone, Debug)]
pub struct Desugared;

impl Phase for Parsed {
    type FormattedString = String;
    type ForLoop = ForLoop;
}

impl Phase for Desugared {
    type FormattedString = Never;
    type ForLoop = Never;
}

/// Trait for formatting with a module environment
pub trait FormatWithIndent {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv,
        indent: usize,
    ) -> std::fmt::Result;
}

impl FormatWithIndent for Never {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &crate::module::ModuleEnv,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        write!(f, "{indent_str}{self}")
    }
}

/// Trait for visiting expressions
pub trait VisitExpr<P: Phase> {
    fn visit<V: ExprVisitor<P>>(&self, visitor: &mut V);

    fn visit_with<V: ExprVisitor<P>>(&self, mut visitor: V) -> V {
        self.visit(&mut visitor);
        visitor
    }
}

impl<P: Phase> VisitExpr<P> for Never {
    fn visit<V: ExprVisitor<P>>(&self, _visitor: &mut V) {}
}

/// The data of a for loop
#[derive(Clone, Debug)]
pub struct ForLoop {
    pub var_name: UstrSpan,
    pub iterator: B<Expr<Parsed>>,
    pub body: B<Expr<Parsed>>,
}

impl ForLoop {
    pub fn new(var_name: UstrSpan, iterator: Expr<Parsed>, body: Expr<Parsed>) -> Self {
        Self {
            var_name,
            iterator: b(iterator),
            body: b(body),
        }
    }
}

impl FormatWithIndent for ForLoop {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        writeln!(f, "{indent_str}for {} in", self.var_name.0)?;
        self.iterator.format_ind(f, env, indent + 1)?;
        writeln!(f, "{indent_str}do")?;
        self.body.format_ind(f, env, indent + 1)
    }
}

impl VisitExpr<Parsed> for ForLoop {
    fn visit<V: ExprVisitor<Parsed>>(&self, visitor: &mut V) {
        self.iterator.visit(visitor);
        self.body.visit(visitor);
    }
}

pub type ModuleFunctionArg = (UstrSpan, Option<MutTypeTypeSpan>);

#[derive(Debug, Clone)]
pub struct ModuleFunction<P: Phase> {
    pub name: UstrSpan,
    pub args: Vec<ModuleFunctionArg>,
    pub args_span: Location,
    pub ret_ty: Option<TypeSpan>,
    pub body: B<Expr<P>>,
    pub span: Location,
    pub doc: Option<String>,
}
impl<P: Phase> ModuleFunction<P> {
    pub fn new(
        name: UstrSpan,
        args: Vec<ModuleFunctionArg>,
        args_span: Location,
        ret_ty: Option<TypeSpan>,
        body: Expr<P>,
        span: Location,
        doc: Option<String>,
    ) -> Self {
        Self {
            name,
            args,
            args_span,
            ret_ty,
            body: b(body),
            span,
            doc,
        }
    }
}

/// An AST module function just after parsing
pub type PModuleFunction = ModuleFunction<Parsed>;

/// An AST module function after desugaring
pub type DModuleFunction = ModuleFunction<Desugared>;

/// A trait implementation
#[derive(Debug, Clone)]
pub struct TraitImpl<P: Phase> {
    pub trait_name: UstrSpan,
    pub functions: Vec<ModuleFunction<P>>,
    pub span: Location,
}

/// An AST trait implementation just after parsing
pub type PTraitImpl = TraitImpl<Parsed>;

/// An AST trait implementation after desugaring
pub type DTraitImpl = TraitImpl<Desugared>;

// A module is a collection of functions and types, and is the top-level structure of the AST
#[derive(Debug, Clone, Default)]
pub struct Module<P: Phase> {
    pub functions: Vec<ModuleFunction<P>>,
    pub impls: Vec<TraitImpl<P>>,
    pub types: Vec<(Ustr, Type)>,
}
impl<P: Phase> Module<P> {
    pub fn extend(&mut self, other: Self) {
        self.functions.extend(other.functions);
        self.impls.extend(other.impls);
        self.types.extend(other.types);
    }

    pub fn merge(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }

    pub fn errors(&self) -> Vec<LocatedError> {
        self.visit_with(ErrorCollector::default()).0
    }

    pub fn is_empty(&self) -> bool {
        self.functions.is_empty() && self.impls.is_empty() && self.types.is_empty()
    }
}

impl<P: Phase> VisitExpr<P> for Module<P> {
    fn visit<V: ExprVisitor<P>>(&self, visitor: &mut V) {
        for ModuleFunction { body, .. } in self.functions.iter() {
            body.visit(visitor);
        }
        for imp in self.impls.iter() {
            for ModuleFunction { body, .. } in imp.functions.iter() {
                body.visit(visitor);
            }
        }
    }
}

impl<P: Phase> FmtWithModuleEnv for Module<P> {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv,
    ) -> std::fmt::Result {
        if !self.types.is_empty() {
            writeln!(f, "Types:")?;
            for (name, ty) in self.types.iter() {
                writeln!(f, "  {}: {}", name, ty.format_with(env))?;
            }
        }
        if !self.impls.is_empty() {
            writeln!(f, "Trait implementations:")?;
            for TraitImpl {
                trait_name,
                functions,
                ..
            } in self.impls.iter()
            {
                writeln!(f, "  impl {} {{", trait_name.0)?;
                for ModuleFunction {
                    name,
                    args,
                    ret_ty,
                    body,
                    doc,
                    ..
                } in functions.iter()
                {
                    if let Some(doc) = doc {
                        writeln!(f, "    /// {}", doc)?;
                    }
                    write!(
                        f,
                        "    fn {}({})",
                        name.0,
                        args.iter()
                            .map(|((name, _), ty)| if let Some((mut_ty, ty, _)) = ty {
                                format!(
                                    "{}: {}{}",
                                    name,
                                    if mut_ty.is_mutable() { "&mut " } else { "" },
                                    ty.format_with(env)
                                )
                            } else {
                                name.to_string()
                            })
                            .join(", ")
                    )?;
                    if let Some((ret_ty, _)) = ret_ty {
                        write!(f, " → {}", ret_ty.format_with(env))?;
                    }
                    writeln!(f)?;
                    body.format_ind(f, env, 3)?;
                }
                writeln!(f, "  }}")?;
            }
        }
        if !self.functions.is_empty() {
            writeln!(f, "Functions:")?;
            for ModuleFunction {
                name,
                args,
                ret_ty,
                body,
                doc,
                ..
            } in self.functions.iter()
            {
                if let Some(doc) = doc {
                    writeln!(f, "  /// {}", doc)?;
                }
                write!(
                    f,
                    "  fn {}({})",
                    name.0,
                    args.iter()
                        .map(|((name, _), ty)| if let Some((mut_ty, ty, _)) = ty {
                            format!(
                                "{}: {}{}",
                                name,
                                if mut_ty.is_mutable() { "&mut " } else { "" },
                                ty.format_with(env)
                            )
                        } else {
                            name.to_string()
                        })
                        .join(", ")
                )?;
                if let Some((ret_ty, _)) = ret_ty {
                    write!(f, " → {}", ret_ty.format_with(env))?;
                }
                writeln!(f)?;
                body.format_ind(f, env, 2)?;
            }
        }
        Ok(())
    }
}

/// An AST module just after parsing
pub type PModule = Module<Parsed>;

/// An AST module after desugaring
pub type DModule = Module<Desugared>;

/// The kind-specific part of an expression as an Abstract Syntax Tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum ExprKind<P: Phase> {
    Literal(Value, Type),
    FormattedString(P::FormattedString),
    /// A variable, or a function from the module environment, or a null-ary variant constructor
    Identifier(Ustr),
    Let(UstrSpan, MutVal, B<Expr<P>>, Option<(Location, bool)>),
    Abstract(Vec<UstrSpan>, B<Expr<P>>),
    Apply(B<Expr<P>>, Vec<Expr<P>>, bool),
    Block(Vec<Expr<P>>),
    Assign(B<Expr<P>>, Location, B<Expr<P>>),
    PropertyPath(Ustr, Ustr),
    Tuple(Vec<Expr<P>>),
    Project(B<Expr<P>>, (usize, Location)),
    Record(Vec<(UstrSpan, Expr<P>)>),
    FieldAccess(B<Expr<P>>, UstrSpan),
    Array(Vec<Expr<P>>),
    Index(B<Expr<P>>, B<Expr<P>>),
    Match(B<Expr<P>>, Vec<(Pattern, Expr<P>)>, Option<B<Expr<P>>>),
    ForLoop(P::ForLoop),
    Loop(B<Expr<P>>),
    SoftBreak,
    TypeAscription(B<Expr<P>>, Type, Location),
    Error,
}

/// An expression as an Abstract Syntax Tree
#[derive(Debug, Clone)]
pub struct Expr<P: Phase> {
    pub kind: ExprKind<P>,
    pub span: Location,
}
impl<P: Phase> Expr<P> {
    pub fn new(kind: ExprKind<P>, span: Location) -> Self {
        Self { kind, span }
    }
}

impl<P: Phase> FormatWithIndent for Expr<P> {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        use ExprKind::*;
        match &self.kind {
            Literal(value, _) => writeln!(f, "{indent_str}{value}"),
            FormattedString(string) => writeln!(f, "{indent_str}f\"{string}\""),
            Identifier(name) => writeln!(f, "{indent_str}{name} (local)"),
            Let((name, _), mutable, expr, _) => {
                let kw = mutable.var_def_string();
                writeln!(f, "{indent_str}{kw} {name} =")?;
                expr.format_ind(f, env, indent + 1)
            }
            Abstract(args, body) => {
                write!(f, "{indent_str}|")?;
                for (arg, _) in args {
                    write!(f, "{arg}, ")?;
                }
                writeln!(f, "|")?;
                body.format_ind(f, env, indent + 1)
            }
            Apply(func, args, _) => {
                writeln!(f, "{indent_str}eval")?;
                func.format_ind(f, env, indent + 1)?;
                if args.is_empty() {
                    writeln!(f, "{indent_str}and apply to ()")
                } else {
                    writeln!(f, "{indent_str}and apply to (")?;
                    for arg in args {
                        arg.format_ind(f, env, indent + 1)?;
                    }
                    writeln!(f, "{indent_str})")
                }
            }
            Block(exprs) => {
                for expr in exprs.iter() {
                    expr.format_ind(f, env, indent)?;
                }
                Ok(())
            }
            Assign(place, _, value) => {
                writeln!(f, "{indent_str}assign")?;
                place.format_ind(f, env, indent + 1)?;
                value.format_ind(f, env, indent + 1)
            }
            Tuple(args) => {
                writeln!(f, "{indent_str}(")?;
                for arg in args.iter() {
                    arg.format_ind(f, env, indent + 1)?;
                }
                writeln!(f, "{indent_str})")
            }
            Project(expr, (index, _)) => {
                expr.format_ind(f, env, indent)?;
                writeln!(f, "{indent_str}  .{index}")
            }
            Record(fields) => {
                writeln!(f, "{indent_str}{{")?;
                for ((name, _), value) in fields.iter() {
                    writeln!(f, "{indent_str}  {name}:")?;
                    value.format_ind(f, env, indent + 2)?;
                    writeln!(f, "{indent_str}  ,")?;
                }
                writeln!(f, "{indent_str}}}")
            }
            FieldAccess(expr, (field, _)) => {
                expr.format_ind(f, env, indent)?;
                writeln!(f, "{indent_str}  .{field}")
            }
            Array(args) => {
                if args.is_empty() {
                    writeln!(f, "{indent_str}[]")
                } else {
                    writeln!(f, "{indent_str}[")?;
                    for arg in args.iter() {
                        arg.format_ind(f, env, indent + 1)?;
                    }
                    writeln!(f, "{indent_str}]")
                }
            }
            Index(expr, index) => {
                expr.format_ind(f, env, indent)?;
                writeln!(f, "{indent_str}[")?;
                index.format_ind(f, env, indent + 1)?;
                writeln!(f, "{indent_str}]")
            }
            Match(expr, cases, default) => {
                writeln!(f, "{indent_str}match")?;
                expr.format_ind(f, env, indent + 1)?;
                for (value, case) in cases.iter() {
                    writeln!(f, "{indent_str}case")?;
                    value.format_ind(f, indent + 1)?;
                    writeln!(f, "{indent_str}=>")?;
                    case.format_ind(f, env, indent + 1)?;
                }
                if let Some(default) = default {
                    writeln!(f, "{indent_str}case _ =>")?;
                    default.format_ind(f, env, indent + 1)?;
                }
                Ok(())
            }
            ForLoop(for_loop) => for_loop.format_ind(f, env, indent),
            Loop(body) => {
                writeln!(f, "{indent_str}loop")?;
                body.format_ind(f, env, indent + 1)
            }
            SoftBreak => writeln!(f, "{indent_str}SoftBreak"),
            PropertyPath(scope, name) => writeln!(f, "{indent_str}@{}.{}", scope, name),
            TypeAscription(expr, ty, _span) => {
                expr.format_ind(f, env, indent)?;
                writeln!(f, "{indent_str}: {}", ty.format_with(env))
            }
            Error => writeln!(f, "{indent_str}Error"),
        }
    }
}

impl<P: Phase> VisitExpr<P> for Expr<P> {
    /// Visit all nodes of the expression tree
    fn visit<V: ExprVisitor<P>>(&self, visitor: &mut V) {
        visitor.visit_start(self);
        use ExprKind::*;
        match &self.kind {
            Let(_, _, expr, _) => expr.visit(visitor),
            Abstract(_, expr) => expr.visit(visitor),
            Apply(expr, args, _) => {
                expr.visit(visitor);
                visitor.visit_exprs(args.iter());
            }
            Block(exprs) => visitor.visit_exprs(exprs.iter()),
            Assign(place, _, value) => {
                place.visit(visitor);
                value.visit(visitor);
            }
            Tuple(args) => visitor.visit_exprs(args.iter()),
            Project(expr, _) => expr.visit(visitor),
            Record(fields) => visitor.visit_exprs(fields.iter().map(|(_, expr)| expr)),
            FieldAccess(expr, _) => expr.visit(visitor),
            Array(args) => visitor.visit_exprs(args.iter()),
            Index(expr, index) => {
                expr.visit(visitor);
                index.visit(visitor);
            }
            Match(expr, cases, default) => {
                expr.visit(visitor);
                visitor.visit_exprs(cases.iter().map(|(_, expr)| expr));
                if let Some(default) = default {
                    default.visit(visitor);
                }
            }
            ForLoop(for_loop) => for_loop.visit(visitor),
            TypeAscription(expr, _, _) => expr.visit(visitor),
            _ => {}
        }
        visitor.visit_end(self);
    }

    // TODO: use the visitor to collect the dependency graph
}

impl<P: Phase> FmtWithModuleEnv for Expr<P> {
    fn fmt_with_module_env(
        &self,
        f: &mut std::fmt::Formatter,
        env: &crate::module::ModuleEnv<'_>,
    ) -> std::fmt::Result {
        self.format_ind(f, env, 0)
    }
}

/// An AST expression kind just after parsing
pub type PExprKind = ExprKind<Parsed>;

/// An AST expression just after parsing
pub type PExpr = Expr<Parsed>;

/// An AST expression kind after desugaring
pub type DExprKind = ExprKind<Desugared>;

/// An AST expression after desugaring
pub type DExpr = Expr<Desugared>;

/// A visitor pattern for expressions
pub trait ExprVisitor<P: Phase> {
    fn visit_start(&mut self, _expr: &Expr<P>) {}
    fn visit_end(&mut self, _expr: &Expr<P>) {}

    fn visit_exprs<'e>(&mut self, exprs: impl Iterator<Item = &'e Expr<P>>)
    where
        Self: Sized,
        P: 'e,
    {
        for expr in exprs {
            expr.visit(self);
        }
    }
}

#[derive(Default)]
struct ErrorCollector(Vec<LocatedError>);
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

/// The kind-specific part of an expression as an Abstract Syntax Tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum PatternKind {
    Literal(LiteralValue, Type),
    Variant { tag: UstrSpan, vars: Vec<UstrSpan> },
    Error(String),
}
impl PatternKind {
    pub fn variant(tag: UstrSpan, vars: Vec<UstrSpan>) -> Self {
        PatternKind::Variant { tag, vars }
    }

    pub fn empty_variant(tag: UstrSpan) -> Self {
        PatternKind::Variant {
            tag,
            vars: Vec::new(),
        }
    }

    pub fn r#type(&self) -> PatternType {
        use PatternKind::*;
        match self {
            Literal(_, _) => PatternType::Literal,
            Variant { .. } => PatternType::Variant,
            Error(_) => PatternType::Error,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumAsInner)]
pub enum PatternType {
    Literal,
    Variant,
    Error,
}
impl PatternType {
    pub fn name(&self) -> &'static str {
        use PatternType::*;
        match self {
            Literal => "literal",
            Variant => "variant",
            Error => "error",
        }
    }
}

/// An expression as an Abstract Syntax Tree
#[derive(Debug, Clone)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Location,
}

impl Pattern {
    pub fn new(kind: PatternKind, span: Location) -> Self {
        Self { kind, span }
    }

    pub fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        use PatternKind::*;
        match &self.kind {
            Literal(value, _) => writeln!(f, "{indent_str}{value}"),
            Variant { tag, vars, .. } => {
                write!(f, "{indent_str}{} ", tag.0)?;
                if !vars.is_empty() {
                    write!(f, "(")?;
                    write_with_separator(vars.iter().map(|(var, _)| var), ", ", f)?;
                    writeln!(f, ")")
                } else {
                    writeln!(f)
                }
            }
            Error(s) => writeln!(f, "{indent_str}Pattern error: {s}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropertyAccess {
    Get,
    Set,
}
impl PropertyAccess {
    pub fn as_prefix(&self) -> &'static str {
        use PropertyAccess::*;
        match self {
            Get => "get",
            Set => "set",
        }
    }
}
