// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use derive_new::new;
use la_arena::{Arena, Idx};
use std::fmt::{self, Debug, Display};

use ustr::Ustr;

use crate::{
    Location,
    containers::B,
    format::{FormatWith, write_with_separator},
    module::ModuleEnv,
    types::mutability::{FormatInFnArg, MutType as IrMutType},
    types::never::Never,
    types::r#type::Type as IrType,
    types::type_scheme::PubTypeConstraint,
};

use super::expr::{Expr, ForLoopData, MapLiteralEntry, PatternConstraintData};
use super::module::TraitDefinition;
use super::patterns::{LetBindingPattern, LetPatternKind, TypeConstraint, TypeDef};
use super::types::{PMutType, PType, TypeAlias};

/// An index into an expression arena
pub type ExprId<P> = Idx<Expr<P>>;

/// An arena of expressions
pub type ExprArena<P> = Arena<Expr<P>>;

/// A spanned Ustr
pub type UstrSpan = (Ustr, Location);

/// A spanned path
#[derive(Debug, Clone, PartialEq, Eq, new)]

pub struct Path {
    pub segments: Vec<UstrSpan>,
}

impl Path {
    pub fn single(name: Ustr, span: Location) -> Self {
        Self {
            segments: vec![(name, span)],
        }
    }
    pub fn single_str(name: &str, span: Location) -> Self {
        Self {
            segments: vec![(Ustr::from(name), span)],
        }
    }
    pub fn single_tuple(name: UstrSpan) -> Self {
        Self {
            segments: vec![name],
        }
    }
    pub fn is_empty(&self) -> bool {
        self.segments.is_empty()
    }

    pub fn span(&self) -> Option<Location> {
        if let (Some(&(_, start)), Some(&(_, end))) = (self.segments.first(), self.segments.last())
        {
            Location::fuse([start, end])
        } else {
            None
        }
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_with_separator(self.segments.iter().map(|(s, _)| s), "::", f)
    }
}

/// A use definition tree
#[derive(Debug, Clone)]
pub enum UseTree {
    /// Use all symbols from a path, location of `*` character
    Glob(Option<Path>, Location),
    /// Use a group of use directives from a path
    Group(Option<Path>, Vec<UseTree>),
    /// Use one symbol from a path
    Name(Path),
}

/// A phase of the AST, parameterizing over the types of various components that may differ between phases.
pub trait Phase: Sized {
    type FormattedString: Debug + Clone + Display;
    type ForLoop: Debug + Clone + FormatWithIndent<Self> + VisitExpr<Self>;
    type SetLiteralElement: Debug + Clone + FormatWithIndent<Self> + VisitExpr<Self>;
    type MapLiteralEntry: Debug + Clone + FormatWithIndent<Self> + VisitExpr<Self>;
    type LetPatternContent: Debug + Clone + Display;
    type PatternConstraint: Debug + Clone + Display + FormatWithIndent<Self> + VisitExpr<Self>;
    type Type: Debug + Clone + for<'a> FormatWith<ModuleEnv<'a>>;
    type MutType: Debug + Clone + FormatInFnArg;
    type LetTyAscriptionComplete: Debug + Clone;
    type WhereClause: Debug + Clone + for<'a> FormatWith<ModuleEnv<'a>>;
    type TraitInModule: Debug + Clone;
    type TypeAliasInModule: Debug + Clone + for<'a> FormatWith<ModuleEnv<'a>>;
    type TypeDefInModule: Debug + Clone;
}

/// The AST after parsing
#[derive(Default, Clone, Debug)]
pub struct Parsed;

/// The AST after type name resolution and desugaring
#[derive(Default, Clone, Debug)]
pub struct Desugared;

/// The state of the AST just after parsing, before any transformations
impl Phase for Parsed {
    type FormattedString = String;
    type ForLoop = B<ForLoopData>;
    type SetLiteralElement = ExprId<Parsed>;
    type MapLiteralEntry = MapLiteralEntry;
    type LetPatternContent = LetPatternKind;
    type PatternConstraint = Never;
    type Type = PType;
    type MutType = PMutType;
    type LetTyAscriptionComplete = ();
    type WhereClause = TypeConstraint<Self>;
    type TraitInModule = TraitDefinition;
    type TypeAliasInModule = TypeAlias;
    type TypeDefInModule = TypeDef<Self>;
}

/// The state of the AST after type name resolution and desugaring, ready for type inference
impl Phase for Desugared {
    type FormattedString = Never;
    type ForLoop = Never;
    type SetLiteralElement = Never;
    type MapLiteralEntry = Never;
    type LetPatternContent = LetBindingPattern;
    type PatternConstraint = B<PatternConstraintData>;
    type Type = IrType;
    type MutType = IrMutType;
    type LetTyAscriptionComplete = bool;
    type WhereClause = PubTypeConstraint;
    type TraitInModule = Never;
    type TypeAliasInModule = Never;
    type TypeDefInModule = Never;
}

pub trait FormatWithIndent<P: Phase = Parsed> {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv,
        arena: &ExprArena<P>,
        indent: usize,
    ) -> std::fmt::Result;
}

impl<P: Phase> FormatWithIndent<P> for Never {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv,
        _arena: &ExprArena<P>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        write!(f, "{indent_str}{self}")
    }
}

impl<P: Phase, T: FormatWithIndent<P> + ?Sized> FormatWithIndent<P> for Box<T> {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv,
        arena: &ExprArena<P>,
        indent: usize,
    ) -> std::fmt::Result {
        (**self).format_ind(f, env, arena, indent)
    }
}

impl<P: Phase> FormatWithIndent<P> for ExprId<P> {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv,
        arena: &ExprArena<P>,
        indent: usize,
    ) -> std::fmt::Result {
        arena[*self].format_ind(f, env, arena, indent)
    }
}

/// A visitor pattern for expressions
pub trait ExprVisitor<P: Phase> {
    fn visit_start(&mut self, _expr: &Expr<P>) {}
    fn visit_end(&mut self, _expr: &Expr<P>) {}

    fn visit_exprs<'e>(&mut self, exprs: impl Iterator<Item = ExprId<P>>, arena: &ExprArena<P>)
    where
        Self: Sized,
        P: 'e,
    {
        for expr in exprs {
            arena[expr].visit(self, arena);
        }
    }
}

/// Trait for visiting expressions
pub trait VisitExpr<P: Phase> {
    fn visit<V: ExprVisitor<P>>(&self, visitor: &mut V, arena: &ExprArena<P>);

    fn visit_with<V: ExprVisitor<P>>(&self, mut visitor: V, arena: &ExprArena<P>) -> V {
        self.visit(&mut visitor, arena);
        visitor
    }
}

impl<P: Phase> VisitExpr<P> for Never {
    fn visit<V: ExprVisitor<P>>(&self, _visitor: &mut V, _arena: &ExprArena<P>) {}
}

impl<P: Phase, T: VisitExpr<P> + ?Sized> VisitExpr<P> for Box<T> {
    fn visit<V: ExprVisitor<P>>(&self, visitor: &mut V, arena: &ExprArena<P>) {
        (**self).visit(visitor, arena)
    }
}

impl<P: Phase> VisitExpr<P> for ExprId<P> {
    fn visit<V: ExprVisitor<P>>(&self, visitor: &mut V, arena: &ExprArena<P>) {
        arena[*self].visit(visitor, arena);
    }
}
