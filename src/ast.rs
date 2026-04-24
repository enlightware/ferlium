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
use itertools::Itertools;
use la_arena::{Arena, Idx};
use std::fmt::{self, Debug, Display};

use crate::{FxHashMap, FxHashSet, format::write_with_separator_and_format_fn};

use ustr::Ustr;

use crate::{
    Location,
    containers::{B, b},
    effects::PrimitiveEffect,
    error::{InternalCompilationError, LocatedError},
    format::{FormatWith, write_with_separator},
    internal_compilation_error,
    module::ModuleEnv,
    mutability::{FormatInFnArg, MutType as IrMutType, MutVal},
    never::Never,
    parser_helpers::EMPTY_USTR,
    r#type::{Type as IrType, TypeDefRef},
    type_like::TypeLike,
    type_scheme::PubTypeConstraint,
    value::{LiteralValue, Value},
};

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

/// A spanned Type
pub type TypeSpan<P> = (<P as Phase>::Type, Location);

/// A spanned type alias during parsing
#[derive(Debug, Clone, new)]
pub struct TypeAlias {
    pub name: UstrSpan,
    pub generic_params: Vec<UstrSpan>,
    pub ty: TypeSpan<Parsed>,
}
impl FormatWith<ModuleEnv<'_>> for TypeAlias {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv) -> std::fmt::Result {
        write!(f, "{}", self.name.0)?;
        if !self.generic_params.is_empty() {
            write!(f, "<")?;
            write_with_separator(self.generic_params.iter().map(|(s, _)| s), ", ", f)?;
            write!(f, ">")?;
        }
        write!(f, ": ")?;
        self.ty.0.fmt_with(f, env)
    }
}

/// A spanned Type during parsing
pub type PTypeSpan = TypeSpan<Parsed>;

/// A spanned (MutType, Type)
pub type MutTypeTypeSpan<P> = (Option<<P as Phase>::MutType>, <P as Phase>::Type, Location);

/// A spanned (MutType, Type) during parsing
pub type PMutTypeTypeSpan = MutTypeTypeSpan<Parsed>;

/// A phase in the AST processing pipeline
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

/// Types

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PMutType {
    Mut,
    Infer,
}
impl Display for PMutType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PMutType::Mut => write!(f, "mut"),
            PMutType::Infer => write!(f, "?"),
        }
    }
}
impl FormatInFnArg for PMutType {
    fn format_in_fn_arg(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "&{self} ")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, new)]
pub struct PFnArgType {
    pub ty: TypeSpan<Parsed>,
    // TODO: currently we do not support generic mutability in type annotations
    pub mut_ty: Option<PMutType>,
    pub span: Location,
}

impl FormatWith<ModuleEnv<'_>> for PFnArgType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        if let Some(mut_ty) = &self.mut_ty {
            write!(f, "&{mut_ty} ")?;
        }
        self.ty.0.fmt_with(f, env)
    }
}

/// Effect information attached to a parsed function type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PFnEffects {
    ImplicitPure,
    ImplicitGeneric,
    Explicit(Vec<PrimitiveEffect>),
}

impl PFnEffects {
    pub fn implicit(has_generic_effects: bool) -> Self {
        if has_generic_effects {
            Self::ImplicitGeneric
        } else {
            Self::ImplicitPure
        }
    }
}

/// The type of a function
#[derive(Debug, Clone, PartialEq, Eq, new)]
pub struct PFnType {
    pub args: Vec<PFnArgType>,
    pub ret: TypeSpan<Parsed>,
    pub effects: PFnEffects,
}
impl PFnType {
    /// Collect indices of types in ty_names that are referenced in this type.
    pub fn collect_refs(
        &self,
        name: Ustr,
        ty_names: &FxHashMap<Ustr, usize>,
        collected: &mut FxHashSet<usize>,
    ) -> Result<(), InternalCompilationError> {
        for arg in &self.args {
            arg.ty.0.collect_refs(name, ty_names, collected)?;
        }
        self.ret.0.collect_refs(name, ty_names, collected)
    }
}

impl FormatWith<ModuleEnv<'_>> for PFnType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            arg.fmt_with(f, env)?;
        }
        write!(f, ") -> ")?;
        self.ret.0.fmt_with(f, env)?;
        if let PFnEffects::Explicit(effects) = &self.effects {
            write!(f, " !")?;
            if !effects.is_empty() {
                write!(f, " ")?;
                write_with_separator(effects, ", ", f)?;
            }
        }
        Ok(())
    }
}

/// AST-level type representation before resolution
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum PType {
    /// A never type, i.e., a type that cannot have any values
    Never,
    /// A unit type, i.e., `()`
    Unit,
    /// A known, resolved type
    Resolved(IrType),
    /// A type that must be inferred (`_`)
    Infer,
    /// A path to a type
    Path(Path),
    /// A path applied to explicit type arguments
    AppliedPath {
        path: Path,
        args: Vec<TypeSpan<Parsed>>,
    },
    /// Tagged union sum type
    Variant(Vec<(UstrSpan, TypeSpan<Parsed>)>),
    /// Position-based product type
    Tuple(Vec<TypeSpan<Parsed>>),
    /// Named product type
    Record(Vec<(UstrSpan, TypeSpan<Parsed>)>),
    /// An array type
    Array(Box<TypeSpan<Parsed>>),
    /// Function type (args -> return)
    Function(B<PFnType>),
}
impl PType {
    pub fn function_type(fn_type: PFnType) -> Self {
        PType::Function(b(fn_type))
    }

    pub fn path_with_args(path: Path, args: Vec<TypeSpan<Parsed>>) -> Self {
        PType::AppliedPath { path, args }
    }

    /// Collect indices of types in ty_names that are referenced in this type.
    pub fn collect_refs(
        &self,
        name: Ustr,
        ty_names: &FxHashMap<Ustr, usize>,
        collected: &mut FxHashSet<usize>,
    ) -> Result<(), InternalCompilationError> {
        use PType::*;
        match self {
            #[allow(clippy::collapsible_match)]
            Path(path) => {
                if path.segments.len() == 1 {
                    let ty_name = path.segments[0].0;
                    if ty_name == name {
                        return Err(internal_compilation_error!(Unsupported {
                            reason: format!(
                                "Self-referential type paths are not supported, but `{ty_name}` refers to itself"
                            ),
                            span: path.segments[0].1,
                        }));
                    }
                    if let Some(index) = ty_names.get(&ty_name) {
                        collected.insert(*index);
                    }
                }
            }
            AppliedPath { path, args } => {
                if path.segments.len() == 1 {
                    let ty_name = path.segments[0].0;
                    if ty_name == name {
                        return Err(internal_compilation_error!(Unsupported {
                            reason: format!(
                                "Self-referential type paths are not supported, but `{ty_name}` refers to itself"
                            ),
                            span: path.segments[0].1,
                        }));
                    }
                    if let Some(index) = ty_names.get(&ty_name) {
                        collected.insert(*index);
                    }
                }
                args.iter()
                    .try_for_each(|(ty, _)| ty.collect_refs(name, ty_names, collected))?;
            }
            Variant(types) => types
                .iter()
                .try_for_each(|(_, (ty, _))| ty.collect_refs(name, ty_names, collected))?,
            Tuple(elements) => elements
                .iter()
                .try_for_each(|(ty, _)| ty.collect_refs(name, ty_names, collected))?,
            Record(fields) => fields
                .iter()
                .try_for_each(|(_, (ty, _))| ty.collect_refs(name, ty_names, collected))?,
            Array(inner) => inner.0.collect_refs(name, ty_names, collected)?,
            Function(fn_type) => fn_type.collect_refs(name, ty_names, collected)?,
            _ => (),
        }
        Ok(())
    }
}

impl FormatWith<ModuleEnv<'_>> for PType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        use PType::*;
        match self {
            Never => write!(f, "never"),
            Unit => write!(f, "()"),
            Resolved(ty) => ty.fmt_with(f, env),
            Infer => write!(f, "_"),
            Path(path) => write!(f, "{}", path.segments.iter().map(|(s, _)| s).join("::")),
            AppliedPath { path, args } => {
                write!(f, "{path}<")?;
                for (i, (ty, _)) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    ty.fmt_with(f, env)?;
                }
                write!(f, ">")
            }
            Variant(types) => {
                for (i, ((name, _), (ty, _))) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    if *ty == Unit {
                        write!(f, "{name}")?;
                    } else {
                        write!(f, "{name} ")?;
                        ty.fmt_with(f, env)?;
                    }
                }
                Ok(())
            }
            Tuple(elements) => {
                write!(f, "(")?;
                for (i, (ty, _)) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    ty.fmt_with(f, env)?;
                    if elements.len() == 1 {
                        write!(f, ",")?;
                    }
                }
                write!(f, ")")
            }
            Record(fields) => {
                write!(f, "{{ ")?;
                for (i, ((name, _), (ty, _))) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: ")?;
                    ty.fmt_with(f, env)?;
                }
                write!(f, " }}")
            }
            Array(inner) => {
                write!(f, "[")?;
                inner.0.fmt_with(f, env)?;
                write!(f, "]")
            }
            Function(fn_type) => fn_type.fmt_with(f, env),
        }
    }
}

/// Trait for formatting with a module environment and expression arena
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

#[derive(Debug, Clone)]
pub struct ModuleFunctionArg<P: Phase> {
    pub name: UstrSpan,
    pub ty: Option<MutTypeTypeSpan<P>>,
    pub mut_binding: bool,
}

pub type PModuleFunctionArg = ModuleFunctionArg<Parsed>;

pub type DModuleFunctionArg = ModuleFunctionArg<Desugared>;

impl DModuleFunctionArg {
    pub fn locations_and_ty_concreteness(&self) -> (Location, Option<(Location, bool)>) {
        (
            self.name.1,
            self.ty.map(|(mut_ty, ty, span)| {
                let mut_concrete = mut_ty.is_none_or(|m| !m.is_variable());
                let ty_concrete = ty.is_constant();
                (span, mut_concrete && ty_concrete)
            }),
        )
    }
}

#[derive(Debug, Clone, new)]
#[allow(clippy::too_many_arguments)]
pub struct ModuleFunction<P: Phase> {
    pub name: UstrSpan,
    pub generic_params: Vec<UstrSpan>,
    pub args: Vec<ModuleFunctionArg<P>>,
    pub args_span: Location,
    pub ret_ty: Option<TypeSpan<P>>,
    pub where_clause: Vec<P::WhereClause>,
    pub body: ExprId<P>,
    pub span: Location,
    pub doc: Option<String>,
}

/// An AST module function just after parsing
pub type PModuleFunction = ModuleFunction<Parsed>;

/// An AST module function after desugaring
pub type DModuleFunction = ModuleFunction<Desugared>;

#[derive(Debug, Clone)]
pub struct TraitFunctionArg {
    pub name: UstrSpan,
    pub ty: PFnArgType,
}

impl FormatWith<ModuleEnv<'_>> for TraitFunctionArg {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name.0, self.ty.format_with(env))
    }
}

#[derive(Debug, Clone)]
pub struct TraitFunction {
    pub name: UstrSpan,
    pub args: Vec<TraitFunctionArg>,
    pub ret_ty: Option<PTypeSpan>,
    pub effects: PFnEffects,
    pub span: Location,
    pub doc: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TraitDefinition {
    pub name: UstrSpan,
    pub input_type_names: Vec<UstrSpan>,
    pub output_type_names: Vec<UstrSpan>,
    pub where_clause: Vec<PTypeConstraint>,
    pub functions: Vec<TraitFunction>,
    pub span: Location,
    pub doc: Option<String>,
}

impl TraitDefinition {
    pub(crate) fn iter_input_type_names(&self) -> impl Iterator<Item = Ustr> {
        self.input_type_names.iter().map(|(s, _)| *s)
    }
    pub(crate) fn iter_output_type_names(&self) -> impl Iterator<Item = Ustr> {
        self.output_type_names.iter().map(|(s, _)| *s)
    }
}

pub type PTraitDefinition = TraitDefinition;

/// A trait implementation
#[derive(Debug, Clone)]
pub struct TraitImplFor<P: Phase> {
    pub input_types: Vec<TypeConstraintInput<P>>,
    pub output_types: Vec<TypeConstraintOutput<P>>,
    pub span: Location,
}

impl<P: Phase> FormatWith<ModuleEnv<'_>> for TraitImplFor<P> {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        if self.output_types.is_empty()
            && self.input_types.len() == 1
            && self.input_types[0].name.is_none()
        {
            return self.input_types[0].ty.0.fmt_with(f, env);
        }

        if self.output_types.is_empty() && self.input_types.iter().all(|input| input.name.is_none())
        {
            write!(f, "<")?;
            write_with_separator_and_format_fn(
                &self.input_types,
                ", ",
                |input_ty, f| input_ty.ty.0.fmt_with(f, env),
                f,
            )?;
            return write!(f, ">");
        }

        write!(f, "<")?;
        for (index, input) in self.input_types.iter().enumerate() {
            if index > 0 {
                write!(f, ", ")?;
            }
            input.fmt_with(f, env)?;
        }
        if !self.output_types.is_empty() {
            write!(f, " |-> ")?;
            write_with_separator_and_format_fn(
                &self.output_types,
                ", ",
                |output_ty, f| output_ty.ty.0.fmt_with(f, env),
                f,
            )?;
        }
        write!(f, ">")
    }
}

impl TraitImplFor<Desugared> {
    pub fn input_tys(&self) -> Vec<<Desugared as Phase>::Type> {
        self.input_types.iter().map(|input| input.ty.0).collect()
    }
    pub fn output_tys(&self) -> Vec<<Desugared as Phase>::Type> {
        self.output_types.iter().map(|output| output.ty.0).collect()
    }
}

/// An AST trait implementation header just after parsing
pub type PTraitImplFor = TraitImplFor<Parsed>;

/// An AST trait implementation header after desugaring
pub type DTraitImplFor = TraitImplFor<Desugared>;

/// A trait implementation
#[derive(Debug, Clone)]
pub struct TraitImpl<P: Phase> {
    pub generic_params: Vec<UstrSpan>,
    pub trait_name: UstrSpan,
    /// Explicit trait inputs and outputs for the implementation header, if any.
    /// When `None`, they are fully inferred from the function signatures.
    pub for_trait: Option<TraitImplFor<P>>,
    pub where_clause: Vec<P::WhereClause>,
    pub functions: Vec<ModuleFunction<P>>,
    pub span: Location,
}

/// An AST trait implementation just after parsing
pub type PTraitImpl = TraitImpl<Parsed>;

/// An AST trait implementation after desugaring
pub type DTraitImpl = TraitImpl<Desugared>;

// A module is a collection of functions and types, and is the top-level structure of the AST
#[derive(Debug, Clone)]
pub struct Module<P: Phase> {
    pub traits: Vec<P::TraitInModule>,
    pub functions: Vec<ModuleFunction<P>>,
    pub impls: Vec<TraitImpl<P>>,
    pub type_aliases: Vec<P::TypeAliasInModule>,
    pub type_defs: Vec<P::TypeDefInModule>,
    pub uses: Vec<UseTree>,
}
impl<P: Phase> Module<P> {
    pub fn single_trait(trait_def: P::TraitInModule) -> Self {
        Self {
            traits: vec![trait_def],
            ..Self::default()
        }
    }
    pub fn single_function(function: ModuleFunction<P>) -> Self {
        Self {
            functions: vec![function],
            ..Self::default()
        }
    }
    pub fn single_impl(imp: TraitImpl<P>) -> Self {
        Self {
            impls: vec![imp],
            ..Self::default()
        }
    }
    pub fn single_type_alias(alias: P::TypeAliasInModule) -> Self {
        Self {
            type_aliases: vec![alias],
            ..Self::default()
        }
    }
    pub fn single_type_def(def: P::TypeDefInModule) -> Self {
        Self {
            type_defs: vec![def],
            ..Self::default()
        }
    }

    pub fn uses_tree(uses: UseTree) -> Self {
        Self {
            uses: vec![uses],
            ..Self::default()
        }
    }

    pub fn extend(&mut self, other: Self) {
        self.traits.extend(other.traits);
        self.functions.extend(other.functions);
        self.impls.extend(other.impls);
        self.type_aliases.extend(other.type_aliases);
        self.type_defs.extend(other.type_defs);
        self.uses.extend(other.uses);
    }

    pub fn merge(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }

    pub fn errors(&self, arena: &ExprArena<P>) -> Vec<LocatedError> {
        self.visit_with(ErrorCollector::default(), arena).0
    }

    pub fn is_empty(&self) -> bool {
        self.traits.is_empty()
            && self.functions.is_empty()
            && self.impls.is_empty()
            && self.type_aliases.is_empty()
            && self.type_defs.is_empty()
            && self.uses.is_empty()
    }
}
impl Module<Parsed> {
    /// Returns all the names defined in this module, including traits, functions, type aliases, and type definitions.
    pub fn own_symbols(&self) -> impl Iterator<Item = UstrSpan> + '_ {
        self.traits
            .iter()
            .map(|trait_def| trait_def.name)
            .chain(self.functions.iter().map(|f| f.name))
            .chain(self.type_aliases.iter().map(|alias| alias.name))
            .chain(self.type_defs.iter().map(|def| def.name))
    }
}

impl<P: Phase> Default for Module<P> {
    fn default() -> Self {
        Self {
            traits: Vec::new(),
            functions: Vec::new(),
            impls: Vec::new(),
            type_aliases: Vec::new(),
            type_defs: Vec::new(),
            uses: Vec::new(),
        }
    }
}

impl<P: Phase> VisitExpr<P> for Module<P> {
    fn visit<V: ExprVisitor<P>>(&self, visitor: &mut V, arena: &ExprArena<P>) {
        for ModuleFunction { body, .. } in self.functions.iter() {
            arena[*body].visit(visitor, arena);
        }
        for imp in self.impls.iter() {
            for ModuleFunction { body, .. } in imp.functions.iter() {
                arena[*body].visit(visitor, arena);
            }
        }
    }
}

/// A wrapper for displaying a module with its expression arena
#[derive(new)]
pub struct ModuleDisplay<'a, P: Phase> {
    pub module: &'a Module<P>,
    pub arena: &'a ExprArena<P>,
}

fn fmt_trait_function(
    f: &mut fmt::Formatter<'_>,
    env: &ModuleEnv<'_>,
    function: &TraitFunction,
    doc_prefix: &str,
) -> fmt::Result {
    if let Some(doc) = &function.doc {
        for line in doc.split("\n") {
            writeln!(f, "{doc_prefix}/// {line}")?;
        }
    }
    write!(f, "{doc_prefix}fn {}(", function.name.0)?;
    write_with_separator_and_format_fn(&function.args, ", ", |arg, f| arg.fmt_with(f, env), f)?;
    write!(f, ")")?;
    if let Some((ret_ty, _)) = &function.ret_ty {
        write!(f, " → {}", ret_ty.format_with(env))?;
    }
    if let PFnEffects::Explicit(effects) = &function.effects {
        write!(f, " !")?;
        if !effects.is_empty() {
            write!(f, " ")?;
            write_with_separator(effects, ", ", f)?;
        }
    }
    writeln!(f, ";")
}

fn fmt_module_function<P: Phase>(
    f: &mut fmt::Formatter<'_>,
    env: &ModuleEnv<'_>,
    arena: &ExprArena<P>,
    function: &ModuleFunction<P>,
    doc_prefix: &str,
    body_indent: usize,
) -> fmt::Result {
    let ModuleFunction {
        name,
        generic_params,
        args,
        ret_ty,
        where_clause,
        body,
        doc,
        ..
    } = function;

    if let Some(doc) = doc {
        for line in doc.split("\n") {
            writeln!(f, "{doc_prefix}/// {line}")?;
        }
    }
    write!(f, "    fn {}", name.0)?;
    if !generic_params.is_empty() {
        write!(
            f,
            "<{}>",
            generic_params.iter().map(|(name, _)| name).join(", ")
        )?;
    }
    write!(f, "(")?;
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        if let Some((mut_ty, ty, _)) = &arg.ty {
            write!(f, "{}: ", arg.name.0)?;
            if let Some(mut_ty) = mut_ty {
                mut_ty.format_in_fn_arg(f)?;
            }
            write!(f, "{}", ty.format_with(env))?;
        } else {
            write!(f, "{}", arg.name.0)?;
        }
    }
    write!(f, ")")?;
    if let Some((ret_ty, _)) = ret_ty {
        write!(f, " → {}", ret_ty.format_with(env))?;
    }
    if !where_clause.is_empty() {
        write!(f, " where ")?;
        write_with_separator_and_format_fn(
            where_clause,
            ", ",
            |constraint, f| constraint.fmt_with(f, env),
            f,
        )?;
    }
    writeln!(f)?;
    arena[*body].format_ind(f, env, arena, body_indent)
}

impl<'a> FormatWith<ModuleEnv<'_>> for ModuleDisplay<'a, Parsed> {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv) -> std::fmt::Result {
        let module = self.module;
        let arena = self.arena;
        if !module.type_aliases.is_empty() {
            writeln!(f, "Types:")?;
            for alias in module.type_aliases.iter() {
                writeln!(f, "  {}", alias.format_with(env))?;
            }
        }
        if !module.traits.is_empty() {
            writeln!(f, "Traits:")?;
            for trait_def in module.traits.iter() {
                if let Some(doc) = &trait_def.doc {
                    for line in doc.split("\n") {
                        writeln!(f, "  /// {line}")?;
                    }
                }
                write!(f, "  trait {}<", trait_def.name.0)?;
                write_with_separator(trait_def.iter_input_type_names(), ", ", f)?;
                if !trait_def.output_type_names.is_empty() {
                    write!(f, " |-> ")?;
                    write_with_separator(trait_def.iter_output_type_names(), ", ", f)?;
                }
                write!(f, ">")?;
                if !trait_def.where_clause.is_empty() {
                    write!(f, " where ")?;
                    write_with_separator_and_format_fn(
                        &trait_def.where_clause,
                        ", ",
                        |constraint, f| constraint.fmt_with(f, env),
                        f,
                    )?;
                }
                writeln!(f, " {{")?;
                for function in &trait_def.functions {
                    fmt_trait_function(f, env, function, "    ")?;
                }
                writeln!(f, "  }}")?;
            }
        }
        if !module.impls.is_empty() {
            writeln!(f, "Trait implementations:")?;
            for TraitImpl {
                generic_params,
                trait_name,
                for_trait,
                where_clause,
                functions,
                ..
            } in module.impls.iter()
            {
                write!(f, "  impl")?;
                if !generic_params.is_empty() {
                    write!(
                        f,
                        "<{}>",
                        generic_params.iter().map(|(name, _)| name).join(", ")
                    )?;
                }
                write!(f, " {}", trait_name.0)?;
                if let Some(for_trait) = for_trait {
                    write!(f, " for {}", for_trait.format_with(env))?;
                } else {
                    write!(f, " ")?;
                }
                if !where_clause.is_empty() {
                    write!(f, " where ")?;
                    write_with_separator_and_format_fn(
                        where_clause,
                        ", ",
                        |constraint, f| constraint.fmt_with(f, env),
                        f,
                    )?;
                    write!(f, " ")?;
                }
                writeln!(f, "{{")?;
                for function in functions.iter() {
                    fmt_module_function(f, env, arena, function, "    ", 3)?;
                }
                writeln!(f, "  }}")?;
            }
        }
        if !module.functions.is_empty() {
            writeln!(f, "Functions:")?;
            for function in module.functions.iter() {
                fmt_module_function(f, env, arena, function, "  ", 2)?;
            }
        }
        Ok(())
    }
}

/// An AST module just after parsing
pub type PModule = Module<Parsed>;

/// An AST module after desugaring
pub type DModule = Module<Desugared>;

/// A record field in an expression
pub type RecordField<P> = (UstrSpan, ExprId<P>);

/// A collection of record fields in an expression
pub type RecordFields<P> = Vec<RecordField<P>>;

/// A single binding pattern in a desugared `let`.
#[derive(Debug, Clone, Copy, new)]
pub struct LetBindingPattern {
    pub name: UstrSpan,
    pub mut_val: MutVal,
}

impl Display for LetBindingPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.mut_val == MutVal::mutable() {
            write!(f, "mut {}", self.name.0)
        } else {
            write!(f, "{}", self.name.0)
        }
    }
}

/// An internal constraint induced by a destructuring pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternConstraintKind {
    ExactTuple(usize),
    NamedType(TypeDefRef),
}

impl Display for PatternConstraintKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternConstraintKind::ExactTuple(element_count) => {
                write!(f, "exact {element_count}-tuple")
            }
            PatternConstraintKind::NamedType(type_def) => {
                write!(f, "named type {}", type_def.name)
            }
        }
    }
}

/// A record field in a let-pattern
#[derive(Debug, Clone, new)]
pub struct LetRecordPatternField {
    pub name: UstrSpan,
    pub pattern: PLetPattern,
}

impl Display for LetRecordPatternField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let LetPatternKind::Binding { name, mut_val } = &self.pattern.kind
            && name.0 == self.name.0
            && *mut_val == MutVal::constant()
        {
            write!(f, "{}", self.name.0)
        } else {
            write!(f, "{}: {}", self.name.0, self.pattern)
        }
    }
}

/// The kind-specific part of a let-pattern.
#[derive(Debug, Clone, EnumAsInner)]
pub enum LetPatternKind {
    Binding {
        name: UstrSpan,
        mut_val: MutVal,
    },
    Ignore,
    Tuple {
        path: Option<Path>,
        elements: Vec<PLetPattern>,
        has_rest: bool,
    },
    Record {
        path: Option<Path>,
        fields: Vec<LetRecordPatternField>,
        has_rest: bool,
    },
}

impl LetPatternKind {
    pub fn binding(name: UstrSpan, mut_val: MutVal) -> Self {
        Self::Binding { name, mut_val }
    }

    pub fn tuple(path: Option<Path>, elements: Vec<PLetPattern>, has_rest: bool) -> Self {
        Self::Tuple {
            path,
            elements,
            has_rest,
        }
    }

    pub fn record(path: Option<Path>, fields: Vec<LetRecordPatternField>, has_rest: bool) -> Self {
        Self::Record {
            path,
            fields,
            has_rest,
        }
    }
}

impl Display for LetPatternKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LetPatternKind::Binding { name, mut_val } => {
                if *mut_val == MutVal::mutable() {
                    write!(f, "mut {}", name.0)
                } else {
                    write!(f, "{}", name.0)
                }
            }
            LetPatternKind::Ignore => write!(f, "_"),
            LetPatternKind::Tuple {
                path,
                elements,
                has_rest,
            } => {
                if let Some(path) = path {
                    write!(f, "{path}(")?;
                } else {
                    write!(f, "(")?;
                }
                write_with_separator(elements.iter(), ", ", f)?;
                if *has_rest {
                    if !elements.is_empty() {
                        write!(f, ", ")?;
                    }
                    write!(f, "..")?;
                }
                if path.is_none() && elements.len() == 1 && !*has_rest {
                    write!(f, ",")?;
                }
                write!(f, ")")
            }
            LetPatternKind::Record {
                path,
                fields,
                has_rest,
            } => {
                if let Some(path) = path {
                    write!(f, "{path} {{")?;
                } else {
                    write!(f, "{{")?;
                }
                write_with_separator(fields.iter(), ", ", f)?;
                if *has_rest {
                    if !fields.is_empty() {
                        write!(f, ", ")?;
                    }
                    write!(f, "..")?;
                }
                write!(f, "}}")
            }
        }
    }
}

/// A let-pattern.
#[derive(Debug, Clone, new)]
pub struct LetPattern<P: Phase> {
    pub kind: P::LetPatternContent,
    pub span: Location,
}

impl LetPattern<Parsed> {
    pub fn binding(name: UstrSpan, mut_val: MutVal) -> Self {
        let span = name.1;
        Self::new(LetPatternKind::binding(name, mut_val), span)
    }
}

impl LetPattern<Desugared> {
    pub fn binding(name: UstrSpan, mut_val: MutVal) -> Self {
        let span = name.1;
        Self::new(LetBindingPattern::new(name, mut_val), span)
    }
}

/// An AST let-pattern just after parsing
pub type PLetPattern = LetPattern<Parsed>;

/// An AST let-pattern after desugaring
pub type DLetPattern = LetPattern<Desugared>;

impl<P: Phase> Display for LetPattern<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.kind, f)
    }
}

/// Whether some arguments of an apply node should be hidden in the IDE
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

#[derive(Debug, Clone, EnumAsInner)]
pub enum PatternVariantKind {
    Tuple,
    Record,
}

#[derive(Debug, Clone, EnumAsInner)]
pub enum PatternVar {
    Named(UstrSpan),
    Wildcard(Location),
}
impl Display for PatternVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        use PatternVar::*;
        match self {
            Named((name, _)) => write!(f, "{name}"),
            Wildcard(_) => write!(f, ".."),
        }
    }
}

/// The kind-specific part of an expression as an Abstract Syntax Tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum PatternKind {
    Literal(LiteralValue, IrType),
    Variant {
        tag: UstrSpan,
        kind: PatternVariantKind,
        vars: Vec<PatternVar>,
    },
    Error(String),
}
impl PatternKind {
    pub fn tuple_variant(tag: UstrSpan, vars: Vec<PatternVar>) -> Self {
        PatternKind::Variant {
            tag,
            kind: PatternVariantKind::Tuple,
            vars,
        }
    }

    pub fn struct_variant(tag: UstrSpan, vars: Vec<PatternVar>) -> Self {
        PatternKind::Variant {
            tag,
            kind: PatternVariantKind::Record,
            vars,
        }
    }

    pub fn empty_tuple_variant(tag: UstrSpan) -> Self {
        PatternKind::Variant {
            tag,
            kind: PatternVariantKind::Tuple,
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
#[derive(Debug, Clone, new)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Location,
}

impl Pattern {
    pub fn format_ind(&self, f: &mut std::fmt::Formatter, indent: usize) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        use PatternKind::*;
        match &self.kind {
            Literal(value, _) => writeln!(f, "{indent_str}{value}"),
            Variant { tag, vars, .. } => {
                write!(f, "{indent_str}{} ", tag.0)?;
                if !vars.is_empty() {
                    write!(f, "(")?;
                    write_with_separator(vars.iter(), ", ", f)?;
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

/// A single, Rust-like attribute
#[derive(Debug, Clone)]
pub struct Attribute {
    pub path: UstrSpan,
    pub items: Vec<MetaItem>,
    pub span: Location,
}

/// A single item in an attribute
#[derive(Debug, Clone, EnumAsInner)]
pub enum MetaItem {
    Flag(UstrSpan),
    NameValue {
        key: UstrSpan,
        value: UstrSpan,
        span: Location,
    },
}

/// A parsed input trait constraint as written in a type definition `where` clause.
#[derive(Debug, Clone)]
pub struct TypeConstraintInput<P: Phase> {
    pub name: Option<UstrSpan>,
    pub ty: TypeSpan<P>,
}

impl<P: Phase> FormatWith<ModuleEnv<'_>> for TypeConstraintInput<P> {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        if let Some((name, _)) = self.name {
            write!(f, "{name} = {}", self.ty.0.format_with(env))
        } else {
            self.ty.0.fmt_with(f, env)
        }
    }
}

impl TypeConstraintInput<Parsed> {
    pub fn collect_refs(
        &self,
        name: Ustr,
        ty_names: &FxHashMap<Ustr, usize>,
        collected: &mut FxHashSet<usize>,
    ) -> Result<(), InternalCompilationError> {
        self.ty.0.collect_refs(name, ty_names, collected)
    }
}

/// A parsed output trait constraint as written in a type definition `where` clause.
#[derive(Debug, Clone)]
pub struct TypeConstraintOutput<P: Phase> {
    pub name: UstrSpan,
    pub ty: TypeSpan<P>,
}

impl<P: Phase> FormatWith<ModuleEnv<'_>> for TypeConstraintOutput<P> {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.name.0, self.ty.0.format_with(env))
    }
}

impl TypeConstraintOutput<Parsed> {
    pub fn collect_refs(
        &self,
        name: Ustr,
        ty_names: &FxHashMap<Ustr, usize>,
        collected: &mut FxHashSet<usize>,
    ) -> Result<(), InternalCompilationError> {
        self.ty.0.collect_refs(name, ty_names, collected)
    }
}

/// A parsed trait constraint as written in a type definition `where` clause.
#[derive(Debug, Clone)]
pub struct TypeConstraint<P: Phase> {
    pub trait_name: Path,
    pub input_types: Vec<TypeConstraintInput<P>>,
    pub output_types: Vec<TypeConstraintOutput<P>>,
    pub span: Location,
}

impl<P: Phase> FormatWith<ModuleEnv<'_>> for TypeConstraint<P> {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        if self.input_types.len() == 1 && self.input_types[0].name.is_none() {
            write!(
                f,
                "{}: {}",
                self.input_types[0].ty.0.format_with(env),
                self.trait_name
            )?;
            if self.output_types.is_empty() {
                return Ok(());
            }
            write!(f, "<")?;
            write_with_separator_and_format_fn(
                &self.output_types,
                ", ",
                |output_ty, f| output_ty.fmt_with(f, env),
                f,
            )?;
            write!(f, ">")?;
            return Ok(());
        }

        write!(f, "{}<", self.trait_name)?;
        write_with_separator_and_format_fn(
            &self.input_types,
            ", ",
            |input_ty, f| input_ty.fmt_with(f, env),
            f,
        )?;
        if !self.output_types.is_empty() {
            write!(f, " |-> ")?;
            write_with_separator_and_format_fn(
                &self.output_types,
                ", ",
                |output_ty, f| output_ty.fmt_with(f, env),
                f,
            )?;
        }
        write!(f, ">")
    }
}

impl TypeConstraint<Parsed> {
    pub fn collect_refs(
        &self,
        name: Ustr,
        ty_names: &FxHashMap<Ustr, usize>,
        collected: &mut FxHashSet<usize>,
    ) -> Result<(), InternalCompilationError> {
        self.input_types
            .iter()
            .try_for_each(|input| input.collect_refs(name, ty_names, collected))?;
        self.output_types
            .iter()
            .try_for_each(|output| output.collect_refs(name, ty_names, collected))?;
        Ok(())
    }
}

/// A type definition with common metadata
#[derive(Debug, Clone)]
pub struct TypeDef<P: Phase> {
    pub name: UstrSpan,
    pub generic_params: Vec<UstrSpan>,
    // The structural shape of the type (record, tuple, or unit)
    pub shape: P::Type,
    pub where_clause: Vec<TypeConstraint<P>>,
    pub attributes: Vec<Attribute>,
    pub variant_attributes: Vec<Vec<Attribute>>,
    pub span: Location,
    pub doc_comments: Vec<String>,
}

/// A type definition just after parsing
pub type PTypeDef = TypeDef<Parsed>;

/// A parsed output type constraint as written in a type definition `where` clause, after parsing.
pub type PTypeConstraintInput = TypeConstraintInput<Parsed>;

/// A parsed input type constraint as written in a type definition `where` clause, after parsing.
pub type PTypeConstraintOutput = TypeConstraintOutput<Parsed>;

/// A parsed type constraint as written in a type definition `where` clause, after parsing.
pub type PTypeConstraint = TypeConstraint<Parsed>;
