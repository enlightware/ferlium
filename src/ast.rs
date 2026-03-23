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

use crate::{FxHashMap, FxHashSet};

use ustr::Ustr;

use crate::{
    Location,
    containers::{B, b},
    error::{InternalCompilationError, LocatedError},
    format::{FormatWith, write_with_separator},
    internal_compilation_error,
    module::ModuleEnv,
    mutability::{FormatInFnArg, MutType as IrMutType, MutVal},
    never::Never,
    parser_helpers::EMPTY_USTR,
    r#type::Type as IrType,
    type_like::TypeLike,
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
    pub ty: TypeSpan<Parsed>,
}
impl FormatWith<ModuleEnv<'_>> for TypeAlias {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv) -> std::fmt::Result {
        write!(f, "{}: {}", self.name.0, self.ty.0.format_with(env))?;
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
    type Type: Debug + Clone + for<'a> FormatWith<ModuleEnv<'a>>;
    type MutType: Debug + Clone + FormatInFnArg;
    type LetTyAscriptionComplete: Debug + Clone;
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
    type Type = PType;
    type MutType = PMutType;
    type LetTyAscriptionComplete = ();
    type TypeAliasInModule = TypeAlias;
    type TypeDefInModule = TypeDef<Self>;
}

/// The state of the AST after type name resolution and desugaring, ready for type inference
impl Phase for Desugared {
    type FormattedString = Never;
    type ForLoop = Never;
    type Type = IrType;
    type MutType = IrMutType;
    type LetTyAscriptionComplete = bool;
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

/// The type of a function
#[derive(Debug, Clone, PartialEq, Eq, new)]
pub struct PFnType {
    pub args: Vec<PFnArgType>,
    pub ret: TypeSpan<Parsed>,
    pub effects: bool, // true if this function should have generic effects
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
        self.ret.0.fmt_with(f, env)
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
    // TODO: currently we do not support explicit generic types in the AST
}
impl PType {
    pub fn function_type(fn_type: PFnType) -> Self {
        PType::Function(b(fn_type))
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

/// The data of a for loop
#[derive(Clone, Debug)]
pub struct ForLoopData {
    pub var_name: UstrSpan,
    pub iterator: PExprId,
    pub body: PExprId,
}

impl ForLoopData {
    pub fn new(var_name: UstrSpan, iterator: PExprId, body: PExprId) -> Self {
        Self {
            var_name,
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
        writeln!(f, "{indent_str}for {} in", self.var_name.0)?;
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

#[derive(Debug, Clone)]
pub struct ModuleFunction<P: Phase> {
    pub name: UstrSpan,
    pub args: Vec<ModuleFunctionArg<P>>,
    pub args_span: Location,
    pub ret_ty: Option<TypeSpan<P>>,
    pub body: ExprId<P>,
    pub span: Location,
    pub doc: Option<String>,
}
impl<P: Phase> ModuleFunction<P> {
    pub fn new(
        name: UstrSpan,
        args: Vec<ModuleFunctionArg<P>>,
        args_span: Location,
        ret_ty: Option<TypeSpan<P>>,
        body: ExprId<P>,
        span: Location,
        doc: Option<String>,
    ) -> Self {
        Self {
            name,
            args,
            args_span,
            ret_ty,
            body,
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
    /// Explicit concrete types for the implementation, e.g. `impl Ord for S`.
    /// When `None`, the types are fully inferred from the functions signatures.
    pub for_tys: Option<Vec<TypeSpan<P>>>,
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
    pub functions: Vec<ModuleFunction<P>>,
    pub impls: Vec<TraitImpl<P>>,
    pub type_aliases: Vec<P::TypeAliasInModule>,
    pub type_defs: Vec<P::TypeDefInModule>,
    pub uses: Vec<UseTree>,
}
impl<P: Phase> Module<P> {
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
        self.functions.is_empty()
            && self.impls.is_empty()
            && self.type_aliases.is_empty()
            && self.type_defs.is_empty()
            && self.uses.is_empty()
    }
}
impl Module<Parsed> {
    /// Returns all the names defined in this module, including functions, type aliases, and type definitions.
    pub fn own_symbols(&self) -> impl Iterator<Item = UstrSpan> + '_ {
        self.functions
            .iter()
            .map(|f| f.name)
            .chain(self.type_aliases.iter().map(|alias| alias.name))
            .chain(self.type_defs.iter().map(|def| def.name))
    }
}

impl<P: Phase> Default for Module<P> {
    fn default() -> Self {
        Self {
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

impl<'a, P: Phase> FormatWith<ModuleEnv<'_>> for ModuleDisplay<'a, P> {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv) -> std::fmt::Result {
        let module = self.module;
        let arena = self.arena;
        if !module.type_aliases.is_empty() {
            writeln!(f, "Types:")?;
            for alias in module.type_aliases.iter() {
                writeln!(f, "  {}", alias.format_with(env))?;
            }
        }
        if !module.impls.is_empty() {
            writeln!(f, "Trait implementations:")?;
            for TraitImpl {
                trait_name,
                for_tys: for_ty,
                functions,
                ..
            } in module.impls.iter()
            {
                if let Some(tys) = for_ty {
                    if let [ty] = &tys[..] {
                        writeln!(
                            f,
                            "  impl {} for {} {{",
                            trait_name.0,
                            ty.0.format_with(env)
                        )?;
                    } else {
                        writeln!(
                            f,
                            "  impl {} for <{}> {{",
                            trait_name.0,
                            tys.iter().map(|ty| ty.0.format_with(env)).join(", ")
                        )?;
                    }
                } else {
                    writeln!(f, "  impl {} {{", trait_name.0)?;
                }
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
                        for line in doc.split("\n") {
                            writeln!(f, "    /// {line}")?;
                        }
                    }
                    write!(f, "    fn {}(", name.0,)?;
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
                    writeln!(f)?;
                    arena[*body].format_ind(f, env, arena, 3)?;
                }
                writeln!(f, "  }}")?;
            }
        }
        if !module.functions.is_empty() {
            writeln!(f, "Functions:")?;
            for ModuleFunction {
                name,
                args,
                ret_ty,
                body,
                doc,
                ..
            } in module.functions.iter()
            {
                if let Some(doc) = doc {
                    for line in doc.split("\n") {
                        writeln!(f, "  /// {line}")?;
                    }
                }
                write!(f, "    fn {}(", name.0,)?;
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
                writeln!(f)?;
                arena[*body].format_ind(f, env, arena, 2)?;
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
    pub name: UstrSpan,
    pub mut_val: MutVal,
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
    Index(IndexData<P>),
    Match(B<MatchData<P>>),
    ForLoop(P::ForLoop),
    Loop(ExprId<P>),
    SoftBreak,
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
        name: UstrSpan,
        mut_val: MutVal,
        expr: ExprId<P>,
        ty_ascription: Option<(Location, P::LetTyAscriptionComplete)>,
    ) -> Self {
        ExprKind::Let(b(LetData {
            name,
            mut_val,
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

    /// Construct an [`Index`](ExprKind::Index) expression (array indexing).
    pub fn index(array: ExprId<P>, index: ExprId<P>) -> Self {
        ExprKind::Index(IndexData { array, index })
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
                let kw = data.mut_val.var_def_string();
                writeln!(f, "{indent_str}{kw} {} =", data.name.0)?;
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
            Index(data) => {
                arena[data.array].format_ind(f, env, arena, indent)?;
                writeln!(f, "{indent_str}[")?;
                arena[data.index].format_ind(f, env, arena, indent + 1)?;
                writeln!(f, "{indent_str}]")
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
            Index(data) => {
                arena[data.array].visit(visitor, arena);
                arena[data.index].visit(visitor, arena);
            }
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
            TypeAscription(data) => arena[data.expr].visit(visitor, arena),
            _ => {}
        }
        visitor.visit_end(self);
    }

    // TODO: use the visitor to collect the dependency graph
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

/// A type definition with common metadata
#[derive(Debug, Clone)]
pub struct TypeDef<P: Phase> {
    pub name: UstrSpan,
    pub generic_params: Vec<UstrSpan>,
    // The structural shape of the type (record, tuple, or unit)
    pub shape: P::Type,
    pub attributes: Vec<Attribute>,
    pub span: Location,
    pub doc_comments: Vec<String>,
    // TODO: add constraints for the type arguments
}

/// A type definition just after parsing
pub type PTypeDef = TypeDef<Parsed>;
