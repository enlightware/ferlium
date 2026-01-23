use derive_new::new;
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
use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Debug, Display},
};

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
}

impl Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_with_separator(self.segments.iter().map(|(s, _)| s), "::", f)
    }
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
    type ForLoop: Debug + Clone + FormatWithIndent + VisitExpr<Self>;
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
    type ForLoop = ForLoop;
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
        ty_names: &HashMap<Ustr, usize>,
        collected: &mut HashSet<usize>,
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
        ty_names: &HashMap<Ustr, usize>,
        collected: &mut HashSet<usize>,
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

/// Trait for formatting with a module environment
pub trait FormatWithIndent {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv,
        indent: usize,
    ) -> std::fmt::Result;
}

impl FormatWithIndent for Never {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv,
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
        env: &ModuleEnv,
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
    pub body: B<Expr<P>>,
    pub span: Location,
    pub doc: Option<String>,
}
impl<P: Phase> ModuleFunction<P> {
    pub fn new(
        name: UstrSpan,
        args: Vec<ModuleFunctionArg<P>>,
        args_span: Location,
        ret_ty: Option<TypeSpan<P>>,
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
#[derive(Debug, Clone)]
pub struct Module<P: Phase> {
    pub functions: Vec<ModuleFunction<P>>,
    pub impls: Vec<TraitImpl<P>>,
    pub type_aliases: Vec<P::TypeAliasInModule>,
    pub type_defs: Vec<P::TypeDefInModule>,
}
impl<P: Phase> Module<P> {
    pub fn extend(&mut self, other: Self) {
        self.functions.extend(other.functions);
        self.impls.extend(other.impls);
        self.type_aliases.extend(other.type_aliases);
        self.type_defs.extend(other.type_defs);
    }

    pub fn merge(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }

    pub fn errors(&self) -> Vec<LocatedError> {
        self.visit_with(ErrorCollector::default()).0
    }

    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
            && self.impls.is_empty()
            && self.type_aliases.is_empty()
            && self.type_defs.is_empty()
    }
}
impl Module<Parsed> {
    /// Returns all the names defined in this module, including functions, type aliases, and type definitions.
    pub fn name_iter(&self) -> impl Iterator<Item = UstrSpan> + '_ {
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
        }
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

impl<P: Phase> FormatWith<ModuleEnv<'_>> for Module<P> {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv) -> std::fmt::Result {
        if !self.type_aliases.is_empty() {
            writeln!(f, "Types:")?;
            for alias in self.type_aliases.iter() {
                writeln!(f, "  {}", alias.format_with(env))?;
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
                        writeln!(f, "    /// {doc}")?;
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
                    writeln!(f, "  /// {doc}")?;
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

/// A record field in an expression
pub type RecordField<P> = (UstrSpan, Expr<P>);

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

/// The kind-specific part of an expression as an Abstract Syntax Tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum ExprKind<P: Phase> {
    Literal(Value, IrType),
    FormattedString(P::FormattedString),
    /// A variable, or a function from the module environment, or a null-ary variant constructor
    Identifier(Path),
    Let(
        UstrSpan,
        MutVal,
        B<Expr<P>>,
        Option<(Location, P::LetTyAscriptionComplete)>,
    ),
    Return(B<Expr<P>>),
    Abstract(Vec<UstrSpan>, B<Expr<P>>),
    Apply(B<Expr<P>>, Vec<Expr<P>>, UnnamedArg),
    Block(Vec<Expr<P>>),
    Assign(B<Expr<P>>, Location, B<Expr<P>>),
    PropertyPath(Path, Ustr),
    Tuple(Vec<Expr<P>>),
    Project(B<Expr<P>>, (usize, Location)),
    Record(RecordFields<P>),
    StructLiteral(Path, RecordFields<P>),
    FieldAccess(B<Expr<P>>, UstrSpan),
    Array(Vec<Expr<P>>),
    Index(B<Expr<P>>, B<Expr<P>>),
    Match(B<Expr<P>>, Vec<(Pattern, Expr<P>)>, Option<B<Expr<P>>>),
    ForLoop(P::ForLoop),
    Loop(B<Expr<P>>),
    SoftBreak,
    TypeAscription(B<Expr<P>>, P::Type, Location),
    Error,
}

/// An expression as an Abstract Syntax Tree
#[derive(Debug, Clone, new)]
pub struct Expr<P: Phase> {
    pub kind: ExprKind<P>,
    pub span: Location,
}

impl<P: Phase> Expr<P> {
    pub fn single_identifier(name: Ustr, span: Location) -> Self {
        Expr::new(ExprKind::Identifier(Path::single(name, span)), span)
    }
}

impl<P: Phase> FormatWithIndent for Expr<P> {
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "  ".repeat(indent);
        use ExprKind::*;
        match &self.kind {
            Literal(value, ty) => writeln!(f, "{indent_str}{}", value.display_pretty(ty)),
            FormattedString(string) => writeln!(f, "{indent_str}f\"{string}\""),
            Identifier(path) => writeln!(f, "{indent_str}{path}"),
            Let((name, _), mutable, expr, _) => {
                let kw = mutable.var_def_string();
                writeln!(f, "{indent_str}{kw} {name} =")?;
                expr.format_ind(f, env, indent + 1)
            }
            Return(expr) => {
                writeln!(f, "{indent_str}return")?;
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
            StructLiteral(path, fields) => {
                writeln!(f, "{indent_str}{path} {{")?;
                for ((name, _), value) in fields.iter() {
                    writeln!(f, "{indent_str}  {name}:")?;
                    value.format_ind(f, env, indent + 2)?;
                    writeln!(f, "{indent_str}  ,")?;
                }
                writeln!(f, "{indent_str}}}")
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
            PropertyPath(scope, name) => writeln!(f, "{indent_str}@{scope}.{name}"),
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
            StructLiteral(_, fields) => visitor.visit_exprs(fields.iter().map(|(_, expr)| expr)),
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

impl<P: Phase> FormatWith<ModuleEnv<'_>> for Expr<P> {
    fn fmt_with(&self, f: &mut std::fmt::Formatter, env: &ModuleEnv<'_>) -> std::fmt::Result {
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
