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
    FxHashMap, FxHashSet, Location,
    compiler::error::InternalCompilationError,
    format::write_with_separator_and_format_fn,
    format::{FormatWith, write_identifier, write_with_separator},
    hir::value::LiteralValue,
    module::{ModuleEnv, TypeDefId, Visibility},
    types::mutability::MutVal,
    types::r#type::{Type as IrType, TypeDefShapeDocs},
};

use super::{Desugared, GenericParams, PEffect, Parsed, Path, Phase, TypeSpan, UstrSpan};

#[derive(Debug, Clone, Copy, new)]
pub struct LetBindingPattern {
    pub name: UstrSpan,
    pub mut_val: MutVal,
}

impl Display for LetBindingPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.mut_val == MutVal::mutable() {
            write!(f, "mut ")?;
            write_identifier(f, self.name.0.as_str())
        } else {
            write_identifier(f, self.name.0.as_str())
        }
    }
}

/// An internal constraint induced by a destructuring pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternConstraintKind {
    ExactTuple(usize),
    NamedType(TypeDefId),
}

impl Display for PatternConstraintKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternConstraintKind::ExactTuple(element_count) => {
                write!(f, "exact {element_count}-tuple")
            }
            PatternConstraintKind::NamedType(type_def) => {
                write!(f, "named type #{}:{}", type_def.module, type_def.index)
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
            write_identifier(f, self.name.0.as_str())
        } else {
            write_identifier(f, self.name.0.as_str())?;
            write!(f, ": {}", self.pattern)
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
                    write!(f, "mut ")?;
                    write_identifier(f, name.0.as_str())
                } else {
                    write_identifier(f, name.0.as_str())
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
            Named((name, _)) => write_identifier(f, name.as_str()),
            Wildcard(_) => write!(f, ".."),
        }
    }
}

/// A variant constructor path used by match patterns.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatternVariantPath {
    pub path: Path,
}

impl PatternVariantPath {
    pub fn new(path: Path) -> Self {
        Self { path }
    }

    pub fn single(tag: UstrSpan) -> Self {
        Self::new(Path::single_tuple(tag))
    }

    pub fn is_qualified(&self) -> bool {
        self.path.segments.len() > 1
    }

    pub fn tag(&self) -> UstrSpan {
        *self
            .path
            .segments
            .last()
            .expect("pattern variant path cannot be empty")
    }
}

impl Display for PatternVariantPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.path, f)
    }
}

/// The kind-specific part of an expression as an Abstract Syntax Tree
#[derive(Debug, Clone, EnumAsInner)]
pub enum PatternKind {
    Literal(LiteralValue, IrType),
    Variant {
        path: PatternVariantPath,
        kind: PatternVariantKind,
        vars: Vec<PatternVar>,
    },
    Error(String),
}
impl PatternKind {
    pub fn tuple_variant(tag: UstrSpan, vars: Vec<PatternVar>) -> Self {
        Self::tuple_variant_path_ref(PatternVariantPath::single(tag), vars)
    }

    pub fn tuple_variant_path(path: Path, vars: Vec<PatternVar>) -> Self {
        Self::tuple_variant_path_ref(PatternVariantPath::new(path), vars)
    }

    pub fn tuple_variant_path_ref(path: PatternVariantPath, vars: Vec<PatternVar>) -> Self {
        PatternKind::Variant {
            path,
            kind: PatternVariantKind::Tuple,
            vars,
        }
    }

    pub fn struct_variant(tag: UstrSpan, vars: Vec<PatternVar>) -> Self {
        Self::struct_variant_path_ref(PatternVariantPath::single(tag), vars)
    }

    pub fn struct_variant_path(path: Path, vars: Vec<PatternVar>) -> Self {
        Self::struct_variant_path_ref(PatternVariantPath::new(path), vars)
    }

    pub fn struct_variant_path_ref(path: PatternVariantPath, vars: Vec<PatternVar>) -> Self {
        PatternKind::Variant {
            path,
            kind: PatternVariantKind::Record,
            vars,
        }
    }

    pub fn empty_tuple_variant(tag: UstrSpan) -> Self {
        Self::empty_tuple_variant_path(Path::single_tuple(tag))
    }

    pub fn empty_tuple_variant_path(path: Path) -> Self {
        PatternKind::Variant {
            path: PatternVariantPath::new(path),
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
            Variant { path, vars, .. } => {
                write!(f, "{indent_str}{path} ")?;
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
            write_identifier(f, name.as_str())?;
            write!(f, " = {}", self.ty.0.format_with(env))
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
        write_identifier(f, self.name.0.as_str())?;
        write!(f, " = {}", self.ty.0.format_with(env))
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

/// A parsed output effect binding in a trait constraint.
#[derive(Debug, Clone)]
pub struct TypeConstraintEffectOutput {
    pub name: UstrSpan,
    pub effects: Vec<PEffect>,
}

pub(crate) fn format_effect_binding_value(
    effects: &[PEffect],
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    match effects {
        [] => write!(f, "()"),
        [effect] => effect.fmt(f),
        effects => {
            write!(f, "(")?;
            write_with_separator(effects, ", ", f)?;
            write!(f, ")")
        }
    }
}

/// A parsed trait constraint as written in a type definition `where` clause.
#[derive(Debug, Clone)]
pub struct TypeConstraint<P: Phase> {
    pub trait_name: Path,
    pub input_types: Vec<TypeConstraintInput<P>>,
    pub output_types: Vec<TypeConstraintOutput<P>>,
    pub output_effects: Vec<TypeConstraintEffectOutput>,
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
            if self.output_types.is_empty() && self.output_effects.is_empty() {
                return Ok(());
            }
            write!(f, "<")?;
            if !self.output_types.is_empty() {
                write_with_separator_and_format_fn(
                    &self.output_types,
                    ", ",
                    |output_ty, f| output_ty.fmt_with(f, env),
                    f,
                )?;
            }
            if !self.output_effects.is_empty() {
                if !self.output_types.is_empty() {
                    write!(f, " ")?;
                }
                write!(f, "! ")?;
                write_with_separator_and_format_fn(
                    &self.output_effects,
                    ", ",
                    |output_eff, f| {
                        write_identifier(f, output_eff.name.0.as_str())?;
                        write!(f, " = ")?;
                        format_effect_binding_value(&output_eff.effects, f)
                    },
                    f,
                )?;
            }
            write!(f, ">")?;
            return Ok(());
        }

        self.fmt_trait_headed(f, env)
    }
}

impl<P: Phase> TypeConstraint<P> {
    pub(crate) fn fmt_trait_headed(
        &self,
        f: &mut fmt::Formatter<'_>,
        env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "{}<", self.trait_name)?;
        write_with_separator_and_format_fn(
            &self.input_types,
            ", ",
            |input_ty, f| input_ty.fmt_with(f, env),
            f,
        )?;
        if !self.output_types.is_empty() || !self.output_effects.is_empty() {
            write!(f, " |-> ")?;
            if !self.output_types.is_empty() {
                write_with_separator_and_format_fn(
                    &self.output_types,
                    ", ",
                    |output_ty, f| output_ty.fmt_with(f, env),
                    f,
                )?;
            }
            if !self.output_effects.is_empty() {
                if !self.output_types.is_empty() {
                    write!(f, " ")?;
                }
                write!(f, "! ")?;
                write_with_separator_and_format_fn(
                    &self.output_effects,
                    ", ",
                    |output_eff, f| {
                        write_identifier(f, output_eff.name.0.as_str())?;
                        write!(f, " = ")?;
                        format_effect_binding_value(&output_eff.effects, f)
                    },
                    f,
                )?;
            }
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
    pub visibility: Visibility,
    pub name: UstrSpan,
    pub generic_params: GenericParams,
    // The structural shape of the type (record, tuple, or unit)
    pub shape: P::Type,
    pub where_clause: Vec<TypeConstraint<P>>,
    pub attributes: Vec<Attribute>,
    pub variant_attributes: Vec<Vec<Attribute>>,
    pub shape_docs: TypeDefShapeDocs,
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
