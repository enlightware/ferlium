// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use core::panic;
use std::{
    fmt::{self, Debug, Display},
    ops::Deref,
};

use crate::{
    format::FormatWith, location::Location, r#trait::TraitRef, r#type::TypeDefRef,
    type_inference::SubOrSameType, type_scheme::PubTypeConstraint,
};
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use ustr::Ustr;

use crate::{
    ast::{PatternType, PropertyAccess},
    effects::EffType,
    module::ModuleEnv,
    r#type::{Type, TypeVar},
};

pub type LocatedError = (String, Location);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ADTAccessType {
    RecordAccess,
    TupleProject,
    Variant,
}
impl ADTAccessType {
    pub fn adt_kind(&self) -> &'static str {
        use ADTAccessType::*;
        match self {
            RecordAccess => "record",
            TupleProject => "tuple",
            Variant => "variant",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MutabilityMustBeWhat {
    Mutable,
    Constant,
    Equal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MutabilityMustBeContext {
    Value,
    FnTypeArg(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DuplicatedFieldContext {
    Record,
    Struct,
}
impl DuplicatedFieldContext {
    pub fn as_str(&self) -> &'static str {
        use DuplicatedFieldContext::*;
        match self {
            Record => "record",
            Struct => "struct",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DuplicatedVariantContext {
    Match,
    Enum,
    Variant,
}
impl DuplicatedVariantContext {
    pub fn as_str(&self) -> &'static str {
        use DuplicatedVariantContext::*;
        match self {
            Match => "match",
            Enum => "enum",
            Variant => "variant union",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WhichProductTypeIsNot {
    Unit,
    Record,
    Tuple,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WhatIsNotAProductType {
    EnumVariant(Ustr),
    Struct,
}
impl WhatIsNotAProductType {
    pub fn from_tag(tag: Option<Ustr>) -> Self {
        tag.map_or(Self::Struct, Self::EnumVariant)
    }
}

/// A scope of error messages, either internal within the compiler, or external for users.
pub trait Scope: Sized {
    type Type: Debug + Clone;
    type TypeVar: Debug + Clone;
    type TypeDefRef: Debug + Clone;
    type PubTypeConstraint: Debug + Clone;
    type TraitRef: Debug + Clone;
    type ValidVariant: Debug + Clone;
}

/// Internal scope, using internal compiler representations.
/// Types are complete internal types.
#[derive(Debug, Clone)]
pub struct Internal;
impl Scope for Internal {
    type Type = Type;
    type TypeVar = TypeVar;
    type TypeDefRef = TypeDefRef;
    type PubTypeConstraint = PubTypeConstraint;
    type TraitRef = TraitRef;
    type ValidVariant = ();
}

/// External scope, using user-facing representations.
/// Types are strings suitable for display.
#[derive(Debug, Clone)]
pub struct External;
impl Scope for External {
    type Type = String;
    type TypeVar = String;
    type TypeDefRef = (String, Location);
    type PubTypeConstraint = String;
    type TraitRef = String;
    type ValidVariant = Vec<String>;
}

/// Compilation error implementation.
/// Uses the tree-that-grows pattern to be generic over
/// the scope of error message use.
#[derive(Debug, Clone, EnumAsInner)]
pub enum CompilationErrorImpl<S: Scope> {
    ParsingFailed(Vec<LocatedError>),
    NameDefinedMultipleTimes {
        name: Ustr,
        first_occurrence: Location,
        second_occurrence: Location,
    },
    TypeNotFound(Location),
    TraitNotFound(Location),
    WrongNumberOfArguments {
        expected: usize,
        expected_span: Location,
        got: usize,
        got_span: Location,
    },
    MutabilityMustBe {
        source_span: Location,
        reason_span: Location,
        what: MutabilityMustBeWhat,
        ctx: MutabilityMustBeContext,
    },
    TypeMismatch {
        current_ty: S::Type,
        current_span: Location,
        expected_ty: S::Type,
        expected_span: Location,
        sub_or_same: SubOrSameType,
    },
    NamedTypeMismatch {
        current_decl: S::TypeDefRef,
        current_span: Location,
        expected_decl: S::TypeDefRef,
        expected_span: Location,
    },
    InfiniteType(S::TypeVar, S::Type, Location),
    UnboundTypeVar {
        ty_var: S::TypeVar,
        ty: S::Type,
        span: Location,
    },
    UnresolvedConstraints {
        constraints: Vec<S::PubTypeConstraint>,
        span: Location,
    },
    InvalidTupleIndex {
        index: usize,
        index_span: Location,
        tuple_length: usize,
        tuple_span: Location,
    },
    InvalidTupleProjection {
        expr_ty: S::Type,
        expr_span: Location,
        index_span: Location,
    },
    DuplicatedField {
        first_occurrence: Location,
        second_occurrence: Location,
        constructor_span: Location,
        ctx: DuplicatedFieldContext,
    },
    InvalidRecordField {
        field_span: Location,
        record_ty: S::Type,
        record_span: Location,
    },
    InvalidRecordFieldAccess {
        field_span: Location,
        record_ty: S::Type,
        record_span: Location,
    },
    InvalidVariantName {
        name: Location,
        ty: S::Type,
        valid: S::ValidVariant,
    },
    InvalidVariantType {
        name: Location,
        ty: S::Type,
    },
    InvalidVariantConstructor {
        span: Location,
        // Only one error type for now: a path was used as a variant constructor
    },
    IsNotCorrectProductType {
        which: WhichProductTypeIsNot,
        type_def: S::TypeDefRef,
        what: WhatIsNotAProductType,
        instantiation_span: Location,
    },
    InvalidStructField {
        type_def: S::TypeDefRef,
        field_name: Ustr,
        field_span: Location,
        instantiation_span: Location,
    },
    MissingStructField {
        type_def: S::TypeDefRef,
        field_name: Ustr,
        instantiation_span: Location,
    },
    InconsistentADT {
        a_type: ADTAccessType,
        a_span: Location,
        b_type: ADTAccessType,
        b_span: Location,
    },
    EmptyMatchBody {
        span: Location,
    },
    InconsistentPattern {
        a_type: PatternType,
        a_span: Location,
        b_type: PatternType,
        b_span: Location,
    },
    DuplicatedVariant {
        first_occurrence: Location,
        second_occurrence: Location,
        ctx_span: Location,
        ctx: DuplicatedVariantContext,
    },
    RecordWildcardPatternNotAtEnd {
        pattern_span: Location,
        wildcard_span: Location,
    },
    TraitImplNotFound {
        trait_ref: S::TraitRef,
        input_tys: Vec<S::Type>,
        fn_span: Location,
    },
    MethodsNotPartOfTrait {
        trait_ref: S::TraitRef,
        spans: Vec<Location>,
    },
    TraitMethodImplsMissing {
        trait_ref: S::TraitRef,
        impl_span: Location,
        missings: Vec<Ustr>,
    },
    TraitMethodArgCountMismatch {
        trait_ref: S::TraitRef,
        method_index: usize,
        method_name: Ustr,
        expected: usize,
        got: usize,
        args_span: Location,
    },
    IdentifierBoundMoreThanOnceInAPattern {
        first_occurrence: Location,
        second_occurrence: Location,
        pattern_span: Location,
    },
    DuplicatedLiteralPattern {
        first_occurrence: Location,
        second_occurrence: Location,
        match_span: Location,
    },
    NonExhaustivePattern {
        span: Location,
        ty: S::Type,
        // TODO: have a generic way to talk about the non-covered values
    },
    TypeValuesCannotBeEnumerated {
        span: Location,
        ty: S::Type,
    },
    MutablePathsOverlap {
        a_span: Location,
        b_span: Location,
        fn_span: Location,
    },
    UndefinedVarInStringFormatting {
        var_span: Location,
        string_span: Location,
    },
    InvalidEffectDependency {
        source: EffType,
        source_span: Location,
        target: EffType,
        target_span: Location,
    },
    UnknownProperty {
        scope: Ustr,
        variable: Ustr,
        cause: PropertyAccess,
        span: Location,
    },
    Unsupported {
        span: Location,
        reason: String,
    },
    ReturnOutsideFunction {
        span: Location,
    },
    /*UnresolvedImport {
        function_path: String,
        span: Location,
    },
    ImportSignatureMismatch {
        function_path: String,
        expected_signature: String,
        got_signature: String,
        span: Location,
    },
    CircularImportDependency {
        import_chain: Vec<String>,
        span: Location,
    },*/
    Internal(String),
}

#[derive(Debug, Clone)]
pub struct BoxedCompilationError<S: Scope>(Box<CompilationErrorImpl<S>>);
impl<S: Scope> BoxedCompilationError<S> {
    pub fn new(error: CompilationErrorImpl<S>) -> Self {
        Self(Box::new(error))
    }
    pub fn into_inner(self) -> CompilationErrorImpl<S> {
        *self.0
    }
}

impl<S: Scope> Deref for BoxedCompilationError<S> {
    type Target = CompilationErrorImpl<S>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub type InternalCompilationError = BoxedCompilationError<Internal>;

#[macro_export]
macro_rules! internal_compilation_error {
    ($($ctor:tt)*) => {
        InternalCompilationError::new(
            $crate::error::CompilationErrorImpl::$($ctor)*
        )
    };
}

impl InternalCompilationError {
    pub fn new_inconsistent_adt(
        mut a_type: ADTAccessType,
        mut a_span: Location,
        mut b_type: ADTAccessType,
        mut b_span: Location,
    ) -> Self {
        if a_span.start() > b_span.start() {
            std::mem::swap(&mut a_type, &mut b_type);
            std::mem::swap(&mut a_span, &mut b_span);
        }
        internal_compilation_error!(InconsistentADT {
            a_type,
            a_span,
            b_type,
            b_span,
        })
    }
}

impl FormatWith<(ModuleEnv<'_>, &str)> for InternalCompilationError {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &(ModuleEnv<'_>, &str)) -> fmt::Result {
        let (env, source) = data;
        let error = CompilationError::resolve_types(self.clone(), env, source);
        write!(f, "{}", error.format_with(source))
    }
}

fn span_to_string(loc: &Location, source: &str) -> String {
    match loc.module() {
        Some(module) => format!(
            "{}..{} in module {}",
            module.span().start(),
            module.span().end(),
            module.module_name()
        ),
        None => {
            if loc.start() < loc.end() {
                source[loc.start()..loc.end()].to_string()
            } else {
                let end = source.len().min(loc.end() + 20);
                let more = if end < source.len() { "…" } else { "" };
                format!(
                    "location where \"{}{more}\" starts",
                    &source[loc.start()..end]
                )
            }
        }
    }
}

pub type CompilationError = BoxedCompilationError<External>;

impl FormatWith<&str> for CompilationError {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, data: &&'_ str) -> fmt::Result {
        let source = data;
        let fmt_span = |loc: &Location| span_to_string(loc, source);
        use CompilationErrorImpl::*;
        match self.deref() {
            ParsingFailed(errors) => {
                write!(f, "Parsing failed: ")?;
                for (i, (msg, span)) in errors.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} in {}", msg, fmt_span(span))?;
                }
                Ok(())
            }
            NameDefinedMultipleTimes { name, .. } => {
                write!(f, "Name `{name}` defined multiple times")
            }
            TypeNotFound(span) => {
                write!(f, "Cannot find type `{}` in this scope", fmt_span(span))
            }
            TraitNotFound(span) => {
                write!(f, "Cannot find trait `{}` in this scope", fmt_span(span))
            }
            WrongNumberOfArguments {
                expected,
                expected_span,
                got,
                got_span,
            } => {
                write!(
                    f,
                    "Wrong number of arguments: expected {} due to `{}`, but {} were provided in `{}`",
                    expected,
                    fmt_span(expected_span),
                    got,
                    fmt_span(got_span)
                )
            }
            MutabilityMustBe {
                source_span,
                reason_span,
                what,
                ..
            } => {
                let source_name = fmt_span(source_span);
                let reason_name = fmt_span(reason_span);
                use MutabilityMustBeWhat::*;
                let what = match what {
                    Mutable => "mutable due to",
                    Constant => "constant due to",
                    Equal => "of same mutability to",
                };
                write!(
                    f,
                    "Expression `{source_name}` must be {what} `{reason_name}`"
                )
            }
            TypeMismatch {
                current_ty,
                current_span,
                expected_ty,
                expected_span,
                sub_or_same,
            } => write!(
                f,
                "Type `{}` in `{}` is not {} `{}` in `{}`",
                current_ty,
                fmt_span(current_span),
                match sub_or_same {
                    SubOrSameType::SubType => "a sub-type of",
                    SubOrSameType::SameType => "the same type as",
                },
                expected_ty,
                fmt_span(expected_span),
            ),
            NamedTypeMismatch {
                current_decl,
                current_span,
                expected_decl,
                expected_span,
            } => write!(
                f,
                "Named type `{}` in `{}` (from `{}`) is different than named type `{}` in `{}` (from `{}`)",
                current_decl.0,
                fmt_span(current_span),
                fmt_span(&current_decl.1),
                expected_decl.0,
                fmt_span(expected_span),
                fmt_span(&expected_decl.1),
            ),
            InfiniteType(ty_var, ty, span) => {
                write!(
                    f,
                    "Infinite type: `{}` = `{}` in `{}`",
                    ty_var,
                    ty,
                    fmt_span(span)
                )
            }
            UnboundTypeVar { ty_var, ty, span } => {
                write!(
                    f,
                    "Unbound type variable `{}` in type `{}` in `{}`",
                    ty_var,
                    ty,
                    fmt_span(span)
                )
            }
            UnresolvedConstraints { constraints, span } => {
                write!(
                    f,
                    "Unresolved constraints `{}` in expression `{}`",
                    constraints.join(" ∧ "),
                    fmt_span(span)
                )
            }
            InvalidTupleIndex {
                index,
                tuple_length,
                tuple_span,
                ..
            } => {
                write!(
                    f,
                    "Invalid index {} of a tuple of length {} in `{}`",
                    index,
                    tuple_length,
                    fmt_span(tuple_span)
                )
            }
            InvalidTupleProjection {
                expr_ty, expr_span, ..
            } => {
                write!(
                    f,
                    "Expected tuple, got `{}` in `{}`",
                    expr_ty,
                    fmt_span(expr_span)
                )
            }
            DuplicatedField {
                first_occurrence,
                constructor_span,
                ctx,
                ..
            } => {
                write!(
                    f,
                    "Duplicated field `{}` in {} `{}`",
                    fmt_span(first_occurrence),
                    ctx.as_str(),
                    fmt_span(constructor_span)
                )
            }
            InvalidRecordField {
                field_span,
                record_ty,
                record_span,
            } => {
                write!(
                    f,
                    "Field `{}` not found in record `{}` of type `{}`",
                    fmt_span(field_span),
                    fmt_span(record_span),
                    record_ty,
                )
            }
            InvalidRecordFieldAccess {
                field_span,
                record_ty,
                record_span,
            } => {
                write!(
                    f,
                    "Expected record due to `{}`, got `{}` in `{}`",
                    fmt_span(field_span),
                    record_ty,
                    fmt_span(record_span)
                )
            }
            InvalidVariantName { name, ty, valid } => {
                write!(
                    f,
                    "Variant name `{}` does not exist for variant type `{}`, valid names are `{}`",
                    fmt_span(name),
                    ty,
                    valid.join(", ")
                )
            }
            InvalidVariantType { name, ty } => {
                write!(
                    f,
                    "Type `{}` is not a variant, but variant constructor `{}` requires it",
                    ty,
                    fmt_span(name)
                )
            }
            InvalidVariantConstructor { span } => {
                write!(
                    f,
                    "Variant constructor cannot be paths, but `{}` is",
                    fmt_span(span)
                )
            }
            ReturnOutsideFunction { span } => {
                write!(
                    f,
                    "Return statement can only be used inside a function, but found in sub-expression `{}`",
                    fmt_span(span)
                )
            }
            IsNotCorrectProductType {
                which,
                type_def,
                what,
                instantiation_span,
            } => {
                use WhichProductTypeIsNot::*;
                let which = match which {
                    Unit => "arguments, but none are provided in",
                    Record => "a record, but none is provided in",
                    Tuple => "a tuple, but none is provided in",
                };
                let what = match what {
                    WhatIsNotAProductType::EnumVariant(tag) => {
                        format!("Variant `{tag}` of `{}`", type_def.0)
                    }
                    WhatIsNotAProductType::Struct => format!("`{}`", type_def.0),
                };
                write!(
                    f,
                    "{} requires {} `{}`",
                    what,
                    which,
                    fmt_span(instantiation_span)
                )
            }
            InvalidStructField {
                type_def,
                instantiation_span,
                field_name,
                ..
            } => {
                write!(
                    f,
                    "Field `{}` does not exists in `{}`, but is present in `{}`",
                    field_name,
                    type_def.0,
                    fmt_span(instantiation_span)
                )
            }
            MissingStructField {
                type_def,
                field_name,
                instantiation_span,
            } => {
                write!(
                    f,
                    "Field `{}` from `{}` is missing in `{}`",
                    field_name,
                    type_def.0,
                    fmt_span(instantiation_span)
                )
            }
            InconsistentADT {
                a_type,
                a_span,
                b_type,
                b_span,
            } => {
                write!(
                    f,
                    "Inconsistent data types: {} due to `{}` is incompatible with {} due to `{}`",
                    a_type.adt_kind(),
                    fmt_span(a_span),
                    b_type.adt_kind(),
                    fmt_span(b_span)
                )
            }
            InconsistentPattern {
                a_type,
                a_span,
                b_type,
                b_span,
            } => {
                write!(
                    f,
                    "Inconsistent pattern types: {} due to `{}` is incompatible with {} due to `{}`",
                    a_type.name(),
                    fmt_span(a_span),
                    b_type.name(),
                    fmt_span(b_span)
                )
            }
            DuplicatedVariant {
                first_occurrence,
                ctx_span,
                ctx,
                ..
            } => {
                write!(
                    f,
                    "Duplicated variant `{}` in {} `{}`",
                    fmt_span(first_occurrence),
                    ctx.as_str(),
                    fmt_span(ctx_span)
                )
            }
            RecordWildcardPatternNotAtEnd { pattern_span, .. } => {
                write!(
                    f,
                    "Record wildcard pattern .. must be at the end of the pattern in `{}`",
                    fmt_span(pattern_span)
                )
            }
            TraitImplNotFound {
                trait_ref,
                input_tys,
                fn_span,
            } => {
                write!(
                    f,
                    "Implementation of trait `{}` over types `{}` not found (when calling `{}`)",
                    trait_ref,
                    input_tys.join(", "),
                    fmt_span(fn_span)
                )
            }
            MethodsNotPartOfTrait { trait_ref, spans } => {
                write!(
                    f,
                    "Methods `{}` are not part of trait `{}`",
                    spans.iter().map(fmt_span).join(", "),
                    trait_ref
                )
            }
            TraitMethodImplsMissing {
                trait_ref,
                missings,
                impl_span,
            } => {
                write!(
                    f,
                    "Implementation of trait `{}` is missing methods `{}` in `{}`",
                    trait_ref,
                    missings.iter().join(", "),
                    fmt_span(impl_span)
                )
            }
            TraitMethodArgCountMismatch {
                trait_ref,
                method_name,
                expected,
                got,
                args_span,
                ..
            } => {
                write!(
                    f,
                    "Method `{}` of trait `{}` expects {} arguments, but {} are provided in `{}`",
                    method_name,
                    trait_ref,
                    expected,
                    got,
                    fmt_span(args_span)
                )
            }
            IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence,
                pattern_span,
                ..
            } => {
                write!(
                    f,
                    "Identifier `{}` bound more than once in a pattern: `{}`",
                    fmt_span(first_occurrence),
                    fmt_span(pattern_span)
                )
            }
            DuplicatedLiteralPattern {
                first_occurrence,
                match_span,
                ..
            } => {
                write!(
                    f,
                    "Duplicated literal pattern `{}` in match `{}`",
                    fmt_span(first_occurrence),
                    fmt_span(match_span)
                )
            }
            EmptyMatchBody { span } => {
                write!(f, "Match body cannot be empty in `{}`", fmt_span(span))
            }
            NonExhaustivePattern { span, ty } => {
                write!(
                    f,
                    "Non-exhaustive patterns for type `{}`, all possible values must be covered in `{}`",
                    ty,
                    fmt_span(span)
                )
            }
            TypeValuesCannotBeEnumerated { span, ty } => {
                write!(
                    f,
                    "Values of type `{}` cannot be enumerated in `{}`, but all possible values must be known for exhaustive match coverage analysis",
                    ty,
                    fmt_span(span)
                )
            }
            MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            } => {
                write!(
                    f,
                    "Mutable paths overlap: `{}` and `{}` when calling `{}`",
                    fmt_span(a_span),
                    fmt_span(b_span),
                    fmt_span(fn_span),
                )
            }
            UndefinedVarInStringFormatting {
                var_span,
                string_span,
            } => {
                write!(
                    f,
                    "Undefined variable `{}` used in string formatting `{}`",
                    fmt_span(var_span),
                    fmt_span(string_span),
                )
            }
            InvalidEffectDependency {
                source,
                source_span,
                target,
                target_span,
            } => {
                write!(
                    f,
                    "Invalid effect dependency: `{}` due to `{}` is incompatible with `{}` due to `{}`",
                    source,
                    fmt_span(source_span),
                    target,
                    fmt_span(target_span),
                )
            }
            UnknownProperty {
                scope,
                variable,
                cause,
                ..
            } => {
                write!(
                    f,
                    "Unknown {} property: `{}.{}`",
                    cause.as_prefix(),
                    scope,
                    variable
                )
            }
            Unsupported { span, reason } => {
                write!(f, "Unsupported: {} in `{}`", reason, fmt_span(span))
            }
            /*UnresolvedImport {
                function_path,
                span,
            } => {
                write!(f, "Unresolved import: `{}` in `{}`", function_path, fmt_span(span))
            }
            ImportSignatureMismatch {
                function_path,
                expected_signature,
                got_signature,
                span,
            } => {
                write!(
                    f,
                    "Import signature mismatch for `{}`: expected `{}`, got `{}` in `{}`",
                    function_path,
                    expected_signature,
                    got_signature,
                    fmt_span(span)
                )
            }
            CircularImportDependency {
                import_chain,
                span,
            } => {
                write!(
                    f,
                    "Circular import dependency: {} in `{}`",
                    import_chain.join(" -> "),
                    fmt_span(span)
                )
            }*/
            Internal(msg) => write!(f, "ICE: {msg}"),
        }
    }
}

#[macro_export]
macro_rules! compilation_error {
    ($($ctor:tt)*) => {
        CompilationError::new(
            $crate::error::CompilationErrorImpl::$($ctor)*
        )
    };
}

impl CompilationError {
    pub fn resolve_types(
        error: InternalCompilationError,
        env: &ModuleEnv<'_>,
        source: &str,
    ) -> Self {
        use CompilationErrorImpl::*;
        match error.into_inner() {
            ParsingFailed(errors) => compilation_error!(ParsingFailed(errors)),
            NameDefinedMultipleTimes {
                name,
                first_occurrence,
                second_occurrence,
            } => compilation_error!(NameDefinedMultipleTimes {
                name,
                first_occurrence,
                second_occurrence,
            }),
            TypeNotFound(span) => compilation_error!(TypeNotFound(span)),
            TraitNotFound(span) => compilation_error!(TraitNotFound(span)),
            WrongNumberOfArguments {
                expected,
                expected_span,
                got,
                got_span,
            } => compilation_error!(WrongNumberOfArguments {
                expected,
                expected_span,
                got,
                got_span,
            }),
            MutabilityMustBe {
                source_span,
                reason_span,
                what,
                ctx,
            } => {
                let (source_span, reason_span) =
                    resolve_must_be_mutable_ctx(source_span, reason_span, ctx, source);
                compilation_error!(MutabilityMustBe {
                    source_span,
                    reason_span,
                    what,
                    ctx
                })
            }
            TypeMismatch {
                current_ty,
                current_span,
                expected_ty,
                expected_span,
                sub_or_same,
            } => compilation_error!(TypeMismatch {
                current_ty: current_ty.format_with(env).to_string(),
                current_span,
                expected_ty: expected_ty.format_with(env).to_string(),
                expected_span,
                sub_or_same,
            }),
            NamedTypeMismatch {
                current_decl,
                current_span,
                expected_decl,
                expected_span,
            } => compilation_error!(NamedTypeMismatch {
                current_decl: (current_decl.name.to_string(), current_decl.span),
                current_span,
                expected_decl: (expected_decl.name.to_string(), expected_decl.span),
                expected_span,
            }),
            InfiniteType(ty_var, ty, span) => {
                compilation_error!(InfiniteType(
                    ty_var.to_string(),
                    ty.format_with(env).to_string(),
                    span
                ))
            }
            UnboundTypeVar { ty_var, ty, span } => compilation_error!(UnboundTypeVar {
                ty_var: ty_var.to_string(),
                ty: ty.format_with(env).to_string(),
                span,
            }),
            UnresolvedConstraints { constraints, span } => {
                compilation_error!(UnresolvedConstraints {
                    constraints: constraints
                        .iter()
                        .map(|c| c.format_with(env).to_string())
                        .collect(),
                    span,
                })
            }
            InvalidTupleIndex {
                index,
                index_span,
                tuple_length,
                tuple_span,
            } => compilation_error!(InvalidTupleIndex {
                index,
                index_span,
                tuple_length,
                tuple_span,
            }),
            InvalidTupleProjection {
                expr_ty,
                expr_span,
                index_span,
            } => compilation_error!(InvalidTupleProjection {
                expr_ty: expr_ty.format_with(env).to_string(),
                expr_span,
                index_span,
            }),
            DuplicatedField {
                first_occurrence,
                second_occurrence,
                constructor_span,
                ctx,
            } => compilation_error!(DuplicatedField {
                first_occurrence,
                second_occurrence,
                constructor_span,
                ctx,
            }),
            InvalidRecordField {
                field_span,
                record_ty,
                record_span,
            } => compilation_error!(InvalidRecordField {
                field_span,
                record_ty: record_ty.format_with(env).to_string(),
                record_span,
            }),
            InvalidRecordFieldAccess {
                field_span,
                record_ty,
                record_span,
            } => compilation_error!(InvalidRecordFieldAccess {
                field_span,
                record_ty: record_ty.format_with(env).to_string(),
                record_span,
            }),
            InvalidVariantName { name, ty, .. } => compilation_error!(InvalidVariantName {
                name,
                ty: ty.format_with(env).to_string(),
                valid: ty
                    .data()
                    .as_variant()
                    .unwrap()
                    .iter()
                    .map(|(name, _)| name.to_string())
                    .collect(),
            }),
            InvalidVariantType { name, ty } => compilation_error!(InvalidVariantType {
                name,
                ty: ty.format_with(env).to_string(),
            }),
            InvalidVariantConstructor { span } => {
                compilation_error!(InvalidVariantConstructor { span })
            }
            ReturnOutsideFunction { span } => {
                compilation_error!(ReturnOutsideFunction { span })
            }
            IsNotCorrectProductType {
                which,
                type_def,
                what,
                instantiation_span,
            } => compilation_error!(IsNotCorrectProductType {
                which,
                type_def: (type_def.name.to_string(), type_def.span),
                what,
                instantiation_span,
            }),
            InvalidStructField {
                type_def,
                field_name,
                field_span,
                instantiation_span,
            } => compilation_error!(InvalidStructField {
                type_def: (type_def.name.to_string(), type_def.span),
                field_name,
                field_span,
                instantiation_span,
            }),
            MissingStructField {
                type_def,
                field_name,
                instantiation_span,
            } => compilation_error!(MissingStructField {
                type_def: (type_def.name.to_string(), type_def.span),
                field_name,
                instantiation_span,
            }),
            InconsistentADT {
                a_type,
                a_span,
                b_type,
                b_span,
            } => compilation_error!(InconsistentADT {
                a_type,
                a_span,
                b_type,
                b_span,
            }),
            InconsistentPattern {
                a_type,
                a_span,
                b_type,
                b_span,
            } => compilation_error!(InconsistentPattern {
                a_type,
                a_span,
                b_type,
                b_span,
            }),
            DuplicatedVariant {
                first_occurrence,
                second_occurrence,
                ctx_span,
                ctx,
            } => compilation_error!(DuplicatedVariant {
                first_occurrence,
                second_occurrence,
                ctx_span,
                ctx
            }),
            RecordWildcardPatternNotAtEnd {
                pattern_span,
                wildcard_span,
            } => {
                compilation_error!(RecordWildcardPatternNotAtEnd {
                    pattern_span,
                    wildcard_span
                })
            }
            TraitImplNotFound {
                trait_ref,
                input_tys,
                fn_span,
            } => compilation_error!(TraitImplNotFound {
                trait_ref: trait_ref.name.to_string(),
                input_tys: input_tys
                    .iter()
                    .zip(trait_ref.input_type_names.iter())
                    .map(|(ty, name)| format!("{name} = {}", ty.format_with(env)))
                    .collect(),
                fn_span,
            }),
            MethodsNotPartOfTrait { trait_ref, spans } => {
                compilation_error!(MethodsNotPartOfTrait {
                    trait_ref: trait_ref.name.to_string(),
                    spans
                })
            }
            TraitMethodImplsMissing {
                trait_ref,
                missings,
                impl_span,
            } => compilation_error!(TraitMethodImplsMissing {
                trait_ref: trait_ref.name.to_string(),
                missings,
                impl_span,
            }),
            TraitMethodArgCountMismatch {
                trait_ref,
                method_name,
                method_index,
                expected,
                got,
                args_span,
            } => compilation_error!(TraitMethodArgCountMismatch {
                trait_ref: trait_ref.name.to_string(),
                method_name,
                method_index,
                expected,
                got,
                args_span,
            }),
            IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence,
                second_occurrence,
                pattern_span,
            } => compilation_error!(IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence,
                second_occurrence,
                pattern_span,
            }),
            DuplicatedLiteralPattern {
                first_occurrence,
                second_occurrence,
                match_span,
            } => compilation_error!(DuplicatedLiteralPattern {
                first_occurrence,
                second_occurrence,
                match_span,
            }),
            EmptyMatchBody { span: cond_span } => {
                compilation_error!(EmptyMatchBody { span: cond_span })
            }
            NonExhaustivePattern { span, ty } => compilation_error!(NonExhaustivePattern {
                span,
                ty: ty.format_with(env).to_string(),
            }),
            TypeValuesCannotBeEnumerated { span, ty } => {
                compilation_error!(TypeValuesCannotBeEnumerated {
                    span,
                    ty: ty.format_with(env).to_string(),
                })
            }
            MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            } => compilation_error!(MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            }),
            UndefinedVarInStringFormatting {
                var_span,
                string_span,
            } => compilation_error!(UndefinedVarInStringFormatting {
                var_span,
                string_span,
            }),
            InvalidEffectDependency {
                source,
                source_span,
                target,
                target_span,
            } => compilation_error!(InvalidEffectDependency {
                source,
                source_span,
                target,
                target_span,
            }),
            UnknownProperty {
                scope,
                variable,
                cause,
                span,
            } => compilation_error!(UnknownProperty {
                scope,
                variable,
                cause,
                span,
            }),
            Unsupported { span, reason } => compilation_error!(Unsupported { span, reason }),
            /*UnresolvedImport {
                function_path,
                span,
            } => compilation_error!(UnresolvedImport {
                function_path,
                span,
            }),
            ImportSignatureMismatch {
                function_path,
                expected_signature,
                got_signature,
                span,
            } => compilation_error!(ImportSignatureMismatch {
                function_path,
                expected_signature,
                got_signature,
                span,
            }),
            CircularImportDependency { import_chain, span } => {
                compilation_error!(CircularImportDependency { import_chain, span })
            }*/
            Internal(msg) => compilation_error!(Internal(msg)),
        }
    }

    pub fn expect_name_defined_multiple_times(&self, name: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            NameDefinedMultipleTimes { name: n, .. } => {
                if *n == name {
                    return;
                }
                panic!(
                    "expect_name_defined_multiple_times failed: expected \"{}\", got \"{}\"",
                    name, n
                );
            }
            _ => panic!(
                "expect_name_defined_multiple_times called on non-NameDefinedMultipleTimes error {self:?}"
            ),
        }
    }

    pub fn expect_wrong_number_of_arguments(&self, expected: usize, got: usize) {
        use CompilationErrorImpl::*;
        match self.deref() {
            WrongNumberOfArguments {
                expected: exp,
                got: g,
                ..
            } => {
                if exp == &expected && g == &got {
                    return;
                }
                panic!(
                    "expect_wrong_number_of_arguments failed: expected {} != {}, got {} != {}",
                    exp, g, expected, got
                );
            }
            _ => panic!(
                "expect_wrong_number_of_arguments called on non-WrongNumberOfArguments error {self:?}"
            ),
        }
    }

    pub fn expect_mutability_must_be(&self, should_be: MutabilityMustBeWhat) {
        let is_what = self
            .as_mutability_must_be()
            .unwrap_or_else(|| {
                panic!("expect_mutability_must_be called on non-MutabilityMustBe error {self:?}")
            })
            .2;
        if *is_what != should_be {
            panic!(
                "expect_mutability_must_be failed: expected {:?}, got {:?}",
                should_be, is_what
            );
        }
    }

    pub fn expect_type_mismatch(&self, cur_ty: &str, exp_ty: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            TypeMismatch {
                current_ty,
                expected_ty,
                ..
            } => {
                if current_ty == cur_ty && expected_ty == exp_ty {
                    return;
                }
                panic!(
                    "expect_type_mismatch failed: expected \"{}\" ≰ \"{}\", got \"{}\" ≰ \"{}\"",
                    cur_ty, exp_ty, current_ty, expected_ty
                );
            }
            _ => panic!("expect_type_mismatch called on non-TypeMismatch error {self:?}"),
        }
    }

    pub fn expect_unbound_ty_var(&self) {
        use CompilationErrorImpl::*;
        // TODO: once ty_var normalization is implemented, pass the ty_var as parameter
        match self.deref() {
            UnboundTypeVar { .. } => (),
            _ => panic!("expect_unbound_ty_val called on non-UnboundTypeVar error {self:?}"),
        }
    }

    pub fn expect_duplicate_record_field(&self, src: &str, exp_name: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            DuplicatedField {
                first_occurrence: first_occurrence_span,
                ..
            } => {
                let name =
                    src[first_occurrence_span.start()..first_occurrence_span.end()].to_string();
                if name == exp_name {
                } else {
                    panic!(
                        "expect_duplicate_record_field failed: expected \"{}\", got \"{}\"",
                        exp_name, name
                    );
                }
            }
            _ => panic!(
                "expect_duplicate_record_field called on non-DuplicatedRecordField error {self:?}"
            ),
        }
    }

    pub fn expect_inconsistent_adt(&self) {
        use CompilationErrorImpl::*;
        match self.deref() {
            InconsistentADT { .. } => (),
            _ => panic!("expect_inconsistent_adt called on non-InconsistentADT error {self:?}"),
        }
    }

    pub fn expect_duplicated_variant(&self, src: &str, exp_name: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            DuplicatedVariant {
                first_occurrence: first_occurrence_span,
                ..
            } => {
                let name = &src[first_occurrence_span.start()..first_occurrence_span.end()];
                if name == exp_name {
                } else {
                    panic!(
                        "expect_duplicated_variant failed: expected \"{}\", got \"{}\"",
                        exp_name, name
                    );
                }
            }
            _ => panic!("expect_duplicated_variant called on non-DuplicatedVariant error {self:?}"),
        }
    }

    pub fn expect_mutable_paths_overlap(&self) {
        use CompilationErrorImpl::*;
        match self.deref() {
            MutablePathsOverlap { .. } => (),
            _ => panic!(
                "expect_mutable_paths_overlap called on non-MutablePathsOverlap error {self:?}"
            ),
        }
    }

    pub fn expect_undefined_var_in_string_formatting(&self, src: &str, exp_name: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            UndefinedVarInStringFormatting { var_span, .. } => {
                let var_name = &src[var_span.start()..var_span.end()];
                if var_name == exp_name {
                } else {
                    panic!(
                        "expect_undefined_var_in_string_formatting failed: expected \"{}\", got \"{}\"",
                        exp_name, var_name
                    );
                }
            }
            _ => panic!(
                "expect_undefined_var_in_string_formatting called on non-UndefinedVarInStringFormatting error {self:?}"
            ),
        }
    }

    pub fn expect_invalid_effect_dependency(&self, cur_eff: EffType, target_eff: EffType) {
        use CompilationErrorImpl::*;
        match self.deref() {
            InvalidEffectDependency { source, target, .. } => {
                if source == &cur_eff && target == &target_eff {
                    return;
                }
                panic!(
                    "expect_invalid_effect_dependency failed: expected {} ≰ {}, got {} ≰ {}",
                    cur_eff, target_eff, source, target
                );
            }
            _ => panic!(
                "expect_invalid_effect_dependency called on non-InvalidEffectDependency error {self:?}"
            ),
        }
    }

    pub fn expect_trait_impl_not_found(&self, trait_name: &str, tys: &[&str]) {
        use CompilationErrorImpl::*;
        match self.deref() {
            TraitImplNotFound {
                trait_ref: name,
                input_tys,
                ..
            } => {
                if name == trait_name
                    && input_tys
                        .iter()
                        .map(|ty| ty.as_str())
                        .eq(tys.iter().copied())
                {
                    return;
                }
                panic!(
                    "expect_trait_impl_not_found failed: expected {} over {:?}, got {} over {:?}",
                    trait_name, tys, name, input_tys
                );
            }
            _ => {
                panic!("expect_trait_impl_not_found called on non-TraitImplNotFound error {self:?}")
            }
        }
    }

    pub fn expect_return_outside_function(&self) {
        use CompilationErrorImpl::*;
        match self.deref() {
            ReturnOutsideFunction { .. } => (),
            _ => panic!(
                "expect_return_outside_function called on non-ReturnOutsideFunction error {self:?}"
            ),
        }
    }
}

/// Runtime error

#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum RuntimeError {
    Aborted(Option<String>),
    DivisionByZero,
    RemainderByZero,
    InvalidArgument(Ustr),
    ArrayAccessOutOfBounds { index: isize, len: usize },
    RecursionLimitExceeded { limit: usize },
    // TODO: add execution duration limit exhausted
}

impl Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RuntimeError::*;
        match self {
            Aborted(msg) => match msg {
                Some(msg) => write!(f, "Aborted: {msg}"),
                None => write!(f, "Aborted"),
            },
            DivisionByZero => write!(f, "Division by zero"),
            RemainderByZero => write!(f, "Remainder by zero"),
            InvalidArgument(reason) => write!(f, "Invalid argument: {reason}"),
            ArrayAccessOutOfBounds { index, len } => {
                write!(
                    f,
                    "Array access out of bounds: index {index} for length {len}"
                )
            }
            RecursionLimitExceeded { limit } => {
                write!(f, "Recursion limit exceeded: limit is {limit}")
            }
        }
    }
}

pub fn resolve_must_be_mutable_ctx(
    current_span: Location,
    reason_span: Location,
    ctx: MutabilityMustBeContext,
    src: &str,
) -> (Location, Location) {
    match ctx {
        MutabilityMustBeContext::Value => (current_span, reason_span),
        MutabilityMustBeContext::FnTypeArg(index) => {
            // FIXME: this should probably be done later on when the source is available anyway
            if reason_span.module().is_none() {
                let arg_span = extract_ith_fn_arg(src, reason_span, index);
                (arg_span, current_span)
            } else {
                (current_span, reason_span)
            }
        }
    }
}

pub fn extract_ith_fn_arg(src: &str, span: Location, index: usize) -> Location {
    let fn_text = &src[span.start()..span.end()];
    let bytes = fn_text.as_bytes();
    let mut count = 0;
    let mut args_start = fn_text.len();

    // Iterate backwards through the string within the span to find the start of the argument list
    for i in (0..fn_text.len()).rev() {
        match bytes[i] as char {
            ')' => count += 1,
            '(' => {
                count -= 1;
                if count == 0 {
                    args_start = i;
                    break;
                }
            }
            _ => {}
        }
    }

    // Extracting the arguments from the located position
    if args_start == fn_text.len() {
        return span;
    }
    let args_section = &fn_text[args_start + 1..fn_text.len() - 1]; // Strip the outer parentheses
    let mut arg_count = 0;
    let mut start = 0;

    count = 0; // Reset count for argument extraction
    for (i, char) in args_section.char_indices() {
        match char {
            '(' => count += 1,
            ')' => count -= 1,
            ',' if count == 0 => {
                if arg_count == index {
                    return Location::new_local(
                        span.start() + args_start + 1 + start,
                        span.start() + args_start + 1 + i,
                    );
                }
                arg_count += 1;
                start = i + 1;
            }
            _ => {}
        }
    }

    // Handling the last argument
    if arg_count == index && start < args_section.len() {
        return Location::new_local(
            span.start() + args_start + 1 + start,
            span.start() + args_start + 1 + args_section.len(),
        );
    }

    panic!("Argument {index} not found");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extract_ith_fn_arg_single() {
        let src = "(|x| x)((1+2))";
        let span = Location::new_local(0, src.len());
        let expected = ["(1+2)"];
        for (index, expected) in expected.into_iter().enumerate() {
            let arg_span = super::extract_ith_fn_arg(src, span, index);
            assert_eq!(&src[arg_span.start()..arg_span.end()], expected);
        }
    }

    #[test]
    fn extract_ith_fn_arg_multi() {
        let src = "(|x,y| x*y)(12, (1 + 3))";
        let span = Location::new_local(0, src.len());
        let expected = ["12", " (1 + 3)"];
        for (index, expected) in expected.into_iter().enumerate() {
            let arg_span = super::extract_ith_fn_arg(src, span, index);
            assert_eq!(&src[arg_span.start()..arg_span.end()], expected);
        }
    }
}
