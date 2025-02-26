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
    fmt::{self, Display},
    ops::Deref,
};

use crate::{
    location::Location, r#trait::TraitRef, type_inference::SubOrSameType,
    type_scheme::PubTypeConstraint,
};
use enum_as_inner::EnumAsInner;
use itertools::Itertools;
use ustr::Ustr;

use crate::{
    ast::{PatternType, PropertyAccess},
    effects::EffType,
    format::FormatWith,
    module::{FmtWithModuleEnv, ModuleEnv},
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

/// Compilation error, for internal use
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InternalCompilationErrorImpl {
    SymbolNotFound(Location),
    FunctionNotFound(Location),
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
        current_ty: Type,
        current_span: Location,
        expected_ty: Type,
        expected_span: Location,
        sub_or_same: SubOrSameType,
    },
    InfiniteType(TypeVar, Type, Location),
    UnboundTypeVar {
        ty_var: TypeVar,
        ty: Type,
        span: Location,
    },
    UnresolvedConstraints {
        constraints: Vec<PubTypeConstraint>,
        span: Location,
    },
    InvalidTupleIndex {
        index: usize,
        index_span: Location,
        tuple_length: usize,
        tuple_span: Location,
    },
    InvalidTupleProjection {
        tuple_ty: Type,
        tuple_span: Location,
        index_span: Location,
    },
    DuplicatedRecordField {
        first_occurrence: Location,
        second_occurrence: Location,
    },
    InvalidRecordField {
        field_span: Location,
        record_ty: Type,
        record_span: Location,
    },
    InvalidRecordFieldAccess {
        field_span: Location,
        record_ty: Type,
        record_span: Location,
    },
    InvalidVariantName {
        name: Location,
        ty: Type,
    },
    InvalidVariantType {
        name: Location,
        ty: Type,
    },
    InvalidVariantConstructor {
        span: Location,
        // Only one error type for now: a path was used as a variant constructor
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
    },
    TraitImplNotFound {
        trait_ref: TraitRef,
        input_tys: Vec<Type>,
        fn_span: Location,
    },
    IdentifierBoundMoreThanOnceInAPattern {
        first_occurrence: Location,
        second_occurrence: Location,
    },
    DuplicatedLiteralPattern {
        first_occurrence: Location,
        second_occurrence: Location,
    },
    NonExhaustivePattern {
        span: Location,
        ty: Type,
        // TODO: have a generic way to talk about the non-covered values
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
    Internal(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InternalCompilationError(Box<InternalCompilationErrorImpl>);

impl InternalCompilationError {
    pub fn new(error: InternalCompilationErrorImpl) -> Self {
        Self(Box::new(error))
    }

    pub fn into_inner(self) -> InternalCompilationErrorImpl {
        *self.0
    }
}

impl Deref for InternalCompilationError {
    type Target = InternalCompilationErrorImpl;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[macro_export]
macro_rules! internal_compilation_error {
    ($($ctor:tt)*) => {
        InternalCompilationError::new(
            $crate::error::InternalCompilationErrorImpl::$($ctor)*
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

impl fmt::Display for FormatWith<'_, InternalCompilationError, (ModuleEnv<'_>, &str)> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (env, source) = self.data;
        let fmt_span = |loc: &Location| match loc.module() {
            Some(module) => format!(
                "{}..{} in module {}",
                module.span().start(),
                module.span().end(),
                module.module_name()
            ),
            None => source[loc.start()..loc.end()].to_string(),
        };
        use InternalCompilationErrorImpl::*;
        match self.value.deref() {
            SymbolNotFound(span) => {
                write!(f, "Variable or function not found: {}", fmt_span(span))
            }
            FunctionNotFound(span) => {
                write!(f, "Function not found: {}", fmt_span(span))
            }
            WrongNumberOfArguments { expected, got, .. } => {
                write!(
                    f,
                    "Wrong number of arguments: expected {}, got {}",
                    expected, got
                )
            }
            MutabilityMustBe {
                source_span,
                reason_span,
                what,
                ctx,
            } => {
                let (source_span, reason_span) =
                    resolve_must_be_mutable_ctx(*source_span, *reason_span, *ctx, source);
                let source_name = fmt_span(&source_span);
                let reason_name = fmt_span(&reason_span);
                use MutabilityMustBeWhat::*;
                let what = match what {
                    Mutable => "mutable due to",
                    Constant => "constant due to",
                    Equal => "of same mutability to",
                };
                write!(
                    f,
                    "Expression \"{source_name}\" must be {what} \"{reason_name}\""
                )
            }
            TypeMismatch {
                current_ty,
                expected_ty,
                sub_or_same,
                ..
            } => write!(
                f,
                "Type \"{}\" is not {} \"{}\"",
                current_ty.format_with(env),
                match sub_or_same {
                    SubOrSameType::SubType => "a sub-type of",
                    SubOrSameType::SameType => "the same type as",
                },
                expected_ty.format_with(env)
            ),
            InfiniteType(ty_var, ty, _span) => {
                write!(f, "Infinite type: {} = \"{}\"", ty_var, ty.format_with(env))
            }
            UnboundTypeVar { ty_var, ty, .. } => {
                write!(
                    f,
                    "Unbound type variable {} in {}",
                    ty_var,
                    ty.format_with(env)
                )
            }
            UnresolvedConstraints { constraints, span } => {
                let constraints = constraints.iter().map(|c| c.format_with(env)).join(" ∧ ");
                write!(
                    f,
                    "Unresolved constraints {} in expression {}",
                    constraints,
                    fmt_span(span)
                )
            }
            InvalidTupleIndex {
                index,
                tuple_length,
                ..
            } => {
                write!(
                    f,
                    "Invalid index {index} of a tuple of length {tuple_length}"
                )
            }
            InvalidTupleProjection {
                tuple_ty: expr_ty, ..
            } => {
                write!(f, "Expected tuple, got \"{}\"", expr_ty.format_with(env))
            }
            DuplicatedRecordField {
                first_occurrence: first_occurrence_span,
                ..
            } => {
                write!(
                    f,
                    "Duplicated record field: {}",
                    fmt_span(first_occurrence_span),
                )
            }
            InvalidRecordField {
                field_span,
                record_ty,
                ..
            } => {
                write!(
                    f,
                    "Field {} not found in record {}",
                    fmt_span(field_span),
                    record_ty.format_with(env)
                )
            }
            InvalidRecordFieldAccess {
                field_span,
                record_ty,
                ..
            } => {
                write!(
                    f,
                    "Expected record due to {}, got \"{}\"",
                    fmt_span(field_span),
                    record_ty.format_with(env)
                )
            }
            InvalidVariantName { name, ty } => {
                let valids = ty
                    .data()
                    .as_variant()
                    .unwrap()
                    .iter()
                    .map(|(name, _)| name.as_ref())
                    .join(", ");
                write!(
                    f,
                    "Variant name {} does not exist for variant type {}, valid names are {}",
                    fmt_span(name),
                    ty.format_with(env),
                    valids,
                )
            }
            InvalidVariantType { name, ty } => {
                write!(
                    f,
                    "Type {} is not a variant, but variant constructor {} requires it",
                    ty.format_with(env),
                    fmt_span(name),
                )
            }
            InvalidVariantConstructor { span } => {
                write!(
                    f,
                    "Variant constructor cannot be paths, but {} is",
                    fmt_span(span),
                )
            }
            InconsistentADT {
                a_type,
                b_type,
                a_span,
                b_span,
            } => {
                write!(
                    f,
                    "Inconsistent data types: {} due to .{} is incompatible with {} due to .{}",
                    a_type.adt_kind(),
                    fmt_span(a_span),
                    b_type.adt_kind(),
                    fmt_span(b_span),
                )
            }
            InconsistentPattern {
                a_type,
                b_type,
                a_span,
                b_span,
            } => {
                write!(
                    f,
                    "Inconsistent pattern types: {} due to {} is incompatible with {} due to {}",
                    a_type.name(),
                    fmt_span(a_span),
                    b_type.name(),
                    fmt_span(b_span),
                )
            }
            DuplicatedVariant {
                first_occurrence: first_occurrence_span,
                ..
            } => {
                write!(f, "Duplicated variant: {}", fmt_span(first_occurrence_span),)
            }
            TraitImplNotFound {
                trait_ref,
                input_tys,
                fn_span,
            } => {
                write!(
                    f,
                    "Implementation of trait {} over types {} not found (when calling {})",
                    trait_ref.name,
                    input_tys
                        .iter()
                        .map(|ty| ty.format_with(env).to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    fmt_span(fn_span),
                )
            }
            IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence: first_occurrence_span,
                ..
            } => {
                write!(
                    f,
                    "Identifier {} bound more than once in a pattern",
                    fmt_span(first_occurrence_span),
                )
            }
            DuplicatedLiteralPattern {
                first_occurrence, ..
            } => {
                write!(
                    f,
                    "Duplicated literal pattern: {}",
                    fmt_span(first_occurrence),
                )
            }
            EmptyMatchBody { .. } => {
                write!(f, "Match body cannot be empty")
            }
            NonExhaustivePattern { ty, .. } => {
                write!(
                    f,
                    "Non-exhaustive patterns for type {}, all possible values must be covered.",
                    ty.format_with(env)
                )
            }
            MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            } => {
                write!(
                    f,
                    "Mutable paths overlap: {} and {} when calling {}",
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
                    "Undefined variable {} used in string formatting {}",
                    fmt_span(var_span),
                    fmt_span(string_span),
                )
            }
            InvalidEffectDependency {
                source: cur,
                source_span,
                target,
                target_span,
            } => {
                write!(
                    f,
                    "Invalid effect dependency: {} due to {} is incompatible with {} due to {}",
                    cur,
                    fmt_span(source_span),
                    target,
                    fmt_span(target_span),
                )
            }
            UnknownProperty {
                scope, variable, ..
            } => {
                write!(f, "Unknown property: {}.{}", scope, variable,)
            }
            Unsupported { span, reason } => {
                write!(f, "Unsupported: {} at {}", reason, fmt_span(span))
            }
            Internal(msg) => write!(f, "ICE: {}", msg),
        }
    }
}

/// Compilation error, for external use
#[derive(Debug, EnumAsInner)]
pub enum CompilationErrorImpl {
    ParsingFailed(Vec<LocatedError>),
    VariableNotFound(Location),
    FunctionNotFound(Location),
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
    },
    TypeMismatch {
        current_ty: String,
        current_span: Location,
        expected_ty: String,
        expected_span: Location,
        sub_or_same: SubOrSameType,
    },
    InfiniteType(String, String, Location),
    UnboundTypeVar {
        ty_var: String,
        ty: String,
        span: Location,
    },
    UnresolvedConstraints {
        constraints: Vec<String>,
        span: Location,
    },
    InvalidTupleIndex {
        index: usize,
        index_span: Location,
        tuple_length: usize,
        tuple_span: Location,
    },
    InvalidTupleProjection {
        expr_ty: String,
        expr_span: Location,
        index_span: Location,
    },
    DuplicatedRecordField {
        first_occurrence: Location,
        second_occurrence: Location,
    },
    InvalidRecordField {
        field_span: Location,
        record_ty: String,
        record_span: Location,
    },
    InvalidRecordFieldAccess {
        field_span: Location,
        record_ty: String,
        record_span: Location,
    },
    InvalidVariantName {
        name: Location,
        ty: String,
        valids: Vec<String>,
    },
    InvalidVariantType {
        name: Location,
        ty: String,
    },
    InvalidVariantConstructor {
        span: Location,
    },
    InconsistentADT {
        a_type: ADTAccessType,
        a_span: Location,
        b_type: ADTAccessType,
        b_span: Location,
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
    },
    TraitImplNotFound {
        trait_name: String,
        input_tys: Vec<String>,
        fn_span: Location,
    },
    IdentifierBoundMoreThanOnceInAPattern {
        first_occurrence: Location,
        second_occurrence: Location,
    },
    DuplicatedLiteralPattern {
        first_occurrence: Location,
        second_occurrence: Location,
    },
    EmptyMatchBody {
        span: Location,
    },
    NonExhaustivePattern {
        span: Location,
        ty: String,
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
    Internal(String),
}

#[derive(Debug)]
pub struct CompilationError(Box<CompilationErrorImpl>);

impl CompilationError {
    pub fn new(error: CompilationErrorImpl) -> Self {
        Self(Box::new(error))
    }

    pub fn into_inner(self) -> CompilationErrorImpl {
        *self.0
    }
}

impl Deref for CompilationError {
    type Target = CompilationErrorImpl;

    fn deref(&self) -> &Self::Target {
        &self.0
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
    pub fn from_internal(
        error: InternalCompilationError,
        env: &ModuleEnv<'_>,
        source: &str,
    ) -> Self {
        use InternalCompilationErrorImpl::*;
        match error.into_inner() {
            SymbolNotFound(span) => compilation_error!(VariableNotFound(span)),
            FunctionNotFound(span) => compilation_error!(FunctionNotFound(span)),
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
                    what
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
                tuple_ty: expr_ty,
                tuple_span: expr_span,
                index_span,
            } => compilation_error!(InvalidTupleProjection {
                expr_ty: expr_ty.format_with(env).to_string(),
                expr_span,
                index_span,
            }),
            DuplicatedRecordField {
                first_occurrence,
                second_occurrence,
            } => compilation_error!(DuplicatedRecordField {
                first_occurrence,
                second_occurrence,
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
            InvalidVariantName { name, ty } => compilation_error!(InvalidVariantName {
                name,
                ty: ty.format_with(env).to_string(),
                valids: ty
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
            } => compilation_error!(DuplicatedVariant {
                first_occurrence,
                second_occurrence,
            }),
            TraitImplNotFound {
                trait_ref,
                input_tys,
                fn_span,
            } => compilation_error!(TraitImplNotFound {
                trait_name: trait_ref.name.to_string(),
                input_tys: input_tys
                    .iter()
                    .map(|ty| ty.format_with(env).to_string())
                    .collect(),
                fn_span,
            }),
            IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence,
                second_occurrence,
            } => compilation_error!(IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence,
                second_occurrence,
            }),
            DuplicatedLiteralPattern {
                first_occurrence,
                second_occurrence,
            } => compilation_error!(DuplicatedLiteralPattern {
                first_occurrence,
                second_occurrence,
            }),
            EmptyMatchBody { span: cond_span } => {
                compilation_error!(EmptyMatchBody { span: cond_span })
            }
            NonExhaustivePattern { span, ty } => compilation_error!(NonExhaustivePattern {
                span,
                ty: ty.format_with(env).to_string(),
            }),
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
            Internal(msg) => compilation_error!(Internal(msg)),
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
            _ => panic!("expect_wrong_number_of_arguments called on non-WrongNumberOfArguments error {self:?}"),
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
            DuplicatedRecordField {
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
            },
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
            },
            _ => panic!(
                "expect_invalid_effect_dependency called on non-InvalidEffectDependency error {self:?}"
            ),
        }
    }

    pub fn expect_trait_impl_not_found(&self, trait_name: &str, tys: &[&str]) {
        use CompilationErrorImpl::*;
        match self.deref() {
            TraitImplNotFound {
                trait_name: name,
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
                Some(msg) => write!(f, "Aborted: {}", msg),
                None => write!(f, "Aborted"),
            },
            DivisionByZero => write!(f, "Division by zero"),
            RemainderByZero => write!(f, "Remainder by zero"),
            InvalidArgument(reason) => write!(f, "Invalid argument: {reason}"),
            ArrayAccessOutOfBounds { index, len } => {
                write!(
                    f,
                    "Array access out of bounds: index {} for length {}",
                    index, len
                )
            }
            RecursionLimitExceeded { limit } => {
                write!(f, "Recursion limit exceeded: limit is {}", limit)
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
