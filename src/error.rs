use std::{
    fmt::{self, Display},
    ops::Deref,
};

use crate::location::Location;
use enum_as_inner::EnumAsInner;
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
pub enum MustBeMutableContext {
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
    MustBeMutable(Location, Location, MustBeMutableContext),
    IsNotSubtype(Type, Location, Type, Location),
    InfiniteType(TypeVar, Type, Location),
    UnboundTypeVar {
        ty_var: TypeVar,
        ty: Type,
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
            MustBeMutable(current_span, reason_span, ctx) => {
                let (current_span, reason_span) =
                    resolve_must_be_mutable_ctx(*current_span, *reason_span, *ctx, source);
                let current_name = fmt_span(&current_span);
                let reason_name = fmt_span(&reason_span);
                write!(
                    f,
                    "Expression \"{current_name}\" must be mutable due to \"{reason_name}\""
                )
            }
            IsNotSubtype(cur, _cur_span, exp, _exp_span) => write!(
                f,
                "Type \"{}\" is not a sub-type of \"{}\"",
                cur.format_with(env),
                exp.format_with(env)
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
                write!(
                    f,
                    "Variant name {} does not exist for variant type {}",
                    fmt_span(name),
                    ty.format_with(env)
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
    MustBeMutable(Location, Location),
    IsNotSubtype(String, Location, String, Location),
    InfiniteType(String, String, Location),
    UnboundTypeVar {
        ty_var: String,
        ty: String,
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
            MustBeMutable(current_span, reason_span, ctx) => {
                let (current_span, reason_span) =
                    resolve_must_be_mutable_ctx(current_span, reason_span, ctx, source);
                compilation_error!(MustBeMutable(current_span, reason_span))
            }
            IsNotSubtype(cur, cur_span, exp, exp_span) => compilation_error!(IsNotSubtype(
                cur.format_with(env).to_string(),
                cur_span,
                exp.format_with(env).to_string(),
                exp_span,
            )),
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

    pub fn expect_must_be_mutable(&self) {
        self.as_must_be_mutable().unwrap_or_else(|| {
            panic!("expect_must_be_mutable called on non-MustBeMutable error {self:?}")
        });
    }

    pub fn expect_is_not_subtype(&self, cur_ty: &str, exp_ty: &str) {
        use CompilationErrorImpl::*;
        match self.deref() {
            IsNotSubtype(cur, _, exp, _) => {
                if cur == cur_ty && exp == exp_ty {
                    return;
                }
                panic!(
                    "expect_is_not_subtype failed: expected \"{}\" ≰ \"{}\", got \"{}\" ≰ \"{}\"",
                    cur_ty, exp_ty, cur, exp
                );
            }
            _ => panic!("expect_is_not_subtype called on non-IsNotSubtype error {self:?}"),
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
}

/// Runtime error

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeError {
    Aborted,
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
            Aborted => write!(f, "Aborted"),
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
    ctx: MustBeMutableContext,
    src: &str,
) -> (Location, Location) {
    match ctx {
        MustBeMutableContext::Value => (current_span, reason_span),
        MustBeMutableContext::FnTypeArg(index) => {
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
