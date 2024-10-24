use std::fmt::{self, Display};

use crate::span::Span;
use enum_as_inner::EnumAsInner;
use ustr::Ustr;

use crate::{
    ast::{PatternType, PropertyAccess},
    effects::EffType,
    format::FormatWith,
    module::{FmtWithModuleEnv, ModuleEnv},
    r#type::{Type, TypeVar},
};

pub type LocatedError = (String, Span);

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
pub enum InternalCompilationError {
    SymbolNotFound(Span),
    FunctionNotFound(Span),
    WrongNumberOfArguments {
        expected: usize,
        expected_span: Span,
        got: usize,
        got_span: Span,
    },
    MustBeMutable(Span, Span, MustBeMutableContext),
    IsNotSubtype(Type, Span, Type, Span),
    InfiniteType(TypeVar, Type, Span),
    UnboundTypeVar {
        ty_var: TypeVar,
        ty: Type,
        span: Span,
    },
    InvalidTupleIndex {
        index: usize,
        index_span: Span,
        tuple_length: usize,
        tuple_span: Span,
    },
    InvalidTupleProjection {
        tuple_ty: Type,
        tuple_span: Span,
        index_span: Span,
    },
    DuplicatedRecordField {
        first_occurrence: Span,
        second_occurrence: Span,
    },
    InvalidRecordField {
        field_span: Span,
        record_ty: Type,
        record_span: Span,
    },
    InvalidRecordFieldAccess {
        field_span: Span,
        record_ty: Type,
        record_span: Span,
    },
    InvalidVariantName {
        name: Span,
        ty: Type,
    },
    InvalidVariantType {
        name: Span,
        ty: Type,
    },
    InconsistentADT {
        a_type: ADTAccessType,
        a_span: Span,
        b_type: ADTAccessType,
        b_span: Span,
    },
    InconsistentPattern {
        a_type: PatternType,
        a_span: Span,
        b_type: PatternType,
        b_span: Span,
    },
    DuplicatedVariant {
        first_occurrence: Span,
        second_occurrence: Span,
    },
    IdentifierBoundMoreThanOnceInAPattern {
        first_occurrence: Span,
        second_occurrence: Span,
    },
    MutablePathsOverlap {
        a_span: Span,
        b_span: Span,
        fn_span: Span,
    },
    UndefinedVarInStringFormatting {
        var_span: Span,
        string_span: Span,
    },
    InvalidEffectDependency {
        source: EffType,
        source_span: Span,
        target: EffType,
        target_span: Span,
    },
    UnknownProperty {
        scope: Ustr,
        variable: Ustr,
        cause: PropertyAccess,
        span: Span,
    },
    Internal(String),
}
impl InternalCompilationError {
    pub fn new_inconsistent_adt(
        mut a_type: ADTAccessType,
        mut a_span: Span,
        mut b_type: ADTAccessType,
        mut b_span: Span,
    ) -> Self {
        if a_span.start() > b_span.start() {
            std::mem::swap(&mut a_type, &mut b_type);
            std::mem::swap(&mut a_span, &mut b_span);
        }
        Self::InconsistentADT {
            a_type,
            a_span,
            b_type,
            b_span,
        }
    }
}

impl fmt::Display for FormatWith<'_, InternalCompilationError, (ModuleEnv<'_>, &str)> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (env, source) = self.data;
        let fmt_span = |span: &Span| match span.module() {
            Some(module) => format!("{}..{} in module {}", span.start(), span.end(), module),
            None => source[span.start()..span.end()].to_string(),
        };
        use InternalCompilationError::*;
        match self.value {
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
pub enum CompilationError {
    ParsingFailed(Vec<LocatedError>),
    VariableNotFound(Span),
    FunctionNotFound(Span),
    WrongNumberOfArguments {
        expected: usize,
        expected_span: Span,
        got: usize,
        got_span: Span,
    },
    MustBeMutable(Span, Span),
    IsNotSubtype(String, Span, String, Span),
    InfiniteType(String, String, Span),
    UnboundTypeVar {
        ty_var: String,
        ty: String,
        span: Span,
    },
    InvalidTupleIndex {
        index: usize,
        index_span: Span,
        tuple_length: usize,
        tuple_span: Span,
    },
    InvalidTupleProjection {
        expr_ty: String,
        expr_span: Span,
        index_span: Span,
    },
    DuplicatedRecordField {
        first_occurrence: Span,
        second_occurrence: Span,
    },
    InvalidRecordField {
        field_span: Span,
        record_ty: String,
        record_span: Span,
    },
    InvalidRecordFieldAccess {
        field_span: Span,
        record_ty: String,
        record_span: Span,
    },
    InvalidVariantName {
        name: Span,
        ty: String,
        valids: Vec<String>,
    },
    InvalidVariantType {
        name: Span,
        ty: String,
    },
    InconsistentADT {
        a_type: ADTAccessType,
        a_span: Span,
        b_type: ADTAccessType,
        b_span: Span,
    },
    InconsistentPattern {
        a_type: PatternType,
        a_span: Span,
        b_type: PatternType,
        b_span: Span,
    },
    DuplicatedVariant {
        first_occurrence: Span,
        second_occurrence: Span,
    },
    IdentifierBoundMoreThanOnceInAPattern {
        first_occurrence: Span,
        second_occurrence: Span,
    },
    MutablePathsOverlap {
        a_span: Span,
        b_span: Span,
        fn_span: Span,
    },
    UndefinedVarInStringFormatting {
        var_span: Span,
        string_span: Span,
    },
    InvalidEffectDependency {
        source: EffType,
        source_span: Span,
        target: EffType,
        target_span: Span,
    },
    UnknownProperty {
        scope: Ustr,
        variable: Ustr,
        cause: PropertyAccess,
        span: Span,
    },
    Internal(String),
}

impl CompilationError {
    pub fn from_internal(
        error: InternalCompilationError,
        env: &ModuleEnv<'_>,
        source: &str,
    ) -> Self {
        use InternalCompilationError::*;
        match error {
            SymbolNotFound(span) => Self::VariableNotFound(span),
            FunctionNotFound(span) => Self::FunctionNotFound(span),
            WrongNumberOfArguments {
                expected,
                expected_span,
                got,
                got_span,
            } => Self::WrongNumberOfArguments {
                expected,
                expected_span,
                got,
                got_span,
            },
            MustBeMutable(current_span, reason_span, ctx) => {
                let (current_span, reason_span) =
                    resolve_must_be_mutable_ctx(current_span, reason_span, ctx, source);
                Self::MustBeMutable(current_span, reason_span)
            }
            IsNotSubtype(cur, cur_span, exp, exp_span) => Self::IsNotSubtype(
                cur.format_with(env).to_string(),
                cur_span,
                exp.format_with(env).to_string(),
                exp_span,
            ),
            InfiniteType(ty_var, ty, span) => {
                Self::InfiniteType(ty_var.to_string(), ty.format_with(env).to_string(), span)
            }
            UnboundTypeVar { ty_var, ty, span } => Self::UnboundTypeVar {
                ty_var: ty_var.to_string(),
                ty: ty.format_with(env).to_string(),
                span,
            },
            InvalidTupleIndex {
                index,
                index_span,
                tuple_length,
                tuple_span,
            } => Self::InvalidTupleIndex {
                index,
                index_span,
                tuple_length,
                tuple_span,
            },
            InvalidTupleProjection {
                tuple_ty: expr_ty,
                tuple_span: expr_span,
                index_span,
            } => Self::InvalidTupleProjection {
                expr_ty: expr_ty.format_with(env).to_string(),
                expr_span,
                index_span,
            },
            DuplicatedRecordField {
                first_occurrence,
                second_occurrence,
            } => Self::DuplicatedRecordField {
                first_occurrence,
                second_occurrence,
            },
            InvalidRecordField {
                field_span,
                record_ty,
                record_span,
            } => Self::InvalidRecordField {
                field_span,
                record_ty: record_ty.format_with(env).to_string(),
                record_span,
            },
            InvalidRecordFieldAccess {
                field_span,
                record_ty,
                record_span,
            } => Self::InvalidRecordFieldAccess {
                field_span,
                record_ty: record_ty.format_with(env).to_string(),
                record_span,
            },
            InvalidVariantName { name, ty } => Self::InvalidVariantName {
                name,
                ty: ty.format_with(env).to_string(),
                valids: ty
                    .data()
                    .as_variant()
                    .unwrap()
                    .iter()
                    .map(|(name, _)| name.to_string())
                    .collect(),
            },
            InvalidVariantType { name, ty } => Self::InvalidVariantType {
                name,
                ty: ty.format_with(env).to_string(),
            },
            InconsistentADT {
                a_type,
                a_span,
                b_type,
                b_span,
            } => Self::InconsistentADT {
                a_type,
                a_span,
                b_type,
                b_span,
            },
            InconsistentPattern {
                a_type,
                a_span,
                b_type,
                b_span,
            } => Self::InconsistentPattern {
                a_type,
                a_span,
                b_type,
                b_span,
            },
            DuplicatedVariant {
                first_occurrence,
                second_occurrence,
            } => Self::DuplicatedVariant {
                first_occurrence,
                second_occurrence,
            },
            IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence,
                second_occurrence,
            } => Self::IdentifierBoundMoreThanOnceInAPattern {
                first_occurrence,
                second_occurrence,
            },
            MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            } => Self::MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            },
            UndefinedVarInStringFormatting {
                var_span,
                string_span,
            } => Self::UndefinedVarInStringFormatting {
                var_span,
                string_span,
            },
            InvalidEffectDependency {
                source,
                source_span,
                target,
                target_span,
            } => Self::InvalidEffectDependency {
                source,
                source_span,
                target,
                target_span,
            },
            UnknownProperty {
                scope,
                variable,
                cause,
                span,
            } => Self::UnknownProperty {
                scope,
                variable,
                cause,
                span,
            },
            Internal(msg) => Self::Internal(msg),
        }
    }

    pub fn expect_wrong_number_of_arguments(&self, expected: usize, got: usize) {
        match self {
            Self::WrongNumberOfArguments {
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
        match self {
            Self::IsNotSubtype(cur, _, exp, _) => {
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
        // TODO: once ty_var normalization is implemented, pass the ty_var as parameter
        match self {
            Self::UnboundTypeVar { .. } => (),
            _ => panic!("expect_unbound_ty_val called on non-UnboundTypeVar error {self:?}"),
        }
    }

    pub fn expect_duplicate_record_field(&self, src: &str, exp_name: &str) {
        match self {
            Self::DuplicatedRecordField {
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
        match self {
            Self::InconsistentADT { .. } => (),
            _ => panic!("expect_inconsistent_adt called on non-InconsistentADT error {self:?}"),
        }
    }

    pub fn expect_duplicated_variant(&self, src: &str, exp_name: &str) {
        match self {
            Self::DuplicatedVariant {
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
        match self {
            Self::MutablePathsOverlap { .. } => (),
            _ => panic!(
                "expect_mutable_paths_overlap called on non-MutablePathsOverlap error {self:?}"
            ),
        }
    }

    pub fn expect_undefined_var_in_string_formatting(&self, src: &str, exp_name: &str) {
        match self {
            Self::UndefinedVarInStringFormatting { var_span, .. } => {
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
        match self {
            Self::InvalidEffectDependency { source, target, .. } => {
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
    current_span: Span,
    reason_span: Span,
    ctx: MustBeMutableContext,
    src: &str,
) -> (Span, Span) {
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

pub fn extract_ith_fn_arg(src: &str, span: Span, index: usize) -> Span {
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
                    return Span::new_local(
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
        return Span::new_local(
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
        let span = Span::new_local(0, src.len());
        let expected = ["(1+2)"];
        for (index, expected) in expected.into_iter().enumerate() {
            let arg_span = super::extract_ith_fn_arg(src, span, index);
            assert_eq!(&src[arg_span.start()..arg_span.end()], expected);
        }
    }

    #[test]
    fn extract_ith_fn_arg_multi() {
        let src = "(|x,y| x*y)(12, (1 + 3))";
        let span = Span::new_local(0, src.len());
        let expected = ["12", " (1 + 3)"];
        for (index, expected) in expected.into_iter().enumerate() {
            let arg_span = super::extract_ith_fn_arg(src, span, index);
            assert_eq!(&src[arg_span.start()..arg_span.end()], expected);
        }
    }
}
