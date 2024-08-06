use std::fmt;

use lrpar::Span;

use crate::{
    format::FormatWith,
    module::{FmtWithModuleEnv, ModuleEnv},
    r#type::{Type, TypeVar},
};

pub type LocatedError = (String, Span);

/// Compilation error, for internal use
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InternalCompilationError {
    VariableNotFound(Span),
    FunctionNotFound(Span),
    MustBeMutable(Span),
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
        expr_ty: Type,
        expr_span: Span,
        index_span: Span,
    },
    Internal(String),
}

impl fmt::Display for FormatWith<'_, InternalCompilationError, (ModuleEnv<'_>, &str)> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (env, source) = self.data;
        use InternalCompilationError::*;
        match self.value {
            VariableNotFound(span) => {
                let name = &source[span.start()..span.end()];
                write!(f, "Variable not found: {}", name)
            }
            FunctionNotFound(span) => {
                let name = &source[span.start()..span.end()];
                write!(f, "Function not found: {}", name)
            }
            MustBeMutable(span) => {
                let name = &source[span.start()..span.end()];
                write!(f, "Expression must be mutable: {}", name)
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
            InvalidTupleProjection { expr_ty, .. } => {
                write!(f, "Expected tuple, got \"{}\"", expr_ty.format_with(env))
            }
            Internal(msg) => write!(f, "ICE: {}", msg),
        }
    }
}

/// Compilation error, for external use
#[derive(Debug)]
pub enum CompilationError {
    ParsingFailed(Vec<LocatedError>),
    VariableNotFound(String, Span),
    FunctionNotFound(String, Span),
    MustBeMutable(Span),
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
    Internal(String),
}

impl CompilationError {
    pub fn from_internal(error: InternalCompilationError, env: &ModuleEnv<'_>, src: &str) -> Self {
        use InternalCompilationError::*;
        match error {
            VariableNotFound(span) => {
                let name = &src[span.start()..span.end()];
                Self::VariableNotFound(name.to_string(), span)
            }
            FunctionNotFound(span) => {
                let name = &src[span.start()..span.end()];
                Self::FunctionNotFound(name.to_string(), span)
            }
            MustBeMutable(span) => Self::MustBeMutable(span),
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
                expr_ty,
                expr_span,
                index_span,
            } => Self::InvalidTupleProjection {
                expr_ty: expr_ty.format_with(env).to_string(),
                expr_span,
                index_span,
            },
            Internal(msg) => Self::Internal(msg),
        }
    }

    pub fn expect_must_be_mutable(&self) {
        match self {
            Self::MustBeMutable(_) => (),
            _ => panic!("expect_must_be_mutable called on non-MustBeMutable error"),
        }
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
            _ => panic!("expect_is_not_subtype called on non-TypeMismatch error"),
        }
    }

    pub fn expect_unbound_ty_var(&self) {
        // TODO: once ty_var normalization is implemented, pass the ty_var as parameter
        match self {
            Self::UnboundTypeVar { .. } => (),
            _ => panic!("expect_unbound_ty_val called on non-UnboundTypeVar error"),
        }
    }
}

/// Runtime error

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeError {
    DivisionByZero,
    RemainderByZero,
    ArrayAccessOutOfBounds { index: isize, len: usize },
    // TODO: add execution duration limit exhausted
    // TODO: add stack overflow
}
