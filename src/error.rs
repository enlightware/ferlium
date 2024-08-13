use std::fmt::{self, Display};

use lrpar::Span;

use crate::{
    format::FormatWith,
    module::{FmtWithModuleEnv, ModuleEnv},
    r#type::{Type, TypeVar},
};

pub type LocatedError = (String, Span);

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
        expr_ty: Type,
        expr_span: Span,
        index_span: Span,
    },
    MutablePathsOverlap {
        a_span: Span,
        b_span: Span,
        fn_span: Span,
    },
    Internal(String),
}

impl fmt::Display for FormatWith<'_, InternalCompilationError, (ModuleEnv<'_>, &str)> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (env, source) = self.data;
        use InternalCompilationError::*;
        match self.value {
            SymbolNotFound(span) => {
                let name = &source[span.start()..span.end()];
                write!(f, "Variable or function not found: {}", name)
            }
            FunctionNotFound(span) => {
                let name = &source[span.start()..span.end()];
                write!(f, "Function not found: {}", name)
            }
            MustBeMutable(current_span, reason_span, ctx) => {
                let (current_span, reason_span) =
                    resolve_must_be_mutable_ctx(*current_span, *reason_span, *ctx, source);
                let current_name = &source[current_span.start()..current_span.end()];
                let reason_name = &source[reason_span.start()..reason_span.end()];
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
            InvalidTupleProjection { expr_ty, .. } => {
                write!(f, "Expected tuple, got \"{}\"", expr_ty.format_with(env))
            }
            MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            } => {
                write!(
                    f,
                    "Mutable paths overlap: {} and {} when calling {}",
                    &source[a_span.start()..a_span.end()],
                    &source[b_span.start()..b_span.end()],
                    &source[fn_span.start()..fn_span.end()],
                )
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
    MutablePathsOverlap {
        a_name: String,
        a_span: Span,
        b_name: String,
        b_span: Span,
        fn_name: String,
        fn_span: Span,
    },
    Internal(String),
}

impl CompilationError {
    pub fn from_internal(error: InternalCompilationError, env: &ModuleEnv<'_>, src: &str) -> Self {
        use InternalCompilationError::*;
        match error {
            SymbolNotFound(span) => {
                let name = &src[span.start()..span.end()];
                Self::VariableNotFound(name.to_string(), span)
            }
            FunctionNotFound(span) => {
                let name = &src[span.start()..span.end()];
                Self::FunctionNotFound(name.to_string(), span)
            }
            MustBeMutable(current_span, reason_span, ctx) => {
                let (current_span, reason_span) =
                    resolve_must_be_mutable_ctx(current_span, reason_span, ctx, src);
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
                expr_ty,
                expr_span,
                index_span,
            } => Self::InvalidTupleProjection {
                expr_ty: expr_ty.format_with(env).to_string(),
                expr_span,
                index_span,
            },
            MutablePathsOverlap {
                a_span,
                b_span,
                fn_span,
            } => Self::MutablePathsOverlap {
                a_name: src[a_span.start()..a_span.end()].to_string(),
                a_span,
                b_name: src[b_span.start()..b_span.end()].to_string(),
                b_span,
                fn_name: src[fn_span.start()..fn_span.end()].to_string(),
                fn_span,
            },
            Internal(msg) => Self::Internal(msg),
        }
    }

    pub fn expect_must_be_mutable(&self) {
        match self {
            Self::MustBeMutable(_, _) => (),
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

    pub fn expect_mutable_paths_overlap(&self) {
        match self {
            Self::MutablePathsOverlap { .. } => (),
            _ => panic!("expect_mutable_paths_overlap called on non-MutablePathsOverlap error"),
        }
    }
}

/// Runtime error

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeError {
    DivisionByZero,
    RemainderByZero,
    ArrayAccessOutOfBounds { index: isize, len: usize },
    RecursionLimitExceeded { limit: usize },
    // TODO: add execution duration limit exhausted
}

impl Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RuntimeError::*;
        match self {
            DivisionByZero => write!(f, "Division by zero"),
            RemainderByZero => write!(f, "Remainder by zero"),
            ArrayAccessOutOfBounds { index, len } => {
                write!(f, "Array access out of bounds: index {} for length {}", index, len)
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
            let arg_span = extract_ith_fn_arg(src, reason_span, index);
            (arg_span, current_span)
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
                    return Span::new(
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
        return Span::new(
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
        let span = Span::new(0, src.len());
        let expected = ["(1+2)"];
        for (index, expected) in expected.into_iter().enumerate() {
            let arg_span = super::extract_ith_fn_arg(src, span, index);
            assert_eq!(&src[arg_span.start()..arg_span.end()], expected);
        }
    }

    #[test]
    fn extract_ith_fn_arg_multi() {
        let src = "(|x,y| x*y)(12, (1 + 3))";
        let span = Span::new(0, src.len());
        let expected = ["12", " (1 + 3)"];
        for (index, expected) in expected.into_iter().enumerate() {
            let arg_span = super::extract_ith_fn_arg(src, span, index);
            assert_eq!(&src[arg_span.start()..arg_span.end()], expected);
        }
    }
}
