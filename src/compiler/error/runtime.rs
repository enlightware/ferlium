// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::fmt::{self, Display};

use enum_as_inner::EnumAsInner;

/// A failure declared by Ferlium's `Fallible` source effect.
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum SourceFailureKind {
    Aborted(Option<String>),
    DivisionByZero,
    RemainderByZero,
    InvalidArgument(String),
}

impl Display for SourceFailureKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SourceFailureKind::*;
        match self {
            Aborted(msg) => match msg {
                Some(msg) => write!(f, "Aborted: {msg}"),
                None => write!(f, "Aborted"),
            },
            DivisionByZero => write!(f, "Division by zero"),
            RemainderByZero => write!(f, "Remainder by zero"),
            InvalidArgument(reason) => write!(f, "Invalid argument: {reason}"),
        }
    }
}

/// A host-enforced resource limit that terminates and poisons an execution domain.
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum SandboxViolationKind {
    CallDepthLimitExceeded { limit: usize },
    EnvironmentCellLimitExceeded { limit: usize },
    StackByteLimitExceeded { limit: usize },
    FuelExhausted,
}

impl Display for SandboxViolationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SandboxViolationKind::*;
        match self {
            CallDepthLimitExceeded { limit } => {
                write!(f, "Call depth limit exceeded: limit is {limit}")
            }
            EnvironmentCellLimitExceeded { limit } => {
                write!(
                    f,
                    "Interpreter environment cell limit exceeded: limit is {limit}"
                )
            }
            StackByteLimitExceeded { limit } => {
                write!(f, "Execution stack byte limit exceeded: limit is {limit}")
            }
            FuelExhausted => write!(f, "Execution fuel exhausted"),
        }
    }
}

/// Stable summary of the structurally distinct outcomes carried by `RuntimeError`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeErrorKind {
    /// The selected backend could not prepare or execute the artifact; not a source effect.
    Backend,
    SourceFailure(SourceFailureKind),
    SandboxViolation(SandboxViolationKind),
    FailureDuringCleanup,
    /// A source failure escaped a function whose type says it cannot fail (through `effects_unsafe`).
    EffectViolation,
}

impl Display for RuntimeErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Backend => f.write_str("Execution backend error"),
            Self::SourceFailure(kind) => kind.fmt(f),
            Self::SandboxViolation(kind) => kind.fmt(f),
            Self::FailureDuringCleanup => {
                f.write_str("A second source failure occurred during cleanup")
            }
            Self::EffectViolation => {
                f.write_str("A source failure escaped a function that cannot fail")
            }
        }
    }
}
