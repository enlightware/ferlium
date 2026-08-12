// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! MIR block terminators and their control-flow contracts.

use std::fmt;

use crate::{
    Location,
    format::FormatWith,
    mir::{self, Operation},
    module::ModuleEnv,
};

/// The single control-flow exit of a MIR basic block.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Terminator {
    /// The source region associated with the transfer.
    pub span: Location,

    /// The kind-specific transfer and its successors.
    pub kind: TerminatorKind,
}

impl Terminator {
    pub fn goto(span: Location, target: mir::BlockId) -> Self {
        Self {
            span,
            kind: TerminatorKind::Goto { target },
        }
    }

    pub fn cond_br(
        span: Location,
        condition: mir::Value,
        then_target: mir::BlockId,
        else_target: mir::BlockId,
    ) -> Self {
        Self {
            span,
            kind: TerminatorKind::CondBr {
                condition,
                then_target,
                else_target,
            },
        }
    }

    pub fn invoke(
        span: Location,
        operation: Operation,
        normal: mir::BlockId,
        error: mir::BlockId,
    ) -> Self {
        Self {
            span,
            kind: TerminatorKind::Invoke {
                operation,
                normal,
                error,
            },
        }
    }

    pub fn r#yield(span: Location, place: mir::Value, resume: mir::BlockId) -> Self {
        Self {
            span,
            kind: TerminatorKind::Yield { place, resume },
        }
    }

    pub fn ret(span: Location) -> Self {
        Self {
            span,
            kind: TerminatorKind::Return,
        }
    }

    pub fn propagate_error(span: Location) -> Self {
        Self {
            span,
            kind: TerminatorKind::PropagateError,
        }
    }

    pub fn failure_during_cleanup(span: Location) -> Self {
        Self {
            span,
            kind: TerminatorKind::FailureDuringCleanup,
        }
    }

    /// Whether two terminators are the same, with the operands of an invoked operation compared by
    /// `operand_eq` rather than directly. See [`Operation::eq_by_operands`].
    ///
    /// Only [`TerminatorKind::Invoke`] can carry an operand naming a function, so every other form
    /// is compared by the derived equality — complete by construction, and a form that later gained
    /// one would compare its operand directly and refuse a match rather than invent one.
    pub(crate) fn eq_by_operands(
        &self,
        other: &Self,
        operand_eq: &impl Fn(&mir::Value, &mir::Value) -> bool,
    ) -> bool {
        let Self { span, kind } = self;
        if *span != other.span {
            return false;
        }
        match (kind, &other.kind) {
            (
                TerminatorKind::Invoke {
                    operation,
                    normal,
                    error,
                },
                TerminatorKind::Invoke {
                    operation: other_operation,
                    normal: other_normal,
                    error: other_error,
                },
            ) => {
                normal == other_normal
                    && error == other_error
                    && operation.eq_by_operands(other_operation, operand_eq)
            }
            (kind, other) => kind == other,
        }
    }

    /// Visits every value operand used directly by this terminator, including operands of an
    /// invoked operation.
    pub fn operands(&self) -> &[mir::Value] {
        match &self.kind {
            TerminatorKind::CondBr { condition, .. } => std::slice::from_ref(condition),
            TerminatorKind::Invoke { operation, .. } => &operation.operands,
            TerminatorKind::Yield { place, .. } => std::slice::from_ref(place),
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup => &[],
        }
    }
}

/// Control-flow forms of canonical MIR.
#[derive(Clone, PartialEq, Eq, Hash, strum::EnumDiscriminants)]
#[strum_discriminants(
    name(TerminatorKindDiscriminant),
    derive(Hash, PartialOrd, Ord, strum::Display),
    strum(serialize_all = "snake_case")
)]
pub enum TerminatorKind {
    Goto {
        target: mir::BlockId,
    },
    CondBr {
        condition: mir::Value,
        then_target: mir::BlockId,
        else_target: mir::BlockId,
    },
    /// Execute one source-fallible operation and select its normal or source-error successor.
    Invoke {
        operation: Operation,
        normal: mir::BlockId,
        error: mir::BlockId,
    },
    /// Suspend a scoped accessor and continue at `resume` when its driver ends the projection.
    Yield {
        place: mir::Value,
        resume: mir::BlockId,
    },
    Return,
    /// Continue propagating the source failure currently in flight to the caller.
    PropagateError,
    /// Poison execution after a cleanup action raised while another source failure was in flight.
    FailureDuringCleanup,
}

impl FormatWith<ModuleEnv<'_>> for Terminator {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        match &self.kind {
            TerminatorKind::Goto { target } => write!(f, "br b{}", target.as_u32()),
            TerminatorKind::CondBr {
                condition,
                then_target,
                else_target,
            } => write!(
                f,
                "condbr {}, b{}, b{}",
                condition.format_with(env),
                then_target.as_u32(),
                else_target.as_u32()
            ),
            TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } => {
                write!(f, "invoke {}", operation.format_with(env))?;
                write!(f, " -> b{} error b{}", normal.as_u32(), error.as_u32())
            }
            TerminatorKind::Yield { place, resume } => write!(
                f,
                "yield {} -> b{}",
                place.format_with(env),
                resume.as_u32()
            ),
            TerminatorKind::Return => write!(f, "ret"),
            TerminatorKind::PropagateError => write!(f, "propagate_error"),
            TerminatorKind::FailureDuringCleanup => write!(f, "failure_during_cleanup"),
        }
    }
}
