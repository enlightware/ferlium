// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Compiler-owned callable identities. Execution belongs to the interpreters and backends.

use std::fmt;

use crate::{
    eval::{EvalCtx, EvalResult, ValOrMut},
    hir::function::{ArgConvention, Callable},
    module::{ELocalDecl, ModuleEnv},
};

const LET: ArgConvention = ArgConvention::Let;
const MUTABLE_REF: ArgConvention = ArgConvention::MutableRef;

pub(crate) const INVALID_BUFFER_CLONE: &str =
    "Buffer::clone should never be called; arrays must clone their initialized elements";

/// Private typed-storage operations used by `Array<T>` and Buffer's trait implementations.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BufferPrimitive {
    /// Return a place rooted in the buffer argument, without reading the selected element.
    Slot,
    /// Allocate fixed-capacity storage with all element slots uninitialized.
    WithCapacity,
    /// Transfer one element into an uninitialized slot, leaving its source uninitialized.
    MoveInto,
    /// Release the target storage, transfer ownership, and leave an empty buffer in the source.
    Move,
    /// Transfer an element to the result, leaving its slot uninitialized.
    Take,
    Equal,
    ToString,
    Hash,
    Clone,
    /// Release storage after its elements have been consumed, and clear the owning slot.
    Drop,
}

impl BufferPrimitive {
    /// Storage intrinsics expanded at direct physical call sites.
    pub(crate) fn is_storage(self) -> bool {
        matches!(
            self,
            Self::Slot | Self::WithCapacity | Self::MoveInto | Self::Move | Self::Take | Self::Drop
        )
    }
}

impl Callable for BufferPrimitive {
    fn call(&self, _args: Vec<ValOrMut>, _ctx: &mut EvalCtx) -> EvalResult {
        unreachable!("Buffer primitives must be dispatched by the interpreter")
    }
    fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
        Some(match self {
            Self::Slot | Self::Take => &[MUTABLE_REF, LET, LET],
            Self::WithCapacity => &[LET, LET, LET],
            Self::MoveInto => &[MUTABLE_REF, LET, MUTABLE_REF, LET, LET],
            Self::Move => &[MUTABLE_REF, MUTABLE_REF],
            Self::Equal => &[LET, LET],
            Self::ToString | Self::Clone => &[LET],
            Self::Hash => &[LET, MUTABLE_REF],
            Self::Drop => &[MUTABLE_REF],
        })
    }
    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        _: &[ELocalDecl],
        _: &ModuleEnv,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result {
        write!(
            f,
            "{}{}Buffer::{self:?}",
            "  ".repeat(spacing),
            "⎸ ".repeat(indent)
        )
    }
}
