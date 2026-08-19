// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Where an operation sits in a body.
//!
//! Almost every pass has to name a position it plans to rewrite, and a position is not an identity:
//! MIR operations carry none, so a pass records where one *is* and must not hold that across an
//! edit that shifts it. Construction-time diagnostics name an insertion point the same way.

use std::fmt;

use crate::{mir::BlockId, module::id::Id};

crate::define_id_type!(
    /// A transient position in one block's operation vector, not a stable MIR identity.
    ///
    /// A block's terminator takes the index one past the last operation, for the passes that need
    /// to name it in the same space.
    OperationIndex
);

/// An operation's position: which block, and where in it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct OperationSite {
    pub(crate) block: BlockId,
    pub(crate) index: OperationIndex,
}

impl fmt::Display for OperationSite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "block b{} operation {}",
            self.block.as_u32(),
            self.index.as_index()
        )
    }
}
