// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! First-class subscript lifecycle lowering.

use crate::mir::{OperationKind, edit::FunctionEdit};

/// Refine semantic member selection into an ephemeral borrow of the owned subscript environment.
pub(super) fn lower_members(edit: &mut FunctionEdit) {
    let blocks = edit.blocks().collect::<Vec<_>>();
    for block in blocks {
        for operation in &mut edit.block_mut(block).operations {
            let OperationKind::SubscriptMember { mut_member, ty } = operation.kind else {
                continue;
            };
            operation.kind = OperationKind::BorrowSubscriptMember { mut_member, ty };
        }
    }
}
