// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

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
