// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Specialization and inlining may leave a guarded body with no way to call script code.

use crate::{
    mir::{Function, OperationKind, edit::FunctionEdit, terminator::TerminatorKind},
    module::{FunctionId, ModuleEnv},
};

pub(super) fn remove_leaf_checks(body: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let native = |id: FunctionId| {
        env.module_by_id(id.module)
            .and_then(|module| module.get_function_by_id(id.function))
            .is_some_and(|function| function.code.native_entry().is_some())
    };
    let mut has_check = false;
    for id in body.blocks() {
        let block = body.block(id);
        if matches!(block.terminator().kind, TerminatorKind::Yield { .. }) {
            return None;
        }
        let invoke = match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        for operation in block.operations().iter().chain(invoke) {
            has_check |= operation.kind == OperationKind::CheckCallDepth;
            if !super::will_return::operation_calls_only(operation, &native) {
                return None;
            }
        }
    }
    if !has_check {
        return None;
    }
    let mut edit = FunctionEdit::new(body.clone());
    for id in body.blocks() {
        edit.block_mut(id)
            .operations
            .retain(|operation| operation.kind != OperationKind::CheckCallDepth);
    }
    Some(edit.finish(env))
}
