// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Scalar call arguments read at the call.
//!
//! The ABI passes a read-only argument of a concrete scalar type by value, and semantic MIR may
//! too (see [`accepts_value_argument`]). This pass reads each such argument passed as a place into
//! a value just before its call. The read the callee made through the place becomes an ordinary
//! `load` of the caller, which the caller's passes see: LICM hoists one that a loop does not
//! change, where a read inside a call that also takes the loop's cursor was invisible to it.
//!
//! The rewrite preserves meaning because a `Let` argument cannot change during the call:
//! overlapping mutable arguments are invalid, so the callee observes the value the place holds at
//! the call.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    mir::{
        self, Function, Operation, OperationKind, ValueId,
        edit::FunctionEdit,
        operation::{OperationResult, accepts_value_argument},
        role::{MirType, ValueRole, ValueRoles},
        terminator::TerminatorKind,
    },
    types::r#type::Type,
};

/// Reads every scalar place argument of a `call` into a value before it, or `None` if there is
/// none.
pub(crate) fn read_scalar_arguments(func: &Function) -> Option<Function> {
    let roles = ValueRoles::derive(func);
    // A place of a refined type, such as `raw_float` read as `float`, keeps passing as a place: its
    // value would not have the argument's type.
    let holds = |operand: &mir::Value, ty: Type| {
        roles.get(operand, func.constants()).is_some_and(|role| {
            role.is_place_operand() && role.place_pointee_type() == Some(MirType::Lowered(ty))
        })
    };
    let reads_of = |operation: &Operation| -> Vec<usize> {
        let OperationKind::Call { ty, metadata } = &operation.kind else {
            return Vec::new();
        };
        let visible_start = operation.operands.len()
            - ty.fn_ty.args.len()
            - usize::from(ty.result_convention.has_result_place());
        (0..ty.fn_ty.args.len())
            .filter(|&offset| {
                accepts_value_argument(ty, metadata.as_deref(), offset)
                    && holds(
                        &operation.operands[visible_start + offset],
                        ty.fn_ty.args[offset].ty,
                    )
            })
            .map(|offset| visible_start + offset)
            .collect()
    };
    let changed = func.blocks().any(|block| {
        let block = func.block(block);
        let invoked = match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        block
            .operations()
            .iter()
            .chain(invoked)
            .any(|operation| !reads_of(operation).is_empty())
    });
    if !changed {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    let blocks = edit.blocks().collect::<Vec<_>>();
    for block in blocks {
        let operations = std::mem::take(&mut edit.block_mut(block).operations);
        let mut rewritten = Vec::with_capacity(operations.len());
        for mut operation in operations {
            let reads = reads_of(&operation);
            read_before(&mut edit, &mut operation, &reads, &mut rewritten);
            rewritten.push(operation);
        }
        let mut terminator = edit.block(block).terminator.clone();
        if let TerminatorKind::Invoke { operation, .. } = &mut terminator.kind {
            let reads = reads_of(operation);
            read_before(&mut edit, operation, &reads, &mut rewritten);
        }
        let block = edit.block_mut(block);
        block.operations = rewritten;
        block.terminator = terminator;
    }
    Some(edit.finish_unverified())
}

/// Appends a `load` of each operand at `reads` to `operations`, and passes its value instead.
fn read_before(
    edit: &mut FunctionEdit,
    call: &mut Operation,
    reads: &[usize],
    operations: &mut Vec<Operation>,
) {
    for &index in reads {
        let mut load = Operation::load(call.span, call.operands[index].clone());
        let value = edit
            .assign_new_result(&mut load)
            .expect("a load defines its value");
        operations.push(load);
        call.operands[index] = value;
    }
}

/// Passes every scalar value argument of a `call` as a place again, the inverse of
/// [`read_scalar_arguments`], for consumers that bind every argument to a place, such as
/// physical lowering. `None` if no call passes a value.
///
/// A value loaded in the call's block, with nothing but other loads in between, is replaced by the
/// place it was loaded from, and the load is dropped when nothing else reads it: the call reads
/// that place as it did before normalization. Any other value, such as a load LICM hoisted, is
/// stored into a frame slot of its own in the entry block, just before the call, which the Wasm
/// emitter keeps in a local.
pub(crate) fn spill_value_arguments(func: &Function) -> Option<Function> {
    if !may_pass_values(func) {
        return None;
    }
    let roles = ValueRoles::derive(func);
    let spills_of = |operation: &Operation| -> Vec<usize> {
        let OperationKind::Call { ty, metadata } = &operation.kind else {
            return Vec::new();
        };
        let visible_start = operation.operands.len()
            - ty.fn_ty.args.len()
            - usize::from(ty.result_convention.has_result_place());
        (0..ty.fn_ty.args.len())
            .filter(|&offset| accepts_value_argument(ty, metadata.as_deref(), offset))
            .map(|offset| visible_start + offset)
            .filter(|&index| {
                roles
                    .get(&operation.operands[index], func.constants())
                    .is_some_and(|role| {
                        matches!(*role, ValueRole::Materialized(MirType::Lowered(_)))
                    })
            })
            .collect()
    };
    let changed = func.blocks().any(|block| {
        let block = func.block(block);
        let invoked = match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        block
            .operations()
            .iter()
            .chain(invoked)
            .any(|operation| !spills_of(operation).is_empty())
    });
    if !changed {
        return None;
    }

    let mut uses = FxHashMap::<ValueId, usize>::default();
    for block in func.blocks() {
        let block = func.block(block);
        let operands = block
            .operations()
            .iter()
            .flat_map(|operation| operation.operands.iter())
            .chain(block.terminator().operands());
        for operand in operands {
            if let mir::Value::Register(id) = operand {
                *uses.entry(*id).or_default() += 1;
            }
        }
    }

    let mut edit = FunctionEdit::new(func.clone());
    let mut slots = Vec::new();
    let blocks = edit.blocks().collect::<Vec<_>>();
    for block in blocks {
        let operations = std::mem::take(&mut edit.block_mut(block).operations);
        let mut rewritten: Vec<Option<Operation>> = Vec::with_capacity(operations.len());
        for mut operation in operations {
            let spills = spills_of(&operation);
            spill_before(
                &mut edit,
                &mut operation,
                &spills,
                &mut rewritten,
                &mut slots,
                &mut uses,
            );
            rewritten.push(Some(operation));
        }
        let mut terminator = edit.block(block).terminator.clone();
        if let TerminatorKind::Invoke { operation, .. } = &mut terminator.kind {
            let spills = spills_of(operation);
            spill_before(
                &mut edit,
                operation,
                &spills,
                &mut rewritten,
                &mut slots,
                &mut uses,
            );
        }
        let block = edit.block_mut(block);
        block.operations = rewritten.into_iter().flatten().collect();
        block.terminator = terminator;
    }
    let entry = edit.entry();
    let operations = &mut edit.block_mut(entry).operations;
    operations.splice(0..0, slots);
    Some(edit.finish_unverified())
}

/// Whether some call may pass a scalar argument as a value: a constant, or a register whose
/// definition may yield a value, such as a `load`, a comparison, or a load's uses forwarded to the
/// value stored. A syntactic filter, so that a body without one, such as raw MIR, derives no roles;
/// it may admit a body that passes none, never miss one that does.
fn may_pass_values(func: &Function) -> bool {
    let values = func
        .blocks()
        .flat_map(|block| func.block(block).operations())
        .filter(|operation| {
            operation.result_id().is_some()
                && !matches!(operation.kind, OperationKind::Alloca { .. })
                && matches!(
                    operation.result(),
                    OperationResult::Lowered(_)
                        | OperationResult::Pointee(_)
                        | OperationResult::Same(_)
                )
        })
        .filter_map(Operation::result_id)
        .collect::<FxHashSet<_>>();
    func.blocks().any(|block| {
        let block = func.block(block);
        let invoked = match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        block.operations().iter().chain(invoked).any(|operation| {
            let OperationKind::Call { ty, metadata } = &operation.kind else {
                return false;
            };
            let visible_start = operation.operands.len()
                - ty.fn_ty.args.len()
                - usize::from(ty.result_convention.has_result_place());
            (0..ty.fn_ty.args.len()).any(|offset| {
                accepts_value_argument(ty, metadata.as_deref(), offset)
                    && match &operation.operands[visible_start + offset] {
                        mir::Value::Constant(_) => true,
                        mir::Value::Register(id) => values.contains(id),
                        _ => false,
                    }
            })
        })
    })
}

/// Passes each value operand at `spills` of `call`, which follows `operations`, as a place: the
/// one a trailing load read it from, or else a fresh slot added to `slots` and written by a store
/// appended to `operations`. A load no longer read is dropped.
fn spill_before(
    edit: &mut FunctionEdit,
    call: &mut Operation,
    spills: &[usize],
    operations: &mut Vec<Option<Operation>>,
    slots: &mut Vec<Operation>,
    uses: &mut FxHashMap<ValueId, usize>,
) {
    let mut stored = Vec::new();
    for &index in spills {
        let mir::Value::Register(id) = call.operands[index] else {
            stored.push(index);
            continue;
        };
        let Some(position) = trailing_load(operations, id) else {
            stored.push(index);
            continue;
        };
        let load = operations[position]
            .as_ref()
            .expect("a trailing load is still present");
        call.operands[index] = load.operands[0].clone();
        let remaining = uses.get_mut(&id).expect("a passed value is used");
        *remaining -= 1;
        if *remaining == 0 {
            operations[position] = None;
        }
    }
    let OperationKind::Call { ty, .. } = &call.kind else {
        return;
    };
    let visible_start = call.operands.len()
        - ty.fn_ty.args.len()
        - usize::from(ty.result_convention.has_result_place());
    for index in stored {
        let mut alloca = Operation::alloca(call.span, ty.fn_ty.args[index - visible_start].ty);
        let slot = edit
            .assign_new_result(&mut alloca)
            .expect("an alloca defines its place");
        slots.push(alloca);
        operations.push(Some(Operation::store(
            call.span,
            call.operands[index].clone(),
            slot.clone(),
        )));
        call.operands[index] = slot;
    }
}

/// The position of the load defining `value` among the loads that end `operations`, if it is one
/// of them. Nothing but loads runs between it and what follows, so its place still holds the value.
fn trailing_load(operations: &[Option<Operation>], value: ValueId) -> Option<usize> {
    for (position, operation) in operations.iter().enumerate().rev() {
        let Some(operation) = operation else {
            continue;
        };
        if !matches!(operation.kind, OperationKind::Load) {
            return None;
        }
        if operation.result_id() == Some(value) {
            return Some(position);
        }
    }
    None
}
