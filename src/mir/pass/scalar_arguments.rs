// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Scalar call arguments and results.
//!
//! The ABI passes a read-only argument of a concrete scalar type by value, and semantic MIR does
//! too (see [`accepts_value_argument`]): HIR emission reads it where the argument is evaluated, and
//! a substitution that makes an argument such a scalar reads it with [`read_before`]. The read is
//! an ordinary `load` of the caller, which the caller's passes see: LICM hoists one that a loop does
//! not change, where a read inside a call was invisible to it. A non-fallible scalar result is a
//! register the call defines, likewise (see [`accepts_value_result`]).
//!
//! Physical MIR passes such an argument as a place where the callee's entry takes it through a
//! pointer ([`spill_value_arguments`]), and such a result as a place where the entry returns it
//! through one ([`place_value_results`]).

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    mir::{
        self, Function, Operation, OperationKind, ValueId,
        edit::FunctionEdit,
        operation::{OperationResult, accepts_value_argument, accepts_value_result},
        role::{MirType, ValueRole, ValueRoles},
        terminator::TerminatorKind,
    },
    module::id::Id,
};

/// Appends a `load` of each operand at `reads` to `operations`, and passes its value instead.
pub(crate) fn read_before(
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

/// Passes each scalar value argument of a `call` or a `project` as a place where `takes_value` says
/// its callee's entry takes that argument through a pointer. `takes_value` is given the operation and
/// the argument's offset among the visible ones. `None` if no such argument is a value.
///
/// A value loaded in the call's block, with nothing but other loads and `alloca`s in between, is
/// replaced by the place it was loaded from, and the load is dropped when nothing else reads it:
/// the call reads that place directly. Any other value, such as a load LICM hoisted, is stored into
/// a frame slot of its own in the entry block, just before the call, which the Wasm emitter keeps
/// in a local.
pub(crate) fn spill_value_arguments(
    func: &Function,
    takes_value: impl Fn(&Operation, usize) -> bool,
) -> Option<Function> {
    if !may_pass_values(func) {
        return None;
    }
    let roles = ValueRoles::derive(func);
    let spills_of = |operation: &Operation| -> Vec<usize> {
        let Some((_, ty, metadata)) = operation.call_site() else {
            return Vec::new();
        };
        let visible_start = operation.call_visible_start();
        (0..ty.fn_ty.args.len())
            .filter(|&offset| {
                accepts_value_argument(ty, metadata, offset) && !takes_value(operation, offset)
            })
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

/// Makes a call writing its result through a place define it as a register instead, if its type
/// now carries the result as a value (see [`accepts_value_result`]): substituting a generic result
/// or effect, or making a fallible call infallible, can make it one. Returns the store of the
/// register into the former result place, which follows the call.
pub(crate) fn return_value_from_call(
    edit: &mut FunctionEdit,
    call: &mut Operation,
) -> Option<Operation> {
    let OperationKind::Call {
        ty, value_result, ..
    } = &mut call.kind
    else {
        return None;
    };
    if *value_result || !accepts_value_result(ty) {
        return None;
    }
    *value_result = true;
    let mut operands = call.operands.to_vec();
    let place = operands
        .pop()
        .expect("a call returning through a place has one");
    call.operands = operands.into_boxed_slice();
    let value = edit
        .assign_new_result(call)
        .expect("a value call defines its result");
    Some(Operation::store(call.span, value, place))
}

/// Passes a result place to each `call` defining its result register where `returns_value` says its
/// callee's entry returns that result through a pointer. The place is a frame slot of its own in the
/// entry block, which a `load` after the call reads into the register. `None` if no call needs one.
pub(crate) fn place_value_results(
    func: &Function,
    returns_value: impl Fn(&Operation) -> bool,
) -> Option<Function> {
    let needs_place = |operation: &Operation| {
        matches!(
            operation.kind,
            OperationKind::Call {
                value_result: true,
                ..
            }
        ) && !returns_value(operation)
    };
    if !func
        .blocks()
        .any(|block| func.block(block).operations().iter().any(&needs_place))
    {
        return None;
    }
    let mut edit = FunctionEdit::new(func.clone());
    let mut slots = Vec::new();
    for block in edit.blocks().collect::<Vec<_>>() {
        let operations = std::mem::take(&mut edit.block_mut(block).operations);
        let mut rewritten = Vec::with_capacity(operations.len());
        for operation in operations {
            if !needs_place(&operation) {
                rewritten.push(operation);
                continue;
            }
            let OperationKind::Call { ty, metadata, .. } = &operation.kind else {
                unreachable!("only a call defines a value result");
            };
            let result = operation
                .result_id()
                .expect("a value call defines its result");
            let mut alloca = Operation::alloca(operation.span, ty.fn_ty.ret);
            let slot = edit
                .assign_new_result(&mut alloca)
                .expect("an alloca defines its place");
            slots.push(alloca);
            let mut operands = operation.operands.to_vec();
            operands.push(slot.clone());
            rewritten.push(Operation::from_parts(
                operation.span,
                operands.into_boxed_slice(),
                OperationKind::Call {
                    ty: ty.clone(),
                    metadata: metadata.clone(),
                    value_result: false,
                },
            ));
            let mut load = Operation::load(operation.span, slot);
            load.assign_result_id(Some(result));
            rewritten.push(load);
        }
        edit.block_mut(block).operations = rewritten;
    }
    let entry = edit.entry();
    edit.block_mut(entry).operations.splice(0..0, slots);
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
            let Some((_, ty, metadata)) = operation.call_site() else {
                return false;
            };
            let visible_start = operation.call_visible_start();
            (0..ty.fn_ty.args.len()).any(|offset| {
                accepts_value_argument(ty, metadata, offset)
                    && match &operation.operands[visible_start + offset] {
                        mir::Value::Constant(_) => true,
                        mir::Value::Register(id) => values.contains(id),
                        mir::Value::Parameter(id) => func.parameters()[id.as_index()].is_value(),
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
    let Some((_, ty, _)) = call.call_site() else {
        return;
    };
    let visible_start = call.call_visible_start();
    let types: Vec<_> = stored
        .iter()
        .map(|index| ty.fn_ty.args[index - visible_start].ty)
        .collect();
    for (index, ty) in stored.into_iter().zip(types) {
        let mut alloca = Operation::alloca(call.span, ty);
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

/// The position of the load defining `value` among the loads and `alloca`s that end `operations`,
/// if it is one of them. Nothing between it and what follows writes an existing place, so its place
/// still holds the value.
fn trailing_load(operations: &[Option<Operation>], value: ValueId) -> Option<usize> {
    for (position, operation) in operations.iter().enumerate().rev() {
        let Some(operation) = operation else {
            continue;
        };
        match operation.kind {
            OperationKind::Alloca { .. } => continue,
            OperationKind::Load => {}
            _ => return None,
        }
        if operation.result_id() == Some(value) {
            return Some(position);
        }
    }
    None
}
