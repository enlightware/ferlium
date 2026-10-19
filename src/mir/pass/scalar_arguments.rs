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

use rustc_hash::FxHashMap;

use crate::mir::{
    self, Function, Operation, OperationKind, ResultTransport, ValueId,
    edit::FunctionEdit,
    operation::{accepts_value_argument, accepts_value_result},
    results::{accepts_no_value_result, zero_sized_result},
    terminator::TerminatorKind,
};
use crate::{module::ModuleEnv, types::r#type::CallResultConvention};

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
/// the argument's offset among the visible ones. `None` if no argument needs a place.
///
/// A value loaded in the call's block, with nothing but other loads and `alloca`s in between, is
/// replaced by the place it was loaded from, and the load is dropped when nothing else reads it:
/// the call reads that place directly. Any other value, such as a load LICM hoisted, is stored into
/// a frame slot of its own in the entry block, just before the call, which the Wasm emitter keeps
/// in a local.
pub(crate) fn spill_value_arguments(
    func: &Function,
    takes_value: impl Fn(&Operation, usize) -> bool,
    env: ModuleEnv<'_>,
) -> Option<Function> {
    // A read-only scalar argument is a value exactly when the call-site type says so, as the
    // semantic verifier requires.
    let spills_of = |operation: &Operation| -> Vec<usize> {
        let Some((_, ty, metadata)) = operation.call_site() else {
            return Vec::new();
        };
        let visible_start = operation.call_visible_start();
        (0..ty.fn_ty.args.len())
            .filter(|&offset| {
                accepts_value_argument(ty, metadata, offset, &env)
                    && !takes_value(operation, offset)
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

/// Restores canonical result form after substitution or invoke demotion: a scalar register or
/// NoValue with a typed zero-sized constant. Returns the store initializing the former output
/// place, which must follow the call on its success path only.
pub(crate) fn normalize_call_result(
    edit: &mut FunctionEdit,
    call: &mut Operation,
    env: ModuleEnv<'_>,
) -> Option<Operation> {
    let OperationKind::Call {
        ty,
        result_transport,
        ..
    } = &mut call.kind
    else {
        return None;
    };
    if ty.result_convention == CallResultConvention::Value && accepts_no_value_result(ty, &env) {
        let constant = zero_sized_result(ty.fn_ty.ret, &env).expect("eligible result");
        let value = mir::Value::Constant(edit.add_constant(ty.fn_ty.ret, constant, &env));
        ty.result_convention = CallResultConvention::NoValue;
        *result_transport = ResultTransport::NoValue;
        let mut operands = call.operands.to_vec();
        let place = operands
            .pop()
            .expect("an indirect result has its output place");
        call.operands = operands.into_boxed_slice();
        return Some(Operation::store(call.span, value, place));
    }
    if *result_transport != ResultTransport::Place || !accepts_value_result(ty, &env) {
        return None;
    }
    *result_transport = ResultTransport::Value;
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

/// Passes a result place to each `call` defining its result register where `result_transport` says its
/// callee's entry returns that result through a pointer. The place is a frame slot of its own in the
/// entry block, which a `load` after the call reads into the register. `None` if no call needs one.
pub(crate) fn place_value_results(
    func: &Function,
    result_transport: impl Fn(&Operation) -> ResultTransport,
) -> Option<Function> {
    let needs_place = |operation: &Operation| {
        matches!(
            operation.kind,
            OperationKind::Call {
                result_transport: ResultTransport::Value,
                ..
            }
        ) && result_transport(operation) != ResultTransport::Value
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
                    result_transport: ResultTransport::Place,
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

/// Defines the result register of each `call` passing a result place where `result_transport`
/// says its callee's entry returns that result directly, and stores it into the place after the
/// call. A call type more conservative than its callee, such as a devirtualized trait method
/// declared fallible, keeps a place in semantic MIR. `None` if no call needs a register.
pub(crate) fn value_place_results(
    func: &Function,
    result_transport: impl Fn(&Operation) -> ResultTransport,
) -> Option<Function> {
    let needs_value = |operation: &Operation| {
        matches!(
            operation.kind,
            OperationKind::Call {
                result_transport: ResultTransport::Place,
                ..
            }
        ) && result_transport(operation) == ResultTransport::Value
    };
    if !func
        .blocks()
        .any(|block| func.block(block).operations().iter().any(&needs_value))
    {
        return None;
    }
    let mut edit = FunctionEdit::new(func.clone());
    for block in edit.blocks().collect::<Vec<_>>() {
        let operations = std::mem::take(&mut edit.block_mut(block).operations);
        let mut rewritten = Vec::with_capacity(operations.len());
        for mut operation in operations {
            if !needs_value(&operation) {
                rewritten.push(operation);
                continue;
            }
            let OperationKind::Call {
                result_transport, ..
            } = &mut operation.kind
            else {
                unreachable!("only a call passes a result place");
            };
            *result_transport = ResultTransport::Value;
            let mut operands = operation.operands.to_vec();
            let place = operands
                .pop()
                .expect("a call returning through a place has one");
            operation.operands = operands.into_boxed_slice();
            let value = edit
                .assign_new_result(&mut operation)
                .expect("a value call defines its result");
            let span = operation.span;
            rewritten.push(operation);
            rewritten.push(Operation::store(span, value, place));
        }
        edit.block_mut(block).operations = rewritten;
    }
    Some(edit.finish_unverified())
}

/// Supplies output storage where a semantic NoValue call reaches an indirect result interface.
/// Invokes keep that storage private: no value is read on either successor.
pub(crate) fn place_no_value_results(
    func: &Function,
    result_transport: impl Fn(&Operation) -> ResultTransport,
) -> Option<Function> {
    let needs_place = |op: &Operation| {
        matches!(&op.kind,
        OperationKind::Call { ty, .. } if ty.result_convention == CallResultConvention::NoValue)
            && result_transport(op) != ResultTransport::NoValue
    };
    if !func.blocks().any(|block| {
        let block = func.block(block);
        block
            .operations()
            .iter()
            .chain(match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            })
            .any(&needs_place)
    }) {
        return None;
    }
    let mut edit = FunctionEdit::new(func.clone());
    let mut slots = Vec::new();
    for block in edit.blocks().collect::<Vec<_>>() {
        let mut operations = std::mem::take(&mut edit.block_mut(block).operations);
        let mut terminator = edit.block(block).terminator.clone();
        let invoked = match &mut terminator.kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        for op in operations.iter_mut().chain(invoked) {
            if !needs_place(op) {
                continue;
            }
            let OperationKind::Call {
                ty,
                result_transport,
                ..
            } = &mut op.kind
            else {
                unreachable!()
            };
            let mut alloca = Operation::alloca(op.span, ty.fn_ty.ret);
            let slot = edit.assign_new_result(&mut alloca).unwrap();
            slots.push(alloca);
            ty.result_convention = CallResultConvention::Value;
            *result_transport = ResultTransport::Place;
            let mut operands = op.operands.to_vec();
            operands.push(slot);
            op.operands = operands.into_boxed_slice();
        }
        edit.block_mut(block).operations = operations;
        edit.block_mut(block).terminator = terminator;
    }
    if slots.is_empty() {
        return None;
    }
    let entry = edit.entry();
    edit.block_mut(entry).operations.splice(0..0, slots);
    Some(edit.finish_unverified())
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
