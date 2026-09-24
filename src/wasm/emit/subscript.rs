// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Uniform subscript-member dispatch.

use wasm_encoder::{BlockType, Function as WasmFunction, Instruction as I, MemArg, ValType};

use crate::{
    FxHashMap,
    hir::native_functions::NativeResult,
    mir::{
        Value,
        physical::{PhysicalSubscriptDefinition, program::ResolvedPhysicalProgram},
    },
    module::{FunctionId, YieldProvenance, id::Id},
    types::r#type::Type,
    wasm::{
        abi::{CallAbi, Parameter as ParameterTransport, WasmFunctionId, WasmLocalId, WasmTypeId},
        callable_environment::Environment,
        evidence::ENVIRONMENT_OFFSET,
    },
};

use super::{ScalarType, enter_frame, leave_frame, memarg};

/// A member selected from symbolic evidence or an owning materialized subscript.
#[derive(Clone)]
pub(super) struct Borrowed {
    pub source: Value,
    pub mut_member: bool,
    pub materialized: bool,
}

pub(super) struct Entries {
    pub signatures_by_arity: FxHashMap<usize, WasmTypeId>,
    pub resume_signature: WasmTypeId,
}

/// Every projected argument is a place. Results are status, retained frame, and yielded address.
pub(super) fn parameters(arity: usize) -> Vec<ValType> {
    vec![ValType::I32; arity + 3]
}

pub(super) fn results() -> [ValType; 3] {
    [ValType::I32; 3]
}

pub(super) fn visible_arity(target: &CallAbi, captures: usize) -> Result<usize, String> {
    target
        .parameters
        .len()
        .checked_sub(captures)
        .ok_or_else(|| "subscript capture arity".into())
}

fn target_types(
    program: &ResolvedPhysicalProgram<'_>,
    target: FunctionId,
) -> Result<Vec<Type>, String> {
    if let Some(body) = program.function(target) {
        Ok(body
            .parameters()
            .iter()
            .filter(|parameter| parameter.kind != crate::mir::ParameterKind::Return)
            .map(|parameter| parameter.ty)
            .collect())
    } else {
        let native = program
            .module(target.module)
            .and_then(|module| module.native_entry(target))
            .ok_or_else(|| format!("missing subscript member {target:?}"))?;
        Ok(native
            .signature()
            .parameters
            .iter()
            .map(|parameter| parameter.layout().ty)
            .collect())
    }
}

fn capture_address(
    code: &mut WasmFunction,
    definition: &PhysicalSubscriptDefinition,
    index: usize,
) {
    let source = WasmLocalId::from_index(1);
    let materialized = WasmLocalId::from_index(2);
    code.instruction(&I::LocalGet(materialized.as_u32()));
    code.instruction(&I::If(BlockType::Result(ValType::I32)));
    code.instruction(&I::LocalGet(source.as_u32()));
    code.instruction(&I::I32Load(MemArg {
        offset: ENVIRONMENT_OFFSET,
        ..memarg(2)
    }));
    code.instruction(&I::I32Const(Environment::hidden_offset(index) as i32));
    code.instruction(&I::I32Add);
    code.instruction(&I::Else);
    code.instruction(&I::LocalGet(source.as_u32()));
    code.instruction(&I::I32Load(MemArg {
        offset: ENVIRONMENT_OFFSET,
        ..memarg(2)
    }));
    code.instruction(&I::I32Const(
        definition.environment().fields[index].offset as i32,
    ));
    code.instruction(&I::I32Add);
    code.instruction(&I::End);
}

fn call_inputs(
    code: &mut WasmFunction,
    program: &ResolvedPhysicalProgram<'_>,
    definition: &PhysicalSubscriptDefinition,
    target: FunctionId,
    direct: &CallAbi,
) -> Result<(), String> {
    let captures = definition.capture_schema().len();
    let types = target_types(program, target)?;
    if types.len() != direct.parameters.len() || captures > types.len() {
        return Err("subscript member argument count".into());
    }
    for (index, transport) in direct.parameters.iter().enumerate() {
        if index < captures {
            capture_address(code, definition, index);
        } else {
            code.instruction(&I::LocalGet((3 + index - captures) as u32));
        }
        if matches!(transport, ParameterTransport::Direct(_)) {
            ScalarType::of(types[index])?.load(code);
        }
    }
    Ok(())
}

/// Bridge a descriptor-selected member to its direct addressor or yielded-accessor entry.
pub(super) fn member_adapter(
    program: &ResolvedPhysicalProgram<'_>,
    definition: &PhysicalSubscriptDefinition,
    mut_member: bool,
    direct: &CallAbi,
    target_index: WasmFunctionId,
) -> Result<WasmFunction, String> {
    let member = definition
        .member(mut_member)
        .ok_or("missing subscript member")?;
    let target = program.direct_entry(member.function());
    let arity = visible_arity(direct, definition.capture_schema().len())?;
    let parameter_count = arity + 3;
    let frame = WasmLocalId::from_index(parameter_count);
    let status = WasmLocalId::from_index(parameter_count + 1);
    let yielded = WasmLocalId::from_index(parameter_count + 2);
    let mut code = WasmFunction::new([(3, ValType::I32)]);
    if direct.fallible {
        code.instruction(&I::LocalGet(0));
    }
    call_inputs(&mut code, program, definition, target, direct)?;
    match member.provenance() {
        YieldProvenance::YieldedOnce => {
            debug_assert!(direct.fallible && direct.output());
            code.instruction(&I::I32Const(0)); // Yielded bodies do not use their MIR @ret slot.
            code.instruction(&I::Call(target_index.as_u32()));
        }
        YieldProvenance::AddressorPlace => {
            if direct.fallible {
                enter_frame(&mut code, frame, 8);
                code.instruction(&I::LocalGet(frame.as_u32()));
            }
            code.instruction(&I::Call(target_index.as_u32()));
            if direct.fallible {
                code.instruction(&I::LocalSet(status.as_u32()));
                code.instruction(&I::LocalGet(frame.as_u32()));
                code.instruction(&I::I32Load(memarg(2)));
                code.instruction(&I::LocalSet(yielded.as_u32()));
                leave_frame(&mut code, frame);
                code.instruction(&I::LocalGet(status.as_u32()));
            } else {
                code.instruction(&I::LocalSet(yielded.as_u32()));
                code.instruction(&I::I32Const(0));
            }
            code.instruction(&I::I32Const(0));
            code.instruction(&I::LocalGet(yielded.as_u32()));
        }
    }
    code.instruction(&I::End);
    Ok(code)
}

pub(super) fn is_addressor_native(
    program: &ResolvedPhysicalProgram<'_>,
    target: FunctionId,
) -> bool {
    program
        .module(target.module)
        .and_then(|module| module.native_entry(target))
        .is_some_and(|entry| matches!(entry.signature().result, NativeResult::Addressor { .. }))
}
