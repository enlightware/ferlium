// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Bridges between dictionary, native and host entry calling conventions.

use std::mem::offset_of;

use wasm_encoder::{BlockType, Function as WasmFunction, Instruction as I, MemArg, ValType};

use crate::{
    CompilerSession, FxHashMap, Location,
    hir::{native_functions::NativeResult, value::VariantPayloadStorage},
    mir::{ParameterKind, physical::program::ResolvedPhysicalProgram},
    module::{
        DictionaryEntryEvidence, FunctionId, ModuleEnv, ProjectionIndex, TraitDictionaryId, id::Id,
    },
    std::value::{
        product_layout_spec, structural_variant, value_layout_for_type, variant_payload_offset,
        variant_payload_storage_for_type,
    },
    types::{r#trait::TraitDictionaryEntryIndex, r#type::Type},
    ustr,
    wasm::{
        Imports,
        abi::{CallAbi, Parameter as ParameterTransport, ResultKind, WasmFunctionId, WasmLocalId},
        evidence::ENVIRONMENT_OFFSET,
        execution::{FailureCode, InvocationState},
    },
};

use super::{
    ScalarType, check_context, context_pointer, enter_frame, frame_address, frame_bytes,
    leave_frame, memarg, store_failure_and_trap,
};

/// Bridge the declaration-fixed dictionary ABI to the implementation's direct ABI.
pub(super) fn dictionary_adapter(
    program: &ResolvedPhysicalProgram<'_>,
    dictionary: TraitDictionaryId,
    entry: TraitDictionaryEntryIndex,
    abi: &CallAbi,
    callees: &FxHashMap<FunctionId, (WasmFunctionId, &CallAbi)>,
    session: &CompilerSession,
    imports: &Imports,
) -> Result<WasmFunction, String> {
    let definition = program.dictionary(dictionary).unwrap();
    let entry = &definition.entries()[entry.as_index()];
    let target = program.direct_entry(entry.function());
    let (index, direct) = &callees[&target];
    let native = program
        .module(target.module)
        .and_then(|module| module.native_entry(target));
    let (input_types, result_ty) = if let Some(body) = program.function(target) {
        (
            body.parameters()
                .iter()
                .filter(|p| p.kind != ParameterKind::Return)
                .map(|p| p.ty)
                .collect::<Vec<_>>(),
            body.parameters()
                .iter()
                .find(|p| p.kind == ParameterKind::Return)
                .map_or(Type::unit(), |p| p.ty),
        )
    } else {
        let native = native.unwrap().signature();
        (
            native.parameters.iter().map(|p| p.layout().ty).collect(),
            native.result.ty(),
        )
    };
    let captures = entry.capture_mapping();
    if direct.parameters.len() != captures.len() + abi.parameters.len() - 1 {
        return Err(format!("dictionary adapter argument count for {target:?}"));
    }
    let env = session
        .modules()
        .env_for(session.expect_fresh_module(target.module));
    let optional = if matches!(direct.result, ResultKind::Optional) {
        let NativeResult::Optional { payload, .. } = native.unwrap().signature().result else {
            unreachable!()
        };
        Some(NativeOptionalResultAdapter::new(
            result_ty, payload.ty, env, session,
        )?)
    } else {
        None
    };
    let mut frame_size = optional
        .as_ref()
        .map(|adapter| frame_bytes(adapter.payload_size))
        .transpose()?
        .unwrap_or(0);
    let mut spills = vec![None; abi.parameters.len() - 1];
    for (i, canonical) in abi.parameters[1..].iter().enumerate() {
        if matches!(canonical, ParameterTransport::Direct(_))
            && direct.parameters[captures.len() + i] == ParameterTransport::Indirect
        {
            spills[i] = Some(frame_size);
            frame_size = frame_size
                .checked_add(8)
                .ok_or("dictionary adapter frame overflow")?;
        }
    }
    let frame = WasmLocalId::from_index(abi.parameter_count());
    let scratch = WasmLocalId::from_index(abi.parameter_count() + 1);
    let mut code = WasmFunction::new([(if frame_size == 0 { 0 } else { 2 }, ValType::I32)]);
    if frame_size != 0 {
        enter_frame(&mut code, frame, frame_size);
        for (i, offset) in spills.iter().enumerate() {
            if let Some(offset) = offset {
                frame_address(&mut code, frame, *offset);
                code.instruction(&I::LocalGet(abi.input_local(i + 1).as_u32()));
                ScalarType::of(input_types[captures.len() + i])?.store(&mut code);
            }
        }
    }
    if !direct.fallible && matches!(direct.result, ResultKind::Direct(_)) {
        code.instruction(&I::LocalGet(abi.output_local().as_u32()));
    }
    if direct.fallible {
        if abi.fallible {
            code.instruction(&I::LocalGet(abi.failure_local().as_u32()));
        } else {
            context_pointer(&mut code, offset_of!(InvocationState, native_failure));
        }
    }
    for mapping in captures {
        code.instruction(&I::LocalGet(abi.input_local(0).as_u32()));
        if let DictionaryEntryEvidence::Capture(index) = mapping {
            code.instruction(&I::I32Load(MemArg {
                offset: ENVIRONMENT_OFFSET,
                ..memarg(2)
            }));
            code.instruction(&I::I32Const(
                definition.environment().fields[*index].offset as i32,
            ));
            code.instruction(&I::I32Add);
        }
    }
    for (i, canonical) in abi.parameters[1..].iter().enumerate() {
        let actual = direct.parameters[captures.len() + i];
        if let Some(offset) = spills[i] {
            frame_address(&mut code, frame, offset);
            continue;
        }
        code.instruction(&I::LocalGet(abi.input_local(i + 1).as_u32()));
        if let (ParameterTransport::Indirect, ParameterTransport::Direct(_)) = (*canonical, actual)
        {
            ScalarType::of(input_types[captures.len() + i])?.load(&mut code);
        }
    }
    if direct.output() {
        code.instruction(&I::LocalGet(
            (if optional.is_some() {
                frame
            } else {
                abi.output_local()
            })
            .as_u32(),
        ));
    }
    code.instruction(&I::Call(index.as_u32()));
    if let Some(adapter) = optional {
        adapter.emit(
            &mut code,
            abi.output_local(),
            frame,
            scratch,
            imports.function_index("alloc"),
        );
    }
    if direct.fallible {
        if !abi.fallible {
            // A status ABI does not imply a source-level permission to fail. The declaration's
            // infallible contract guarantees success here, including after unsafe effect erasure.
            code.instruction(&I::Drop);
        }
    } else {
        if matches!(direct.result, ResultKind::Direct(_)) {
            ScalarType::of(result_ty)?.store(&mut code);
        }
        if abi.fallible {
            code.instruction(&I::I32Const(0));
        }
    }
    if frame_size != 0 {
        leave_frame(&mut code, frame);
    }
    code.instruction(&I::End);
    Ok(code)
}

/// Concrete native presence/payload transport to the language's Option representation.
pub(super) struct NativeOptionalResultAdapter {
    some_tag: u32,
    none_tag: u32,
    storage: VariantPayloadStorage,
    size: u32,
    align: u32,
    field: u32,
    pub(super) payload_size: u32,
}

impl NativeOptionalResultAdapter {
    pub(super) fn new(
        ty: Type,
        payload: Type,
        env: ModuleEnv<'_>,
        session: &CompilerSession,
    ) -> Result<Self, String> {
        let (_, cases) = structural_variant(ty, &env).ok_or("optional output is not a variant")?;
        let some = cases
            .iter()
            .find(|(tag, _)| *tag == ustr("Some"))
            .ok_or("optional output has no Some case")?
            .1;
        let span = Location::new_synthesized();
        let storage = variant_payload_storage_for_type(ty, ustr("Some"), span, &env)
            .map_err(|e| format!("optional payload storage: {e:?}"))?;
        let layout = value_layout_for_type(some, span, &env)
            .map_err(|e| format!("optional payload layout: {e:?}"))?;
        let payload_layout = value_layout_for_type(payload, span, &env)
            .map_err(|e| format!("optional native layout: {e:?}"))?;
        if payload_layout.align > 8 {
            return Err("optional native alignment exceeds frame alignment".into());
        }
        let field = product_layout_spec(some, span, &env)
            .and_then(|p| p.static_field_offset(ProjectionIndex::from_index(0)))
            .ok_or("optional payload must be a concrete tuple")? as u32;
        Ok(Self {
            some_tag: storage.encode_tag_id(session.variant_tag_id(ustr("Some"))),
            none_tag: session.variant_tag_id(ustr("None")),
            storage,
            size: layout.size,
            align: layout.align,
            field,
            payload_size: payload_layout.size,
        })
    }

    pub(super) fn emit(
        &self,
        code: &mut WasmFunction,
        output: WasmLocalId,
        payload: WasmLocalId,
        scratch: WasmLocalId,
        allocate: WasmFunctionId,
    ) {
        code.instruction(&I::If(BlockType::Empty)); // Native presence, not a failure status.
        code.instruction(&I::LocalGet(output.as_u32()));
        code.instruction(&I::I32Const(self.some_tag as i32));
        code.instruction(&I::I32Store(memarg(2)));
        code.instruction(&I::LocalGet(output.as_u32()));
        code.instruction(&I::I32Const(
            variant_payload_offset(if self.storage.is_indirect() {
                align_of::<usize>() as u32
            } else {
                self.align
            }) as i32,
        ));
        code.instruction(&I::I32Add);
        if self.storage.is_indirect() {
            code.instruction(&I::I32Const(self.size as i32));
            code.instruction(&I::I32Const(self.align as i32));
            code.instruction(&I::Call(allocate.as_u32()));
            code.instruction(&I::LocalTee(scratch.as_u32()));
            code.instruction(&I::I32Store(memarg(2)));
            code.instruction(&I::LocalGet(scratch.as_u32()));
        }
        code.instruction(&I::I32Const(self.field as i32));
        code.instruction(&I::I32Add);
        code.instruction(&I::LocalGet(payload.as_u32()));
        code.instruction(&I::I32Const(self.payload_size as i32));
        code.instruction(&I::MemoryCopy {
            src_mem: 0,
            dst_mem: 0,
        });
        code.instruction(&I::Else);
        code.instruction(&I::LocalGet(output.as_u32()));
        code.instruction(&I::I32Const(self.none_tag as i32));
        code.instruction(&I::I32Store(memarg(2)));
        code.instruction(&I::End);
    }
}

pub(super) fn entry_wrapper(
    index: WasmFunctionId,
    signature: &CallAbi,
    result: ScalarType,
) -> WasmFunction {
    debug_assert!(signature.fallible);
    let frame = WasmLocalId::from_index(signature.parameters.len());
    let mut code = WasmFunction::new([(1, ValType::I32)]);
    check_context(&mut code);
    // The scalar host result needs at most eight aligned bytes, reserved before the callee.
    enter_frame(&mut code, frame, 8);
    context_pointer(&mut code, offset_of!(InvocationState, native_failure));
    for i in 0..signature.parameters.len() {
        code.instruction(&I::LocalGet(WasmLocalId::from_index(i).as_u32()));
    }
    if signature.output() {
        code.instruction(&I::LocalGet(frame.as_u32()));
    }
    code.instruction(&I::Call(index.as_u32()));
    leave_frame(&mut code, frame);
    code.instruction(&I::If(BlockType::Empty));
    store_failure_and_trap(&mut code, FailureCode::Source);
    code.instruction(&I::End);
    if !result.is_unit() {
        code.instruction(&I::LocalGet(frame.as_u32()));
        result.load(&mut code);
    }
    code.instruction(&I::End);
    code
}

/// Normalize a no-argument expression entry to one caller-provided result pointer.
pub(super) fn boxed_entry_wrapper(
    index: WasmFunctionId,
    signature: &CallAbi,
) -> Result<WasmFunction, String> {
    if !signature.parameters.is_empty() {
        return Err("boxed Wasm expression entry has parameters".into());
    }
    let output = WasmLocalId::from_index(0);
    let mut code = WasmFunction::new([]);
    check_context(&mut code);
    // An infallible direct result stays on the operand stack above its destination address. A
    // fallible direct result already uses the ordinary output-pointer form.
    if !signature.fallible && matches!(signature.result, ResultKind::Direct(_)) {
        code.instruction(&I::LocalGet(output.as_u32()));
    }
    if signature.fallible {
        context_pointer(&mut code, offset_of!(InvocationState, native_failure));
    }
    if signature.output() {
        code.instruction(&I::LocalGet(output.as_u32()));
    }
    code.instruction(&I::Call(index.as_u32()));
    if signature.fallible {
        code.instruction(&I::If(BlockType::Empty));
        store_failure_and_trap(&mut code, FailureCode::Source);
        code.instruction(&I::End);
    } else if let ResultKind::Direct(ty) = signature.result {
        // The temporary boxed harness always reserves at least one aligned Wasm word, even when
        // the Ferlium result layout (notably bool) is narrower than this ABI store.
        code.instruction(&match ty {
            ValType::I32 => I::I32Store(memarg(2)),
            ValType::F64 => I::F64Store(memarg(3)),
            _ => return Err("unsupported boxed Wasm direct result".into()),
        });
    }
    code.instruction(&I::End);
    Ok(code)
}
