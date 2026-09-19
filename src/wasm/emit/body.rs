// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Per-function storage assignment and instruction emission.

use std::mem::offset_of;

use wasm_encoder::{BlockType, Function as WasmFunction, Instruction as I, MemArg, ValType};

use crate::{
    CompilerSession, FxHashMap, FxHashSet, Location,
    hir::{
        native_functions::{NativeResult, NativeScalar},
        value::{LiteralValue, VariantPayloadStorage},
    },
    mir::{
        BlockId, Function, Operation, OperationKind, ParameterId, ParameterKind, Value, ValueId,
        operation::OperationKindDiscriminant,
        physical::{DictionaryReference, program::ResolvedPhysicalProgram},
        role::{MirType, ValueRole, ValueRoles},
        terminator::TerminatorKind,
        value::ConstantId,
    },
    module::{FunctionId, ModuleEnv, ProjectionIndex, TraitId, id::Id},
    std::{
        logic::bool_type,
        math::Float,
        string::StaticStr,
        value::{product_layout_spec, value_layout_for_type},
    },
    types::{r#trait::TraitDictionaryEntryIndex, r#type::Type},
    wasm::{
        Imports,
        abi::{
            CallAbi, Parameter as ParameterTransport, ResultKind, WasmFunctionId, WasmLocalId,
            WasmTypeId,
        },
        evidence::{self, ENVIRONMENT_OFFSET},
        execution::{FailureCode, InvocationState},
    },
};

use super::{
    Global, ScalarType, StringLiterals, adapters::NativeOptionalResultAdapter, allocate_frame,
    callable, callee, context_pointer, dictionary_table, emit_failure, enter_frame, frame_address,
    frame_bytes, layout_witness, leave_frame, memarg, operations, scalar,
};

#[derive(Clone, Copy)]
enum Storage {
    Local(WasmLocalId),
    /// Byte offset from the function's frame base in linear memory.
    Stack(u32),
}

#[derive(Clone, Copy)]
struct LayoutLocals {
    dictionary: WasmLocalId,
    table: WasmLocalId,
    output: WasmLocalId,
}

pub(super) struct Body<'a, 's> {
    pub(super) body: &'a Function,
    signature: &'a CallAbi,
    pub(super) roles: ValueRoles,
    pub(super) env: ModuleEnv<'a>,
    pub(super) imports: &'a Imports,
    strings: &'a mut StringLiterals,
    evidence: &'a evidence::Image,
    entry_abis: &'a FxHashMap<(TraitId, TraitDictionaryEntryIndex), (WasmTypeId, CallAbi)>,
    layout_entries: [(TraitId, TraitDictionaryEntryIndex); 2],
    pub(super) callable_entries: &'a callable::Entries,
    pub(super) callable_locals: Option<(WasmLocalId, WasmLocalId)>,
    callable_values: FxHashSet<ValueId>,
    pub(super) dictionary_definitions: FxHashMap<ValueId, &'a Operation>,
    selections: &'s FxHashMap<ValueId, (TraitId, TraitDictionaryEntryIndex)>,
    owned_evidence: Vec<ValueId>,
    capture_slots: FxHashMap<ValueId, u32>,
    variant_shells: FxHashSet<ValueId>,
    layout_slot: Option<u32>,
    pub(super) dynamic_size: WasmLocalId,
    pub(super) dynamic_align: WasmLocalId,
    dynamic_base: WasmLocalId,
    allocation_end: WasmLocalId,
    evidence_base: Option<WasmLocalId>,
    layout_locals: Option<LayoutLocals>,
    pending_failure: WasmLocalId,
    pub(super) scratch: WasmLocalId,
    scratch_slots: FxHashMap<Type, u32>,
    callees: &'a FxHashMap<FunctionId, (WasmFunctionId, &'a CallAbi)>,
    program: &'a ResolvedPhysicalProgram<'a>,
    session: &'a CompilerSession,
    registers: FxHashMap<ValueId, WasmLocalId>,
    storage: FxHashMap<Value, Storage>,
    locals: Vec<ValType>,
    frame: Option<WasmLocalId>,
    pc: Option<WasmLocalId>,
    frame_size: u32,
    pub(super) code: WasmFunction,
}

impl<'a, 's> Body<'a, 's> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        body: &'a Function,
        signature: &'a CallAbi,
        callees: &'a FxHashMap<FunctionId, (WasmFunctionId, &'a CallAbi)>,
        program: &'a ResolvedPhysicalProgram<'a>,
        session: &'a CompilerSession,
        env: ModuleEnv<'a>,
        imports: &'a Imports,
        strings: &'a mut StringLiterals,
        evidence: &'a evidence::Image,
        entry_abis: &'a FxHashMap<(TraitId, TraitDictionaryEntryIndex), (WasmTypeId, CallAbi)>,
        layout_entries: [(TraitId, TraitDictionaryEntryIndex); 2],
        callable_entries: &'a callable::Entries,
        selections: &'s FxHashMap<ValueId, (TraitId, TraitDictionaryEntryIndex)>,
    ) -> Result<Self, String> {
        let mut this = Self {
            body,
            signature,
            env,
            imports,
            strings,
            evidence,
            entry_abis,
            layout_entries,
            callable_entries,
            callable_locals: None,
            callable_values: FxHashSet::default(),
            dictionary_definitions: FxHashMap::default(),
            selections,
            owned_evidence: Vec::new(),
            capture_slots: FxHashMap::default(),
            variant_shells: FxHashSet::default(),
            layout_slot: None,
            dynamic_size: WasmLocalId::default(),
            dynamic_align: WasmLocalId::default(),
            dynamic_base: WasmLocalId::default(),
            allocation_end: WasmLocalId::default(),
            evidence_base: None,
            layout_locals: None,
            pending_failure: WasmLocalId::default(),
            scratch: WasmLocalId::default(),
            scratch_slots: FxHashMap::default(),
            callees,
            program,
            session,
            roles: ValueRoles::derive(body),
            registers: FxHashMap::default(),
            storage: FxHashMap::default(),
            locals: Vec::new(),
            frame: None,
            pc: None,
            frame_size: 0,
            code: WasmFunction::new([]),
        };
        this.pending_failure = this.local(ValType::I32);
        this.scratch = this.local(ValType::I32);
        this.dynamic_size = this.local(ValType::I32);
        this.dynamic_align = this.local(ValType::I32);
        this.dynamic_base = this.local(ValType::I32);
        this.allocation_end = this.local(ValType::I64);
        if body.blocks().count() != 1
            || !matches!(
                body.block(body.entry()).terminator().kind,
                TerminatorKind::Return | TerminatorKind::InvariantFailure { .. }
            )
        {
            this.pc = Some(this.local(ValType::I32));
        }
        let addressed = this.address_observations();
        // Constants remain immediate unless an indirect argument or pointer use needs storage.
        for (index, constant) in body.constants().iter().enumerate() {
            let value = Value::Constant(ConstantId::from_index(index));
            if addressed.contains(&value) || ScalarType::of(constant.ty).is_err() {
                this.slot(value, this.size(&MirType::Lowered(constant.ty))?)?;
            }
        }
        for (index, parameter) in body.parameters().iter().enumerate() {
            if (parameter.kind == ParameterKind::Return
                && parameter.ty != Type::never()
                && !signature.output())
                || signature
                    .parameters
                    .get(index)
                    .is_some_and(|p| matches!(p, ParameterTransport::Direct(_)))
            {
                let value = Value::Parameter(ParameterId::from_index(index));
                let ty = this.pointee(&value)?;
                if addressed.contains(&value) {
                    this.slot(value, ty.size())?;
                } else {
                    let local = if parameter.kind == ParameterKind::Return {
                        this.local(ty.wasm())
                    } else {
                        signature.input_local(index)
                    };
                    this.storage.insert(value, Storage::Local(local));
                }
            }
        }
        for block in body.blocks() {
            for operation in operations(body.block(block)) {
                if matches!(operation.kind, OperationKind::BuildClosure { .. }) {
                    if this.callable_locals.is_none() {
                        this.callable_locals =
                            Some((this.local(ValType::I32), this.local(ValType::I32)));
                    }
                    if this.layout_slot.is_none() {
                        this.layout_slot = Some(this.reserve_bytes(8)?);
                    }
                }
                if this.layout_slot.is_none() && layout_witness(operation).is_some() {
                    this.layout_slot = Some(this.reserve_bytes(8)?);
                }
                if matches!(operation.kind, OperationKind::Replace)
                    && layout_witness(operation).is_none()
                {
                    let MirType::Lowered(ty) = this.pointee_type(&operation.operands[0])? else {
                        return Err("pointer replacement".into());
                    };
                    this.reserve_scratch(ty)?;
                }
                if let Some(Value::Function(target)) = callee(operation)
                    && let Some(payload) = this.optional_payload(*target)
                {
                    this.reserve_scratch(payload)?;
                }
                if let Some(id) = operation.result_id() {
                    if matches!(operation.kind, OperationKind::Load)
                        && this.selections.contains_key(&id)
                    {
                        this.slot(Value::Register(id), size_of::<DictionaryReference>() as u32)?;
                        this.owned_evidence.push(id);
                        continue;
                    }
                    match operation.kind {
                        OperationKind::BuildClosure { .. }
                        | OperationKind::CloneClosureEnv { .. } => {
                            // Generic Value glue can erase the function type, but these operations
                            // still produce the fixed descriptor/environment representation.
                            this.slot(
                                Value::Register(id),
                                size_of::<DictionaryReference>() as u32,
                            )?;
                            this.callable_values.insert(id);
                            continue;
                        }
                        OperationKind::BuildDictionary { definition, .. } => {
                            this.dictionary_definitions.insert(id, operation);
                            this.slot(
                                Value::Register(id),
                                size_of::<DictionaryReference>() as u32,
                            )?;
                            this.owned_evidence.push(id);
                            let bytes = program
                                .dictionary(definition)
                                .unwrap()
                                .environment()
                                .allocation
                                .size();
                            let offset = this.reserve_bytes(bytes as u32)?;
                            this.capture_slots.insert(id, offset);
                            continue;
                        }
                        OperationKind::DictEntry { .. } => {
                            this.slot(
                                Value::Register(id),
                                size_of::<DictionaryReference>() as u32,
                            )?;
                            this.owned_evidence.push(id);
                            continue;
                        }
                        OperationKind::Variant { .. } => {
                            this.slot(Value::Register(id), 4)?;
                            this.variant_shells.insert(id);
                            continue;
                        }
                        _ => (),
                    }
                    let storage_ty = match &operation.kind {
                        OperationKind::Alloca { ty } if operation.operands.is_empty() => {
                            Some(MirType::Lowered(*ty))
                        }
                        OperationKind::AllocaPlace { .. } => {
                            Some(MirType::Pointer(Box::new(MirType::Lowered(Type::unit()))))
                        }
                        _ => None,
                    };
                    if let Some(ty) = storage_ty {
                        let value = Value::Register(id);
                        if !addressed.contains(&value)
                            && let Ok(ty) = scalar(&ty)
                        {
                            let local = this.local(ty.wasm());
                            this.storage.insert(value, Storage::Local(local));
                        } else {
                            this.slot(value, this.size(&ty)?)?;
                        }
                        continue;
                    }
                    let role = this
                        .roles
                        .get(&Value::Register(id), body.constants())
                        .unwrap()
                        .into_owned();
                    if let ValueRole::Materialized(MirType::Lowered(ty)) = &role
                        && let Ok(ty) = ScalarType::of(*ty)
                        && addressed.contains(&Value::Register(id))
                    {
                        this.slot(Value::Register(id), ty.size())?;
                    }
                    let ty = match &role {
                        ValueRole::Place(_) | ValueRole::StackMarker | ValueRole::VariantTag => {
                            ValType::I32
                        }
                        ValueRole::Materialized(ty) => match scalar(ty) {
                            Ok(ty) => ty.wasm(),
                            Err(_) => {
                                this.slot(Value::Register(id), this.size(ty)?)?;
                                continue;
                            }
                        },
                        _ => {
                            return Err(format!(
                                "unsupported result role for {}",
                                OperationKindDiscriminant::from(&operation.kind)
                            ));
                        }
                    };
                    let local = this.local(ty);
                    this.registers.insert(id, local);
                }
            }
        }
        if !this.selections.is_empty() {
            this.reserve_scratch(Type::unit())?;
        }
        if !this.selections.is_empty() || this.layout_slot.is_some() {
            this.evidence_base = Some(this.local(ValType::I32));
        }
        if this.layout_slot.is_some() {
            this.layout_locals = Some(LayoutLocals {
                dictionary: this.local(ValType::I32),
                table: this.local(ValType::I32),
                output: this.local(ValType::I32),
            });
        }
        if this.frame_size != 0 {
            this.frame = Some(this.local(ValType::I32));
        }
        this.code = WasmFunction::new(this.locals.iter().map(|ty| (1, *ty)));
        Ok(this)
    }

    fn size(&self, ty: &MirType) -> Result<u32, String> {
        match ty {
            MirType::Pointer(_) => Ok(ScalarType::pointer().size()),
            MirType::Lowered(ty) => {
                let layout = value_layout_for_type(*ty, Location::new_synthesized(), &self.env)
                    .map_err(|e| format!("Wasm storage layout: {e:?}"))?;
                if layout.align > 8 {
                    return Err("Wasm frame alignment above eight bytes".into());
                }
                Ok(layout.size)
            }
        }
    }

    fn optional_payload(&self, target: FunctionId) -> Option<Type> {
        let native = self.program.module(target.module)?.native_entry(target)?;
        match native.signature().result {
            NativeResult::Optional { payload, .. } => Some(payload.ty),
            _ => None,
        }
    }

    fn reserve_scratch(&mut self, ty: Type) -> Result<(), String> {
        if !self.scratch_slots.contains_key(&ty) {
            let size = self.size(&MirType::Lowered(ty))?;
            let offset = self.reserve_bytes(size)?;
            self.scratch_slots.insert(ty, offset);
        }
        Ok(())
    }

    fn scratch_address(&mut self, ty: Type) {
        self.frame_address(self.scratch_slots[&ty]);
    }

    /// Turn the native presence result and temporary payload into an owned Ferlium Option.
    fn finish_optional(&mut self, output: &Value, payload: Type) -> Result<(), String> {
        let MirType::Lowered(ty) = self.pointee_type(output)? else {
            return Err("optional output must be a value place".into());
        };
        let adapter = NativeOptionalResultAdapter::new(ty, payload, self.env, self.session)?;
        // Preserve the presence result on the operand stack while preparing the two addresses.
        self.address(output)?;
        self.i(I::LocalSet(self.dynamic_base.as_u32()));
        self.scratch_address(payload);
        self.i(I::LocalSet(self.dynamic_size.as_u32()));
        adapter.emit(
            &mut self.code,
            self.dynamic_base,
            self.dynamic_size,
            self.scratch,
            self.imports.function_index("alloc"),
        );
        Ok(())
    }

    pub(super) fn pointee_type(&self, value: &Value) -> Result<MirType, String> {
        self.roles
            .get(value, self.body.constants())
            .and_then(|role| role.place_pointee_type())
            .ok_or_else(|| "expected place".into())
    }

    pub(super) fn context_pointer(&mut self, offset: usize) {
        context_pointer(&mut self.code, offset);
    }

    fn frame_address(&mut self, offset: u32) {
        frame_address(
            &mut self.code,
            self.frame.expect("reserved frame storage"),
            offset,
        );
    }

    fn release_evidence(&mut self, reference: &Value) -> Result<(), String> {
        self.context_pointer(offset_of!(InvocationState, evidence));
        self.address(reference)?;
        self.i(I::Call(
            self.imports.function_index("release_evidence").as_u32(),
        ));
        Ok(())
    }

    fn dictionary_index(&mut self, dictionary: &Value, entry: usize) -> Result<(), String> {
        self.value(dictionary)?;
        self.dictionary_table();
        self.i(I::I32Load(MemArg {
            offset: entry as u64 * 4,
            ..memarg(2)
        }));
        Ok(())
    }

    /// Replace a dictionary reference on the operand stack with its immutable entry-table address.
    fn dictionary_table(&mut self) {
        let evidence_base = self
            .evidence_base
            .expect("dictionary lookup needs a base local");
        dictionary_table(&mut self.code, evidence_base);
    }

    pub(super) fn dynamic_layout(&mut self, dictionary: &Value) -> Result<(), String> {
        let slot = self
            .layout_slot
            .expect("layout witness needs output storage");
        let LayoutLocals {
            dictionary: dictionary_local,
            table,
            output,
        } = self.layout_locals.expect("layout witness needs locals");
        self.value(dictionary)?;
        self.i(I::LocalTee(dictionary_local.as_u32()));
        self.dictionary_table();
        self.i(I::LocalSet(table.as_u32()));
        self.frame_address(slot);
        self.i(I::LocalSet(output.as_u32()));
        for (index, entry) in self.layout_entries.into_iter().enumerate() {
            let (ty, _) = self.entry_abis[&entry];
            self.i(I::LocalGet(dictionary_local.as_u32()));
            self.i(I::LocalGet(output.as_u32()));
            self.i(I::LocalGet(table.as_u32()));
            self.i(I::I32Load(MemArg {
                offset: entry.1.as_index() as u64 * 4,
                ..memarg(2)
            }));
            self.i(I::CallIndirect {
                type_index: ty.as_u32(),
                table_index: 0,
            });
            // Each result is read before the next call, so both entries share one output slot.
            self.i(I::LocalGet(output.as_u32()));
            self.i(I::I32Load(memarg(2)));
            self.i(I::LocalSet(
                (if index == 0 {
                    self.dynamic_size
                } else {
                    self.dynamic_align
                })
                .as_u32(),
            ));
        }
        Ok(())
    }

    fn dynamic_alloca(&mut self) {
        allocate_frame(
            &mut self.code,
            self.dynamic_size,
            self.dynamic_align,
            self.dynamic_base,
            self.allocation_end,
        );
    }
    fn call_dictionary(
        &mut self,
        selected: &Value,
        inputs: &[&Value],
        output: Option<&Value>,
        invoked: bool,
    ) -> Result<(), String> {
        let Value::Register(id) = selected else {
            return Err("stored callable dispatch".into());
        };
        let key = *self
            .selections
            .get(id)
            .ok_or("non-dictionary indirect call")?;
        let entry_abis = self.entry_abis;
        let (ty, abi) = &entry_abis[&key];
        if inputs.len() + 1 != abi.parameters.len() {
            return Err("dictionary call argument count".into());
        }
        if abi.fallible {
            self.context_pointer(offset_of!(InvocationState, native_failure));
        }
        self.address(selected)?;
        self.call_inputs(inputs, &abi.parameters[1..])?;
        if let Some(output) = output {
            self.address(output)?;
        } else {
            self.scratch_address(Type::unit());
        }
        self.dictionary_index(selected, key.1.as_index())?;
        self.i(I::CallIndirect {
            type_index: ty.as_u32(),
            table_index: 0,
        });
        self.call_status(invoked, abi.fallible);
        Ok(())
    }

    fn call_inputs(
        &mut self,
        inputs: &[&Value],
        transports: &[ParameterTransport],
    ) -> Result<(), String> {
        for (input, transport) in inputs.iter().zip(transports) {
            match transport {
                ParameterTransport::Direct(_) => {
                    self.read(input)?;
                }
                ParameterTransport::Indirect => self.address(input)?,
            }
        }
        Ok(())
    }

    pub(super) fn call_status(&mut self, invoked: bool, fallible: bool) {
        if invoked && !fallible {
            self.i(I::I32Const(0));
        } else if !invoked && fallible {
            // A plain call promises success, even when its callee uses a status-return ABI.
            self.i(I::Drop);
        }
    }

    fn capture_failure(&mut self) {
        self.context_pointer(offset_of!(InvocationState, diagnostics));
        self.i(I::LocalGet(self.pending_failure.as_u32()));
        self.i(I::Call(
            self.imports.function_index("capture_failure").as_u32(),
        ));
        self.i(I::LocalSet(self.pending_failure.as_u32()));
    }

    fn propagate_failure(&mut self) {
        self.context_pointer(offset_of!(InvocationState, diagnostics));
        self.i(I::LocalGet(self.pending_failure.as_u32()));
        self.i(I::Call(
            self.imports.function_index("propagate_failure").as_u32(),
        ));
        self.i(I::If(BlockType::Empty));
        self.fail(FailureCode::Source);
        self.i(I::End);
    }

    fn return_frame(&mut self, failed: bool) -> Result<(), String> {
        if failed && !self.signature.fallible {
            return Err("failure in an infallible entry".into());
        }
        for index in 0..self.owned_evidence.len() {
            self.release_evidence(&Value::Register(self.owned_evidence[index]))?;
        }
        if let Some(frame) = self.frame {
            leave_frame(&mut self.code, frame);
        }
        self.i(I::GlobalGet(Global::Depth as u32));
        self.i(I::I32Const(1));
        self.i(I::I32Sub);
        self.i(I::GlobalSet(Global::Depth as u32));
        if self.signature.fallible {
            self.i(I::I32Const(i32::from(failed)));
        } else if matches!(self.signature.result, ResultKind::Direct(_)) {
            let result =
                Value::Parameter(ParameterId::from_index(self.body.parameters().len() - 1));
            self.load_place(&result, self.pointee(&result)?)?;
        }
        self.i(I::Return);
        Ok(())
    }

    fn initialize_literal(
        &mut self,
        destination: &Value,
        ty: Type,
        literal: &LiteralValue,
        offset: u32,
    ) -> Result<(), String> {
        if let Some(text) = literal.as_primitive_ty::<StaticStr>() {
            let index = self.strings.intern(*text);
            self.address(destination)?;
            self.i(I::I32Const(offset as i32));
            self.i(I::I32Add);
            self.context_pointer(offset_of!(InvocationState, strings));
            self.i(I::I32Const((index * size_of::<StaticStr>()) as i32));
            self.i(I::I32Add);
            self.i(I::I32Const(size_of::<StaticStr>() as i32));
            self.i(I::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            });
        } else if let LiteralValue::Tuple(fields) = literal {
            let layout = product_layout_spec(ty, Location::new_synthesized(), &self.env)
                .ok_or("expected product constant")?;
            for (index, field) in fields.iter().enumerate() {
                let field_offset = layout
                    .static_field_offset(ProjectionIndex::from_index(index))
                    .ok_or("open constant layout")? as u32;
                self.initialize_literal(
                    destination,
                    layout.members[index].ty,
                    field,
                    offset + field_offset,
                )?;
            }
        } else {
            self.address(destination)?;
            self.i(I::I32Const(offset as i32));
            self.i(I::I32Add);
            self.literal(literal)?;
            self.store(ScalarType::of(ty)?);
        }
        Ok(())
    }

    fn call_operation(&mut self, op: &Operation, invoked: bool) -> Result<(), String> {
        let callee = callee(op).ok_or("unsupported fallible operation")?;
        let (inputs, output): (Vec<_>, _) = match &op.kind {
            OperationKind::Call { ty, .. } => {
                let output = ty
                    .result_convention
                    .has_result_place()
                    .then(|| op.operands.last().unwrap());
                (
                    op.operands[1..op.operands.len() - usize::from(output.is_some())]
                        .iter()
                        .collect(),
                    output,
                )
            }
            OperationKind::Clone { .. } => (
                op.operands[3..].iter().chain([&op.operands[0]]).collect(),
                Some(&op.operands[1]),
            ),
            OperationKind::Drop { .. } | OperationKind::DropInitialized { .. } => (
                op.operands[2..].iter().chain([&op.operands[0]]).collect(),
                None,
            ),
            _ => return Err("unsupported call operation".into()),
        };
        let Value::Function(target) = callee else {
            if !matches!(callee, Value::Register(id) if self.selections.contains_key(id)) {
                return self.call_stored(callee, &inputs, output, invoked);
            }
            return self.call_dictionary(callee, &inputs, output, invoked);
        };
        // Static calls bypass fixed Value adapters without adding a source call-depth frame.
        let target = self.program.direct_entry(*target);
        let callees = self.callees;
        let (index, abi) = callees.get(&target).ok_or("unresolved callee")?;
        if inputs.len() != abi.parameters.len() {
            return Err("hidden call evidence".into());
        }
        let direct_result = if !abi.fallible {
            match abi.result {
                ResultKind::Direct(_) => Some(self.pointee(output.ok_or("missing result")?)?),
                _ => None,
            }
        } else {
            None
        };
        if direct_result.is_some() {
            self.prepare_store(output.unwrap())?;
        }
        if abi.fallible {
            self.context_pointer(offset_of!(InvocationState, native_failure));
        }
        self.call_inputs(&inputs, &abi.parameters)?;
        let optional_payload = self.optional_payload(target);
        if let Some(payload) = optional_payload {
            self.scratch_address(payload);
        } else if abi.output() {
            self.address(output.ok_or("missing output storage")?)?;
        }
        self.i(I::Call(index.as_u32()));
        if let Some(payload) = optional_payload {
            self.finish_optional(output.ok_or("missing optional output")?, payload)?;
        }
        if let Some(ty) = direct_result {
            self.finish_store(output.unwrap(), ty);
        }
        self.call_status(invoked, abi.fallible);
        Ok(())
    }

    fn local(&mut self, ty: ValType) -> WasmLocalId {
        let id = WasmLocalId::from_index(self.signature.parameter_count() + self.locals.len());
        self.locals.push(ty);
        id
    }

    /// Only explicit content reads/writes permit promotion. Taking an offset, storing a pointer,
    /// passing an indirect argument, or any unmodelled use keeps that root in memory. No alias
    /// analysis is needed: deriving an alias already observes the original root's address.
    fn address_observations(&self) -> FxHashSet<Value> {
        let mut addressed = FxHashSet::default();
        for block in self.body.blocks() {
            let block = self.body.block(block);
            for op in operations(block) {
                let call_abi = if matches!(op.kind, OperationKind::Call { .. })
                    && let Value::Function(target) = &op.operands[0]
                {
                    self.callees
                        .get(&self.program.direct_entry(*target))
                        .map(|(_, abi)| *abi)
                } else {
                    None
                };
                for (index, operand) in op.operands.iter().enumerate() {
                    let observes = match &op.kind {
                        OperationKind::Load
                        | OperationKind::Clear
                        | OperationKind::Memcpy
                        | OperationKind::Move
                        | OperationKind::MoveBytes { .. }
                        | OperationKind::CompareEqual => false,
                        OperationKind::Store if index == 1 => false,
                        OperationKind::Store => self
                            .roles
                            .get(operand, self.body.constants())
                            .is_some_and(|r| r.is_place_operand()),
                        OperationKind::AddressOffset { .. }
                        | OperationKind::AddressOffsetPlace { .. }
                            if index == 1 =>
                        {
                            false
                        }
                        OperationKind::Call { ty, .. } => {
                            if index + 1 == op.operands.len()
                                && ty.result_convention.has_result_place()
                            {
                                call_abi.is_none_or(CallAbi::output)
                            } else {
                                !index
                                    .checked_sub(1)
                                    .and_then(|i| call_abi?.parameters.get(i))
                                    .is_some_and(|p| matches!(p, ParameterTransport::Direct(_)))
                            }
                        }
                        _ => true,
                    };
                    if observes {
                        addressed.insert(operand.clone());
                    }
                }
            }
            if !matches!(
                block.terminator().kind,
                TerminatorKind::CondBr { .. } | TerminatorKind::Invoke { .. }
            ) {
                addressed.extend(block.terminator().operands().iter().cloned());
            }
        }
        addressed
    }

    fn slot(&mut self, value: Value, size: u32) -> Result<(), String> {
        // All slots are 8-aligned, including distinct zero-sized places.
        let offset = self.reserve_bytes(size)?;
        self.storage.insert(value, Storage::Stack(offset));
        Ok(())
    }

    fn reserve_bytes(&mut self, size: u32) -> Result<u32, String> {
        let offset = self.frame_size;
        self.frame_size = self
            .frame_size
            .checked_add(frame_bytes(size)?)
            .ok_or("frame size overflow")?;
        Ok(offset)
    }

    pub(super) fn i(&mut self, instruction: I<'_>) {
        self.code.instruction(&instruction);
    }

    fn fail(&mut self, code: FailureCode) {
        // A host can reach the exported entry without installing an invocation. Trap without
        // touching low linear memory when there is no diagnostic destination.
        emit_failure(&mut self.code, code);
    }

    pub(super) fn address(&mut self, value: &Value) -> Result<(), String> {
        match self.storage.get(value) {
            Some(Storage::Stack(offset)) => {
                let offset = *offset;
                self.frame_address(offset);
            }
            Some(Storage::Local(_)) => return Err("address requested for promoted storage".into()),
            None => self.value(value)?,
        }
        Ok(())
    }

    pub(super) fn value(&mut self, value: &Value) -> Result<(), String> {
        if let Value::Function(target) = value {
            let offset = *self
                .callable_entries
                .references
                .get(target)
                .ok_or("unresolved stored function")?;
            self.context_pointer(offset_of!(InvocationState, evidence));
            self.i(I::I32Const(offset as i32));
            self.i(I::I32Add);
            return Ok(());
        }
        if let Some(id) = self.program.evidence_id(value) {
            self.context_pointer(offset_of!(InvocationState, evidence));
            self.i(I::I32Const(self.evidence.references[&id] as i32));
            self.i(I::I32Add);
            return Ok(());
        }
        if self.storage.contains_key(value)
            && !self
                .roles
                .get(value, self.body.constants())
                .is_some_and(|r| matches!(&*r, ValueRole::Materialized(ty) if scalar(ty).is_ok()))
        {
            return self.address(value);
        }
        match value {
            Value::Register(id) => self.i(I::LocalGet(self.registers[id].as_u32())),
            Value::Parameter(id) => self.i(I::LocalGet(
                (if self.body.parameters()[id.as_index()].kind == ParameterKind::Return {
                    self.signature.output_local()
                } else {
                    self.signature.input_local(id.as_index())
                })
                .as_u32(),
            )),
            Value::Constant(id) => self.literal(&self.body.constant(*id).representation)?,
            Value::Pattern(literal) => self.literal(literal)?,
            _ => return Err(format!("unsupported operand {value}")),
        }
        Ok(())
    }

    fn literal(&mut self, literal: &LiteralValue) -> Result<(), String> {
        if let LiteralValue::VariantTag(tag) = literal {
            self.i(I::I32Const(self.session.variant_tag_id(*tag) as i32));
        } else if let Some(value) = literal.as_primitive_ty::<isize>() {
            self.i(I::I32Const(*value as i32));
        } else if let Some(value) = literal.as_primitive_ty::<bool>() {
            self.i(I::I32Const(i32::from(*value)));
        } else if let Some(value) = literal.as_primitive_ty::<Float>() {
            self.i(I::F64Const(value.into_inner().into()));
        } else if literal.as_primitive_ty::<()>().is_some() {
            self.i(I::I32Const(0));
        } else {
            return Err("non-scalar literal".into());
        }
        Ok(())
    }

    fn pointee(&self, value: &Value) -> Result<ScalarType, String> {
        scalar(
            &self
                .roles
                .get(value, self.body.constants())
                .and_then(|r| r.place_pointee_type())
                .ok_or("expected scalar place")?,
        )
    }

    pub(super) fn read(&mut self, value: &Value) -> Result<ScalarType, String> {
        let role = self
            .roles
            .get(value, self.body.constants())
            .ok_or("missing operand role")?;
        let storage_parameter = matches!(value, Value::Parameter(id)
            if self.body.parameters()[id.as_index()].kind == ParameterKind::Dictionary
                && self.body.parameters()[id.as_index()].ty == bool_type());
        if matches!(&*role, ValueRole::VariantPayloadStorage) || storage_parameter {
            let ty = ScalarType::native(NativeScalar::Bool);
            self.value(value)?;
            self.load(ty);
            return Ok(ty);
        }
        if matches!(&*role, ValueRole::VariantTag) {
            self.value(value)?;
            return Ok(ScalarType::pointer());
        }
        if let Some(pointee) = role.place_pointee_type() {
            let ty = scalar(&pointee)?;
            self.load_place(value, ty)?;
            Ok(ty)
        } else {
            let ValueRole::Materialized(ty) = &*role else {
                return Err("expected scalar value".into());
            };
            let ty = scalar(ty)?;
            self.value(value)?;
            Ok(ty)
        }
    }

    fn load_place(&mut self, value: &Value, ty: ScalarType) -> Result<(), String> {
        if let Some(&Storage::Local(local)) = self.storage.get(value) {
            self.i(I::LocalGet(local.as_u32()));
        } else {
            self.address(value)?;
            self.load(ty);
        }
        Ok(())
    }

    // A memory store needs its address below the value; a local store needs only the value.
    fn prepare_store(&mut self, destination: &Value) -> Result<(), String> {
        if !matches!(self.storage.get(destination), Some(Storage::Local(_))) {
            self.address(destination)?;
        }
        Ok(())
    }

    fn finish_store(&mut self, destination: &Value, ty: ScalarType) {
        if let Some(&Storage::Local(local)) = self.storage.get(destination) {
            self.i(I::LocalSet(local.as_u32()));
        } else {
            self.store(ty);
        }
    }

    fn load(&mut self, ty: ScalarType) {
        ty.load(&mut self.code);
    }

    fn store(&mut self, ty: ScalarType) {
        ty.store(&mut self.code);
    }

    pub(super) fn emit(mut self) -> Result<WasmFunction, String> {
        if let Some(frame) = self.frame {
            enter_frame(&mut self.code, frame, self.frame_size);
        }
        self.i(I::GlobalGet(Global::Depth as u32));
        self.i(I::I32Const(1));
        self.i(I::I32Add);
        self.i(I::GlobalSet(Global::Depth as u32));
        for index in 0..self.owned_evidence.len() {
            self.address(&Value::Register(self.owned_evidence[index]))?;
            self.i(I::I64Const(0));
            self.i(I::I64Store(memarg(2)));
        }
        for (index, constant) in self.body.constants().iter().enumerate() {
            let value = Value::Constant(ConstantId::from_index(index));
            if self.storage.contains_key(&value) {
                self.initialize_literal(&value, constant.ty, &constant.representation, 0)?;
            }
        }
        for (index, transport) in self.signature.parameters.iter().enumerate() {
            let value = Value::Parameter(ParameterId::from_index(index));
            if matches!(transport, ParameterTransport::Direct(_))
                && matches!(self.storage.get(&value), Some(Storage::Stack(_)))
            {
                self.address(&value)?;
                self.i(I::LocalGet(self.signature.input_local(index).as_u32()));
                self.store(ScalarType::of(self.body.parameters()[index].ty)?);
            }
        }
        if let Some(pc) = self.pc {
            let count = self.body.blocks().count() as u32;
            self.i(I::Loop(BlockType::Empty));
            // The outer block is the invalid-PC target; each inner block exits at one MIR body.
            // At case i's code, count - i enclosing labels lead back to the dispatcher loop.
            self.i(I::Block(BlockType::Empty));
            for _ in 0..count {
                self.i(I::Block(BlockType::Empty));
            }
            self.i(I::LocalGet(pc.as_u32()));
            self.i(I::BrTable((0..count).collect::<Vec<_>>().into(), count));
            for block_id in self.body.blocks() {
                self.i(I::End);
                self.emit_block(block_id, Some(count - block_id.as_u32()))?;
            }
            self.i(I::End);
            self.fail(FailureCode::Invariant);
            self.i(I::End);
        } else {
            self.emit_block(self.body.entry(), None)?;
        }
        self.i(I::Unreachable);
        self.i(I::End);
        Ok(self.code)
    }

    fn emit_block(&mut self, block_id: BlockId, dispatch_depth: Option<u32>) -> Result<(), String> {
        let block = self.body.block(block_id);
        for operation in block.operations() {
            self.operation(operation).map_err(|e| {
                format!(
                    "{} in block {}: {e}",
                    OperationKindDiscriminant::from(&operation.kind),
                    block_id.as_u32()
                )
            })?;
        }
        match &block.terminator().kind {
            TerminatorKind::Goto { target } => {
                self.i(I::I32Const(target.as_u32() as i32));
                self.jump(dispatch_depth);
            }
            TerminatorKind::CondBr {
                condition,
                then_target,
                else_target,
            } => {
                self.i(I::I32Const(then_target.as_u32() as i32));
                self.i(I::I32Const(else_target.as_u32() as i32));
                self.read(condition)?;
                self.i(I::Select);
                self.jump(dispatch_depth);
            }
            TerminatorKind::SwitchVariant {
                tag,
                cases,
                default,
            } => {
                self.i(I::I32Const(default.as_u32() as i32));
                for (case, target) in cases {
                    self.i(I::I32Const(target.as_u32() as i32));
                    self.value(tag)?;
                    self.i(I::I32Const(self.session.variant_tag_id(*case) as i32));
                    self.i(I::I32Ne);
                    self.i(I::Select);
                }
                self.jump(dispatch_depth);
            }
            TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } => {
                self.call_operation(operation, true)?;
                self.i(I::If(BlockType::Result(ValType::I32)));
                self.capture_failure();
                self.i(I::I32Const(error.as_u32() as i32));
                self.i(I::Else);
                self.i(I::I32Const(normal.as_u32() as i32));
                self.i(I::End);
                self.jump(dispatch_depth);
            }
            TerminatorKind::PropagateError | TerminatorKind::FailureDuringCleanup => {
                self.propagate_failure();
                if matches!(
                    block.terminator().kind,
                    TerminatorKind::FailureDuringCleanup
                ) {
                    // A correctly chained cleanup failure already trapped while propagating.
                    self.fail(FailureCode::Invariant);
                } else {
                    self.return_frame(true)?;
                }
            }
            TerminatorKind::Return => self.return_frame(false)?,
            TerminatorKind::InvariantFailure { .. } => self.fail(FailureCode::Invariant),
            _ => return Err("unsupported terminator".into()),
        }
        Ok(())
    }

    fn jump(&mut self, dispatch_depth: Option<u32>) {
        self.i(I::LocalSet(
            self.pc.expect("branch needs a dispatcher").as_u32(),
        ));
        self.i(I::Br(dispatch_depth.expect("branch needs a dispatcher")));
    }

    fn operation(&mut self, op: &Operation) -> Result<(), String> {
        use OperationKind::*;
        let args = &op.operands;
        if matches!(op.kind, Store | Move | Memcpy | MoveBytes { .. })
            && let Value::Register(id) = &args[0]
            && let Some(&entry) = self.selections.get(id)
        {
            return self.store_selected(&args[0], &args[1], entry);
        }
        match &op.kind {
            BuildClosure { .. } => {
                self.build_closure(op)?;
                return Ok(());
            }
            CloneClosureEnv { .. } => {
                let clone = self
                    .callable_entries
                    .clone
                    .ok_or("missing callable environment clone entry")?;
                let result = Value::Register(op.result_id().unwrap());
                self.address(&result)?;
                self.address(&args[0])?;
                self.i(I::I32Load(memarg(2)));
                self.i(I::I32Store(memarg(2)));
                self.address(&result)?;
                self.address(&args[0])?;
                self.i(I::I32Load(MemArg {
                    offset: ENVIRONMENT_OFFSET,
                    ..memarg(2)
                }));
                self.i(I::Call(clone.as_u32()));
                self.i(I::I32Store(MemArg {
                    offset: ENVIRONMENT_OFFSET,
                    ..memarg(2)
                }));
                return Ok(());
            }
            DropClosureEnv => {
                let drop = self
                    .callable_entries
                    .drop
                    .ok_or("missing callable environment drop entry")?;
                self.address(&args[0])?;
                self.i(I::I32Load(MemArg {
                    offset: ENVIRONMENT_OFFSET,
                    ..memarg(2)
                }));
                // Detach ownership before guest destruction; poisoning must never retry it.
                self.address(&args[0])?;
                self.i(I::I64Const(0));
                self.i(I::I64Store(memarg(2)));
                self.i(I::Call(drop.as_u32()));
            }
            BuildArray { element_ty } => {
                let (destination, elements) = args.split_last().unwrap();
                let MirType::Lowered(array_ty) = self.pointee_type(destination)? else {
                    return Err("array output must be a value place".into());
                };
                let layout = product_layout_spec(array_ty, op.span, &self.env)
                    .ok_or("array representation")?;
                let element = value_layout_for_type(*element_ty, op.span, &self.env)
                    .map_err(|e| format!("array element layout: {e:?}"))?;
                let bytes = element
                    .size
                    .checked_mul(elements.len() as u32)
                    .ok_or("array allocation overflow")?;
                self.i(I::I32Const(bytes as i32));
                self.i(I::I32Const(element.align as i32));
                self.i(I::Call(self.imports.function_index("alloc").as_u32()));
                self.i(I::LocalSet(self.scratch.as_u32()));
                for (index, value) in elements.iter().enumerate() {
                    self.i(I::LocalGet(self.scratch.as_u32()));
                    self.i(I::I32Const((index as u32 * element.size) as i32));
                    self.i(I::I32Add);
                    if let Ok(ty) = ScalarType::of(*element_ty) {
                        self.read(value)?;
                        self.store(ty);
                    } else {
                        self.address(value)?;
                        self.i(I::I32Const(element.size as i32));
                        self.i(I::MemoryCopy {
                            src_mem: 0,
                            dst_mem: 0,
                        });
                    }
                }
                // The compiler-known array fields are normalized as capacity, data, len, start.
                for index in 0..4 {
                    self.address(destination)?;
                    if index == 1 {
                        self.i(I::LocalGet(self.scratch.as_u32()));
                    } else {
                        self.i(I::I32Const(if index == 3 {
                            0
                        } else {
                            elements.len() as i32
                        }));
                    }
                    self.i(I::I32Store(MemArg {
                        offset: layout
                            .static_field_offset(ProjectionIndex::from_index(index))
                            .ok_or("open array field offset")?
                            as u64,
                        ..memarg(2)
                    }));
                }
            }
            BuildDictionary { definition, .. } => {
                let result = Value::Register(op.result_id().unwrap());
                self.release_evidence(&result)?;
                let program = self.program;
                let fields = &program
                    .dictionary(*definition)
                    .unwrap()
                    .environment()
                    .fields;
                let capture_offset = self.capture_slots[&op.result_id().unwrap()];
                for (field, argument) in fields.iter().zip(args) {
                    self.frame_address(capture_offset + field.offset as u32);
                    if field.is_storage_flag {
                        self.read(argument)?;
                        self.i(I::I32Store8(memarg(0)));
                    } else {
                        self.value(argument)?;
                        self.i(I::I32Const(size_of::<DictionaryReference>() as i32));
                        self.i(I::MemoryCopy {
                            src_mem: 0,
                            dst_mem: 0,
                        });
                    }
                }
                self.context_pointer(offset_of!(InvocationState, evidence));
                self.i(I::I32Const(
                    self.program.descriptor_index(*definition).unwrap().as_u32() as i32,
                ));
                self.frame_address(capture_offset);
                self.address(&result)?;
                self.i(I::Call(
                    self.imports.function_index("build_evidence").as_u32(),
                ));
                return Ok(());
            }
            DictEntry { .. } | Load
                if matches!(op.kind, DictEntry { .. })
                    || op
                        .result_id()
                        .is_some_and(|id| self.selections.contains_key(&id)) =>
            {
                let result = Value::Register(op.result_id().unwrap());
                self.release_evidence(&result)?;
                self.address(&result)?;
                self.value(&args[0])?;
                self.i(I::I32Const(size_of::<DictionaryReference>() as i32));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&result)?;
                self.i(I::Call(
                    self.imports.function_index("retain_evidence").as_u32(),
                ));
                return Ok(());
            }
            Alloca { .. } if !args.is_empty() => {
                self.dynamic_layout(&args[0])?;
                self.dynamic_alloca();
            }
            Alloca { .. } | AllocaPlace { .. } => {
                let value = Value::Register(op.result_id().unwrap());
                if !self.storage.contains_key(&value) {
                    return Err("dynamic storage".into());
                }
                // The frame/local was reserved at entry; valid MIR never reads an absent lifetime.
                return Ok(());
            }
            Load => {
                let ty = self.pointee_type(&args[0])?;
                if let Ok(scalar) = scalar(&ty) {
                    self.load_place(&args[0], scalar)?;
                } else {
                    self.address(&Value::Register(op.result_id().unwrap()))?;
                    self.address(&args[0])?;
                    self.i(I::I32Const(self.size(&ty)? as i32));
                    self.i(I::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });
                    return Ok(());
                }
            }
            Store => {
                // Store takes a materialized value, including a pointer; it must not dereference
                // a place operand as read() would. The MIR verifier checks this operand contract.
                if matches!(&args[0], Value::Register(id) if self.callable_values.contains(id)) {
                    self.address(&args[1])?;
                    self.address(&args[0])?;
                    self.i(I::I64Load(memarg(2)));
                    self.i(I::I64Store(memarg(2)));
                    return Ok(());
                }
                if matches!(&args[0], Value::Register(id) if self.variant_shells.contains(id)) {
                    self.address(&args[1])?;
                    self.address(&args[0])?;
                    self.i(I::I32Load(memarg(2)));
                    self.i(I::I32Store(memarg(2)));
                    return Ok(());
                }
                let ty = self.pointee_type(&args[1])?;
                if let Ok(ty) = scalar(&ty) {
                    self.prepare_store(&args[1])?;
                    self.value(&args[0])?;
                    self.finish_store(&args[1], ty);
                } else {
                    self.address(&args[1])?;
                    self.value(&args[0])?;
                    self.i(I::I32Const(self.size(&ty)? as i32));
                    self.i(I::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });
                }
            }
            Memcpy | Move | MoveBytes { .. } => {
                let ty = self.pointee_type(&args[1])?;
                if let Some(witness) = layout_witness(op) {
                    self.dynamic_layout(witness)?;
                }
                if let Ok(ty) = scalar(&ty) {
                    self.prepare_store(&args[1])?;
                    self.read(&args[0])?;
                    self.finish_store(&args[1], ty);
                } else {
                    self.address(&args[1])?;
                    self.address(&args[0])?;
                    if matches!(op.kind, MoveBytes { .. }) {
                        self.read(&args[2])?;
                    } else if layout_witness(op).is_some() {
                        self.i(I::LocalGet(self.dynamic_size.as_u32()));
                    } else {
                        self.i(I::I32Const(self.size(&ty)? as i32));
                    }
                    self.i(I::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });
                }
            }
            Replace => {
                let MirType::Lowered(ty) = self.pointee_type(&args[0])? else {
                    return Err("pointer replacement".into());
                };
                if let Some(witness) = layout_witness(op) {
                    self.dynamic_layout(witness)?;
                    self.i(I::GlobalGet(Global::Stack as u32));
                    self.i(I::LocalSet(self.scratch.as_u32()));
                    self.dynamic_alloca();
                    self.i(I::Drop);
                } else {
                    self.scratch_address(ty);
                    self.i(I::LocalSet(self.dynamic_base.as_u32()));
                    self.i(I::I32Const(self.size(&MirType::Lowered(ty))? as i32));
                    self.i(I::LocalSet(self.dynamic_size.as_u32()));
                }
                self.i(I::LocalGet(self.dynamic_base.as_u32()));
                self.address(&args[0])?;
                self.i(I::LocalGet(self.dynamic_size.as_u32()));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&args[0])?;
                self.address(&args[1])?;
                self.i(I::LocalGet(self.dynamic_size.as_u32()));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&args[1])?;
                self.i(I::LocalGet(self.dynamic_base.as_u32()));
                self.i(I::LocalGet(self.dynamic_size.as_u32()));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                if layout_witness(op).is_some() {
                    self.i(I::LocalGet(self.scratch.as_u32()));
                    self.i(I::GlobalSet(Global::Stack as u32));
                }
            }
            AddressOffset { .. } | AddressOffsetPlace { .. } => {
                self.address(&args[0])?;
                self.read(&args[1])?;
                self.i(I::I32Add);
            }
            Clear => (), // Lifetimes are explicit in MIR; backing bytes may remain stale after cleanup.
            StackRestore => {
                self.value(&args[0])?;
                self.i(I::GlobalSet(Global::Stack as u32));
            }
            Variant { tag, storage, .. } => {
                self.address(&Value::Register(op.result_id().unwrap()))?;
                if let Some(storage) = storage {
                    self.i(I::I32Const(
                        storage.encode_tag_id(self.session.variant_tag_id(*tag)) as i32,
                    ));
                } else {
                    self.read(&args[0])?;
                    self.i(I::I32Const(31));
                    self.i(I::I32Shl);
                    self.i(I::I32Const(self.session.variant_tag_id(*tag) as i32));
                    self.i(I::I32Or);
                }
                self.i(I::I32Store(memarg(2)));
                // A shell initializes only the tag; physical MIR constructs its payload in place.
                return Ok(());
            }
            ExtractTag | ExtractPayloadIndirection => {
                self.address(&args[0])?;
                self.i(I::I32Load(memarg(2)));
                if matches!(op.kind, ExtractTag) {
                    self.i(I::I32Const(!VariantPayloadStorage::INDIRECT_TAG_BIT as i32));
                    self.i(I::I32And);
                } else {
                    self.i(I::I32Const(31));
                    self.i(I::I32ShrU);
                }
            }
            StackSave => self.i(I::GlobalGet(Global::Stack as u32)),
            CompareEqual => {
                let ty = self.read(&args[0])?;
                // The second operand is a compile-time Pattern, enforced by physical verification.
                self.value(&args[1])?;
                self.i(ty.equal());
            }
            CheckCallDepth => {
                self.i(I::GlobalGet(Global::Depth as u32));
                self.i(I::GlobalGet(Global::DepthLimit as u32));
                self.i(I::I32GeU);
                self.i(I::If(BlockType::Empty));
                self.fail(FailureCode::CallDepth);
                self.i(I::End);
            }
            CheckFuel => {
                self.i(I::GlobalGet(Global::FuelEnabled as u32));
                self.i(I::If(BlockType::Empty));
                self.i(I::GlobalGet(Global::Fuel as u32));
                self.i(I::I32Eqz);
                self.i(I::If(BlockType::Empty));
                self.fail(FailureCode::Fuel);
                self.i(I::End);
                self.i(I::GlobalGet(Global::Fuel as u32));
                self.i(I::I32Const(1));
                self.i(I::I32Sub);
                self.i(I::GlobalSet(Global::Fuel as u32));
                self.i(I::End);
            }
            Call { .. } | Clone { .. } | Drop { .. } | DropInitialized { .. } => {
                self.call_operation(op, false)?
            }
            RuntimeAlloc { .. } => {
                self.read(&args[0])?;
                self.read(&args[1])?;
                self.i(I::Call(self.imports.function_index("alloc").as_u32()));
            }
            RuntimeDealloc => {
                self.address(&args[0])?;
                self.i(I::Call(self.imports.function_index("dealloc").as_u32()));
            }
            _ => return Err("unsupported physical operation".into()),
        }
        if let Some(id) = op.result_id() {
            self.i(I::LocalSet(self.registers[&id].as_u32()));
            let value = Value::Register(id);
            if self.storage.contains_key(&value) {
                let role = self.roles.get(&value, self.body.constants()).unwrap();
                if let ValueRole::Materialized(ty) = &*role {
                    let ty = scalar(ty)?;
                    self.address(&value)?;
                    self.i(I::LocalGet(self.registers[&id].as_u32()));
                    self.store(ty);
                }
            }
        }
        Ok(())
    }
}
