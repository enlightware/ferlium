// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Per-function storage assignment and instruction emission.

use std::{mem::offset_of, ops::Range};

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
        pass::known_callee::KnownCallee,
        physical::{
            ConstructedSubscript, DictionaryReference, constructed_subscript_definitions,
            program::{Descriptor, ResolvedPhysicalProgram},
        },
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
    types::{
        r#trait::TraitDictionaryEntryIndex,
        r#type::{CallResultConvention, Type, TypeKind},
    },
    wasm::{
        Imports,
        abi::{
            CallAbi, DispatchTableSlotId, Parameter as ParameterTransport, ResultKind,
            WasmFunctionId, WasmLocalId, WasmTypeId,
        },
        evidence::{self, ENVIRONMENT_OFFSET},
        execution::{FailureCode, InvocationState},
    },
};

use super::{
    Global, RuntimeGlobals, ScalarType, StringLiterals,
    adapters::NativeOptionalResultAdapter,
    allocate_frame, callable, callee, context_pointer,
    control_flow::{ControlFlow, ControlRegion},
    dictionary_table, emit_failure, enter_frame, frame_address, frame_bytes, layout_witness,
    leave_frame, memarg, operations, scalar, subscript, wasm_intrinsic,
};

/// Code ranges generated for MIR operations and terminators, with their source spans.
pub(super) type BodySourceMap = Vec<(Range<usize>, Location)>;

#[derive(Clone, Copy)]
enum Storage {
    Local(WasmLocalId),
    /// Byte offset from the function's frame base in linear memory.
    Stack(u32),
}

#[derive(Clone, Copy)]
enum BranchContext {
    Linear,
    Loop { header: BlockId, exit: BlockId },
    Dispatcher { depth: u32 },
}

fn wasm_value_size(ty: ValType) -> u32 {
    match ty {
        ValType::I32 | ValType::F32 => 4,
        ValType::I64 | ValType::F64 => 8,
        _ => unreachable!("the Wasm32 backend emits only numeric locals"),
    }
}

pub(super) fn local_load(ty: ValType, offset: u32) -> I<'static> {
    match ty {
        ValType::I32 => I::I32Load(MemArg {
            offset: offset.into(),
            ..memarg(2)
        }),
        ValType::I64 => I::I64Load(MemArg {
            offset: offset.into(),
            ..memarg(3)
        }),
        ValType::F32 => I::F32Load(MemArg {
            offset: offset.into(),
            ..memarg(2)
        }),
        ValType::F64 => I::F64Load(MemArg {
            offset: offset.into(),
            ..memarg(3)
        }),
        _ => unreachable!("the Wasm32 backend emits only numeric locals"),
    }
}

fn local_store(ty: ValType) -> I<'static> {
    match ty {
        ValType::I32 => I::I32Store(memarg(2)),
        ValType::I64 => I::I64Store(memarg(3)),
        ValType::F32 => I::F32Store(memarg(2)),
        ValType::F64 => I::F64Store(memarg(3)),
        _ => unreachable!("the Wasm32 backend emits only numeric locals"),
    }
}

#[derive(Clone, Copy)]
struct LayoutLocals {
    dictionary: WasmLocalId,
    table: WasmLocalId,
    output: WasmLocalId,
}

#[derive(Clone, Copy)]
pub(super) struct HelperLocals {
    pub(super) pending_failure: WasmLocalId,
    pub(super) scratch: WasmLocalId,
    pub(super) dynamic_size: WasmLocalId,
    pub(super) dynamic_align: WasmLocalId,
    pub(super) dynamic_base: WasmLocalId,
    pub(super) allocation_end: WasmLocalId,
}

const RESUME_SLOT_OFFSET: u32 = 0;
const RESUME_BLOCK_OFFSET: u32 = 4;
const SUSPENDED_STACK_END_OFFSET: u32 = 8;
const CONTINUATION_HEADER_SIZE: u32 = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BodyMode {
    Normal,
    ProjectionStart { resume: DispatchTableSlotId },
    ProjectionResume,
}

impl BodyMode {
    fn extra_parameters(self) -> usize {
        usize::from(matches!(self, Self::ProjectionResume))
    }

    fn projection(self) -> bool {
        !matches!(self, Self::Normal)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SuspensionLayout {
    pub inputs: Vec<(u32, ValType)>,
    locals: Vec<(u32, ValType)>,
}

pub(super) struct EmittedBody {
    pub function: WasmFunction,
    pub source_map: BodySourceMap,
    pub suspension: Option<SuspensionLayout>,
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
    subscript_entries: &'a subscript::Entries,
    pub(super) callable_locals: Option<(WasmLocalId, WasmLocalId)>,
    callable_values: FxHashSet<ValueId>,
    subscript_values: FxHashSet<ValueId>,
    borrowed_subscripts: FxHashMap<ValueId, subscript::Borrowed>,
    projection_frames: FxHashMap<ValueId, WasmLocalId>,
    constructed_subscripts: FxHashMap<ValueId, ConstructedSubscript>,
    pub(super) dictionary_definitions: FxHashMap<ValueId, &'a Operation>,
    selections: &'s FxHashMap<ValueId, (TraitId, TraitDictionaryEntryIndex)>,
    owned_evidence: Vec<ValueId>,
    capture_slots: FxHashMap<ValueId, u32>,
    variant_shells: FxHashSet<ValueId>,
    layout_slot: Option<u32>,
    helpers: Option<HelperLocals>,
    evidence_base: Option<WasmLocalId>,
    layout_locals: Option<LayoutLocals>,
    scratch_slots: FxHashMap<Type, u32>,
    callees: &'a FxHashMap<FunctionId, (WasmFunctionId, &'a CallAbi)>,
    program: &'a ResolvedPhysicalProgram<'a>,
    session: &'a CompilerSession,
    registers: FxHashMap<ValueId, WasmLocalId>,
    storage: FxHashMap<Value, Storage>,
    locals: Vec<ValType>,
    mode: BodyMode,
    suspension: Option<SuspensionLayout>,
    /// Stack frontier on entry to a resumed accessor, below which its restores may not reach.
    resume_stack_floor: Option<WasmLocalId>,
    frame: Option<WasmLocalId>,
    pc: Option<WasmLocalId>,
    control_flow: Option<ControlFlow>,
    frame_size: u32,
    runtime_globals: RuntimeGlobals,
    track_depth: bool,
    forwarded_result: Option<Value>,
    fallthrough_return: bool,
    comparison_fusions: FxHashMap<ValueId, KnownCallee>,
    pub(super) code: WasmFunction,
    source_map: BodySourceMap,
}

impl<'a, 's> Body<'a, 's> {
    pub(super) fn helper_locals(&self) -> HelperLocals {
        self.helpers
            .expect("body operation requires reserved helper locals")
    }

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
        subscript_entries: &'a subscript::Entries,
        selections: &'s FxHashMap<ValueId, (TraitId, TraitDictionaryEntryIndex)>,
        mode: BodyMode,
        runtime_globals: RuntimeGlobals,
        track_depth: bool,
    ) -> Result<Self, String> {
        let constructed_subscripts = constructed_subscript_definitions(body);
        let control_flow = ControlFlow::of(body, mode);
        let dispatched = matches!(control_flow, ControlFlow::Dispatcher);
        let forwarded_result = forwarded_result(body, signature, mode);
        let fallthrough_return = has_fallthrough_return(body, mode, &control_flow);
        let comparison_fusions = comparison_fusions(body, session);
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
            subscript_entries,
            callable_locals: None,
            callable_values: FxHashSet::default(),
            subscript_values: FxHashSet::default(),
            borrowed_subscripts: FxHashMap::default(),
            projection_frames: FxHashMap::default(),
            constructed_subscripts,
            dictionary_definitions: FxHashMap::default(),
            selections,
            owned_evidence: Vec::new(),
            capture_slots: FxHashMap::default(),
            variant_shells: FxHashSet::default(),
            layout_slot: None,
            helpers: None,
            evidence_base: None,
            layout_locals: None,
            scratch_slots: FxHashMap::default(),
            callees,
            program,
            session,
            roles: ValueRoles::derive(body),
            registers: FxHashMap::default(),
            storage: FxHashMap::default(),
            locals: Vec::new(),
            mode,
            suspension: None,
            resume_stack_floor: None,
            frame: None,
            pc: None,
            control_flow: Some(control_flow),
            frame_size: if mode.projection() {
                CONTINUATION_HEADER_SIZE
            } else {
                0
            },
            runtime_globals,
            track_depth,
            forwarded_result,
            fallthrough_return,
            comparison_fusions,
            code: WasmFunction::new([]),
            source_map: Vec::new(),
        };
        if needs_helper_locals(body, mode) {
            this.helpers = Some(HelperLocals {
                pending_failure: this.local(ValType::I32),
                scratch: this.local(ValType::I32),
                dynamic_size: this.local(ValType::I32),
                dynamic_align: this.local(ValType::I32),
                dynamic_base: this.local(ValType::I32),
                allocation_end: this.local(ValType::I64),
            });
        }
        if dispatched {
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
                && !signature.output()
                && this.forwarded_result.is_none())
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
                    if let OperationKind::BorrowSubscriptMember { mut_member, .. } = operation.kind
                    {
                        let source = operation.operands[0].clone();
                        // Physical MIR represents symbolic subscript evidence as an evidence
                        // value and an owned first-class subscript as a place. This is the same
                        // distinction used by the physical interpreter; role verification rejects
                        // every other operand form before emission.
                        let materialized = this
                            .roles
                            .get(&source, body.constants())
                            .is_some_and(|role| role.is_place_operand());
                        this.borrowed_subscripts.insert(
                            id,
                            subscript::Borrowed {
                                source,
                                mut_member,
                                materialized,
                            },
                        );
                        continue;
                    }
                    if matches!(operation.kind, OperationKind::Project { .. }) {
                        let local = this.local(ValType::I32);
                        this.registers.insert(id, local);
                        let frame = this.local(ValType::I32);
                        this.projection_frames.insert(id, frame);
                        continue;
                    }
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
                        OperationKind::BuildSubscript { .. }
                        | OperationKind::CloneSubscriptEnv { .. } => {
                            this.slot(
                                Value::Register(id),
                                size_of::<DictionaryReference>() as u32,
                            )?;
                            this.subscript_values.insert(id);
                            continue;
                        }
                        OperationKind::BuildSubscriptEvidence { .. } => {
                            let constructed = *this
                                .constructed_subscripts
                                .get(&id)
                                .ok_or("dynamic subscript evidence base")?;
                            let definition = program
                                .subscript(constructed.definition)
                                .ok_or("missing subscript definition")?;
                            this.slot(
                                Value::Register(id),
                                size_of::<DictionaryReference>() as u32,
                            )?;
                            this.owned_evidence.push(id);
                            let offset = this
                                .reserve_bytes(definition.environment().allocation.size() as u32)?;
                            this.capture_slots.insert(id, offset);
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
                            let size = this.size(&ty).map_err(|error| {
                                format!(
                                    "{error} for result {id:?} of {}",
                                    OperationKindDiscriminant::from(&operation.kind)
                                )
                            })?;
                            this.slot(value, size)?;
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
                                let size = this.size(ty).map_err(|error| {
                                    format!(
                                        "{error} for result {id:?} of {}",
                                        OperationKindDiscriminant::from(&operation.kind)
                                    )
                                })?;
                                this.slot(Value::Register(id), size)?;
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
        if !this.projection_frames.is_empty() {
            this.reserve_scratch(Type::unit())?;
        }
        if !this.selections.is_empty()
            || !this.borrowed_subscripts.is_empty()
            || this.layout_slot.is_some()
        {
            this.evidence_base = Some(this.local(ValType::I32));
        }
        if this.layout_slot.is_some() {
            this.layout_locals = Some(LayoutLocals {
                dictionary: this.local(ValType::I32),
                table: this.local(ValType::I32),
                output: this.local(ValType::I32),
            });
        }
        if mode.projection() {
            let inputs = signature
                .parameters
                .iter()
                .map(|parameter| {
                    let ty = match parameter {
                        ParameterTransport::Direct(ty) => *ty,
                        ParameterTransport::Indirect => ValType::I32,
                    };
                    let offset = this.reserve_bytes(wasm_value_size(ty))?;
                    Ok((offset, ty))
                })
                .collect::<Result<Vec<_>, String>>()?;
            let local_count = this.locals.len();
            let locals = (0..local_count)
                .map(|index| {
                    let ty = this.locals[index];
                    let offset = this.reserve_bytes(wasm_value_size(ty))?;
                    Ok((offset, ty))
                })
                .collect::<Result<Vec<_>, String>>()?;
            this.suspension = Some(SuspensionLayout { inputs, locals });
            this.frame = Some(match mode {
                BodyMode::ProjectionStart { .. } => this.local(ValType::I32),
                BodyMode::ProjectionResume => WasmLocalId::from_index(signature.parameter_count()),
                BodyMode::Normal => unreachable!(),
            });
            if matches!(mode, BodyMode::ProjectionResume) {
                this.resume_stack_floor = Some(this.local(ValType::I32));
            }
        } else if this.frame_size != 0 {
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
        let helpers = self.helper_locals();
        // Preserve the presence result on the operand stack while preparing the two addresses.
        self.address(output)?;
        self.i(I::LocalSet(helpers.dynamic_base.as_u32()));
        self.scratch_address(payload);
        self.i(I::LocalSet(helpers.dynamic_size.as_u32()));
        adapter.emit(
            &mut self.code,
            helpers.dynamic_base,
            helpers.dynamic_size,
            helpers.scratch,
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

    fn store_local_in_frame(&mut self, local: WasmLocalId, offset: u32, ty: ValType) {
        self.frame_address(offset);
        self.i(I::LocalGet(local.as_u32()));
        self.i(local_store(ty));
    }

    fn load_local_from_frame(&mut self, local: WasmLocalId, offset: u32, ty: ValType) {
        self.frame_address(offset);
        self.i(local_load(ty, 0));
        self.i(I::LocalSet(local.as_u32()));
    }

    fn initialize_suspension(&mut self) {
        let input_count = self
            .suspension
            .as_ref()
            .expect("projected body has a suspension layout")
            .inputs
            .len();
        for index in 0..input_count {
            let (offset, ty) = self
                .suspension
                .as_ref()
                .expect("projected body has a suspension layout")
                .inputs[index];
            self.store_local_in_frame(self.signature.input_local(index), offset, ty);
        }
    }

    fn finish_project(&mut self, result: ValueId, invoked: bool) {
        let yielded = self.registers[&result];
        let frame = self.projection_frames[&result];
        self.i(I::LocalSet(yielded.as_u32()));
        self.i(I::LocalSet(frame.as_u32()));
        self.call_status(invoked, true);
    }

    fn project(&mut self, op: &Operation, invoked: bool) -> Result<(), String> {
        let helpers = self.helper_locals();
        let result = op.result_id().expect("project produces a place");
        let callee = &op.operands[0];
        let inputs = &op.operands[1..];
        if let Value::Register(id) = callee
            && let Some(selected) = self.borrowed_subscripts.get(id).cloned()
        {
            let ty = self.subscript_entries.signatures_by_arity[&inputs.len()];
            if selected.materialized {
                self.address(&selected.source)?;
            } else {
                self.value(&selected.source)?;
            }
            self.i(I::LocalTee(helpers.dynamic_base.as_u32()));
            self.dictionary_table();
            self.i(I::I32Load(MemArg {
                offset: u64::from(selected.mut_member) * 4,
                ..memarg(2)
            }));
            self.i(I::LocalSet(helpers.dynamic_size.as_u32()));
            self.context_pointer(offset_of!(InvocationState, native_failure));
            self.i(I::LocalGet(helpers.dynamic_base.as_u32()));
            self.i(I::I32Const(i32::from(selected.materialized)));
            for input in inputs {
                self.address(input)?;
            }
            self.i(I::LocalGet(helpers.dynamic_size.as_u32()));
            self.i(I::CallIndirect {
                type_index: ty.as_u32(),
                table_index: 0,
            });
            self.finish_project(result, invoked);
            return Ok(());
        }
        let Value::Function(target) = callee else {
            return Err("project requires a subscript member".into());
        };
        let target = self.program.direct_entry(*target);
        let (index, abi) = self.callees[&target];
        if inputs.len() != abi.parameters.len() {
            return Err("project argument count".into());
        }
        if abi.fallible {
            self.context_pointer(offset_of!(InvocationState, native_failure));
        }
        self.call_inputs(inputs.iter(), &abi.parameters)?;
        let convention = self
            .program
            .function(target)
            .map(Function::result_convention);
        if convention == Some(CallResultConvention::YIELDED_ONCE) {
            self.i(I::I32Const(0));
            self.i(I::Call(index.as_u32()));
            self.finish_project(result, invoked);
            return Ok(());
        }
        if !subscript::is_addressor_native(self.program, target)
            && convention != Some(CallResultConvention::ADDRESSOR_PLACE)
        {
            return Err("project target is not a place accessor".into());
        }
        if abi.output() {
            self.scratch_address(Type::unit());
        }
        self.i(I::Call(index.as_u32()));
        let yielded = self.registers[&result];
        if abi.fallible {
            self.i(I::LocalSet(helpers.dynamic_size.as_u32()));
            self.scratch_address(Type::unit());
            self.i(I::I32Load(memarg(2)));
            self.i(I::LocalSet(yielded.as_u32()));
            self.i(I::LocalGet(helpers.dynamic_size.as_u32()));
        } else {
            self.i(I::LocalSet(yielded.as_u32()));
            self.i(I::I32Const(0));
        }
        self.i(I::I32Const(0));
        self.i(I::LocalGet(yielded.as_u32()));
        self.finish_project(result, invoked);
        Ok(())
    }

    fn call_subscript_member(
        &mut self,
        selected: subscript::Borrowed,
        inputs: &[&Value],
        output: Option<&Value>,
        invoked: bool,
    ) -> Result<(), String> {
        let helpers = self.helper_locals();
        let output = output.ok_or("addressor call requires output storage")?;
        let ty = self.subscript_entries.signatures_by_arity[&inputs.len()];
        if selected.materialized {
            self.address(&selected.source)?;
        } else {
            self.value(&selected.source)?;
        }
        self.i(I::LocalTee(helpers.dynamic_base.as_u32()));
        self.dictionary_table();
        self.i(I::I32Load(MemArg {
            offset: u64::from(selected.mut_member) * 4,
            ..memarg(2)
        }));
        self.i(I::LocalSet(helpers.scratch.as_u32()));
        self.context_pointer(offset_of!(InvocationState, native_failure));
        self.i(I::LocalGet(helpers.dynamic_base.as_u32()));
        self.i(I::I32Const(i32::from(selected.materialized)));
        for input in inputs {
            self.address(input)?;
        }
        self.i(I::LocalGet(helpers.scratch.as_u32()));
        self.i(I::CallIndirect {
            type_index: ty.as_u32(),
            table_index: 0,
        });
        self.i(I::LocalSet(helpers.dynamic_base.as_u32())); // yielded address
        self.i(I::LocalSet(helpers.dynamic_align.as_u32())); // retained frame
        self.i(I::LocalSet(helpers.dynamic_size.as_u32())); // status
        self.i(I::LocalGet(helpers.dynamic_align.as_u32()));
        self.i(I::If(BlockType::Empty));
        self.fail(FailureCode::Invariant);
        self.i(I::End);
        self.address(output)?;
        self.i(I::LocalGet(helpers.dynamic_base.as_u32()));
        self.i(I::I32Store(memarg(2)));
        self.i(I::LocalGet(helpers.dynamic_size.as_u32()));
        self.call_status(invoked, true);
        Ok(())
    }

    fn end_project(&mut self, projected: &Value, invoked: bool) -> Result<(), String> {
        let Value::Register(id) = projected else {
            return Err("end_project requires its project result".into());
        };
        let frame = self.projection_frames[id];
        self.i(I::LocalGet(frame.as_u32()));
        self.i(I::If(BlockType::Result(ValType::I32)));
        self.context_pointer(offset_of!(InvocationState, native_failure));
        self.i(I::LocalGet(frame.as_u32()));
        self.i(I::LocalGet(frame.as_u32()));
        self.i(I::I32Load(MemArg {
            offset: RESUME_SLOT_OFFSET as u64,
            ..memarg(2)
        }));
        self.i(I::CallIndirect {
            type_index: self.subscript_entries.resume_signature.as_u32(),
            table_index: 0,
        });
        self.i(I::Else);
        self.i(I::I32Const(0));
        self.i(I::End);
        // The retained frame is dead on both success and source failure. Keeping zero in the
        // local also lets later stack restores ignore this completed projection.
        self.i(I::I32Const(0));
        self.i(I::LocalSet(frame.as_u32()));
        self.call_status(invoked, true);
        Ok(())
    }

    fn suspend(&mut self, yielded: &Value, resume: BlockId) -> Result<(), String> {
        let entry = match self.mode {
            BodyMode::ProjectionStart { resume } => resume,
            BodyMode::ProjectionResume => {
                self.fail(FailureCode::Invariant);
                return Ok(());
            }
            BodyMode::Normal => return Err("ordinary call yielded a place".into()),
        };
        let local_count = self
            .suspension
            .as_ref()
            .expect("projected body has a suspension layout")
            .locals
            .len();
        for index in 0..local_count {
            let (offset, ty) = self
                .suspension
                .as_ref()
                .expect("projected body has a suspension layout")
                .locals[index];
            let local = WasmLocalId::from_index(self.signature.parameter_count() + index);
            self.store_local_in_frame(local, offset, ty);
        }
        self.frame_address(RESUME_SLOT_OFFSET);
        self.i(I::I32Const(entry.as_u32() as i32));
        self.i(I::I32Store(memarg(2)));
        self.frame_address(RESUME_BLOCK_OFFSET);
        self.i(I::I32Const(resume.as_u32() as i32));
        self.i(I::I32Store(memarg(2)));
        // The caller may allocate above this retained frame before resuming it. Remember the
        // frontier so its stack restores cannot reclaim the continuation and completion can tell
        // caller-owned storage from allocations made by the resumed half itself.
        self.frame_address(SUSPENDED_STACK_END_OFFSET);
        self.i(I::GlobalGet(Global::Stack as u32));
        self.i(I::I32Store(memarg(2)));
        self.i(I::I32Const(0));
        self.i(I::LocalGet(self.frame.unwrap().as_u32()));
        self.address(yielded)?;
        self.i(I::Return);
        Ok(())
    }

    fn restore_suspension(&mut self) {
        let local_count = self
            .suspension
            .as_ref()
            .expect("projected body has a suspension layout")
            .locals
            .len();
        for index in 0..local_count {
            let (offset, ty) = self
                .suspension
                .as_ref()
                .expect("projected body has a suspension layout")
                .locals[index];
            let local = WasmLocalId::from_index(self.signature.parameter_count() + 1 + index);
            self.load_local_from_frame(local, offset, ty);
        }
        let pc = self.pc.expect("projected body uses a dispatcher");
        self.frame_address(RESUME_BLOCK_OFFSET);
        self.i(I::I32Load(memarg(2)));
        self.i(I::LocalSet(pc.as_u32()));
    }

    /// Restore a MIR stack marker without crossing a suspended continuation frame.
    fn restore_stack(&mut self, marker: &Value) -> Result<(), String> {
        let helpers = self.helper_locals();
        self.value(marker)?;
        self.i(I::LocalSet(helpers.scratch.as_u32()));
        if let Some(floor) = self.resume_stack_floor {
            self.raise_stack_floor(floor);
        }
        let mut frames = self
            .projection_frames
            .iter()
            .map(|(id, frame)| (*id, *frame))
            .collect::<Vec<_>>();
        frames.sort_by_key(|(id, _)| id.as_index());
        for (_, frame) in frames {
            self.i(I::LocalGet(frame.as_u32()));
            self.i(I::If(BlockType::Empty));
            self.i(I::LocalGet(frame.as_u32()));
            self.i(I::I32Load(MemArg {
                offset: SUSPENDED_STACK_END_OFFSET.into(),
                ..memarg(2)
            }));
            self.i(I::LocalSet(helpers.dynamic_base.as_u32()));
            self.raise_stack_floor(helpers.dynamic_base);
            self.i(I::End);
        }
        self.i(I::LocalGet(helpers.scratch.as_u32()));
        Ok(())
    }

    /// Raise the pending stack frontier in `scratch` to `floor` when necessary.
    fn raise_stack_floor(&mut self, floor: WasmLocalId) {
        let scratch = self.helper_locals().scratch;
        self.i(I::LocalGet(scratch.as_u32()));
        self.i(I::LocalGet(floor.as_u32()));
        self.i(I::LocalGet(scratch.as_u32()));
        self.i(I::LocalGet(floor.as_u32()));
        self.i(I::I32GtU);
        self.i(I::Select);
        self.i(I::LocalSet(scratch.as_u32()));
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
        let helpers = self.helper_locals();
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
                    helpers.dynamic_size
                } else {
                    helpers.dynamic_align
                })
                .as_u32(),
            ));
        }
        Ok(())
    }

    fn dynamic_alloca(&mut self) {
        let helpers = self.helper_locals();
        allocate_frame(
            &mut self.code,
            helpers.dynamic_size,
            helpers.dynamic_align,
            helpers.dynamic_base,
            helpers.allocation_end,
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
        self.call_inputs(inputs.iter().copied(), &abi.parameters[1..])?;
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

    fn call_inputs<'v>(
        &mut self,
        inputs: impl IntoIterator<Item = &'v Value>,
        transports: &[ParameterTransport],
    ) -> Result<(), String> {
        for (input, transport) in inputs.into_iter().zip(transports) {
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
        let pending = self.helper_locals().pending_failure;
        self.context_pointer(offset_of!(InvocationState, diagnostics));
        self.i(I::LocalGet(pending.as_u32()));
        self.i(I::Call(
            self.imports.function_index("capture_failure").as_u32(),
        ));
        self.i(I::LocalSet(pending.as_u32()));
    }

    fn propagate_failure(&mut self) {
        let pending = self.helper_locals().pending_failure;
        self.context_pointer(offset_of!(InvocationState, diagnostics));
        self.i(I::LocalGet(pending.as_u32()));
        self.i(I::Call(
            self.imports.function_index("propagate_failure").as_u32(),
        ));
        self.i(I::If(BlockType::Empty));
        self.fail(FailureCode::Source);
        self.i(I::End);
    }

    fn return_frame(&mut self, failed: bool, explicit_return: bool) -> Result<(), String> {
        if matches!(self.mode, BodyMode::ProjectionStart { .. }) && !failed {
            // Resume-only blocks share the same MIR body. They are encoded in the start entry but
            // cannot be reached before its Yield; trap if malformed control flow reaches one.
            self.fail(FailureCode::Invariant);
            return Ok(());
        }
        if failed && !self.signature.fallible {
            return Err("failure in an infallible entry".into());
        }
        for index in 0..self.owned_evidence.len() {
            self.release_evidence(&Value::Register(self.owned_evidence[index]))?;
        }
        if let Some(frame) = self.frame {
            if matches!(self.mode, BodyMode::ProjectionResume) {
                let floor = self
                    .resume_stack_floor
                    .expect("projection resume records its entry stack frontier");
                // Reclaim both the retained continuation and allocations made after resumption
                // when no caller-owned storage was already above the frame. The current stack
                // frontier cannot answer that question because the resumed half may have pushed
                // its own dynamic allocations. Otherwise retain the frame and caller storage but
                // still restore the resume-entry frontier to discard those later allocations.
                self.i(I::LocalGet(floor.as_u32()));
                self.i(I::LocalGet(frame.as_u32()));
                self.i(I::I32Load(MemArg {
                    offset: SUSPENDED_STACK_END_OFFSET.into(),
                    ..memarg(2)
                }));
                self.i(I::I32Eq);
                self.i(I::If(BlockType::Empty));
                leave_frame(&mut self.code, frame);
                self.i(I::Else);
                self.i(I::LocalGet(floor.as_u32()));
                self.i(I::GlobalSet(Global::Stack as u32));
                self.i(I::End);
            } else {
                leave_frame(&mut self.code, frame);
            }
        }
        if self.track_depth {
            let depth = self
                .runtime_globals
                .depth
                .expect("depth-tracked body has depth globals");
            self.i(I::GlobalGet(depth.depth));
            self.i(I::I32Const(1));
            self.i(I::I32Sub);
            self.i(I::GlobalSet(depth.depth));
        }
        if matches!(self.mode, BodyMode::ProjectionStart { .. }) {
            self.i(I::I32Const(1));
            self.i(I::I32Const(0));
            self.i(I::I32Const(0));
        } else if matches!(self.mode, BodyMode::ProjectionResume) || self.signature.fallible {
            self.i(I::I32Const(i32::from(failed)));
        } else if matches!(self.signature.result, ResultKind::Direct(_)) {
            if let Some(result) = self.forwarded_result.clone() {
                self.value(&result)?;
            } else {
                let result =
                    Value::Parameter(ParameterId::from_index(self.body.parameters().len() - 1));
                self.load_place(&result, self.pointee(&result)?)?;
            }
        }
        if explicit_return {
            self.i(I::Return);
        }
        Ok(())
    }

    fn initialize_literal(
        &mut self,
        destination: &Value,
        ty: Type,
        literal: &LiteralValue,
        offset: u32,
    ) -> Result<(), String> {
        if value_layout_for_type(ty, Location::new_synthesized(), &self.env)
            .map_err(|error| format!("constant layout: {error:?}"))?
            .size
            == 0
        {
            return Ok(());
        }
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

    fn pattern_address(&mut self, value: &Value, offset: u32) -> Result<(), String> {
        self.address(value)?;
        if offset != 0 {
            self.i(I::I32Const(offset as i32));
            self.i(I::I32Add);
        }
        Ok(())
    }

    fn pattern_equal_at(
        &mut self,
        value: &Value,
        offset: u32,
        ty: Type,
        literal: &LiteralValue,
    ) -> Result<(), String> {
        let data = ty.data().clone();
        if let TypeKind::Named(named) = data {
            let represented = self
                .env
                .type_def(named.def)
                .instantiated_shape_with_effects(&named.params, &named.effect_params);
            return self.pattern_equal_at(value, offset, represented, literal);
        }
        if let Some(expected) = literal.as_primitive_ty::<StaticStr>() {
            let index = self.strings.intern(*expected);
            self.pattern_address(value, offset)?;
            self.context_pointer(offset_of!(InvocationState, strings));
            self.i(I::I32Const((index * size_of::<StaticStr>()) as i32));
            self.i(I::I32Add);
            self.i(I::Call(
                self.imports.function_index("string_matches").as_u32(),
            ));
            return Ok(());
        }
        if let LiteralValue::Tuple(fields) = literal {
            let layout = product_layout_spec(ty, Location::new_synthesized(), &self.env)
                .ok_or("expected product pattern")?;
            if fields.len() != layout.members.len() {
                return Err("product pattern arity mismatch".into());
            }
            self.i(I::I32Const(1));
            for (index, field) in fields.iter().enumerate() {
                let field_offset = layout
                    .static_field_offset(ProjectionIndex::from_index(index))
                    .ok_or("open product pattern layout")?
                    as u32;
                self.pattern_equal_at(
                    value,
                    offset + field_offset,
                    layout.members[index].ty,
                    field,
                )?;
                self.i(I::I32And);
            }
            return Ok(());
        }
        // Variant tags are only whole-pattern discriminants. HIR lowers nested variant matching
        // structurally rather than embedding symbolic tags in product literals.

        // A pattern fixes the concrete scalar representation even when the scrutinee's static
        // type is an unresolved parameter constrained to that literal type.
        let scalar = literal
            .native_type()
            .map(ScalarType::of)
            .transpose()?
            .ok_or("expected scalar pattern")?;
        if scalar.is_unit() {
            self.i(I::I32Const(1));
        } else {
            self.pattern_address(value, offset)?;
            self.load(scalar);
            self.literal(literal)?;
            self.i(scalar.equal());
        }
        Ok(())
    }

    fn call_operation(&mut self, op: &Operation, invoked: bool) -> Result<(), String> {
        if matches!(op.kind, OperationKind::Project { .. }) {
            return self.project(op, invoked);
        }
        if matches!(op.kind, OperationKind::EndProject) {
            return self.end_project(&op.operands[0], invoked);
        }
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
            if let Value::Register(id) = callee
                && let Some(selected) = self.borrowed_subscripts.get(id).cloned()
            {
                return self.call_subscript_member(selected, &inputs, output, invoked);
            }
            if !matches!(callee, Value::Register(id) if self.selections.contains_key(id)) {
                return self.call_stored(callee, &inputs, output, invoked);
            }
            return self.call_dictionary(callee, &inputs, output, invoked);
        };
        if let Some(intrinsic) = wasm_intrinsic(self.session, op) {
            return self.call_intrinsic(intrinsic, &inputs, output, invoked);
        }
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
        self.call_inputs(inputs.iter().copied(), &abi.parameters)?;
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

    fn call_intrinsic(
        &mut self,
        intrinsic: KnownCallee,
        inputs: &[&Value],
        output: Option<&Value>,
        invoked: bool,
    ) -> Result<(), String> {
        let arity = match intrinsic {
            KnownCallee::IntAdd
            | KnownCallee::IntSub
            | KnownCallee::IntMul
            | KnownCallee::IntCmpCode
            | KnownCallee::FloatAdd
            | KnownCallee::FloatSub
            | KnownCallee::FloatMul
            | KnownCallee::FloatCmpCode => 2,
            KnownCallee::IntNeg
            | KnownCallee::IntFromInt
            | KnownCallee::FloatNeg
            | KnownCallee::BoolNot => 1,
            _ => unreachable!("wasm_intrinsic filters unsupported known callees"),
        };
        if inputs.len() != arity {
            return Err("wasm intrinsic argument count".into());
        }
        let output = output.ok_or("wasm intrinsic result storage")?;
        let ty = self.pointee(output)?;
        self.prepare_store(output)?;
        match intrinsic {
            KnownCallee::IntNeg => {
                self.i(I::I32Const(0));
                self.read(inputs[0])?;
                self.i(I::I32Sub);
            }
            KnownCallee::IntFromInt => {
                self.read(inputs[0])?;
            }
            KnownCallee::FloatNeg => {
                self.read(inputs[0])?;
                self.i(I::F64Neg);
            }
            KnownCallee::BoolNot => {
                self.read(inputs[0])?;
                self.i(I::I32Eqz);
            }
            KnownCallee::FloatAdd | KnownCallee::FloatSub | KnownCallee::FloatMul => {
                self.read(inputs[0])?;
                self.read(inputs[1])?;
                self.i(match intrinsic {
                    KnownCallee::FloatAdd => I::F64Add,
                    KnownCallee::FloatSub => I::F64Sub,
                    KnownCallee::FloatMul => I::F64Mul,
                    _ => unreachable!(),
                });
                // Ferlium floats are finite. Operations on finite operands cannot produce NaN,
                // but overflow can produce either infinity; clamp it exactly as
                // Float::new_saturating does in the native implementation.
                self.i(I::F64Const((-f64::MAX).into()));
                self.i(I::F64Max);
                self.i(I::F64Const(f64::MAX.into()));
                self.i(I::F64Min);
            }
            KnownCallee::IntAdd | KnownCallee::IntSub | KnownCallee::IntMul => {
                self.read(inputs[0])?;
                self.read(inputs[1])?;
                self.i(match intrinsic {
                    KnownCallee::IntAdd => I::I32Add,
                    KnownCallee::IntSub => I::I32Sub,
                    KnownCallee::IntMul => I::I32Mul,
                    _ => unreachable!(),
                });
            }
            KnownCallee::IntCmpCode | KnownCallee::FloatCmpCode => {
                // Preserve the comparison code when it escapes the usual predicate idiom. Wasm
                // comparisons yield 0 or 1, so `(left > right) - (left < right)` is exactly the
                // native -1/0/1 convention. The common single-predicate use is fused earlier and
                // does not materialize this code at all.
                self.read(inputs[0])?;
                self.read(inputs[1])?;
                self.i(match intrinsic {
                    KnownCallee::IntCmpCode => I::I32GtS,
                    KnownCallee::FloatCmpCode => I::F64Gt,
                    _ => unreachable!(),
                });
                self.read(inputs[0])?;
                self.read(inputs[1])?;
                self.i(match intrinsic {
                    KnownCallee::IntCmpCode => I::I32LtS,
                    KnownCallee::FloatCmpCode => I::F64Lt,
                    _ => unreachable!(),
                });
                self.i(I::I32Sub);
            }
            _ => unreachable!("wasm_intrinsic filters unsupported known callees"),
        }
        self.finish_store(output, ty);
        self.call_status(invoked, false);
        Ok(())
    }

    fn local(&mut self, ty: ValType) -> WasmLocalId {
        let id = WasmLocalId::from_index(
            self.signature.parameter_count() + self.mode.extra_parameters() + self.locals.len(),
        );
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
                let intrinsic = wasm_intrinsic(self.session, op);
                let call_abi = if intrinsic.is_none()
                    && matches!(op.kind, OperationKind::Call { .. })
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
                            if intrinsic.is_some() {
                                false
                            } else if index + 1 == op.operands.len()
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
            Value::Register(id) => {
                let local = self
                    .registers
                    .get(id)
                    .copied()
                    .ok_or_else(|| format!("register {id:?} has no Wasm value"))?;
                self.i(I::LocalGet(local.as_u32()));
            }
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

    pub(super) fn emit(mut self) -> Result<EmittedBody, String> {
        if let Some(frame) = self.frame
            && !matches!(self.mode, BodyMode::ProjectionResume)
        {
            enter_frame(&mut self.code, frame, self.frame_size);
        }
        if !matches!(self.mode, BodyMode::ProjectionResume) {
            if self.track_depth {
                let depth = self
                    .runtime_globals
                    .depth
                    .expect("depth-tracked body has depth globals");
                self.i(I::GlobalGet(depth.depth));
                self.i(I::I32Const(1));
                self.i(I::I32Add);
                self.i(I::GlobalSet(depth.depth));
            }
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
            if matches!(self.mode, BodyMode::ProjectionStart { .. }) {
                self.initialize_suspension();
            }
        } else {
            self.i(I::GlobalGet(Global::Stack as u32));
            self.i(I::LocalSet(
                self.resume_stack_floor
                    .expect("resumed projection has a stack floor")
                    .as_u32(),
            ));
            self.restore_suspension();
        }
        let control_flow = self
            .control_flow
            .take()
            .expect("Wasm body control flow is emitted once");
        match control_flow {
            ControlFlow::Dispatcher => {
                let pc = self.pc.expect("dispatched body has a program counter");
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
                    let next = next_block(self.body, block_id);
                    self.emit_block(
                        block_id,
                        BranchContext::Dispatcher {
                            depth: count - block_id.as_u32(),
                        },
                        next,
                    )?;
                }
                self.i(I::End);
                self.fail(FailureCode::Invariant);
                self.i(I::End);
            }
            ControlFlow::Structured(regions) => {
                for (index, region) in regions.iter().enumerate() {
                    match region {
                        ControlRegion::Loop(region) => {
                            // The outer block is `break`; the inner loop is `continue`.
                            self.i(I::Block(BlockType::Empty));
                            self.i(I::Loop(BlockType::Empty));
                            for (block_index, &block_id) in region.blocks.iter().enumerate() {
                                let next = Some(
                                    region
                                        .blocks
                                        .get(block_index + 1)
                                        .copied()
                                        .unwrap_or(region.exit),
                                );
                                self.emit_block(
                                    block_id,
                                    BranchContext::Loop {
                                        header: region.header,
                                        exit: region.exit,
                                    },
                                    next,
                                )?;
                            }
                            self.i(I::End);
                            self.i(I::End);
                        }
                        ControlRegion::Block(block_id) => {
                            let next = regions.get(index + 1).map(ControlRegion::entry);
                            self.emit_block(*block_id, BranchContext::Linear, next)?;
                        }
                    }
                }
            }
        }
        if !self.fallthrough_return {
            self.i(I::Unreachable);
        }
        self.i(I::End);
        Ok(EmittedBody {
            function: self.code,
            source_map: self.source_map,
            suspension: self.suspension,
        })
    }

    fn emit_block(
        &mut self,
        block_id: BlockId,
        context: BranchContext,
        next: Option<BlockId>,
    ) -> Result<(), String> {
        let block = self.body.block(block_id);
        let operations = block.operations();
        let operation_count = operations.len();
        let mut index = 0;
        while index < operations.len() {
            let operation = &operations[index];
            if self.forwarded_result.is_some()
                && block_id == self.body.entry()
                && index + 1 == operation_count
            {
                index += 1;
                continue;
            }
            if let Some(test) = operations.get(index + 1)
                && let Some(&intrinsic) = test
                    .result_id()
                    .and_then(|result| self.comparison_fusions.get(&result))
            {
                let start = self.code.byte_len();
                self.comparison_predicate(intrinsic, operation, test)?;
                self.finish_operation_result(test)?;
                self.record_source(start, operation.span);
                index += 2;
                continue;
            }
            let start = self.code.byte_len();
            self.operation(operation).map_err(|e| {
                format!(
                    "{} in block {}: {e}",
                    OperationKindDiscriminant::from(&operation.kind),
                    block_id.as_u32()
                )
            })?;
            self.record_source(start, operation.span);
            index += 1;
        }
        let start = self.code.byte_len();
        let span = match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => operation.span,
            _ => block.terminator().span,
        };
        match &block.terminator().kind {
            TerminatorKind::Goto { target } => {
                self.branch(*target, context, next, 0);
            }
            TerminatorKind::CondBr {
                condition,
                then_target,
                else_target,
            } => {
                if then_target == else_target {
                    self.branch(*then_target, context, next, 0);
                } else if Some(*then_target) == next {
                    self.read(condition)?;
                    self.i(I::I32Eqz);
                    self.branch_if(*else_target, context, 0);
                } else if Some(*else_target) == next {
                    self.read(condition)?;
                    self.branch_if(*then_target, context, 0);
                } else {
                    if !matches!(context, BranchContext::Dispatcher { .. }) {
                        unreachable!("structured conditional must have a fallthrough target");
                    }
                    self.i(I::I32Const(then_target.as_u32() as i32));
                    self.i(I::I32Const(else_target.as_u32() as i32));
                    self.read(condition)?;
                    self.i(I::Select);
                    self.dispatch(context, 0);
                }
            }
            TerminatorKind::SwitchVariant {
                tag,
                cases,
                default,
            } => {
                if Some(*default) == next {
                    for (case, target) in cases {
                        if Some(*target) == next {
                            continue;
                        }
                        self.value(tag)?;
                        self.i(I::I32Const(self.session.variant_tag_id(*case) as i32));
                        self.i(I::I32Eq);
                        self.branch_if(*target, context, 0);
                    }
                } else {
                    self.i(I::I32Const(default.as_u32() as i32));
                    for (case, target) in cases {
                        self.i(I::I32Const(target.as_u32() as i32));
                        self.value(tag)?;
                        self.i(I::I32Const(self.session.variant_tag_id(*case) as i32));
                        self.i(I::I32Ne);
                        self.i(I::Select);
                    }
                    self.dispatch(context, 0);
                }
            }
            TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } => {
                self.call_operation(operation, true)?;
                if normal == error {
                    self.i(I::If(BlockType::Empty));
                    self.capture_failure();
                    self.i(I::End);
                    self.branch(*normal, context, next, 0);
                } else if Some(*normal) == next {
                    self.i(I::If(BlockType::Empty));
                    self.capture_failure();
                    self.branch(*error, context, None, 1);
                    self.i(I::End);
                } else if Some(*error) == next {
                    self.i(I::If(BlockType::Empty));
                    self.capture_failure();
                    self.i(I::Else);
                    self.branch(*normal, context, None, 1);
                    self.i(I::End);
                } else {
                    self.i(I::If(BlockType::Result(ValType::I32)));
                    self.capture_failure();
                    self.i(I::I32Const(error.as_u32() as i32));
                    self.i(I::Else);
                    self.i(I::I32Const(normal.as_u32() as i32));
                    self.i(I::End);
                    self.dispatch(context, 0);
                }
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
                    self.return_frame(true, true)?;
                }
            }
            TerminatorKind::Return => {
                self.return_frame(false, !self.fallthrough_return)?;
            }
            TerminatorKind::Yield { place, resume } => self.suspend(place, *resume)?,
            TerminatorKind::InvariantFailure { .. } => self.fail(FailureCode::Invariant),
        }
        self.record_source(start, span);
        Ok(())
    }

    fn record_source(&mut self, start: usize, span: Location) {
        let end = self.code.byte_len();
        if start < end && !span.is_synthesized() {
            self.source_map.push((start..end, span));
        }
    }

    fn dispatch(&mut self, context: BranchContext, nested: u32) {
        let BranchContext::Dispatcher { depth } = context else {
            unreachable!("structured control flow cannot require dispatch")
        };
        self.i(I::LocalSet(
            self.pc.expect("branch needs a dispatcher").as_u32(),
        ));
        self.i(I::Br(depth.checked_add(nested).expect("Wasm branch depth")));
    }

    fn branch(
        &mut self,
        target: BlockId,
        context: BranchContext,
        next: Option<BlockId>,
        nested: u32,
    ) {
        if Some(target) == next {
            return;
        }
        match context {
            BranchContext::Loop { header, .. } if target == header => {
                self.i(I::Br(nested));
            }
            BranchContext::Loop { exit, .. } if target == exit => {
                self.i(I::Br(1 + nested));
            }
            BranchContext::Dispatcher { .. } => {
                self.i(I::I32Const(target.as_u32() as i32));
                self.dispatch(context, nested);
            }
            BranchContext::Linear | BranchContext::Loop { .. } => {
                unreachable!("unstructured edge reached structured Wasm emission")
            }
        }
    }

    /// Branch conditionally to a MIR block; expects its condition on the operand stack.
    fn branch_if(&mut self, target: BlockId, context: BranchContext, nested: u32) {
        match context {
            BranchContext::Loop { header, .. } if target == header => {
                self.i(I::BrIf(nested));
            }
            BranchContext::Loop { exit, .. } if target == exit => {
                self.i(I::BrIf(1 + nested));
            }
            BranchContext::Dispatcher { depth } => {
                self.i(I::I32Const(target.as_u32() as i32));
                self.i(I::LocalSet(
                    self.pc.expect("branch needs a dispatcher").as_u32(),
                ));
                self.i(I::BrIf(
                    depth.checked_add(nested).expect("Wasm branch depth"),
                ));
            }
            BranchContext::Linear | BranchContext::Loop { .. } => {
                unreachable!("unstructured edge reached structured Wasm emission")
            }
        }
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
            CloneSubscriptEnv { .. } => {
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
            DropClosureEnv | DropSubscriptEnv => {
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
            BuildSubscriptEvidence { .. } => {
                let id = op.result_id().unwrap();
                let result = Value::Register(id);
                let constructed = *self
                    .constructed_subscripts
                    .get(&id)
                    .ok_or("dynamic subscript evidence base")?;
                let definition = self
                    .program
                    .subscript(constructed.definition)
                    .ok_or("missing subscript definition")?;
                let fields = &definition.environment().fields;
                let appended = args.len() - 1;
                let inherited = constructed
                    .capture_count
                    .checked_sub(appended)
                    .ok_or("subscript capture count")?;
                if inherited > fields.len() {
                    return Err("subscript base capture count".into());
                }
                self.release_evidence(&result)?;
                let capture_offset = self.capture_slots[&id];
                for field in &fields[..inherited] {
                    self.frame_address(capture_offset + field.offset as u32);
                    self.value(&args[0])?;
                    self.i(I::I32Load(MemArg {
                        offset: ENVIRONMENT_OFFSET,
                        ..memarg(2)
                    }));
                    self.i(I::I32Const(field.offset as i32));
                    self.i(I::I32Add);
                    if field.is_storage_flag {
                        self.i(I::I32Load8U(memarg(0)));
                        self.i(I::I32Store8(memarg(0)));
                    } else {
                        self.i(I::I32Const(size_of::<DictionaryReference>() as i32));
                        self.i(I::MemoryCopy {
                            src_mem: 0,
                            dst_mem: 0,
                        });
                    }
                }
                for (field, argument) in fields[inherited..].iter().zip(&args[1..]) {
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
                    self.program
                        .reference_index(Descriptor::Subscript(constructed.definition))
                        .unwrap()
                        .as_u32() as i32,
                ));
                self.frame_address(capture_offset);
                self.address(&result)?;
                self.i(I::Call(
                    self.imports.function_index("build_evidence").as_u32(),
                ));
                return Ok(());
            }
            BuildSubscript { .. } => {
                let result = Value::Register(op.result_id().unwrap());
                self.address(&result)?;
                self.value(&args[0])?;
                self.i(I::I32Load(memarg(2)));
                self.i(I::I32Store(memarg(2)));
                self.address(&result)?;
                self.context_pointer(offset_of!(InvocationState, evidence));
                self.value(&args[0])?;
                self.i(I::Call(
                    self.imports
                        .function_index("materialize_subscript_environment")
                        .as_u32(),
                ));
                self.i(I::I32Store(MemArg {
                    offset: ENVIRONMENT_OFFSET,
                    ..memarg(2)
                }));
                return Ok(());
            }
            BorrowSubscriptMember { .. } => return Ok(()),
            Project { .. } => return self.project(op, false),
            EndProject => return self.end_project(&args[0], false),
            BuildArray { element_ty } => {
                let helpers = self.helper_locals();
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
                self.i(I::LocalSet(helpers.scratch.as_u32()));
                for (index, value) in elements.iter().enumerate() {
                    self.i(I::LocalGet(helpers.scratch.as_u32()));
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
                        self.i(I::LocalGet(helpers.scratch.as_u32()));
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
                if matches!(&args[0], Value::Register(id) if self.callable_values.contains(id) || self.subscript_values.contains(id))
                {
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
                        self.i(I::LocalGet(self.helper_locals().dynamic_size.as_u32()));
                    } else {
                        self.i(I::I32Const(self.size(&ty)? as i32));
                    }
                    self.i(I::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });
                }
            }
            BlackBox { ty } => {
                if let Some(witness) = layout_witness(op) {
                    self.dynamic_layout(witness)?;
                }
                self.address(&args[0])?;
                if layout_witness(op).is_some() {
                    self.i(I::LocalGet(self.helper_locals().dynamic_size.as_u32()));
                } else {
                    self.i(I::I32Const(self.size(&MirType::Lowered(*ty))? as i32));
                }
                self.i(I::Call(self.imports.function_index("black_box").as_u32()));
            }
            Replace => {
                let helpers = self.helper_locals();
                let MirType::Lowered(ty) = self.pointee_type(&args[0])? else {
                    return Err("pointer replacement".into());
                };
                if let Some(witness) = layout_witness(op) {
                    self.dynamic_layout(witness)?;
                    self.i(I::GlobalGet(Global::Stack as u32));
                    self.i(I::LocalSet(helpers.scratch.as_u32()));
                    self.dynamic_alloca();
                    self.i(I::Drop);
                } else {
                    self.scratch_address(ty);
                    self.i(I::LocalSet(helpers.dynamic_base.as_u32()));
                    self.i(I::I32Const(self.size(&MirType::Lowered(ty))? as i32));
                    self.i(I::LocalSet(helpers.dynamic_size.as_u32()));
                }
                self.i(I::LocalGet(helpers.dynamic_base.as_u32()));
                self.address(&args[0])?;
                self.i(I::LocalGet(helpers.dynamic_size.as_u32()));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&args[0])?;
                self.address(&args[1])?;
                self.i(I::LocalGet(helpers.dynamic_size.as_u32()));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&args[1])?;
                self.i(I::LocalGet(helpers.dynamic_base.as_u32()));
                self.i(I::LocalGet(helpers.dynamic_size.as_u32()));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                if layout_witness(op).is_some() {
                    self.i(I::LocalGet(helpers.scratch.as_u32()));
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
                self.restore_stack(&args[0])?;
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
                let Value::Pattern(pattern) = &args[1] else {
                    return Err("compare_equal requires a pattern".into());
                };
                if matches!(&**pattern, LiteralValue::VariantTag(_)) {
                    let ty = self.read(&args[0])?;
                    self.value(&args[1])?;
                    self.i(ty.equal());
                } else if let Some(MirType::Lowered(ty)) = self
                    .roles
                    .get(&args[0], self.body.constants())
                    .and_then(|role| role.place_pointee_type())
                {
                    if ScalarType::of(ty).is_ok() {
                        let ty = self.read(&args[0])?;
                        self.value(&args[1])?;
                        self.i(ty.equal());
                    } else {
                        self.pattern_equal_at(&args[0], 0, ty, pattern)?;
                    }
                } else {
                    let ty = self.read(&args[0])?;
                    self.value(&args[1])?;
                    self.i(ty.equal());
                }
            }
            CheckCallDepth => {
                let depth = self
                    .runtime_globals
                    .depth
                    .expect("call-depth check has depth globals");
                self.i(I::GlobalGet(depth.depth));
                self.i(I::GlobalGet(depth.limit));
                self.i(I::I32GeU);
                self.i(I::If(BlockType::Empty));
                self.fail(FailureCode::CallDepth);
                self.i(I::End);
            }
            CheckFuel => {
                let fuel = self
                    .runtime_globals
                    .fuel
                    .expect("fuel check has fuel globals");
                self.i(I::GlobalGet(fuel.enabled));
                self.i(I::If(BlockType::Empty));
                self.i(I::GlobalGet(fuel.fuel));
                self.i(I::I32Eqz);
                self.i(I::If(BlockType::Empty));
                self.fail(FailureCode::Fuel);
                self.i(I::End);
                self.i(I::GlobalGet(fuel.fuel));
                self.i(I::I32Const(1));
                self.i(I::I32Sub);
                self.i(I::GlobalSet(fuel.fuel));
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
        self.finish_operation_result(op)
    }

    fn finish_operation_result(&mut self, op: &Operation) -> Result<(), String> {
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

    fn comparison_predicate(
        &mut self,
        intrinsic: KnownCallee,
        call: &Operation,
        test: &Operation,
    ) -> Result<(), String> {
        let [_, left, right, _] = &*call.operands else {
            return Err("comparison-code call operands".into());
        };
        let Value::Pattern(pattern) = &test.operands[1] else {
            return Err("comparison-code pattern".into());
        };
        let code = *pattern
            .as_primitive_ty::<isize>()
            .ok_or("comparison-code integer pattern")?;
        self.read(left)?;
        self.read(right)?;
        self.i(match (intrinsic, code) {
            (KnownCallee::IntCmpCode, -1) => I::I32LtS,
            (KnownCallee::IntCmpCode, 0) => I::I32Eq,
            (KnownCallee::IntCmpCode, 1) => I::I32GtS,
            (KnownCallee::FloatCmpCode, -1) => I::F64Lt,
            (KnownCallee::FloatCmpCode, 0) => I::F64Eq,
            (KnownCallee::FloatCmpCode, 1) => I::F64Gt,
            _ => return Err("comparison-code pattern outside -1/0/1".into()),
        });
        Ok(())
    }
}

/// Adjacent comparison-code calls whose only result observation is an equality test can select a
/// target predicate directly. Requiring adjacency keeps the original input values live without
/// needing alias analysis. Requiring a fresh result allocation, observed only by the call output
/// and test input, lets emission omit the intermediate code without leaving aliased storage stale.
fn comparison_fusions(
    body: &Function,
    session: &CompilerSession,
) -> FxHashMap<ValueId, KnownCallee> {
    let mut uses = FxHashMap::<ValueId, usize>::default();
    let mut definitions = FxHashMap::<ValueId, &Operation>::default();
    for block in body.blocks() {
        let block = body.block(block);
        for operation in block.operations() {
            if let Some(result) = operation.result_id() {
                definitions.insert(result, operation);
            }
            for operand in &operation.operands {
                if let Value::Register(id) = operand {
                    *uses.entry(*id).or_default() += 1;
                }
            }
        }
        for operand in block.terminator().operands() {
            if let Value::Register(id) = operand {
                *uses.entry(*id).or_default() += 1;
            }
        }
    }

    let mut fused = FxHashMap::default();
    for block in body.blocks() {
        for pair in body.block(block).operations().windows(2) {
            let [call, test] = pair else { unreachable!() };
            let Some(intrinsic @ (KnownCallee::IntCmpCode | KnownCallee::FloatCmpCode)) =
                wasm_intrinsic(session, call)
            else {
                continue;
            };
            let OperationKind::Call { ty, .. } = &call.kind else {
                continue;
            };
            if !ty.result_convention.has_result_place()
                || !matches!(test.kind, OperationKind::CompareEqual)
                || call.operands.len() != 4
                || test.operands.len() != 2
            {
                continue;
            }
            let output = &call.operands[3];
            let Value::Register(output_id) = output else {
                continue;
            };
            let Value::Pattern(pattern) = &test.operands[1] else {
                continue;
            };
            if test.operands[0] != *output
                || uses.get(output_id).copied() != Some(2)
                || !definitions.get(output_id).is_some_and(|definition| {
                    matches!(definition.kind, OperationKind::Alloca { .. })
                })
                || !matches!(pattern.as_primitive_ty::<isize>(), Some(-1..=1))
            {
                continue;
            }
            if let Some(result) = test.result_id() {
                fused.insert(result, intrinsic);
            }
        }
    }
    fused
}

fn needs_helper_locals(body: &Function, mode: BodyMode) -> bool {
    mode.projection()
        || body.blocks().any(|block| {
            let block = body.block(block);
            matches!(
                block.terminator().kind,
                TerminatorKind::Invoke { .. }
                    | TerminatorKind::PropagateError
                    | TerminatorKind::FailureDuringCleanup
            ) || operations(block).any(operation_needs_helper_locals)
        })
}

pub(super) fn operation_needs_helper_locals(operation: &Operation) -> bool {
    layout_witness(operation).is_some()
        || !matches!(
            operation.kind,
            OperationKind::Alloca { .. }
                | OperationKind::AllocaPlace { .. }
                | OperationKind::Load
                | OperationKind::Store
                | OperationKind::CompareEqual
                | OperationKind::ExtractTag
                | OperationKind::ExtractPayloadIndirection
                | OperationKind::IsInitialized
                | OperationKind::AddressOffset { .. }
                | OperationKind::AddressOffsetPlace { .. }
                | OperationKind::Clear
                | OperationKind::StackSave
                | OperationKind::CheckCallDepth
                | OperationKind::CheckFuel
                | OperationKind::RuntimeAlloc { .. }
                | OperationKind::RuntimeDealloc
        )
}

fn next_block(body: &Function, block: BlockId) -> Option<BlockId> {
    (block.as_index() + 1 < body.blocks().count())
        .then(|| BlockId::from_index(block.as_index() + 1))
}

fn has_fallthrough_return(body: &Function, mode: BodyMode, control_flow: &ControlFlow) -> bool {
    let ControlFlow::Structured(regions) = control_flow else {
        return false;
    };
    matches!(mode, BodyMode::Normal)
        && matches!(regions.last(), Some(ControlRegion::Block(block))
            if matches!(body.block(*block).terminator().kind, TerminatorKind::Return))
}

fn forwarded_result(body: &Function, signature: &CallAbi, mode: BodyMode) -> Option<Value> {
    if !matches!(mode, BodyMode::Normal)
        || body.blocks().count() != 1
        || signature.fallible
        || !matches!(signature.result, ResultKind::Direct(_))
        || !matches!(
            body.block(body.entry()).terminator().kind,
            TerminatorKind::Return
        )
    {
        return None;
    }
    let block = body.block(body.entry());
    let return_id = body
        .parameters()
        .iter()
        .position(|parameter| parameter.kind == ParameterKind::Return)?;
    let destination = Value::Parameter(ParameterId::from_index(return_id));
    let (last, prefix) = block.operations().split_last()?;
    if !matches!(last.kind, OperationKind::Store)
        || last.operands.get(1) != Some(&destination)
        || prefix
            .iter()
            .any(|operation| operation.operands.contains(&destination))
    {
        return None;
    }
    Some(last.operands[0].clone())
}
