// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Per-function storage assignment and instruction emission.

use std::{cell::RefCell, mem::offset_of, ops::Range};

use self::HelperLocal::{
    AllocationEnd, CopyDestination, CopySource, DynamicAlign, DynamicBase, DynamicSize,
    PendingFailure, Scratch,
};

use wasm_encoder::{BlockType, Function as WasmFunction, Instruction as I, MemArg, ValType};

use ustr::{Ustr, ustr};

use crate::{
    CompilerSession, FxHashMap, FxHashSet, Location,
    hir::{
        native_functions::{NativeResult, NativeScalar},
        value::{LiteralValue, VariantPayloadStorage},
    },
    mir::{
        BlockId, DebugLocation, Function, Operation, OperationKind, ParameterId, ParameterKind,
        Value, ValueId,
        operation::OperationKindDiscriminant,
        pass::{known_callee::KnownCallee, stack_region::no_op_stack_markers},
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
        STD_MODULE_ID,
        logic::bool_type,
        math::{Float, RawFloat},
        string::{
            STRING_FROM_STATIC_FUNCTION_NAME, STRING_PUSH_STATIC_STR_FUNCTION_NAME, StaticStr,
            static_str_type,
        },
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
    control_flow::{ControlFlow, Item, conditional_targets, distinct_targets},
    dictionary_table, emit_failure, emit_small_copy, enter_frame,
    expressions::{
        Analysis as ExpressionAnalysis, Plan as ExpressionPlan, Source as ExpressionSource,
    },
    frame_address, frame_bytes, is_elided_stack_operation, layout_witness, leave_frame, memarg,
    memarg_at, operations,
    peephole::{Code, Spans},
    scalar, stack, subscript,
    suspension::Crossing,
};

// The backend currently assumes the compiler and generated Wasm share a wasm32 runtime layout.
const _: () = assert!(size_of::<StaticStr>() == 4);

/// Code ranges generated for MIR operations and terminators, with their source spans. Ranges are
/// ordered, and either disjoint or identical: code doing the work of several operations has one
/// entry per span.
pub(super) type BodySourceMap = Vec<(Range<usize>, DebugLocation)>;

#[derive(Clone, Copy)]
enum Storage {
    Local(WasmLocalId),
    /// Byte offset from the function's frame base in linear memory.
    Stack(u32),
    /// A single-assignment scalar place whose value is emitted at its only read.
    Expression,
}

/// An enclosing Wasm construct of structured emission.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Label {
    /// A `block` whose end leads to the given MIR block.
    Block(BlockId),
    /// A `loop` whose start is the given MIR block.
    Loop(BlockId),
    /// An `if` entering one arm of a terminator.
    If,
}

fn wasm_value_size(ty: ValType) -> u32 {
    match ty {
        ValType::I32 | ValType::F32 => 4,
        ValType::I64 | ValType::F64 => 8,
        _ => unreachable!("the Wasm32 backend emits only numeric locals"),
    }
}

fn local_load(ty: ValType, offset: u32) -> I<'static> {
    match ty {
        ValType::I32 => I::I32Load(memarg_at(2, offset)),
        ValType::I64 => I::I64Load(memarg_at(3, offset)),
        ValType::F32 => I::F32Load(memarg_at(2, offset)),
        ValType::F64 => I::F64Load(memarg_at(3, offset)),
        _ => unreachable!("the Wasm32 backend emits only numeric locals"),
    }
}

fn local_store(ty: ValType, offset: u32) -> I<'static> {
    match ty {
        ValType::I32 => I::I32Store(memarg_at(2, offset)),
        ValType::I64 => I::I64Store(memarg_at(3, offset)),
        ValType::F32 => I::F32Store(memarg_at(2, offset)),
        ValType::F64 => I::F64Store(memarg_at(3, offset)),
        _ => unreachable!("the Wasm32 backend emits only numeric locals"),
    }
}

#[derive(Clone, Copy)]
struct LayoutLocals {
    dictionary: WasmLocalId,
    table: WasmLocalId,
    output: WasmLocalId,
}

/// Scratch locals are assigned before emission and never retained across a yield.
#[derive(Clone, Copy, Debug)]
pub(super) enum HelperLocal {
    PendingFailure,
    Scratch,
    DynamicSize,
    DynamicAlign,
    DynamicBase,
    AllocationEnd,
    CopySource,
    CopyDestination,
}

impl HelperLocal {
    // Discriminants index storage; this lists every helper once. Order only sets allocation order.
    const ALL: [Self; 8] = [
        Self::PendingFailure,
        Self::Scratch,
        Self::DynamicSize,
        Self::DynamicAlign,
        Self::DynamicBase,
        Self::AllocationEnd,
        Self::CopySource,
        Self::CopyDestination,
    ];

    fn ty(self) -> ValType {
        match self {
            Self::AllocationEnd => ValType::I64,
            _ => ValType::I32,
        }
    }
}

#[derive(Clone, Copy, Default)]
pub(super) struct HelperLocals([Option<WasmLocalId>; HelperLocal::ALL.len()]);

impl HelperLocals {
    pub(super) fn get(self, helper: HelperLocal) -> WasmLocalId {
        self.0[helper as usize].unwrap_or_else(|| panic!("unreserved helper local: {helper:?}"))
    }
}

const RESUME_SLOT_OFFSET: u32 = 0;
const SUSPENDED_STACK_END_OFFSET: u32 = 4;
const CONTINUATION_HEADER_SIZE: u32 = 8;
/// A resume body receives the failure destination and its retained frame, and restores the
/// parameters it reads from that frame into the locals that follow.
const RESUME_PARAMETER_COUNT: usize = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BodyMode {
    Normal,
    ProjectionStart { resume: DispatchTableSlotId },
    ProjectionResume,
}

impl BodyMode {
    /// The Wasm index of the first local after the parameters.
    fn local_base(self, signature: &CallAbi) -> usize {
        match self {
            Self::ProjectionResume => RESUME_PARAMETER_COUNT,
            _ => signature.parameter_count(),
        }
    }

    fn projection(self) -> bool {
        !matches!(self, Self::Normal)
    }
}

fn returns_direct_result(mode: BodyMode, signature: &CallAbi) -> bool {
    matches!(mode, BodyMode::Normal)
        && !signature.fallible
        && matches!(signature.result, ResultKind::Direct(_))
}

/// The locals that a suspended accessor retains for its resumed half: the parameters and the
/// registers that the resumed half reads. Each one has a slot in the frame, at a byte offset from
/// the frame base.
#[derive(Clone, Debug, PartialEq, Eq)]
struct SuspensionLayout {
    /// The local holding each value, in this body's numbering, with its slot offset and type.
    locals: Vec<(WasmLocalId, u32, ValType)>,
}

pub(super) struct EmittedBody {
    pub function: WasmFunction,
    pub source_map: BodySourceMap,
}

pub(super) struct Body<'a, 's> {
    pub(super) body: &'a Function,
    signature: &'a CallAbi,
    pub(super) roles: ValueRoles,
    pub(super) env: ModuleEnv<'a>,
    /// Validated sizes shared by bodies in this module's fixed type environment.
    type_sizes: &'s RefCell<FxHashMap<Type, u32>>,
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
    /// Shells with a constant tag word whose only use stores them: the store writes the word
    /// directly, so the shell needs no slot.
    stored_variants: FxHashMap<ValueId, i32>,
    layout_slot: Option<u32>,
    helpers: HelperLocals,
    evidence_base: Option<WasmLocalId>,
    layout_locals: Option<LayoutLocals>,
    scratch_slots: FxHashMap<Type, u32>,
    callees: &'a FxHashMap<FunctionId, (WasmFunctionId, &'a CallAbi)>,
    /// The resume body of each projection whose accessor is known.
    direct_resumes: FxHashMap<ValueId, WasmFunctionId>,
    program: &'a ResolvedPhysicalProgram<'a>,
    session: &'a CompilerSession,
    registers: FxHashMap<ValueId, WasmLocalId>,
    storage: FxHashMap<Value, Storage>,
    borrowed_static_strings: FxHashMap<Value, usize>,
    locals: Vec<ValType>,
    mode: BodyMode,
    /// The block where execution starts: the resume block for a resume body.
    entry: BlockId,
    suspension: Option<SuspensionLayout>,
    /// Stack frontier on entry to a resumed accessor, which completion compares with the frontier
    /// at suspension to tell whether its caller allocated above the continuation.
    resume_frontier: Option<WasmLocalId>,
    frame: Option<WasmLocalId>,
    pc: Option<WasmLocalId>,
    control_flow: Option<ControlFlow>,
    /// Enclosing constructs of structured emission, innermost last.
    labels: Vec<Label>,
    frame_size: u32,
    runtime_globals: RuntimeGlobals,
    track_depth: bool,
    forwarded_result: Option<Value>,
    /// The block whose return falls through the end of the function, if any.
    fallthrough_return: Option<BlockId>,
    analysis: ExpressionAnalysis,
    expressions: ExpressionPlan,
    no_op_stack_markers: FxHashSet<ValueId>,
    /// The blocks emitted so far, indexed by block.
    emitted: Vec<bool>,
    /// `raw_float_to_float` calls only reachable once their operand has been checked finite.
    checked_float_conversions: FxHashSet<ExpressionSource>,
    /// The local an unchecked `raw_float_to_float` holds its operand in, for its fallback.
    float_conversion_local: Option<WasmLocalId>,
    pub(super) code: Code,
    /// Whether to map the code back to its source.
    source_map: bool,
    /// The spans of the code emitted before each open source region, innermost last.
    sources: Vec<Spans>,
}

impl<'a, 's> Body<'a, 's> {
    pub(super) fn helper_locals(&self) -> HelperLocals {
        self.helpers
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        body: &'a Function,
        signature: &'a CallAbi,
        callees: &'a FxHashMap<FunctionId, (WasmFunctionId, &'a CallAbi)>,
        resumes: &'a FxHashMap<FunctionId, WasmFunctionId>,
        program: &'a ResolvedPhysicalProgram<'a>,
        session: &'a CompilerSession,
        env: ModuleEnv<'a>,
        type_sizes: &'s RefCell<FxHashMap<Type, u32>>,
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
        source_map: bool,
    ) -> Result<Self, String> {
        stack::check_nesting(body)?;
        let constructed_subscripts = constructed_subscript_definitions(body);
        let crossing = mode.projection().then(|| Crossing::of(body)).transpose()?;
        let entry = match mode {
            BodyMode::ProjectionResume => crossing
                .as_ref()
                .and_then(|crossing| crossing.resume)
                .ok_or("resumed accessor without a yield")?,
            _ => body.entry(),
        };
        let control_flow = ControlFlow::of(body, entry);
        let dispatched = matches!(control_flow, ControlFlow::Dispatcher);
        let forwarded_result = forwarded_result(body, signature, mode);
        let fallthrough_return = has_fallthrough_return(body, mode, &control_flow);
        let roles = ValueRoles::derive(body);
        let no_op_stack_markers = no_op_stack_markers(
            body,
            operation_changes_stack_frontier,
            terminator_changes_stack_frontier,
        );
        let (analysis, expressions) = ExpressionAnalysis::of(
            body,
            &roles,
            callees,
            program,
            session,
            env,
            returns_direct_result(mode, signature) && forwarded_result.is_none(),
            &no_op_stack_markers,
        );
        let mut this = Self {
            body,
            signature,
            env,
            type_sizes,
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
            stored_variants: FxHashMap::default(),
            layout_slot: None,
            helpers: HelperLocals::default(),
            evidence_base: None,
            layout_locals: None,
            scratch_slots: FxHashMap::default(),
            callees,
            direct_resumes: FxHashMap::default(),
            program,
            session,
            roles,
            registers: FxHashMap::default(),
            storage: FxHashMap::default(),
            borrowed_static_strings: FxHashMap::default(),
            locals: Vec::new(),
            mode,
            entry,
            suspension: None,
            resume_frontier: None,
            frame: None,
            pc: None,
            control_flow: Some(control_flow),
            labels: Vec::new(),
            frame_size: if mode.projection() {
                CONTINUATION_HEADER_SIZE
            } else {
                0
            },
            runtime_globals,
            track_depth,
            forwarded_result,
            fallthrough_return,
            checked_float_conversions: checked_float_conversions(body, &analysis),
            float_conversion_local: None,
            analysis,
            expressions,
            no_op_stack_markers,
            emitted: vec![false; body.blocks().count()],
            code: Code::new(WasmFunction::new([])),
            source_map,
            sources: Vec::new(),
        };
        if matches!(mode, BodyMode::ProjectionResume) {
            // The parameters other than the failure destination become locals, in their order.
            let parameters = signature.params();
            this.locals.extend(parameters.iter().skip(1));
        }
        let unchecked_float_conversion = body.blocks().any(|block| {
            (0..body.block(block).operations().len()).any(|index| {
                let source = ExpressionSource::from_index(block, index);
                this.analysis.intrinsic(source) == Some(KnownCallee::RawFloatToFloat)
                    && !this.checked_float_conversions.contains(&source)
            })
        });
        if unchecked_float_conversion {
            this.float_conversion_local = Some(this.local(ValType::F64));
        }
        if dispatched {
            this.pc = Some(this.local(ValType::I32));
        }
        // Constants remain immediate unless an indirect argument or pointer use needs storage. A
        // constant that is only ever stored initializes each destination from its literal instead,
        // so it needs no slot initialized on every entry, typically a failure message.
        let only_stored = constants_only_stored(body);
        let (borrowed_strings, borrowed_places) = borrowed_static_strings(body, env);
        for (id, constant) in borrowed_places {
            let text = body
                .constant(constant)
                .representation
                .as_primitive_ty::<StaticStr>()
                .unwrap();
            let reference = this.strings.intern(*text);
            this.borrowed_static_strings
                .insert(Value::Register(id), reference);
        }
        for (index, constant) in body.constants().iter().enumerate() {
            let value = Value::Constant(ConstantId::from_index(index));
            if !only_stored[index] && borrowed_strings[index] {
                let text = constant
                    .representation
                    .as_primitive_ty::<StaticStr>()
                    .unwrap();
                let reference = this.strings.intern(*text);
                this.borrowed_static_strings.insert(value, reference);
                continue;
            }
            if !only_stored[index]
                && (this.analysis.is_addressed(&value)
                    || ScalarType::in_env(constant.ty, &this.env).is_err())
            {
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
                if this.expressions.has_place(&value) {
                    this.storage.insert(value, Storage::Expression);
                } else if this.analysis.is_addressed(&value) {
                    this.slot(value, ty.size())?;
                } else {
                    let local = if parameter.kind == ParameterKind::Return {
                        this.local(ty.wasm())
                    } else {
                        this.input_local(index)
                    };
                    this.storage.insert(value, Storage::Local(local));
                }
            }
        }
        for block in body.blocks() {
            for operation in operations(body.block(block)) {
                if is_elided_stack_operation(operation, &this.no_op_stack_markers)
                    || this.analysis.skips_metadata_load(operation)
                {
                    continue;
                }
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
                    && let Some(payload) = this.optional_payload(this.program.direct_entry(*target))
                {
                    this.reserve_scratch(payload)?;
                }
                if let Some(id) = operation.result_id() {
                    if this
                        .borrowed_static_strings
                        .contains_key(&Value::Register(id))
                    {
                        continue;
                    }
                    if this.expressions.has_pending_value(id) {
                        continue;
                    }
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
                        if let Value::Function(target) = &operation.operands[0]
                            && let Some(resume) = resumes.get(&program.direct_entry(*target))
                        {
                            this.direct_resumes.insert(id, *resume);
                        }
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
                        OperationKind::Variant {
                            tag,
                            storage: Some(storage),
                            ..
                        } if this.only_stored(id) => {
                            let word = storage.encode_tag_id(this.session.variant_tag_id(tag));
                            this.stored_variants.insert(id, word as i32);
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
                        if this.expressions.has_place(&value) {
                            this.storage.insert(value, Storage::Expression);
                        } else if !this.analysis.is_addressed(&value)
                            && let Ok(ty) = scalar(&ty, &this.env)
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
                        && let Ok(ty) = ScalarType::in_env(*ty, &this.env)
                        && this.analysis.is_addressed(&Value::Register(id))
                    {
                        this.slot(Value::Register(id), ty.size())?;
                    }
                    let ty = match &role {
                        ValueRole::Place(_) | ValueRole::StackMarker | ValueRole::VariantTag => {
                            ValType::I32
                        }
                        ValueRole::Materialized(ty) => match scalar(ty, &this.env) {
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
        let required = this.required_helper_locals();
        for helper in HelperLocal::ALL {
            if required[helper as usize] {
                this.helpers.0[helper as usize] = Some(this.local(helper.ty()));
            }
        }
        if let Some(crossing) = crossing {
            // Only what the resumed half reads from before the yield is retained. Other locals,
            // like helpers and the dispatcher's program counter, are written before being read.
            let mut retained = Vec::new();
            for (index, parameter) in signature.parameters.iter().enumerate() {
                // A parameter held in the frame is read from there instead of from its local.
                let value = Value::Parameter(ParameterId::from_index(index));
                if crossing.inputs[index]
                    && !matches!(
                        this.storage.get(&value),
                        Some(Storage::Stack(_) | Storage::Expression)
                    )
                {
                    let ty = match parameter {
                        ParameterTransport::Direct(ty) => *ty,
                        ParameterTransport::Indirect => ValType::I32,
                    };
                    retained.push((this.input_local(index), ty));
                }
            }
            let mut registers = crossing
                .registers
                .iter()
                .filter_map(|id| {
                    this.registers.get(id).copied().or_else(|| {
                        match this.storage.get(&Value::Register(*id)) {
                            Some(Storage::Local(local)) => Some(*local),
                            _ => None,
                        }
                    })
                })
                .chain(
                    crossing
                        .projection_frames
                        .iter()
                        .map(|id| this.projection_frames[id]),
                )
                .collect::<Vec<_>>();
            registers.sort_by_key(|local| local.as_index());
            let local_base = mode.local_base(signature);
            retained.extend(
                registers
                    .into_iter()
                    .map(|local| (local, this.locals[local.as_index() - local_base])),
            );
            let mut locals = Vec::with_capacity(retained.len());
            for (local, ty) in retained {
                locals.push((local, this.reserve_bytes(wasm_value_size(ty))?, ty));
            }
            this.suspension = Some(SuspensionLayout { locals });
            this.frame = Some(match mode {
                BodyMode::ProjectionStart { .. } => this.local(ValType::I32),
                BodyMode::ProjectionResume => WasmLocalId::from_index(RESUME_PARAMETER_COUNT - 1),
                BodyMode::Normal => unreachable!(),
            });
            if matches!(mode, BodyMode::ProjectionResume) {
                this.resume_frontier = Some(this.local(ValType::I32));
            }
        } else if this.frame_size != 0
            || body
                .blocks()
                .any(|block| operations(body.block(block)).any(operation_changes_stack_frontier))
        {
            // A zero-sized frame is still an entry-frontier guard. Witnessed allocas are not part
            // of the fixed frame, so a normal callee must restore their storage before returning;
            // callers may then safely regard calls as frontier-transparent.
            this.frame = Some(this.local(ValType::I32));
        }
        this.code = Code::new(WasmFunction::new(this.locals.iter().map(|ty| (1, *ty))));
        Ok(this)
    }

    fn size(&self, ty: &MirType) -> Result<u32, String> {
        match ty {
            MirType::Pointer(_) => Ok(ScalarType::pointer().size()),
            MirType::Lowered(ty) => {
                if let Some(&size) = self.type_sizes.borrow().get(ty) {
                    return Ok(size);
                }
                let layout = value_layout_for_type(*ty, Location::new_synthesized(), &self.env)
                    .map_err(|e| format!("Wasm storage layout: {e:?}"))?;
                if layout.align > 8 {
                    return Err("Wasm frame alignment above eight bytes".into());
                }
                self.type_sizes.borrow_mut().insert(*ty, layout.size);
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

    /// Mirror the emission paths that use scratch locals. Planning happens after dictionary
    /// and subscript selection, but before suspension layout; an undeclared use fails in `get`.
    fn required_helper_locals(&self) -> [bool; HelperLocal::ALL.len()] {
        use OperationKind::*;

        let mut required = [false; HelperLocal::ALL.len()];
        let mut require = |helpers: &[HelperLocal]| {
            for &helper in helpers {
                required[helper as usize] = true;
            }
        };
        for block in self.body.blocks() {
            let block = self.body.block(block);
            if matches!(
                block.terminator().kind,
                TerminatorKind::Invoke { .. }
                    | TerminatorKind::PropagateError
                    | TerminatorKind::FailureDuringCleanup
            ) {
                require(&[PendingFailure]);
            }
            for operation in operations(block) {
                if is_elided_stack_operation(operation, &self.no_op_stack_markers)
                    || self.analysis.skips_metadata_load(operation)
                {
                    continue;
                }
                if matches!(operation.kind, Store | Move | Memcpy | MoveBytes { .. })
                    && matches!(&operation.operands[0], Value::Register(id) if self.selections.contains_key(id))
                {
                    require(&[Scratch]);
                    continue;
                }
                if let Some(needed) = self.small_copy_locals(operation) {
                    if needed[0] {
                        require(&[CopySource]);
                    }
                    if needed[1] {
                        require(&[CopyDestination]);
                    }
                }
                let witnessed = layout_witness(operation).is_some();
                match operation.kind {
                    Alloca { .. } if witnessed => {
                        require(&[DynamicSize, DynamicAlign, DynamicBase, AllocationEnd]);
                    }
                    Move | Memcpy | MoveBytes { .. } | BlackBox { .. } if witnessed => {
                        require(&[DynamicSize, DynamicAlign]);
                    }
                    Replace => {
                        require(&[DynamicBase, DynamicSize]);
                        if witnessed {
                            require(&[Scratch, DynamicAlign, AllocationEnd]);
                        }
                    }
                    BuildArray { .. } => require(&[Scratch]),
                    BuildClosure {
                        num_hidden_dicts,
                        has_env_dict,
                        ..
                    } => {
                        // Hidden evidence alone needs no size/alignment scratch. Value captures
                        // and the environment dictionary do, even when their layout is static.
                        if has_env_dict || operation.operands.len() > num_hidden_dicts as usize {
                            require(&[DynamicSize, DynamicAlign]);
                        }
                    }
                    Project { .. } => match &operation.operands[0] {
                        Value::Register(id) if self.borrowed_subscripts.contains_key(id) => {
                            require(&[DynamicBase, DynamicSize]);
                        }
                        Value::Function(target) => {
                            let target = self.program.direct_entry(*target);
                            if self.callees[&target].1.fallible
                                && self
                                    .program
                                    .function(target)
                                    .map(Function::result_convention)
                                    != Some(CallResultConvention::YIELDED_ONCE)
                            {
                                require(&[DynamicSize]);
                            }
                        }
                        _ => (), // Unsupported targets are diagnosed during emission.
                    },
                    Call { .. } | Clone { .. } | Drop { .. } | DropInitialized { .. } => {
                        match callee(operation) {
                            Some(Value::Register(id))
                                if self.borrowed_subscripts.contains_key(id) =>
                            {
                                require(&[Scratch, DynamicBase, DynamicSize, DynamicAlign]);
                            }
                            Some(Value::Function(target))
                                if self
                                    .optional_payload(self.program.direct_entry(*target))
                                    .is_some() =>
                            {
                                require(&[Scratch, DynamicBase, DynamicSize]);
                            }
                            _ => (),
                        }
                    }
                    Alloca { .. }
                    | AllocaPlace { .. }
                    | RuntimeAlloc { .. }
                    | RuntimeDealloc
                    | EndProject
                    | CompareEqual
                    | Load
                    | BlackBox { .. }
                    | Subfield { .. }
                    | AddressOffset { .. }
                    | AddressOffsetPlace { .. }
                    | DictEntry { .. }
                    | BuildDictionary { .. }
                    | SubscriptMember { .. }
                    | BuildSubscriptEvidence { .. }
                    | BuildSubscript { .. }
                    | CloneSubscriptEnv { .. }
                    | DropSubscriptEnv
                    | BorrowSubscriptMember { .. }
                    | Variant { .. }
                    | ExtractTag
                    | ExtractPayloadIndirection
                    | IsInitialized
                    | Store
                    | Clear
                    | Memcpy
                    | Move
                    | MoveBytes { .. }
                    | StackSave
                    | StackRestore
                    | CheckCallDepth
                    | CheckFuel
                    | CloneClosureEnv { .. }
                    | DropClosureEnv => (),
                }
            }
        }
        required
    }

    /// A conservative scratch requirement; emission chooses copies in the existing fallback arms.
    fn small_copy_locals(&self, operation: &Operation) -> Option<[bool; 2]> {
        use OperationKind::*;
        let args = &operation.operands;
        let place = match operation.kind {
            Load => &args[0],
            Store => &args[1],
            Memcpy | Move if layout_witness(operation).is_none() => &args[1],
            _ => return None,
        };
        let known_address = |value: &Value| {
            matches!(self.storage.get(value), Some(Storage::Stack(_)))
                || self.copy_address_local(value).is_some()
        };
        let destination_known = if operation.kind == Load {
            known_address(&Value::Register(operation.result_id().unwrap()))
        } else {
            known_address(&args[1])
        };
        let needed = [!known_address(&args[0]), !destination_known];
        // Known bases need no scratch locals, regardless of the copy's size.
        if !needed.contains(&true) {
            return None;
        }
        let ty = self.pointee_type(place).ok()?;
        if scalar(&ty, &self.env).is_ok() {
            return None;
        }
        matches!(self.size(&ty), Ok(12 | 16)).then_some(needed)
    }

    /// An address already in an immutable local, without storage or deferred evaluation.
    fn copy_address_local(&self, value: &Value) -> Option<WasmLocalId> {
        if self.storage.contains_key(value) || self.borrowed_static_strings.contains_key(value) {
            return None;
        }
        match value {
            Value::Parameter(id) => Some(self.parameter_local(*id)),
            Value::Register(id) if !self.expressions.has_value(*id) => {
                self.registers.get(id).copied()
            }
            _ => None,
        }
    }

    fn copy_bytes(&mut self, source: &Value, destination: &Value, size: u32) -> Result<(), String> {
        // Non-scalar Store values use the same backing-storage address as place operands.
        if !matches!(size, 12 | 16) {
            self.address(destination)?;
            self.address(source)?;
            self.i(I::I32Const(size as i32));
            self.i(I::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            });
            return Ok(());
        }
        // Fixed slots reuse the frame base and put their offsets directly into memory accesses.
        let known_address = |value: &Value| match self.storage.get(value) {
            Some(&Storage::Stack(offset)) => Some((
                self.frame.expect("reserved frame storage"),
                memarg_at(3, offset),
            )),
            _ => self
                .copy_address_local(value)
                .map(|local| (local, memarg(0))),
        };
        let source_base = known_address(source);
        let destination_base = known_address(destination);
        if destination_base.is_none() {
            self.address(destination)?;
        }
        if source_base.is_none() {
            self.address(source)?;
        }
        // Evaluate both addresses before capturing either, so nested emission cannot clobber them.
        let source = source_base.unwrap_or_else(|| {
            let local = self.helpers.get(CopySource);
            self.i(I::LocalSet(local.as_u32()));
            (local, memarg(0))
        });
        let destination = destination_base.unwrap_or_else(|| {
            let local = self.helpers.get(CopyDestination);
            self.i(I::LocalSet(local.as_u32()));
            (local, memarg(0))
        });
        emit_small_copy(&mut self.code, size, source, destination);
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
        self.i(I::LocalSet(helpers.get(DynamicBase).as_u32()));
        self.scratch_address(payload);
        self.i(I::LocalSet(helpers.get(DynamicSize).as_u32()));
        adapter.emit(
            &mut self.code,
            helpers.get(DynamicBase),
            helpers.get(DynamicSize),
            helpers.get(Scratch),
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

    /// Pushes the frame pointer and returns `offset`, for the next access to take as its own.
    fn frame_base(&mut self, offset: u32) -> u32 {
        self.i(I::LocalGet(
            self.frame.expect("reserved frame storage").as_u32(),
        ));
        offset
    }

    fn store_local_in_frame(&mut self, local: WasmLocalId, offset: u32, ty: ValType) {
        let offset = self.frame_base(offset);
        self.i(I::LocalGet(local.as_u32()));
        self.i(local_store(ty, offset));
    }

    fn load_local_from_frame(&mut self, local: WasmLocalId, offset: u32, ty: ValType) {
        self.frame_address(offset);
        self.i(local_load(ty, 0));
        self.i(I::LocalSet(local.as_u32()));
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
            self.i(I::LocalTee(helpers.get(DynamicBase).as_u32()));
            self.dictionary_table();
            self.i(I::I32Load(MemArg {
                offset: u64::from(selected.mut_member) * 4,
                ..memarg(2)
            }));
            self.i(I::LocalSet(helpers.get(DynamicSize).as_u32()));
            self.context_pointer(offset_of!(InvocationState, native_failure));
            self.i(I::LocalGet(helpers.get(DynamicBase).as_u32()));
            self.i(I::I32Const(i32::from(selected.materialized)));
            for input in inputs {
                self.address(input)?;
            }
            self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
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
            self.i(I::LocalSet(helpers.get(DynamicSize).as_u32()));
            self.scratch_address(Type::unit());
            self.i(I::I32Load(memarg(2)));
            self.i(I::LocalSet(yielded.as_u32()));
            self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
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
        self.i(I::LocalTee(helpers.get(DynamicBase).as_u32()));
        self.dictionary_table();
        self.i(I::I32Load(MemArg {
            offset: u64::from(selected.mut_member) * 4,
            ..memarg(2)
        }));
        self.i(I::LocalSet(helpers.get(Scratch).as_u32()));
        self.context_pointer(offset_of!(InvocationState, native_failure));
        self.i(I::LocalGet(helpers.get(DynamicBase).as_u32()));
        self.i(I::I32Const(i32::from(selected.materialized)));
        for input in inputs {
            self.address(input)?;
        }
        self.i(I::LocalGet(helpers.get(Scratch).as_u32()));
        self.i(I::CallIndirect {
            type_index: ty.as_u32(),
            table_index: 0,
        });
        self.i(I::LocalSet(helpers.get(DynamicBase).as_u32())); // yielded address
        self.i(I::LocalSet(helpers.get(DynamicAlign).as_u32())); // retained frame
        self.i(I::LocalSet(helpers.get(DynamicSize).as_u32())); // status
        self.i(I::LocalGet(helpers.get(DynamicAlign).as_u32()));
        self.i(I::If(BlockType::Empty));
        self.fail(FailureCode::Invariant);
        self.i(I::End);
        let offset = self.address_base(output)?;
        self.i(I::LocalGet(helpers.get(DynamicBase).as_u32()));
        self.i(I::I32Store(memarg_at(2, offset)));
        self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
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
        if let Some(resume) = self.direct_resumes.get(id) {
            self.i(I::Call(resume.as_u32()));
        } else {
            self.i(I::LocalGet(frame.as_u32()));
            self.i(I::I32Load(MemArg {
                offset: RESUME_SLOT_OFFSET as u64,
                ..memarg(2)
            }));
            self.i(I::CallIndirect {
                type_index: self.subscript_entries.resume_signature.as_u32(),
                table_index: 0,
            });
        }
        self.i(I::Else);
        self.i(I::I32Const(0));
        self.i(I::End);
        self.call_status(invoked, true);
        Ok(())
    }

    fn suspend(&mut self, yielded: &Value) -> Result<(), String> {
        let resume = match self.mode {
            BodyMode::ProjectionStart { resume } => resume,
            BodyMode::ProjectionResume => {
                self.fail(FailureCode::Invariant);
                return Ok(());
            }
            BodyMode::Normal => return Err("ordinary call yielded a place".into()),
        };
        let layout = self
            .suspension
            .take()
            .expect("projected body has a suspension layout");
        for &(local, offset, ty) in &layout.locals {
            self.store_local_in_frame(local, offset, ty);
        }
        self.suspension = Some(layout);
        // A caller that does not know the accessor resumes it through this slot.
        let offset = self.frame_base(RESUME_SLOT_OFFSET);
        self.i(I::I32Const(resume.as_u32() as i32));
        self.i(I::I32Store(memarg_at(2, offset)));
        // The caller may allocate above this retained frame before resuming it. Completion
        // reclaims the frame only if the frontier is still this one when it resumes.
        let offset = self.frame_base(SUSPENDED_STACK_END_OFFSET);
        self.i(I::GlobalGet(Global::Stack as u32));
        self.i(I::I32Store(memarg_at(2, offset)));
        self.i(I::I32Const(0));
        self.i(I::LocalGet(self.frame.unwrap().as_u32()));
        self.address(yielded)?;
        self.i(I::Return);
        Ok(())
    }

    fn restore_suspension(&mut self) {
        let layout = self
            .suspension
            .take()
            .expect("projected body has a suspension layout");
        for &(local, offset, ty) in &layout.locals {
            self.load_local_from_frame(local, offset, ty);
        }
        self.suspension = Some(layout);
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
                    helpers.get(DynamicSize)
                } else {
                    helpers.get(DynamicAlign)
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
            self.imports.failure_function(),
            helpers.get(DynamicSize),
            helpers.get(DynamicAlign),
            helpers.get(DynamicBase),
            helpers.get(AllocationEnd),
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
        let pending = self.helper_locals().get(PendingFailure);
        self.context_pointer(offset_of!(InvocationState, diagnostics));
        self.i(I::LocalGet(pending.as_u32()));
        self.i(I::Call(
            self.imports.function_index("capture_failure").as_u32(),
        ));
        self.i(I::LocalSet(pending.as_u32()));
    }

    fn propagate_failure(&mut self) {
        let pending = self.helper_locals().get(PendingFailure);
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
        // Read a direct result while its frame and evidence are still live. Keeping the value on
        // the Wasm operand stack across the epilogue also lets expression stackification defer its
        // producer safely to this point.
        if returns_direct_result(self.mode, self.signature) {
            if let Some(result) = self.forwarded_result.clone() {
                self.value(&result)?;
            } else {
                let result =
                    Value::Parameter(ParameterId::from_index(self.body.parameters().len() - 1));
                self.load_place(&result, self.pointee(&result)?)?;
            }
        }
        for index in 0..self.owned_evidence.len() {
            self.release_evidence(&Value::Register(self.owned_evidence[index]))?;
        }
        if let Some(frame) = self.frame {
            if matches!(self.mode, BodyMode::ProjectionResume) {
                let resumed = self
                    .resume_frontier
                    .expect("projection resume records its entry stack frontier");
                // Reclaim the continuation and everything above it when the caller allocated
                // nothing above it while it was suspended. The current frontier cannot tell,
                // because the resumed half may have allocated too. Otherwise the caller's storage
                // is live: keep the continuation, which the caller reclaims with it, and only
                // discard what the resumed half allocated.
                self.i(I::LocalGet(resumed.as_u32()));
                self.i(I::LocalGet(frame.as_u32()));
                self.i(I::I32Load(MemArg {
                    offset: SUSPENDED_STACK_END_OFFSET.into(),
                    ..memarg(2)
                }));
                self.i(I::I32Eq);
                self.i(I::If(BlockType::Empty));
                leave_frame(&mut self.code, frame);
                self.i(I::Else);
                self.i(I::LocalGet(resumed.as_u32()));
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
            let base = self.address_base(destination)?;
            self.context_pointer(offset_of!(InvocationState, strings));
            // Load the immutable handle before storing it in the destination.
            self.i(I::I32Load(memarg_at(
                2,
                (index * size_of::<StaticStr>()) as u32,
            )));
            self.i(I::I32Store(memarg_at(2, base + offset)));
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
            let base = self.address_base(destination)?;
            self.literal(literal)?;
            ScalarType::in_env(ty, &self.env)?.store_at(&mut self.code, base + offset);
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
            .map(|ty| ScalarType::in_env(ty, &self.env))
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

    fn call_operation(
        &mut self,
        op: &Operation,
        invoked: bool,
        source: ExpressionSource,
    ) -> Result<(), String> {
        let intrinsic = self.analysis.intrinsic(source);
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
        if let Some(intrinsic) = intrinsic {
            let checked = self.checked_float_conversions.contains(&source);
            return self.call_intrinsic(intrinsic, &inputs, output, invoked, checked);
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
        let result_offset = if direct_result.is_some() {
            self.prepare_store(output.unwrap())?
        } else {
            0
        };
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
            self.finish_store(output.unwrap(), ty, result_offset);
        }
        self.call_status(invoked, abi.fallible);
        Ok(())
    }

    /// Emits a known callee inline. `checked` says that a `raw_float_to_float` operand is known
    /// to be finite, which makes the conversion the identity.
    fn call_intrinsic(
        &mut self,
        intrinsic: KnownCallee,
        inputs: &[&Value],
        output: Option<&Value>,
        invoked: bool,
        checked: bool,
    ) -> Result<(), String> {
        let arity = match intrinsic {
            KnownCallee::IntAdd
            | KnownCallee::IntSub
            | KnownCallee::IntMul
            | KnownCallee::IntCmp
            | KnownCallee::IntLt
            | KnownCallee::IntLe
            | KnownCallee::IntGt
            | KnownCallee::IntGe
            | KnownCallee::IntEq
            | KnownCallee::BoolEq
            | KnownCallee::FloatAdd
            | KnownCallee::FloatSub
            | KnownCallee::FloatMul
            | KnownCallee::FloatCmp
            | KnownCallee::FloatLt
            | KnownCallee::FloatLe
            | KnownCallee::FloatGt
            | KnownCallee::FloatGe
            | KnownCallee::FloatEq
            | KnownCallee::RawFloatAdd
            | KnownCallee::RawFloatSub
            | KnownCallee::RawFloatMul => 2,
            KnownCallee::IntNeg
            | KnownCallee::IntFromInt
            | KnownCallee::FloatNeg
            | KnownCallee::RawFloatNeg
            | KnownCallee::RawFloatIsFinite
            | KnownCallee::RawFloatToFloat
            | KnownCallee::BoolNot => 1,
            _ => unreachable!("wasm_intrinsic filters unsupported known callees"),
        };
        if inputs.len() != arity {
            return Err("wasm intrinsic argument count".into());
        }
        let output = output.ok_or("wasm intrinsic result storage")?;
        let ty = self.pointee(output)?;
        let offset = self.prepare_store(output)?;
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
            // Both float types are f64 values, so a raw operation reads a `float` input as is.
            KnownCallee::RawFloatAdd | KnownCallee::RawFloatSub | KnownCallee::RawFloatMul => {
                self.read(inputs[0])?;
                self.read(inputs[1])?;
                self.i(match intrinsic {
                    KnownCallee::RawFloatAdd => I::F64Add,
                    KnownCallee::RawFloatSub => I::F64Sub,
                    KnownCallee::RawFloatMul => I::F64Mul,
                    _ => unreachable!(),
                });
            }
            KnownCallee::RawFloatNeg => {
                self.read(inputs[0])?;
                self.i(I::F64Neg);
            }
            KnownCallee::RawFloatIsFinite => {
                self.read(inputs[0])?;
                self.finite_test();
            }
            KnownCallee::RawFloatToFloat if checked => {
                self.read(inputs[0])?;
            }
            KnownCallee::RawFloatToFloat => {
                // The total fallback: the value itself when finite, and zero otherwise.
                let value = self
                    .float_conversion_local
                    .expect("an unchecked float conversion reserved its local");
                self.read(inputs[0])?;
                self.i(I::LocalTee(value.as_u32()));
                self.i(I::F64Const(0.0.into()));
                self.i(I::LocalGet(value.as_u32()));
                self.finite_test();
                self.i(I::Select);
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
            KnownCallee::IntLt
            | KnownCallee::IntLe
            | KnownCallee::IntGt
            | KnownCallee::IntGe
            | KnownCallee::IntEq
            | KnownCallee::BoolEq => {
                self.read(inputs[0])?;
                self.read(inputs[1])?;
                self.i(match intrinsic {
                    KnownCallee::IntLt => I::I32LtS,
                    KnownCallee::IntLe => I::I32LeS,
                    KnownCallee::IntGt => I::I32GtS,
                    KnownCallee::IntGe => I::I32GeS,
                    KnownCallee::IntEq | KnownCallee::BoolEq => I::I32Eq,
                    _ => unreachable!(),
                });
            }
            KnownCallee::FloatLt
            | KnownCallee::FloatLe
            | KnownCallee::FloatGt
            | KnownCallee::FloatGe
            | KnownCallee::FloatEq => {
                self.read(inputs[0])?;
                self.read(inputs[1])?;
                self.i(match intrinsic {
                    KnownCallee::FloatLt => I::F64Lt,
                    KnownCallee::FloatLe => I::F64Le,
                    KnownCallee::FloatGt => I::F64Gt,
                    KnownCallee::FloatGe => I::F64Ge,
                    KnownCallee::FloatEq => I::F64Eq,
                    _ => unreachable!(),
                });
            }
            KnownCallee::IntCmp | KnownCallee::FloatCmp => {
                // Select the semantic session-local tag. Both arguments are read twice;
                // expression planning keeps them in locals unless a predicate is fused.
                self.i(I::I32Const(self.session.variant_tag_id(ustr("Less")) as i32));
                self.i(I::I32Const(
                    self.session.variant_tag_id(ustr("Greater")) as i32
                ));
                self.i(I::I32Const(
                    self.session.variant_tag_id(ustr("Equal")) as i32
                ));
                self.read(inputs[0])?;
                self.read(inputs[1])?;
                self.i(match intrinsic {
                    KnownCallee::IntCmp => I::I32GtS,
                    KnownCallee::FloatCmp => I::F64Gt,
                    _ => unreachable!(),
                });
                self.i(I::Select);
                self.read(inputs[0])?;
                self.read(inputs[1])?;
                self.i(match intrinsic {
                    KnownCallee::IntCmp => I::I32LtS,
                    KnownCallee::FloatCmp => I::F64Lt,
                    _ => unreachable!(),
                });
                self.i(I::Select);
            }
            _ => unreachable!("wasm_intrinsic filters unsupported known callees"),
        }
        self.finish_store(output, ty, offset);
        self.call_status(invoked, false);
        Ok(())
    }

    /// Replaces the f64 on the stack by whether it is finite: `x * 0` is a zero exactly when `x`
    /// is finite, and NaN for an infinity or NaN.
    fn finite_test(&mut self) {
        self.i(I::F64Const(0.0.into()));
        self.i(I::F64Mul);
        self.i(I::F64Const(0.0.into()));
        self.i(I::F64Eq);
    }

    fn local(&mut self, ty: ValType) -> WasmLocalId {
        let id = WasmLocalId::from_index(self.mode.local_base(self.signature) + self.locals.len());
        self.locals.push(ty);
        id
    }

    /// The local holding a parameter, which a resume body restores from its frame.
    fn input_local(&self, index: usize) -> WasmLocalId {
        match self.mode {
            BodyMode::ProjectionResume => WasmLocalId::from_index(RESUME_PARAMETER_COUNT + index),
            _ => self.signature.input_local(index),
        }
    }

    fn parameter_local(&self, id: ParameterId) -> WasmLocalId {
        if self.body.parameters()[id.as_index()].kind == ParameterKind::Return {
            self.input_local(self.signature.parameters.len())
        } else {
            self.input_local(id.as_index())
        }
    }

    /// Whether register `id` is read only as the value of one `store`.
    fn only_stored(&self, id: ValueId) -> bool {
        self.analysis.sole_use(id).is_some_and(|source| {
            self.body
                .block(source.block)
                .operations()
                .get(source.operation_id().as_index())
                .is_some_and(|operation| {
                    operation.kind == OperationKind::Store
                        && operation.operands[0] == Value::Register(id)
                })
        })
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
        emit_failure(&mut self.code, self.imports.failure_function(), code);
    }

    pub(super) fn address(&mut self, value: &Value) -> Result<(), String> {
        if let Some(&index) = self.borrowed_static_strings.get(value) {
            self.context_pointer(offset_of!(InvocationState, strings));
            self.i(I::I32Const((index * size_of::<StaticStr>()) as i32));
            self.i(I::I32Add);
            return Ok(());
        }
        match self.storage.get(value) {
            Some(Storage::Stack(offset)) => {
                let offset = *offset;
                self.frame_address(offset);
            }
            Some(Storage::Local(_)) => return Err("address requested for promoted storage".into()),
            Some(Storage::Expression) => {
                return Err("address requested for stackified storage".into());
            }
            None => self.value(value)?,
        }
        Ok(())
    }

    /// Pushes the base of a place's address and returns the static offset that completes it,
    /// for the access that follows to take as its own. A frame slot never wraps the address
    /// space, as its frame was checked against the stack end.
    pub(super) fn address_base(&mut self, value: &Value) -> Result<u32, String> {
        if let Some(&Storage::Stack(offset)) = self.storage.get(value) {
            return Ok(self.frame_base(offset));
        }
        self.address(value)?;
        Ok(0)
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
        if matches!(value, Value::Register(id) if self.variant_shells.contains(id))
            && self.roles.get(value, self.body.constants()).is_some_and(
                |r| matches!(&*r, ValueRole::Materialized(ty) if scalar(ty, &self.env).is_ok_and(ScalarType::is_tag)),
            )
        {
            self.address(value)?;
            self.i(I::I32Load(memarg(2)));
            return Ok(());
        }
        // A variant whose only use is a store has no local; a forwarded direct result reads it here.
        if let Value::Register(id) = value
            && let Some(&word) = self.stored_variants.get(id)
        {
            self.i(I::I32Const(word));
            return Ok(());
        }
        if self.storage.contains_key(value)
            && !self.roles.get(value, self.body.constants()).is_some_and(
                |r| matches!(&*r, ValueRole::Materialized(ty) if scalar(ty, &self.env).is_ok()),
            )
        {
            return self.address(value);
        }
        match value {
            Value::Register(id) => {
                if let Some(source) = self.expressions.take_value(*id) {
                    return self.stackified(source);
                }
                let local = self
                    .registers
                    .get(id)
                    .copied()
                    .ok_or_else(|| format!("register {id:?} has no Wasm value"))?;
                self.i(I::LocalGet(local.as_u32()));
            }
            Value::Parameter(id) => self.i(I::LocalGet(self.parameter_local(*id).as_u32())),
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
        } else if let Some(value) = literal.as_primitive_ty::<RawFloat>() {
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
            &self.env,
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
            let ty = scalar(&pointee, &self.env)?;
            self.load_place(value, ty)?;
            Ok(ty)
        } else {
            let ValueRole::Materialized(ty) = &*role else {
                return Err("expected scalar value".into());
            };
            let ty = scalar(ty, &self.env)?;
            self.value(value)?;
            Ok(ty)
        }
    }

    fn load_place(&mut self, value: &Value, ty: ScalarType) -> Result<(), String> {
        match self.storage.get(value).copied() {
            Some(Storage::Local(local)) => self.i(I::LocalGet(local.as_u32())),
            Some(Storage::Expression) => {
                let source = self
                    .expressions
                    .take_place(value)
                    .ok_or("stackified scalar place read more than once")?;
                self.stackified(source)?;
            }
            Some(Storage::Stack(_)) | None => {
                self.address(value)?;
                self.load(ty);
            }
        }
        Ok(())
    }

    // A memory store needs its address below the value; a local store needs only the value.
    // It returns the static offset that `finish_store` takes.
    fn prepare_store(&mut self, destination: &Value) -> Result<u32, String> {
        if matches!(
            self.storage.get(destination),
            Some(Storage::Local(_) | Storage::Expression)
        ) {
            return Ok(0);
        }
        self.address_base(destination)
    }

    fn finish_store(&mut self, destination: &Value, ty: ScalarType, offset: u32) {
        match self.storage.get(destination) {
            Some(Storage::Local(local)) => self.i(I::LocalSet(local.as_u32())),
            Some(Storage::Expression) => (),
            Some(Storage::Stack(_)) | None => ty.store_at(&mut self.code, offset),
        }
    }

    fn load(&mut self, ty: ScalarType) {
        ty.load(&mut self.code);
    }

    pub(super) fn emit(mut self) -> Result<EmittedBody, String> {
        if let Some(frame) = self.frame
            && !matches!(self.mode, BodyMode::ProjectionResume)
        {
            enter_frame(
                &mut self.code,
                self.imports.failure_function(),
                frame,
                self.frame_size,
            );
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
                let offset = self.address_base(&Value::Register(self.owned_evidence[index]))?;
                self.i(I::I64Const(0));
                self.i(I::I64Store(memarg_at(2, offset)));
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
                    let offset = self.address_base(&value)?;
                    self.i(I::LocalGet(self.input_local(index).as_u32()));
                    ScalarType::in_env(self.body.parameters()[index].ty, &self.env)?
                        .store_at(&mut self.code, offset);
                }
            }
        } else {
            self.i(I::GlobalGet(Global::Stack as u32));
            self.i(I::LocalSet(
                self.resume_frontier
                    .expect("resumed projection has a stack floor")
                    .as_u32(),
            ));
            self.restore_suspension();
            if let Some(pc) = self.pc {
                self.i(I::I32Const(self.entry.as_u32() as i32));
                self.i(I::LocalSet(pc.as_u32()));
            }
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
                    self.emit_dispatched_block(block_id, count - block_id.as_u32(), next)?;
                }
                self.i(I::End);
                self.fail(FailureCode::Invariant);
                self.i(I::End);
            }
            ControlFlow::Structured(items) => {
                self.emit_items(&items, None)?;
                debug_assert!(self.labels.is_empty());
            }
        }
        if self.fallthrough_return.is_none() {
            self.i(I::Unreachable);
        }
        debug_assert!(
            self.expressions
                .is_fully_emitted(|block| self.emitted[block.as_index()]),
            "every stackified scalar expression and place is consumed"
        );
        debug_assert!(self.sources.is_empty(), "every source region is closed");
        self.i(I::End);
        let (function, source_map) = self.code.finish();
        Ok(EmittedBody {
            function,
            source_map,
        })
    }

    /// Emits a structured sequence; `next` is the block reached by falling off its end.
    fn emit_items(&mut self, items: &[Item], next: Option<BlockId>) -> Result<(), String> {
        for (index, item) in items.iter().enumerate() {
            match item {
                Item::Block { follower, body } => {
                    self.i(I::Block(BlockType::Empty));
                    self.labels.push(Label::Block(*follower));
                    self.emit_items(body, Some(*follower))?;
                    self.labels.pop();
                    self.i(I::End);
                }
                Item::Loop { header, body } => {
                    debug_assert_eq!(index + 1, items.len(), "a loop ends its sequence");
                    self.i(I::Loop(BlockType::Empty));
                    self.labels.push(Label::Loop(*header));
                    self.emit_items(body, next)?;
                    self.labels.pop();
                    self.i(I::End);
                }
                Item::Node {
                    block,
                    nested,
                    continuation,
                } => {
                    debug_assert_eq!(
                        continuation.is_none(),
                        index + 1 == items.len(),
                        "only a node without continuation ends its sequence"
                    );
                    self.emit_node(*block, nested, *continuation, next)?;
                }
            }
        }
        Ok(())
    }

    /// Emits a block and its terminator in structured control flow.
    ///
    /// Each target other than the one taken without a test is entered after its arm's condition:
    /// a nested target inside an `if`, any other one by a branch to its label. The untested
    /// target is the continuation, else `next` when it is a target, so that no branch is needed.
    fn emit_node(
        &mut self,
        block_id: BlockId,
        nested: &[(BlockId, Vec<Item>)],
        continuation: Option<BlockId>,
        next: Option<BlockId>,
    ) -> Result<(), String> {
        self.emit_operations(block_id)?;
        let body = self.body;
        let terminator = body.block(block_id).terminator();
        let targets = distinct_targets(&terminator.kind);
        let untested = continuation
            .or_else(|| targets.iter().copied().find(|target| Some(*target) == next))
            .or_else(|| match &terminator.kind {
                TerminatorKind::CondBr { else_target, .. } => Some(*else_target),
                TerminatorKind::SwitchVariant { default, .. } => Some(*default),
                TerminatorKind::Invoke { normal, .. } => Some(*normal),
                _ => targets.first().copied(),
            });
        match &terminator.kind {
            TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } => {
                self.open_source(operation.span);
                let source =
                    ExpressionSource::from_index(block_id, body.block(block_id).operations().len());
                self.call_operation(operation, true, source)?;
                if normal == error {
                    self.i(I::If(BlockType::Empty));
                    self.capture_failure();
                    self.i(I::End);
                } else if untested == Some(*normal) {
                    self.i(I::If(BlockType::Empty));
                    self.labels.push(Label::If);
                    self.capture_failure();
                    self.enter(*error, nested)?;
                    self.labels.pop();
                    self.i(I::End);
                } else {
                    self.i(I::I32Eqz);
                    self.enter_if(*normal, nested)?;
                    self.capture_failure();
                }
                self.close_source();
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::CondBr { .. }
            | TerminatorKind::SwitchVariant { .. } => {
                self.open_source(terminator.span);
                for &target in &targets {
                    if Some(target) != untested {
                        self.arm_condition(block_id, target)?;
                        self.enter_if(target, nested)?;
                    }
                }
                self.close_source();
            }
            TerminatorKind::Yield { place, .. } => {
                self.open_source(terminator.span);
                self.suspend(place)?;
                self.close_source();
                return Ok(());
            }
            TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup
            | TerminatorKind::InvariantFailure { .. } => {
                self.open_source(terminator.span);
                self.exit(block_id)?;
                self.close_source();
                return Ok(());
            }
        }
        let untested = untested.expect("a terminator with targets has an untested one");
        if Some(untested) != continuation && Some(untested) != next {
            self.open_source(terminator.span);
            self.i(I::Br(self.label_depth(untested)));
            self.close_source();
        }
        Ok(())
    }

    /// Enters `target` when the condition on the operand stack holds.
    fn enter_if(&mut self, target: BlockId, nested: &[(BlockId, Vec<Item>)]) -> Result<(), String> {
        if nested.iter().any(|(block, _)| *block == target) {
            self.i(I::If(BlockType::Empty));
            self.labels.push(Label::If);
            self.enter(target, nested)?;
            self.labels.pop();
            self.i(I::End);
        } else {
            self.i(I::BrIf(self.label_depth(target)));
        }
        Ok(())
    }

    /// Enters `target` from inside an arm whose end must not be reached.
    ///
    /// A nested arm is not the terminator's code: it has the sources of its own blocks.
    fn enter(&mut self, target: BlockId, nested: &[(BlockId, Vec<Item>)]) -> Result<(), String> {
        if let Some((_, items)) = nested.iter().find(|(block, _)| *block == target) {
            self.open_source(DebugLocation::new_synthesized());
            self.emit_items(items, None)?;
            self.close_source();
            Ok(())
        } else {
            self.i(I::Br(self.label_depth(target)));
            Ok(())
        }
    }

    /// The relative depth of the enclosing label that branching to `target` uses.
    fn label_depth(&self, target: BlockId) -> u32 {
        self.labels
            .iter()
            .rev()
            .position(|label| matches!(label, Label::Block(block) | Label::Loop(block) if *block == target))
            .expect("a branch target has an enclosing label") as u32
    }

    /// Pushes whether the terminator of `block_id` selects `target`.
    fn arm_condition(&mut self, block_id: BlockId, target: BlockId) -> Result<(), String> {
        let body = self.body;
        match &body.block(block_id).terminator().kind {
            TerminatorKind::CondBr {
                condition,
                then_target,
                ..
            } => {
                self.read(condition)?;
                if target != *then_target {
                    self.i(I::I32Eqz);
                }
            }
            TerminatorKind::SwitchVariant {
                tag,
                cases,
                default,
            } => {
                if let Some(intrinsic) = self.analysis.comparison_switch(body.block(block_id)) {
                    let operations = body.block(block_id).operations();
                    let call = &operations[operations.len() - 2];
                    self.open_source(call.span);
                    self.comparison_switch_predicate(intrinsic, call, cases, *default, target)?;
                    self.close_source();
                    return Ok(());
                }
                // The default arm is selected by no case reaching another target.
                let (selected, compare, combine) = if target == *default {
                    (
                        cases
                            .iter()
                            .filter(|(_, case_target)| case_target != default)
                            .collect::<Vec<_>>(),
                        I::I32Ne,
                        I::I32And,
                    )
                } else {
                    (
                        cases
                            .iter()
                            .filter(|(_, case_target)| *case_target == target)
                            .collect::<Vec<_>>(),
                        I::I32Eq,
                        I::I32Or,
                    )
                };
                if selected.is_empty() {
                    self.i(I::I32Const(1));
                }
                for (index, (case, _)) in selected.into_iter().enumerate() {
                    self.value(tag)?;
                    self.i(I::I32Const(self.session.variant_tag_id(*case) as i32));
                    self.i(compare.clone());
                    if index > 0 {
                        self.i(combine.clone());
                    }
                }
            }
            _ => unreachable!("expected a conditional terminator"),
        }
        Ok(())
    }

    /// Emits a terminator without successors.
    fn exit(&mut self, block_id: BlockId) -> Result<(), String> {
        match &self.body.block(block_id).terminator().kind {
            TerminatorKind::PropagateError => {
                self.propagate_failure();
                self.return_frame(true, true)?;
            }
            TerminatorKind::FailureDuringCleanup => {
                self.propagate_failure();
                // A correctly chained cleanup failure already trapped while propagating.
                self.fail(FailureCode::Invariant);
            }
            TerminatorKind::Return => {
                self.return_frame(false, self.fallthrough_return != Some(block_id))?;
            }
            TerminatorKind::InvariantFailure { .. } => self.fail(FailureCode::Invariant),
            _ => unreachable!("expected a terminator without successors"),
        }
        Ok(())
    }

    fn emit_operations(&mut self, block_id: BlockId) -> Result<(), String> {
        self.emitted[block_id.as_index()] = true;
        let operations = self.body.block(block_id).operations();
        let operation_count = operations.len();
        let mut index = 0;
        while index < operations.len() {
            let operation = &operations[index];
            if is_elided_stack_operation(operation, &self.no_op_stack_markers)
                || self.analysis.skips_metadata_load(operation)
            {
                index += 1;
                continue;
            }
            if self.expressions.skips(
                ExpressionSource::from_index(block_id, index),
                &self.analysis,
            ) {
                index += 1;
                continue;
            }
            if operation
                .result_id()
                .is_some_and(|id| self.expressions.has_pending_value(id))
            {
                index += 1;
                continue;
            }
            if self.forwarded_result.is_some()
                && block_id == self.body.entry()
                && index + 1 == operation_count
            {
                index += 1;
                continue;
            }
            if index + 2 == operations.len()
                && self
                    .analysis
                    .comparison_switch(self.body.block(block_id))
                    .is_some()
            {
                // The two-target switch emits its comparison directly at the terminator.
                break;
            }
            if let Some(test) = operations.get(index + 2)
                && let Some(intrinsic) = test
                    .result_id()
                    .and_then(|result| self.analysis.comparison_fusion(result))
            {
                self.open_source(operation.span);
                self.comparison_predicate(intrinsic, operation, test)?;
                self.finish_operation_result(test)?;
                self.close_source();
                index += 3;
                continue;
            }
            self.open_source(operation.span);
            self.operation(ExpressionSource::from_index(block_id, index), operation)
                .map_err(|e| {
                    format!(
                        "{} in block {}: {e}",
                        OperationKindDiscriminant::from(&operation.kind),
                        block_id.as_u32()
                    )
                })?;
            self.close_source();
            index += 1;
        }
        Ok(())
    }

    /// Emits a block of the program-counter dispatcher, whose loop is `depth` labels up.
    fn emit_dispatched_block(
        &mut self,
        block_id: BlockId,
        depth: u32,
        next: Option<BlockId>,
    ) -> Result<(), String> {
        self.emit_operations(block_id)?;
        let block = self.body.block(block_id);
        let span = match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => operation.span,
            _ => block.terminator().span,
        };
        self.open_source(span);
        if let Some((then_target, else_target)) = conditional_targets(&block.terminator().kind) {
            if then_target == else_target {
                self.dispatch_branch(then_target, depth, next, 0);
            } else if Some(then_target) == next {
                self.arm_condition(block_id, else_target)?;
                self.dispatch_branch_if(else_target, depth);
            } else if Some(else_target) == next {
                self.arm_condition(block_id, then_target)?;
                self.dispatch_branch_if(then_target, depth);
            } else {
                self.i(I::I32Const(then_target.as_u32() as i32));
                self.i(I::I32Const(else_target.as_u32() as i32));
                self.arm_condition(block_id, then_target)?;
                self.i(I::Select);
                self.dispatch(depth, 0);
            }
            self.close_source();
            return Ok(());
        }
        match &block.terminator().kind {
            TerminatorKind::Goto { target } => {
                self.dispatch_branch(*target, depth, next, 0);
            }
            TerminatorKind::CondBr { .. } => unreachable!("conditional branches are handled above"),
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
                        self.dispatch_branch_if(*target, depth);
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
                    self.dispatch(depth, 0);
                }
            }
            TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } => {
                let source = ExpressionSource::from_index(block_id, block.operations().len());
                self.call_operation(operation, true, source)?;
                if normal == error {
                    self.i(I::If(BlockType::Empty));
                    self.capture_failure();
                    self.i(I::End);
                    self.dispatch_branch(*normal, depth, next, 0);
                } else if Some(*normal) == next {
                    self.i(I::If(BlockType::Empty));
                    self.capture_failure();
                    self.dispatch_branch(*error, depth, None, 1);
                    self.i(I::End);
                } else if Some(*error) == next {
                    self.i(I::If(BlockType::Empty));
                    self.capture_failure();
                    self.i(I::Else);
                    self.dispatch_branch(*normal, depth, None, 1);
                    self.i(I::End);
                } else {
                    self.i(I::If(BlockType::Result(ValType::I32)));
                    self.capture_failure();
                    self.i(I::I32Const(error.as_u32() as i32));
                    self.i(I::Else);
                    self.i(I::I32Const(normal.as_u32() as i32));
                    self.i(I::End);
                    self.dispatch(depth, 0);
                }
            }
            TerminatorKind::Yield { place, .. } => self.suspend(place)?,
            TerminatorKind::Return
            | TerminatorKind::PropagateError
            | TerminatorKind::FailureDuringCleanup
            | TerminatorKind::InvariantFailure { .. } => self.exit(block_id)?,
        }
        self.close_source();
        Ok(())
    }

    /// Opens the source region of the code emitted until [`close_source`](Self::close_source).
    ///
    /// Regions nest, and the code of the inner one belongs to it only: the enclosing region pauses
    /// until the inner one closes. A synthesized `span` not inlined from anywhere gives its code no
    /// source, as does emission without source map.
    fn open_source(&mut self, span: DebugLocation) {
        self.sources.push(self.code.spans());
        self.code.set_source(
            (self.source_map && (!span.is_synthesized() || span.inlined_at.is_some()))
                .then_some(span),
        );
    }

    fn close_source(&mut self) {
        let enclosing = self.sources.pop().expect("an open source region closes");
        self.code.set_spans(enclosing);
    }

    /// Emits the stackified operation at `source` where its value is read, in its own source
    /// region.
    fn stackified(&mut self, source: ExpressionSource) -> Result<(), String> {
        let body = self.body;
        let operation = &body.block(source.block).operations()[source.operation_id().as_index()];
        self.open_source(operation.span);
        self.operation(source, operation)?;
        self.close_source();
        Ok(())
    }

    /// Continues the dispatcher loop, `depth + nested` labels up, at the block on the stack.
    fn dispatch(&mut self, depth: u32, nested: u32) {
        self.i(I::LocalSet(
            self.pc.expect("branch needs a dispatcher").as_u32(),
        ));
        self.i(I::Br(depth.checked_add(nested).expect("Wasm branch depth")));
    }

    fn dispatch_branch(&mut self, target: BlockId, depth: u32, next: Option<BlockId>, nested: u32) {
        if Some(target) == next {
            return;
        }
        self.i(I::I32Const(target.as_u32() as i32));
        self.dispatch(depth, nested);
    }

    /// Dispatches to a MIR block if the condition on the operand stack holds.
    fn dispatch_branch_if(&mut self, target: BlockId, depth: u32) {
        self.i(I::I32Const(target.as_u32() as i32));
        self.i(I::LocalSet(
            self.pc.expect("branch needs a dispatcher").as_u32(),
        ));
        self.i(I::BrIf(depth));
    }

    fn operation(&mut self, source: ExpressionSource, op: &Operation) -> Result<(), String> {
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
                let offset = self.address_base(&result)?;
                self.address(&args[0])?;
                self.i(I::I32Load(memarg(2)));
                self.i(I::I32Store(memarg_at(2, offset)));
                let offset = self.address_base(&result)?;
                self.address(&args[0])?;
                self.i(I::I32Load(MemArg {
                    offset: ENVIRONMENT_OFFSET,
                    ..memarg(2)
                }));
                self.i(I::Call(clone.as_u32()));
                self.i(I::I32Store(memarg_at(
                    2,
                    offset + ENVIRONMENT_OFFSET as u32,
                )));
                return Ok(());
            }
            CloneSubscriptEnv { .. } => {
                let clone = self
                    .callable_entries
                    .clone
                    .ok_or("missing callable environment clone entry")?;
                let result = Value::Register(op.result_id().unwrap());
                let offset = self.address_base(&result)?;
                self.address(&args[0])?;
                self.i(I::I32Load(memarg(2)));
                self.i(I::I32Store(memarg_at(2, offset)));
                let offset = self.address_base(&result)?;
                self.address(&args[0])?;
                self.i(I::I32Load(MemArg {
                    offset: ENVIRONMENT_OFFSET,
                    ..memarg(2)
                }));
                self.i(I::Call(clone.as_u32()));
                self.i(I::I32Store(memarg_at(
                    2,
                    offset + ENVIRONMENT_OFFSET as u32,
                )));
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
                let offset = self.address_base(&args[0])?;
                self.i(I::I64Const(0));
                self.i(I::I64Store(memarg_at(2, offset)));
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
                    let offset = capture_offset + field.offset as u32;
                    if field.is_storage_flag {
                        let offset = self.frame_base(offset);
                        self.value(&args[0])?;
                        self.i(I::I32Load(MemArg {
                            offset: ENVIRONMENT_OFFSET,
                            ..memarg(2)
                        }));
                        self.i(I::I32Load8U(memarg_at(0, field.offset as u32)));
                        self.i(I::I32Store8(memarg_at(0, offset)));
                    } else {
                        self.frame_address(offset);
                        self.value(&args[0])?;
                        self.i(I::I32Load(MemArg {
                            offset: ENVIRONMENT_OFFSET,
                            ..memarg(2)
                        }));
                        self.i(I::I32Const(field.offset as i32));
                        self.i(I::I32Add);
                        self.i(I::I32Const(size_of::<DictionaryReference>() as i32));
                        self.i(I::MemoryCopy {
                            src_mem: 0,
                            dst_mem: 0,
                        });
                    }
                }
                for (field, argument) in fields[inherited..].iter().zip(&args[1..]) {
                    if field.is_storage_flag {
                        let offset = self.frame_base(capture_offset + field.offset as u32);
                        self.read(argument)?;
                        self.i(I::I32Store8(memarg_at(0, offset)));
                    } else {
                        self.frame_address(capture_offset + field.offset as u32);
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
                let offset = self.address_base(&result)?;
                self.value(&args[0])?;
                self.i(I::I32Load(memarg(2)));
                self.i(I::I32Store(memarg_at(2, offset)));
                let offset = self.address_base(&result)?;
                self.context_pointer(offset_of!(InvocationState, evidence));
                self.value(&args[0])?;
                self.i(I::Call(
                    self.imports
                        .function_index("materialize_subscript_environment")
                        .as_u32(),
                ));
                self.i(I::I32Store(memarg_at(
                    2,
                    offset + ENVIRONMENT_OFFSET as u32,
                )));
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
                let layout = product_layout_spec(array_ty, op.span.location, &self.env)
                    .ok_or("array representation")?;
                let element = value_layout_for_type(*element_ty, op.span.location, &self.env)
                    .map_err(|e| format!("array element layout: {e:?}"))?;
                let bytes = element
                    .size
                    .checked_mul(elements.len() as u32)
                    .ok_or("array allocation overflow")?;
                self.i(I::I32Const(bytes as i32));
                self.i(I::I32Const(element.align as i32));
                self.i(I::Call(self.imports.function_index("alloc").as_u32()));
                self.i(I::LocalSet(helpers.get(Scratch).as_u32()));
                for (index, value) in elements.iter().enumerate() {
                    // The allocation holds every element, so no offset wraps the address space.
                    let offset = index as u32 * element.size;
                    self.i(I::LocalGet(helpers.get(Scratch).as_u32()));
                    if let Ok(ty) = ScalarType::in_env(*element_ty, &self.env) {
                        self.read(value)?;
                        ty.store_at(&mut self.code, offset);
                    } else {
                        self.i(I::I32Const(offset as i32));
                        self.i(I::I32Add);
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
                    let base = self.address_base(destination)?;
                    if index == 1 {
                        self.i(I::LocalGet(helpers.get(Scratch).as_u32()));
                    } else {
                        self.i(I::I32Const(if index == 3 {
                            0
                        } else {
                            elements.len() as i32
                        }));
                    }
                    let field = layout
                        .static_field_offset(ProjectionIndex::from_index(index))
                        .ok_or("open array field offset")? as u32;
                    self.i(I::I32Store(memarg_at(2, base + field)));
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
                    if field.is_storage_flag {
                        let offset = self.frame_base(capture_offset + field.offset as u32);
                        self.read(argument)?;
                        self.i(I::I32Store8(memarg_at(0, offset)));
                    } else {
                        self.frame_address(capture_offset + field.offset as u32);
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
                if self.borrowed_static_strings.contains_key(&value) {
                    return Ok(());
                }
                if !self.storage.contains_key(&value) {
                    return Err("dynamic storage".into());
                }
                // The frame/local was reserved at entry; valid MIR never reads an absent lifetime.
                return Ok(());
            }
            Load => {
                let ty = self.pointee_type(&args[0])?;
                if let Ok(scalar) = scalar(&ty, &self.env) {
                    self.load_place(&args[0], scalar)?;
                } else {
                    self.copy_bytes(
                        &args[0],
                        &Value::Register(op.result_id().unwrap()),
                        self.size(&ty)?,
                    )?;
                    return Ok(());
                }
            }
            Store => {
                if self.borrowed_static_strings.contains_key(&args[1]) {
                    return Ok(());
                }
                // Store takes a materialized value, including a pointer; it must not dereference
                // a place operand as read() would. The MIR verifier checks this operand contract.
                if matches!(&args[0], Value::Register(id) if self.callable_values.contains(id) || self.subscript_values.contains(id))
                {
                    let offset = self.address_base(&args[1])?;
                    self.address(&args[0])?;
                    self.i(I::I64Load(memarg(2)));
                    self.i(I::I64Store(memarg_at(2, offset)));
                    return Ok(());
                }
                if let Value::Register(id) = &args[0]
                    && let Some(&word) = self.stored_variants.get(id)
                {
                    let offset = self.prepare_store(&args[1])?;
                    self.i(I::I32Const(word));
                    // Every variant shell begins with a canonical u32 tag, even when its
                    // destination also reserves payload bytes.
                    let tag = self
                        .pointee(&args[1])
                        .unwrap_or(ScalarType::native(NativeScalar::Int));
                    self.finish_store(&args[1], tag, offset);
                    return Ok(());
                }
                if matches!(&args[0], Value::Register(id) if self.variant_shells.contains(id)) {
                    let offset = self.address_base(&args[1])?;
                    self.address(&args[0])?;
                    self.i(I::I32Load(memarg(2)));
                    self.i(I::I32Store(memarg_at(2, offset)));
                    return Ok(());
                }
                let ty = self.pointee_type(&args[1])?;
                if let Ok(ty) = scalar(&ty, &self.env) {
                    let offset = self.prepare_store(&args[1])?;
                    self.value(&args[0])?;
                    self.finish_store(&args[1], ty, offset);
                } else if let Value::Constant(id) = &args[0]
                    && !self.storage.contains_key(&args[0])
                {
                    let constant = self.body.constant(*id);
                    self.initialize_literal(&args[1], constant.ty, &constant.representation, 0)?;
                } else {
                    self.copy_bytes(&args[0], &args[1], self.size(&ty)?)?;
                }
            }
            Memcpy | Move | MoveBytes { .. } => {
                let ty = self.pointee_type(&args[1])?;
                if let Some(witness) = layout_witness(op) {
                    self.dynamic_layout(witness)?;
                }
                if let Ok(ty) = scalar(&ty, &self.env) {
                    let offset = self.prepare_store(&args[1])?;
                    self.read(&args[0])?;
                    self.finish_store(&args[1], ty, offset);
                } else {
                    if !matches!(op.kind, MoveBytes { .. }) && layout_witness(op).is_none() {
                        self.copy_bytes(&args[0], &args[1], self.size(&ty)?)?;
                        return Ok(());
                    }
                    self.address(&args[1])?;
                    self.address(&args[0])?;
                    if matches!(op.kind, MoveBytes { .. }) {
                        self.read(&args[2])?;
                    } else {
                        self.i(I::LocalGet(self.helper_locals().get(DynamicSize).as_u32()));
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
                    self.i(I::LocalGet(self.helper_locals().get(DynamicSize).as_u32()));
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
                    self.i(I::LocalSet(helpers.get(Scratch).as_u32()));
                    self.dynamic_alloca();
                    self.i(I::Drop);
                } else {
                    self.scratch_address(ty);
                    self.i(I::LocalSet(helpers.get(DynamicBase).as_u32()));
                    self.i(I::I32Const(self.size(&MirType::Lowered(ty))? as i32));
                    self.i(I::LocalSet(helpers.get(DynamicSize).as_u32()));
                }
                self.i(I::LocalGet(helpers.get(DynamicBase).as_u32()));
                self.address(&args[0])?;
                self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&args[0])?;
                self.address(&args[1])?;
                self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&args[1])?;
                self.i(I::LocalGet(helpers.get(DynamicBase).as_u32()));
                self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                if layout_witness(op).is_some() {
                    self.i(I::LocalGet(helpers.get(Scratch).as_u32()));
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
                // Nesting was checked: this reclaims no open continuation or caller storage.
                self.value(&args[0])?;
                self.i(I::GlobalSet(Global::Stack as u32));
            }
            Variant { .. } if self.stored_variants.contains_key(&op.result_id().unwrap()) => {
                // Written by its store.
                return Ok(());
            }
            Variant { tag, storage, .. } => {
                let offset = self.address_base(&Value::Register(op.result_id().unwrap()))?;
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
                self.i(I::I32Store(memarg_at(2, offset)));
                // A shell initializes only the tag; physical MIR constructs its payload in place.
                return Ok(());
            }
            ExtractTag | ExtractPayloadIndirection => {
                let ty = self.pointee_type(&args[0])?;
                let tag_scalar = scalar(&ty, &self.env).is_ok_and(ScalarType::is_tag);
                if tag_scalar {
                    self.read(&args[0])?;
                } else {
                    self.address(&args[0])?;
                    self.i(I::I32Load(memarg(2)));
                }
                if tag_scalar && matches!(op.kind, ExtractTag) {
                    // Every case is inline: the representation bit is statically clear.
                } else if matches!(op.kind, ExtractTag) {
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
                    if ScalarType::in_env(ty, &self.env).is_ok() {
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
                self.call_operation(op, false, source)?
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
            if self.expressions.has_value(id) {
                return Ok(());
            }
            self.i(I::LocalSet(self.registers[&id].as_u32()));
            let value = Value::Register(id);
            if self.storage.contains_key(&value) {
                let role = self.roles.get(&value, self.body.constants()).unwrap();
                if let ValueRole::Materialized(ty) = &*role {
                    let ty = scalar(ty, &self.env)?;
                    let offset = self.address_base(&value)?;
                    self.i(I::LocalGet(self.registers[&id].as_u32()));
                    ty.store_at(&mut self.code, offset);
                }
            }
        }
        Ok(())
    }

    fn comparison_switch_predicate(
        &mut self,
        intrinsic: KnownCallee,
        call: &Operation,
        cases: &[(Ustr, BlockId)],
        default: BlockId,
        target: BlockId,
    ) -> Result<(), String> {
        // Every two-way partition of finite Ordering is a single ordered predicate.
        let mask =
            ["Less", "Equal", "Greater"]
                .into_iter()
                .enumerate()
                .fold(0, |mask, (bit, tag)| {
                    let arm = cases
                        .iter()
                        .find(|(case, _)| case.as_str() == tag)
                        .map_or(default, |(_, arm)| *arm);
                    mask | (u8::from(arm == target) << bit)
                });
        self.emit_comparison_predicate(intrinsic, call, mask)
    }

    fn emit_comparison_predicate(
        &mut self,
        intrinsic: KnownCallee,
        call: &Operation,
        mask: u8,
    ) -> Result<(), String> {
        let [_, left, right, _] = &*call.operands else {
            return Err("comparison call operands".into());
        };
        if mask == 0 || mask == 7 {
            self.i(I::I32Const(i32::from(mask == 7)));
            return Ok(());
        }
        self.read(left)?;
        self.read(right)?;
        self.i(match (intrinsic, mask) {
            (KnownCallee::IntCmp, 1) => I::I32LtS,
            (KnownCallee::IntCmp, 2) => I::I32Eq,
            (KnownCallee::IntCmp, 3) => I::I32LeS,
            (KnownCallee::IntCmp, 4) => I::I32GtS,
            (KnownCallee::IntCmp, 5) => I::I32Ne,
            (KnownCallee::IntCmp, 6) => I::I32GeS,
            (KnownCallee::FloatCmp, 1) => I::F64Lt,
            (KnownCallee::FloatCmp, 2) => I::F64Eq,
            (KnownCallee::FloatCmp, 3) => I::F64Le,
            (KnownCallee::FloatCmp, 4) => I::F64Gt,
            (KnownCallee::FloatCmp, 5) => I::F64Ne,
            (KnownCallee::FloatCmp, 6) => I::F64Ge,
            _ => unreachable!("checked comparison intrinsic and nonconstant case mask"),
        });
        Ok(())
    }

    fn comparison_predicate(
        &mut self,
        intrinsic: KnownCallee,
        call: &Operation,
        test: &Operation,
    ) -> Result<(), String> {
        let Value::Pattern(pattern) = &test.operands[1] else {
            return Err("comparison pattern".into());
        };
        let tag = pattern
            .as_variant_tag()
            .ok_or("comparison variant pattern")?;
        let mask = match tag.as_str() {
            "Less" => 1,
            "Equal" => 2,
            "Greater" => 4,
            _ => return Err("comparison pattern outside Ordering".into()),
        };
        self.emit_comparison_predicate(intrinsic, call, mask)
    }
}

/// Which constants are only ever the value a `store` writes.
fn constants_only_stored(body: &Function) -> Vec<bool> {
    let mut only_stored = vec![true; body.constants().len()];
    for block in body.blocks() {
        let block = body.block(block);
        let operations = block.operations().iter().flat_map(|operation| {
            operation
                .operands
                .iter()
                .enumerate()
                .map(move |(position, operand)| {
                    (
                        operand,
                        operation.kind == OperationKind::Store && position == 0,
                    )
                })
        });
        let terminator = block
            .terminator()
            .operands()
            .iter()
            .map(|operand| (operand, false));
        for (operand, stored) in operations.chain(terminator) {
            if let Value::Constant(id) = operand
                && !stored
            {
                only_stored[id.as_index()] = false;
            }
        }
    }
    only_stored
}

/// Borrow StaticStr constants and their single-initialization places at declared std readers.
/// Other uses retain private storage: an indirect call or derived alias could write through it.
/// The instance owns the immutable table for the whole invocation, including native calls.
fn borrowed_static_strings(
    body: &Function,
    env: ModuleEnv<'_>,
) -> (Vec<bool>, FxHashMap<ValueId, ConstantId>) {
    let mut borrowed: Vec<_> = body
        .constants()
        .iter()
        .map(|constant| {
            constant
                .representation
                .as_primitive_ty::<StaticStr>()
                .is_some()
        })
        .collect();
    if !borrowed.iter().any(|&borrowed| borrowed) {
        return (borrowed, FxHashMap::default());
    }
    // Record all candidates before checking uses, so cross-block uses cannot be missed.
    let mut places = FxHashMap::default();
    for block in body.blocks() {
        for operation in body.block(block).operations() {
            if matches!(operation.kind, OperationKind::Alloca { ty } if ty == static_str_type())
                && operation.operands.is_empty()
            {
                places.insert(operation.result_id().unwrap(), (block, None, true));
            }
        }
    }
    let named = |name| {
        env.module_by_id(STD_MODULE_ID)
            .and_then(|module| module.get_local_function_id(ustr(name)))
            .map(|function| FunctionId::new(STD_MODULE_ID, function))
    };
    // Call operands start with the callee: from_static reads its first input, while
    // push_static_str reads its second input, after the mutable destination string.
    let readers = [
        (named(STRING_FROM_STATIC_FUNCTION_NAME), 1),
        (named(STRING_PUSH_STATIC_STR_FUNCTION_NAME), 2),
    ];
    for block_id in body.blocks() {
        let block = body.block(block_id);
        let invoked = match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        for operation in block.operations().iter().chain(invoked) {
            for (position, operand) in operation.operands.iter().enumerate() {
                let read_only = operation.kind == OperationKind::Clear
                    || matches!(operation.kind, OperationKind::Call { .. })
                        && readers.iter().any(|&(reader, input)| {
                            position == input
                                && reader.is_some_and(|reader| {
                                    operation.operands.first() == Some(&Value::Function(reader))
                                })
                        });
                if let Value::Constant(id) = operand {
                    borrowed[id.as_index()] &=
                        read_only || operation.kind == OperationKind::Store && position == 0;
                }
                if let Value::Register(id) = operand
                    && let Some((block, initializer, valid)) = places.get_mut(id)
                {
                    if operation.kind == OperationKind::Clear {
                        continue;
                    }
                    if operation.kind == OperationKind::Store
                        && position == 1
                        && *block == block_id
                        && initializer.is_none()
                        && let Value::Constant(constant) = operation.operands[0]
                        && body
                            .constant(constant)
                            .representation
                            .as_primitive_ty::<StaticStr>()
                            .is_some()
                    {
                        *initializer = Some(constant);
                    } else {
                        *valid &= read_only && *block == block_id && initializer.is_some();
                    }
                }
            }
        }
        if invoked.is_none() {
            for operand in block.terminator().operands() {
                if let Value::Constant(id) = operand {
                    borrowed[id.as_index()] = false;
                }
                if let Value::Register(id) = operand
                    && let Some((_, _, valid)) = places.get_mut(id)
                {
                    *valid = false;
                }
            }
        }
    }
    (
        borrowed,
        places
            .into_iter()
            .filter_map(|(id, (_, initializer, valid))| {
                valid
                    .then_some(initializer)
                    .flatten()
                    .map(|constant| (id, constant))
            })
            .collect(),
    )
}

/// The `raw_float_to_float` calls whose operand is known to be finite where they execute.
///
/// Float speculation branches on `raw_float_is_finite(r)` into a block converting `r`. When that
/// block has no other predecessor and nothing rewrites `r` or the tested flag in between, the
/// conversion's fallback can never be taken. Anything else, such as a later pass merging the block
/// with another path, simply keeps the fallback: this is a local proof, never an assumption.
fn checked_float_conversions(
    body: &Function,
    analysis: &ExpressionAnalysis,
) -> FxHashSet<ExpressionSource> {
    let mut checked = FxHashSet::default();
    let mut predecessors: FxHashMap<BlockId, usize> = FxHashMap::default();
    for block in body.blocks() {
        for successor in body.block(block).terminator().successors() {
            *predecessors.entry(successor).or_default() += 1;
        }
    }
    let is = |source, known| analysis.intrinsic(source) == Some(known);
    for block_id in body.blocks() {
        let block = body.block(block_id);
        let TerminatorKind::CondBr {
            condition: Value::Register(condition),
            then_target,
            else_target,
        } = &block.terminator().kind
        else {
            continue;
        };
        if then_target == else_target || predecessors.get(then_target) != Some(&1) {
            continue;
        }
        let operations = block.operations();
        let Some(load) = operations
            .iter()
            .position(|operation| operation.result_id() == Some(*condition))
        else {
            continue;
        };
        if !matches!(operations[load].kind, OperationKind::Load) {
            continue;
        }
        let flag = &operations[load].operands[0];
        let Some(test) = (0..load)
            .rev()
            .find(|&index| operations[index].operands.contains(flag))
        else {
            continue;
        };
        if !is(
            ExpressionSource::from_index(block_id, test),
            KnownCallee::RawFloatIsFinite,
        ) || operations[test].operands.last() != Some(flag)
        {
            continue;
        }
        let tested = &operations[test].operands[1];
        let untouched = operations[test + 1..]
            .iter()
            .enumerate()
            .all(|(offset, operation)| {
                test + 1 + offset == load
                    || !(operation.operands.contains(tested) || operation.operands.contains(flag))
            });
        if !untouched {
            continue;
        }
        for (index, operation) in body.block(*then_target).operations().iter().enumerate() {
            if !operation.operands.contains(tested) {
                continue;
            }
            let source = ExpressionSource::from_index(*then_target, index);
            if !is(source, KnownCallee::RawFloatToFloat) || operation.operands[1] != *tested {
                break;
            }
            checked.insert(source);
        }
    }
    checked
}

/// Whether an operation can change the Wasm shadow-stack frontier beyond its own execution.
///
/// Statically sized MIR allocas already have fixed frame slots and calls reclaim their own frames.
/// Witnessed allocas and retained projection frames can raise the frontier, while ending a
/// projection can lower it. A `yield` is handled separately as a terminator because its caller may
/// allocate before resumption.
pub(in crate::wasm) fn operation_changes_stack_frontier(operation: &Operation) -> bool {
    matches!(operation.kind, OperationKind::Alloca { .. }) && !operation.operands.is_empty()
        || matches!(
            operation.kind,
            OperationKind::Project { .. } | OperationKind::EndProject
        )
}

pub(in crate::wasm) fn terminator_changes_stack_frontier(terminator: &TerminatorKind) -> bool {
    matches!(terminator, TerminatorKind::Yield { .. })
}

fn next_block(body: &Function, block: BlockId) -> Option<BlockId> {
    (block.as_index() + 1 < body.blocks().count())
        .then(|| BlockId::from_index(block.as_index() + 1))
}

/// Returns the block whose return is the last code of a structured body, so that it can fall
/// through the end of the function.
fn has_fallthrough_return(
    body: &Function,
    mode: BodyMode,
    control_flow: &ControlFlow,
) -> Option<BlockId> {
    let ControlFlow::Structured(items) = control_flow else {
        return None;
    };
    match items.last() {
        Some(Item::Node { block, .. })
            if matches!(mode, BodyMode::Normal)
                && matches!(body.block(*block).terminator().kind, TerminatorKind::Return) =>
        {
            Some(*block)
        }
        _ => None,
    }
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
