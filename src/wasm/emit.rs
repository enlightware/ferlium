// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Concrete physical MIR to core Wasm. A dispatcher preserves arbitrary MIR control flow.

use std::{iter, mem::offset_of};

use strum::{EnumIter, IntoEnumIterator};
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, ElementSection, Elements, EntityType, ExportKind,
    ExportSection, Function as WasmFunction, FunctionSection, GlobalSection, GlobalType,
    ImportSection, Instruction as I, MemArg, MemoryType, Module, RefType, TableSection, TableType,
    TypeSection, ValType,
};

use crate::{
    CompilerSession, FxHashMap, FxHashSet, Location,
    hir::{
        function::ArgConvention,
        native_functions::{NativeResult, NativeScalar},
        value::{LiteralValue, VariantPayloadStorage},
    },
    mir::{
        BasicBlock, BlockId, Function, Operation, OperationKind, ParameterId, ParameterKind, Value,
        ValueId,
        operation::OperationKindDiscriminant,
        physical::{DictionaryReference, program::ResolvedPhysicalProgram},
        role::{MirType, ValueRole, ValueRoles},
        terminator::TerminatorKind,
        value::ConstantId,
    },
    module::{
        DictionaryEntryEvidence, FunctionId, ModuleEnv, ProjectionIndex, TraitDictionaryId,
        TraitId, id::Id,
    },
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        logic::bool_type,
        math::{Float, float_type, int_type},
        string::StaticStr,
        value::{
            VALUE_ALIGN_ASSOC_CONST_INDEX, VALUE_SIZE_ASSOC_CONST_INDEX, product_layout_spec,
            structural_variant, value_layout_for_type, variant_payload_offset,
            variant_payload_storage_for_type,
        },
    },
    types::{
        effects::{EffType, Effect, PrimitiveEffect},
        mutability::MutType,
        r#trait::TraitDictionaryEntryIndex,
        r#type::{CallResultConvention, FnType, Type, TypeKind},
    },
    ustr,
};

use super::{
    IMPORT_MODULE, Imports, MEMORY_IMPORT,
    abi::{
        CallAbi, EvidenceTableSlotId, Parameter as ParameterTransport, ResultKind, WasmFunctionId,
        WasmLocalId, WasmTypeId, scalar_type,
    },
    evidence::{self, DictionaryDescriptor, ENVIRONMENT_OFFSET, ReachableEvidence},
    execution::{FailureCode, InvocationState},
};

/// A Ferlium type checked to belong to the emitter's supported scalar subset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ScalarType(Type);

impl ScalarType {
    pub(super) fn of(ty: Type) -> Result<Self, String> {
        [Type::unit(), bool_type(), int_type(), float_type()]
            .contains(&ty)
            .then_some(Self(ty))
            .ok_or_else(|| format!("unsupported Wasm storage type {ty:?}"))
    }

    fn unit() -> Self {
        Self(Type::unit())
    }

    fn native(scalar: NativeScalar) -> Self {
        Self(match scalar {
            NativeScalar::Bool => bool_type(),
            NativeScalar::Int => int_type(),
            NativeScalar::Float => float_type(),
        })
    }

    fn is_unit(self) -> bool {
        self.0 == Type::unit()
    }

    /// Unit has no native scalar transport.
    fn as_non_unit_native(self) -> Option<NativeScalar> {
        if self.is_unit() {
            None
        } else if self.0 == bool_type() {
            Some(NativeScalar::Bool)
        } else if self.0 == int_type() {
            Some(NativeScalar::Int)
        } else if self.0 == float_type() {
            Some(NativeScalar::Float)
        } else {
            unreachable!("checked scalar type")
        }
    }

    fn wasm(self) -> ValType {
        // Internal unit placeholder, never a direct ABI argument or result.
        self.as_non_unit_native().map_or(ValType::I32, scalar_type)
    }

    fn load(self, code: &mut WasmFunction) {
        let instruction = match self.as_non_unit_native() {
            None => {
                code.instruction(&I::Drop);
                I::I32Const(0)
            }
            Some(NativeScalar::Bool) => I::I32Load8U(memarg(0)),
            Some(NativeScalar::Int) => I::I32Load(memarg(2)),
            Some(NativeScalar::Float) => I::F64Load(memarg(3)),
        };
        code.instruction(&instruction);
    }

    fn store(self, code: &mut WasmFunction) {
        let instruction = match self.as_non_unit_native() {
            None => {
                code.instruction(&I::Drop);
                I::Drop
            }
            Some(NativeScalar::Bool) => I::I32Store8(memarg(0)),
            Some(NativeScalar::Int) => I::I32Store(memarg(2)),
            Some(NativeScalar::Float) => I::F64Store(memarg(3)),
        };
        code.instruction(&instruction);
    }

    fn equal(self) -> I<'static> {
        match self.as_non_unit_native() {
            None | Some(NativeScalar::Bool | NativeScalar::Int) => I::I32Eq,
            Some(NativeScalar::Float) => I::F64Eq,
        }
    }

    fn pointer() -> Self {
        // The wasm32 profile uses the same machine representation for pointers and native int.
        Self::native(NativeScalar::Int)
    }

    fn size(self) -> u32 {
        let data = self.0.data();
        let TypeKind::Native(native) = &*data else {
            unreachable!("checked scalar types are native")
        };
        native.bare_ty.value_size() as u32
    }
}

// Private invocation state: no extra parameters in the language ABI, and violations trap rather
// than masquerading as source failures. The host resets all state before each invocation.
#[derive(Clone, Copy, EnumIter)]
#[repr(u32)]
enum Global {
    Stack,
    End,
    Depth,
    DepthLimit,
    Fuel,
    Context,
    FuelEnabled,
}

fn value_transport(ty: Type) -> ParameterTransport {
    ScalarType::of(ty)
        .ok()
        .and_then(ScalarType::as_non_unit_native)
        .map_or(ParameterTransport::Indirect, |scalar| {
            ParameterTransport::Direct(scalar_type(scalar))
        })
}

fn script_abi(body: &Function) -> Result<CallAbi, String> {
    // Physical verification requires a unique trailing Return for Value, none for NoValue.
    // Thus MIR input indices also index abi.parameters; only the failure pointer shifts locals.
    if !matches!(
        body.result_convention(),
        CallResultConvention::Value
            | CallResultConvention::NoValue
            | CallResultConvention::ADDRESSOR_PLACE
    ) {
        return Err("scoped result convention".into());
    }
    let mut parameters = Vec::new();
    let mut result = None;
    for parameter in body.parameters() {
        match parameter.kind {
            ParameterKind::Return => result = Some(parameter.ty),
            ParameterKind::Parameter(mode) => {
                parameters.push(if mode == ArgConvention::Let {
                    value_transport(parameter.ty)
                } else {
                    ParameterTransport::Indirect
                });
            }
            ParameterKind::Owned => {
                parameters.push(ParameterTransport::Indirect);
            }
            ParameterKind::Dictionary => parameters.push(ParameterTransport::Indirect),
        }
    }
    let result_kind = match result {
        Some(_) if body.result_convention() == CallResultConvention::ADDRESSOR_PLACE => {
            ResultKind::Direct(ScalarType::pointer().wasm())
        }
        None => ResultKind::Unit,
        Some(ty) if ty == Type::unit() || ty == Type::never() => ResultKind::Unit,
        Some(ty) => {
            ScalarType::of(ty).map_or(ResultKind::Output, |ty| ResultKind::Direct(ty.wasm()))
        }
    };
    let fallible = body.blocks().any(|id| {
        matches!(
            body.block(id).terminator().kind,
            TerminatorKind::Invoke { .. }
        )
    });
    Ok(CallAbi {
        parameters,
        result: result_kind,
        fallible,
    })
}

pub(super) struct Emitted {
    pub bytes: Vec<u8>,
    pub strings: Box<[StaticStr]>,
    pub parameters: Vec<ScalarType>,
    pub result: ScalarType,
    pub evidence: evidence::Image,
}

fn dictionary_abi(
    env: ModuleEnv<'_>,
    trait_id: TraitId,
    entry: TraitDictionaryEntryIndex,
) -> Result<CallAbi, String> {
    let definition = env.trait_def(trait_id);
    let getter;
    let ty = if let Some((_, method)) = definition.methods.get(entry.as_index()) {
        &method.ty_scheme.ty
    } else {
        let constant = definition
            .associated_consts
            .get(entry.as_index() - definition.methods.len())
            .ok_or("missing dictionary entry declaration")?;
        getter = FnType::new_by_val([], constant.ty, EffType::empty());
        &getter
    };
    Ok(CallAbi {
        // The leading pointer borrows the complete dictionary reference, including self evidence.
        parameters: iter::once(ParameterTransport::Indirect)
            .chain(ty.args.iter().map(|arg| {
                if arg.mut_ty != MutType::constant() {
                    ParameterTransport::Indirect
                } else {
                    value_transport(arg.ty)
                }
            }))
            .collect(),
        result: ResultKind::Output,
        fallible: ty.effects.has_variables()
            || ty
                .effects
                .contains(Effect::Primitive(PrimitiveEffect::Fallible)),
    })
}

pub(super) fn emit(
    program: &ResolvedPhysicalProgram<'_>,
    entry: FunctionId,
    imports: &mut Imports,
    session: &CompilerSession,
) -> Result<Emitted, String> {
    let entry_body = program
        .function(entry)
        .ok_or_else(|| format!("missing script entry {entry:?}"))?;
    if !matches!(
        entry_body.result_convention(),
        CallResultConvention::Value | CallResultConvention::NoValue
    ) {
        return Err(diagnostic(
            entry,
            entry_body,
            "Wasm host binding requires a value result",
        ));
    }
    if entry_body.parameters().iter().any(|p| {
        !matches!(
            p.kind,
            ParameterKind::Return | ParameterKind::Parameter(ArgConvention::Let)
        )
    }) {
        return Err(diagnostic(
            entry,
            entry_body,
            "Wasm host binding requires by-value arguments",
        ));
    }
    // Preserve the public result type before selecting a NoValue implementation: an elided
    // zero-sized named product is not the unit type supported by the Rust binding.
    let result = entry_body
        .parameters()
        .iter()
        .find(|parameter| parameter.kind == ParameterKind::Return)
        .map(|parameter| ScalarType::of(parameter.ty))
        .transpose()?
        .unwrap_or_else(ScalarType::unit);
    let host_parameters = entry_body
        .parameters()
        .iter()
        .filter(|p| p.kind != ParameterKind::Return)
        .map(|p| ScalarType::of(p.ty))
        .collect::<Result<Vec<_>, _>>()?;
    let entry = program.direct_entry(entry);
    let env = session
        .modules()
        .env_for(session.expect_fresh_module(entry.module));
    let value_trait = env.expect_std_trait_id(VALUE_TRAIT_NAME);
    let definition = env.trait_def(value_trait);
    let layout_entries =
        [VALUE_SIZE_ASSOC_CONST_INDEX, VALUE_ALIGN_ASSOC_CONST_INDEX].map(|index| {
            (
                value_trait,
                definition.dictionary_associated_const_index(index),
            )
        });
    let mut pending = vec![entry];
    let mut seen = FxHashSet::default();
    let mut bodies = Vec::new();
    let mut natives = FxHashMap::default();
    let mut reachable = ReachableEvidence::default();
    let mut adapters = Vec::new();
    loop {
        if pending.is_empty() {
            reachable.discover_dispatches(program, |id, entry| {
                let definition = program.dictionary(id).unwrap();
                let target =
                    program.direct_entry(definition.entries()[entry.as_index()].function());
                if !seen.contains(&target) {
                    pending.push(target);
                }
                adapters.push((id, entry));
            });
        }
        let Some(id) = pending.pop() else {
            break;
        };
        if !seen.insert(id) {
            continue;
        }
        let Some(body) = program.function(id) else {
            let native = program
                .module(id.module)
                .and_then(|m| m.native_entry(id))
                .ok_or_else(|| format!("missing native entry {id:?}"))?;
            let index = imports
                .add_native(id, native)
                .map_err(|e| format!("native linkage {id:?}: {e:?}"))?;
            let abi = CallAbi::native(native.signature())
                .map_err(|reason| format!("native {id:?}: {reason}"))?;
            natives.insert(id, (index, abi));
            continue;
        };
        let signature = script_abi(body).map_err(|reason| diagnostic(id, body, &reason))?;
        for block in body.blocks() {
            let block = body.block(block);
            if !matches!(
                block.terminator().kind,
                TerminatorKind::Goto { .. }
                    | TerminatorKind::CondBr { .. }
                    | TerminatorKind::SwitchVariant { .. }
                    | TerminatorKind::Invoke { .. }
                    | TerminatorKind::PropagateError
                    | TerminatorKind::FailureDuringCleanup
                    | TerminatorKind::Return
                    | TerminatorKind::InvariantFailure { .. }
            ) {
                return Err(diagnostic(id, body, "unsupported terminator (yield)"));
            }
            for operation in operations(block) {
                for value in &operation.operands {
                    reachable.value(program, value)?;
                }
                match operation.kind {
                    OperationKind::BuildDictionary { definition, .. } => {
                        reachable.dictionary(definition)
                    }
                    OperationKind::DictEntry {
                        trait_id,
                        entry_index,
                        ..
                    } => reachable.entry(trait_id, entry_index),
                    OperationKind::Alloca { .. }
                    | OperationKind::Move
                    | OperationKind::Replace
                    | OperationKind::Variant { .. }
                        if layout_witness(operation).is_some() =>
                    {
                        for (trait_id, entry) in layout_entries {
                            reachable.entry(trait_id, entry);
                        }
                    }
                    _ => (),
                }
                if let Some(Value::Function(target)) = callee(operation) {
                    pending.push(program.direct_entry(*target));
                }
            }
        }
        bodies.push((id, body, signature));
    }
    let mut types = TypeSection::new();
    let mut import_section = ImportSection::new();
    import_section.import(
        IMPORT_MODULE,
        MEMORY_IMPORT,
        MemoryType {
            minimum: 0,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        },
    );
    for import in imports.functions() {
        let index = WasmTypeId::new(types.len());
        types.ty().function(
            import.parameters.iter().copied(),
            import.results.iter().copied(),
        );
        import_section.import(
            IMPORT_MODULE,
            &import.name,
            EntityType::Function(index.as_u32()),
        );
    }
    let callees: FxHashMap<_, _> = bodies
        .iter()
        .enumerate()
        .map(|(i, (id, _, sig))| {
            (
                *id,
                (
                    WasmFunctionId::from_index(imports.functions().len() + i),
                    sig,
                ),
            )
        })
        .chain(
            natives
                .iter()
                .map(|(&id, (index, abi))| (id, (*index, abi))),
        )
        .collect();
    let mut functions = FunctionSection::new();
    let mut code = CodeSection::new();
    let mut entry_abis = FxHashMap::default();
    for &(trait_id, entry) in &reachable.entries {
        let abi = dictionary_abi(env, trait_id, entry)?;
        let index = WasmTypeId::new(types.len());
        types.ty().function(abi.params(), abi.results());
        entry_abis.insert((trait_id, entry), (index, abi));
    }
    let table = adapters
        .iter()
        .enumerate()
        .map(|(index, &(id, entry))| {
            (
                (id, entry.as_index()),
                EvidenceTableSlotId::from_index(index + 1),
            )
        })
        .collect();
    let evidence = evidence::Image::build(program, &reachable, &table);
    let mut strings = StringLiterals::default();
    for (id, body, signature) in &bodies {
        functions.function(WasmTypeId::new(types.len()).as_u32());
        types.ty().function(signature.params(), signature.results());
        let emitted = Body::new(
            body,
            signature,
            &callees,
            program,
            session,
            session
                .modules()
                .env_for(session.expect_fresh_module(id.module)),
            imports,
            &mut strings,
            &evidence,
            &entry_abis,
            layout_entries,
        )
        .and_then(Body::emit)
        .map_err(|reason| diagnostic(*id, body, &reason))?;
        code.function(&emitted);
    }
    let adapter_base = WasmFunctionId::from_index(imports.functions().len() + bodies.len());
    for &(id, entry) in &adapters {
        let definition = program.dictionary(id).unwrap();
        let (ty, abi) = &entry_abis[&(definition.trait_id(), entry)];
        functions.function(ty.as_u32());
        code.function(&dictionary_adapter(
            program, id, entry, abi, &callees, session, imports,
        )?);
    }
    let mut tables = TableSection::new();
    tables.table(TableType {
        element_type: RefType::FUNCREF,
        table64: false,
        minimum: adapters.len() as u64 + 1,
        maximum: None,
        shared: false,
    });
    let mut elements = ElementSection::new();
    elements.active(
        None,
        &ConstExpr::i32_const(1),
        Elements::Functions(
            (0..adapters.len())
                .map(|index| WasmFunctionId::from_index(adapter_base.as_index() + index).as_u32())
                .collect::<Vec<_>>()
                .into(),
        ),
    );
    let mut globals = GlobalSection::new();
    let mut exports = ExportSection::new();
    for _ in Global::iter() {
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(0),
        );
    }
    let (entry_index, entry_signature) = &callees[&entry];
    let mut setup_index = WasmFunctionId::from_index(adapter_base.as_index() + adapters.len());
    // Only fallible entries need a host adapter: internal status returns become a Rust error
    // through the outer invocation boundary, without changing the scalar host C signature.
    if entry_signature.fallible {
        debug_assert_eq!(host_parameters.len(), entry_signature.parameters.len());
        functions.function(WasmTypeId::new(types.len()).as_u32());
        types.ty().function(
            host_parameters.iter().copied().map(ScalarType::wasm),
            result_as_wasm(result),
        );
        code.function(&entry_wrapper(*entry_index, entry_signature, result));
        exports.export("entry", ExportKind::Func, setup_index.as_u32());
        setup_index = WasmFunctionId::from_index(setup_index.as_index() + 1);
    } else {
        exports.export("entry", ExportKind::Func, entry_index.as_u32());
    }
    // Rust calls this setter directly at invocation boundaries. All state and diagnostics stay
    // in shared memory; no language values or per-call state are passed through JavaScript.
    functions.function(WasmTypeId::new(types.len()).as_u32());
    types.ty().function([ValType::I32], []);
    code.function(&setup());
    exports.export("setup", ExportKind::Func, setup_index.as_u32());
    let mut module = Module::new();
    module
        .section(&types)
        .section(&import_section)
        .section(&functions)
        .section(&tables)
        .section(&globals)
        .section(&exports)
        .section(&elements)
        .section(&code);
    Ok(Emitted {
        bytes: module.finish(),
        parameters: host_parameters,
        strings: strings.values.into_boxed_slice(),
        result,
        evidence,
    })
}

fn operations(block: &BasicBlock) -> impl Iterator<Item = &Operation> {
    block
        .operations()
        .iter()
        .chain(match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        })
}

fn layout_witness(op: &Operation) -> Option<&Value> {
    match op.kind {
        OperationKind::Alloca { .. } if !op.operands.is_empty() => op.operands.first(),
        OperationKind::Move | OperationKind::Replace if op.operands.len() == 3 => {
            op.operands.last()
        }
        OperationKind::Variant {
            has_layout_witness: true,
            ..
        } => op.operands.last(),
        _ => None,
    }
}

/// Bridge the declaration-fixed dictionary ABI to the implementation's direct ABI.
fn dictionary_adapter(
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
struct NativeOptionalResultAdapter {
    some_tag: u32,
    none_tag: u32,
    storage: VariantPayloadStorage,
    size: u32,
    align: u32,
    field: u32,
    payload_size: u32,
}

impl NativeOptionalResultAdapter {
    fn new(
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

    fn emit(
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

fn emit_failure(code: &mut WasmFunction, failure: FailureCode) {
    check_context(code);
    store_failure_and_trap(code, failure);
}

fn check_context(code: &mut WasmFunction) {
    // An exported entry can be reached without an invocation; never write through a null context.
    code.instruction(&I::GlobalGet(Global::Context as u32));
    code.instruction(&I::I32Eqz);
    code.instruction(&I::If(BlockType::Empty));
    code.instruction(&I::Unreachable);
    code.instruction(&I::End);
}

fn store_failure_and_trap(code: &mut WasmFunction, failure: FailureCode) {
    code.instruction(&I::GlobalGet(Global::Context as u32));
    code.instruction(&I::I32Const(failure as i32));
    code.instruction(&I::I32Store(MemArg {
        offset: offset_of!(InvocationState, failure) as u64,
        ..memarg(2)
    }));
    code.instruction(&I::Unreachable);
}

fn context_pointer(code: &mut WasmFunction, offset: usize) {
    code.instruction(&I::GlobalGet(Global::Context as u32));
    code.instruction(&I::I32Load(MemArg {
        offset: offset as u64,
        ..memarg(2)
    }));
}

fn frame_address(code: &mut WasmFunction, frame: WasmLocalId, offset: u32) {
    code.instruction(&I::LocalGet(frame.as_u32()));
    code.instruction(&I::I32Const(offset as i32));
    code.instruction(&I::I32Add);
}

fn frame_bytes(size: u32) -> Result<u32, String> {
    Ok(size.max(1).checked_add(7).ok_or("frame size overflow")? & !7)
}

fn enter_frame(code: &mut WasmFunction, frame: WasmLocalId, size: u32) {
    // Check before addition, so a large frame cannot wrap the linear-memory stack pointer.
    code.instruction(&I::GlobalGet(Global::Stack as u32));
    code.instruction(&I::LocalSet(frame.as_u32()));
    code.instruction(&I::GlobalGet(Global::End as u32));
    code.instruction(&I::LocalGet(frame.as_u32()));
    code.instruction(&I::I32Sub);
    code.instruction(&I::I32Const(size as i32));
    code.instruction(&I::I32LtU);
    code.instruction(&I::If(BlockType::Empty));
    emit_failure(code, FailureCode::StackCapacity);
    code.instruction(&I::End);
    frame_address(code, frame, size);
    code.instruction(&I::GlobalSet(Global::Stack as u32));
}

fn leave_frame(code: &mut WasmFunction, frame: WasmLocalId) {
    code.instruction(&I::LocalGet(frame.as_u32()));
    code.instruction(&I::GlobalSet(Global::Stack as u32));
}

fn callee(op: &Operation) -> Option<&Value> {
    match &op.kind {
        OperationKind::Call { .. } | OperationKind::Project { .. } => Some(&op.operands[0]),
        OperationKind::Clone { .. } => Some(&op.operands[2]),
        OperationKind::Drop { .. } | OperationKind::DropInitialized { .. } => Some(&op.operands[1]),
        _ => None,
    }
}

fn result_as_wasm(result: ScalarType) -> Option<ValType> {
    (!result.is_unit()).then(|| result.wasm())
}

fn entry_wrapper(index: WasmFunctionId, signature: &CallAbi, result: ScalarType) -> WasmFunction {
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

fn setup() -> WasmFunction {
    let mut code = WasmFunction::new([]);
    for global in Global::iter() {
        let offset = match global {
            Global::Context => {
                code.instruction(&I::LocalGet(0));
                code.instruction(&I::GlobalSet(global as u32));
                continue;
            }
            Global::Depth => {
                code.instruction(&I::I32Const(0));
                code.instruction(&I::GlobalSet(global as u32));
                continue;
            }
            Global::Stack => offset_of!(InvocationState, stack),
            Global::End => offset_of!(InvocationState, end),
            Global::DepthLimit => offset_of!(InvocationState, depth_limit),
            Global::Fuel => offset_of!(InvocationState, fuel),
            Global::FuelEnabled => offset_of!(InvocationState, fuel_enabled),
        };
        code.instruction(&I::LocalGet(0));
        code.instruction(&I::If(BlockType::Result(ValType::I32)));
        code.instruction(&I::LocalGet(0));
        code.instruction(&I::I32Load(MemArg {
            offset: offset as u64,
            ..memarg(2)
        }));
        code.instruction(&I::Else);
        code.instruction(&I::I32Const(0));
        code.instruction(&I::End);
        code.instruction(&I::GlobalSet(global as u32));
    }
    code.instruction(&I::End);
    code
}

fn diagnostic(id: FunctionId, body: &Function, reason: &str) -> String {
    format!("Wasm generation in {} ({id:?}): {reason}", body.name)
}

#[derive(Clone, Copy)]
enum Storage {
    Local(WasmLocalId),
    /// Byte offset from the function's frame base in linear memory.
    Stack(u32),
}

#[derive(Default)]
struct StringLiterals {
    values: Vec<StaticStr>,
    indices: FxHashMap<StaticStr, usize>,
}

impl StringLiterals {
    fn intern(&mut self, text: StaticStr) -> usize {
        *self.indices.entry(text).or_insert_with(|| {
            let index = self.values.len();
            self.values.push(text);
            index
        })
    }
}

#[derive(Clone, Copy)]
struct LayoutLocals {
    dictionary: WasmLocalId,
    table: WasmLocalId,
    output: WasmLocalId,
}

struct Body<'a> {
    body: &'a Function,
    signature: &'a CallAbi,
    roles: ValueRoles,
    env: ModuleEnv<'a>,
    imports: &'a Imports,
    strings: &'a mut StringLiterals,
    evidence: &'a evidence::Image,
    entry_abis: &'a FxHashMap<(TraitId, TraitDictionaryEntryIndex), (WasmTypeId, CallAbi)>,
    layout_entries: [(TraitId, TraitDictionaryEntryIndex); 2],
    selections: FxHashMap<ValueId, (TraitId, TraitDictionaryEntryIndex)>,
    owned_evidence: Vec<ValueId>,
    capture_slots: FxHashMap<ValueId, u32>,
    variant_shells: FxHashSet<ValueId>,
    layout_slot: Option<u32>,
    dynamic_size: WasmLocalId,
    dynamic_align: WasmLocalId,
    dynamic_base: WasmLocalId,
    allocation_end: WasmLocalId,
    evidence_base: Option<WasmLocalId>,
    layout_locals: Option<LayoutLocals>,
    pending_failure: WasmLocalId,
    scratch: WasmLocalId,
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
    code: WasmFunction,
}

impl<'a> Body<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
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
            selections: FxHashMap::default(),
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
                    match operation.kind {
                        OperationKind::BuildDictionary { definition, .. } => {
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
                        OperationKind::DictEntry {
                            trait_id,
                            entry_index,
                            ..
                        } => {
                            this.slot(
                                Value::Register(id),
                                size_of::<DictionaryReference>() as u32,
                            )?;
                            this.owned_evidence.push(id);
                            this.selections.insert(id, (trait_id, entry_index));
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

    fn pointee_type(&self, value: &Value) -> Result<MirType, String> {
        self.roles
            .get(value, self.body.constants())
            .and_then(|role| role.place_pointee_type())
            .ok_or_else(|| "expected place".into())
    }

    fn context_pointer(&mut self, offset: usize) {
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
        // Descriptor and entry-table addresses are image-relative; environments are relocated.
        self.i(I::I32Load(memarg(2)));
        self.i(I::I32Const(2));
        self.i(I::I32Shl);
        self.context_pointer(offset_of!(InvocationState, evidence));
        self.i(I::LocalTee(evidence_base.as_u32()));
        self.i(I::I32Add);
        self.i(I::I32Load(memarg(2)));
        self.i(I::LocalGet(evidence_base.as_u32()));
        self.i(I::I32Add);
        self.i(I::I32Load(MemArg {
            offset: offset_of!(DictionaryDescriptor, entries) as u64,
            ..memarg(2)
        }));
        self.i(I::LocalGet(evidence_base.as_u32()));
        self.i(I::I32Add);
    }

    fn dynamic_layout(&mut self, dictionary: &Value) -> Result<(), String> {
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

    /// Reserve witnessed frame bytes, doing the alignment and extent arithmetic without wrapping.
    fn dynamic_alloca(&mut self) {
        // alignment = max(requested_alignment, 8), preserving alignment for callees' fixed frames.
        self.i(I::LocalGet(self.dynamic_align.as_u32()));
        self.i(I::I32Const(8));
        self.i(I::LocalGet(self.dynamic_align.as_u32()));
        self.i(I::I32Const(8));
        self.i(I::I32GtU);
        self.i(I::Select);
        self.i(I::LocalSet(self.dynamic_align.as_u32()));
        // base = align_up(stack_pointer, alignment).
        self.i(I::GlobalGet(Global::Stack as u32));
        self.i(I::I64ExtendI32U);
        self.i(I::LocalGet(self.dynamic_align.as_u32()));
        self.i(I::I64ExtendI32U);
        self.i(I::I64Const(1));
        self.i(I::I64Sub);
        self.i(I::I64Add);
        self.i(I::I64Const(0));
        self.i(I::LocalGet(self.dynamic_align.as_u32()));
        self.i(I::I64ExtendI32U);
        self.i(I::I64Sub);
        self.i(I::I64And);
        self.i(I::LocalTee(self.allocation_end.as_u32()));
        self.i(I::I32WrapI64);
        self.i(I::LocalSet(self.dynamic_base.as_u32()));
        // end = align_up(base + max(size, 1), 8), reserving a distinct address even for zero size.
        self.i(I::LocalGet(self.allocation_end.as_u32()));
        self.i(I::LocalGet(self.dynamic_size.as_u32()));
        self.i(I::I32Const(1));
        self.i(I::LocalGet(self.dynamic_size.as_u32()));
        self.i(I::Select);
        self.i(I::I64ExtendI32U);
        self.i(I::I64Add);
        self.i(I::I64Const(7));
        self.i(I::I64Add);
        self.i(I::I64Const(-8));
        self.i(I::I64And);
        self.i(I::LocalTee(self.allocation_end.as_u32()));
        // if end > stack_limit: fail(StackCapacity).
        self.i(I::GlobalGet(Global::End as u32));
        self.i(I::I64ExtendI32U);
        self.i(I::I64GtU);
        self.i(I::If(BlockType::Empty));
        self.fail(FailureCode::StackCapacity);
        self.i(I::End);
        // stack_pointer = end.
        self.i(I::LocalGet(self.allocation_end.as_u32()));
        self.i(I::I32WrapI64);
        self.i(I::GlobalSet(Global::Stack as u32));
        // Leave base on the operand stack as the allocation result.
        self.i(I::LocalGet(self.dynamic_base.as_u32()));
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

    fn call_status(&mut self, invoked: bool, fallible: bool) {
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

    fn i(&mut self, instruction: I<'_>) {
        self.code.instruction(&instruction);
    }

    fn fail(&mut self, code: FailureCode) {
        // A host can reach the exported entry without installing an invocation. Trap without
        // touching low linear memory when there is no diagnostic destination.
        emit_failure(&mut self.code, code);
    }

    fn address(&mut self, value: &Value) -> Result<(), String> {
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

    fn value(&mut self, value: &Value) -> Result<(), String> {
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

    fn read(&mut self, value: &Value) -> Result<ScalarType, String> {
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

    fn emit(mut self) -> Result<WasmFunction, String> {
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
        match &op.kind {
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
                    self.program.descriptor_index(*definition).unwrap() as i32,
                ));
                self.frame_address(capture_offset);
                self.address(&result)?;
                self.i(I::Call(
                    self.imports.function_index("build_evidence").as_u32(),
                ));
                return Ok(());
            }
            DictEntry { .. } => {
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

fn scalar(ty: &MirType) -> Result<ScalarType, String> {
    match ty {
        MirType::Pointer(_) => Ok(ScalarType::pointer()),
        MirType::Lowered(ty) => ScalarType::of(*ty),
    }
}

fn memarg(align: u32) -> MemArg {
    MemArg {
        offset: 0,
        align,
        memory_index: 0,
    }
}
