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
        math::Float,
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
    abi::{CallAbi, Parameter as ParameterTransport, ResultKind, scalar_type},
    evidence::{self, DictionaryDescriptor, ENVIRONMENT_OFFSET, ReachableEvidence},
    execution::{FailureCode, InvocationState},
};

/// A Ferlium type checked to belong to the emitter's supported scalar subset.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ScalarType(Type);

impl ScalarType {
    pub(super) fn of(ty: Type) -> Result<Self, String> {
        if [
            Type::unit(),
            Type::primitive::<bool>(),
            Type::primitive::<isize>(),
            Type::primitive::<Float>(),
        ]
        .contains(&ty)
        {
            Ok(Self(ty))
        } else {
            Err(format!("unsupported Wasm storage type {ty:?}"))
        }
    }

    fn unit() -> Self {
        Self(Type::unit())
    }

    fn native(scalar: NativeScalar) -> Self {
        Self(match scalar {
            NativeScalar::Bool => Type::primitive::<bool>(),
            NativeScalar::Int => Type::primitive::<isize>(),
            NativeScalar::Float => Type::primitive::<Float>(),
        })
    }

    fn is<T: 'static>(self) -> bool {
        self.0 == Type::primitive::<T>()
    }

    fn wasm(self) -> ValType {
        if self.is::<Float>() {
            scalar_type(NativeScalar::Float)
        } else if self.is::<bool>() {
            scalar_type(NativeScalar::Bool)
        } else if self.is::<isize>() {
            scalar_type(NativeScalar::Int)
        } else if self.is::<()>() {
            ValType::I32 // Internal unit placeholder, never a direct ABI argument or result.
        } else {
            unreachable!("missing scalar transport mapping")
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
                    ScalarType::of(parameter.ty)
                        .ok()
                        .filter(|ty| !ty.is::<()>())
                        .map_or(ParameterTransport::Indirect, |ty| {
                            ParameterTransport::Direct(ty.wasm())
                        })
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
                    ScalarType::of(arg.ty)
                        .ok()
                        .filter(|ty| !ty.is::<()>())
                        .map_or(ParameterTransport::Indirect, |ty| {
                            ParameterTransport::Direct(ty.wasm())
                        })
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
    loop {
        if pending.is_empty() {
            for &id in &reachable.dictionaries {
                let definition = program.dictionary(id).unwrap();
                for &(trait_id, entry) in &reachable.entries {
                    if definition.trait_id() == trait_id {
                        let target =
                            program.direct_entry(definition.entries()[entry.as_index()].function());
                        if !seen.contains(&target) {
                            pending.push(target);
                        }
                    }
                }
            }
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
                    pending.push(program.direct_entry(target));
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
        let index = types.len();
        types.ty().function(
            import.parameters.iter().copied(),
            import.results.iter().copied(),
        );
        import_section.import(IMPORT_MODULE, &import.name, EntityType::Function(index));
    }
    let indices: FxHashMap<_, _> = bodies
        .iter()
        .enumerate()
        .map(|(i, (id, _, sig))| {
            (
                *id,
                (imports.functions().len() as u32 + i as u32, sig.clone()),
            )
        })
        .collect();
    let callees: FxHashMap<_, _> = indices
        .iter()
        .map(|(id, (index, signature))| (*id, (*index, signature.clone())))
        .chain(natives)
        .collect();
    let mut functions = FunctionSection::new();
    let mut code = CodeSection::new();
    let mut table = FxHashMap::default();
    let mut adapters = Vec::new();
    let mut entry_abis = FxHashMap::default();
    for &(trait_id, entry) in &reachable.entries {
        let abi = dictionary_abi(env, trait_id, entry)?;
        let index = types.len();
        types.ty().function(abi.params(), abi.results());
        entry_abis.insert((trait_id, entry), (index, abi));
    }
    for &id in &reachable.dictionaries {
        let definition = program.dictionary(id).unwrap();
        for &(trait_id, entry) in &reachable.entries {
            if trait_id == definition.trait_id() {
                table.insert((id, entry.as_index()), adapters.len() as u32 + 1);
                adapters.push((id, entry));
            }
        }
    }
    let evidence = evidence::Image::build(program, &reachable, &table);
    let mut strings = Vec::new();
    for (id, body, signature) in &bodies {
        functions.function(types.len());
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
    let adapter_base = imports.functions().len() as u32 + bodies.len() as u32;
    for &(id, entry) in &adapters {
        let definition = program.dictionary(id).unwrap();
        let (ty, abi) = &entry_abis[&(definition.trait_id(), entry)];
        functions.function(*ty);
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
            (adapter_base..adapter_base + adapters.len() as u32)
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
    let entry_signature = &indices[&entry].1;
    let mut setup_index = adapter_base + adapters.len() as u32;
    // Only fallible entries need a host adapter: internal status returns become a Rust error
    // through the outer invocation boundary, without changing the scalar host C signature.
    if entry_signature.fallible {
        debug_assert_eq!(host_parameters.len(), entry_signature.parameters.len());
        functions.function(types.len());
        types.ty().function(
            host_parameters.iter().map(|ty| {
                if ty.is::<()>() {
                    ValType::I32
                } else {
                    ty.wasm()
                }
            }),
            result_as_wasm(result),
        );
        code.function(&entry_wrapper(indices[&entry].0, entry_signature, result));
        exports.export("entry", ExportKind::Func, setup_index);
        setup_index += 1;
    } else {
        exports.export("entry", ExportKind::Func, indices[&entry].0);
    }
    // Rust calls this setter directly at invocation boundaries. All state and diagnostics stay
    // in shared memory; no language values or per-call state are passed through JavaScript.
    functions.function(types.len());
    types.ty().function([ValType::I32], []);
    code.function(&setup());
    exports.export("setup", ExportKind::Func, setup_index);
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
        strings: strings.into_boxed_slice(),
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
#[allow(clippy::too_many_arguments)]
fn dictionary_adapter(
    program: &ResolvedPhysicalProgram<'_>,
    dictionary: TraitDictionaryId,
    entry: TraitDictionaryEntryIndex,
    abi: &CallAbi,
    callees: &FxHashMap<FunctionId, (u32, CallAbi)>,
    session: &CompilerSession,
    imports: &Imports,
) -> Result<WasmFunction, String> {
    let definition = program.dictionary(dictionary).unwrap();
    let entry = &definition.entries()[entry.as_index()];
    let target = program.direct_entry(entry.function());
    let (index, direct) = &callees[&target];
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
        let native = program
            .module(target.module)
            .unwrap()
            .native_entry(target)
            .unwrap()
            .signature();
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
        let NativeResult::Optional { payload, .. } = program
            .module(target.module)
            .unwrap()
            .native_entry(target)
            .unwrap()
            .signature()
            .result
        else {
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
        .map_or(0, |adapter| (adapter.payload_size.max(1) + 7) & !7);
    let mut spills = FxHashMap::default();
    for (i, canonical) in abi.parameters[1..].iter().enumerate() {
        if matches!(canonical, ParameterTransport::Direct(_))
            && direct.parameters[captures.len() + i] == ParameterTransport::Indirect
        {
            spills.insert(i, frame_size);
            frame_size = frame_size
                .checked_add(8)
                .ok_or("dictionary adapter frame overflow")?;
        }
    }
    let frame = abi.parameter_count() as u32;
    let scratch = frame + 1;
    let mut code = WasmFunction::new([(if frame_size == 0 { 0 } else { 2 }, ValType::I32)]);
    if frame_size != 0 {
        code.instruction(&I::GlobalGet(Global::Stack as u32));
        code.instruction(&I::LocalSet(frame));
        code.instruction(&I::GlobalGet(Global::End as u32));
        code.instruction(&I::LocalGet(frame));
        code.instruction(&I::I32Sub);
        code.instruction(&I::I32Const(frame_size as i32));
        code.instruction(&I::I32LtU);
        code.instruction(&I::If(BlockType::Empty));
        emit_failure(&mut code, FailureCode::StackCapacity);
        code.instruction(&I::End);
        code.instruction(&I::LocalGet(frame));
        code.instruction(&I::I32Const(frame_size as i32));
        code.instruction(&I::I32Add);
        code.instruction(&I::GlobalSet(Global::Stack as u32));
        for (i, _) in abi.parameters[1..].iter().enumerate() {
            if let Some(offset) = spills.get(&i) {
                code.instruction(&I::LocalGet(frame));
                code.instruction(&I::I32Const(*offset as i32));
                code.instruction(&I::I32Add);
                code.instruction(&I::LocalGet(abi.input_local(i as u32 + 1)));
                code.instruction(&scalar_store(ScalarType::of(
                    input_types[captures.len() + i],
                )?));
            }
        }
    }
    if !direct.fallible && matches!(direct.result, ResultKind::Direct(_)) {
        code.instruction(&I::LocalGet(abi.output_local()));
    }
    if direct.fallible {
        if abi.fallible {
            code.instruction(&I::LocalGet(0));
        } else {
            code.instruction(&I::GlobalGet(Global::Context as u32));
            code.instruction(&I::I32Load(MemArg {
                offset: offset_of!(InvocationState, native_failure) as u64,
                ..memarg(2)
            }));
        }
    }
    for mapping in captures {
        code.instruction(&I::LocalGet(abi.input_local(0)));
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
        if let Some(offset) = spills.get(&i) {
            code.instruction(&I::LocalGet(frame));
            code.instruction(&I::I32Const(*offset as i32));
            code.instruction(&I::I32Add);
            continue;
        }
        code.instruction(&I::LocalGet(abi.input_local(i as u32 + 1)));
        if let (ParameterTransport::Indirect, ParameterTransport::Direct(_)) = (*canonical, actual)
        {
            code.instruction(&scalar_load(ScalarType::of(
                input_types[captures.len() + i],
            )?));
        }
    }
    if direct.output() {
        code.instruction(&I::LocalGet(if optional.is_some() {
            frame
        } else {
            abi.output_local()
        }));
    }
    code.instruction(&I::Call(*index));
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
            code.instruction(&scalar_store(ScalarType::of(result_ty)?));
        }
        if abi.fallible {
            code.instruction(&I::I32Const(0));
        }
    }
    if frame_size != 0 {
        code.instruction(&I::LocalGet(frame));
        code.instruction(&I::GlobalSet(Global::Stack as u32));
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
        output: u32,
        payload: u32,
        scratch: u32,
        allocate: u32,
    ) {
        code.instruction(&I::If(BlockType::Empty)); // Native presence, not a failure status.
        code.instruction(&I::LocalGet(output));
        code.instruction(&I::I32Const(self.some_tag as i32));
        code.instruction(&I::I32Store(memarg(2)));
        code.instruction(&I::LocalGet(output));
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
            code.instruction(&I::Call(allocate));
            code.instruction(&I::LocalTee(scratch));
            code.instruction(&I::I32Store(memarg(2)));
            code.instruction(&I::LocalGet(scratch));
        }
        code.instruction(&I::I32Const(self.field as i32));
        code.instruction(&I::I32Add);
        code.instruction(&I::LocalGet(payload));
        code.instruction(&I::I32Const(self.payload_size as i32));
        code.instruction(&I::MemoryCopy {
            src_mem: 0,
            dst_mem: 0,
        });
        code.instruction(&I::Else);
        code.instruction(&I::LocalGet(output));
        code.instruction(&I::I32Const(self.none_tag as i32));
        code.instruction(&I::I32Store(memarg(2)));
        code.instruction(&I::End);
    }
}

fn emit_failure(code: &mut WasmFunction, failure: FailureCode) {
    code.instruction(&I::GlobalGet(Global::Context as u32));
    code.instruction(&I::I32Eqz);
    code.instruction(&I::If(BlockType::Empty));
    code.instruction(&I::Unreachable);
    code.instruction(&I::End);
    code.instruction(&I::GlobalGet(Global::Context as u32));
    code.instruction(&I::I32Const(failure as i32));
    code.instruction(&I::I32Store(MemArg {
        offset: offset_of!(InvocationState, failure) as u64,
        ..memarg(2)
    }));
    code.instruction(&I::Unreachable);
}

fn scalar_load(ty: ScalarType) -> I<'static> {
    if ty.is::<bool>() {
        I::I32Load8U(memarg(0))
    } else if ty.is::<Float>() {
        I::F64Load(memarg(3))
    } else if ty.is::<isize>() {
        I::I32Load(memarg(2))
    } else {
        unreachable!("non-scalar transport")
    }
}

fn scalar_store(ty: ScalarType) -> I<'static> {
    if ty.is::<bool>() {
        I::I32Store8(memarg(0))
    } else if ty.is::<Float>() {
        I::F64Store(memarg(3))
    } else if ty.is::<isize>() {
        I::I32Store(memarg(2))
    } else {
        unreachable!("non-scalar transport")
    }
}

fn callee(op: &Operation) -> Option<Value> {
    match &op.kind {
        OperationKind::Call { .. } | OperationKind::Project { .. } => Some(op.operands[0].clone()),
        OperationKind::Clone { .. } => Some(op.operands[2].clone()),
        OperationKind::Drop { .. } | OperationKind::DropInitialized { .. } => {
            Some(op.operands[1].clone())
        }
        _ => None,
    }
}

fn result_as_wasm(result: ScalarType) -> Option<ValType> {
    (!result.is::<()>()).then(|| result.wasm())
}

fn entry_wrapper(index: u32, signature: &CallAbi, result: ScalarType) -> WasmFunction {
    debug_assert!(signature.fallible);
    let frame = signature.parameters.len() as u32;
    let mut code = WasmFunction::new([(1, ValType::I32)]);
    code.instruction(&I::GlobalGet(Global::Context as u32));
    code.instruction(&I::I32Eqz);
    code.instruction(&I::If(BlockType::Empty));
    code.instruction(&I::Unreachable);
    code.instruction(&I::End);
    // The scalar host result needs at most eight aligned bytes, reserved before the callee.
    code.instruction(&I::GlobalGet(Global::Stack as u32));
    code.instruction(&I::LocalSet(frame));
    code.instruction(&I::GlobalGet(Global::End as u32));
    code.instruction(&I::LocalGet(frame));
    code.instruction(&I::I32Sub);
    code.instruction(&I::I32Const(8));
    code.instruction(&I::I32LtU);
    code.instruction(&I::If(BlockType::Empty));
    code.instruction(&I::GlobalGet(Global::Context as u32));
    code.instruction(&I::I32Const(FailureCode::StackCapacity as i32));
    code.instruction(&I::I32Store(MemArg {
        offset: offset_of!(InvocationState, failure) as u64,
        ..memarg(2)
    }));
    code.instruction(&I::Unreachable);
    code.instruction(&I::End);
    code.instruction(&I::LocalGet(frame));
    code.instruction(&I::I32Const(8));
    code.instruction(&I::I32Add);
    code.instruction(&I::GlobalSet(Global::Stack as u32));
    code.instruction(&I::GlobalGet(Global::Context as u32));
    code.instruction(&I::I32Load(MemArg {
        offset: offset_of!(InvocationState, native_failure) as u64,
        ..memarg(2)
    }));
    for i in 0..signature.parameters.len() as u32 {
        code.instruction(&I::LocalGet(i));
    }
    if signature.output() {
        code.instruction(&I::LocalGet(frame));
    }
    code.instruction(&I::Call(index));
    code.instruction(&I::LocalGet(frame));
    code.instruction(&I::GlobalSet(Global::Stack as u32));
    code.instruction(&I::If(BlockType::Empty));
    code.instruction(&I::GlobalGet(Global::Context as u32));
    code.instruction(&I::I32Const(FailureCode::Source as i32));
    code.instruction(&I::I32Store(MemArg {
        offset: offset_of!(InvocationState, failure) as u64,
        ..memarg(2)
    }));
    code.instruction(&I::Unreachable);
    code.instruction(&I::End);
    if !result.is::<()>() {
        code.instruction(&I::LocalGet(frame));
        code.instruction(&if result.is::<Float>() {
            I::F64Load(memarg(3))
        } else if result.is::<bool>() {
            I::I32Load8U(memarg(0))
        } else {
            I::I32Load(memarg(2))
        });
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
    Local(u32),
    Stack(u32),
}

struct Body<'a> {
    body: &'a Function,
    signature: &'a CallAbi,
    roles: ValueRoles,
    env: ModuleEnv<'a>,
    imports: &'a Imports,
    strings: &'a mut Vec<StaticStr>,
    evidence: &'a evidence::Image,
    entry_abis: &'a FxHashMap<(TraitId, TraitDictionaryEntryIndex), (u32, CallAbi)>,
    layout_entries: [(TraitId, TraitDictionaryEntryIndex); 2],
    selections: FxHashMap<ValueId, (TraitId, TraitDictionaryEntryIndex)>,
    owned_evidence: Vec<Value>,
    capture_slots: FxHashMap<ValueId, u32>,
    variant_shells: FxHashSet<ValueId>,
    layout_slot: u32,
    dynamic_size: u32,
    dynamic_align: u32,
    dynamic_base: u32,
    allocation_end: u32,
    pending_failure: u32,
    scratch: u32,
    scratch_slots: FxHashMap<Type, u32>,
    callees: &'a FxHashMap<FunctionId, (u32, CallAbi)>,
    program: &'a ResolvedPhysicalProgram<'a>,
    session: &'a CompilerSession,
    registers: FxHashMap<ValueId, u32>,
    storage: FxHashMap<Value, Storage>,
    locals: Vec<ValType>,
    frame: Option<u32>,
    pc: Option<u32>,
    frame_size: u32,
    code: WasmFunction,
}

impl<'a> Body<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        body: &'a Function,
        signature: &'a CallAbi,
        callees: &'a FxHashMap<FunctionId, (u32, CallAbi)>,
        program: &'a ResolvedPhysicalProgram<'a>,
        session: &'a CompilerSession,
        env: ModuleEnv<'a>,
        imports: &'a Imports,
        strings: &'a mut Vec<StaticStr>,
        evidence: &'a evidence::Image,
        entry_abis: &'a FxHashMap<(TraitId, TraitDictionaryEntryIndex), (u32, CallAbi)>,
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
            layout_slot: 0,
            dynamic_size: 0,
            dynamic_align: 0,
            dynamic_base: 0,
            allocation_end: 0,
            pending_failure: 0,
            scratch: 0,
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
        let witnessed = body
            .blocks()
            .any(|block| operations(body.block(block)).any(|op| layout_witness(op).is_some()));
        if witnessed {
            this.layout_slot = this.reserve_bytes(8)?;
        }
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
                        signature.input_local(index as u32)
                    };
                    this.storage.insert(value, Storage::Local(local));
                }
            }
        }
        for block in body.blocks() {
            for operation in operations(body.block(block)) {
                if matches!(operation.kind, OperationKind::Replace)
                    && layout_witness(operation).is_none()
                {
                    let MirType::Lowered(ty) = this.pointee_type(&operation.operands[0])? else {
                        return Err("pointer replacement".into());
                    };
                    this.reserve_scratch(ty)?;
                }
                if let Some(Value::Function(target)) = callee(operation)
                    && let Some(payload) = this.optional_payload(target)
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
                            this.owned_evidence.push(Value::Register(id));
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
                            this.owned_evidence.push(Value::Register(id));
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
                        if addressed.contains(&value) || scalar(&ty).is_err() {
                            this.slot(value, this.size(&ty)?)?;
                        } else {
                            let local = this.local(scalar(&ty)?.wasm());
                            this.storage.insert(value, Storage::Local(local));
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
        this.frame_size = (this.frame_size + 7) & !7;
        if !this.selections.is_empty() {
            this.reserve_scratch(Type::unit())?;
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
            let offset = self.frame_size;
            self.frame_size = self
                .frame_size
                .checked_add(size.max(1).checked_add(7).ok_or("frame overflow")? & !7)
                .ok_or("frame overflow")?;
            self.scratch_slots.insert(ty, offset);
        }
        Ok(())
    }

    fn scratch_address(&mut self, ty: Type) {
        self.i(I::LocalGet(self.frame.expect("scratch needs a frame")));
        self.i(I::I32Const(self.scratch_slots[&ty] as i32));
        self.i(I::I32Add);
    }

    /// Turn the native presence result and temporary payload into an owned Ferlium Option.
    fn finish_optional(&mut self, output: &Value, payload: Type) -> Result<(), String> {
        let MirType::Lowered(ty) = self.pointee_type(output)? else {
            return Err("optional output must be a value place".into());
        };
        let adapter = NativeOptionalResultAdapter::new(ty, payload, self.env, self.session)?;
        // Preserve the presence result on the operand stack while preparing the two addresses.
        self.address(output)?;
        self.i(I::LocalSet(self.dynamic_base));
        self.scratch_address(payload);
        self.i(I::LocalSet(self.dynamic_size));
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
        self.i(I::GlobalGet(Global::Context as u32));
        self.i(I::I32Load(MemArg {
            offset: offset as u64,
            ..memarg(2)
        }));
    }

    fn frame_address(&mut self, offset: u32) {
        self.i(I::LocalGet(self.frame.expect("reserved frame storage")));
        self.i(I::I32Const(offset as i32));
        self.i(I::I32Add);
    }

    fn release_evidence(&mut self, reference: &Value) -> Result<(), String> {
        self.context_pointer(offset_of!(InvocationState, evidence));
        self.address(reference)?;
        self.i(I::Call(self.imports.function_index("release_evidence")));
        Ok(())
    }

    fn dictionary_index(&mut self, dictionary: &Value, entry: usize) -> Result<(), String> {
        // Descriptor and entry-table addresses are image-relative; environments are relocated.
        self.context_pointer(offset_of!(InvocationState, evidence));
        self.context_pointer(offset_of!(InvocationState, evidence));
        self.context_pointer(offset_of!(InvocationState, evidence));
        self.value(dictionary)?;
        self.i(I::I32Load(memarg(2)));
        self.i(I::I32Const(2));
        self.i(I::I32Shl);
        self.i(I::I32Add);
        self.i(I::I32Load(memarg(2)));
        self.i(I::I32Add);
        self.i(I::I32Load(MemArg {
            offset: offset_of!(DictionaryDescriptor, entries) as u64,
            ..memarg(2)
        }));
        self.i(I::I32Add);
        self.i(I::I32Load(MemArg {
            offset: entry as u64 * 4,
            ..memarg(2)
        }));
        Ok(())
    }

    fn dynamic_layout(&mut self, dictionary: &Value) -> Result<(), String> {
        for (index, entry) in self.layout_entries.into_iter().enumerate() {
            let (ty, _) = self.entry_abis[&entry];
            self.value(dictionary)?;
            self.frame_address(self.layout_slot + index as u32 * 4);
            self.dictionary_index(dictionary, entry.1.as_index())?;
            self.i(I::CallIndirect {
                type_index: ty,
                table_index: 0,
            });
            self.frame_address(self.layout_slot + index as u32 * 4);
            self.i(I::I32Load(memarg(2)));
            self.i(I::LocalSet(if index == 0 {
                self.dynamic_size
            } else {
                self.dynamic_align
            }));
        }
        Ok(())
    }

    /// Reserve witnessed frame bytes, doing the alignment and extent arithmetic without wrapping.
    fn dynamic_alloca(&mut self) {
        // alignment = max(requested_alignment, 8), preserving alignment for callees' fixed frames.
        self.i(I::LocalGet(self.dynamic_align));
        self.i(I::I32Const(8));
        self.i(I::LocalGet(self.dynamic_align));
        self.i(I::I32Const(8));
        self.i(I::I32GtU);
        self.i(I::Select);
        self.i(I::LocalSet(self.dynamic_align));
        // base = align_up(stack_pointer, alignment).
        self.i(I::GlobalGet(Global::Stack as u32));
        self.i(I::I64ExtendI32U);
        self.i(I::LocalGet(self.dynamic_align));
        self.i(I::I64ExtendI32U);
        self.i(I::I64Const(1));
        self.i(I::I64Sub);
        self.i(I::I64Add);
        self.i(I::I64Const(0));
        self.i(I::LocalGet(self.dynamic_align));
        self.i(I::I64ExtendI32U);
        self.i(I::I64Sub);
        self.i(I::I64And);
        self.i(I::LocalTee(self.allocation_end));
        self.i(I::I32WrapI64);
        self.i(I::LocalSet(self.dynamic_base));
        // end = align_up(base + max(size, 1), 8), reserving a distinct address even for zero size.
        self.i(I::LocalGet(self.allocation_end));
        self.i(I::LocalGet(self.dynamic_size));
        self.i(I::I32Const(1));
        self.i(I::LocalGet(self.dynamic_size));
        self.i(I::Select);
        self.i(I::I64ExtendI32U);
        self.i(I::I64Add);
        self.i(I::I64Const(7));
        self.i(I::I64Add);
        self.i(I::I64Const(-8));
        self.i(I::I64And);
        self.i(I::LocalTee(self.allocation_end));
        // if end > stack_limit: fail(StackCapacity).
        self.i(I::GlobalGet(Global::End as u32));
        self.i(I::I64ExtendI32U);
        self.i(I::I64GtU);
        self.i(I::If(BlockType::Empty));
        self.fail(FailureCode::StackCapacity);
        self.i(I::End);
        // stack_pointer = end.
        self.i(I::LocalGet(self.allocation_end));
        self.i(I::I32WrapI64);
        self.i(I::GlobalSet(Global::Stack as u32));
        // Leave base on the operand stack as the allocation result.
        self.i(I::LocalGet(self.dynamic_base));
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
        let (ty, abi) = self.entry_abis[&key].clone();
        if inputs.len() + 1 != abi.parameters.len() {
            return Err("dictionary call argument count".into());
        }
        if abi.fallible {
            self.context_pointer(offset_of!(InvocationState, native_failure));
        }
        self.address(selected)?;
        for (input, transport) in inputs.iter().zip(&abi.parameters[1..]) {
            match transport {
                ParameterTransport::Direct(_) => {
                    self.read(input)?;
                }
                ParameterTransport::Indirect => self.address(input)?,
            }
        }
        if let Some(output) = output {
            self.address(output)?;
        } else {
            self.scratch_address(Type::unit());
        }
        self.dictionary_index(selected, key.1.as_index())?;
        self.i(I::CallIndirect {
            type_index: ty,
            table_index: 0,
        });
        if invoked && !abi.fallible {
            self.i(I::I32Const(0));
        } else if !invoked && abi.fallible {
            self.i(I::Drop);
        }
        Ok(())
    }

    fn capture_failure(&mut self) {
        self.context_pointer(offset_of!(InvocationState, diagnostics));
        self.i(I::LocalGet(self.pending_failure));
        self.i(I::Call(self.imports.function_index("capture_failure")));
        self.i(I::LocalSet(self.pending_failure));
    }

    fn propagate_failure(&mut self) {
        self.context_pointer(offset_of!(InvocationState, diagnostics));
        self.i(I::LocalGet(self.pending_failure));
        self.i(I::Call(self.imports.function_index("propagate_failure")));
        self.i(I::If(BlockType::Empty));
        self.fail(FailureCode::Source);
        self.i(I::End);
    }

    fn return_frame(&mut self, failed: bool) -> Result<(), String> {
        if failed && !self.signature.fallible {
            return Err("failure in an infallible entry".into());
        }
        for value in self.owned_evidence.clone() {
            self.release_evidence(&value)?;
        }
        if let Some(frame) = self.frame {
            self.i(I::LocalGet(frame));
            self.i(I::GlobalSet(Global::Stack as u32));
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
            let index = self
                .strings
                .iter()
                .position(|candidate| candidate == text)
                .unwrap_or_else(|| {
                    self.strings.push(*text);
                    self.strings.len() - 1
                });
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
            return self.call_dictionary(&callee, &inputs, output, invoked);
        };
        // Static calls bypass fixed Value adapters without adding a source call-depth frame.
        let target = self.program.direct_entry(target);
        let (index, abi) = self
            .callees
            .get(&target)
            .cloned()
            .ok_or("unresolved callee")?;
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
        for (parameter, input) in abi.parameters.iter().zip(inputs) {
            match parameter {
                ParameterTransport::Direct(_) => {
                    self.read(input)?;
                }
                ParameterTransport::Indirect => self.address(input)?,
            }
        }
        let optional_payload = self.optional_payload(target);
        if let Some(payload) = optional_payload {
            self.scratch_address(payload);
        } else if abi.output() {
            self.address(output.ok_or("missing output storage")?)?;
        }
        self.i(I::Call(index));
        if let Some(payload) = optional_payload {
            self.finish_optional(output.ok_or("missing optional output")?, payload)?;
        }
        if let Some(ty) = direct_result {
            self.finish_store(output.unwrap(), ty);
        }
        if invoked && !abi.fallible {
            self.i(I::I32Const(0));
        } else if abi.fallible && !invoked {
            // A plain call promises success, even when its callee uses a status-return ABI.
            self.i(I::Drop);
        }
        Ok(())
    }

    fn local(&mut self, ty: ValType) -> u32 {
        let id = self.signature.parameter_count() as u32 + self.locals.len() as u32;
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
                            let abi = match &op.operands[0] {
                                Value::Function(target) => {
                                    let target = self.program.direct_entry(*target);
                                    self.callees.get(&target).map(|(_, abi)| abi)
                                }
                                _ => None,
                            };
                            if index + 1 == op.operands.len()
                                && ty.result_convention.has_result_place()
                            {
                                abi.is_none_or(CallAbi::output)
                            } else {
                                !index
                                    .checked_sub(1)
                                    .and_then(|i| abi?.parameters.get(i))
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
            .checked_add(size.max(1).checked_add(7).ok_or("frame size overflow")? & !7)
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
                self.i(I::LocalGet(self.frame.expect("stack slot needs a frame")));
                self.i(I::I32Const(offset as i32));
                self.i(I::I32Add);
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
            Value::Register(id) => self.i(I::LocalGet(self.registers[id])),
            Value::Parameter(id) => self.i(I::LocalGet(
                if self.body.parameters()[id.as_index()].kind == ParameterKind::Return {
                    self.signature.output_local()
                } else {
                    self.signature.input_local(id.as_u32())
                },
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
        if matches!(&*role, ValueRole::VariantPayloadStorage) {
            self.value(value)?;
            self.load(ScalarType::native(NativeScalar::Bool));
            return Ok(ScalarType::native(NativeScalar::Bool));
        }
        if let Value::Parameter(id) = value
            && self.body.parameters()[id.as_index()].kind == ParameterKind::Dictionary
            && self.body.parameters()[id.as_index()].ty == Type::primitive::<bool>()
        {
            self.value(value)?;
            self.load(ScalarType::native(NativeScalar::Bool));
            return Ok(ScalarType::native(NativeScalar::Bool));
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
            self.i(I::LocalGet(local));
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
            self.i(I::LocalSet(local));
        } else {
            self.store(ty);
        }
    }

    fn load(&mut self, ty: ScalarType) {
        if ty.is::<()>() {
            self.i(I::Drop);
            self.i(I::I32Const(0));
        } else if ty.is::<bool>() {
            self.i(I::I32Load8U(memarg(0)));
        } else if ty.is::<Float>() {
            self.i(I::F64Load(memarg(3)));
        } else if ty.is::<isize>() {
            self.i(I::I32Load(memarg(2)));
        } else {
            unreachable!("missing scalar load mapping")
        }
    }

    fn store(&mut self, ty: ScalarType) {
        if ty.is::<()>() {
            self.i(I::Drop);
            self.i(I::Drop);
        } else if ty.is::<bool>() {
            self.i(I::I32Store8(memarg(0)));
        } else if ty.is::<Float>() {
            self.i(I::F64Store(memarg(3)));
        } else if ty.is::<isize>() {
            self.i(I::I32Store(memarg(2)));
        } else {
            unreachable!("missing scalar store mapping")
        }
    }

    fn emit(mut self) -> Result<WasmFunction, String> {
        // Check before addition, so a large frame cannot wrap the linear-memory stack pointer.
        if let Some(frame) = self.frame {
            self.i(I::GlobalGet(Global::Stack as u32));
            self.i(I::LocalSet(frame));
            self.i(I::I32Const(self.frame_size as i32));
            self.i(I::GlobalGet(Global::End as u32));
            self.i(I::GlobalGet(Global::Stack as u32));
            self.i(I::I32Sub);
            self.i(I::I32GtU);
            self.i(I::If(BlockType::Empty));
            self.fail(FailureCode::StackCapacity);
            self.i(I::End);
            self.i(I::GlobalGet(Global::Stack as u32));
            self.i(I::I32Const(self.frame_size as i32));
            self.i(I::I32Add);
            self.i(I::GlobalSet(Global::Stack as u32));
        }
        self.i(I::GlobalGet(Global::Depth as u32));
        self.i(I::I32Const(1));
        self.i(I::I32Add);
        self.i(I::GlobalSet(Global::Depth as u32));
        for value in self.owned_evidence.clone() {
            self.address(&value)?;
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
                self.i(I::LocalGet(self.signature.input_local(index as u32)));
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
            self.i(I::LocalGet(pc));
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
                self.i(I::LocalSet(self.pc.expect("branch needs a dispatcher")));
                self.i(I::Br(dispatch_depth.expect("branch needs a dispatcher")));
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
                self.i(I::LocalSet(self.pc.expect("branch needs a dispatcher")));
                self.i(I::Br(dispatch_depth.expect("branch needs a dispatcher")));
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
                self.i(I::LocalSet(self.pc.expect("switch needs a dispatcher")));
                self.i(I::Br(dispatch_depth.expect("switch needs a dispatcher")));
            }
            TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } => {
                self.call_operation(operation, true)?;
                self.i(I::If(BlockType::Empty));
                self.capture_failure();
                self.i(I::I32Const(error.as_u32() as i32));
                self.i(I::LocalSet(self.pc.unwrap()));
                self.i(I::Else);
                self.i(I::I32Const(normal.as_u32() as i32));
                self.i(I::LocalSet(self.pc.unwrap()));
                self.i(I::End);
                self.i(I::Br(dispatch_depth.unwrap()));
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
                self.i(I::Call(self.imports.function_index("alloc")));
                self.i(I::LocalSet(self.scratch));
                for (index, value) in elements.iter().enumerate() {
                    self.i(I::LocalGet(self.scratch));
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
                        self.i(I::LocalGet(self.scratch));
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
                let fields = self
                    .program
                    .dictionary(*definition)
                    .unwrap()
                    .environment()
                    .fields
                    .clone();
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
                self.i(I::Call(self.imports.function_index("build_evidence")));
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
                self.i(I::Call(self.imports.function_index("retain_evidence")));
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
                        self.i(I::LocalGet(self.dynamic_size));
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
                    self.i(I::LocalSet(self.scratch));
                    self.dynamic_alloca();
                    self.i(I::Drop);
                } else {
                    self.scratch_address(ty);
                    self.i(I::LocalSet(self.dynamic_base));
                    self.i(I::I32Const(self.size(&MirType::Lowered(ty))? as i32));
                    self.i(I::LocalSet(self.dynamic_size));
                }
                self.i(I::LocalGet(self.dynamic_base));
                self.address(&args[0])?;
                self.i(I::LocalGet(self.dynamic_size));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&args[0])?;
                self.address(&args[1])?;
                self.i(I::LocalGet(self.dynamic_size));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&args[1])?;
                self.i(I::LocalGet(self.dynamic_base));
                self.i(I::LocalGet(self.dynamic_size));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                if layout_witness(op).is_some() {
                    self.i(I::LocalGet(self.scratch));
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
                self.i(if ty.is::<Float>() {
                    I::F64Eq
                } else if ty.is::<isize>() || ty.is::<bool>() || ty.is::<()>() {
                    I::I32Eq
                } else {
                    unreachable!("missing scalar comparison mapping")
                });
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
                self.i(I::Call(self.imports.function_index("alloc")));
            }
            RuntimeDealloc => {
                self.address(&args[0])?;
                self.i(I::Call(self.imports.function_index("dealloc")));
            }
            _ => return Err("unsupported physical operation".into()),
        }
        if let Some(id) = op.result_id() {
            self.i(I::LocalSet(self.registers[&id]));
            let value = Value::Register(id);
            if self.storage.contains_key(&value) {
                let role = self.roles.get(&value, self.body.constants()).unwrap();
                if let ValueRole::Materialized(ty) = &*role {
                    let ty = scalar(ty)?;
                    self.address(&value)?;
                    self.i(I::LocalGet(self.registers[&id]));
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
