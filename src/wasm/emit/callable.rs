// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Uniform callable entries and adapters to direct implementations.

use std::mem::offset_of;

use wasm_encoder::{BlockType, Function as WasmFunction, Instruction as I, MemArg, ValType};

use crate::{
    CompilerSession, FxHashMap, FxHashSet,
    hir::native_functions::NativeResult,
    mir::{
        Function, Operation, OperationKind, ParameterKind, Value, ValueId,
        physical::{DictionaryReference, program::ResolvedPhysicalProgram},
        role::{MirType, ValueRole},
    },
    module::{FunctionId, ModuleEnv, TraitId, id::Id},
    std::{core_traits_names::VALUE_TRAIT_NAME, logic::bool_type, value::value_layout_for_type},
    types::{r#trait::TraitDictionaryEntryIndex, r#type::Type},
    wasm::{
        Imports,
        abi::{
            CallAbi, DispatchTableSlotId, Parameter as ParameterTransport, ResultKind,
            WasmFunctionId, WasmLocalId, WasmTypeId,
        },
        callable_environment::Environment,
        evidence::ENVIRONMENT_OFFSET,
        execution::InvocationState,
    },
};

use super::{
    Global, ScalarType, adapters::NativeOptionalResultAdapter, allocate_frame, body::Body,
    context_pointer, dictionary_table, enter_frame, frame_address, frame_bytes, leave_frame,
    memarg, operations,
};

/// Construction schema; every materialization of a given target has the same leading parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Captures {
    pub hidden: usize,
    pub values: usize,
}

#[derive(Default)]
pub(super) struct Reachable {
    pub entries: Vec<(FunctionId, Captures)>,
    indices: FxHashMap<FunctionId, usize>,
    pub arities: Vec<usize>,
    pub references: FxHashSet<FunctionId>,
    pub selected: Vec<(TraitId, TraitDictionaryEntryIndex)>,
}

impl Reachable {
    pub fn add(&mut self, target: FunctionId, captures: Captures) {
        if let Some(&index) = self.indices.get(&target) {
            assert_eq!(self.entries[index].1, captures, "callable capture schema");
        } else {
            self.indices.insert(target, self.entries.len());
            self.entries.push((target, captures));
        }
    }

    pub fn arity(&mut self, arity: usize) {
        if !self.arities.contains(&arity) {
            self.arities.push(arity);
        }
    }

    pub fn select(&mut self, entry: (TraitId, TraitDictionaryEntryIndex)) {
        if !self.selected.contains(&entry) {
            self.selected.push(entry);
        }
    }
}

/// The first parameter is the borrowed environment; all visible arguments and results are places.
pub(super) fn abi(arity: usize) -> CallAbi {
    CallAbi {
        parameters: vec![ParameterTransport::Indirect; arity + 1],
        result: ResultKind::Output,
        fallible: true,
    }
}

pub(super) fn visible_arity(target: &CallAbi, captures: Captures) -> Result<usize, String> {
    captures
        .hidden
        .checked_add(captures.values)
        .and_then(|leading| target.parameters.len().checked_sub(leading))
        .ok_or_else(|| "callable capture arity".into())
}

#[derive(Clone, Copy)]
pub(super) struct ValueMethod {
    ty: WasmTypeId,
    entry: TraitDictionaryEntryIndex,
}

impl ValueMethod {
    pub(super) fn new(ty: WasmTypeId, entry: TraitDictionaryEntryIndex) -> Self {
        Self { ty, entry }
    }
}

#[derive(Clone, Copy)]
pub(super) struct ValueMethods {
    pub clone: ValueMethod,
    pub drop: ValueMethod,
}

pub(super) struct Entries {
    pub slots: FxHashMap<FunctionId, DispatchTableSlotId>,
    pub signatures: FxHashMap<usize, WasmTypeId>,
    pub references: FxHashMap<FunctionId, u32>,
    pub selected: FxHashMap<(TraitId, TraitDictionaryEntryIndex), DispatchTableSlotId>,
    pub clone: Option<WasmFunctionId>,
    pub drop: Option<WasmFunctionId>,
    pub value_methods: Option<ValueMethods>,
}

/// Dictionary entry selections are borrowed until a transfer materializes an owning function.
pub(super) fn selections(
    body: &Function,
) -> FxHashMap<ValueId, (TraitId, TraitDictionaryEntryIndex)> {
    let mut entries = FxHashMap::default();
    loop {
        let previous = entries.len();
        for operation in body.blocks().flat_map(|b| operations(body.block(b))) {
            match operation.kind {
                OperationKind::DictEntry {
                    trait_id,
                    entry_index,
                    ..
                } => {
                    entries.insert(operation.result_id().unwrap(), (trait_id, entry_index));
                }
                OperationKind::Load => {
                    if let Value::Register(id) = &operation.operands[0]
                        && let Some(&entry) = entries.get(id)
                    {
                        entries.insert(operation.result_id().unwrap(), entry);
                    }
                }
                _ => (),
            }
        }
        if previous == entries.len() {
            break;
        }
    }
    entries
}

pub(super) fn selected_adapter(
    env: ModuleEnv<'_>,
    entry: (TraitId, TraitDictionaryEntryIndex),
    ty: WasmTypeId,
    target: &CallAbi,
) -> Result<WasmFunction, String> {
    let abi = abi(target
        .parameters
        .len()
        .checked_sub(1)
        .ok_or("selected callable dictionary arity")?);
    let base = WasmLocalId::from_index(abi.parameter_count());
    let dictionary = WasmLocalId::from_index(abi.parameter_count() + 1);
    let mut code = WasmFunction::new([(2, ValType::I32)]);
    frame_address(&mut code, abi.input_local(0), Environment::hidden_offset(0));
    code.instruction(&I::LocalSet(dictionary.as_u32()));
    if target.fallible {
        code.instruction(&I::LocalGet(abi.failure_local().as_u32()));
    }
    code.instruction(&I::LocalGet(dictionary.as_u32()));
    let declaration = env.trait_def(entry.0);
    for (index, transport) in target.parameters[1..].iter().enumerate() {
        code.instruction(&I::LocalGet(abi.input_local(index + 1).as_u32()));
        if matches!(transport, ParameterTransport::Direct(_)) {
            ScalarType::of(declaration.methods[entry.1.as_index()].1.ty_scheme.ty.args[index].ty)?
                .load(&mut code);
        }
    }
    code.instruction(&I::LocalGet(abi.output_local().as_u32()));
    code.instruction(&I::LocalGet(dictionary.as_u32()));
    dictionary_table(&mut code, base);
    code.instruction(&I::I32Load(MemArg {
        offset: entry.1.as_index() as u64 * 4,
        ..memarg(2)
    }));
    code.instruction(&I::CallIndirect {
        type_index: ty.as_u32(),
        table_index: 0,
    });
    if !target.fallible {
        code.instruction(&I::I32Const(0));
    }
    code.instruction(&I::End);
    Ok(code)
}

fn field(code: &mut WasmFunction, base: WasmLocalId, offset: usize) {
    code.instruction(&I::LocalGet(base.as_u32()));
    code.instruction(&I::I32Load(MemArg {
        offset: offset as u64,
        ..memarg(2)
    }));
}

fn values(code: &mut WasmFunction, environment: WasmLocalId) {
    code.instruction(&I::LocalGet(environment.as_u32()));
    field(code, environment, offset_of!(Environment, values_offset));
    code.instruction(&I::I32Add);
}

fn dictionary(code: &mut WasmFunction, environment: WasmLocalId) {
    frame_address(
        code,
        environment,
        offset_of!(Environment, dictionary) as u32,
    );
}

/// Read an entry slot from the capture tuple's Value dictionary.
fn value_entry(
    code: &mut WasmFunction,
    environment: WasmLocalId,
    base: WasmLocalId,
    entry: TraitDictionaryEntryIndex,
) {
    dictionary(code, environment);
    dictionary_table(code, base);
    code.instruction(&I::I32Load(MemArg {
        offset: entry.as_index() as u64 * 4,
        ..memarg(2)
    }));
}

pub(super) fn clone_entry(imports: &Imports, method: ValueMethod) -> WasmFunction {
    let source = WasmLocalId::new(0);
    let result = WasmLocalId::new(1);
    let base = WasmLocalId::new(2);
    let mut code = WasmFunction::new([(2, ValType::I32)]);
    code.instruction(&I::LocalGet(source.as_u32()));
    code.instruction(&I::I32Eqz);
    code.instruction(&I::If(BlockType::Empty));
    code.instruction(&I::I32Const(0));
    code.instruction(&I::Return);
    code.instruction(&I::End);
    code.instruction(&I::LocalGet(source.as_u32()));
    code.instruction(&I::Call(
        imports.function_index("copy_callable_environment").as_u32(),
    ));
    code.instruction(&I::LocalSet(result.as_u32()));
    field(&mut code, source, offset_of!(Environment, capture_count));
    code.instruction(&I::If(BlockType::Empty));
    dictionary(&mut code, source);
    values(&mut code, source);
    values(&mut code, result);
    value_entry(&mut code, source, base, method.entry);
    code.instruction(&I::CallIndirect {
        type_index: method.ty.as_u32(),
        table_index: 0,
    });
    code.instruction(&I::End);
    code.instruction(&I::LocalGet(result.as_u32()));
    code.instruction(&I::End);
    code
}

pub(super) fn drop_entry(imports: &Imports, method: ValueMethod) -> WasmFunction {
    let environment = WasmLocalId::new(0);
    let base = WasmLocalId::new(1);
    let mut code = WasmFunction::new([(1, ValType::I32)]);
    code.instruction(&I::LocalGet(environment.as_u32()));
    code.instruction(&I::If(BlockType::Empty));
    field(
        &mut code,
        environment,
        offset_of!(Environment, capture_count),
    );
    code.instruction(&I::If(BlockType::Empty));
    dictionary(&mut code, environment);
    values(&mut code, environment);
    // Unit has no bytes; the live environment supplies an aligned result address.
    code.instruction(&I::LocalGet(environment.as_u32()));
    value_entry(&mut code, environment, base, method.entry);
    code.instruction(&I::CallIndirect {
        type_index: method.ty.as_u32(),
        table_index: 0,
    });
    code.instruction(&I::End);
    context_pointer(&mut code, offset_of!(InvocationState, evidence));
    code.instruction(&I::LocalGet(environment.as_u32()));
    code.instruction(&I::Call(
        imports
            .function_index("release_callable_environment")
            .as_u32(),
    ));
    code.instruction(&I::End);
    code.instruction(&I::End);
    code
}

/// Bridge one uniform entry to its target. Evidence-only calls borrow their environment; source
/// captures get an independent invocation copy, destroyed on both success and source failure.
pub(super) fn adapter(
    program: &ResolvedPhysicalProgram<'_>,
    target: FunctionId,
    captures: Captures,
    callees: &FxHashMap<FunctionId, (WasmFunctionId, &CallAbi)>,
    entries: &Entries,
    imports: &Imports,
    session: &CompilerSession,
) -> Result<WasmFunction, String> {
    let target = program.direct_entry(target);
    let (index, direct) = callees[&target];
    let native = program
        .module(target.module)
        .and_then(|m| m.native_entry(target));
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
        let signature = native.ok_or("missing callable native")?.signature();
        (
            signature.parameters.iter().map(|p| p.layout().ty).collect(),
            signature.result.ty(),
        )
    };
    let leading = captures
        .hidden
        .checked_add(captures.values)
        .ok_or("callable capture arity")?;
    let abi = abi(visible_arity(direct, captures)?);
    let environment = WasmLocalId::from_index(abi.parameter_count());
    let status = WasmLocalId::from_index(abi.parameter_count() + 1);
    let pending = WasmLocalId::from_index(abi.parameter_count() + 2);
    let frame = WasmLocalId::from_index(abi.parameter_count() + 3);
    let scratch = WasmLocalId::from_index(abi.parameter_count() + 4);
    let temporary = WasmLocalId::from_index(abi.parameter_count() + 5);
    let size = WasmLocalId::from_index(abi.parameter_count() + 6);
    let align = WasmLocalId::from_index(abi.parameter_count() + 7);
    let base = WasmLocalId::from_index(abi.parameter_count() + 8);
    let optional_frame = WasmLocalId::from_index(abi.parameter_count() + 9);
    let end = WasmLocalId::from_index(abi.parameter_count() + 10);
    let mut code = WasmFunction::new([(10, ValType::I32), (1, ValType::I64)]);
    code.instruction(&I::LocalGet(abi.input_local(0).as_u32()));
    code.instruction(&I::LocalSet(environment.as_u32()));
    if captures.values != 0 {
        let methods = entries
            .value_methods
            .expect("value captures require callable Value methods");
        code.instruction(&I::GlobalGet(Global::Stack as u32));
        code.instruction(&I::LocalSet(frame.as_u32()));
        field(&mut code, environment, offset_of!(Environment, values_size));
        code.instruction(&I::LocalSet(size.as_u32()));
        field(
            &mut code,
            environment,
            offset_of!(Environment, values_align),
        );
        code.instruction(&I::LocalSet(align.as_u32()));
        allocate_frame(&mut code, size, align, temporary, end);
        code.instruction(&I::Drop);
        dictionary(&mut code, environment);
        values(&mut code, environment);
        code.instruction(&I::LocalGet(temporary.as_u32()));
        value_entry(&mut code, environment, base, methods.clone.entry);
        code.instruction(&I::CallIndirect {
            type_index: methods.clone.ty.as_u32(),
            table_index: 0,
        });
    }
    let optional = if matches!(direct.result, ResultKind::Optional) {
        let NativeResult::Optional { payload, .. } = native.unwrap().signature().result else {
            unreachable!()
        };
        let env = session
            .modules()
            .env_for(session.expect_fresh_module(target.module));
        Some(NativeOptionalResultAdapter::new(
            result_ty, payload.ty, env, session,
        )?)
    } else {
        None
    };
    if let Some(optional) = &optional {
        enter_frame(
            &mut code,
            optional_frame,
            frame_bytes(optional.payload_size)?,
        );
    }
    if !direct.fallible && matches!(direct.result, ResultKind::Direct(_)) {
        code.instruction(&I::LocalGet(abi.output_local().as_u32()));
    }
    if direct.fallible {
        code.instruction(&I::LocalGet(abi.failure_local().as_u32()));
    }
    for (i, (&transport, &ty)) in direct.parameters.iter().zip(&input_types).enumerate() {
        if i < captures.hidden {
            frame_address(&mut code, environment, Environment::hidden_offset(i));
        } else if i < leading {
            code.instruction(&I::LocalGet(temporary.as_u32()));
            field(
                &mut code,
                environment,
                Environment::capture_offset(captures.hidden, i - captures.hidden) as usize,
            );
            code.instruction(&I::I32Add);
        } else {
            code.instruction(&I::LocalGet(abi.input_local(i - leading + 1).as_u32()));
        }
        if matches!(transport, ParameterTransport::Direct(_)) {
            ScalarType::of(ty)?.load(&mut code);
        }
    }
    if direct.output() {
        code.instruction(&I::LocalGet(
            if optional.is_some() {
                optional_frame
            } else {
                abi.output_local()
            }
            .as_u32(),
        ));
    }
    code.instruction(&I::Call(index.as_u32()));
    if direct.fallible {
        code.instruction(&I::LocalSet(status.as_u32()));
    } else {
        if let Some(optional) = optional {
            optional.emit(
                &mut code,
                abi.output_local(),
                optional_frame,
                scratch,
                imports.function_index("alloc"),
            );
            leave_frame(&mut code, optional_frame);
        } else if matches!(direct.result, ResultKind::Direct(_)) {
            ScalarType::of(result_ty)?.store(&mut code);
        }
    }
    if captures.values != 0 {
        let methods = entries
            .value_methods
            .expect("value captures require callable Value methods");
        // Detach the call's diagnostic before invoking guest cleanup, so a trap during drop
        // preserves the original cause in the invocation's pending-failure stack.
        code.instruction(&I::LocalGet(status.as_u32()));
        code.instruction(&I::If(BlockType::Empty));
        context_pointer(&mut code, offset_of!(InvocationState, diagnostics));
        code.instruction(&I::I32Const(0));
        code.instruction(&I::Call(imports.function_index("capture_failure").as_u32()));
        code.instruction(&I::LocalSet(pending.as_u32()));
        code.instruction(&I::End);
        dictionary(&mut code, environment);
        code.instruction(&I::LocalGet(temporary.as_u32()));
        code.instruction(&I::LocalGet(temporary.as_u32())); // Unit result, no bytes written.
        value_entry(&mut code, environment, base, methods.drop.entry);
        code.instruction(&I::CallIndirect {
            type_index: methods.drop.ty.as_u32(),
            table_index: 0,
        });
        leave_frame(&mut code, frame);
        code.instruction(&I::LocalGet(status.as_u32()));
        code.instruction(&I::If(BlockType::Empty));
        context_pointer(&mut code, offset_of!(InvocationState, diagnostics));
        code.instruction(&I::LocalGet(pending.as_u32()));
        code.instruction(&I::Call(
            imports.function_index("propagate_failure").as_u32(),
        ));
        code.instruction(&I::If(BlockType::Empty));
        code.instruction(&I::Unreachable);
        code.instruction(&I::End);
        code.instruction(&I::End);
    }
    code.instruction(&I::LocalGet(status.as_u32()));
    code.instruction(&I::End);
    Ok(code)
}

impl Body<'_, '_> {
    pub(super) fn store_selected(
        &mut self,
        source: &Value,
        destination: &Value,
        entry: (TraitId, TraitDictionaryEntryIndex),
    ) -> Result<(), String> {
        self.i(I::I32Const(0));
        self.i(I::I32Const(1));
        self.i(I::I32Const(1));
        self.i(I::I32Const(0));
        self.i(I::Call(
            self.imports
                .function_index("allocate_callable_environment")
                .as_u32(),
        ));
        self.i(I::LocalSet(self.scratch.as_u32()));
        frame_address(&mut self.code, self.scratch, Environment::hidden_offset(0));
        self.address(source)?;
        self.i(I::I32Const(size_of::<DictionaryReference>() as i32));
        self.i(I::MemoryCopy {
            src_mem: 0,
            dst_mem: 0,
        });
        frame_address(&mut self.code, self.scratch, Environment::hidden_offset(0));
        self.i(I::Call(
            self.imports.function_index("retain_evidence").as_u32(),
        ));
        self.address(destination)?;
        self.i(I::I32Const(
            self.callable_entries.selected[&entry].as_u32() as i32
        ));
        self.i(I::I32Store(memarg(2)));
        self.address(destination)?;
        self.i(I::LocalGet(self.scratch.as_u32()));
        self.i(I::I32Store(MemArg {
            offset: ENVIRONMENT_OFFSET,
            ..memarg(2)
        }));
        Ok(())
    }

    pub(super) fn call_stored(
        &mut self,
        selected: &Value,
        inputs: &[&Value],
        output: Option<&Value>,
        invoked: bool,
    ) -> Result<(), String> {
        self.context_pointer(offset_of!(InvocationState, native_failure));
        self.address(selected)?;
        self.i(I::I32Load(MemArg {
            offset: ENVIRONMENT_OFFSET,
            ..memarg(2)
        }));
        for input in inputs {
            self.address(input)?;
        }
        self.address(output.ok_or("stored callable requires result storage")?)?;
        self.address(selected)?;
        self.i(I::I32Load(memarg(2)));
        self.i(I::CallIndirect {
            type_index: self.callable_entries.signatures[&inputs.len()].as_u32(),
            table_index: 0,
        });
        self.call_status(invoked, true);
        Ok(())
    }

    /// Find an explicit Value witness among this construction's evidence dependencies. Do not
    /// search arbitrary registers: an unrelated dictionary may not dominate this construction.
    fn capture_witness(&self, ty: Type, roots: &[Value]) -> Option<Value> {
        let value_trait = self.env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let expected = self
            .env
            .trait_def(value_trait)
            .get_dictionary_type_for_tys(&[ty], &[], &[]);
        let mut pending = roots.to_vec();
        let mut seen = FxHashSet::default();
        while let Some(value) = pending.pop() {
            if !seen.insert(value.clone()) {
                continue;
            }
            match &value {
                Value::Parameter(id) if self.body.parameters()[id.as_index()].ty == expected => {
                    return Some(value);
                }
                Value::Register(id) => {
                    if let Some(op) = self.dictionary_definitions.get(id)
                        && let OperationKind::BuildDictionary { ty, .. } = op.kind
                    {
                        if ty == expected {
                            return Some(value);
                        }
                        pending.extend(op.operands.iter().cloned());
                    }
                }
                _ => (),
            }
        }
        None
    }

    pub(super) fn build_closure(&mut self, op: &Operation) -> Result<(), String> {
        let OperationKind::BuildClosure {
            function,
            num_hidden_dicts,
            has_env_dict,
            ..
        } = op.kind
        else {
            unreachable!()
        };
        let hidden = num_hidden_dicts as usize;
        let end = op.operands.len() - usize::from(has_env_dict);
        let captures = &op.operands[hidden..end];
        assert!(
            has_env_dict || captures.is_empty(),
            "closure value captures require a Value dictionary"
        );
        let result = Value::Register(op.result_id().unwrap());
        self.address(&result)?;
        self.i(I::I32Const(
            self.callable_entries.slots[&function].as_u32() as i32
        ));
        self.i(I::I32Store(memarg(2)));
        if hidden == 0 && captures.is_empty() {
            self.address(&result)?;
            self.i(I::I32Const(0));
            self.i(I::I32Store(MemArg {
                offset: ENVIRONMENT_OFFSET,
                ..memarg(2)
            }));
            return Ok(());
        }
        let (environment, cursor) = self.callable_locals.expect("closure construction locals");
        if has_env_dict {
            self.dynamic_layout(&op.operands[end])?;
            self.i(I::LocalGet(self.dynamic_size.as_u32()));
            self.i(I::LocalGet(self.dynamic_align.as_u32()));
        } else {
            self.i(I::I32Const(0));
            self.i(I::I32Const(1));
        }
        self.i(I::I32Const(hidden as i32));
        self.i(I::I32Const(captures.len() as i32));
        self.i(I::Call(
            self.imports
                .function_index("allocate_callable_environment")
                .as_u32(),
        ));
        self.i(I::LocalSet(environment.as_u32()));
        self.address(&result)?;
        self.i(I::LocalGet(environment.as_u32()));
        self.i(I::I32Store(MemArg {
            offset: ENVIRONMENT_OFFSET,
            ..memarg(2)
        }));
        for index in 0..hidden + usize::from(has_env_dict) {
            let (offset, value) = if index == hidden {
                (
                    offset_of!(Environment, dictionary) as u32,
                    &op.operands[end],
                )
            } else {
                (Environment::hidden_offset(index), &op.operands[index])
            };
            frame_address(&mut self.code, environment, offset);
            if matches!(
                self.roles.get(value, self.body.constants()).as_deref(),
                Some(ValueRole::VariantPayloadStorage)
            ) || matches!(self.roles.get(value, self.body.constants()).as_deref(),
                Some(ValueRole::Materialized(MirType::Lowered(ty))) if *ty == bool_type())
                || matches!(value, Value::Parameter(id) if self.body.parameters()[id.as_index()].ty == bool_type())
            {
                self.read(value)?;
                self.i(I::I32Store8(memarg(0)));
            } else {
                self.value(value)?;
                self.i(I::I32Const(size_of::<DictionaryReference>() as i32));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                frame_address(&mut self.code, environment, offset);
                self.i(I::Call(
                    self.imports.function_index("retain_evidence").as_u32(),
                ));
            }
        }
        self.i(I::I32Const(0));
        self.i(I::LocalSet(cursor.as_u32()));
        for (index, capture) in captures.iter().enumerate() {
            let MirType::Lowered(ty) = self.pointee_type(capture)? else {
                return Err("pointer capture".into());
            };
            if let Ok(layout) = value_layout_for_type(ty, op.span, &self.env) {
                self.i(I::I32Const(layout.size as i32));
                self.i(I::LocalSet(self.dynamic_size.as_u32()));
                self.i(I::I32Const(layout.align as i32));
                self.i(I::LocalSet(self.dynamic_align.as_u32()));
            } else {
                let witness = self
                    .capture_witness(ty, &op.operands)
                    .ok_or_else(|| format!("missing explicit closure capture layout for {ty:?}"))?;
                self.dynamic_layout(&witness)?;
            }
            // Positional tuple layout: align each field, then advance by its representation size.
            self.i(I::LocalGet(cursor.as_u32()));
            self.i(I::LocalGet(self.dynamic_align.as_u32()));
            self.i(I::I32Const(1));
            self.i(I::I32Sub);
            self.i(I::I32Add);
            self.i(I::I32Const(0));
            self.i(I::LocalGet(self.dynamic_align.as_u32()));
            self.i(I::I32Sub);
            self.i(I::I32And);
            self.i(I::LocalSet(cursor.as_u32()));
            self.i(I::LocalGet(environment.as_u32()));
            self.i(I::LocalGet(cursor.as_u32()));
            self.i(I::I32Store(MemArg {
                offset: Environment::capture_offset(hidden, index) as u64,
                ..memarg(2)
            }));
            values(&mut self.code, environment);
            self.i(I::LocalGet(cursor.as_u32()));
            self.i(I::I32Add);
            self.address(capture)?;
            self.i(I::LocalGet(self.dynamic_size.as_u32()));
            self.i(I::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            });
            self.i(I::LocalGet(cursor.as_u32()));
            self.i(I::LocalGet(self.dynamic_size.as_u32()));
            self.i(I::I32Add);
            self.i(I::LocalSet(cursor.as_u32()));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use wasm_bindgen_test::wasm_bindgen_test;

    use super::*;
    use crate::{
        Location, MirOptimization,
        hir::function::ArgConvention,
        mir::{
            builder::FunctionBuilder,
            physical::{prepare_physical_mir, program::resolve_physical_program},
            terminator::Terminator,
        },
        module::{LocalFunctionId, Path},
        std::{math::int_type, value::VALUE_CLONE_METHOD_INDEX},
        types::{
            effects::no_effects,
            r#type::{CallImplType, CallResultConvention, FnType},
        },
        ustr,
        wasm::{CompiledProgram, WasmLimits, callable_environment::LIVE_ENVIRONMENTS},
    };

    #[wasm_bindgen_test]
    fn wasm_codegen_materialized_dictionary_entry() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        session.set_physical_mir_optimization(MirOptimization::Disabled);
        let module = session
            .compile(
                "fn identity(x: int) -> int { x } fn compute(x: int) -> int { let f = identity; f(x) }",
                "selected",
                Path::single_str("selected"),
            )
            .unwrap()
            .module_id;
        let current = session.expect_fresh_module(module);
        let env = session.modules().env_for(current);
        let entry = FunctionId::new(
            module,
            current.get_local_function_id(ustr("compute")).unwrap(),
        );
        let original = session.prepare_physical_program(module).unwrap();
        let original_body = original.function(entry).unwrap();
        let drop = original_body
            .blocks()
            .flat_map(|b| operations(original_body.block(b)))
            .find(|op| {
                matches!(op.kind, OperationKind::DropInitialized { .. })
                    && matches!(op.operands[1], Value::Function(_))
            })
            .expect("concrete callable destructor")
            .operands[1]
            .clone();
        let trait_id = env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let dictionary_ty =
            env.trait_def(trait_id)
                .get_dictionary_type_for_tys(&[int_type()], &[], &[]);
        let dictionary = original
            .modules()
            .iter()
            .flat_map(|m| m.dictionaries())
            .find(|d| d.ty() == dictionary_ty && d.capture_types().is_empty())
            .unwrap()
            .id();
        let signature = FnType::new_by_val([int_type()], int_type(), no_effects());
        let ty = Type::function_type(signature.clone());
        let span = Location::new_synthesized();
        let mut body = FunctionBuilder::new(ustr("compute"), CallResultConvention::Value);
        let input = Value::Parameter(
            body.add_parameter(int_type(), ParameterKind::Parameter(ArgConvention::Let)),
        );
        let output = Value::Parameter(body.add_parameter(int_type(), ParameterKind::Return));
        let block = body.add_block();
        let marker = body
            .append_operation(block, Operation::stack_save(span))
            .unwrap();
        let selected = body
            .append_operation(
                block,
                Operation::dict_entry(
                    span,
                    Value::Dictionary(dictionary),
                    trait_id,
                    env.trait_def(trait_id)
                        .dictionary_method_index(VALUE_CLONE_METHOD_INDEX),
                    ty,
                ),
            )
            .unwrap();
        let loaded = body
            .append_operation(block, Operation::load(span, selected))
            .unwrap();
        let stored = body
            .append_operation(block, Operation::alloca(span, ty))
            .unwrap();
        body.append_operation(block, Operation::store(span, loaded, stored.clone()));
        let cloned = body
            .append_operation(
                block,
                Operation::clone_closure_env(span, stored.clone(), ty),
            )
            .unwrap();
        let second = body
            .append_operation(block, Operation::alloca(span, ty))
            .unwrap();
        body.append_operation(block, Operation::store(span, cloned, second.clone()));
        body.append_operation(
            block,
            Operation::call(
                span,
                second.clone(),
                [input, output],
                CallImplType::value(signature),
            ),
        );
        body.append_operation(
            block,
            Operation::drop_initialized(span, second, drop.clone(), ty),
        );
        body.append_operation(block, Operation::drop_initialized(span, stored, drop, ty));
        body.append_operation(block, Operation::stack_restore(span, marker));
        body.set_terminator(block, Terminator::ret(span));
        let artifacts = original.module(module).unwrap();
        let mut functions = (0..artifacts.entry_count())
            .map(|i| artifacts.get(LocalFunctionId::from_index(i)).cloned())
            .collect::<Vec<_>>();
        functions[entry.function.as_index()] = Some(body.finish_physical(env));
        let replacement = prepare_physical_mir(
            functions,
            artifacts.direct_entries().clone(),
            session
                .mir_artifacts_for(module, MirOptimization::Disabled)
                .unwrap(),
            env,
        )
        .unwrap();
        let program = resolve_physical_program(original.modules().iter().map(|m| {
            if m.module() == module {
                &replacement
            } else {
                *m
            }
        }))
        .unwrap();
        let mut instance = CompiledProgram::from_physical(&session, &program, entry)
            .unwrap()
            .instantiate::<(isize,), isize>()
            .unwrap();
        let live = LIVE_ENVIRONMENTS.get();
        assert_eq!(instance.run((17,), WasmLimits::default()).unwrap(), 17);
        assert_eq!(LIVE_ENVIRONMENTS.get(), live);
    }
}
