// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Uniform callable entries and adapters to direct implementations.

use std::mem::offset_of;

use wasm_encoder::{BlockType, Function as WasmFunction, Instruction as I, MemArg, ValType};

use crate::{
    CompilerSession, FxHashMap, FxHashSet,
    mir::{
        Function, Operation, OperationKind, Value, ValueId,
        physical::{DictionaryReference, program::ResolvedPhysicalProgram},
        role::{MirType, ValueRole},
    },
    module::{FunctionId, ModuleEnv, ProjectionIndex, TraitId, id::Id},
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        logic::bool_type,
        value::{
            ProductLayoutSpec, ProductMemberLayout, VALUE_SIZE_ASSOC_CONST_INDEX, ValueLayoutExpr,
            product_layout_spec, value_layout_formula_for_type,
        },
    },
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
    Global, ScalarType,
    adapters::AdapterTarget,
    allocate_frame,
    body::{
        Body,
        HelperLocal::{DynamicAlign, DynamicBase, DynamicSize, Scratch},
    },
    context_pointer, dictionary_table, enter_frame, frame_address, frame_bytes, leave_frame,
    memarg, memarg_at, offset_sum, operations,
    peephole::Instructions,
};

fn closure_value_captures(op: &Operation) -> &[Value] {
    let OperationKind::BuildClosure {
        num_hidden_dicts,
        has_env_dict,
        ..
    } = op.kind
    else {
        unreachable!()
    };
    let end = op.operands.len() - usize::from(has_env_dict);
    &op.operands[num_hidden_dicts as usize..end]
}

/// One recipe shared by local planning and capture emission. Static layouts are resolved once.
pub(super) struct CaptureLayout {
    spec: ProductLayoutSpec,
    offsets: Option<Vec<usize>>,
    fallbacks: CaptureFallbacks,
}

#[derive(Default)]
struct CaptureFallbacks {
    leaves: Vec<(Type, Value, WasmLocalId, WasmLocalId)>,
    expressions: Vec<(ValueLayoutExpr, WasmLocalId)>,
    layouts: FxHashMap<Type, (WasmLocalId, WasmLocalId)>,
}

impl CaptureFallbacks {
    fn expression_local(&self, expr: &ValueLayoutExpr) -> Option<WasmLocalId> {
        self.expressions
            .iter()
            .find_map(|(planned, local)| (planned == expr).then_some(*local))
    }
}

impl CaptureLayout {
    pub(super) fn needs_order_scratch(&self) -> bool {
        self.offsets.is_none()
    }
}

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
            ScalarType::in_env(
                declaration.methods[entry.1.as_index()].1.ty_scheme.ty.args[index].ty,
                &env,
            )?
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

fn field(code: &mut impl Instructions, base: WasmLocalId, offset: usize) {
    code.instruction(&I::LocalGet(base.as_u32()));
    code.instruction(&I::I32Load(MemArg {
        offset: offset as u64,
        ..memarg(2)
    }));
}

fn values(code: &mut impl Instructions, environment: WasmLocalId) {
    code.instruction(&I::LocalGet(environment.as_u32()));
    field(code, environment, offset_of!(Environment, values_offset));
    code.instruction(&I::I32Add);
}

fn dictionary(code: &mut impl Instructions, environment: WasmLocalId) {
    frame_address(
        code,
        environment,
        offset_of!(Environment, dictionary) as u32,
    );
}

/// Read an entry slot from the capture tuple's Value dictionary.
fn value_entry(
    code: &mut impl Instructions,
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

/// State needed to copy and clean up a callable's source captures.
struct CaptureState {
    frame: WasmLocalId,
    temporary: WasmLocalId,
    size: WasmLocalId,
    align: WasmLocalId,
    base: WasmLocalId,
    end: WasmLocalId,
    pending: Option<WasmLocalId>,
    methods: ValueMethods,
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
    let env = session
        .modules()
        .env_for(session.expect_fresh_module(target.module));
    let (index, direct) = callees[&target];
    let AdapterTarget {
        inputs: input_types,
        result: result_ty,
        optional,
    } = AdapterTarget::new(program, target, direct, env, session)?;
    let leading = captures
        .hidden
        .checked_add(captures.values)
        .ok_or("callable capture arity")?;
    let abi = abi(visible_arity(direct, captures)?);
    let mut locals = Vec::new();
    let mut local = |ty| {
        let id = WasmLocalId::from_index(abi.parameter_count() + locals.len());
        locals.push(ty);
        id
    };
    let environment = (leading != 0).then(|| local(ValType::I32));
    let status = direct.fallible.then(|| local(ValType::I32));
    let optional_frame = optional.as_ref().map(|_| local(ValType::I32));
    let scratch = optional
        .as_ref()
        .filter(|adapter| adapter.needs_scratch())
        .map(|_| local(ValType::I32));
    let capture_state = (captures.values != 0).then(|| CaptureState {
        frame: local(ValType::I32),
        temporary: local(ValType::I32),
        size: local(ValType::I32),
        align: local(ValType::I32),
        base: local(ValType::I32),
        pending: status.map(|_| local(ValType::I32)),
        // Keep the wide allocation helper last so declarations form at most two type groups.
        end: local(ValType::I64),
        methods: entries
            .value_methods
            .expect("value captures require callable Value methods"),
    });
    let mut code = WasmFunction::new_with_locals_types(locals);
    if let Some(environment) = environment {
        code.instruction(&I::LocalGet(abi.input_local(0).as_u32()));
        code.instruction(&I::LocalSet(environment.as_u32()));
    }
    if let Some(capture) = &capture_state {
        let environment = environment.unwrap();
        code.instruction(&I::GlobalGet(Global::Stack as u32));
        code.instruction(&I::LocalSet(capture.frame.as_u32()));
        field(&mut code, environment, offset_of!(Environment, values_size));
        code.instruction(&I::LocalSet(capture.size.as_u32()));
        field(
            &mut code,
            environment,
            offset_of!(Environment, values_align),
        );
        code.instruction(&I::LocalSet(capture.align.as_u32()));
        allocate_frame(
            &mut code,
            imports.failure_function(),
            capture.size,
            capture.align,
            capture.temporary,
            capture.end,
        );
        code.instruction(&I::Drop);
        dictionary(&mut code, environment);
        values(&mut code, environment);
        code.instruction(&I::LocalGet(capture.temporary.as_u32()));
        value_entry(
            &mut code,
            environment,
            capture.base,
            capture.methods.clone.entry,
        );
        code.instruction(&I::CallIndirect {
            type_index: capture.methods.clone.ty.as_u32(),
            table_index: 0,
        });
    }
    if let Some(optional) = &optional {
        enter_frame(
            &mut code,
            imports.failure_function(),
            optional_frame.unwrap(),
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
            frame_address(
                &mut code,
                environment.unwrap(),
                Environment::hidden_offset(i),
            );
        } else if i < leading {
            let capture = capture_state.as_ref().unwrap();
            code.instruction(&I::LocalGet(capture.temporary.as_u32()));
            field(
                &mut code,
                environment.unwrap(),
                Environment::capture_offset(captures.hidden, i - captures.hidden) as usize,
            );
            code.instruction(&I::I32Add);
        } else {
            code.instruction(&I::LocalGet(abi.input_local(i - leading + 1).as_u32()));
        }
        if matches!(transport, ParameterTransport::Direct(_)) {
            ScalarType::in_env(ty, &env)?.load(&mut code);
        }
    }
    if direct.output() {
        code.instruction(&I::LocalGet(
            optional_frame
                .unwrap_or_else(|| abi.output_local())
                .as_u32(),
        ));
    }
    code.instruction(&I::Call(index.as_u32()));
    if let Some(status) = status {
        code.instruction(&I::LocalSet(status.as_u32()));
    } else if let Some(optional) = optional {
        optional.emit(
            &mut code,
            abi.output_local(),
            optional_frame.unwrap(),
            scratch,
            imports.function_index("alloc"),
        );
        leave_frame(&mut code, optional_frame.unwrap());
    } else if matches!(direct.result, ResultKind::Direct(_)) {
        ScalarType::in_env(result_ty, &env)?.store(&mut code);
    }
    if let Some(capture) = &capture_state {
        let environment = environment.unwrap();
        // Detach the call's diagnostic before invoking guest cleanup, so a trap during drop
        // preserves the original cause in the invocation's pending-failure stack.
        if let Some(status) = status {
            code.instruction(&I::LocalGet(status.as_u32()));
            code.instruction(&I::If(BlockType::Empty));
            context_pointer(&mut code, offset_of!(InvocationState, diagnostics));
            code.instruction(&I::I32Const(0));
            code.instruction(&I::Call(imports.function_index("capture_failure").as_u32()));
            code.instruction(&I::LocalSet(capture.pending.unwrap().as_u32()));
            code.instruction(&I::End);
        }
        dictionary(&mut code, environment);
        code.instruction(&I::LocalGet(capture.temporary.as_u32()));
        code.instruction(&I::LocalGet(capture.temporary.as_u32())); // Unit result, no bytes written.
        value_entry(
            &mut code,
            environment,
            capture.base,
            capture.methods.drop.entry,
        );
        code.instruction(&I::CallIndirect {
            type_index: capture.methods.drop.ty.as_u32(),
            table_index: 0,
        });
        leave_frame(&mut code, capture.frame);
        if let Some(status) = status {
            code.instruction(&I::LocalGet(status.as_u32()));
            code.instruction(&I::If(BlockType::Empty));
            context_pointer(&mut code, offset_of!(InvocationState, diagnostics));
            code.instruction(&I::LocalGet(capture.pending.unwrap().as_u32()));
            code.instruction(&I::Call(
                imports.function_index("propagate_failure").as_u32(),
            ));
            code.instruction(&I::If(BlockType::Empty));
            code.instruction(&I::Unreachable);
            code.instruction(&I::End);
            code.instruction(&I::End);
        }
    }
    if let Some(status) = status {
        code.instruction(&I::LocalGet(status.as_u32()));
    } else {
        // Uniform callable entries return a status even when the direct target is infallible.
        code.instruction(&I::I32Const(0));
    }
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
        let scratch = self.helper_locals().get(Scratch);
        self.i(I::I32Const(0));
        self.i(I::I32Const(1));
        self.i(I::I32Const(1));
        self.i(I::I32Const(0));
        self.i(I::Call(
            self.imports
                .function_index("allocate_callable_environment")
                .as_u32(),
        ));
        self.i(I::LocalSet(scratch.as_u32()));
        frame_address(&mut self.code, scratch, Environment::hidden_offset(0));
        self.address(source)?;
        self.i(I::I32Const(size_of::<DictionaryReference>() as i32));
        self.i(I::MemoryCopy {
            src_mem: 0,
            dst_mem: 0,
        });
        frame_address(&mut self.code, scratch, Environment::hidden_offset(0));
        self.i(I::Call(
            self.imports.function_index("retain_evidence").as_u32(),
        ));
        let offset = self.address_base(destination)?;
        self.i(I::I32Const(
            self.callable_entries.selected[&entry].as_u32() as i32
        ));
        self.i(I::I32Store(memarg_at(2, offset)));
        let offset = self.address_base(destination)?;
        self.i(I::LocalGet(scratch.as_u32()));
        self.i(I::I32Store(memarg_at(
            2,
            offset_sum(offset, ENVIRONMENT_OFFSET as u32)?,
        )));
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

    pub(super) fn plan_closure_captures(&self, op: &Operation) -> Result<CaptureLayout, String> {
        let captures = closure_value_captures(op);
        let capture_types = captures
            .iter()
            .map(|capture| {
                let MirType::Lowered(ty) = self.pointee_type(capture)? else {
                    return Err("pointer capture".into());
                };
                Ok(ty)
            })
            .collect::<Result<Vec<_>, String>>()?;
        let spec = if capture_types.is_empty() {
            ProductLayoutSpec {
                members: Vec::new(),
            }
        } else {
            product_layout_spec(Type::tuple(capture_types), op.span.location, &self.env)
                .ok_or("expected capture tuple layout")?
        };
        let offsets = spec.static_field_offsets();
        Ok(CaptureLayout {
            spec,
            offsets,
            fallbacks: CaptureFallbacks::default(),
        })
    }

    /// Run after dictionary definitions have been collected, and before local declarations.
    pub(super) fn plan_closure_layout_fallbacks(&mut self, op: &Operation) -> Result<(), String> {
        let id = op.result_id().unwrap();
        let Some(mut layout) = self.closure_layouts.remove(&id) else {
            return Ok(());
        };
        for member in &layout.spec.members {
            if member.static_layout.is_some()
                || self.capture_witness(member.ty, &op.operands).is_some()
                || layout.fallbacks.layouts.contains_key(&member.ty)
            {
                continue;
            }
            let formula = value_layout_formula_for_type(member.ty, op.span.location, &self.env)
                .map_err(|error| format!("closure capture layout: {error:?}"))?;
            let size =
                self.plan_capture_layout_expr(&formula.size, &op.operands, &mut layout.fallbacks)?;
            let align =
                self.plan_capture_layout_expr(&formula.align, &op.operands, &mut layout.fallbacks)?;
            layout.fallbacks.layouts.insert(member.ty, (size, align));
        }
        self.closure_layouts.insert(id, layout);
        Ok(())
    }

    fn plan_capture_layout_expr(
        &mut self,
        expr: &ValueLayoutExpr,
        operands: &[Value],
        plan: &mut CaptureFallbacks,
    ) -> Result<WasmLocalId, String> {
        if let Some(local) = plan.expression_local(expr) {
            return Ok(local);
        }
        let local = match expr {
            ValueLayoutExpr::AssociatedConst { ty, index } => {
                let (size, align) = if let Some((_, _, size, align)) =
                    plan.leaves.iter().find(|(leaf, ..)| leaf == ty)
                {
                    (*size, *align)
                } else {
                    let witness = self.capture_witness(*ty, operands).ok_or_else(|| {
                        format!("missing explicit closure capture layout for {ty:?}")
                    })?;
                    let size = self.local(ValType::I32);
                    let align = self.local(ValType::I32);
                    plan.leaves.push((*ty, witness, size, align));
                    (size, align)
                };
                if *index == VALUE_SIZE_ASSOC_CONST_INDEX {
                    size
                } else {
                    align
                }
            }
            ValueLayoutExpr::Constant(_) => self.local(ValType::I32),
            ValueLayoutExpr::Add(left, right)
            | ValueLayoutExpr::Max(left, right)
            | ValueLayoutExpr::AlignTo(left, right) => {
                self.plan_capture_layout_expr(left, operands, plan)?;
                self.plan_capture_layout_expr(right, operands, plan)?;
                self.local(ValType::I32)
            }
        };
        plan.expressions.push((expr.clone(), local));
        Ok(local)
    }

    fn closure_capture_layout(
        &mut self,
        member: ProductMemberLayout,
        operands: &[Value],
        fallbacks: &CaptureFallbacks,
    ) -> Result<(), String> {
        let helpers = self.helper_locals();
        if let Some(layout) = member.static_layout {
            self.i(I::I32Const(layout.size as i32));
            self.i(I::LocalSet(helpers.get(DynamicSize).as_u32()));
            self.i(I::I32Const(layout.align as i32));
            self.i(I::LocalSet(helpers.get(DynamicAlign).as_u32()));
            Ok(())
        } else if let Some(witness) = self.capture_witness(member.ty, operands) {
            self.dynamic_layout(&witness)
        } else {
            let (size, align) = fallbacks.layouts[&member.ty];
            self.i(I::LocalGet(size.as_u32()));
            self.i(I::LocalGet(align.as_u32()));
            self.i(I::LocalSet(helpers.get(DynamicAlign).as_u32()));
            self.i(I::LocalSet(helpers.get(DynamicSize).as_u32()));
            Ok(())
        }
    }

    fn emit_capture_layout_fallbacks(&mut self, plan: &CaptureFallbacks) -> Result<(), String> {
        let helpers = self.helper_locals();
        for (_, witness, size, align) in &plan.leaves {
            self.dynamic_layout(witness)?;
            self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
            self.i(I::LocalSet(size.as_u32()));
            self.i(I::LocalGet(helpers.get(DynamicAlign).as_u32()));
            self.i(I::LocalSet(align.as_u32()));
        }
        // Postorder planning gives each expression already-computed operands. Shared
        // subtrees and evidence leaves are evaluated once per closure construction.
        for (expr, result) in &plan.expressions {
            let operand = |expr| plan.expression_local(expr).unwrap().as_u32();
            match expr {
                ValueLayoutExpr::Constant(value) => self.i(I::I32Const(*value as i32)),
                ValueLayoutExpr::AssociatedConst { .. } => continue,
                ValueLayoutExpr::Add(left, right) => {
                    self.i(I::LocalGet(operand(left)));
                    self.i(I::LocalGet(operand(right)));
                    self.i(I::I32Add);
                }
                ValueLayoutExpr::Max(left, right) => {
                    self.i(I::LocalGet(operand(left)));
                    self.i(I::LocalGet(operand(right)));
                    self.i(I::LocalGet(operand(left)));
                    self.i(I::LocalGet(operand(right)));
                    self.i(I::I32GtU);
                    self.i(I::Select);
                }
                ValueLayoutExpr::AlignTo(offset, align) => {
                    self.i(I::LocalGet(operand(offset)));
                    self.i(I::LocalGet(operand(align)));
                    self.i(I::I32Const(1));
                    self.i(I::I32Sub);
                    self.i(I::I32Add);
                    self.i(I::I32Const(0));
                    self.i(I::LocalGet(operand(align)));
                    self.i(I::I32Sub);
                    self.i(I::I32And);
                }
            }
            self.i(I::LocalSet(result.as_u32()));
        }
        Ok(())
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
        let captures = closure_value_captures(op);
        assert!(
            has_env_dict || captures.is_empty(),
            "closure value captures require a Value dictionary"
        );
        let result = Value::Register(op.result_id().unwrap());
        let offset = self.address_base(&result)?;
        self.i(I::I32Const(
            self.callable_entries.slots[&function].as_u32() as i32
        ));
        self.i(I::I32Store(memarg_at(2, offset)));
        if hidden == 0 && captures.is_empty() {
            let offset = self.address_base(&result)?;
            self.i(I::I32Const(0));
            self.i(I::I32Store(memarg_at(
                2,
                offset_sum(offset, ENVIRONMENT_OFFSET as u32)?,
            )));
            return Ok(());
        }
        let helpers = self.helper_locals();
        let (environment, cursor) = self.callable_locals.expect("closure construction locals");
        if has_env_dict {
            self.dynamic_layout(&op.operands[end])?;
            self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
            self.i(I::LocalGet(helpers.get(DynamicAlign).as_u32()));
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
        let offset = self.address_base(&result)?;
        self.i(I::LocalGet(environment.as_u32()));
        self.i(I::I32Store(memarg_at(
            2,
            offset_sum(offset, ENVIRONMENT_OFFSET as u32)?,
        )));
        for index in 0..hidden + usize::from(has_env_dict) {
            let (offset, value) = if index == hidden {
                (
                    offset_of!(Environment, dictionary) as u32,
                    &op.operands[end],
                )
            } else {
                (Environment::hidden_offset(index), &op.operands[index])
            };
            if matches!(
                self.roles.get(value, self.body.constants()).as_deref(),
                Some(ValueRole::VariantPayloadStorage)
            ) || matches!(self.roles.get(value, self.body.constants()).as_deref(),
                Some(ValueRole::Materialized(MirType::Lowered(ty))) if *ty == bool_type())
                || matches!(value, Value::Parameter(id) if self.body.parameters()[id.as_index()].ty == bool_type())
            {
                self.i(I::LocalGet(environment.as_u32()));
                self.read(value)?;
                self.i(I::I32Store8(memarg_at(0, offset)));
            } else {
                frame_address(&mut self.code, environment, offset);
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
        if captures.is_empty() {
            return Ok(());
        }
        let layout = self
            .closure_layouts
            .remove(&op.result_id().unwrap())
            .expect("each closure is emitted once after layout planning");
        let spec = &layout.spec;
        let static_offsets = &layout.offsets;
        self.emit_capture_layout_fallbacks(&layout.fallbacks)?;
        for (index, capture) in captures.iter().enumerate() {
            let target = ProjectionIndex::from_index(index);
            let member = spec.members[index];
            if let Some(offsets) = static_offsets {
                self.i(I::I32Const(offsets[index] as i32));
                self.i(I::LocalSet(cursor.as_u32()));
                self.closure_capture_layout(member, &op.operands, &layout.fallbacks)?;
            } else {
                self.i(I::I32Const(
                    spec.static_prefix_offset(target).unwrap_or(0) as i32
                ));
                self.i(I::LocalSet(cursor.as_u32()));
                self.closure_capture_layout(member, &op.operands, &layout.fallbacks)?;
                self.i(I::LocalGet(helpers.get(DynamicAlign).as_u32()));
                self.i(I::LocalSet(helpers.get(Scratch).as_u32()));
                // DynamicBase temporarily holds the target size; candidate layout queries
                // overwrite DynamicSize/Align but leave this local intact.
                self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
                self.i(I::LocalSet(helpers.get(DynamicBase).as_u32()));
                for (candidate_index, equal_precedes) in spec.runtime_order_candidates(target) {
                    let candidate = spec.members[candidate_index.as_index()];
                    self.closure_capture_layout(candidate, &op.operands, &layout.fallbacks)?;
                    self.i(I::LocalGet(helpers.get(DynamicAlign).as_u32()));
                    self.i(I::LocalGet(helpers.get(Scratch).as_u32()));
                    self.i(if equal_precedes { I::I32GeU } else { I::I32GtU });
                    self.i(I::If(BlockType::Empty));
                    self.i(I::LocalGet(cursor.as_u32()));
                    self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
                    self.i(I::I32Add);
                    self.i(I::LocalSet(cursor.as_u32()));
                    self.i(I::End);
                }
                self.i(I::LocalGet(helpers.get(DynamicBase).as_u32()));
                self.i(I::LocalSet(helpers.get(DynamicSize).as_u32()));
            }
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
            self.i(I::LocalGet(helpers.get(DynamicSize).as_u32()));
            self.i(I::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            });
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
            ParameterKind,
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
                // Assigned twice, so the function value keeps its cell and its destructor.
                "fn identity(x: int) -> int { x } \
                 fn compute(x: int) -> int { let mut f = identity; if x > 0 { f = identity }; f(x) }",
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
