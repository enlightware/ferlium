// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Concrete physical MIR to core Wasm. A dispatcher preserves arbitrary MIR control flow.

use std::mem::offset_of;

use strum::{EnumIter, IntoEnumIterator};
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, EntityType, ExportKind, ExportSection,
    Function as WasmFunction, FunctionSection, GlobalSection, GlobalType, ImportSection,
    Instruction as I, MemArg, MemoryType, Module, TypeSection, ValType,
};

use crate::{
    CompilerSession, FxHashMap, FxHashSet, Location,
    hir::{
        function::ArgConvention,
        native_functions::{NativeResult, NativeScalar},
        value::LiteralValue,
    },
    mir::{
        BasicBlock, BlockId, Function, Operation, OperationKind, ParameterId, ParameterKind, Value,
        ValueId,
        operation::OperationKindDiscriminant,
        physical::program::ResolvedPhysicalProgram,
        role::{MirType, ValueRole, ValueRoles},
        terminator::TerminatorKind,
        value::ConstantId,
    },
    module::{FunctionId, ModuleEnv, ProjectionIndex, id::Id},
    std::{
        math::Float,
        string::StaticStr,
        value::{product_layout_spec, value_layout_for_type},
    },
    types::{
        r#type::{CallResultConvention, Type, TypeKind},
        type_like::TypeLike,
    },
};

use super::{
    IMPORT_MODULE, Imports, MEMORY_IMPORT,
    abi::{CallAbi, Parameter as ParameterTransport, ResultKind, scalar_type},
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
        CallResultConvention::Value | CallResultConvention::NoValue
    ) {
        return Err("scoped or addressor result convention".into());
    }
    let mut parameters = Vec::new();
    let mut result = None;
    for parameter in body.parameters() {
        if !parameter.ty.is_constant() {
            return Err("generic storage or evidence".into());
        }
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
            ParameterKind::Dictionary => return Err("generic evidence".into()),
        }
    }
    let result_kind = match result {
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
    let mut pending = vec![entry];
    let mut seen = FxHashSet::default();
    let mut bodies = Vec::new();
    let mut natives = FxHashMap::default();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        let body = program
            .function(id)
            .ok_or_else(|| format!("missing script entry {id:?}"))?;
        let signature = script_abi(body).map_err(|reason| diagnostic(id, body, &reason))?;
        for block in body.blocks() {
            let block = body.block(block);
            if !matches!(
                block.terminator().kind,
                TerminatorKind::Goto { .. }
                    | TerminatorKind::CondBr { .. }
                    | TerminatorKind::Invoke { .. }
                    | TerminatorKind::PropagateError
                    | TerminatorKind::FailureDuringCleanup
                    | TerminatorKind::Return
                    | TerminatorKind::InvariantFailure { .. }
            ) {
                return Err(diagnostic(
                    id,
                    body,
                    "unsupported terminator (variant switch or yield)",
                ));
            }
            for operation in operations(block) {
                if let Some(callee) = callee(operation) {
                    let Value::Function(mut target) = callee else {
                        return Err(diagnostic(id, body, "indirect call"));
                    };
                    target = program.direct_entry(target);
                    if program.function(target).is_some() {
                        pending.push(target);
                    } else {
                        let native = program
                            .module(target.module)
                            .and_then(|m| m.native_entry(target))
                            .ok_or_else(|| diagnostic(id, body, "missing native entry"))?;
                        let sig = native.signature();
                        if matches!(
                            sig.result,
                            NativeResult::Optional { .. } | NativeResult::Addressor { .. }
                        ) {
                            return Err(diagnostic(
                                id,
                                body,
                                "optional or addressor native result",
                            ));
                        }
                        let index = imports
                            .add_native(target, native)
                            .map_err(|error| format!("native linkage {target:?}: {error:?}"))?;
                        let abi = CallAbi::native(sig)
                            .map_err(|reason| format!("native {target:?}: {reason}"))?;
                        natives.insert(target, (index, abi));
                    }
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
    let mut strings = Vec::new();
    for (id, body, signature) in &bodies {
        functions.function(types.len());
        types.ty().function(signature.params(), signature.results());
        let emitted = Body::new(
            body,
            signature,
            &callees,
            program,
            session
                .modules()
                .env_for(session.expect_fresh_module(id.module)),
            imports,
            &mut strings,
        )
        .and_then(Body::emit)
        .map_err(|reason| diagnostic(*id, body, &reason))?;
        code.function(&emitted);
    }
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
    let mut setup_index = imports.functions().len() as u32 + bodies.len() as u32;
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
        .section(&globals)
        .section(&exports)
        .section(&code);
    Ok(Emitted {
        bytes: module.finish(),
        parameters: host_parameters,
        strings: strings.into_boxed_slice(),
        result,
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

fn callee(op: &Operation) -> Option<Value> {
    match &op.kind {
        OperationKind::Call { .. } => Some(op.operands[0].clone()),
        OperationKind::Clone { .. } => Some(op.operands[2].clone()),
        OperationKind::Drop { .. } => Some(op.operands[1].clone()),
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
    pending_failure: u32,
    scratch: u32,
    replacements: FxHashMap<Type, u32>,
    callees: &'a FxHashMap<FunctionId, (u32, CallAbi)>,
    program: &'a ResolvedPhysicalProgram<'a>,
    registers: FxHashMap<ValueId, u32>,
    storage: FxHashMap<Value, Storage>,
    locals: Vec<ValType>,
    frame: Option<u32>,
    pc: Option<u32>,
    frame_size: u32,
    code: WasmFunction,
}

impl<'a> Body<'a> {
    fn new(
        body: &'a Function,
        signature: &'a CallAbi,
        callees: &'a FxHashMap<FunctionId, (u32, CallAbi)>,
        program: &'a ResolvedPhysicalProgram<'a>,
        env: ModuleEnv<'a>,
        imports: &'a Imports,
        strings: &'a mut Vec<StaticStr>,
    ) -> Result<Self, String> {
        let mut this = Self {
            body,
            signature,
            env,
            imports,
            strings,
            pending_failure: 0,
            scratch: 0,
            replacements: FxHashMap::default(),
            callees,
            program,
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
                let ty = ScalarType::of(parameter.ty)?;
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
                if matches!(operation.kind, OperationKind::Replace) {
                    let MirType::Lowered(ty) = this.pointee_type(&operation.operands[0])? else {
                        return Err("pointer replacement".into());
                    };
                    if !this.replacements.contains_key(&ty) {
                        let offset = this.frame_size;
                        let size = this.size(&MirType::Lowered(ty))?;
                        this.frame_size = this
                            .frame_size
                            .checked_add(size.max(1).checked_add(7).ok_or("frame overflow")? & !7)
                            .ok_or("frame overflow")?;
                        this.replacements.insert(ty, offset);
                    }
                }
                if let Some(id) = operation.result_id() {
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
                        .unwrap();
                    let ty = match &*role {
                        ValueRole::Place(_) | ValueRole::StackMarker => ValType::I32,
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
                if !ty.is_constant() {
                    return Err("open storage layout".into());
                }
                let layout = value_layout_for_type(*ty, Location::new_synthesized(), &self.env)
                    .map_err(|e| format!("Wasm storage layout: {e:?}"))?;
                if layout.align > 8 {
                    return Err("Wasm frame alignment above eight bytes".into());
                }
                Ok(layout.size)
            }
        }
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
            self.load_place(
                &Value::Parameter(ParameterId::from_index(self.body.parameters().len() - 1)),
                ScalarType::of(self.body.parameters().last().unwrap().ty)?,
            )?;
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
        let Value::Function(mut target) = callee else {
            return Err("indirect lifecycle call".into());
        };
        // Static calls can bypass fixed Value adapters: an elided result has no bytes to write.
        // This also avoids charging an adapter as an additional source call-depth frame.
        target = self.program.direct_entry(target);
        let (index, abi) = self
            .callees
            .get(&target)
            .cloned()
            .ok_or("unresolved callee")?;
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
            OperationKind::Drop { .. } => (
                op.operands[2..].iter().chain([&op.operands[0]]).collect(),
                None,
            ),
            _ => unreachable!(),
        };
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
        if abi.output() {
            self.address(output.ok_or("missing output storage")?)?;
        }
        self.i(I::Call(index));
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
        self.storage.insert(value, Storage::Stack(self.frame_size));
        self.frame_size = self
            .frame_size
            .checked_add(size.max(1).checked_add(7).ok_or("frame size overflow")? & !7)
            .ok_or("frame size overflow")?;
        Ok(())
    }

    fn i(&mut self, instruction: I<'_>) {
        self.code.instruction(&instruction);
    }

    fn fail(&mut self, code: FailureCode) {
        // A host can reach the exported entry without installing an invocation. Trap without
        // touching low linear memory when there is no diagnostic destination.
        self.i(I::GlobalGet(Global::Context as u32));
        self.i(I::I32Eqz);
        self.i(I::If(BlockType::Empty));
        self.i(I::Unreachable);
        self.i(I::End);
        self.i(I::GlobalGet(Global::Context as u32));
        self.i(I::I32Const(code as i32));
        self.i(I::I32Store(MemArg {
            offset: offset_of!(InvocationState, failure) as u64,
            ..memarg(2)
        }));
        self.i(I::Unreachable);
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
        if self.storage.contains_key(value)
            && (!matches!(value, Value::Constant(_))
                || self.roles.get(value, self.body.constants()).is_some_and(
                    |r| matches!(&*r, ValueRole::Materialized(ty) if scalar(ty).is_err()),
                ))
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
        if let Some(value) = literal.as_primitive_ty::<isize>() {
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
                if args.len() > 2 && !matches!(op.kind, MoveBytes { .. }) {
                    return Err("layout evidence".into());
                }
                let ty = self.pointee_type(&args[1])?;
                if matches!(op.kind, MoveBytes { .. }) {
                    self.read(&args[2])?;
                    self.i(I::I32Const(self.size(&ty)? as i32));
                    self.i(I::I32Ne);
                    self.i(I::If(BlockType::Empty));
                    self.fail(FailureCode::Invariant);
                    self.i(I::End);
                }
                if let Ok(ty) = scalar(&ty) {
                    self.prepare_store(&args[1])?;
                    self.read(&args[0])?;
                    self.finish_store(&args[1], ty);
                } else {
                    self.address(&args[1])?;
                    self.address(&args[0])?;
                    self.i(I::I32Const(self.size(&ty)? as i32));
                    self.i(I::MemoryCopy {
                        src_mem: 0,
                        dst_mem: 0,
                    });
                }
            }
            Replace => {
                if args.len() != 2 {
                    return Err("replacement layout evidence".into());
                }
                let MirType::Lowered(ty) = self.pointee_type(&args[0])? else {
                    return Err("pointer replacement".into());
                };
                let offset = self.replacements[&ty];
                self.i(I::LocalGet(self.frame.unwrap()));
                self.i(I::I32Const(offset as i32));
                self.i(I::I32Add);
                self.i(I::LocalSet(self.scratch));
                let size = self.size(&MirType::Lowered(ty))?;
                self.i(I::LocalGet(self.scratch));
                self.address(&args[0])?;
                self.i(I::I32Const(size as i32));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&args[0])?;
                self.address(&args[1])?;
                self.i(I::I32Const(size as i32));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
                self.address(&args[1])?;
                self.i(I::LocalGet(self.scratch));
                self.i(I::I32Const(size as i32));
                self.i(I::MemoryCopy {
                    src_mem: 0,
                    dst_mem: 0,
                });
            }
            AddressOffset { .. } | AddressOffsetPlace { .. } => {
                self.address(&args[0])?;
                self.read(&args[1])?;
                self.i(I::I32Add);
            }
            Clear | StackRestore => (), // Lifetimes are explicit in MIR; backing frame bytes may remain stale after cleanup.
            StackSave => self.i(I::I32Const(0)),
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
            Call { .. } | Clone { .. } | Drop { .. } => self.call_operation(op, false)?,
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
