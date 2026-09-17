// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Closed scalar physical MIR to core Wasm. A dispatcher preserves arbitrary MIR control flow.

use std::mem::offset_of;

use strum::{EnumIter, IntoEnumIterator};
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, EntityType, ExportKind, ExportSection,
    Function as WasmFunction, FunctionSection, GlobalSection, GlobalType, ImportSection,
    Instruction as I, MemArg, MemoryType, Module, TypeSection, ValType,
};

use crate::{
    FxHashMap, FxHashSet,
    hir::{
        function::ArgConvention,
        native_functions::{
            NativeFailureConvention, NativeParameter, NativeResult, NativeScalar, NativeSignature,
        },
        value::LiteralValue,
    },
    mir::{
        BlockId, Function, Operation, OperationKind, ParameterId, ParameterKind, Value, ValueId,
        operation::OperationKindDiscriminant,
        physical::program::ResolvedPhysicalProgram,
        role::{MirType, ValueRole, ValueRoles},
        terminator::TerminatorKind,
        value::ConstantId,
    },
    module::{FunctionId, id::Id},
    std::math::Float,
    types::r#type::{CallResultConvention, Type, TypeKind},
};

use super::{
    IMPORT_MODULE, Imports, MEMORY_IMPORT,
    execution::{FailureCode, InvocationState},
    scalar_type,
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

#[derive(Clone)]
struct Signature {
    parameters: Vec<(ScalarType, ParameterTransport)>,
    result: Option<ScalarType>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ParameterTransport {
    Direct,
    Indirect,
}

impl Signature {
    fn of(body: &Function) -> Result<Self, String> {
        // Physical verification guarantees a trailing Return (or none for NoValue). With evidence
        // and owned parameters rejected below, MIR input indexes are exactly Wasm local indexes.
        if !matches!(
            body.result_convention(),
            CallResultConvention::Value | CallResultConvention::NoValue
        ) {
            return Err("scoped or addressor result convention".into());
        }
        let mut parameters = Vec::new();
        let mut result = None;
        for parameter in body.parameters() {
            let ty = ScalarType::of(parameter.ty)?;
            match parameter.kind {
                ParameterKind::Return => result = Some(ty),
                ParameterKind::Parameter(mode) => {
                    let transport = if mode == ArgConvention::Let && !ty.is::<()>() {
                        ParameterTransport::Direct
                    } else {
                        ParameterTransport::Indirect
                    };
                    parameters.push((ty, transport));
                }
                _ => return Err("owned or evidence parameters".into()),
            }
        }
        Ok(Self { parameters, result })
    }

    fn params(&self) -> impl ExactSizeIterator<Item = ValType> + '_ {
        self.parameters
            .iter()
            .map(|(ty, transport)| match transport {
                ParameterTransport::Direct => ty.wasm(),
                ParameterTransport::Indirect => ValType::I32,
            })
    }

    fn results(&self) -> impl ExactSizeIterator<Item = ValType> {
        self.result
            .filter(|ty| !ty.is::<()>())
            .map(ScalarType::wasm)
            .into_iter()
    }
}

pub(super) struct Emitted {
    pub bytes: Vec<u8>,
    pub parameters: Vec<ScalarType>,
    pub result: ScalarType,
}

pub(super) fn emit(
    program: &ResolvedPhysicalProgram<'_>,
    entry: FunctionId,
    imports: &mut Imports,
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
        let signature = Signature::of(body).map_err(|reason| diagnostic(id, body, &reason))?;
        for block in body.blocks() {
            let block = body.block(block);
            if !matches!(
                block.terminator().kind,
                TerminatorKind::Goto { .. }
                    | TerminatorKind::CondBr { .. }
                    | TerminatorKind::Return
                    | TerminatorKind::InvariantFailure { .. }
            ) {
                return Err(diagnostic(
                    id,
                    body,
                    "unsupported terminator (source failure, variant switch or yield)",
                ));
            }
            for operation in block.operations() {
                if let OperationKind::Call { ty, .. } = &operation.kind {
                    let Value::Function(mut target) = operation.operands[0] else {
                        return Err(diagnostic(id, body, "indirect call"));
                    };
                    if ty.result_convention == CallResultConvention::NoValue {
                        target = program.direct_entry(target);
                    }
                    if program.function(target).is_some() {
                        pending.push(target);
                    } else {
                        let native = program
                            .module(target.module)
                            .and_then(|m| m.native_entry(target))
                            .ok_or_else(|| diagnostic(id, body, "missing native entry"))?;
                        let sig = native.signature();
                        if sig.failure != NativeFailureConvention::Infallible
                            || !matches!(sig.result, NativeResult::Scalar(..) | NativeResult::Unit)
                        {
                            return Err(diagnostic(
                                id,
                                body,
                                &format!("unsupported native contract {target:?}"),
                            ));
                        }
                        let index = imports
                            .add_native(target, native)
                            .map_err(|error| format!("native linkage {target:?}: {error:?}"))?;
                        natives.insert(target, (index, sig.clone()));
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
    let mut functions = FunctionSection::new();
    let mut code = CodeSection::new();
    for (id, body, signature) in &bodies {
        functions.function(types.len());
        types.ty().function(signature.params(), signature.results());
        let emitted = Body::new(body, signature, &indices, &natives, program)
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
    exports.export("entry", ExportKind::Func, indices[&entry].0);
    // Rust calls this setter directly at invocation boundaries. All state and diagnostics stay
    // in shared memory; no language values or per-call state are passed through JavaScript.
    let setup_index = imports.functions().len() as u32 + bodies.len() as u32;
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
    let signature = &indices[&entry].1;
    Ok(Emitted {
        bytes: module.finish(),
        parameters: signature.parameters.iter().map(|(ty, _)| *ty).collect(),
        result,
    })
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
    signature: &'a Signature,
    roles: ValueRoles,
    functions: &'a FxHashMap<FunctionId, (u32, Signature)>,
    natives: &'a FxHashMap<FunctionId, (u32, NativeSignature)>,
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
        signature: &'a Signature,
        functions: &'a FxHashMap<FunctionId, (u32, Signature)>,
        natives: &'a FxHashMap<FunctionId, (u32, NativeSignature)>,
        program: &'a ResolvedPhysicalProgram<'a>,
    ) -> Result<Self, String> {
        let mut this = Self {
            body,
            signature,
            functions,
            natives,
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
            if addressed.contains(&value) {
                this.slot(value, ScalarType::of(constant.ty)?.size());
            }
        }
        for (index, parameter) in body.parameters().iter().enumerate() {
            if parameter.kind == ParameterKind::Return
                || signature
                    .parameters
                    .get(index)
                    .is_some_and(|(_, transport)| *transport == ParameterTransport::Direct)
            {
                let value = Value::Parameter(ParameterId::from_index(index));
                let ty = ScalarType::of(parameter.ty)?;
                if addressed.contains(&value) {
                    this.slot(value, ty.size());
                } else {
                    let local = if parameter.kind == ParameterKind::Return {
                        this.local(ty.wasm())
                    } else {
                        index as u32 // Direct parameters already occupy a Wasm local.
                    };
                    this.storage.insert(value, Storage::Local(local));
                }
            }
        }
        for block in body.blocks() {
            for operation in body.block(block).operations() {
                if let Some(id) = operation.result_id() {
                    let storage_ty = match &operation.kind {
                        OperationKind::Alloca { ty } if operation.operands.is_empty() => {
                            Some(ScalarType::of(*ty)?)
                        }
                        OperationKind::AllocaPlace { .. } => Some(ScalarType::pointer()),
                        _ => None,
                    };
                    if let Some(ty) = storage_ty {
                        let value = Value::Register(id);
                        if addressed.contains(&value) {
                            this.slot(value, ty.size());
                        } else {
                            let local = this.local(ty.wasm());
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
                        ValueRole::Materialized(ty) => scalar(ty)?.wasm(),
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

    fn local(&mut self, ty: ValType) -> u32 {
        let id = self.signature.parameters.len() as u32 + self.locals.len() as u32;
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
            for op in block.operations() {
                for (index, operand) in op.operands.iter().enumerate() {
                    let observes = match &op.kind {
                        OperationKind::Load | OperationKind::Clear => false,
                        OperationKind::Store if index == 1 => false,
                        OperationKind::Store => self
                            .roles
                            .get(operand, self.body.constants())
                            .is_some_and(|role| role.is_place_operand()),
                        OperationKind::Memcpy
                        | OperationKind::Move
                        | OperationKind::MoveBytes { .. } => false,
                        OperationKind::CompareEqual => false,
                        OperationKind::AddressOffset { .. }
                        | OperationKind::AddressOffsetPlace { .. }
                            if index == 1 =>
                        {
                            false
                        }
                        OperationKind::Call { ty, .. } => {
                            if index != 0
                                && index + 1 == op.operands.len()
                                && ty.result_convention.has_result_place()
                            {
                                false // Scalar results return directly, then write the destination.
                            } else if let (Some(Value::Function(target)), Some(input)) =
                                (op.operands.first(), index.checked_sub(1))
                            {
                                let target =
                                    if ty.result_convention == CallResultConvention::NoValue {
                                        self.program.direct_entry(*target)
                                    } else {
                                        *target
                                    };
                                if let Some((_, signature)) = self.functions.get(&target) {
                                    !signature.parameters.get(input).is_some_and(
                                        |(_, transport)| *transport == ParameterTransport::Direct,
                                    )
                                } else if let Some((_, signature)) = self.natives.get(&target) {
                                    !matches!(
                                        signature.parameters.get(input),
                                        Some(NativeParameter::Scalar(..))
                                    )
                                } else {
                                    true
                                }
                            } else {
                                true
                            }
                        }
                        _ => true,
                    };
                    if observes {
                        addressed.insert(operand.clone());
                    }
                }
            }
            if !matches!(block.terminator().kind, TerminatorKind::CondBr { .. }) {
                addressed.extend(block.terminator().operands().iter().cloned());
            }
        }
        addressed
    }

    fn slot(&mut self, value: Value, size: u32) {
        // All slots are 8-aligned, including distinct zero-sized places.
        self.storage.insert(value, Storage::Stack(self.frame_size));
        self.frame_size += (size.max(1) + 7) & !7;
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
        if self.storage.contains_key(value) && !matches!(value, Value::Constant(_)) {
            return self.address(value);
        }
        match value {
            Value::Register(id) => self.i(I::LocalGet(self.registers[id])),
            Value::Parameter(id) => self.i(I::LocalGet(id.as_u32())),
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
                self.address(&value)?;
                self.literal(&constant.representation)?;
                self.store(ScalarType::of(constant.ty)?);
            }
        }
        for (index, (ty, transport)) in self.signature.parameters.iter().enumerate() {
            let value = Value::Parameter(ParameterId::from_index(index));
            if *transport == ParameterTransport::Direct
                && matches!(self.storage.get(&value), Some(Storage::Stack(_)))
            {
                self.address(&value)?;
                self.i(I::LocalGet(index as u32));
                self.store(*ty);
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
            TerminatorKind::Return => {
                if let Some(frame) = self.frame {
                    self.i(I::LocalGet(frame));
                    self.i(I::GlobalSet(Global::Stack as u32));
                }
                self.i(I::GlobalGet(Global::Depth as u32));
                self.i(I::I32Const(1));
                self.i(I::I32Sub);
                self.i(I::GlobalSet(Global::Depth as u32));
                if let Some(ty) = self.signature.result.filter(|ty| !ty.is::<()>()) {
                    self.load_place(
                        &Value::Parameter(ParameterId::from_index(
                            self.body.parameters().len() - 1,
                        )),
                        ty,
                    )?;
                }
                self.i(I::Return);
            }
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
                self.load_place(&args[0], self.pointee(&args[0])?)?;
            }
            Store => {
                // Store takes a materialized value, including a pointer; it must not dereference
                // a place operand as read() would. The MIR verifier checks this operand contract.
                let ty = self.pointee(&args[1])?;
                self.prepare_store(&args[1])?;
                self.value(&args[0])?;
                self.finish_store(&args[1], ty);
            }
            Memcpy | Move | MoveBytes { .. } => {
                if args.len() > 2 && !matches!(op.kind, MoveBytes { .. }) {
                    return Err("layout evidence".into());
                }
                let ty = self.pointee(&args[1])?;
                if matches!(op.kind, MoveBytes { .. }) {
                    self.read(&args[2])?;
                    self.i(I::I32Const(ty.size() as i32));
                    self.i(I::I32Ne);
                    self.i(I::If(BlockType::Empty));
                    self.fail(FailureCode::Invariant);
                    self.i(I::End);
                }
                self.prepare_store(&args[1])?;
                self.read(&args[0])?;
                self.finish_store(&args[1], ty);
            }
            AddressOffset { .. } | AddressOffsetPlace { .. } => {
                self.address(&args[0])?;
                self.read(&args[1])?;
                self.i(I::I32Add);
            }
            Clear | StackRestore => (), // Scalar storage is reserved for the whole frame; no destructor or escaping views.
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
            Call { ty, .. } => {
                let Value::Function(mut target) = args[0] else {
                    return Err("indirect call".into());
                };
                if ty.result_convention == CallResultConvention::NoValue {
                    target = self.program.direct_entry(target);
                }
                let output = ty
                    .result_convention
                    .has_result_place()
                    .then(|| args.last().unwrap());
                if let Some((index, signature)) = self.functions.get(&target) {
                    if args.len() != 1 + signature.parameters.len() + usize::from(output.is_some())
                    {
                        return Err("hidden call evidence".into());
                    }
                    let result = signature.result.filter(|ty| !ty.is::<()>());
                    if result.is_some() {
                        self.prepare_store(output.ok_or("missing call result")?)?;
                    }
                    for ((_, transport), argument) in signature.parameters.iter().zip(&args[1..]) {
                        match transport {
                            ParameterTransport::Direct => {
                                self.read(argument)?;
                            }
                            ParameterTransport::Indirect => self.address(argument)?,
                        }
                    }
                    self.i(I::Call(*index));
                    if let Some(result) = result {
                        self.finish_store(output.unwrap(), result);
                    }
                } else {
                    let (index, sig) = self.natives.get(&target).ok_or("unresolved callee")?;
                    if args.len() != sig.parameters.len() + 2 {
                        return Err("native hidden arguments".into());
                    }
                    let result = match sig.result {
                        NativeResult::Scalar(_, scalar) => Some(ScalarType::native(scalar)),
                        _ => None,
                    };
                    if result.is_some() {
                        self.prepare_store(output.ok_or("missing native result")?)?;
                    }
                    for (parameter, argument) in sig.parameters.iter().zip(&args[1..]) {
                        // Reject non-scalar native storage even for a shared pointer: the subset's
                        // frame does not contain managed/native aggregates.
                        if matches!(parameter, NativeParameter::Scalar(..)) {
                            self.read(argument)?;
                        } else {
                            self.pointee(argument)?;
                            self.address(argument)?;
                        }
                    }
                    self.i(I::Call(*index));
                    if let Some(result) = result {
                        self.finish_store(output.unwrap(), result);
                    }
                }
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
