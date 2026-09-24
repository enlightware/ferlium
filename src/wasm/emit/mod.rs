// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Physical MIR to core Wasm, with structured regions and a dispatcher for arbitrary control flow.

mod adapters;
mod body;
mod callable;
mod control_flow;
mod expressions;
mod subscript;

use self::{
    adapters::{boxed_entry_wrapper, dictionary_adapter, entry_wrapper},
    body::{Body, BodyMode},
};

use std::{iter, mem::offset_of, ops::Range};

use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, ElementSection, Elements, EntityType, ExportKind,
    ExportSection, FuncType as WasmFuncType, Function as WasmFunction, FunctionSection,
    GlobalSection, GlobalType, ImportSection, Instruction as I, MemArg, MemoryType, Module,
    NameMap, NameSection, RefType, TableSection, TableType, TypeSection, ValType,
};

use crate::{
    CompilerSession, FxHashMap, FxHashSet, Location, MirOptimization,
    hir::{function::ArgConvention, native_functions::NativeScalar},
    mir::{
        BasicBlock, Function, Operation, OperationKind, ParameterKind, Value,
        pass::known_callee::KnownCallee,
        physical::{constructed_subscript_definitions, program::ResolvedPhysicalProgram},
        role::MirType,
        terminator::TerminatorKind,
    },
    module::{FunctionId, ModuleEnv, ModuleId, TraitDictionaryId, TraitId, id::Id},
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        logic::bool_type,
        math::{float_type, int_type},
        string::StaticStr,
        value::{
            VALUE_ALIGN_ASSOC_CONST_INDEX, VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX,
            VALUE_SIZE_ASSOC_CONST_INDEX,
        },
    },
    types::{
        effects::{EffType, Effect, PrimitiveEffect},
        mutability::MutType,
        r#trait::TraitDictionaryEntryIndex,
        r#type::{CallResultConvention, FnType, Type, TypeKind},
    },
};

use super::{
    IMPORT_MODULE, Imports, MEMORY_IMPORT,
    abi::{
        CallAbi, DispatchTableSlotId, Parameter as ParameterTransport, ResultKind, WasmFunctionId,
        WasmLocalId, WasmTypeId, scalar_type,
    },
    evidence::{self, DictionaryDescriptor, ReachableEvidence},
    execution::{FailureCode, InvocationState},
};

#[cfg(test)]
pub(super) fn operation_needs_helper_locals(operation: &Operation) -> bool {
    body::operation_needs_helper_locals(operation)
}

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
#[derive(Clone, Copy)]
#[repr(u32)]
enum Global {
    Context,
    Stack,
    End,
}

impl Global {
    fn name(self) -> &'static str {
        match self {
            Self::Context => "invocation_context",
            Self::Stack => "stack",
            Self::End => "stack_end",
        }
    }
}

const BASE_GLOBALS: [Global; 3] = [Global::Context, Global::Stack, Global::End];

#[derive(Clone, Copy)]
struct DepthGlobals {
    depth: u32,
    limit: u32,
}

#[derive(Clone, Copy)]
struct FuelGlobals {
    fuel: u32,
    enabled: u32,
}

#[derive(Clone, Copy)]
struct RuntimeGlobals {
    base: bool,
    depth: Option<DepthGlobals>,
    fuel: Option<FuelGlobals>,
    count: u32,
}

impl RuntimeGlobals {
    fn new(needs_base: bool, needs_depth: bool, needs_fuel: bool) -> Self {
        debug_assert!(!(needs_depth || needs_fuel) || needs_base);
        let mut count = u32::from(needs_base) * BASE_GLOBALS.len() as u32;
        let depth = needs_depth.then(|| {
            let globals = DepthGlobals {
                depth: count,
                limit: count + 1,
            };
            count += 2;
            globals
        });
        let fuel = needs_fuel.then(|| {
            let globals = FuelGlobals {
                fuel: count,
                enabled: count + 1,
            };
            count += 2;
            globals
        });
        Self {
            base: needs_base,
            depth,
            fuel,
            count,
        }
    }

    fn base(self) -> impl Iterator<Item = Global> {
        self.base.then_some(BASE_GLOBALS).into_iter().flatten()
    }
}

/// Module-wide structural interner for core-Wasm function types.
#[derive(Default)]
struct FunctionTypes {
    section: TypeSection,
    indices: FxHashMap<WasmFuncType, WasmTypeId>,
}

impl FunctionTypes {
    fn intern(
        &mut self,
        parameters: impl IntoIterator<Item = ValType>,
        results: impl IntoIterator<Item = ValType>,
    ) -> WasmTypeId {
        let ty = WasmFuncType::new(parameters, results);
        if let Some(&id) = self.indices.get(&ty) {
            return id;
        }
        let id = WasmTypeId::new(self.section.len());
        self.section.ty().func_type(&ty);
        self.indices.insert(ty, id);
        id
    }
}

/// Reserve dynamic frame storage without wrapping alignment or extent arithmetic.
fn allocate_frame(
    code: &mut WasmFunction,
    size: WasmLocalId,
    align: WasmLocalId,
    base: WasmLocalId,
    end: WasmLocalId,
) {
    // alignment = max(requested_alignment, 8), preserving alignment for callees' fixed frames.
    code.instruction(&I::LocalGet(align.as_u32()));
    code.instruction(&I::I32Const(8));
    code.instruction(&I::LocalGet(align.as_u32()));
    code.instruction(&I::I32Const(8));
    code.instruction(&I::I32GtU);
    code.instruction(&I::Select);
    code.instruction(&I::LocalSet(align.as_u32()));
    // base = align_up(stack_pointer, alignment).
    code.instruction(&I::GlobalGet(Global::Stack as u32));
    code.instruction(&I::I64ExtendI32U);
    code.instruction(&I::LocalGet(align.as_u32()));
    code.instruction(&I::I64ExtendI32U);
    code.instruction(&I::I64Const(1));
    code.instruction(&I::I64Sub);
    code.instruction(&I::I64Add);
    code.instruction(&I::I64Const(0));
    code.instruction(&I::LocalGet(align.as_u32()));
    code.instruction(&I::I64ExtendI32U);
    code.instruction(&I::I64Sub);
    code.instruction(&I::I64And);
    code.instruction(&I::LocalTee(end.as_u32()));
    code.instruction(&I::I32WrapI64);
    code.instruction(&I::LocalSet(base.as_u32()));
    // end = align_up(base + max(size, 1), 8), reserving a distinct address even for zero size.
    code.instruction(&I::LocalGet(end.as_u32()));
    code.instruction(&I::LocalGet(size.as_u32()));
    code.instruction(&I::I32Const(1));
    code.instruction(&I::LocalGet(size.as_u32()));
    code.instruction(&I::Select);
    code.instruction(&I::I64ExtendI32U);
    code.instruction(&I::I64Add);
    code.instruction(&I::I64Const(7));
    code.instruction(&I::I64Add);
    code.instruction(&I::I64Const(-8));
    code.instruction(&I::I64And);
    code.instruction(&I::LocalTee(end.as_u32()));
    // if end > stack_limit: fail(StackCapacity).
    code.instruction(&I::GlobalGet(Global::End as u32));
    code.instruction(&I::I64ExtendI32U);
    code.instruction(&I::I64GtU);
    code.instruction(&I::If(BlockType::Empty));
    emit_failure(code, FailureCode::StackCapacity);
    code.instruction(&I::End);
    // stack_pointer = end.
    code.instruction(&I::LocalGet(end.as_u32()));
    code.instruction(&I::I32WrapI64);
    code.instruction(&I::GlobalSet(Global::Stack as u32));
    // Leave base on the operand stack as the allocation result.
    code.instruction(&I::LocalGet(base.as_u32()));
}

fn value_transport(ty: Type) -> ParameterTransport {
    ScalarType::of(ty)
        .ok()
        .and_then(ScalarType::as_non_unit_native)
        .map_or(ParameterTransport::Indirect, |scalar| {
            ParameterTransport::Direct(scalar_type(scalar))
        })
}

/// Replace a dictionary pointer with its image-relative entry table's absolute address.
fn dictionary_table(code: &mut WasmFunction, evidence_base: WasmLocalId) {
    code.instruction(&I::I32Load(memarg(2)));
    code.instruction(&I::I32Const(2));
    code.instruction(&I::I32Shl);
    context_pointer(code, offset_of!(InvocationState, evidence));
    code.instruction(&I::LocalTee(evidence_base.as_u32()));
    code.instruction(&I::I32Add);
    code.instruction(&I::I32Load(memarg(2)));
    code.instruction(&I::LocalGet(evidence_base.as_u32()));
    code.instruction(&I::I32Add);
    code.instruction(&I::I32Load(MemArg {
        offset: offset_of!(DictionaryDescriptor, entries) as u64,
        ..memarg(2)
    }));
    code.instruction(&I::LocalGet(evidence_base.as_u32()));
    code.instruction(&I::I32Add);
}

fn script_abi(body: &Function) -> Result<CallAbi, String> {
    // Physical verification requires a unique trailing Return for Value, none for NoValue.
    // Thus MIR input indices also index abi.parameters; only the failure pointer shifts locals.
    let yielded = body.result_convention() == CallResultConvention::YIELDED_ONCE;
    if !matches!(
        body.result_convention(),
        CallResultConvention::Value
            | CallResultConvention::NoValue
            | CallResultConvention::ADDRESSOR_PLACE
            | CallResultConvention::YIELDED_ONCE
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
        _ if yielded => ResultKind::Output,
        Some(_) if body.result_convention() == CallResultConvention::ADDRESSOR_PLACE => {
            ResultKind::Direct(ScalarType::pointer().wasm())
        }
        None => ResultKind::Unit,
        Some(ty) if ty == Type::unit() || ty == Type::never() => ResultKind::Unit,
        Some(ty) => {
            ScalarType::of(ty).map_or(ResultKind::Output, |ty| ResultKind::Direct(ty.wasm()))
        }
    };
    let fallible = yielded
        || body.blocks().any(|id| {
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
    pub exports: Vec<HostExport>,
    pub evidence: evidence::Image,
    /// Dictionaries described in the evidence image, in image order.
    #[cfg_attr(not(feature = "wasm-text"), allow(dead_code))]
    pub dictionaries: Box<[TraitDictionaryId]>,
    /// Number of subscripts described in the evidence image.
    #[cfg_attr(not(feature = "wasm-text"), allow(dead_code))]
    pub subscript_count: usize,
    /// Source regions of the code generated for MIR operations and terminators.
    #[cfg_attr(not(feature = "wasm-text"), allow(dead_code))]
    pub source_map: Vec<CodeSourceMapEntry>,
}

/// A function exported to the Rust host binding.
pub(super) struct HostExport {
    pub function: FunctionId,
    pub name: String,
    pub kind: HostExportKind,
}

pub(super) enum HostExportKind {
    Scalar {
        parameters: Vec<ScalarType>,
        result: ScalarType,
    },
    Boxed {
        result: Type,
    },
}

/// The code generated for one MIR operation or terminator.
#[cfg_attr(not(feature = "wasm-text"), allow(dead_code))]
#[derive(Clone, Debug)]
pub(super) struct CodeSourceMapEntry {
    /// Index of the function body in the code section.
    pub body: usize,
    /// Byte range within that body, which starts with its local declarations.
    pub bytes: Range<usize>,
    pub span: Location,
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

/// The scalar host signature of a script function, or why the host binding cannot call it.
pub(super) fn host_signature(
    program: &ResolvedPhysicalProgram<'_>,
    function: FunctionId,
) -> Result<(Vec<ScalarType>, ScalarType), String> {
    let body = program
        .function(function)
        .ok_or_else(|| format!("missing script entry {function:?}"))?;
    if !matches!(
        body.result_convention(),
        CallResultConvention::Value | CallResultConvention::NoValue
    ) {
        return Err(diagnostic(
            function,
            body,
            "Wasm host binding requires a value result",
        ));
    }
    if body.parameters().iter().any(|p| {
        !matches!(
            p.kind,
            ParameterKind::Return | ParameterKind::Parameter(ArgConvention::Let)
        )
    }) {
        return Err(diagnostic(
            function,
            body,
            "Wasm host binding requires by-value arguments",
        ));
    }
    // Preserve the public result type before selecting a NoValue implementation: an elided
    // zero-sized named product is not the unit type supported by the Rust binding.
    let result = body
        .parameters()
        .iter()
        .find(|parameter| parameter.kind == ParameterKind::Return)
        .map(|parameter| ScalarType::of(parameter.ty))
        .transpose()?
        .unwrap_or_else(ScalarType::unit);
    let parameters = body
        .parameters()
        .iter()
        .filter(|p| p.kind != ParameterKind::Return)
        .map(|p| ScalarType::of(p.ty))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((parameters, result))
}

/// Compile the roots and everything they reach into one module. Each export names a root to
/// expose to the Rust host binding, which requires a scalar host signature.
pub(super) fn emit(
    program: &ResolvedPhysicalProgram<'_>,
    roots: &[FunctionId],
    exports: &[(FunctionId, String)],
    imports: &mut Imports,
    session: &CompilerSession,
) -> Result<Emitted, String> {
    emit_with_export_kind(
        program,
        roots,
        exports,
        imports,
        session,
        |program, function| {
            let (parameters, result) = host_signature(program, function)?;
            Ok(HostExportKind::Scalar { parameters, result })
        },
    )
}

/// Emit no-argument roots through the temporary boxed differential-testing boundary.
pub(super) fn emit_boxed(
    program: &ResolvedPhysicalProgram<'_>,
    roots: &[FunctionId],
    exports: &[(FunctionId, String)],
    imports: &mut Imports,
    session: &CompilerSession,
) -> Result<Emitted, String> {
    emit_with_export_kind(
        program,
        roots,
        exports,
        imports,
        session,
        |program, function| {
            let body = program
                .function(function)
                .ok_or_else(|| format!("missing script entry {function:?}"))?;
            if !matches!(
                body.result_convention(),
                CallResultConvention::Value | CallResultConvention::NoValue
            ) {
                return Err(diagnostic(
                    function,
                    body,
                    "boxed Wasm expression binding requires a value result",
                ));
            }
            if body
                .parameters()
                .iter()
                .any(|parameter| parameter.kind != ParameterKind::Return)
            {
                return Err(diagnostic(
                    function,
                    body,
                    "boxed Wasm expression binding requires no arguments",
                ));
            }
            Ok(HostExportKind::Boxed {
                result: body
                    .parameters()
                    .iter()
                    .find(|parameter| parameter.kind == ParameterKind::Return)
                    .map_or(Type::unit(), |parameter| parameter.ty),
            })
        },
    )
}

fn emit_with_export_kind(
    program: &ResolvedPhysicalProgram<'_>,
    roots: &[FunctionId],
    exports: &[(FunctionId, String)],
    imports: &mut Imports,
    session: &CompilerSession,
    export_kind: impl Fn(&ResolvedPhysicalProgram<'_>, FunctionId) -> Result<HostExportKind, String>,
) -> Result<Emitted, String> {
    let host_exports = exports
        .iter()
        .map(|(function, name)| {
            debug_assert!(roots.contains(function), "export {name} is not a root");
            Ok(HostExport {
                function: *function,
                name: name.clone(),
                kind: export_kind(program, *function)?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let env = session
        .modules()
        .env_for(session.expect_fresh_module(roots.first().ok_or("no Wasm roots")?.module));
    let value_trait = env.expect_std_trait_id(VALUE_TRAIT_NAME);
    let definition = env.trait_def(value_trait);
    let layout_entries =
        [VALUE_SIZE_ASSOC_CONST_INDEX, VALUE_ALIGN_ASSOC_CONST_INDEX].map(|index| {
            (
                value_trait,
                definition.dictionary_associated_const_index(index),
            )
        });
    let mut pending = roots
        .iter()
        .map(|&root| program.direct_entry(root))
        .collect::<Vec<_>>();
    let mut seen = FxHashSet::default();
    let mut bodies = Vec::new();
    let mut natives = FxHashMap::default();
    let mut reachable = ReachableEvidence::default();
    let mut callables = callable::Reachable::default();
    let mut needs_callable_glue = false;
    let mut adapters = Vec::new();
    let mut subscript_modes = Vec::new();
    let mut subscript_adapters = Vec::new();
    let mut subscript_adapter_set = FxHashSet::default();
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
            for &id in &reachable.subscripts {
                for &mut_member in &subscript_modes {
                    if subscript_adapter_set.insert((id, mut_member))
                        && let Some(member) = program.subscript_member(id, mut_member)
                    {
                        pending.push(program.direct_entry(member.function()));
                        subscript_adapters.push((id, mut_member));
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
        let selections = callable::selections(body);
        let constructed_subscripts = constructed_subscript_definitions(body);
        for block in body.blocks() {
            let block = body.block(block);
            for operation in operations(block) {
                if matches!(
                    operation.kind,
                    OperationKind::Store
                        | OperationKind::Move
                        | OperationKind::Memcpy
                        | OperationKind::MoveBytes { .. }
                ) && let Value::Register(id) = &operation.operands[0]
                    && let Some(&entry) = selections.get(id)
                {
                    callables.select(entry);
                }
                for (index, value) in operation.operands.iter().enumerate() {
                    reachable.value(program, value)?;
                    if let Value::Function(target) = value
                        && !(index == 0
                            && matches!(
                                operation.kind,
                                OperationKind::Call { .. } | OperationKind::Project { .. }
                            ))
                        && !matches!(
                            operation.kind,
                            OperationKind::Clone { .. } | OperationKind::DropInitialized { .. }
                        )
                    {
                        callables.add(
                            *target,
                            callable::Captures {
                                hidden: 0,
                                values: 0,
                            },
                        );
                        callables.references.insert(*target);
                        pending.push(program.direct_entry(*target));
                    }
                }
                match operation.kind {
                    OperationKind::BuildClosure {
                        function,
                        num_hidden_dicts,
                        has_env_dict,
                        ..
                    } => {
                        let captures = callable::Captures {
                            hidden: num_hidden_dicts as usize,
                            values: operation.operands.len()
                                - num_hidden_dicts as usize
                                - usize::from(has_env_dict),
                        };
                        callables.add(function, captures);
                        pending.push(program.direct_entry(function));
                        for (trait_id, entry) in layout_entries {
                            reachable.entry(trait_id, entry);
                        }
                    }
                    OperationKind::Call { ref ty, .. }
                        if !matches!(operation.operands[0], Value::Function(_)) =>
                    {
                        callables.arity(
                            operation.operands.len()
                                - 1
                                - usize::from(ty.result_convention.has_result_place()),
                        );
                    }
                    OperationKind::BuildDictionary { definition, .. } => {
                        reachable.dictionary(definition)
                    }
                    OperationKind::BuildSubscriptEvidence { .. } => {
                        if let Some(result) = operation.result_id()
                            && let Some(constructed) = constructed_subscripts.get(&result)
                        {
                            reachable.subscript(constructed.definition);
                        }
                    }
                    OperationKind::BorrowSubscriptMember { mut_member, .. } => {
                        if !subscript_modes.contains(&mut_member) {
                            subscript_modes.push(mut_member);
                        }
                    }
                    OperationKind::DictEntry {
                        trait_id,
                        entry_index,
                        ..
                    } => reachable.entry(trait_id, entry_index),
                    OperationKind::CloneClosureEnv { .. }
                    | OperationKind::DropClosureEnv
                    | OperationKind::CloneSubscriptEnv { .. }
                    | OperationKind::DropSubscriptEnv => needs_callable_glue = true,
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
                if wasm_intrinsic(session, operation).is_none()
                    && let Some(Value::Function(target)) = callee(operation)
                {
                    pending.push(program.direct_entry(*target));
                }
            }
        }
        if !callables.entries.is_empty() || !callables.selected.is_empty() || needs_callable_glue {
            reachable.entry(
                value_trait,
                definition.dictionary_method_index(VALUE_CLONE_METHOD_INDEX),
            );
            reachable.entry(
                value_trait,
                definition.dictionary_method_index(VALUE_DROP_METHOD_INDEX),
            );
        }
        bodies.push((id, body, signature, selections));
    }
    let depth_tracked =
        depth_tracked_bodies(program, bodies.iter().map(|(id, body, _, _)| (*id, *body)));
    let needs_fuel = bodies.iter().any(|(_, body, _, _)| {
        body.blocks().any(|block| {
            operations(body.block(block))
                .any(|operation| matches!(operation.kind, OperationKind::CheckFuel))
        })
    });
    let needs_base = !adapters.is_empty()
        || !callables.entries.is_empty()
        || !callables.selected.is_empty()
        || needs_callable_glue
        || !subscript_adapters.is_empty()
        || host_exports
            .iter()
            .any(|export| matches!(export.kind, HostExportKind::Boxed { .. }))
        || bodies
            .iter()
            .any(|(_, body, signature, _)| !is_trivial_runtime_body(body, signature));
    let runtime_globals = RuntimeGlobals::new(needs_base, !depth_tracked.is_empty(), needs_fuel);
    let mut types = FunctionTypes::default();
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
        let index = types.intern(
            import.parameters.iter().copied(),
            import.results.iter().copied(),
        );
        import_section.import(
            IMPORT_MODULE,
            &import.name,
            EntityType::Function(index.as_u32()),
        );
    }
    let mut direct_index = imports.functions().len();
    let mut resume_indices = FxHashMap::default();
    let callees: FxHashMap<_, _> = bodies
        .iter()
        .map(|(id, body, sig, _)| {
            let start = WasmFunctionId::from_index(direct_index);
            direct_index += 1;
            if body.result_convention() == CallResultConvention::YIELDED_ONCE {
                resume_indices.insert(*id, WasmFunctionId::from_index(direct_index));
                direct_index += 1;
            }
            (*id, (start, sig))
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
        let index = types.intern(abi.params(), abi.results());
        entry_abis.insert((trait_id, entry), (index, abi));
    }
    let dictionary_table = adapters
        .iter()
        .enumerate()
        .map(|(index, &(id, entry))| {
            (
                (id, entry.as_index()),
                DispatchTableSlotId::from_index(index + 1),
            )
        })
        .collect();
    let direct_count = direct_index - imports.functions().len();
    let adapter_base = WasmFunctionId::from_index(imports.functions().len() + direct_count);
    for &(target, captures) in &callables.entries {
        let abi = callees[&program.direct_entry(target)].1;
        callables
            .arities
            .push(callable::visible_arity(abi, captures)?);
    }
    for entry in &callables.selected {
        callables.arities.push(
            entry_abis[entry]
                .1
                .parameters
                .len()
                .checked_sub(1)
                .ok_or("selected callable dictionary arity")?,
        );
    }
    let callable_count = callables.entries.len() + callables.selected.len();
    let subscript_base = adapters.len() + callable_count;
    let subscript_table = subscript_adapters
        .iter()
        .enumerate()
        .map(|(index, &entry)| {
            (
                entry,
                DispatchTableSlotId::from_index(subscript_base + index + 1),
            )
        })
        .collect::<FxHashMap<_, _>>();
    let resume_base = subscript_base + subscript_adapters.len();
    let resume_slots = bodies
        .iter()
        .filter(|(_, body, _, _)| body.result_convention() == CallResultConvention::YIELDED_ONCE)
        .enumerate()
        .map(|(index, (id, _, _, _))| {
            (
                *id,
                DispatchTableSlotId::from_index(resume_base + index + 1),
            )
        })
        .collect::<FxHashMap<_, _>>();
    let table_count =
        adapters.len() + callable_count + subscript_adapters.len() + resume_slots.len();
    let glue_base = WasmFunctionId::from_index(adapter_base.as_index() + table_count);
    let mut evidence =
        evidence::Image::build(program, &reachable, &dictionary_table, &subscript_table);
    let emit_callable_glue = callable_count != 0 || needs_callable_glue;
    let clone_method = definition.dictionary_method_index(VALUE_CLONE_METHOD_INDEX);
    let drop_method = definition.dictionary_method_index(VALUE_DROP_METHOD_INDEX);
    let mut callable_entries = callable::Entries {
        slots: callables
            .entries
            .iter()
            .enumerate()
            .map(|(index, &(target, _))| {
                (
                    target,
                    DispatchTableSlotId::from_index(adapters.len() + index + 1),
                )
            })
            .collect(),
        signatures: FxHashMap::default(),
        references: FxHashMap::default(),
        selected: callables
            .selected
            .iter()
            .enumerate()
            .map(|(index, &entry)| {
                (
                    entry,
                    DispatchTableSlotId::from_index(
                        adapters.len() + callables.entries.len() + index + 1,
                    ),
                )
            })
            .collect(),
        clone: emit_callable_glue.then_some(glue_base),
        drop: emit_callable_glue.then(|| WasmFunctionId::from_index(glue_base.as_index() + 1)),
        value_methods: emit_callable_glue.then(|| callable::ValueMethods {
            clone: callable::ValueMethod::new(
                entry_abis[&(value_trait, clone_method)].0,
                clone_method,
            ),
            drop: callable::ValueMethod::new(
                entry_abis[&(value_trait, drop_method)].0,
                drop_method,
            ),
        }),
    };
    let resume_signature = types.intern([ValType::I32, ValType::I32], [ValType::I32]);
    let mut subscript_entries = subscript::Entries {
        signatures_by_arity: FxHashMap::default(),
        resume_signature,
    };
    for &(target, _) in &callables.entries {
        if callables.references.contains(&target) {
            let offset = evidence.callable_reference(callable_entries.slots[&target]);
            callable_entries.references.insert(target, offset);
        }
    }
    for &arity in &callables.arities {
        callable_entries.signatures.entry(arity).or_insert_with(|| {
            let abi = callable::abi(arity);
            types.intern(abi.params(), abi.results())
        });
    }
    for &(id, mut_member) in &subscript_adapters {
        let definition = program.subscript(id).unwrap();
        let target = program.direct_entry(definition.member(mut_member).unwrap().function());
        let arity =
            subscript::visible_arity(callees[&target].1, definition.capture_schema().len())?;
        subscript_entries
            .signatures_by_arity
            .entry(arity)
            .or_insert_with(|| types.intern(subscript::parameters(arity), subscript::results()));
    }
    let mut strings = StringLiterals::default();
    let mut names = WasmNames::new(session, imports);
    let mut source_map = Vec::new();
    let mut suspension_layouts = FxHashMap::default();
    let mut body_index = 0;
    for (id, body, signature, selections) in &bodies {
        names.push(format!(
            "{}::{}",
            module_path(session, id.module),
            body.name
        ));
        let ty = if body.result_convention() == CallResultConvention::YIELDED_ONCE {
            types.intern(signature.params(), subscript::results())
        } else {
            types.intern(signature.params(), signature.results())
        };
        functions.function(ty.as_u32());
        let mode = if body.result_convention() == CallResultConvention::YIELDED_ONCE {
            BodyMode::ProjectionStart {
                resume: resume_slots[id],
            }
        } else {
            BodyMode::Normal
        };
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
            &callable_entries,
            &subscript_entries,
            selections,
            mode,
            runtime_globals,
            depth_tracked.contains(id),
        )
        .and_then(Body::emit)
        .map_err(|reason| diagnostic(*id, body, &reason))?;
        if let Some(layout) = emitted.suspension {
            suspension_layouts.insert(*id, layout);
        }
        code.function(&emitted.function);
        source_map.extend(
            emitted
                .source_map
                .into_iter()
                .map(|(bytes, span)| CodeSourceMapEntry {
                    body: body_index,
                    bytes,
                    span,
                }),
        );
        body_index += 1;
        if body.result_convention() == CallResultConvention::YIELDED_ONCE {
            names.push(format!("<resume {}>", body.name));
            let mut parameters = signature.params();
            parameters.push(ValType::I32);
            functions.function(types.intern(parameters, [ValType::I32]).as_u32());
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
                &callable_entries,
                &subscript_entries,
                selections,
                BodyMode::ProjectionResume,
                runtime_globals,
                depth_tracked.contains(id),
            )
            .and_then(Body::emit)
            .map_err(|reason| diagnostic(*id, body, &reason))?;
            debug_assert!(emitted.suspension.is_some());
            code.function(&emitted.function);
            source_map.extend(emitted.source_map.into_iter().map(|(bytes, span)| {
                CodeSourceMapEntry {
                    body: body_index,
                    bytes,
                    span,
                }
            }));
            body_index += 1;
        }
    }
    for &(id, entry) in &adapters {
        let definition = program.dictionary(id).unwrap();
        let (ty, abi) = &entry_abis[&(definition.trait_id(), entry)];
        names.push(format!(
            "<dictionary adapter {}>",
            dictionary_entry_name(env, definition.trait_id(), entry)
        ));
        functions.function(ty.as_u32());
        code.function(&dictionary_adapter(
            program, id, entry, abi, &callees, session, imports,
        )?);
    }
    for &(target, captures) in &callables.entries {
        let arity = callable::visible_arity(callees[&program.direct_entry(target)].1, captures)?;
        names.push(format!(
            "<callable adapter {}>",
            program
                .function(program.direct_entry(target))
                .map_or_else(|| format!("{target:?}"), |body| body.name.to_string())
        ));
        functions.function(callable_entries.signatures[&arity].as_u32());
        code.function(&callable::adapter(
            program,
            target,
            captures,
            &callees,
            &callable_entries,
            imports,
            session,
        )?);
    }
    for &entry in &callables.selected {
        let (ty, abi) = &entry_abis[&entry];
        let arity = abi
            .parameters
            .len()
            .checked_sub(1)
            .ok_or("selected callable dictionary arity")?;
        names.push(format!(
            "<callable adapter {}>",
            dictionary_entry_name(env, entry.0, entry.1)
        ));
        functions.function(callable_entries.signatures[&arity].as_u32());
        code.function(&callable::selected_adapter(env, entry, *ty, abi)?);
    }
    for &(id, mut_member) in &subscript_adapters {
        let definition = program.subscript(id).unwrap();
        let member = definition.member(mut_member).unwrap();
        let target = program.direct_entry(member.function());
        let (index, abi) = callees[&target];
        let arity = subscript::visible_arity(abi, definition.capture_schema().len())?;
        names.push(format!(
            "<subscript {} member>",
            if mut_member { "mut" } else { "ref" }
        ));
        functions.function(subscript_entries.signatures_by_arity[&arity].as_u32());
        code.function(&subscript::member_adapter(
            program, definition, mut_member, abi, index,
        )?);
    }
    for &target in bodies
        .iter()
        .filter(|(_, body, _, _)| body.result_convention() == CallResultConvention::YIELDED_ONCE)
        .map(|(id, _, _, _)| id)
    {
        let (_, abi) = callees[&target];
        names.push(format!(
            "<subscript resume {}>",
            program.function(target).unwrap().name
        ));
        functions.function(subscript_entries.resume_signature.as_u32());
        code.function(&subscript::resume_adapter(
            abi,
            &suspension_layouts[&target],
            resume_indices[&target],
        ));
    }
    if let Some(methods) = callable_entries.value_methods {
        names.push("<callable clone>".into());
        names.push("<callable drop>".into());
        functions.function(types.intern([ValType::I32], [ValType::I32]).as_u32());
        code.function(&callable::clone_entry(imports, methods.clone));
        functions.function(types.intern([ValType::I32], []).as_u32());
        code.function(&callable::drop_entry(imports, methods.drop));
    }
    let mut tables = TableSection::new();
    tables.table(TableType {
        element_type: RefType::FUNCREF,
        table64: false,
        minimum: table_count as u64 + 1,
        maximum: None,
        shared: false,
    });
    let mut elements = ElementSection::new();
    elements.active(
        None,
        &ConstExpr::i32_const(1),
        Elements::Functions(
            (0..table_count)
                .map(|index| WasmFunctionId::from_index(adapter_base.as_index() + index).as_u32())
                .collect::<Vec<_>>()
                .into(),
        ),
    );
    let mut globals = GlobalSection::new();
    let mut exports = ExportSection::new();
    for _ in 0..runtime_globals.count {
        globals.global(
            GlobalType {
                val_type: ValType::I32,
                mutable: true,
                shared: false,
            },
            &ConstExpr::i32_const(0),
        );
    }
    let mut next_index =
        WasmFunctionId::from_index(glue_base.as_index() + if emit_callable_glue { 2 } else { 0 });
    for export in &host_exports {
        let (index, signature) = &callees[&program.direct_entry(export.function)];
        match &export.kind {
            HostExportKind::Scalar { parameters, result } if signature.fallible => {
                // Internal status returns become a Rust error through the outer invocation
                // boundary, without changing the scalar host C signature.
                debug_assert_eq!(parameters.len(), signature.parameters.len());
                names.push(format!("<host entry {}>", export.name));
                functions.function(
                    types
                        .intern(
                            parameters.iter().copied().map(ScalarType::wasm),
                            result_as_wasm(*result),
                        )
                        .as_u32(),
                );
                code.function(&entry_wrapper(*index, signature, *result));
                exports.export(&export.name, ExportKind::Func, next_index.as_u32());
                next_index = WasmFunctionId::from_index(next_index.as_index() + 1);
            }
            HostExportKind::Scalar { .. } => {
                exports.export(&export.name, ExportKind::Func, index.as_u32());
            }
            HostExportKind::Boxed { .. } => {
                names.push(format!("<boxed host entry {}>", export.name));
                functions.function(types.intern([ValType::I32], []).as_u32());
                code.function(&boxed_entry_wrapper(*index, signature)?);
                exports.export(&export.name, ExportKind::Func, next_index.as_u32());
                next_index = WasmFunctionId::from_index(next_index.as_index() + 1);
            }
        }
    }
    // Rust calls this setter directly at invocation boundaries. All state and diagnostics stay
    // in shared memory; no language values or per-call state are passed through JavaScript.
    functions.function(types.intern([ValType::I32], []).as_u32());
    code.function(&setup(runtime_globals));
    names.push("<setup>".into());
    exports.export(SETUP_EXPORT, ExportKind::Func, next_index.as_u32());
    let mut module = Module::new();
    module
        .section(&types.section)
        .section(&import_section)
        .section(&functions)
        .section(&tables);
    if runtime_globals.count != 0 {
        module.section(&globals);
    }
    module
        .section(&exports)
        .section(&elements)
        .section(&code)
        .section(&names.finish(runtime_globals));
    Ok(Emitted {
        bytes: module.finish(),
        strings: strings.values.into_boxed_slice(),
        exports: host_exports,
        evidence,
        dictionaries: reachable.dictionaries.into_boxed_slice(),
        subscript_count: reachable.subscripts.len(),
        source_map,
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

/// Bodies whose active frame contributes to a reachable call-depth check.
///
/// Known calls follow the assembled direct-entry graph. An indirect call is conservative: once
/// any reachable body checks depth, its caller must retain its depth contribution because the
/// runtime target may be that checked body. Bounded frames outside that guest call graph, such as
/// a caller that enters a callback through native code, are deliberately not counted; this can
/// shift the exact limit at which Wasm and the interpreters report call-depth exhaustion.
fn depth_tracked_bodies<'a>(
    program: &ResolvedPhysicalProgram<'_>,
    bodies: impl IntoIterator<Item = (FunctionId, &'a Function)>,
) -> FxHashSet<FunctionId> {
    let bodies = bodies.into_iter().collect::<Vec<_>>();
    let mut tracked = FxHashSet::default();
    let mut calls = FxHashMap::<FunctionId, Vec<FunctionId>>::default();
    let mut indirect = FxHashSet::default();
    for &(id, body) in &bodies {
        for block in body.blocks() {
            for operation in operations(body.block(block)) {
                if matches!(operation.kind, OperationKind::CheckCallDepth) {
                    tracked.insert(id);
                }
                if let Some(callee) = callee(operation) {
                    if let Value::Function(target) = callee {
                        calls
                            .entry(id)
                            .or_default()
                            .push(program.direct_entry(*target));
                    } else {
                        indirect.insert(id);
                    }
                }
            }
        }
    }
    if tracked.is_empty() {
        return tracked;
    }
    loop {
        let mut changed = false;
        for &(id, _) in &bodies {
            if !tracked.contains(&id)
                && (indirect.contains(&id)
                    || calls.get(&id).is_some_and(|targets| {
                        targets.iter().any(|target| tracked.contains(target))
                    }))
            {
                changed |= tracked.insert(id);
            }
        }
        if !changed {
            return tracked;
        }
    }
}

/// A body proven not to touch the shadow stack or invocation diagnostics.
///
/// This intentionally recognizes only the small scalar leaf shape. More bodies can be admitted as
/// their storage requirements become explicit emitter metadata.
fn is_trivial_runtime_body(body: &Function, signature: &CallAbi) -> bool {
    !signature.fallible
        && body.result_convention() != CallResultConvention::YIELDED_ONCE
        && body.blocks().count() == 1
        && matches!(
            body.block(body.entry()).terminator().kind,
            TerminatorKind::Return
        )
        && body
            .parameters()
            .iter()
            .all(|parameter| ScalarType::of(parameter.ty).is_ok())
        && body
            .constants()
            .iter()
            .all(|constant| ScalarType::of(constant.ty).is_ok())
        && body
            .block(body.entry())
            .operations()
            .iter()
            .all(|operation| matches!(operation.kind, OperationKind::Store))
}

fn layout_witness(op: &Operation) -> Option<&Value> {
    match op.kind {
        OperationKind::Alloca { .. } if !op.operands.is_empty() => op.operands.first(),
        OperationKind::Move | OperationKind::Replace if op.operands.len() == 3 => {
            op.operands.last()
        }
        OperationKind::BlackBox { .. } if op.operands.len() == 2 => op.operands.last(),
        OperationKind::Variant {
            has_layout_witness: true,
            ..
        } => op.operands.last(),
        _ => None,
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

/// Resolve a direct MIR call for target-specific Wasm instruction selection.
fn wasm_intrinsic(session: &CompilerSession, operation: &Operation) -> Option<KnownCallee> {
    if !matches!(operation.kind, OperationKind::Call { .. }) {
        return None;
    }
    let Value::Function(callee) = operation.operands.first()? else {
        return None;
    };
    // Physical lowering always starts from optimized semantic MIR, even when its own optimization
    // stage is disabled, so its function ids use the optimized artifact's specialization table.
    let known = session.known_callees().resolve(*callee, |callee| {
        Some(session.hir_identity_of(callee, MirOptimization::Enabled))
    })?;
    matches!(
        known,
        KnownCallee::IntAdd
            | KnownCallee::IntSub
            | KnownCallee::IntMul
            | KnownCallee::IntNeg
            | KnownCallee::IntFromInt
            | KnownCallee::IntCmpCode
            | KnownCallee::FloatAdd
            | KnownCallee::FloatSub
            | KnownCallee::FloatMul
            | KnownCallee::FloatNeg
            | KnownCallee::FloatCmpCode
            | KnownCallee::BoolNot
    )
    .then_some(known)
}

fn result_as_wasm(result: ScalarType) -> Option<ValType> {
    (!result.is_unit()).then(|| result.wasm())
}

fn setup(runtime_globals: RuntimeGlobals) -> WasmFunction {
    let mut code = WasmFunction::new([]);
    for global in runtime_globals.base() {
        let offset = match global {
            Global::Context => {
                code.instruction(&I::LocalGet(0));
                code.instruction(&I::GlobalSet(global as u32));
                continue;
            }
            Global::Stack => offset_of!(InvocationState, stack),
            Global::End => offset_of!(InvocationState, end),
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
    if let Some(depth) = runtime_globals.depth {
        code.instruction(&I::I32Const(0));
        code.instruction(&I::GlobalSet(depth.depth));
        load_invocation_state(
            &mut code,
            depth.limit,
            offset_of!(InvocationState, depth_limit),
        );
    }
    if let Some(fuel) = runtime_globals.fuel {
        load_invocation_state(&mut code, fuel.fuel, offset_of!(InvocationState, fuel));
        load_invocation_state(
            &mut code,
            fuel.enabled,
            offset_of!(InvocationState, fuel_enabled),
        );
    }
    code.instruction(&I::End);
    code
}

fn load_invocation_state(code: &mut WasmFunction, global: u32, offset: usize) {
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
    code.instruction(&I::GlobalSet(global));
}

/// The export of the invocation-state setter, alongside the host-callable functions.
pub(super) const SETUP_EXPORT: &str = "setup";

fn module_path(session: &CompilerSession, module: ModuleId) -> String {
    session
        .modules()
        .path(module)
        .map_or_else(|| format!("m{}", module.as_u32()), ToString::to_string)
}

fn dictionary_entry_name(
    env: ModuleEnv<'_>,
    trait_id: TraitId,
    entry: TraitDictionaryEntryIndex,
) -> String {
    let definition = env.trait_def(trait_id);
    let index = entry.as_index();
    let entry = definition
        .methods
        .get(index)
        .map(|(name, _)| *name)
        .or_else(|| {
            definition
                .associated_consts
                .get(index - definition.methods.len())
                .map(|constant| constant.name)
        })
        .map_or_else(|| format!("#{index}"), |name| name.to_string());
    format!("{}::{entry}", definition.name)
}

/// Debug names retained in the custom name section.
struct WasmNames {
    functions: Vec<String>,
}

impl WasmNames {
    fn new(session: &CompilerSession, imports: &Imports) -> Self {
        let mut functions = imports
            .functions()
            .iter()
            .map(|import| import.name.clone())
            .collect::<Vec<_>>();
        for (&id, index) in &imports.natives {
            if let Some(name) = session
                .expect_fresh_module(id.module)
                .get_function_name_by_id(id.function)
            {
                functions[index.as_index()] =
                    format!("{}::{name}", module_path(session, id.module));
            }
        }
        Self { functions }
    }

    fn push(&mut self, name: String) {
        self.functions.push(name);
    }

    fn finish(self, runtime_globals: RuntimeGlobals) -> NameSection {
        let mut functions = NameMap::new();
        for (index, name) in self.functions.iter().enumerate() {
            functions.append(index as u32, name);
        }
        let mut section = NameSection::new();
        section.functions(&functions);
        let mut globals = NameMap::new();
        for global in runtime_globals.base() {
            globals.append(global as u32, global.name());
        }
        if let Some(depth) = runtime_globals.depth {
            globals.append(depth.depth, "call_depth");
            globals.append(depth.limit, "call_depth_limit");
        }
        if let Some(fuel) = runtime_globals.fuel {
            globals.append(fuel.fuel, "fuel");
            globals.append(fuel.enabled, "fuel_enabled");
        }
        section.globals(&globals);
        section
    }
}

fn diagnostic(id: FunctionId, body: &Function, reason: &str) -> String {
    format!("Wasm generation in {} ({id:?}): {reason}", body.name)
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
