// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Checked physical-MIR execution. Boxed values exist only at the host boundary.
//! Unsupported reachable contracts are rejected before execution, even in untaken branches.

#[path = "interpreter_memory.rs"]
mod memory;

use super::{
    dictionary::DictionaryReference,
    program::{InternedStaticEvidence, ProgramEvidenceId, ResolvedPhysicalProgram},
};
use crate::{
    CompilerSession, Location,
    compiler::error::SandboxViolationKind,
    eval::RuntimeError,
    execution::ReferenceInterpreterLimits,
    hir::{
        function::ArgConvention,
        native_functions::{
            NativeCallOutcome, NativeEntry, NativeFailureState, NativeParameter, NativeResult,
        },
        value::{LiteralValue, Value, VariantPayloadStorage},
    },
    mir::{
        self, Function, Operation, OperationKind, ValueId,
        function::ParameterKind,
        role::{MirType, ValueRoles},
        terminator::TerminatorKind,
        value::StaticEvidence,
    },
    module::{DictionaryEntryEvidence, FunctionId, ModuleEnv, TraitDictionaryId, id::Id},
    std::value::VALUE_CLONE_METHOD_INDEX,
    types::{
        r#type::{CallResultConvention, Type, TypeKind},
        type_inference::substitution::InstSubst,
        type_like::TypeLike,
        type_mapper::SimpleInstantiationMapper,
        type_properties::concrete_type_is_trivial_copy,
    },
};
use memory::{Address, Generation, Memory, Scalar, ScalarKind, StoredValue};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{borrow::Cow, fmt::Display, mem, process::abort, ptr, rc::Rc, slice::from_ref};
use ustr::Ustr;

fn unsupported(detail: impl Display) -> RuntimeError {
    RuntimeError::Backend(format!(
        "Physical MIR execution does not yet support {detail}"
    ))
}
fn invalid(detail: &str) -> RuntimeError {
    RuntimeError::Backend(format!("Invalid physical MIR execution: {detail}"))
}

#[derive(Clone)]
enum Binding {
    Scalar(Scalar),
    Aggregate(Rc<StoredValue>),
    Tag(Ustr),
    Place(Address),
    StackMarker(usize),
    Evidence(Evidence),
    Callable(Callable),
}

/// Symbolic dictionaries are used only by capability analysis; execution uses ABI references.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Evidence {
    Physical {
        reference: DictionaryReference,
        generation: Generation,
        ty: Type,
    },
    Dictionary {
        definition: TraitDictionaryId,
        captures: Vec<Evidence>,
        ty: Type,
    },
    Storage(bool),
}

impl Evidence {
    fn ty(&self) -> Type {
        match self {
            Self::Dictionary { ty, .. } | Self::Physical { ty, .. } => *ty,
            Self::Storage(_) => ScalarKind::Bool.ty(),
        }
    }

    fn layout_type(&self) -> Result<Type, RuntimeError> {
        // The clone signature names the type checked by the memory harness, including phantom
        // types. Executable size/alignment come from the dictionary's layout entries.
        let data = self.ty().data();
        let fields = data
            .as_tuple()
            .ok_or_else(|| invalid("expected Value layout evidence"))?;
        let clone = fields
            .get(usize::from(VALUE_CLONE_METHOD_INDEX))
            .ok_or_else(|| invalid("missing Value clone entry"))?
            .data();
        let ty = clone
            .as_function()
            .ok_or_else(|| invalid("invalid Value clone entry"))?
            .ret;
        Ok(ty)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Callable {
    function: FunctionId,
    captures: Vec<Evidence>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Input {
    Place(Type),
    Evidence(Evidence),
}

impl Input {
    fn ty(&self) -> Type {
        match self {
            Self::Place(ty) => *ty,
            Self::Evidence(evidence) => evidence.ty(),
        }
    }
}

/// Concrete type identities for checked storage, not specialized copies of MIR bodies.
#[derive(Default)]
struct RuntimeTypes(InstSubst);

impl RuntimeTypes {
    fn resolve(&self, ty: Type) -> Type {
        ty.map(&mut SimpleInstantiationMapper::new(&self.0))
    }

    fn bind(&mut self, pattern: Type, actual: Type) -> Result<(), RuntimeError> {
        let mut pending = vec![(pattern, actual)];
        let mut seen = FxHashSet::default();
        while let Some((pattern, actual)) = pending.pop() {
            if pattern == actual || !seen.insert((pattern, actual)) {
                continue;
            }
            let lhs = pattern.data();
            let rhs = actual.data();
            use TypeKind::*;
            let pairs: Vec<_> = match (&*lhs, &*rhs) {
                (Variable(var), _) => {
                    if let Some(previous) = self.0.0.insert(*var, actual) {
                        if previous != actual {
                            return Err(invalid("inconsistent runtime type evidence"));
                        }
                    }
                    continue;
                }
                (Tuple(a), Tuple(b)) if a.len() == b.len() => {
                    a.iter().copied().zip(b.iter().copied()).collect()
                }
                (Record(a), Record(b)) | (Variant(a), Variant(b))
                    if a.len() == b.len() && a.iter().zip(b).all(|(a, b)| a.0 == b.0) =>
                {
                    a.iter().zip(b).map(|(a, b)| (a.1, b.1)).collect()
                }
                (Named(a), Named(b)) if a.def == b.def && a.params.len() == b.params.len() => a
                    .params
                    .iter()
                    .copied()
                    .zip(b.params.iter().copied())
                    .collect(),
                (Native(a), Native(b))
                    if a.bare_ty == b.bare_ty && a.arguments.len() == b.arguments.len() =>
                {
                    a.arguments
                        .iter()
                        .copied()
                        .zip(b.arguments.iter().copied())
                        .collect()
                }
                // Effect and mutability annotations do not change dictionary storage identity.
                (Function(a), Function(b)) if a.args.len() == b.args.len() => a
                    .args
                    .iter()
                    .zip(&b.args)
                    .map(|(a, b)| (a.ty, b.ty))
                    .chain([(a.ret, b.ret)])
                    .collect(),
                _ => return Err(invalid("runtime type mismatch")),
            };
            pending.extend(pairs);
        }
        Ok(())
    }

    fn for_call(body: &Function, inputs: &[Input]) -> Result<Self, RuntimeError> {
        if inputs.len() != body.parameters().len() {
            return Err(invalid("call arity mismatch"));
        }
        let mut types = Self::default();
        for (parameter, input) in body.parameters().iter().zip(inputs) {
            if (parameter.kind == ParameterKind::Dictionary) != matches!(input, Input::Evidence(_))
            {
                return Err(invalid("call evidence role mismatch"));
            }
            types.bind(parameter.ty, input.ty())?;
        }
        Ok(types)
    }
}

impl Binding {
    fn evidence_references(&self) -> &[Evidence] {
        match self {
            Self::Evidence(evidence) => from_ref(evidence),
            Self::Callable(callable) => &callable.captures,
            _ => &[],
        }
    }

    fn evidence(self) -> Result<Evidence, RuntimeError> {
        match self {
            Self::Evidence(evidence) => Ok(evidence),
            Self::Scalar(Scalar::Bool(value)) => Ok(Evidence::Storage(value)),
            _ => Err(invalid("expected evidence")),
        }
    }
    fn callable(self) -> Result<Callable, RuntimeError> {
        match self {
            Self::Callable(callable) => Ok(callable),
            _ => Err(unsupported("first-class callable storage")),
        }
    }
    fn place(&self) -> Result<Address, RuntimeError> {
        match self {
            Self::Place(address) => Ok(*address),
            _ => Err(invalid("expected a place")),
        }
    }
    fn scalar(self) -> Result<Scalar, RuntimeError> {
        match self {
            Self::Scalar(value) => Ok(value),
            Self::Evidence(Evidence::Storage(value)) => Ok(Scalar::Bool(value)),
            _ => Err(invalid("expected a scalar register")),
        }
    }
}

pub(crate) fn run_entry(
    program: &ResolvedPhysicalProgram,
    entry: FunctionId,
    arguments: &mut [Value],
    limits: ReferenceInterpreterLimits,
    session: &CompilerSession,
) -> Result<Value, RuntimeError> {
    let mut memory = Memory::default();
    memory.allocation_limit = limits.environment_cell_limit;
    let mut interpreter = Interpreter {
        program,
        memory,
        limits,
        fuel: limits.execution.fuel_limit,
        depth: 0,
        session,
        types: RuntimeTypes::default(),
        static_evidence: FxHashMap::default(),
    };
    interpreter.prepare_native_storage()?;
    interpreter.check_supported(entry)?;
    interpreter
        .memory
        .bind_tags(|tag| session.variant_tag_id(tag));
    let body = program
        .function(entry)
        .ok_or_else(|| unsupported("native host entry points"))?;
    let (result, parameters) = body
        .parameters()
        .split_last()
        .ok_or_else(|| invalid("missing result parameter"))?;
    assert_eq!(
        parameters.len(),
        arguments.len(),
        "host argument count mismatch"
    );
    if parameters.iter().any(|p| {
        !matches!(
            p.kind,
            ParameterKind::Parameter(ArgConvention::Let) | ParameterKind::Owned
        )
    }) {
        return Err(unsupported("this host entry signature"));
    }
    for (parameter, argument) in parameters.iter().zip(arguments.iter()) {
        interpreter.memory.validate_import(parameter.ty, argument)?;
    }
    let mut bindings = Vec::with_capacity(arguments.len() + 1);
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let value = interpreter.memory.import(parameter.ty, argument)?;
        let address = interpreter.memory.allocate(parameter.ty, None)?;
        interpreter.memory.write_value(address, &value)?;
        bindings.push(Binding::Place(address));
    }
    let result = interpreter.memory.allocate(result.ty, None)?;
    bindings.push(Binding::Place(result));
    let outcome = interpreter.call(entry, bindings);
    if outcome.is_ok() || matches!(&outcome, Err(RuntimeError::SourceFailure(_))) {
        interpreter.memory.check_runtime_ownership()?;
    }
    // Export transfers native ownership. Storage teardown never runs Ferlium cleanup; reclamation
    // of native-owned allocations/resources after poisoning belongs to the runtime-domain layer.
    let result = outcome.and_then(|()| interpreter.memory.export(result));
    if result.is_ok() || matches!(&result, Err(RuntimeError::SourceFailure(_))) {
        interpreter.memory.reclaim_host_natives()?;
    }
    result
}

struct Interpreter<'a, 'p> {
    program: &'a ResolvedPhysicalProgram<'p>,
    memory: Memory,
    limits: ReferenceInterpreterLimits,
    fuel: Option<usize>,
    depth: usize,
    session: &'a CompilerSession,
    types: RuntimeTypes,
    static_evidence: FxHashMap<ProgramEvidenceId, Evidence>,
}

impl<'a, 'p> Interpreter<'a, 'p> {
    fn build_evidence(
        &mut self,
        definition: TraitDictionaryId,
        captures: Vec<Evidence>,
        is_static: bool,
        span: Option<Location>,
    ) -> Result<Evidence, RuntimeError> {
        let metadata = self
            .program
            .dictionary(definition)
            .ok_or_else(|| invalid("unresolved dictionary"))?;
        let mut types = RuntimeTypes::default();
        if metadata.capture_types().len() != captures.len() {
            return Err(invalid("dictionary capture count mismatch"));
        }
        for (ty, capture) in metadata.capture_types().iter().zip(&captures) {
            types.bind(*ty, capture.ty())?;
        }
        self.memory.allocate_evidence(
            self.program
                .descriptor_index(definition)
                .ok_or_else(|| invalid("unresolved descriptor"))?,
            types.resolve(metadata.ty()),
            metadata.environment(),
            &captures,
            is_static,
            span,
        )
    }

    fn prepare_static_evidence(
        &mut self,
        mut required: FxHashSet<ProgramEvidenceId>,
    ) -> Result<(), RuntimeError> {
        let mut pending = required.iter().copied().collect::<Vec<_>>();
        while let Some(id) = pending.pop() {
            let captures = match &self.program.static_evidence()[id.as_index()] {
                InternedStaticEvidence::Dictionary { captures, .. }
                | InternedStaticEvidence::Subscript { captures, .. } => captures,
                InternedStaticEvidence::VariantPayloadStorage(_) => continue,
            };
            for &capture in captures {
                if required.insert(capture) {
                    pending.push(capture);
                }
            }
        }
        // Assembly interns children before parents. Sorting just the reachable dependency closure
        // preserves that order without scanning or materializing unrelated program evidence.
        let mut required = required.into_iter().collect::<Vec<_>>();
        required.sort_unstable_by_key(|id| id.as_index());
        for id in required {
            let evidence = &self.program.static_evidence()[id.as_index()];
            let value = match evidence {
                InternedStaticEvidence::Dictionary {
                    definition,
                    captures,
                } => {
                    let captures = captures
                        .iter()
                        .map(|id| self.static_evidence[id].clone())
                        .collect();
                    self.build_evidence(*definition, captures, true, None)?
                }
                InternedStaticEvidence::VariantPayloadStorage(value) => Evidence::Storage(*value),
                InternedStaticEvidence::Subscript { .. } => {
                    return Err(unsupported("subscript evidence"));
                }
            };
            self.static_evidence.insert(id, value);
        }
        Ok(())
    }

    fn retain_binding(&mut self, binding: &Binding) -> Result<(), RuntimeError> {
        for (index, evidence) in binding.evidence_references().iter().enumerate() {
            if let Err(error) = self.memory.retain_evidence(evidence) {
                for retained in &binding.evidence_references()[..index] {
                    self.memory.release_evidence(retained)?;
                }
                return Err(error);
            }
        }
        Ok(())
    }

    fn release_binding(&mut self, binding: &Binding) -> Result<(), RuntimeError> {
        for evidence in binding.evidence_references() {
            self.memory.release_evidence(evidence)?;
        }
        Ok(())
    }

    fn layout_entries(&self, evidence: &Evidence) -> Result<[usize; 2], RuntimeError> {
        let definition = match evidence {
            Evidence::Dictionary { definition, .. } => self.program.dictionary(*definition),
            Evidence::Physical { reference, .. } => self.program.descriptor(reference.descriptor),
            _ => None,
        };
        definition
            .and_then(|d| d.layout_entries())
            .ok_or_else(|| invalid("expected Value layout evidence"))
    }

    fn witness_layout(
        &mut self,
        evidence: Evidence,
        span: Location,
    ) -> Result<[usize; 2], RuntimeError> {
        let mut layout = [0; 2];
        for (index, entry) in self.layout_entries(&evidence)?.into_iter().enumerate() {
            let callable = self.dictionary_entry(evidence.clone(), entry)?;
            let marker = self.memory.len();
            let output = self.memory.allocate(ScalarKind::Int.ty(), Some(span))?;
            let result = self
                .invoke(callable, vec![Binding::Place(output)])
                .and_then(|()| self.memory.read(output));
            self.memory.restore(marker);
            let Scalar::Int(value) = result? else {
                return Err(invalid("non-integer layout witness"));
            };
            layout[index] =
                usize::try_from(value).map_err(|_| invalid("negative layout witness"))?;
        }
        Ok(layout)
    }

    fn native(&self, id: FunctionId) -> Result<&'a NativeEntry, RuntimeError> {
        self.program
            .module(id.module)
            .and_then(|m| m.native_entry(id))
            .ok_or_else(|| unsupported(format!("native entry {id:?}")))
    }

    fn env(&self, id: FunctionId) -> ModuleEnv<'a> {
        ModuleEnv::new(
            self.session.expect_fresh_module(id.module),
            self.session.raw_modules(),
        )
    }

    fn symbolic_dictionary(
        &self,
        definition: TraitDictionaryId,
        captures: Vec<Evidence>,
    ) -> Result<Evidence, RuntimeError> {
        let mut pending = captures.iter().map(|e| (e, 1)).collect::<Vec<_>>();
        let mut count = 0;
        while let Some((evidence, depth)) = pending.pop() {
            count += 1;
            if count > 4096 || depth >= 64 {
                return Err(unsupported("dictionary capture expansion limit"));
            }
            if let Evidence::Dictionary { captures, .. } = evidence {
                pending.extend(captures.iter().map(|e| (e, depth + 1)));
            }
        }
        let definition_data = self
            .program
            .dictionary(definition)
            .ok_or_else(|| invalid("unresolved dictionary"))?;
        if captures.len() != definition_data.capture_schema().len() {
            return Err(invalid("dictionary capture count mismatch"));
        }
        let mut types = RuntimeTypes::default();
        for (ty, capture) in definition_data.capture_types().iter().zip(&captures) {
            types.bind(*ty, capture.ty())?;
        }
        Ok(Evidence::Dictionary {
            definition,
            ty: types.resolve(definition_data.ty()),
            captures,
        })
    }

    fn symbolic_static_evidence(
        &self,
        evidence: &StaticEvidence,
        depth: usize,
    ) -> Result<Evidence, RuntimeError> {
        if depth >= 64 {
            return Err(unsupported("evidence nesting limit"));
        }
        match evidence {
            StaticEvidence::Dictionary {
                definition,
                captures,
            } => self.symbolic_dictionary(
                *definition,
                captures
                    .iter()
                    .map(|e| self.symbolic_static_evidence(e, depth + 1))
                    .collect::<Result<_, _>>()?,
            ),
            StaticEvidence::VariantPayloadStorage(value) => Ok(Evidence::Storage(*value)),
            _ => Err(unsupported("subscript evidence")),
        }
    }

    fn dictionary_entry(&self, evidence: Evidence, index: usize) -> Result<Callable, RuntimeError> {
        let (definition, captures) = match &evidence {
            Evidence::Physical { reference, .. } => (
                self.program.descriptor(reference.descriptor),
                Cow::Owned(self.memory.evidence_captures(&evidence)?),
            ),
            Evidence::Dictionary {
                definition,
                captures,
                ..
            } => (
                self.program.dictionary(*definition),
                Cow::Borrowed(captures.as_slice()),
            ),
            _ => return Err(invalid("expected a dictionary")),
        };
        let entry = definition
            .ok_or_else(|| invalid("unresolved dictionary"))?
            .entries()
            .get(index)
            .ok_or_else(|| invalid("missing dictionary entry"))?;
        Ok(Callable {
            function: entry.function(),
            captures: entry
                .capture_mapping()
                .iter()
                .map(|mapping| match mapping {
                    DictionaryEntryEvidence::Capture(index) => captures
                        .get(*index)
                        .cloned()
                        .ok_or_else(|| invalid("missing dictionary capture")),
                    DictionaryEntryEvidence::SelfDictionary => Ok(evidence.clone()),
                })
                .collect::<Result<_, _>>()?,
        })
    }

    /// Resolve only non-owning evidence/callees. No guest instructions or native calls run here.
    fn symbolic(
        &self,
        body: &Function,
        inputs: &[Input],
        definitions: &FxHashMap<ValueId, &Operation>,
        value: &mir::Value,
        depth: usize,
    ) -> Result<Binding, RuntimeError> {
        if depth >= 128 {
            return Err(unsupported("evidence nesting limit"));
        }
        let get = |value| self.symbolic(body, inputs, definitions, value, depth + 1);
        match value {
            mir::Value::Dictionary(id) => {
                Ok(Binding::Evidence(self.symbolic_dictionary(*id, vec![])?))
            }
            mir::Value::Evidence(e) => Ok(Binding::Evidence(self.symbolic_static_evidence(e, 0)?)),
            mir::Value::Function(function) => Ok(Binding::Callable(Callable {
                function: *function,
                captures: vec![],
            })),
            mir::Value::Parameter(id) => inputs
                .get(id.as_index())
                .and_then(|i| match i {
                    Input::Evidence(e) => Some(e.clone()),
                    _ => None,
                })
                .map(Binding::Evidence)
                .ok_or_else(|| {
                    unsupported("evidence or callees supplied through value parameters")
                }),
            mir::Value::Constant(id) => {
                match Scalar::from_literal(&body.constant(*id).representation)? {
                    Scalar::Bool(value) => Ok(Binding::Evidence(Evidence::Storage(value))),
                    _ => Err(invalid("expected storage evidence")),
                }
            }
            mir::Value::Register(id) => {
                let operation = definitions
                    .get(id)
                    .ok_or_else(|| invalid("missing evidence definition"))?;
                match &operation.kind {
                    OperationKind::BuildDictionary { definition, .. } => {
                        let captures = operation
                            .operands
                            .iter()
                            .map(|v| get(v)?.evidence())
                            .collect::<Result<_, _>>()?;
                        Ok(Binding::Evidence(
                            self.symbolic_dictionary(*definition, captures)?,
                        ))
                    }
                    OperationKind::DictEntry { entry_index, .. } => {
                        Ok(Binding::Callable(self.dictionary_entry(
                            get(&operation.operands[0])?.evidence()?,
                            entry_index.as_index(),
                        )?))
                    }
                    OperationKind::Load => get(&operation.operands[0]),
                    _ => Err(unsupported("data-dependent evidence or callees")),
                }
            }
            _ => Err(unsupported("subscript evidence")),
        }
    }

    /// Bind the current runtime's native layouts and host-boundary move-out glue.
    fn prepare_native_storage(&mut self) -> Result<(), RuntimeError> {
        let mut exports = FxHashMap::default();
        for module in self.program.modules() {
            for (_, native) in module.native_entries() {
                if let Some(export) = native.host_output() {
                    let ty = match native.signature().result {
                        NativeResult::Output(layout)
                        | NativeResult::Optional {
                            payload: layout, ..
                        } => layout.ty,
                        _ => continue,
                    };
                    exports.insert(ty, export);
                }
            }
        }
        for module in self.program.modules() {
            let env = ModuleEnv::new(
                self.session.expect_fresh_module(module.module()),
                self.session.raw_modules(),
            );
            for (layout, _) in module.native_layouts() {
                self.memory.prepare_native(
                    layout,
                    concrete_type_is_trivial_copy(layout.ty, &env),
                    exports.get(&layout.ty).copied(),
                )?;
            }
        }
        Ok(())
    }

    /// Check each reachable instantiation, including calls in untaken branches. The bound also
    /// prevents polymorphic recursion from expanding an unbounded preparation graph before fuel.
    fn check_supported(&mut self, entry: FunctionId) -> Result<(), RuntimeError> {
        let body = self
            .program
            .function(entry)
            .ok_or_else(|| unsupported("native host entry points"))?;
        let inputs = body
            .parameters()
            .iter()
            .map(|p| Input::Place(p.ty))
            .collect::<Vec<_>>();
        let mut pending = vec![(entry, inputs)];
        let mut visited = FxHashSet::default();
        let mut required_evidence = FxHashSet::default();
        while let Some((id, inputs)) = pending.pop() {
            if !visited.insert((id, inputs.clone())) {
                continue;
            }
            if visited.len() > 4096 {
                return Err(unsupported("generic preparation limit"));
            }
            let Some(body) = self.program.function(id) else {
                let native = self.native(id)?;
                if !native.supports_physical_call() {
                    return Err(unsupported("this native adapter"));
                }
                let env = self.env(id);
                for parameter in &native.signature().parameters {
                    self.memory.prepare_type(parameter.layout().ty, &env)?;
                }
                match native.signature().result {
                    NativeResult::Scalar(layout, _) | NativeResult::Output(layout) => {
                        self.memory.prepare_type(layout.ty, &env)?;
                    }
                    NativeResult::Unit | NativeResult::Never => (),
                    NativeResult::Optional { payload, ty } => {
                        self.memory.prepare_type(payload.ty, &env)?;
                        self.memory.prepare_type(ty, &env)?;
                    }
                    NativeResult::Addressor { pointee, .. } => {
                        self.memory.prepare_type(pointee.ty, &env)?;
                    }
                }
                continue;
            };
            if !matches!(
                body.result_convention(),
                CallResultConvention::Value | CallResultConvention::ADDRESSOR_PLACE
            ) {
                return Err(unsupported("place/yield call conventions"));
            }
            let types = RuntimeTypes::for_call(body, &inputs)?;
            let env = self.env(id);
            let roles = ValueRoles::derive(body);
            let operations = body
                .blocks()
                .flat_map(|b| {
                    let b = body.block(b);
                    b.operations().iter().chain(match &b.terminator().kind {
                        TerminatorKind::Invoke { operation, .. } => Some(operation),
                        _ => None,
                    })
                })
                .collect::<Vec<_>>();
            let definitions = operations
                .iter()
                .filter_map(|op| op.result_id().map(|id| (id, *op)))
                .collect();
            for parameter in body.parameters() {
                if parameter.kind != ParameterKind::Dictionary {
                    self.memory
                        .prepare_type(types.resolve(parameter.ty), &env)?;
                }
            }
            for constant in body.constants() {
                let ty = types.resolve(constant.ty);
                self.memory.prepare_type(ty, &env)?;
                self.memory.literal(ty, &constant.representation)?;
            }
            for operation in operations {
                Self::check_operation(operation)?;
                required_evidence.extend(
                    operation
                        .operands
                        .iter()
                        .filter_map(|v| self.program.evidence_id(v)),
                );
                match &operation.kind {
                    OperationKind::Alloca { ty }
                    | OperationKind::AddressOffset { ty, .. }
                    | OperationKind::Clone { ty }
                    | OperationKind::Drop { ty }
                    | OperationKind::MoveBytes { ty } => {
                        self.memory.prepare_type(types.resolve(*ty), &env)?
                    }
                    OperationKind::AllocaPlace { pointing_to }
                    | OperationKind::AddressOffsetPlace { pointing_to } => self
                        .memory
                        .prepare_type(types.resolve(*pointing_to), &env)?,
                    OperationKind::RuntimeAlloc { pointee } => {
                        self.memory.prepare_type(types.resolve(*pointee), &env)?
                    }
                    OperationKind::Variant { metadata, .. } => {
                        self.memory.prepare_type(types.resolve(metadata.ty), &env)?
                    }
                    OperationKind::BuildDictionary { .. } | OperationKind::DictEntry { .. } => {
                        self.symbolic(
                            body,
                            &inputs,
                            &definitions,
                            &mir::Value::Register(operation.result_id().unwrap()),
                            0,
                        )?;
                    }
                    _ => (),
                }
                let witness_index = match &operation.kind {
                    OperationKind::Alloca { .. } if !operation.operands.is_empty() => Some(0),
                    OperationKind::Move | OperationKind::Replace
                        if operation.operands.len() == 3 =>
                    {
                        Some(2)
                    }
                    OperationKind::Variant {
                        has_layout_witness: true,
                        ..
                    } => Some(operation.operands.len() - 1),
                    _ => None,
                };
                if let Some(index) = witness_index {
                    let witness = self
                        .symbolic(body, &inputs, &definitions, &operation.operands[index], 0)?
                        .evidence()?;
                    self.memory.prepare_type(witness.layout_type()?, &env)?;
                    for entry in self.layout_entries(&witness)? {
                        let callable = self.dictionary_entry(witness.clone(), entry)?;
                        let mut inputs = callable
                            .captures
                            .into_iter()
                            .map(Input::Evidence)
                            .collect::<Vec<_>>();
                        inputs.push(Input::Place(ScalarKind::Int.ty()));
                        pending.push((callable.function, inputs));
                    }
                }
                let callee_index = match operation.kind {
                    OperationKind::Call { .. } => 0,
                    OperationKind::Clone { .. } => 2,
                    OperationKind::Drop { .. } => 1,
                    _ => continue,
                };
                let callable = self
                    .symbolic(
                        body,
                        &inputs,
                        &definitions,
                        &operation.operands[callee_index],
                        0,
                    )?
                    .callable()?;
                let mut target_inputs = callable
                    .captures
                    .iter()
                    .map(|e| Input::Evidence(e.clone()))
                    .collect::<Vec<_>>();
                let values = if callee_index == 0 {
                    operation.operands[1..].iter().collect::<Vec<_>>()
                } else {
                    operation.operands[callee_index + 1..]
                        .iter()
                        .chain(operation.operands[..callee_index].iter())
                        .collect()
                };
                for value in values {
                    let role = roles
                        .get(value, body.constants())
                        .ok_or_else(|| invalid("missing operand role"))?;
                    let pointee = role.place_pointee_type();
                    if let Some(mut ty) = pointee {
                        while let MirType::Pointer(inner) = ty {
                            ty = *inner;
                        }
                        let MirType::Lowered(ty) = ty else {
                            unreachable!()
                        };
                        target_inputs.push(Input::Place(types.resolve(ty)));
                    } else {
                        let evidence = self
                            .symbolic(body, &inputs, &definitions, value, 0)?
                            .evidence()?;
                        target_inputs.push(Input::Evidence(evidence));
                    }
                }
                if callee_index == 1 {
                    target_inputs.push(Input::Place(Type::unit()));
                }
                pending.push((callable.function, target_inputs));
            }
            for block in body.blocks() {
                let terminator = body.block(block).terminator();
                required_evidence.extend(
                    terminator
                        .operands()
                        .iter()
                        .filter_map(|v| self.program.evidence_id(v)),
                );
                match &terminator.kind {
                    TerminatorKind::Invoke { .. }
                    | TerminatorKind::Goto { .. }
                    | TerminatorKind::CondBr { .. }
                    | TerminatorKind::SwitchVariant { .. }
                    | TerminatorKind::Return
                    | TerminatorKind::PropagateError
                    | TerminatorKind::FailureDuringCleanup
                    | TerminatorKind::InvariantFailure { .. } => (),
                    _ => return Err(unsupported("yielded places")),
                }
            }
        }
        self.prepare_static_evidence(required_evidence)
    }

    fn check_operation(operation: &Operation) -> Result<(), RuntimeError> {
        // Physical preparation already verifies operand arities; this checks execution capabilities.
        use OperationKind::*;
        match &operation.kind {
            CompareEqual => {
                let mir::Value::Pattern(pattern) = &operation.operands[1] else {
                    return Err(invalid("expected literal pattern"));
                };
                Self::check_pattern(pattern)?;
            }
            Alloca { .. }
            | Clone { .. }
            | Drop { .. }
            | Call { .. }
            | DictEntry { .. }
            | BuildDictionary { .. }
            | AddressOffset { .. }
            | AddressOffsetPlace { .. }
            | AllocaPlace { .. }
            | RuntimeAlloc { .. }
            | RuntimeDealloc
            | ExtractTag
            | ExtractPayloadIndirection
            | MoveBytes { .. }
            | Load
            | Store
            | Clear
            | Memcpy
            | Move
            | Replace
            | IsInitialized
            | StackSave
            | StackRestore
            | CheckCallDepth
            | CheckFuel
            | Variant { .. } => (),
            _ => return Err(unsupported("aggregate, address, or callable operations")),
        }
        Ok(())
    }

    fn check_pattern(pattern: &LiteralValue) -> Result<(), RuntimeError> {
        if matches!(pattern, LiteralValue::VariantTag(_)) {
            Ok(())
        } else if let LiteralValue::Tuple(fields) = pattern {
            for field in fields.iter() {
                if matches!(field, LiteralValue::VariantTag(_)) {
                    return Err(invalid("symbolic tags are not product values"));
                }
                Self::check_pattern(field)?;
            }
            Ok(())
        } else {
            Scalar::from_literal(pattern).map(|_| ())
        }
    }

    fn call(&mut self, id: FunctionId, args: Vec<Binding>) -> Result<(), RuntimeError> {
        let Some(body) = self.program.function(id) else {
            return self.call_native(id, &args);
        };
        let inputs = args
            .iter()
            .map(|arg| match arg {
                Binding::Evidence(e) => Ok(Input::Evidence(e.clone())),
                Binding::Scalar(Scalar::Bool(value)) => {
                    Ok(Input::Evidence(Evidence::Storage(*value)))
                }
                _ => Ok(Input::Place(arg.place()?.ty)),
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let types = RuntimeTypes::for_call(body, &inputs)?;
        for (argument, parameter) in args.iter().zip(body.parameters()) {
            if parameter.kind == ParameterKind::Dictionary {
                continue;
            }
            // Call boundaries retain exact types. Representation-compatible stores are a separate
            // bridge between nominal products and the structural values used to construct them.
            if argument.place()?.ty != types.resolve(parameter.ty) {
                return Err(invalid("call argument type mismatch"));
            }
            let pointer_result = parameter.kind == ParameterKind::Return
                && body.result_convention() == CallResultConvention::ADDRESSOR_PLACE;
            if self.memory.is_pointer_slot(argument.place()?)? != pointer_result {
                return Err(invalid("call argument storage role mismatch"));
            }
        }
        // Explicit CheckCallDepth operations preserve the boxed executor's source-level policy.
        let marker = self.memory.len();
        let previous_types = mem::replace(&mut self.types, types);
        self.depth += 1;
        let result = self.run_frame(body, &args, marker);
        self.depth -= 1;
        self.types = previous_types;
        self.memory.restore(marker);
        result
    }

    fn invoke(&mut self, callable: Callable, args: Vec<Binding>) -> Result<(), RuntimeError> {
        let args = callable
            .captures
            .into_iter()
            .map(Binding::Evidence)
            .chain(args)
            .collect();
        self.call(callable.function, args)
    }

    fn operand(
        &self,
        body: &Function,
        args: &[Binding],
        registers: &FxHashMap<ValueId, Binding>,
        operand: &mir::Value,
    ) -> Result<Binding, RuntimeError> {
        match operand {
            mir::Value::Dictionary(_) | mir::Value::Evidence(_) => {
                let id = self
                    .program
                    .evidence_id(operand)
                    .ok_or_else(|| invalid("unresolved static evidence"))?;
                self.static_evidence
                    .get(&id)
                    .cloned()
                    .map(Binding::Evidence)
                    .ok_or_else(|| invalid("unprepared static evidence"))
            }
            mir::Value::Function(function) => Ok(Binding::Callable(Callable {
                function: *function,
                captures: vec![],
            })),
            mir::Value::Constant(id) => {
                let constant = body.constant(*id);
                if let Ok(scalar) = Scalar::from_literal(&constant.representation) {
                    Ok(Binding::Scalar(scalar))
                } else {
                    Ok(Binding::Aggregate(Rc::new(self.memory.literal(
                        self.types.resolve(constant.ty),
                        &constant.representation,
                    )?)))
                }
            }
            mir::Value::Parameter(id) => args
                .get(id.as_index())
                .cloned()
                .ok_or_else(|| invalid("unbound parameter")),
            mir::Value::Register(id) => registers
                .get(id)
                .cloned()
                .ok_or_else(|| invalid("unbound register")),
            _ => Err(invalid("unsupported operand")),
        }
    }

    fn run_frame(
        &mut self,
        body: &Function,
        args: &[Binding],
        frame_base: usize,
    ) -> Result<(), RuntimeError> {
        let mut registers = FxHashMap::default();
        let result = self.run_blocks(body, args, &mut registers, frame_base);
        // Evidence registers own references independently of stack storage. In particular, CSE
        // may reuse a pure dictionary construction across StackRestore boundaries.
        for binding in registers.values() {
            self.release_binding(binding)?;
        }
        result
    }

    fn run_blocks(
        &mut self,
        body: &Function,
        args: &[Binding],
        registers: &mut FxHashMap<ValueId, Binding>,
        frame_base: usize,
    ) -> Result<(), RuntimeError> {
        let mut block = body.entry();
        let mut pending: Option<RuntimeError> = None;
        let mut secondary: Option<RuntimeError> = None;
        loop {
            let current = body.block(block);
            for operation in current.operations() {
                self.operation(body, args, registers, operation, frame_base)
                    .map_err(|error| match pending.take() {
                        Some(initial) => initial.interrupted_by(error),
                        None => error,
                    })?;
            }
            match &current.terminator().kind {
                TerminatorKind::Goto { target } => block = *target,
                TerminatorKind::CondBr {
                    condition,
                    then_target,
                    else_target,
                } => {
                    let Scalar::Bool(taken) =
                        self.operand(body, args, registers, condition)?.scalar()?
                    else {
                        return Err(invalid("non-boolean branch condition"));
                    };
                    block = if taken { *then_target } else { *else_target };
                }
                TerminatorKind::Invoke {
                    operation,
                    normal,
                    error,
                } => match self.operation(body, args, registers, operation, frame_base) {
                    Ok(()) => block = *normal,
                    Err(failure @ RuntimeError::SourceFailure(_)) => {
                        if pending.is_none() {
                            pending = Some(failure);
                        } else {
                            secondary = Some(failure);
                        }
                        block = *error;
                    }
                    Err(failure) => {
                        return Err(match pending.take() {
                            Some(initial) => initial.interrupted_by(failure),
                            None => failure,
                        });
                    }
                },
                TerminatorKind::SwitchVariant {
                    tag,
                    cases,
                    default,
                } => {
                    let Binding::Tag(tag) = self.operand(body, args, registers, tag)? else {
                        return Err(invalid("expected variant tag"));
                    };
                    block = cases
                        .iter()
                        .find(|(case, _)| *case == tag)
                        .map_or(*default, |(_, target)| *target);
                }
                TerminatorKind::Return => {
                    if pending.is_some() {
                        return Err(invalid("return during source failure"));
                    }
                    return Ok(());
                }
                TerminatorKind::PropagateError => {
                    return Err(pending.ok_or_else(|| invalid("no failure to propagate"))?);
                }
                TerminatorKind::FailureDuringCleanup => {
                    return Err(pending
                        .ok_or_else(|| invalid("no initial cleanup failure"))?
                        .interrupted_by(
                            secondary.ok_or_else(|| invalid("no secondary cleanup failure"))?,
                        ));
                }
                TerminatorKind::InvariantFailure { message } => {
                    eprintln!("Ferlium invariant failure: {message}");
                    abort();
                }
                _ => unreachable!("capability check rejected this terminator"),
            }
        }
    }

    fn operation(
        &mut self,
        body: &Function,
        args: &[Binding],
        registers: &mut FxHashMap<ValueId, Binding>,
        operation: &Operation,
        frame_base: usize,
    ) -> Result<(), RuntimeError> {
        use OperationKind::*;
        let operand =
            |index: usize| self.operand(body, args, registers, &operation.operands[index]);
        let place = |index| operand(index)?.place();
        let witness = match &operation.kind {
            Alloca { ty } if !operation.operands.is_empty() => Some((0, self.types.resolve(*ty))),
            Move | Replace if operation.operands.len() == 3 => Some((2, place(0)?.ty)),
            Variant {
                metadata,
                has_layout_witness: true,
                ..
            } => Some((
                operation.operands.len() - 1,
                self.types.resolve(metadata.payload_ty),
            )),
            _ => None,
        };
        let witnessed_layout = if let Some((index, ty)) = witness {
            let evidence = operand(index)?.evidence()?;
            if evidence.layout_type()? != ty {
                return Err(invalid("layout evidence differs from storage type"));
            }
            let layout = self.witness_layout(evidence, operation.span)?;
            if matches!(operation.kind, Variant { .. }) {
                self.memory.check_type_layout(ty, layout[0], layout[1])?;
            }
            Some(layout)
        } else {
            None
        };
        let operand =
            |index: usize| self.operand(body, args, registers, &operation.operands[index]);
        let place = |index| operand(index)?.place();
        if let Clone { ty } | Drop { ty } | MoveBytes { ty } = &operation.kind {
            if place(0)?.ty != self.types.resolve(*ty) {
                return Err(invalid("operation type differs from storage type"));
            }
        }
        let result = match &operation.kind {
            BuildDictionary { definition, .. } => {
                let captures = (0..operation.operands.len())
                    .map(|i| operand(i)?.evidence())
                    .collect::<Result<_, _>>()?;
                let evidence =
                    self.build_evidence(*definition, captures, false, Some(operation.span))?;
                Some(Binding::Evidence(evidence))
            }
            DictEntry { entry_index, .. } => Some(Binding::Callable(
                self.dictionary_entry(operand(0)?.evidence()?, entry_index.as_index())?,
            )),
            Alloca { ty } => {
                let ty = self.types.resolve(*ty);
                Some(Binding::Place(match witnessed_layout {
                    Some([size, align]) => {
                        self.memory
                            .allocate_witnessed(ty, size, align, Some(operation.span))?
                    }
                    None => self.memory.allocate(ty, Some(operation.span))?,
                }))
            }
            AllocaPlace { pointing_to } => Some(Binding::Place(
                self.memory
                    .allocate_place(self.types.resolve(*pointing_to), Some(operation.span))?,
            )),
            RuntimeAlloc { pointee } => {
                let (Scalar::Int(size), Scalar::Int(align)) =
                    (operand(0)?.scalar()?, operand(1)?.scalar()?)
                else {
                    return Err(invalid("non-integer allocation layout"));
                };
                let size =
                    usize::try_from(size).map_err(|_| invalid("negative allocation size"))?;
                let align =
                    usize::try_from(align).map_err(|_| invalid("negative allocation alignment"))?;
                Some(Binding::Place(self.memory.allocate_runtime(
                    self.types.resolve(*pointee),
                    size,
                    align,
                    Some(operation.span),
                )?))
            }
            RuntimeDealloc => {
                self.memory.deallocate(place(0)?)?;
                None
            }
            AddressOffsetPlace { .. } => {
                let Scalar::Int(offset) = operand(1)?.scalar()? else {
                    return Err(invalid("non-integer offset"));
                };
                let offset = usize::try_from(offset).map_err(|_| invalid("negative offset"))?;
                Some(Binding::Place(self.memory.pointer_slot(place(0)?, offset)?))
            }
            AddressOffset { ty, member } => {
                let Scalar::Int(offset) = operand(1)?.scalar()? else {
                    return Err(invalid("non-integer offset"));
                };
                let offset = usize::try_from(offset).map_err(|_| invalid("negative offset"))?;
                Some(Binding::Place(self.memory.project(
                    place(0)?,
                    offset,
                    self.types.resolve(*ty),
                    *member,
                )?))
            }
            Load => match operand(0)? {
                Binding::Callable(callable) => Some(Binding::Callable(callable)),
                source => {
                    let address = source.place()?;
                    Some(if self.memory.is_pointer_slot(address)? {
                        Binding::Place(self.memory.read_pointer(address)?)
                    } else if ScalarKind::for_type(address.ty).is_ok() {
                        Binding::Scalar(self.memory.read(address)?)
                    } else {
                        Binding::Aggregate(Rc::new(self.memory.read_value(address, false)?))
                    })
                }
            },
            Store => {
                let destination = place(1)?;
                match operand(0)? {
                    Binding::Scalar(value) => self.memory.write(destination, value)?,
                    Binding::Aggregate(value) => self.memory.write_value(destination, &value)?,
                    Binding::Place(value) => self.memory.write_pointer(destination, value)?,
                    _ => return Err(invalid("expected a value register")),
                }
                None
            }
            Clear => {
                self.memory.clear(place(0)?)?;
                None
            }
            IsInitialized => Some(Binding::Scalar(Scalar::Bool(
                self.memory.initialized(place(0)?)?,
            ))),
            Memcpy | Move | MoveBytes { .. } => {
                let source = place(0)?;
                let destination = place(1)?;
                if matches!(operation.kind, Move | MoveBytes { .. }) && source != destination {
                    self.memory.check_consume(source)?;
                }
                if let Some([size, align]) = witnessed_layout {
                    self.memory.check_layout(source, size, align)?;
                }
                if matches!(operation.kind, MoveBytes { .. }) {
                    let Scalar::Int(size) = operand(2)?.scalar()? else {
                        return Err(invalid("non-integer transfer size"));
                    };
                    if usize::try_from(size).ok() != Some(self.memory.size(source)?) {
                        return Err(invalid("transfer size differs from value layout"));
                    }
                }
                if source != destination && self.memory.overlaps(source, destination)? {
                    return Err(invalid("partially overlapping transfer"));
                }
                let value = self.memory.read_value(source, false)?;
                self.memory.write_value(destination, &value)?;
                if matches!(operation.kind, Move | MoveBytes { .. }) && source != destination {
                    self.memory.clear(source)?;
                }
                None
            }
            Replace => {
                let source = place(0)?;
                let destination = place(1)?;
                if let Some([size, align]) = witnessed_layout {
                    self.memory.check_layout(source, size, align)?;
                }
                // Replacement exchanges ownership of the same type; it is not a structural cast.
                if self.memory.overlaps(source, destination)? || source.ty != destination.ty {
                    return Err(invalid("invalid replacement storage"));
                }
                self.memory.replace_value(source, destination)?;
                None
            }
            Clone { .. } => {
                let callable = operand(2)?.callable()?;
                let id = callable.function;
                let values = (3..operation.operands.len())
                    .chain(0..2)
                    .map(operand)
                    .collect::<Result<_, _>>()?;
                self.invoke(callable, values)
                    .map_err(|error| error.with_frame(id, operation.span))?;
                None
            }
            Drop { .. } => {
                let address = place(0)?;
                // Drop must not skip an aggregate with remaining live fields. Partial-construction
                // cleanup is emitted per field (or through a structural drop body); a custom
                // destructor must only be called once its receiver is fully constructed.
                // IsInitialized, by contrast, asks whether the entire selected value is present.
                if self.memory.any_initialized(address)? {
                    let callable = operand(1)?.callable()?;
                    let id = callable.function;
                    let mut values = (2..operation.operands.len())
                        .map(operand)
                        .collect::<Result<Vec<_>, _>>()?;
                    let marker = self.memory.len();
                    let result = self
                        .memory
                        .allocate(ScalarKind::Unit.ty(), Some(operation.span))?;
                    values.extend([Binding::Place(address), Binding::Place(result)]);
                    let outcome = self.invoke(callable, values);
                    self.memory.restore(marker);
                    outcome.map_err(|error| error.with_frame(id, operation.span))?;
                    self.memory.clear(address)?;
                }
                None
            }
            CompareEqual => {
                let mir::Value::Pattern(pattern) = &operation.operands[1] else {
                    return Err(invalid("expected literal pattern"));
                };
                let equal = match operand(0)? {
                    Binding::Tag(tag) => {
                        let LiteralValue::VariantTag(pattern) = &**pattern else {
                            return Err(invalid("expected symbolic tag pattern"));
                        };
                        tag == *pattern
                    }
                    Binding::Place(address) => self.memory.matches(address, pattern)?,
                    Binding::Aggregate(value) => {
                        *value == self.memory.literal(value.ty, pattern)?
                    }
                    value => value.scalar()? == Scalar::from_literal(pattern)?,
                };
                Some(Binding::Scalar(Scalar::Bool(equal)))
            }
            Variant {
                tag,
                metadata,
                storage,
                ..
            } => Some(Binding::Aggregate(Rc::new(self.memory.shell(
                self.types.resolve(metadata.ty),
                *tag,
                match storage {
                    Some(storage) => *storage,
                    None => {
                        let Scalar::Bool(indirect) = operand(0)?.scalar()? else {
                            return Err(invalid("expected variant storage evidence"));
                        };
                        VariantPayloadStorage::from_indirect(indirect)
                    }
                },
            )?))),
            ExtractTag => Some(Binding::Tag(self.memory.tag(place(0)?)?.0)),
            ExtractPayloadIndirection => Some(Binding::Scalar(Scalar::Bool(
                self.memory.tag(place(0)?)?.1.is_indirect(),
            ))),
            Call { .. } => {
                let callable = operand(0)?.callable()?;
                let id = callable.function;
                let values = operation.operands[1..]
                    .iter()
                    .map(|value| self.operand(body, args, registers, value))
                    .collect::<Result<Vec<_>, _>>()?;
                self.invoke(callable, values)
                    .map_err(|error| error.with_frame(id, operation.span))?;
                None
            }
            StackSave => Some(Binding::StackMarker(self.memory.len())),
            StackRestore => {
                let Binding::StackMarker(marker) = operand(0)? else {
                    return Err(invalid("expected stack marker"));
                };
                if marker < frame_base || marker > self.memory.len() {
                    return Err(invalid("stack marker outside frame"));
                }
                self.memory.restore(marker);
                None
            }
            CheckCallDepth => {
                if self.depth >= self.limits.execution.call_depth_limit {
                    return Err(RuntimeError::new_sandbox_violation(
                        SandboxViolationKind::CallDepthLimitExceeded {
                            limit: self.limits.execution.call_depth_limit,
                        },
                        Some(operation.span),
                    ));
                }
                None
            }
            CheckFuel => {
                if let Some(fuel) = &mut self.fuel {
                    if *fuel == 0 {
                        return Err(RuntimeError::new_sandbox_violation(
                            SandboxViolationKind::FuelExhausted,
                            Some(operation.span),
                        ));
                    }
                    *fuel -= 1;
                }
                None
            }
            _ => unreachable!("capability check rejected this operation"),
        };
        if let Some(value) = result {
            // Construction transfers its initial owner; other results retain borrowed evidence.
            if !matches!(operation.kind, BuildDictionary { .. }) {
                self.retain_binding(&value)?;
            }
            if let Some(previous) = registers.insert(
                operation.result_id().expect("value-producing operation"),
                value,
            ) {
                self.release_binding(&previous)?;
            }
        }
        Ok(())
    }

    fn call_native(&mut self, id: FunctionId, args: &[Binding]) -> Result<(), RuntimeError> {
        let native = self.native(id)?;
        let signature = native.signature();
        let (output, inputs) = args
            .split_last()
            .ok_or_else(|| invalid("native result missing"))?;
        if inputs.len() != signature.parameters.len() {
            return Err(invalid("native arity mismatch"));
        }
        let output = output.place()?;
        let addressor = matches!(signature.result, NativeResult::Addressor { .. });
        if self.memory.is_pointer_slot(output)? != addressor || output.ty != signature.result.ty() {
            return Err(invalid("invalid native output storage"));
        }
        let mut addresses = Vec::with_capacity(inputs.len());
        for (input, parameter) in inputs.iter().zip(&signature.parameters) {
            let address = input.place()?;
            self.memory.check_native(address, parameter.layout())?;
            match parameter {
                NativeParameter::Mutable(_) => self.memory.check_write(address)?,
                NativeParameter::Consuming(_) => self.memory.check_consume(address)?,
                _ => (),
            }
            if self.memory.overlaps(address, output)?
                && !matches!(parameter, NativeParameter::Scalar(..))
            {
                return Err(invalid("native output aliases an input"));
            }
            addresses.push(address);
        }
        for (index, address) in addresses.iter().enumerate() {
            for (other_index, other) in addresses[..index].iter().enumerate() {
                if self.memory.overlaps(*address, *other)?
                    && !matches!(signature.parameters[index], NativeParameter::Scalar(..))
                    && !matches!(
                        signature.parameters[other_index],
                        NativeParameter::Scalar(..)
                    )
                    && (matches!(
                        signature.parameters[index],
                        NativeParameter::Mutable(_) | NativeParameter::Consuming(_)
                    ) || matches!(
                        signature.parameters[other_index],
                        NativeParameter::Mutable(_) | NativeParameter::Consuming(_)
                    ))
                {
                    return Err(invalid("overlapping mutable native arguments"));
                }
            }
        }
        // Scalar transport copies before establishing *any* native reference. Optimized MIR may
        // legitimately reuse an input's storage as the output or as another mutable argument.
        let mut scalars = addresses
            .iter()
            .zip(&signature.parameters)
            .map(|(address, parameter)| {
                if matches!(parameter, NativeParameter::Scalar(..)) {
                    self.memory.read(*address).map(Some)
                } else {
                    Ok(None)
                }
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        // Invalidate saved opaque bytes before any mutable native access, also on source failure.
        for (address, parameter) in addresses.iter().zip(&signature.parameters) {
            match parameter {
                NativeParameter::Mutable(_) => self.memory.native_mutated(*address)?,
                NativeParameter::Shared(_) => self.memory.invalidate_native_snapshot(*address)?,
                _ => (),
            }
        }
        let pointers = addresses
            .iter()
            .zip(&mut scalars)
            .map(|(address, scalar)| match scalar {
                Some(value) => Ok(value.pointer()),
                None => self.memory.pointer(*address),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let marker = self.memory.len();
        let payload = match signature.result {
            NativeResult::Optional { payload, .. } => Some(self.memory.allocate(payload.ty, None)?),
            _ => None,
        };
        let mut member_pointer: *mut u8 = ptr::null_mut();
        let output_pointer = if addressor {
            ptr::from_mut(&mut member_pointer).cast()
        } else {
            self.memory.pointer(payload.unwrap_or(output))?
        };
        // TrivialCopy result slots may be reused. Present an absent output to the C protocol,
        // and only mark it initialized after success (also when the previous result was live).
        self.memory.prepare_output(output)?;
        let mut failure = NativeFailureState::default();
        // SAFETY: layouts, initialization, liveness and disjointness were checked above. Addresses
        // are stable; no interpreter storage access occurs until the adapter's Rust borrows end.
        let outcome = unsafe { native.invoke_physical(&pointers, output_pointer, &mut failure) }?;
        if signature.result == NativeResult::Never {
            return Err(invalid("never native returned success"));
        }
        for (address, parameter) in addresses.iter().zip(&signature.parameters) {
            if matches!(parameter, NativeParameter::Consuming(_)) {
                self.memory.consume_native(*address)?;
            }
        }
        if let NativeResult::Addressor {
            pointee,
            root,
            mutable,
        } = signature.result
        {
            // SAFETY: the typed adapter and unsafe registration establish a live rooted member;
            // Memory additionally checks alignment, receiver lifetime, and access permissions.
            let member = unsafe {
                self.memory.native_member(
                    addresses[root as usize],
                    member_pointer,
                    pointee.ty,
                    mutable,
                    Location::new_synthesized(),
                )
            }?;
            self.memory.write_pointer(output, member)?;
        } else if let Some(payload) = payload {
            let present = match outcome {
                NativeCallOutcome::Initialized => {
                    self.memory.mark_initialized(payload)?;
                    true
                }
                NativeCallOutcome::Absent => false,
            };
            self.memory.finish_optional(output, payload, present)?;
            self.memory.restore(marker);
        } else {
            self.memory.mark_initialized(output)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Location, mir::physical::program::resolve_physical_program};
    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::wasm_bindgen_test;

    #[test]
    fn physical_static_evidence_preparation_is_entry_scoped() {
        use crate::module::Path;
        use ustr::ustr;

        let mut session = CompilerSession::new();
        let module = session.compile(
            "pub fn compute() -> int { 42 } pub fn unused(x: int) -> string { to_string((x, true)) }",
            "evidence_scope", Path::single_str("evidence_scope"),
        ).unwrap().module_id;
        let entry = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("compute"))
            .unwrap();
        let program = session.prepare_physical_program(module).unwrap();
        assert!(!program.static_evidence().is_empty());
        let mut interpreter = Interpreter {
            program: &program,
            memory: Memory::default(),
            limits: ReferenceInterpreterLimits::default(),
            fuel: None,
            depth: 0,
            session: &session,
            types: RuntimeTypes::default(),
            static_evidence: FxHashMap::default(),
        };
        interpreter
            .check_supported(FunctionId::new(module, entry))
            .unwrap();
        assert!(
            interpreter.static_evidence.is_empty(),
            "a scalar entry needs none of the program's static evidence"
        );
    }

    #[cfg_attr(not(target_arch = "wasm32"), test)]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn physical_generic_bodies_execute_without_specialization() {
        use crate::{
            ExecutionTarget, MirOptimization,
            mir::physical::lower_physical_mir,
            module::Path,
            std::{STD_MODULE_ID, math::int_value},
        };
        use ustr::ustr;

        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        let support = session.compile(
            "pub trait Describe<Self> { fn describe(value: Self) -> int; } impl Describe for int { fn describe(value: int) -> int { value } } pub struct Wrapper<T>(T) impl<T> Describe for Wrapper<T> where T: Describe, T: Value { fn describe(value: Wrapper<T>) -> int { describe(value.0) + 1 } } pub fn forward<T>(value: T) -> int where T: Describe, T: Value { describe(value) }
             pub trait Tag<Self> { fn tag(value: Self) -> int; } impl<A> Tag for Wrapper<A> { fn tag(value: Wrapper<A>) -> int { 42 } } pub fn tagged<T>(value: T) -> int where T: Tag { tag(value) }
             pub fn tag_wrapped<U>(value: U) -> int { tagged(Wrapper(value)) }",
            "generic_traits", Path::single_str("generic_traits"),
        ).unwrap().module_id;
        session.prepare_execution_target(ExecutionTarget::Mir, support);
        // Keep this invariant test: ordinary optimized execution can specialize away every
        // dictionary parameter, even after the physical backend joins the full language suite.
        for (source, supported) in [
            "fn duplicate<T>(x: T) -> (T, T) { (x, x) } fn compute(x: int) -> ((int, bool), (int, bool)) { duplicate((x, true)) }",
            // Repeated constructions overwrite evidence registers; their owners must not accumulate.
            "fn repeat<T>(x: T) -> T { let mut n = 0; loop { let pair = (x, x); if n == 3 { return pair.0; }; n += 1; } } fn compute(x: int) -> (int, bool) { repeat((x, true)) }",
            "fn replace<T>(x: &mut T, y: T) { x = y; } fn compute(x: int) -> (int, bool) { let mut p = (1, false); replace(p, (x, true)); p }",
            "enum List<T> { Nil, Cons(T, List<T>) } fn duplicate<T>(x: T) -> (T, T) { (x, x) } fn compute(x: int) -> (List<int>, List<int>) { duplicate(List::Cons(x, List::Nil)) }",
            "fn first<T, U>(p: (T, U)) -> T { p.0 } fn compute(x: int) -> (int, bool) { first(((x, true), ())) }",
            "struct Record<T> { a: bool, b: T, c: int } fn member<T>(p: Record<T>) -> T { p.b } fn compute(x: int) -> (int, bool) { member(Record { a: true, b: (x, false), c: 9 }) }",
            "fn equal<T>(a: T, b: T) -> bool { a == b } fn compute(x: int) -> bool { equal((x, true), (7, true)) }",
            "use generic_traits::*; fn compute(x: int) -> int { forward(Wrapper(Wrapper(x))) }",
            // Tag has no captures: its concrete dictionary type must not inherit the impl's A.
            "use generic_traits::*; fn compute(x: int) -> int { tagged(Wrapper(x)) }",
            // Generic construction forwards Tag<Wrapper<U>> as evidence from the concrete caller.
            "use generic_traits::*; fn compute(x: int) -> int { tag_wrapped(x) }",
            "enum Choice<T> { Nothing, Item(T) } fn wrap<T>(x: T) -> Choice<T> { Choice::Item(x) } fn unwrap<T>(x: Choice<T>, fallback: T) -> T { match x { Nothing => fallback, Item(v) => v } } fn compute(x: int) -> (int, bool) { unwrap(wrap((x, true)), (0, false)) }",
            "enum List<T> { Nil, Cons(T, List<T>) } fn fail<T>(value: T, n: int) -> (T, int) { (value, idiv(10, n)) } fn compute(x: int) -> (List<int>, int) { fail(List::Cons(x, List::Nil), x - 7) }",
            "struct Probe(int) impl Value for Probe { fn eq(a: Probe, b: Probe) -> bool { a.0 == b.0 } fn to_string(a: Probe) -> string { to_string(a.0) } fn hash(a: Probe, s: &mut hasher) { hash(a.0, s) } fn clone(a: Probe) -> Probe { Probe(a.0 + 1) } fn drop(a: &mut Probe) { a.0 = 0; } } fn duplicate<T>(x: T) -> (T, T) { (x, x) } fn compute(x: int) -> int { let p = duplicate(Probe(x)); p.0.0 + p.1.0 }",
        ].into_iter().map(|source| (source, true)).chain([
            ("fn maybe<T>(value: T, n: int) -> T { if n == 0 { to_string(value); }; value } fn compute(x: int) -> int { maybe(x, x) }", true),
            // Capability preparation still visits unsupported calls in untaken branches.
            ("fn maybe<T>(value: T, n: int) -> T { if n == 0 { let f = |x| x; f(value); }; value } fn compute(x: int) -> int { maybe(x, x) }", false),
        ]) {
            let module = session
                .compile(source, "generic", Path::single_str("generic"))
                .unwrap()
                .module_id;
            session.prepare_execution_target(ExecutionTarget::Mir, module);
            let entry = session
                .expect_fresh_module(module)
                .get_local_function_id(ustr("compute"))
                .unwrap();
            let expected =
                session.run_entry(ExecutionTarget::Mir, module, entry, vec![int_value(7)]);
            let artifacts = [STD_MODULE_ID, support, module].map(|id| {
                let raw = session
                    .mir_artifacts_for(id, MirOptimization::Disabled)
                    .unwrap();
                lower_physical_mir(
                    id,
                    raw,
                    ModuleEnv::new(session.expect_fresh_module(id), session.raw_modules()),
                    session.known_callees(),
                )
                .unwrap()
            });
            let program = resolve_physical_program(artifacts.iter()).unwrap();
            let actual = run_entry(
                &program,
                FunctionId::new(module, entry),
                &mut [int_value(7)],
                ReferenceInterpreterLimits::default(),
                &session,
            );
            if !supported {
                assert!(matches!(actual, Err(RuntimeError::Backend(_))), "{actual:?}");
                expected.unwrap().discard_storage();
                continue;
            }
            match (expected, actual) {
                (Ok(expected), Ok(actual)) => {
                    assert_eq!(format!("{actual:?}"), format!("{expected:?}"), "{source}");
                    actual.discard_storage();
                    expected.discard_storage();
                }
                (Err(expected), Err(actual)) => {
                    assert_eq!(actual.kind(), expected.kind(), "{source}: {actual:?}")
                }
                (expected, actual) => panic!("{source}: expected={expected:?}, actual={actual:?}"),
            }
        }
    }

    #[test]
    fn physical_scalar_transfers_preserve_absence_and_self_moves() {
        let program = resolve_physical_program([]).unwrap();
        let session = CompilerSession::new();
        let mut interpreter = Interpreter {
            program: &program,
            memory: Memory::default(),
            limits: ReferenceInterpreterLimits::default(),
            fuel: None,
            depth: 0,
            session: &session,
            types: RuntimeTypes::default(),
            static_evidence: FxHashMap::default(),
        };
        let body = Function::new(
            "transfers".into(),
            CallResultConvention::Value,
            vec![],
            vec![],
            vec![],
        );
        let source = interpreter
            .memory
            .allocate(ScalarKind::Int.ty(), None)
            .unwrap();
        let destination = interpreter
            .memory
            .allocate(ScalarKind::Int.ty(), None)
            .unwrap();
        let mut registers = FxHashMap::from_iter([
            (ValueId::from_index(0), Binding::Place(source)),
            (ValueId::from_index(1), Binding::Place(destination)),
        ]);
        let source_operand = mir::Value::Register(ValueId::from_index(0));
        let destination_operand = mir::Value::Register(ValueId::from_index(1));
        let span = Location::new_synthesized();
        let self_move = Operation::move_value(span, source_operand.clone(), source_operand.clone());
        assert!(
            interpreter
                .operation(&body, &[], &mut registers, &self_move, 0)
                .is_err()
        );
        interpreter.memory.write(source, Scalar::Int(42)).unwrap();
        interpreter
            .operation(&body, &[], &mut registers, &self_move, 0)
            .unwrap();
        assert_eq!(interpreter.memory.read(source).unwrap(), Scalar::Int(42));

        let replace = Operation::replace(span, source_operand, destination_operand, None);
        for old in [None, Some(Scalar::Int(7))] {
            interpreter.memory.clear(destination).unwrap();
            if let Some(old) = old {
                interpreter.memory.write(destination, old).unwrap();
            }
            interpreter.memory.write(source, Scalar::Int(42)).unwrap();
            interpreter
                .operation(&body, &[], &mut registers, &replace, 0)
                .unwrap();
            assert_eq!(
                interpreter.memory.read(destination).unwrap(),
                Scalar::Int(42)
            );
            assert_eq!(
                interpreter.memory.initialized(source).unwrap(),
                old.is_some()
            );
            if let Some(old) = old {
                assert_eq!(interpreter.memory.read(source).unwrap(), old);
            }
        }
    }

    #[test]
    fn physical_capability_gate_checks_literal_patterns() {
        for (pattern, supported) in [
            (LiteralValue::new_native(1isize), true),
            (
                LiteralValue::new_tuple(vec![LiteralValue::new_native(1isize)]),
                true,
            ),
            (LiteralValue::new_variant_tag("Some".into()), true),
        ] {
            let operation = Operation::compare_eq(
                Location::new_synthesized(),
                mir::Value::Register(ValueId::from_index(0)),
                mir::Value::Pattern(Box::new(pattern)),
            );
            assert_eq!(Interpreter::check_operation(&operation).is_ok(), supported);
        }
    }
}
