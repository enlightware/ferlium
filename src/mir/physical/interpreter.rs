// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Checked physical-MIR execution. Boxed values exist only at the host boundary.
//! Function storage is prepared on dispatch; every executed access is checked.

use super::{
    DictionaryReference, EvidenceEnvironmentLayout,
    interpreter_memory::{
        Address, CallableReference, Generation, Memory, Scalar, ScalarKind, StoredValue,
    },
    program::{Descriptor, InternedStaticEvidence, ProgramEvidenceId, ResolvedPhysicalProgram},
    results::{ValueAdapter, decode_adapter},
    same_storage_type,
};
use crate::{
    CompilerSession, Location,
    compiler::error::SandboxViolationKind,
    eval::RuntimeError,
    execution::ReferenceInterpreterLimits,
    format::FormatWith,
    hir::{
        function::ArgConvention,
        native_functions::{
            NativeCallOutcome, NativeEntry, NativeFailureState, NativeParameter, NativeResult,
        },
        value::{LiteralValue, Value, VariantPayloadStorage},
    },
    mir::{
        self, BlockId, Function, Operation, OperationKind, ValueId, function::ParameterKind,
        interpreter::FunctionKey, profile::MirExecutionProfile, terminator::TerminatorKind,
    },
    module::{
        DictionaryEntryEvidence, FunctionId, ModuleEnv, SubscriptId, TraitDictionaryId, id::Id,
    },
    std::{
        string::StaticStr,
        value::{VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX},
    },
    types::{
        r#type::{CallResultConvention, Type, TypeKind},
        type_inference::substitution::InstSubst,
        type_like::TypeLike,
        type_mapper::SimpleInstantiationMapper,
        type_properties::concrete_type_is_trivial_copy,
    },
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{fmt::Display, mem, process::abort, ptr, rc::Rc, slice::from_ref};
use ustr::Ustr;

pub(super) fn unsupported(detail: impl Display) -> RuntimeError {
    RuntimeError::Backend(format!(
        "Physical MIR execution does not yet support {detail}"
    ))
}
pub(super) fn invalid(detail: &str) -> RuntimeError {
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
    Projected(Address, usize),
}

/// Runtime evidence carries ABI references or a payload-storage flag.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Evidence {
    Physical {
        reference: DictionaryReference,
        generation: Generation,
        ty: Type,
    },
    Storage(bool),
}

impl Evidence {
    pub(super) fn ty(&self) -> Type {
        match self {
            Self::Physical { ty, .. } => *ty,
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
    environment: Option<Address>,
}

/// Metadata checks the descriptor's environment; captured values themselves live in ABI memory.
#[derive(Clone)]
struct CallableEnvironment {
    evidence: Vec<Evidence>,
    hidden_count: usize,
    values: Address,
    value_dictionary: Option<Evidence>,
}

struct SuspendedFrame {
    function: FunctionId,
    args: Vec<Binding>,
    registers: FxHashMap<ValueId, Binding>,
    resume: BlockId,
    base: usize,
    types: RuntimeTypes,
}

enum FrameExit {
    Returned,
    Yielded(Address, BlockId),
}

/// Concrete type identities for checked storage, not specialized copies of MIR bodies.
#[derive(Default)]
struct RuntimeTypes(InstSubst);

impl RuntimeTypes {
    fn resolve(&self, ty: Type) -> Type {
        ty.map(&mut SimpleInstantiationMapper::new(&self.0))
    }

    fn bind(
        &mut self,
        pattern: Type,
        actual: Type,
        env: ModuleEnv<'_>,
    ) -> Result<(), RuntimeError> {
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
                    if let Some(&previous) = self.0.0.get(var) {
                        if !same_storage_type(previous, actual) {
                            pending.push((previous, actual));
                        }
                    } else {
                        self.0.0.insert(*var, actual);
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
                // Effects are erased, but argument access modes remain part of the contract.
                (Function(a), Function(b))
                    if a.args.len() == b.args.len()
                        && a.args
                            .iter()
                            .zip(&b.args)
                            .all(|(a, b)| a.mut_ty == b.mut_ty) =>
                {
                    a.args
                        .iter()
                        .zip(&b.args)
                        .map(|(a, b)| (a.ty, b.ty))
                        .chain([(a.ret, b.ret)])
                        .collect()
                }
                (Subscript(a), Subscript(b))
                    if a.args.len() == b.args.len()
                        && a.args
                            .iter()
                            .zip(&b.args)
                            .all(|(a, b)| a.mut_ty == b.mut_ty) =>
                {
                    // A subscript can expose fewer members or a widened result convention.
                    // Dispatch checks the selected entry's actual protocol.
                    a.args
                        .iter()
                        .zip(&b.args)
                        .map(|(a, b)| (a.ty, b.ty))
                        .chain([(a.ret, b.ret)])
                        .collect()
                }
                // A nominal value and its Repr share storage, but distinct nominal types do not
                // become interchangeable merely because their representations agree.
                (Named(named), other) if !matches!(other, Named(_)) => {
                    let named = named.clone();
                    drop(lhs);
                    drop(rhs);
                    vec![(named.instantiated_shape(&env), actual)]
                }
                (other, Named(named)) if !matches!(other, Named(_)) => {
                    let named = named.clone();
                    drop(lhs);
                    drop(rhs);
                    vec![(pattern, named.instantiated_shape(&env))]
                }
                _ => {
                    drop(lhs);
                    drop(rhs);
                    return Err(invalid(&format!(
                        "runtime type mismatch: {} versus {}",
                        pattern.format_with(&env),
                        actual.format_with(&env)
                    )));
                }
            };
            pending.extend(pairs);
        }
        Ok(())
    }

    /// Normalize stored evidence and bind types for ordinary and suspended call frames alike.
    fn for_call(
        body: &Function,
        args: &mut [Binding],
        memory: &Memory,
        env: ModuleEnv<'_>,
    ) -> Result<Self, RuntimeError> {
        if args.len() != body.parameters().len() {
            return Err(invalid("call arity mismatch"));
        }
        let mut types = Self::default();
        for (parameter, argument) in body.parameters().iter().zip(args) {
            if parameter.kind == ParameterKind::Dictionary {
                *argument = Binding::Evidence(argument.clone().evidence(memory)?);
            }
            if (parameter.kind == ParameterKind::Dictionary)
                != matches!(argument, Binding::Evidence(_))
            {
                return Err(invalid(&format!(
                    "call evidence role mismatch in {}: {:?}",
                    body.name, parameter.kind
                )));
            }
            // A diverging callee never initializes its caller-provided result storage.
            if parameter.kind != ParameterKind::Return || parameter.ty != Type::never() {
                let ty = match argument {
                    Binding::Evidence(evidence) => evidence.ty(),
                    _ => argument.place()?.ty,
                };
                types.bind(parameter.ty, ty, env)?;
            }
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

    fn evidence(self, memory: &Memory) -> Result<Evidence, RuntimeError> {
        match self {
            Self::Evidence(evidence) => Ok(evidence),
            Self::Scalar(Scalar::Bool(value)) => Ok(Evidence::Storage(value)),
            Self::Place(address) | Self::Projected(address, _) => match memory.read(address)? {
                Scalar::Bool(value) => Ok(Evidence::Storage(value)),
                _ => Err(invalid("expected storage evidence")),
            },
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
            Self::Place(address) | Self::Projected(address, _) => Ok(*address),
            _ => Err(invalid("expected a place")),
        }
    }
    fn scalar(self, memory: &Memory) -> Result<Scalar, RuntimeError> {
        match self {
            Self::Scalar(value) => Ok(value),
            Self::Evidence(Evidence::Storage(value)) => Ok(Scalar::Bool(value)),
            Self::Place(address) | Self::Projected(address, _) => memory.read(address),
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
    run_entry_with_profile(program, entry, arguments, limits, session, None)
}

pub(crate) fn run_entry_with_profile(
    program: &ResolvedPhysicalProgram,
    entry: FunctionId,
    arguments: &mut [Value],
    limits: ReferenceInterpreterLimits,
    session: &CompilerSession,
    profile: Option<&mut MirExecutionProfile>,
) -> Result<Value, RuntimeError> {
    let mut memory = Memory::default();
    memory.allocation_limit = limits.environment_cell_limit;
    memory.peak_allocations = profile.as_ref().map(|_| 0);
    let mut interpreter = Interpreter {
        program,
        memory,
        limits,
        fuel: limits.execution.fuel_limit,
        depth: 0,
        session,
        types: RuntimeTypes::default(),
        static_evidence: FxHashMap::default(),
        environments: FxHashMap::default(),
        prepared: FxHashSet::default(),
        prepared_monomorphic: FxHashSet::default(),
        projections: Vec::new(),
        profile,
    };
    interpreter.prepare_native_storage()?;
    let body = program
        .function(entry)
        .ok_or_else(|| unsupported("native host entry points"))?;
    interpreter.prepare_frame(entry, body, &RuntimeTypes::default())?;
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
    // A script signature may be valid internally but unsupported at the boxed host boundary.
    // Validate the entire boundary before transferring any arguments or executing guest code.
    for parameter in body.parameters() {
        interpreter.memory.validate_host_type(parameter.ty)?;
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
    if let Some(profile) = interpreter.profile {
        profile.record_cell_high_water(interpreter.memory.peak_allocations.unwrap());
    }
    result
}

struct Interpreter<'a, 'p> {
    profile: Option<&'a mut MirExecutionProfile>,
    program: &'a ResolvedPhysicalProgram<'p>,
    memory: Memory,
    limits: ReferenceInterpreterLimits,
    fuel: Option<usize>,
    depth: usize,
    session: &'a CompilerSession,
    types: RuntimeTypes,
    static_evidence: FxHashMap<ProgramEvidenceId, Evidence>,
    environments: FxHashMap<Address, Rc<CallableEnvironment>>,
    prepared: FxHashSet<(FunctionId, Vec<Type>)>,
    prepared_monomorphic: FxHashSet<FunctionId>,
    projections: Vec<Option<SuspendedFrame>>,
}

impl<'a, 'p> Interpreter<'a, 'p> {
    fn prepare_frame(
        &mut self,
        id: FunctionId,
        body: &Function,
        types: &RuntimeTypes,
    ) -> Result<(), RuntimeError> {
        if self.prepared_monomorphic.contains(&id) {
            return Ok(());
        }
        let key = (
            id,
            body.parameters()
                .iter()
                .map(|p| types.resolve(p.ty))
                .collect(),
        );
        if self.prepared.contains(&key) {
            return Ok(());
        }
        if self.prepared.len() >= 4096 {
            return Err(unsupported("generic preparation limit"));
        }
        let env = self.env(id);
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
        let mut evidence = FxHashSet::default();
        for block in body.blocks() {
            let block = body.block(block);
            if !matches!(block.terminator().kind, TerminatorKind::Invoke { .. }) {
                evidence.extend(
                    block
                        .terminator()
                        .operands()
                        .iter()
                        .filter_map(|v| self.program.evidence_id(v)),
                );
            }
            for operation in block
                .operations()
                .iter()
                .chain(match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => Some(operation),
                    _ => None,
                })
            {
                Self::check_operation(operation)?;
                match &operation.kind {
                    OperationKind::Alloca { ty }
                    | OperationKind::AddressOffset { ty, .. }
                    | OperationKind::Clone { ty }
                    | OperationKind::Drop { ty }
                    | OperationKind::DropInitialized { ty }
                    | OperationKind::MoveBytes { ty }
                    | OperationKind::BuildClosure { ty, .. }
                    | OperationKind::BuildSubscript { ty }
                    | OperationKind::CloneSubscriptEnv { ty }
                    | OperationKind::CloneClosureEnv { ty } => {
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
                    _ => (),
                }
                evidence.extend(
                    operation
                        .operands
                        .iter()
                        .filter_map(|v| self.program.evidence_id(v)),
                );
            }
        }
        self.prepare_static_evidence(evidence)?;
        self.memory
            .bind_tags(|tag| self.session.variant_tag_id(tag));
        if body.parameters().iter().all(|p| p.ty.is_constant()) {
            self.prepared_monomorphic.insert(id);
        }
        self.prepared.insert(key);
        Ok(())
    }

    fn build_subscript_evidence(
        &mut self,
        definition: SubscriptId,
        captures: Vec<Evidence>,
        ty: Option<Type>,
        is_static: bool,
        span: Option<Location>,
    ) -> Result<Evidence, RuntimeError> {
        let module = self.session.expect_fresh_module(definition.module);
        let scheme = module
            .get_subscript_by_id(definition.subscript)
            .and_then(|s| s.type_scheme(module))
            .ok_or_else(|| invalid("missing subscript signature"))?;
        let env = ModuleEnv::new(module, self.session.raw_modules());
        let extra = scheme.extra_parameters(env);
        let mut types = RuntimeTypes::default();
        let capture_types = extra
            .requirements
            .iter()
            .map(|r| r.to_dict_type_in_env(&env))
            .collect::<Vec<_>>();
        if !captures.is_empty() && capture_types.len() != captures.len() {
            return Err(invalid("subscript capture count mismatch"));
        }
        for (pattern, actual) in capture_types.iter().zip(&captures) {
            types.bind(*pattern, actual.ty(), env)?;
        }
        let ty = ty.unwrap_or_else(|| types.resolve(Type::subscript_type(scheme.ty)));
        let layout = EvidenceEnvironmentLayout::new(
            captures.iter().map(|e| matches!(e, Evidence::Storage(_))),
        )
        .map_err(|_| invalid("subscript evidence layout overflow"))?;
        let descriptor = self
            .program
            .reference_index(Descriptor::Subscript(definition))
            .ok_or_else(|| invalid("missing subscript descriptor"))?;
        self.memory
            .allocate_evidence(descriptor, ty, &layout, &captures, is_static, span)
    }

    fn resolve_callable(&self, binding: Binding) -> Result<Callable, RuntimeError> {
        match binding {
            Binding::Callable(callable) => Ok(callable),
            Binding::Place(address) => {
                let reference = self.memory.read_callable(address)?;
                let Some(Descriptor::Function(function)) =
                    self.program.reference_descriptor(reference.descriptor)
                else {
                    return Err(invalid("expected function descriptor"));
                };
                let captures = match reference.environment {
                    Some(environment) => {
                        let env = self
                            .environments
                            .get(&environment)
                            .ok_or_else(|| invalid("stale callable environment"))?;
                        env.evidence[..env.hidden_count].to_vec()
                    }
                    None => vec![],
                };
                Ok(Callable {
                    function,
                    captures,
                    environment: reference.environment,
                })
            }
            _ => Err(invalid("expected callable")),
        }
    }

    fn own_callable(
        &mut self,
        descriptor: Descriptor,
        hidden: Vec<Evidence>,
        dictionary: Option<Evidence>,
        captures: &[Address],
        ty: Type,
        span: Location,
    ) -> Result<StoredValue, RuntimeError> {
        let descriptor = self
            .program
            .reference_index(descriptor)
            .ok_or_else(|| invalid("missing callable descriptor"))?;
        let mut evidence = hidden.clone();
        evidence.extend(dictionary.iter().cloned());
        let environment = if evidence.is_empty() && captures.is_empty() {
            None
        } else {
            let layout_ty = dictionary
                .as_ref()
                .map(Evidence::layout_type)
                .transpose()?
                .unwrap_or(Type::unit());
            // Layout evidence may erase callable type variables. Keep the actual capture types
            // for checked accesses, while requiring the descriptor's physical representation.
            let values_ty = Type::tuple(
                captures
                    .iter()
                    .map(|capture| capture.ty)
                    .collect::<Vec<_>>(),
            );
            self.memory
                .prepare_type(values_ty, &self.session.module_env())?;
            self.memory
                .prepare_type(layout_ty, &self.session.module_env())?;
            if !self.memory.compatible_types(values_ty, layout_ty)? {
                return Err(invalid("callable captures disagree with layout evidence"));
            }
            let (environment, values) = self
                .memory
                .allocate_callable_environment(&evidence, values_ty, span)?;
            if captures.is_empty() {
                self.memory.write(values, Scalar::Unit)?;
            }
            for (index, &capture) in captures.iter().enumerate() {
                assert!(
                    self.memory.fully_initialized(capture)?,
                    "physical lowering error at {span:?}: closure capture must be complete"
                );
                self.memory.check_consume(capture)?;
                let value = self.memory.read_value(capture, false)?;
                self.memory
                    .write_value(self.memory.member(values, index)?, &value)?;
                self.memory.clear(capture)?;
            }
            self.environments.insert(
                environment,
                Rc::new(CallableEnvironment {
                    evidence,
                    hidden_count: hidden.len(),
                    values,
                    value_dictionary: dictionary,
                }),
            );
            Some(environment)
        };
        Ok(Memory::callable_value(
            ty,
            CallableReference {
                descriptor,
                environment,
            },
        ))
    }

    fn store_callable(
        &mut self,
        destination: Address,
        callable: Callable,
        span: Location,
    ) -> Result<(), RuntimeError> {
        if callable.environment.is_some() {
            return Err(invalid("borrowed callable cannot become owned storage"));
        }
        let value = self.own_callable(
            Descriptor::Function(callable.function),
            callable.captures,
            None,
            &[],
            destination.ty,
            span,
        )?;
        self.memory.write_value(destination, &value)
    }

    fn drop_capture_tuple(
        &mut self,
        dictionary: Evidence,
        values: Address,
        span: Location,
    ) -> Result<(), RuntimeError> {
        let callable = self.dictionary_entry(dictionary, VALUE_DROP_METHOD_INDEX.as_index())?;
        let marker = self.memory.len();
        let output = self.memory.allocate(Type::unit(), Some(span))?;
        let result = self.invoke(
            callable,
            vec![Binding::Place(values), Binding::Place(output)],
        );
        self.memory.restore(marker);
        result
    }

    fn clone_callable(
        &mut self,
        source: Address,
        ty: Type,
        span: Location,
    ) -> Result<StoredValue, RuntimeError> {
        let reference = self.memory.read_callable(source)?;
        let Some(environment) = reference.environment else {
            return Ok(Memory::callable_value(ty, reference));
        };
        let env = self
            .environments
            .get(&environment)
            .cloned()
            .ok_or_else(|| invalid("stale callable environment"))?;
        let (fresh, values) =
            self.memory
                .allocate_callable_environment(&env.evidence, env.values.ty, span)?;
        self.environments.insert(
            fresh,
            Rc::new(CallableEnvironment {
                values,
                ..(*env).clone()
            }),
        );
        let result = if let Some(dictionary) = env.value_dictionary.clone() {
            let callable =
                self.dictionary_entry(dictionary, VALUE_CLONE_METHOD_INDEX.as_index())?;
            self.invoke(
                callable,
                vec![Binding::Place(env.values), Binding::Place(values)],
            )
        } else {
            self.memory.write(values, Scalar::Unit)
        };
        if let Err(error) = result {
            if matches!(error, RuntimeError::SourceFailure(_)) {
                // A failed clone cleans its partially constructed result; release only the
                // environment allocation and its retained evidence, not the source captures.
                self.release_callable_environment(fresh)?;
            }
            return Err(error);
        }
        Ok(Memory::callable_value(
            ty,
            CallableReference {
                environment: Some(fresh),
                ..reference
            },
        ))
    }

    fn drop_callable(&mut self, address: Address, span: Location) -> Result<(), RuntimeError> {
        let reference = self.memory.read_callable(address)?;
        // Detach before running guest drop: a failing destructor must not leave a live callable
        // pointing at partially destroyed captures.
        self.memory.check_consume(address)?;
        self.memory.clear(address)?;
        if let Some(environment) = reference.environment {
            let env = self
                .environments
                .get(&environment)
                .cloned()
                .ok_or_else(|| invalid("stale callable environment"))?;
            let result = if let Some(dictionary) = env.value_dictionary.clone() {
                self.drop_capture_tuple(dictionary, env.values, span)
            } else {
                Ok(())
            };
            // Do not attempt further reclamation after poisoning or an internal backend error.
            if result
                .as_ref()
                .is_err_and(|e| !matches!(e, RuntimeError::SourceFailure(_)))
            {
                return result;
            }
            let cleanup = self.release_callable_environment(environment);
            return match (result, cleanup) {
                (Ok(()), result) | (result, Ok(())) => result,
                (Err(initial), Err(cleanup)) => Err(initial.interrupted_by(cleanup)),
            };
        }
        Ok(())
    }

    fn release_callable_environment(&mut self, environment: Address) -> Result<(), RuntimeError> {
        self.memory.deallocate(environment)?;
        let env = self
            .environments
            .remove(&environment)
            .ok_or_else(|| invalid("stale callable environment"))?;
        for evidence in &env.evidence {
            self.memory.release_evidence(evidence)?;
        }
        Ok(())
    }

    fn project_call(
        &mut self,
        callable: Callable,
        args: Vec<Binding>,
        yielded: Type,
        span: Location,
    ) -> Result<Binding, RuntimeError> {
        let base = self.memory.len();
        let output = self.memory.allocate_place(yielded, Some(span))?;
        let mut args = callable
            .captures
            .into_iter()
            .map(Binding::Evidence)
            .chain(args)
            .collect::<Vec<_>>();
        args.push(Binding::Place(output));
        let Some(body) = self.program.function(callable.function) else {
            let result = self
                .call_native(callable.function, &args)
                .and_then(|()| self.memory.read_pointer(output));
            self.memory.restore(base);
            return result.map(Binding::Place);
        };
        if body.result_convention() == CallResultConvention::ADDRESSOR_PLACE {
            let result = self
                .call(callable.function, args)
                .and_then(|()| self.memory.read_pointer(output));
            self.memory.restore(base);
            return result.map(Binding::Place);
        }
        if body.result_convention() != CallResultConvention::YIELDED_ONCE {
            return Err(invalid("project requires a place-returning entry"));
        }
        let types =
            RuntimeTypes::for_call(body, &mut args, &self.memory, self.env(callable.function))?;
        self.prepare_frame(callable.function, body, &types)?;
        let previous = mem::replace(&mut self.types, types);
        self.depth += 1;
        let mut registers = FxHashMap::default();
        let outcome = self.run_blocks(
            callable.function,
            body,
            &args,
            &mut registers,
            base,
            body.entry(),
        );
        let types = mem::replace(&mut self.types, previous);
        match outcome {
            Ok(FrameExit::Yielded(address, resume)) => {
                let index = self
                    .projections
                    .iter()
                    .position(Option::is_none)
                    .unwrap_or(self.projections.len());
                let frame = Some(SuspendedFrame {
                    function: callable.function,
                    args,
                    registers,
                    resume,
                    base,
                    types,
                });
                if index == self.projections.len() {
                    self.projections.push(frame);
                } else {
                    self.projections[index] = frame;
                }
                Ok(Binding::Projected(address, index))
            }
            outcome => {
                self.depth -= 1;
                for binding in registers.values() {
                    self.release_binding(binding)?;
                }
                self.memory.restore(base);
                outcome.and_then(|_| Err(invalid("scoped accessor returned without yielding")))
            }
        }
    }

    fn end_project(&mut self, index: usize) -> Result<(), RuntimeError> {
        let mut frame = self
            .projections
            .get_mut(index)
            .and_then(Option::take)
            .ok_or_else(|| invalid("projection already ended"))?;
        let body = self
            .program
            .function(frame.function)
            .ok_or_else(|| invalid("missing suspended entry"))?;
        let previous = mem::replace(&mut self.types, frame.types);
        let outcome = self.run_blocks(
            frame.function,
            body,
            &frame.args,
            &mut frame.registers,
            frame.base,
            frame.resume,
        );
        self.types = previous;
        self.depth -= 1;
        for binding in frame.registers.values() {
            self.release_binding(binding)?;
        }
        self.memory.restore(frame.base);
        match outcome? {
            FrameExit::Returned => Ok(()),
            FrameExit::Yielded(..) => Err(invalid("scoped accessor yielded twice")),
        }
    }

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
        let env = ModuleEnv::new(
            self.session.expect_fresh_module(definition.module_id),
            self.session.raw_modules(),
        );
        for (ty, capture) in metadata.capture_types().iter().zip(&captures) {
            types.bind(*ty, capture.ty(), env)?;
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
            if self.static_evidence.contains_key(&id) {
                continue;
            }
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
                InternedStaticEvidence::Subscript {
                    definition,
                    captures,
                } => {
                    let captures = captures
                        .iter()
                        .map(|id| self.static_evidence[id].clone())
                        .collect();
                    self.build_subscript_evidence(*definition, captures, None, true, None)?
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

    fn dictionary_entry(&self, evidence: Evidence, index: usize) -> Result<Callable, RuntimeError> {
        let Evidence::Physical { reference, .. } = &evidence else {
            return Err(invalid("expected a dictionary"));
        };
        let captures = self.memory.evidence_captures(&evidence)?;
        let entry = self
            .program
            .descriptor(reference.descriptor)
            .ok_or_else(|| invalid("unresolved dictionary"))?
            .entries()
            .get(index)
            .ok_or_else(|| invalid("missing dictionary entry"))?;
        Ok(Callable {
            function: entry.function(),
            environment: None,
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
            | BuildArray { .. }
            | BuildClosure { .. }
            | CloneClosureEnv { .. }
            | DropClosureEnv
            | BuildSubscriptEvidence { .. }
            | BuildSubscript { .. }
            | CloneSubscriptEnv { .. }
            | DropSubscriptEnv
            | BorrowSubscriptMember { .. }
            | Project { .. }
            | EndProject
            | Clone { .. }
            | Drop { .. }
            | DropInitialized { .. }
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
        if matches!(pattern, LiteralValue::VariantTag(_))
            || pattern.as_primitive_ty::<StaticStr>().is_some()
        {
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

    fn call(&mut self, id: FunctionId, mut args: Vec<Binding>) -> Result<(), RuntimeError> {
        let symbol = id;
        let id = self.program.direct_entry(id);
        // The readiness verifier checks the exact forwarding body. Execute that fixed ABI
        // boundary here so generic callbacks do not double the Rust stack needed for recursion.
        let output = if id != symbol {
            let output = args
                .pop()
                .ok_or_else(|| invalid("zero-sized adapter result missing"))?
                .place()?;
            let adapter = self
                .program
                .function(symbol)
                .and_then(decode_adapter)
                .ok_or_else(|| invalid("malformed value adapter"))?;
            if output.ty != adapter.result.ty {
                return Err(invalid("zero-sized adapter result type mismatch"));
            }
            Some(output)
        } else {
            None
        };
        let Some(body) = self.program.function(id) else {
            return self.call_native(id, &args);
        };
        let types = RuntimeTypes::for_call(body, &mut args, &self.memory, self.env(id))?;
        self.prepare_frame(id, body, &types)?;
        for (argument, parameter) in args.iter().zip(body.parameters()) {
            if parameter.kind == ParameterKind::Dictionary {
                continue;
            }
            // for_call checks runtime type identities; callable effect annotations are erased.
            let pointer_result = parameter.kind == ParameterKind::Return
                && body.result_convention() == CallResultConvention::ADDRESSOR_PLACE;
            if self.memory.is_pointer_slot(argument.place()?)? != pointer_result {
                return Err(invalid("call argument storage role mismatch"));
            }
            if parameter.kind == ParameterKind::Owned {
                assert!(
                    self.memory.fully_initialized(argument.place()?)?,
                    "physical lowering error in {id:?}: owned argument must be complete"
                );
            }
        }
        // Explicit CheckCallDepth operations preserve the boxed executor's source-level policy.
        let marker = self.memory.len();
        let previous_types = mem::replace(&mut self.types, types);
        self.depth += 1;
        let result = self.run_frame(id, body, &args, marker);
        self.depth -= 1;
        self.types = previous_types;
        // A callee owns partial result construction, including cleanup before a source failure.
        // Poisoning abandons that contract along with guest cleanup.
        if let Some((argument, _)) = args
            .iter()
            .zip(body.parameters())
            .find(|(_, parameter)| parameter.kind == ParameterKind::Return)
        {
            let address = argument.place()?;
            match &result {
                Ok(()) => assert!(
                    self.memory.fully_initialized(address)?,
                    "physical lowering error in {id:?}: returned an incomplete result"
                ),
                Err(RuntimeError::SourceFailure(_)) => assert!(
                    !self.memory.any_initialized(address)?,
                    "physical lowering error in {id:?}: source failure left a live result"
                ),
                _ => (),
            }
        }
        self.memory.restore(marker);
        if let Some(output) = output {
            let adapter = self
                .program
                .function(symbol)
                .and_then(decode_adapter)
                .ok_or_else(|| invalid("malformed value adapter"))?;
            self.profile_value_adapter(symbol, &adapter, &result);
            result.and_then(|()| {
                // Materializing the adapter's typed result constant transfers
                // the logical result, including product-field liveness, without a source clone.
                let constant = adapter.result;
                let value = self.memory.literal(constant.ty, &constant.representation)?;
                self.memory.write_value(output, &value)
            })
        } else {
            result
        }
    }

    fn profile_value_adapter(
        &mut self,
        id: FunctionId,
        adapter: &ValueAdapter<'_>,
        outcome: &Result<(), RuntimeError>,
    ) {
        let Some(profile) = &mut self.profile else {
            return;
        };
        let key = FunctionKey {
            module: id.module,
            identity: id.function,
        };
        if let Some(invoke) = adapter.invoke {
            profile.record_terminator(key, &invoke.kind);
        }
        profile.record_operation(key, adapter.call);
        if outcome.is_ok() {
            profile.record_operation(key, adapter.store);
            profile.record_terminator(key, &adapter.returned.kind);
        } else if matches!(outcome, Err(RuntimeError::SourceFailure(_)))
            && let Some(failure) = adapter.failure
        {
            profile.record_terminator(key, &failure.kind);
        }
    }

    fn invoke(&mut self, callable: Callable, args: Vec<Binding>) -> Result<(), RuntimeError> {
        if let Some(environment) = callable.environment {
            let env = self
                .environments
                .get(&environment)
                .cloned()
                .ok_or_else(|| invalid("stale callable environment"))?;
            if let Some(dictionary) = env.value_dictionary.clone() {
                let span = Location::new_synthesized();
                let marker = self.memory.len();
                let temporary = self.memory.allocate(env.values.ty, Some(span))?;
                let clone =
                    self.dictionary_entry(dictionary.clone(), VALUE_CLONE_METHOD_INDEX.as_index())?;
                let cloned = self.invoke(
                    clone,
                    vec![Binding::Place(env.values), Binding::Place(temporary)],
                );
                if let Err(error) = cloned {
                    self.memory.restore(marker);
                    return Err(error);
                }
                let count = env
                    .values
                    .ty
                    .data()
                    .as_tuple()
                    .ok_or_else(|| invalid("closure capture tuple expected"))?
                    .len();
                let values = (0..count)
                    .map(|i| self.memory.member(temporary, i).map(Binding::Place))
                    .collect::<Result<Vec<_>, _>>()?;
                let leading = callable
                    .captures
                    .into_iter()
                    .map(Binding::Evidence)
                    .chain(values)
                    .chain(args)
                    .collect();
                let result = self.call(callable.function, leading);
                let cleanup = if result
                    .as_ref()
                    .is_err_and(|e| !matches!(e, RuntimeError::SourceFailure(_)))
                {
                    Ok(())
                } else {
                    self.drop_capture_tuple(dictionary, temporary, span)
                };
                self.memory.restore(marker);
                return match (result, cleanup) {
                    (Ok(()), result) | (result, Ok(())) => result,
                    (Err(initial), Err(cleanup)) => Err(initial.interrupted_by(cleanup)),
                };
            }
        }
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
            mir::Value::Dictionary(_) | mir::Value::Evidence(_) | mir::Value::Subscript(_) => {
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
                environment: None,
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
        id: FunctionId,
        body: &Function,
        args: &[Binding],
        frame_base: usize,
    ) -> Result<(), RuntimeError> {
        let mut registers = FxHashMap::default();
        let result = self.run_blocks(id, body, args, &mut registers, frame_base, body.entry());
        // Evidence registers own references independently of stack storage. In particular, CSE
        // may reuse a pure dictionary construction across StackRestore boundaries.
        for binding in registers.values() {
            self.release_binding(binding)?;
        }
        match result? {
            FrameExit::Returned => Ok(()),
            FrameExit::Yielded(..) => Err(invalid("ordinary call yielded a place")),
        }
    }

    fn run_blocks(
        &mut self,
        id: FunctionId,
        body: &Function,
        args: &[Binding],
        registers: &mut FxHashMap<ValueId, Binding>,
        frame_base: usize,
        mut block: BlockId,
    ) -> Result<FrameExit, RuntimeError> {
        let mut pending: Option<RuntimeError> = None;
        let mut secondary: Option<RuntimeError> = None;
        let key = FunctionKey {
            module: id.module,
            identity: id.function,
        };
        loop {
            let current = body.block(block);
            for operation in current.operations() {
                if let Some(profile) = &mut self.profile {
                    profile.record_operation(key, operation);
                }
                self.operation(body, args, registers, operation, frame_base)
                    .map_err(|error| {
                        assert!(
                            !matches!(error, RuntimeError::SourceFailure(_)),
                            "a plain MIR operation raised a source failure"
                        );
                        match pending.take() {
                            Some(initial) => initial.interrupted_by(error),
                            None => error,
                        }
                    })?;
            }
            if let Some(profile) = &mut self.profile {
                profile.record_terminator(key, &current.terminator().kind);
                if let TerminatorKind::Invoke { operation, .. } = &current.terminator().kind {
                    profile.record_operation(key, operation);
                }
            }
            match &current.terminator().kind {
                TerminatorKind::Goto { target } => block = *target,
                TerminatorKind::CondBr {
                    condition,
                    then_target,
                    else_target,
                } => {
                    let Scalar::Bool(taken) = self
                        .operand(body, args, registers, condition)?
                        .scalar(&self.memory)?
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
                    return Ok(FrameExit::Returned);
                }
                TerminatorKind::Yield { place, resume } => {
                    if pending.is_some() {
                        return Err(invalid("yield during failure cleanup"));
                    }
                    return Ok(FrameExit::Yielded(
                        self.operand(body, args, registers, place)?.place()?,
                        *resume,
                    ));
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
        let result = match &operation.kind {
            Call { ty, .. } => {
                let mut callable = self.resolve_callable(self.operand(
                    body,
                    args,
                    registers,
                    &operation.operands[0],
                )?)?;
                let id = callable.function;
                if ty.result_convention == CallResultConvention::NoValue {
                    callable.function = self.program.direct_entry(callable.function);
                }
                let values = operation.operands[1..]
                    .iter()
                    .map(|value| self.operand(body, args, registers, value))
                    .collect::<Result<Vec<_>, _>>()?;
                self.invoke(callable, values)
                    .map_err(|error| error.with_frame(id, operation.span))?;
                None
            }
            DropInitialized { ty } => {
                self.drop_operation(body, args, registers, operation, *ty)?;
                None
            }
            Clone { .. }
            | Project { .. }
            | EndProject
            | CloneClosureEnv { .. }
            | CloneSubscriptEnv { .. }
            | DropClosureEnv
            | DropSubscriptEnv => self.lifecycle_operation(body, args, registers, operation)?,
            _ => {
                // Layout getters execute guest code. Resolve them before entering the larger
                // storage-operation frame, which must not remain live across those calls.
                let layout = self.storage_witness_layout(body, args, registers, operation)?;
                self.storage_operation(body, args, registers, operation, frame_base, layout)?
            }
        };
        if let Some(value) = result {
            // Construction transfers its initial owner; other results retain borrowed evidence.
            if !matches!(
                operation.kind,
                BuildDictionary { .. } | BuildSubscriptEvidence { .. }
            ) {
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

    // Keep storage-operation temporaries off the Rust stack across recursive guest calls.
    fn lifecycle_operation(
        &mut self,
        body: &Function,
        args: &[Binding],
        registers: &FxHashMap<ValueId, Binding>,
        operation: &Operation,
    ) -> Result<Option<Binding>, RuntimeError> {
        use OperationKind::*;
        let operand =
            |index: usize| self.operand(body, args, registers, &operation.operands[index]);
        let place = |index| operand(index)?.place();
        if let Clone { ty } = &operation.kind {
            if !same_storage_type(place(0)?.ty, self.types.resolve(*ty)) {
                return Err(invalid("operation type differs from storage type"));
            }
        }
        Ok(match &operation.kind {
            Project { yielded, .. } => {
                let callable = self.resolve_callable(operand(0)?)?;
                let arguments = (1..operation.operands.len())
                    .map(operand)
                    .collect::<Result<Vec<_>, _>>()?;
                Some(self.project_call(
                    callable,
                    arguments,
                    self.types.resolve(*yielded),
                    operation.span,
                )?)
            }
            EndProject => {
                if let Binding::Projected(_, index) = operand(0)? {
                    self.end_project(index)?;
                }
                None
            }
            CloneClosureEnv { ty } | CloneSubscriptEnv { ty } => {
                let source = place(0)?;
                Some(Binding::Aggregate(Rc::new(self.clone_callable(
                    source,
                    self.types.resolve(*ty),
                    operation.span,
                )?)))
            }
            DropClosureEnv | DropSubscriptEnv => {
                self.drop_callable(place(0)?, operation.span)?;
                None
            }
            Clone { .. } => {
                let callable = self.resolve_callable(operand(2)?)?;
                let id = callable.function;
                let values = (3..operation.operands.len())
                    .chain(0..2)
                    .map(operand)
                    .collect::<Result<_, _>>()?;
                self.invoke(callable, values)
                    .map_err(|error| error.with_frame(id, operation.span))?;
                None
            }
            _ => unreachable!("lifecycle operation dispatch"),
        })
    }

    // Recursive destruction must not retain the other lifecycle arms' temporaries on the stack.
    fn drop_operation(
        &mut self,
        body: &Function,
        args: &[Binding],
        registers: &FxHashMap<ValueId, Binding>,
        operation: &Operation,
        ty: Type,
    ) -> Result<(), RuntimeError> {
        let operand =
            |index: usize| self.operand(body, args, registers, &operation.operands[index]);
        let address = operand(0)?.place()?;
        if !same_storage_type(address.ty, self.types.resolve(ty)) {
            return Err(invalid("operation type differs from storage type"));
        }
        assert!(
            self.memory.fully_initialized(address)?,
            "physical lowering error: drop_initialized requires fully initialized storage"
        );
        let callable = self.resolve_callable(operand(1)?)?;
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
        self.memory.clear(address)
    }

    fn storage_witness_layout(
        &mut self,
        body: &Function,
        args: &[Binding],
        registers: &FxHashMap<ValueId, Binding>,
        operation: &Operation,
    ) -> Result<Option<[usize; 2]>, RuntimeError> {
        use OperationKind::*;
        let operand =
            |index: usize| self.operand(body, args, registers, &operation.operands[index]);
        let place = |index| operand(index)?.place();
        let witness = match &operation.kind {
            Alloca { ty } if !operation.operands.is_empty() => Some((0, self.types.resolve(*ty))),
            Move if operation.operands.len() == 3 => Some((
                2,
                match operand(0)? {
                    Binding::Callable(_) => place(1)?.ty,
                    source => source.place()?.ty,
                },
            )),
            Replace if operation.operands.len() == 3 => Some((2, place(0)?.ty)),
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
        if let Some((index, ty)) = witness {
            let evidence = operand(index)?.evidence(&self.memory)?;
            if !same_storage_type(evidence.layout_type()?, ty) {
                return Err(invalid("layout evidence differs from storage type"));
            }
            let layout = self.witness_layout(evidence, operation.span)?;
            if matches!(operation.kind, Variant { .. }) {
                self.memory.check_type_layout(ty, layout[0], layout[1])?;
            }
            Ok(Some(layout))
        } else {
            Ok(None)
        }
    }

    fn storage_operation(
        &mut self,
        body: &Function,
        args: &[Binding],
        registers: &mut FxHashMap<ValueId, Binding>,
        operation: &Operation,
        frame_base: usize,
        witnessed_layout: Option<[usize; 2]>,
    ) -> Result<Option<Binding>, RuntimeError> {
        use OperationKind::*;
        let operand =
            |index: usize| self.operand(body, args, registers, &operation.operands[index]);
        let place = |index| operand(index)?.place();
        // A symbolic callable has no source allocation; its destination carries the storage
        // layout against which transfer witnesses and byte counts must still be checked.
        let transfer_storage = match &operation.kind {
            Memcpy | Move | MoveBytes { .. } => Some(match operand(0)? {
                Binding::Callable(_) => place(1)?,
                source => source.place()?,
            }),
            _ => None,
        };
        if let MoveBytes { ty } = &operation.kind {
            if !same_storage_type(transfer_storage.unwrap().ty, self.types.resolve(*ty)) {
                return Err(invalid("operation type differs from storage type"));
            }
        }
        let result = match &operation.kind {
            BuildClosure {
                function,
                num_hidden_dicts,
                has_env_dict,
                ty,
            } => {
                let hidden = (0..*num_hidden_dicts as usize)
                    .map(|i| operand(i)?.evidence(&self.memory))
                    .collect::<Result<Vec<_>, _>>()?;
                let end = operation.operands.len() - usize::from(*has_env_dict);
                let captures = (*num_hidden_dicts as usize..end)
                    .map(place)
                    .collect::<Result<Vec<_>, _>>()?;
                let dictionary = if *has_env_dict {
                    Some(operand(end)?.evidence(&self.memory)?)
                } else {
                    None
                };
                let value = self.own_callable(
                    Descriptor::Function(*function),
                    hidden,
                    dictionary,
                    &captures,
                    self.types.resolve(*ty),
                    operation.span,
                )?;
                Some(Binding::Aggregate(Rc::new(value)))
            }
            BuildSubscriptEvidence { ty } => {
                let evidence = operand(0)?.evidence(&self.memory)?;
                let Evidence::Physical { reference, .. } = evidence else {
                    return Err(invalid("expected subscript evidence"));
                };
                let Some(Descriptor::Subscript(definition)) =
                    self.program.reference_descriptor(reference.descriptor)
                else {
                    return Err(invalid("expected subscript descriptor"));
                };
                let mut captures = self.memory.evidence_captures(&evidence)?;
                captures.extend(
                    (1..operation.operands.len())
                        .map(|i| operand(i)?.evidence(&self.memory))
                        .collect::<Result<Vec<_>, _>>()?,
                );
                Some(Binding::Evidence(self.build_subscript_evidence(
                    definition,
                    captures,
                    Some(self.types.resolve(*ty)),
                    false,
                    Some(operation.span),
                )?))
            }
            BuildSubscript { ty } => {
                let evidence = operand(0)?.evidence(&self.memory)?;
                let Evidence::Physical { reference, .. } = evidence else {
                    return Err(invalid("expected subscript evidence"));
                };
                let descriptor = self
                    .program
                    .reference_descriptor(reference.descriptor)
                    .ok_or_else(|| invalid("missing subscript descriptor"))?;
                let hidden = self.memory.evidence_captures(&evidence)?;
                let value = self.own_callable(
                    descriptor,
                    hidden,
                    None,
                    &[],
                    self.types.resolve(*ty),
                    operation.span,
                )?;
                Some(Binding::Aggregate(Rc::new(value)))
            }
            BorrowSubscriptMember { mut_member, .. } => {
                let (descriptor, captures, environment) = match operand(0)? {
                    Binding::Evidence(evidence @ Evidence::Physical { reference, .. }) => (
                        reference.descriptor,
                        self.memory.evidence_captures(&evidence)?,
                        None,
                    ),
                    Binding::Place(address) => {
                        let reference = self.memory.read_callable(address)?;
                        let captures = reference
                            .environment
                            .map(|a| {
                                self.environments
                                    .get(&a)
                                    .map(|e| e.evidence[..e.hidden_count].to_vec())
                                    .ok_or_else(|| invalid("stale subscript environment"))
                            })
                            .transpose()?
                            .unwrap_or_default();
                        (reference.descriptor, captures, reference.environment)
                    }
                    _ => return Err(invalid("expected subscript")),
                };
                let Some(Descriptor::Subscript(definition)) =
                    self.program.reference_descriptor(descriptor)
                else {
                    return Err(invalid("expected subscript descriptor"));
                };
                let member = self
                    .program
                    .subscript_member(definition, *mut_member)
                    .ok_or_else(|| invalid("missing subscript member"))?;
                Some(Binding::Callable(Callable {
                    function: member.function(),
                    captures,
                    environment,
                }))
            }
            BuildArray { element_ty } => {
                let element = self.types.resolve(*element_ty);
                let values = (0..operation.operands.len() - 1)
                    .map(|i| match operand(i)? {
                        Binding::Scalar(value) => Ok(Memory::scalar_value(value)),
                        Binding::Aggregate(value) => Ok((*value).clone()),
                        Binding::Place(address) => self.memory.read_value(address, false),
                        _ => Err(invalid("invalid array element")),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let destination = place(operation.operands.len() - 1)?;
                self.memory
                    .build_array(destination, element, &values, operation.span)?;
                None
            }
            BuildDictionary { definition, .. } => {
                let captures = (0..operation.operands.len())
                    .map(|i| operand(i)?.evidence(&self.memory))
                    .collect::<Result<_, _>>()?;
                let evidence =
                    self.build_evidence(*definition, captures, false, Some(operation.span))?;
                Some(Binding::Evidence(evidence))
            }
            DictEntry { entry_index, .. } => Some(Binding::Callable(
                self.dictionary_entry(operand(0)?.evidence(&self.memory)?, entry_index.as_index())?,
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
                let (Scalar::Int(size), Scalar::Int(align)) = (
                    operand(0)?.scalar(&self.memory)?,
                    operand(1)?.scalar(&self.memory)?,
                ) else {
                    return Err(invalid("non-integer allocation layout"));
                };
                let size =
                    usize::try_from(size).map_err(|_| invalid("negative allocation size"))?;
                let align =
                    usize::try_from(align).map_err(|_| invalid("negative allocation alignment"))?;
                let pointee = self.types.resolve(*pointee);
                if operation.operands.len() == 3 {
                    let Scalar::Int(count) = operand(2)?.scalar(&self.memory)? else {
                        return Err(invalid("non-integer element count"));
                    };
                    let count =
                        usize::try_from(count).map_err(|_| invalid("negative element count"))?;
                    Some(Binding::Place(self.memory.allocate_sequence(
                        pointee,
                        size,
                        align,
                        count,
                        Some(operation.span),
                    )?))
                } else {
                    Some(Binding::Place(self.memory.allocate_runtime(
                        pointee,
                        size,
                        align,
                        Some(operation.span),
                    )?))
                }
            }
            RuntimeDealloc => {
                self.memory.deallocate(place(0)?)?;
                None
            }
            AddressOffsetPlace { .. } => {
                let Scalar::Int(offset) = operand(1)?.scalar(&self.memory)? else {
                    return Err(invalid("non-integer offset"));
                };
                let offset = usize::try_from(offset).map_err(|_| invalid("negative offset"))?;
                Some(Binding::Place(self.memory.pointer_slot(place(0)?, offset)?))
            }
            AddressOffset { ty, member } => {
                let Scalar::Int(offset) = operand(1)?.scalar(&self.memory)? else {
                    return Err(invalid("non-integer offset"));
                };
                let offset = usize::try_from(offset).map_err(|_| invalid("negative offset"))?;
                if operation.operands.len() == 3 {
                    let Scalar::Int(index) = operand(2)?.scalar(&self.memory)? else {
                        return Err(invalid("non-integer element index"));
                    };
                    let index =
                        usize::try_from(index).map_err(|_| invalid("negative element index"))?;
                    Some(Binding::Place(self.memory.sequence_element(
                        place(0)?,
                        offset,
                        index,
                        self.types.resolve(*ty),
                    )?))
                } else {
                    Some(Binding::Place(self.memory.project(
                        place(0)?,
                        offset,
                        self.types.resolve(*ty),
                        *member,
                    )?))
                }
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
                    Binding::Callable(callable) => {
                        self.store_callable(destination, callable, operation.span)?;
                    }
                    _ => return Err(invalid("expected a value register")),
                }
                None
            }
            Clear => {
                self.memory.clear(place(0)?)?;
                None
            }
            IsInitialized | Drop { .. } => {
                panic!("physical lowering error: implicit destruction state")
            }
            Memcpy | Move | MoveBytes { .. } => {
                let storage = transfer_storage.unwrap();
                if let Some([size, align]) = witnessed_layout {
                    self.memory.check_layout(storage, size, align)?;
                }
                if matches!(operation.kind, MoveBytes { .. }) {
                    let Scalar::Int(size) = operand(2)?.scalar(&self.memory)? else {
                        return Err(invalid("non-integer transfer size"));
                    };
                    if usize::try_from(size).ok() != Some(self.memory.size(storage)?) {
                        return Err(invalid("transfer size differs from value layout"));
                    }
                }
                // Dictionary entries and direct function references have no allocated source.
                // Materializing one retains its evidence in the destination's own environment.
                if let Binding::Callable(callable) = operand(0)? {
                    let destination = place(1)?;
                    self.store_callable(destination, callable, operation.span)?;
                    return Ok(None);
                }
                let source = place(0)?;
                let destination = place(1)?;
                assert!(
                    self.memory.fully_initialized(source)?,
                    "physical lowering error at {:?}: transfer of an incomplete value",
                    operation.span
                );
                if matches!(operation.kind, Move | MoveBytes { .. }) && source != destination {
                    self.memory.check_consume(source)?;
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
                assert!(
                    self.memory.fully_initialized(source)?,
                    "physical lowering error at {:?}: replacement must be complete",
                    operation.span
                );
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
                    value => value.scalar(&self.memory)? == Scalar::from_literal(pattern)?,
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
                        let Scalar::Bool(indirect) = operand(0)?.scalar(&self.memory)? else {
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
        Ok(result)
    }

    fn call_native(&mut self, id: FunctionId, args: &[Binding]) -> Result<(), RuntimeError> {
        let native = self.native(id)?;
        if !native.supports_physical_call() {
            return Err(unsupported("this native adapter"));
        }
        let signature = native.signature();
        let (output, inputs) = args
            .split_last()
            .ok_or_else(|| invalid("native result missing"))?;
        if inputs.len() != signature.parameters.len() {
            return Err(invalid("native arity mismatch"));
        }
        let output = output.place()?;
        let addressor = matches!(signature.result, NativeResult::Addressor { .. });
        if matches!(signature.result, NativeResult::Optional { .. }) {
            self.memory
                .prepare_type(signature.result.ty(), &self.env(id))?;
        }
        if self.memory.is_pointer_slot(output)? != addressor
            || (!matches!(signature.result, NativeResult::Never)
                && !self
                    .memory
                    .compatible_types(output.ty, signature.result.ty())?)
        {
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
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use super::*;
    use crate::{Location, mir::physical::program::resolve_physical_program};
    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::wasm_bindgen_test;

    #[test]
    fn physical_runtime_types_preserve_nominal_identity() {
        use crate::{module::Path, types::r#type::FnType};
        use ustr::ustr;

        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "pub struct Meters(int) pub struct Seconds(int)",
                "nominal_types",
                Path::single_str("nominal_types"),
            )
            .unwrap()
            .module_id;
        let module = session.expect_fresh_module(module);
        let env = ModuleEnv::new(module, session.raw_modules());
        let meters = Type::named(module.get_type_def_id(ustr("Meters")).unwrap(), []);
        let seconds = Type::named(module.get_type_def_id(ustr("Seconds")).unwrap(), []);
        let repr = Type::tuple([ScalarKind::Int.ty()]);
        let variable = Type::variable_id(0);
        let mut types = RuntimeTypes::default();
        types.bind(meters, repr, env).unwrap();
        types.bind(repr, meters, env).unwrap();
        assert!(types.bind(meters, seconds, env).is_err());
        types.bind(variable, meters, env).unwrap();
        types.bind(variable, repr, env).unwrap();
        assert_eq!(types.resolve(variable), meters);
        assert!(types.bind(variable, seconds, env).is_err());
        assert_eq!(types.resolve(variable), meters);

        let callable = |mutable| {
            Type::function_type(FnType::new_mut_resolved(
                [(ScalarKind::Int.ty(), mutable)],
                Type::unit(),
                Default::default(),
            ))
        };
        assert!(types.bind(callable(false), callable(true), env).is_err());
    }

    #[test]
    fn physical_call_arguments_normalize_stored_evidence() {
        use crate::mir::function::Parameter;

        let session = CompilerSession::new();
        let env = ModuleEnv::new(session.std_module(), session.raw_modules());
        let mut memory = Memory::default();
        let flag = memory.allocate(ScalarKind::Bool.ty(), None).unwrap();
        memory.write(flag, Scalar::Bool(true)).unwrap();
        let output = memory.allocate(Type::unit(), None).unwrap();
        for convention in [
            CallResultConvention::Value,
            CallResultConvention::YIELDED_ONCE,
        ] {
            let body = Function::new(
                "evidence_arguments".into(),
                convention,
                vec![
                    Parameter {
                        ty: flag.ty,
                        kind: ParameterKind::Dictionary,
                    },
                    Parameter {
                        ty: output.ty,
                        kind: ParameterKind::Return,
                    },
                ],
                vec![],
                vec![],
            );
            for argument in [
                Binding::Evidence(Evidence::Storage(true)),
                Binding::Scalar(Scalar::Bool(true)),
                Binding::Place(flag),
                Binding::Projected(flag, 0),
            ] {
                let mut args = [argument, Binding::Place(output)];
                RuntimeTypes::for_call(&body, &mut args, &memory, env).unwrap();
                assert!(matches!(
                    args[0],
                    Binding::Evidence(Evidence::Storage(true))
                ));
            }
        }
    }

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
            profile: None,
            program: &program,
            memory: Memory::default(),
            limits: ReferenceInterpreterLimits::default(),
            fuel: None,
            depth: 0,
            session: &session,
            types: RuntimeTypes::default(),
            static_evidence: FxHashMap::default(),
            environments: FxHashMap::default(),
            prepared: FxHashSet::default(),
            prepared_monomorphic: FxHashSet::default(),
            projections: Vec::new(),
        };
        let entry = FunctionId::new(module, entry);
        interpreter
            .prepare_frame(
                entry,
                program.function(entry).unwrap(),
                &RuntimeTypes::default(),
            )
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
        session.set_allow_unsafe(true);
        session.set_mir_optimization(MirOptimization::Disabled);
        session.set_allow_experimental(true);
        let support = session.compile(
            "pub trait Describe<Self> { fn describe(value: Self) -> int; } impl Describe for int { fn describe(value: int) -> int { value } } pub struct Wrapper<T>(T) impl<T> Describe for Wrapper<T> where T: Describe, T: Value { fn describe(value: Wrapper<T>) -> int { describe(value.0) + 1 } } pub fn forward<T>(value: T) -> int where T: Describe, T: Value { describe(value) }
             pub trait Tag<Self> { fn tag(value: Self) -> int; } impl<A> Tag for Wrapper<A> { fn tag(value: Wrapper<A>) -> int { 42 } } pub fn tagged<T>(value: T) -> int where T: Tag { tag(value) }
             pub fn tag_wrapped<U>(value: U) -> int { tagged(Wrapper(value)) }
             pub subscript cell<T>(x: &mut T) -> T where T: Value { ref { let v = x; yield v; } mut { let mut v = x; yield v; x = v; } }",
            "generic_traits", Path::single_str("generic_traits"),
        ).unwrap().module_id;
        session.prepare_execution_target(ExecutionTarget::Mir, support);
        // Keep this invariant test: ordinary optimized execution can specialize away every
        // dictionary parameter, even after the physical backend joins the full language suite.
        for source in [
            "use generic_traits::cell; fn set<T>(value: &mut T, replacement: T) { let s = cell; let t = s; value->[t] = replacement; } fn compute(x: int) -> int { let mut n = x; set(n, x + 1); n }",
            "fn compute(x: int) -> int { let f = to_string; len(f(x)) }",
            "fn make<T>(value: T) -> () -> T { || value } fn compute(x: int) -> int { let f = make(x); let g = f; g() }",
            "fn make_array<T>(value: T) -> [T] { let mut a = [value]; array_append(a, value); a } fn compute(x: int) -> [int] { make_array(x) }",
            "fn maybe<T>(value: T, n: int) -> T { if n == 0 { to_string(value); }; value } fn compute(x: int) -> int { maybe(x, x) }",
            "fn maybe<T>(value: T, n: int) -> T { if n == 0 { let f = |x| x; f(value); }; value } fn compute(x: int) -> int { maybe(x, x) }",
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
        ] {
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
    fn physical_drop_initialized_requires_complete_storage() {
        use crate::module::Path;

        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "pub fn dispose(p: &mut (int, int)) { p.0 = 99; }",
                "initialized_drop",
                Path::single_str("initialized_drop"),
            )
            .unwrap()
            .module_id;
        let callee = FunctionId::new(
            module,
            session
                .expect_fresh_module(module)
                .get_local_function_id("dispose".into())
                .unwrap(),
        );
        let program = session.prepare_physical_program(module).unwrap();
        let mut interpreter = Interpreter {
            profile: None,
            program: &program,
            memory: Memory::default(),
            limits: ReferenceInterpreterLimits::default(),
            fuel: None,
            depth: 0,
            session: &session,
            types: RuntimeTypes::default(),
            static_evidence: FxHashMap::default(),
            environments: FxHashMap::default(),
            prepared: FxHashSet::default(),
            prepared_monomorphic: FxHashSet::default(),
            projections: Vec::new(),
        };
        interpreter.prepare_native_storage().unwrap();
        let ty = Type::tuple([ScalarKind::Int.ty(); 2]);
        let env = ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules());
        interpreter.memory.prepare_type(ty, &env).unwrap();
        let target = interpreter.memory.allocate(ty, None).unwrap();
        let first = interpreter
            .memory
            .project(target, 0, ScalarKind::Int.ty(), None)
            .unwrap();
        let second = interpreter
            .memory
            .project(target, size_of::<isize>(), ScalarKind::Int.ty(), None)
            .unwrap();
        let id = ValueId::from_index(0);
        let registers = FxHashMap::from_iter([(id, Binding::Place(target))]);
        let operation = Operation::drop_initialized(
            Location::new_synthesized(),
            mir::Value::Register(id),
            mir::Value::Function(callee),
            ty,
        );
        let body = program.function(callee).unwrap();
        for initialized in 0..=2 {
            if initialized == 1 {
                interpreter.memory.write(first, Scalar::Int(1)).unwrap();
                let destination = interpreter.memory.allocate(ty, None).unwrap();
                let destination_id = ValueId::from_index(1);
                let mut transfers = registers.clone();
                transfers.insert(destination_id, Binding::Place(destination));
                let source = mir::Value::Register(id);
                let destination = mir::Value::Register(destination_id);
                for transfer in [
                    Operation::move_value(operation.span, source.clone(), destination.clone()),
                    Operation::replace(operation.span, source, destination, None),
                ] {
                    assert!(
                        catch_unwind(AssertUnwindSafe(|| {
                            interpreter.operation(body, &[], &mut transfers, &transfer, 0)
                        }))
                        .is_err()
                    );
                }
            } else if initialized == 2 {
                interpreter.memory.write(second, Scalar::Int(2)).unwrap();
            }
            let result = catch_unwind(AssertUnwindSafe(|| {
                interpreter.drop_operation(body, &[], &registers, &operation, ty)
            }));
            if initialized < 2 {
                assert!(result.is_err());
                if initialized == 1 {
                    assert_eq!(interpreter.memory.read(first).unwrap(), Scalar::Int(1));
                }
            } else {
                result.unwrap().unwrap();
                assert!(!interpreter.memory.any_initialized(target).unwrap());
            }
        }
    }

    #[test]
    fn physical_scalar_transfers_preserve_absence_and_self_moves() {
        let program = resolve_physical_program([]).unwrap();
        let session = CompilerSession::new();
        let mut interpreter = Interpreter {
            profile: None,
            program: &program,
            memory: Memory::default(),
            limits: ReferenceInterpreterLimits::default(),
            fuel: None,
            depth: 0,
            session: &session,
            types: RuntimeTypes::default(),
            static_evidence: FxHashMap::default(),
            environments: FxHashMap::default(),
            prepared: FxHashSet::default(),
            prepared_monomorphic: FxHashSet::default(),
            projections: Vec::new(),
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
            catch_unwind(AssertUnwindSafe(|| {
                interpreter.operation(&body, &[], &mut registers, &self_move, 0)
            }))
            .is_err()
        );
        interpreter.memory.write(source, Scalar::Int(42)).unwrap();
        interpreter
            .operation(&body, &[], &mut registers, &self_move, 0)
            .unwrap();
        assert_eq!(interpreter.memory.read(source).unwrap(), Scalar::Int(42));

        let replace = Operation::replace(span, source_operand, destination_operand, None);
        interpreter.memory.clear(source).unwrap();
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                interpreter.operation(&body, &[], &mut registers, &replace, 0)
            }))
            .is_err()
        );
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
