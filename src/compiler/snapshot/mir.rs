// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Portable representation of standard-library MIR artifacts.

use std::panic::{AssertUnwindSafe, catch_unwind};

use super::{
    CacheChecksum, NativeTypeCatalog, SnapshotError, SnapshotFnType, SnapshotLiteral,
    SnapshotTypeGraph, SnapshotTypeGraphBuilder, SnapshotTypeId,
};
use crate::{
    Location,
    compiler::{
        Modules,
        artifacts::{MirArtifacts, Specialization},
    },
    containers::DenseBitSet,
    hir::{function::ArgConvention, value::VariantPayloadStorage},
    mir::{
        self, BasicBlock, Function, Operation, OperationKind, Parameter, ParameterKind,
        operation::{ProductProjectionMetadata, VariantMetadata},
        pass::OptimizationStats,
        terminator::{Terminator, TerminatorKind},
        value::{Constant, ConstantId, StaticEvidence},
    },
    module::{
        FunctionId, Module, ModuleEnv, ModuleId, ProjectionIndex, SubscriptId, TraitDictionaryId,
    },
    types::{
        effects::{EffType, Effect},
        r#trait::TraitDictionaryEntryIndex,
        r#type::{BareNativeTypeB, CallImplType, CallResultConvention, FnArgType, FnType, Type},
    },
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MirSnapshotStage {
    Raw,
    Optimized,
    Physical,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub(crate) struct CompiledStdMirSnapshot {
    module: ModuleId,
    module_path: String,
    stage: MirSnapshotStage,
    std_source_fingerprint: String,
    semantic_build_fingerprint: String,
    parent_checksum: CacheChecksum,
    payload: SnapshotMirArtifacts,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub(crate) struct SnapshotMirArtifacts {
    types: SnapshotTypeGraph,
    functions: Vec<Option<SnapshotMirFunction>>,
    specializations: Vec<SnapshotSpecialization>,
    pruned_specializations: u64,
    bounds_checks_removed: u64,
}

impl CompiledStdMirSnapshot {
    pub(crate) fn capture(
        stage: MirSnapshotStage,
        parent_checksum: CacheChecksum,
        artifacts: &MirArtifacts,
        module: &Module,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            module: module.module_id(),
            module_path: module.path().to_string(),
            stage,
            std_source_fingerprint: env!("FERLIUM_STD_SOURCE_FINGERPRINT").to_owned(),
            semantic_build_fingerprint: env!("FERLIUM_SEMANTIC_BUILD_FINGERPRINT").to_owned(),
            parent_checksum,
            payload: SnapshotMirArtifacts::capture(artifacts)?,
        })
    }

    pub(crate) fn encode(&self) -> Result<Vec<u8>, postcard::Error> {
        postcard::to_allocvec(self)
    }

    pub(crate) fn decode(bytes: &[u8]) -> Result<Self, postcard::Error> {
        postcard::from_bytes(bytes)
    }

    pub(crate) fn matches_current(
        &self,
        stage: MirSnapshotStage,
        parent_checksum: &CacheChecksum,
    ) -> bool {
        self.stage == stage
            && self.std_source_fingerprint == env!("FERLIUM_STD_SOURCE_FINGERPRINT")
            && self.semantic_build_fingerprint == env!("FERLIUM_SEMANTIC_BUILD_FINGERPRINT")
            && &self.parent_checksum == parent_checksum
    }

    pub(crate) fn validate_lineage(
        &self,
        stage: MirSnapshotStage,
        parent_checksum: &CacheChecksum,
    ) -> Result<(), SnapshotError> {
        self.matches_current(stage, parent_checksum)
            .then_some(())
            .ok_or(SnapshotError::StaleSnapshot)
    }

    pub(crate) fn restore_raw(
        &self,
        module: &Module,
        modules: &Modules,
    ) -> Result<MirArtifacts, SnapshotError> {
        self.validate_module(module)?;
        self.payload.restore_raw(module, modules, false)
    }

    pub(crate) fn restore_raw_verified(
        &self,
        module: &Module,
        modules: &Modules,
    ) -> Result<MirArtifacts, SnapshotError> {
        self.validate_module(module)?;
        self.payload.restore_raw(module, modules, true)
    }

    pub(crate) fn restore_optimized(
        &self,
        module: &Module,
        modules: &Modules,
        raw: &MirArtifacts,
    ) -> Result<MirArtifacts, SnapshotError> {
        self.validate_module(module)?;
        self.payload.restore_optimized(module, modules, raw, false)
    }

    pub(crate) fn restore_optimized_verified(
        &self,
        module: &Module,
        modules: &Modules,
        raw: &MirArtifacts,
    ) -> Result<MirArtifacts, SnapshotError> {
        self.validate_module(module)?;
        self.payload.restore_optimized(module, modules, raw, true)
    }

    fn validate_module(&self, module: &Module) -> Result<(), SnapshotError> {
        if self.module == module.module_id() && self.module_path == module.path().to_string() {
            Ok(())
        } else {
            Err(SnapshotError::StaleSnapshot)
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
struct SnapshotSpecialization {
    original: FunctionId,
    name: String,
    body: SnapshotMirFunction,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub(super) struct SnapshotMirFunction {
    name: String,
    result_convention: CallResultConvention,
    parameters: Vec<SnapshotParameter>,
    constants: Vec<SnapshotConstant>,
    blocks: Vec<SnapshotBasicBlock>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
struct SnapshotParameter {
    ty: SnapshotTypeId,
    kind: SnapshotParameterKind,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy)]
enum SnapshotParameterKind {
    Parameter(ArgConvention),
    Owned,
    Dictionary,
    Return,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
struct SnapshotConstant {
    ty: SnapshotTypeId,
    representation: SnapshotLiteral,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
struct SnapshotBasicBlock {
    operations: Vec<SnapshotOperation>,
    terminator: SnapshotTerminator,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
struct SnapshotOperation {
    result_id: Option<mir::ValueId>,
    span: Location,
    operands: Vec<SnapshotValue>,
    kind: SnapshotOperationKind,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
enum SnapshotValue {
    Constant(ConstantId),
    Dictionary(TraitDictionaryId),
    Subscript(SubscriptId),
    Evidence(SnapshotStaticEvidence),
    Function(FunctionId),
    Parameter(mir::ParameterId),
    Register(mir::ValueId),
    Pattern(SnapshotLiteral),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
enum SnapshotStaticEvidence {
    Dictionary {
        definition: TraitDictionaryId,
        captures: Vec<SnapshotStaticEvidence>,
    },
    Subscript {
        definition: SubscriptId,
        captures: Vec<SnapshotStaticEvidence>,
    },
    VariantPayloadStorage(bool),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
struct SnapshotCallImplType {
    function: SnapshotFnType,
    result_convention: CallResultConvention,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
struct SnapshotInstantiation {
    ty_args: Vec<SnapshotTypeId>,
    eff_args: Vec<Vec<Effect>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
struct SnapshotCallMetadata {
    instantiation: Option<SnapshotInstantiation>,
    owned_arguments: Vec<u32>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
enum SnapshotOperationKind {
    Alloca {
        ty: SnapshotTypeId,
    },
    AllocaPlace {
        pointing_to: SnapshotTypeId,
    },
    RuntimeAlloc {
        pointee: SnapshotTypeId,
    },
    RuntimeDealloc,
    Call {
        ty: SnapshotCallImplType,
        metadata: Option<SnapshotCallMetadata>,
    },
    Project {
        yielded: SnapshotTypeId,
        ty: SnapshotCallImplType,
    },
    EndProject,
    CompareEqual,
    Load,
    Subfield {
        ty: SnapshotTypeId,
        variant_payload: bool,
        has_layout_witness: bool,
        product_ty: Option<SnapshotTypeId>,
        product_layout_witness_tys: Vec<SnapshotTypeId>,
    },
    AddressOffset {
        ty: SnapshotTypeId,
        member: Option<ProjectionIndex>,
    },
    AddressOffsetPlace {
        pointing_to: SnapshotTypeId,
    },
    DictEntry {
        entry_index: TraitDictionaryEntryIndex,
        ty: SnapshotTypeId,
    },
    BuildDictionary {
        definition: TraitDictionaryId,
        ty: SnapshotTypeId,
    },
    SubscriptMember {
        mut_member: bool,
        ty: SnapshotTypeId,
    },
    BuildSubscriptEvidence {
        ty: SnapshotTypeId,
    },
    BuildSubscript {
        ty: SnapshotTypeId,
    },
    CloneSubscriptEnv {
        ty: SnapshotTypeId,
    },
    DropSubscriptEnv,
    BorrowSubscriptMember {
        mut_member: bool,
        ty: SnapshotTypeId,
    },
    Variant {
        tag: String,
        ty: SnapshotTypeId,
        payload_ty: SnapshotTypeId,
        storage: Option<VariantPayloadStorage>,
        has_layout_witness: bool,
    },
    BuildArray {
        element_ty: SnapshotTypeId,
    },
    ExtractTag,
    ExtractPayloadIndirection,
    IsInitialized,
    Store,
    Clear,
    Memcpy,
    Move,
    Replace,
    MoveBytes {
        ty: SnapshotTypeId,
    },
    StackSave,
    StackRestore,
    CheckCallDepth,
    CheckFuel,
    Clone {
        ty: SnapshotTypeId,
    },
    Drop {
        ty: SnapshotTypeId,
    },
    BuildClosure {
        function: FunctionId,
        num_hidden_dicts: u32,
        has_env_dict: bool,
        ty: SnapshotTypeId,
    },
    CloneClosureEnv {
        ty: SnapshotTypeId,
    },
    DropClosureEnv,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
struct SnapshotTerminator {
    span: Location,
    kind: SnapshotTerminatorKind,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
enum SnapshotTerminatorKind {
    Goto {
        target: mir::BlockId,
    },
    CondBr {
        condition: SnapshotValue,
        then_target: mir::BlockId,
        else_target: mir::BlockId,
    },
    SwitchVariant {
        tag: SnapshotValue,
        cases: Vec<(String, mir::BlockId)>,
        default: mir::BlockId,
    },
    Invoke {
        operation: SnapshotOperation,
        normal: mir::BlockId,
        error: mir::BlockId,
    },
    Yield {
        place: SnapshotValue,
        resume: mir::BlockId,
    },
    Return,
    PropagateError,
    FailureDuringCleanup,
    InvariantFailure {
        message: String,
    },
}

impl SnapshotMirArtifacts {
    pub(crate) fn capture(artifacts: &MirArtifacts) -> Result<Self, SnapshotError> {
        let native_types = NativeTypeCatalog::std();
        let native_name = |native: &BareNativeTypeB| native_types.canonical_name(native);
        let mut graph = SnapshotTypeGraphBuilder::new(&native_name);
        let functions = artifacts
            .bodies()
            .iter()
            .map(|function| {
                function
                    .as_ref()
                    .map(|function| SnapshotMirFunction::capture(function, &mut graph))
                    .transpose()
            })
            .collect::<Result<_, _>>()?;
        let specializations = artifacts
            .specializations()
            .iter()
            .map(|specialization| {
                Ok(SnapshotSpecialization {
                    original: specialization.original,
                    name: specialization.name.to_string(),
                    body: SnapshotMirFunction::capture(&specialization.body, &mut graph)?,
                })
            })
            .collect::<Result<_, SnapshotError>>()?;
        let stats = artifacts.optimization_stats();
        Ok(Self {
            types: graph.finish()?,
            functions,
            specializations,
            pruned_specializations: artifacts.pruned_specializations() as u64,
            bounds_checks_removed: stats.bounds_checks_removed as u64,
        })
    }

    pub(crate) fn restore_raw(
        &self,
        module: &Module,
        modules: &Modules,
        verify: bool,
    ) -> Result<MirArtifacts, SnapshotError> {
        if !self.specializations.is_empty()
            || self.pruned_specializations != 0
            || self.bounds_checks_removed != 0
        {
            return Err(SnapshotError::InvalidMir(
                "raw MIR snapshot contains optimized-only data".to_owned(),
            ));
        }
        let types = self.materialize_types()?;
        let functions = self.materialize_functions(&types)?;
        validate_declared_bodies(&functions, module)?;
        if verify {
            verify_functions(&functions, &[], module, modules)?;
        }
        Ok(MirArtifacts::from_snapshot_raw(functions, module, modules))
    }

    pub(crate) fn restore_optimized(
        &self,
        module: &Module,
        modules: &Modules,
        raw: &MirArtifacts,
        verify: bool,
    ) -> Result<MirArtifacts, SnapshotError> {
        let types = self.materialize_types()?;
        let functions = self.materialize_functions(&types)?;
        validate_declared_bodies(&functions, module)?;
        let specializations = self
            .specializations
            .iter()
            .map(|specialization| {
                Ok(Specialization {
                    original: specialization.original,
                    name: specialization.name.as_str().into(),
                    body: specialization.body.materialize(&types)?,
                })
            })
            .collect::<Result<Vec<_>, SnapshotError>>()?;
        if verify {
            verify_functions(&functions, &specializations, module, modules)?;
        }
        Ok(MirArtifacts::from_snapshot_optimized(
            functions,
            specializations,
            usize::try_from(self.pruned_specializations).map_err(|_| {
                SnapshotError::InvalidMir("pruned specialization count does not fit usize".into())
            })?,
            OptimizationStats {
                bounds_checks_removed: usize::try_from(self.bounds_checks_removed).map_err(
                    |_| SnapshotError::InvalidMir("optimization count does not fit usize".into()),
                )?,
            },
            raw,
        ))
    }

    fn materialize_functions(
        &self,
        types: &[Type],
    ) -> Result<Vec<Option<Function>>, SnapshotError> {
        self.functions
            .iter()
            .map(|function| {
                function
                    .as_ref()
                    .map(|function| function.materialize(types))
                    .transpose()
            })
            .collect()
    }

    fn materialize_types(&self) -> Result<Vec<Type>, SnapshotError> {
        let native_types = NativeTypeCatalog::std();
        self.types.materialize(&|name| native_types.resolve(name))
    }
}

fn validate_declared_bodies(
    functions: &[Option<Function>],
    module: &Module,
) -> Result<(), SnapshotError> {
    if functions.len() != module.function_count() {
        return Err(SnapshotError::InvalidMir(format!(
            "snapshot has {} declared function slots, module has {}",
            functions.len(),
            module.function_count()
        )));
    }
    for (index, (body, function)) in functions.iter().zip(module.iter_functions()).enumerate() {
        let expects_body = function.code.as_ref().as_script().is_some();
        if body.is_some() != expects_body {
            return Err(SnapshotError::InvalidMir(format!(
                "function slot {index} has body={}, origin={:?}",
                body.is_some(),
                function.origin,
            )));
        }
    }
    Ok(())
}

fn verify_functions(
    functions: &[Option<Function>],
    specializations: &[Specialization],
    module: &Module,
    modules: &Modules,
) -> Result<(), SnapshotError> {
    let env = ModuleEnv::new(module, modules);
    // Keep the process-wide panic hook intact: replacing it here could hide an unrelated thread's
    // panic. This recovery is consequently noisy, and cannot recover in panic=abort builds.
    catch_unwind(AssertUnwindSafe(|| {
        for function in functions.iter().flatten() {
            let roles = mir::role::check_function_operand_roles(function);
            mir::verify::verify_function_with_roles(function, env, roles);
        }
        for specialization in specializations {
            let roles = mir::role::check_function_operand_roles(&specialization.body);
            mir::verify::verify_function_with_roles(&specialization.body, env, roles);
        }
    }))
    .map_err(|_| SnapshotError::InvalidMir("MIR verification failed".to_owned()))
}

impl SnapshotMirFunction {
    pub(super) fn capture(
        function: &Function,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            name: function.name.to_string(),
            result_convention: function.result_convention(),
            parameters: function
                .parameters()
                .iter()
                .map(|parameter| {
                    Ok(SnapshotParameter {
                        ty: graph.capture(parameter.ty)?,
                        kind: parameter.kind.into(),
                    })
                })
                .collect::<Result<_, SnapshotError>>()?,
            constants: function
                .constants()
                .iter()
                .map(|constant| {
                    Ok(SnapshotConstant {
                        ty: graph.capture(constant.ty)?,
                        representation: SnapshotLiteral::capture(&constant.representation)?,
                    })
                })
                .collect::<Result<_, SnapshotError>>()?,
            blocks: function
                .block_slice()
                .iter()
                .map(|block| SnapshotBasicBlock::capture(block, graph))
                .collect::<Result<_, _>>()?,
        })
    }

    pub(super) fn materialize(&self, types: &[Type]) -> Result<Function, SnapshotError> {
        Ok(Function::new(
            self.name.as_str().into(),
            self.result_convention,
            self.parameters
                .iter()
                .map(|parameter| {
                    Ok(Parameter {
                        ty: resolve_type(types, parameter.ty)?,
                        kind: parameter.kind.into(),
                    })
                })
                .collect::<Result<_, SnapshotError>>()?,
            self.constants
                .iter()
                .map(|constant| {
                    Ok(Constant {
                        ty: resolve_type(types, constant.ty)?,
                        representation: constant.representation.materialize()?,
                    })
                })
                .collect::<Result<_, SnapshotError>>()?,
            self.blocks
                .iter()
                .map(|block| block.materialize(types))
                .collect::<Result<_, _>>()?,
        ))
    }
}

impl From<ParameterKind> for SnapshotParameterKind {
    fn from(value: ParameterKind) -> Self {
        match value {
            ParameterKind::Parameter(convention) => Self::Parameter(convention),
            ParameterKind::Owned => Self::Owned,
            ParameterKind::Dictionary => Self::Dictionary,
            ParameterKind::Return => Self::Return,
        }
    }
}

impl From<SnapshotParameterKind> for ParameterKind {
    fn from(value: SnapshotParameterKind) -> Self {
        match value {
            SnapshotParameterKind::Parameter(convention) => Self::Parameter(convention),
            SnapshotParameterKind::Owned => Self::Owned,
            SnapshotParameterKind::Dictionary => Self::Dictionary,
            SnapshotParameterKind::Return => Self::Return,
        }
    }
}

impl SnapshotBasicBlock {
    fn capture(
        block: &BasicBlock,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            operations: block
                .operations()
                .iter()
                .map(|operation| SnapshotOperation::capture(operation, graph))
                .collect::<Result<_, _>>()?,
            terminator: SnapshotTerminator::capture(block.terminator(), graph)?,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<BasicBlock, SnapshotError> {
        Ok(BasicBlock::new(
            self.operations
                .iter()
                .map(|operation| operation.materialize(types))
                .collect::<Result<_, _>>()?,
            self.terminator.materialize(types)?,
        ))
    }
}

impl SnapshotOperation {
    fn capture(
        operation: &Operation,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            result_id: operation.result_id(),
            span: operation.span,
            operands: operation
                .operands
                .iter()
                .map(SnapshotValue::capture)
                .collect::<Result<_, _>>()?,
            kind: SnapshotOperationKind::capture(&operation.kind, graph)?,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<Operation, SnapshotError> {
        let mut operation = Operation::from_parts(
            self.span,
            self.operands
                .iter()
                .map(SnapshotValue::materialize)
                .collect::<Result<Vec<_>, _>>()?
                .into_boxed_slice(),
            self.kind.materialize(types)?,
        );
        operation.assign_result_id(self.result_id);
        Ok(operation)
    }
}

impl SnapshotValue {
    fn capture(value: &mir::Value) -> Result<Self, SnapshotError> {
        Ok(match value {
            mir::Value::Constant(id) => Self::Constant(*id),
            mir::Value::Dictionary(id) => Self::Dictionary(*id),
            mir::Value::Subscript(id) => Self::Subscript(*id),
            mir::Value::Evidence(evidence) => Self::Evidence(evidence.as_ref().into()),
            mir::Value::Function(id) => Self::Function(*id),
            mir::Value::Parameter(id) => Self::Parameter(*id),
            mir::Value::Register(id) => Self::Register(*id),
            mir::Value::Pattern(pattern) => Self::Pattern(SnapshotLiteral::capture(pattern)?),
        })
    }

    fn materialize(&self) -> Result<mir::Value, SnapshotError> {
        Ok(match self {
            Self::Constant(id) => mir::Value::Constant(*id),
            Self::Dictionary(id) => mir::Value::Dictionary(*id),
            Self::Subscript(id) => mir::Value::Subscript(*id),
            Self::Evidence(evidence) => mir::Value::Evidence(Box::new(evidence.into())),
            Self::Function(id) => mir::Value::Function(*id),
            Self::Parameter(id) => mir::Value::Parameter(*id),
            Self::Register(id) => mir::Value::Register(*id),
            Self::Pattern(pattern) => mir::Value::Pattern(Box::new(pattern.materialize()?)),
        })
    }
}

impl From<&StaticEvidence> for SnapshotStaticEvidence {
    fn from(value: &StaticEvidence) -> Self {
        match value {
            StaticEvidence::Dictionary {
                definition,
                captures,
            } => Self::Dictionary {
                definition: *definition,
                captures: captures.iter().map(Self::from).collect(),
            },
            StaticEvidence::Subscript {
                definition,
                captures,
            } => Self::Subscript {
                definition: *definition,
                captures: captures.iter().map(Self::from).collect(),
            },
            StaticEvidence::VariantPayloadStorage(indirect) => {
                Self::VariantPayloadStorage(*indirect)
            }
        }
    }
}

impl From<&SnapshotStaticEvidence> for StaticEvidence {
    fn from(value: &SnapshotStaticEvidence) -> Self {
        match value {
            SnapshotStaticEvidence::Dictionary {
                definition,
                captures,
            } => Self::Dictionary {
                definition: *definition,
                captures: captures
                    .iter()
                    .map(Self::from)
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            },
            SnapshotStaticEvidence::Subscript {
                definition,
                captures,
            } => Self::Subscript {
                definition: *definition,
                captures: captures
                    .iter()
                    .map(Self::from)
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            },
            SnapshotStaticEvidence::VariantPayloadStorage(indirect) => {
                Self::VariantPayloadStorage(*indirect)
            }
        }
    }
}

impl SnapshotOperationKind {
    fn capture(
        kind: &OperationKind,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        use OperationKind as Source;
        use SnapshotOperationKind as Stored;

        Ok(match kind {
            Source::Alloca { ty } => Stored::Alloca {
                ty: graph.capture(*ty)?,
            },
            Source::AllocaPlace { pointing_to } => Stored::AllocaPlace {
                pointing_to: graph.capture(*pointing_to)?,
            },
            Source::RuntimeAlloc { pointee } => Stored::RuntimeAlloc {
                pointee: graph.capture(*pointee)?,
            },
            Source::RuntimeDealloc => Stored::RuntimeDealloc,
            Source::Call { ty, metadata } => Stored::Call {
                ty: SnapshotCallImplType::capture(ty, graph)?,
                metadata: metadata
                    .as_deref()
                    .map(|m| SnapshotCallMetadata::capture(m, graph))
                    .transpose()?,
            },
            Source::Project { yielded, ty } => Stored::Project {
                yielded: graph.capture(*yielded)?,
                ty: SnapshotCallImplType::capture(ty, graph)?,
            },
            Source::EndProject => Stored::EndProject,
            Source::CompareEqual => Stored::CompareEqual,
            Source::Load => Stored::Load,
            Source::Subfield {
                ty,
                variant_payload,
                has_layout_witness,
                product,
            } => Stored::Subfield {
                ty: graph.capture(*ty)?,
                variant_payload: *variant_payload,
                has_layout_witness: *has_layout_witness,
                product_ty: product
                    .as_ref()
                    .map(|product| graph.capture(product.aggregate_ty))
                    .transpose()?,
                product_layout_witness_tys: product.as_ref().map_or(Ok(Vec::new()), |product| {
                    product
                        .layout_witness_tys
                        .iter()
                        .map(|ty| graph.capture(*ty))
                        .collect()
                })?,
            },
            Source::AddressOffset { ty, member } => Stored::AddressOffset {
                ty: graph.capture(*ty)?,
                member: *member,
            },
            Source::AddressOffsetPlace { pointing_to } => Stored::AddressOffsetPlace {
                pointing_to: graph.capture(*pointing_to)?,
            },
            Source::DictEntry { entry_index, ty } => Stored::DictEntry {
                entry_index: *entry_index,
                ty: graph.capture(*ty)?,
            },
            Source::BuildDictionary { definition, ty } => Stored::BuildDictionary {
                definition: *definition,
                ty: graph.capture(*ty)?,
            },
            Source::SubscriptMember { mut_member, ty } => Stored::SubscriptMember {
                mut_member: *mut_member,
                ty: graph.capture(*ty)?,
            },
            Source::BuildSubscriptEvidence { ty } => Stored::BuildSubscriptEvidence {
                ty: graph.capture(*ty)?,
            },
            Source::BuildSubscript { ty } => Stored::BuildSubscript {
                ty: graph.capture(*ty)?,
            },
            Source::CloneSubscriptEnv { ty } => Stored::CloneSubscriptEnv {
                ty: graph.capture(*ty)?,
            },
            Source::DropSubscriptEnv => Stored::DropSubscriptEnv,
            Source::BorrowSubscriptMember { mut_member, ty } => Stored::BorrowSubscriptMember {
                mut_member: *mut_member,
                ty: graph.capture(*ty)?,
            },
            Source::Variant {
                tag,
                metadata,
                storage,
                has_layout_witness,
            } => Stored::Variant {
                tag: tag.to_string(),
                ty: graph.capture(metadata.ty)?,
                payload_ty: graph.capture(metadata.payload_ty)?,
                storage: *storage,
                has_layout_witness: *has_layout_witness,
            },
            Source::BuildArray { element_ty } => Stored::BuildArray {
                element_ty: graph.capture(*element_ty)?,
            },
            Source::ExtractTag => Stored::ExtractTag,
            Source::ExtractPayloadIndirection => Stored::ExtractPayloadIndirection,
            Source::IsInitialized => Stored::IsInitialized,
            Source::Store => Stored::Store,
            Source::Clear => Stored::Clear,
            Source::Memcpy => Stored::Memcpy,
            Source::Move => Stored::Move,
            Source::Replace => Stored::Replace,
            Source::MoveBytes { ty } => Stored::MoveBytes {
                ty: graph.capture(*ty)?,
            },
            Source::StackSave => Stored::StackSave,
            Source::StackRestore => Stored::StackRestore,
            Source::CheckCallDepth => Stored::CheckCallDepth,
            Source::CheckFuel => Stored::CheckFuel,
            Source::Clone { ty } => Stored::Clone {
                ty: graph.capture(*ty)?,
            },
            Source::Drop { ty } => Stored::Drop {
                ty: graph.capture(*ty)?,
            },
            Source::BuildClosure {
                function,
                num_hidden_dicts,
                has_env_dict,
                ty,
            } => Stored::BuildClosure {
                function: *function,
                num_hidden_dicts: *num_hidden_dicts,
                has_env_dict: *has_env_dict,
                ty: graph.capture(*ty)?,
            },
            Source::CloneClosureEnv { ty } => Stored::CloneClosureEnv {
                ty: graph.capture(*ty)?,
            },
            Source::DropClosureEnv => Stored::DropClosureEnv,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<OperationKind, SnapshotError> {
        use OperationKind as Runtime;
        use SnapshotOperationKind as Stored;

        Ok(match self {
            Stored::Alloca { ty } => Runtime::Alloca {
                ty: resolve_type(types, *ty)?,
            },
            Stored::AllocaPlace { pointing_to } => Runtime::AllocaPlace {
                pointing_to: resolve_type(types, *pointing_to)?,
            },
            Stored::RuntimeAlloc { pointee } => Runtime::RuntimeAlloc {
                pointee: resolve_type(types, *pointee)?,
            },
            Stored::RuntimeDealloc => Runtime::RuntimeDealloc,
            Stored::Call { ty, metadata } => Runtime::Call {
                ty: Box::new(ty.materialize(types)?),
                metadata: metadata
                    .as_ref()
                    .map(|m| m.materialize(types).map(Box::new))
                    .transpose()?,
            },
            Stored::Project { yielded, ty } => Runtime::Project {
                yielded: resolve_type(types, *yielded)?,
                ty: Box::new(ty.materialize(types)?),
            },
            Stored::EndProject => Runtime::EndProject,
            Stored::CompareEqual => Runtime::CompareEqual,
            Stored::Load => Runtime::Load,
            Stored::Subfield {
                ty,
                variant_payload,
                has_layout_witness,
                product_ty,
                product_layout_witness_tys,
            } => Runtime::Subfield {
                ty: resolve_type(types, *ty)?,
                variant_payload: *variant_payload,
                has_layout_witness: *has_layout_witness,
                product: product_ty
                    .map(|product_ty| {
                        Ok(Box::new(ProductProjectionMetadata {
                            aggregate_ty: resolve_type(types, product_ty)?,
                            layout_witness_tys: product_layout_witness_tys
                                .iter()
                                .map(|ty| resolve_type(types, *ty))
                                .collect::<Result<Vec<_>, _>>()?
                                .into_boxed_slice(),
                        }))
                    })
                    .transpose()?,
            },
            Stored::AddressOffset { ty, member } => Runtime::AddressOffset {
                ty: resolve_type(types, *ty)?,
                member: *member,
            },
            Stored::AddressOffsetPlace { pointing_to } => Runtime::AddressOffsetPlace {
                pointing_to: resolve_type(types, *pointing_to)?,
            },
            Stored::DictEntry { entry_index, ty } => Runtime::DictEntry {
                entry_index: *entry_index,
                ty: resolve_type(types, *ty)?,
            },
            Stored::BuildDictionary { definition, ty } => Runtime::BuildDictionary {
                definition: *definition,
                ty: resolve_type(types, *ty)?,
            },
            Stored::SubscriptMember { mut_member, ty } => Runtime::SubscriptMember {
                mut_member: *mut_member,
                ty: resolve_type(types, *ty)?,
            },
            Stored::BuildSubscriptEvidence { ty } => Runtime::BuildSubscriptEvidence {
                ty: resolve_type(types, *ty)?,
            },
            Stored::BuildSubscript { ty } => Runtime::BuildSubscript {
                ty: resolve_type(types, *ty)?,
            },
            Stored::CloneSubscriptEnv { ty } => Runtime::CloneSubscriptEnv {
                ty: resolve_type(types, *ty)?,
            },
            Stored::DropSubscriptEnv => Runtime::DropSubscriptEnv,
            Stored::BorrowSubscriptMember { mut_member, ty } => Runtime::BorrowSubscriptMember {
                mut_member: *mut_member,
                ty: resolve_type(types, *ty)?,
            },
            Stored::Variant {
                tag,
                ty,
                payload_ty,
                storage,
                has_layout_witness,
            } => Runtime::Variant {
                tag: tag.as_str().into(),
                metadata: Box::new(VariantMetadata {
                    ty: resolve_type(types, *ty)?,
                    payload_ty: resolve_type(types, *payload_ty)?,
                }),
                storage: *storage,
                has_layout_witness: *has_layout_witness,
            },
            Stored::BuildArray { element_ty } => Runtime::BuildArray {
                element_ty: resolve_type(types, *element_ty)?,
            },
            Stored::ExtractTag => Runtime::ExtractTag,
            Stored::ExtractPayloadIndirection => Runtime::ExtractPayloadIndirection,
            Stored::IsInitialized => Runtime::IsInitialized,
            Stored::Store => Runtime::Store,
            Stored::Clear => Runtime::Clear,
            Stored::Memcpy => Runtime::Memcpy,
            Stored::Move => Runtime::Move,
            Stored::Replace => Runtime::Replace,
            Stored::MoveBytes { ty } => Runtime::MoveBytes {
                ty: resolve_type(types, *ty)?,
            },
            Stored::StackSave => Runtime::StackSave,
            Stored::StackRestore => Runtime::StackRestore,
            Stored::CheckCallDepth => Runtime::CheckCallDepth,
            Stored::CheckFuel => Runtime::CheckFuel,
            Stored::Clone { ty } => Runtime::Clone {
                ty: resolve_type(types, *ty)?,
            },
            Stored::Drop { ty } => Runtime::Drop {
                ty: resolve_type(types, *ty)?,
            },
            Stored::BuildClosure {
                function,
                num_hidden_dicts,
                has_env_dict,
                ty,
            } => Runtime::BuildClosure {
                function: *function,
                num_hidden_dicts: *num_hidden_dicts,
                has_env_dict: *has_env_dict,
                ty: resolve_type(types, *ty)?,
            },
            Stored::CloneClosureEnv { ty } => Runtime::CloneClosureEnv {
                ty: resolve_type(types, *ty)?,
            },
            Stored::DropClosureEnv => Runtime::DropClosureEnv,
        })
    }
}

impl SnapshotCallImplType {
    fn capture(
        ty: &CallImplType,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            function: graph.capture_fn_type(&ty.fn_ty)?,
            result_convention: ty.result_convention,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<CallImplType, SnapshotError> {
        Ok(CallImplType::new(
            materialize_fn_type(&self.function, types)?,
            self.result_convention,
        ))
    }
}

impl SnapshotCallMetadata {
    fn capture(
        metadata: &mir::CallMetadata,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            instantiation: metadata
                .instantiation
                .as_ref()
                .map(|instantiation| {
                    Ok(SnapshotInstantiation {
                        ty_args: instantiation
                            .ty_args
                            .iter()
                            .map(|ty| graph.capture(*ty))
                            .collect::<Result<_, _>>()?,
                        eff_args: instantiation
                            .eff_args
                            .iter()
                            .map(|effects| effects.iter().collect())
                            .collect(),
                    })
                })
                .transpose()?,
            owned_arguments: metadata
                .owned_arguments
                .iter_ones()
                .map(|index| index as u32)
                .collect(),
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<mir::CallMetadata, SnapshotError> {
        let mut owned_arguments = DenseBitSet::empty();
        for &index in &self.owned_arguments {
            owned_arguments.insert(index as usize);
        }
        Ok(mir::CallMetadata {
            instantiation: self
                .instantiation
                .as_ref()
                .map(|instantiation| {
                    Ok(mir::Instantiation {
                        ty_args: instantiation
                            .ty_args
                            .iter()
                            .map(|id| resolve_type(types, *id))
                            .collect::<Result<_, _>>()?,
                        eff_args: instantiation
                            .eff_args
                            .iter()
                            .map(|effects| effects.iter().copied().collect::<EffType>())
                            .collect(),
                    })
                })
                .transpose()?,
            owned_arguments,
        })
    }
}

impl SnapshotTerminator {
    fn capture(
        terminator: &Terminator,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        use SnapshotTerminatorKind as Stored;
        use TerminatorKind as Source;

        Ok(Self {
            span: terminator.span,
            kind: match &terminator.kind {
                Source::Goto { target } => Stored::Goto { target: *target },
                Source::CondBr {
                    condition,
                    then_target,
                    else_target,
                } => Stored::CondBr {
                    condition: SnapshotValue::capture(condition)?,
                    then_target: *then_target,
                    else_target: *else_target,
                },
                Source::SwitchVariant {
                    tag,
                    cases,
                    default,
                } => Stored::SwitchVariant {
                    tag: SnapshotValue::capture(tag)?,
                    cases: cases
                        .iter()
                        .map(|(name, target)| (name.to_string(), *target))
                        .collect(),
                    default: *default,
                },
                Source::Invoke {
                    operation,
                    normal,
                    error,
                } => Stored::Invoke {
                    operation: SnapshotOperation::capture(operation, graph)?,
                    normal: *normal,
                    error: *error,
                },
                Source::Yield { place, resume } => Stored::Yield {
                    place: SnapshotValue::capture(place)?,
                    resume: *resume,
                },
                Source::Return => Stored::Return,
                Source::PropagateError => Stored::PropagateError,
                Source::FailureDuringCleanup => Stored::FailureDuringCleanup,
                Source::InvariantFailure { message } => Stored::InvariantFailure {
                    message: message.to_string(),
                },
            },
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<Terminator, SnapshotError> {
        use SnapshotTerminatorKind as Stored;
        use TerminatorKind as Runtime;

        Ok(Terminator {
            span: self.span,
            kind: match &self.kind {
                Stored::Goto { target } => Runtime::Goto { target: *target },
                Stored::CondBr {
                    condition,
                    then_target,
                    else_target,
                } => Runtime::CondBr {
                    condition: condition.materialize()?,
                    then_target: *then_target,
                    else_target: *else_target,
                },
                Stored::SwitchVariant {
                    tag,
                    cases,
                    default,
                } => Runtime::SwitchVariant {
                    tag: tag.materialize()?,
                    cases: cases
                        .iter()
                        .map(|(name, target)| (name.as_str().into(), *target))
                        .collect(),
                    default: *default,
                },
                Stored::Invoke {
                    operation,
                    normal,
                    error,
                } => Runtime::Invoke {
                    operation: operation.materialize(types)?,
                    normal: *normal,
                    error: *error,
                },
                Stored::Yield { place, resume } => Runtime::Yield {
                    place: place.materialize()?,
                    resume: *resume,
                },
                Stored::Return => Runtime::Return,
                Stored::PropagateError => Runtime::PropagateError,
                Stored::FailureDuringCleanup => Runtime::FailureDuringCleanup,
                Stored::InvariantFailure { message } => Runtime::InvariantFailure {
                    message: message.as_str().into(),
                },
            },
        })
    }
}

fn materialize_fn_type(function: &SnapshotFnType, types: &[Type]) -> Result<FnType, SnapshotError> {
    Ok(FnType::new(
        function
            .args
            .iter()
            .map(|arg| Ok(FnArgType::new(resolve_type(types, arg.ty)?, arg.mut_ty)))
            .collect::<Result<_, SnapshotError>>()?,
        resolve_type(types, function.ret)?,
        function.effects.iter().copied().collect(),
    ))
}

fn resolve_type(types: &[Type], id: SnapshotTypeId) -> Result<Type, SnapshotError> {
    types
        .get(id.0 as usize)
        .copied()
        .ok_or(SnapshotError::InvalidTypeReference(id.0))
}

#[cfg(test)]
mod tests {
    use ustr::ustr;

    use super::*;
    use crate::{
        compiler::{CompilerSession, ensure_mir_artifacts},
        std::STD_MODULE_ID,
    };

    #[test]
    fn invariant_failure_round_trips_its_diagnostic() {
        let terminator =
            Terminator::invariant_failure(Location::new_synthesized(), ustr("broken invariant"));
        let mut graph = SnapshotTypeGraphBuilder::new(&|_| None);
        let stored = SnapshotTerminator::capture(&terminator, &mut graph).unwrap();
        let bytes = postcard::to_allocvec(&stored).unwrap();
        let decoded: SnapshotTerminator = postcard::from_bytes(&bytes).unwrap();
        let restored = decoded.materialize(&[]).unwrap();
        assert!(restored == terminator);
        assert!(restored.operands().is_empty());
        assert_eq!(restored.successors().count(), 0);
    }

    #[test]
    fn std_raw_and_optimized_mir_round_trip() {
        let session = CompilerSession::new();
        ensure_mir_artifacts(session.raw_modules(), STD_MODULE_ID);
        let entry = session.raw_modules().get(STD_MODULE_ID).unwrap();
        let module = entry.module().unwrap();
        let raw = entry.raw_mir().unwrap();

        let raw_snapshot =
            CompiledStdMirSnapshot::capture(MirSnapshotStage::Raw, [7; 32], raw, module).unwrap();
        let encoded = raw_snapshot.encode().unwrap();
        let decoded = CompiledStdMirSnapshot::decode(&encoded).unwrap();
        assert_eq!(
            decoded.validate_lineage(MirSnapshotStage::Raw, &[7; 32]),
            Ok(())
        );
        assert_eq!(
            decoded.validate_lineage(MirSnapshotStage::Raw, &[8; 32]),
            Err(SnapshotError::StaleSnapshot)
        );
        for source_fingerprint in [true, false] {
            let mut stale = decoded.clone();
            let fingerprint = if source_fingerprint {
                &mut stale.std_source_fingerprint
            } else {
                &mut stale.semantic_build_fingerprint
            };
            fingerprint.push_str("-stale");
            assert_eq!(
                stale.validate_lineage(MirSnapshotStage::Raw, &[7; 32]),
                Err(SnapshotError::StaleSnapshot)
            );
        }
        let restored_raw = decoded
            .restore_raw_verified(module, session.raw_modules())
            .unwrap();
        let recaptured_raw =
            CompiledStdMirSnapshot::capture(MirSnapshotStage::Raw, [7; 32], &restored_raw, module)
                .unwrap();
        assert_eq!(recaptured_raw.encode().unwrap(), encoded);

        let optimized = MirArtifacts::optimize(raw, module, &session);
        let optimized_snapshot = CompiledStdMirSnapshot::capture(
            MirSnapshotStage::Optimized,
            [9; 32],
            &optimized,
            module,
        )
        .unwrap();
        let encoded = optimized_snapshot.encode().unwrap();
        let decoded = CompiledStdMirSnapshot::decode(&encoded).unwrap();
        assert_eq!(
            decoded.validate_lineage(MirSnapshotStage::Optimized, &[9; 32]),
            Ok(())
        );
        assert_eq!(
            decoded.validate_lineage(MirSnapshotStage::Optimized, &[8; 32]),
            Err(SnapshotError::StaleSnapshot)
        );
        let restored_optimized = decoded
            .restore_optimized_verified(module, session.raw_modules(), &restored_raw)
            .unwrap();
        let recaptured_optimized = CompiledStdMirSnapshot::capture(
            MirSnapshotStage::Optimized,
            [9; 32],
            &restored_optimized,
            module,
        )
        .unwrap();
        assert_eq!(recaptured_optimized.encode().unwrap(), encoded);
    }
}
