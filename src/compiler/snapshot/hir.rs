use la_arena::{Arena, Idx, RawIdx};

use crate::{
    Location, ast,
    containers::b,
    hir::{
        self, ENode, ENodeArena, ENodeId, Elaborated, FnInstData, NodeKind,
        dictionary::DictionaryReq, function::ArgConvention,
    },
    module::{
        ExtraParameterId, FunctionId, LocalDeclId, ProjectionIndex, ResolvedLocalClone,
        ResolvedLocalDrop, ResolvedTakeLocalValueMode, SubscriptId, TraitImplId,
    },
    types::{
        effects::{EffType, Effect},
        r#type::{CallImplType, CallResultConvention, Type},
        type_scheme::ProjectionRequirementKind,
    },
};

use super::{
    SnapshotError, SnapshotLiteral, SnapshotTypeGraphBuilder, SnapshotTypeId,
    type_graph::{SnapshotFnType, SnapshotSubscriptType},
};

type SnapshotNodeId = u32;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotPath(Vec<(String, Location)>);

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
enum SnapshotDictionaryReq {
    ProjectionSubscript {
        requirement: ProjectionRequirementKind,
        field: String,
        subscript_ty: SnapshotSubscriptType,
    },
    VariantPayloadStorage {
        variant_ty: SnapshotTypeId,
        tag: String,
        payload_ty: SnapshotTypeId,
    },
    TraitImpl {
        trait_id: crate::module::TraitId,
        input_tys: Vec<SnapshotTypeId>,
        output_tys: Vec<SnapshotTypeId>,
        output_effs: Vec<Vec<Effect>>,
    },
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotFnInstData {
    dicts_req: Vec<SnapshotDictionaryReq>,
    ty_args: Vec<SnapshotTypeId>,
    eff_args: Vec<Vec<Effect>>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotCallImplType {
    fn_ty: SnapshotFnType,
    result_convention: CallResultConvention,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotCallArgument {
    value: SnapshotNodeId,
    passing: ArgConvention,
}

/// Process-independent equivalent of final elaborated HIR.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotHirArena {
    nodes: Vec<SnapshotNode>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotNode {
    kind: SnapshotNodeKind,
    ty: SnapshotTypeId,
    effects: Vec<Effect>,
    span: Location,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
enum SnapshotNodeKind {
    Uninit,
    Immediate(SnapshotLiteral),
    Tuple(Vec<SnapshotNodeId>),
    Record(Vec<SnapshotNodeId>),
    Array(Vec<SnapshotNodeId>),
    Variant {
        tag: String,
        payload: SnapshotNodeId,
        payload_storage: Option<hir::VariantPayloadStorageSource>,
    },
    BuildClosure {
        function: SnapshotNodeId,
        dictionary_captures: Vec<SnapshotNodeId>,
        captures: Vec<SnapshotNodeId>,
        captures_value_dictionary: Option<SnapshotNodeId>,
    },
    Project {
        value: SnapshotNodeId,
        index: ProjectionIndex,
    },
    ExtractTag(SnapshotNodeId),
    LoadLocal(LocalDeclId),
    StoreLocal {
        value: SnapshotNodeId,
        id: LocalDeclId,
    },
    TakeLocalValue {
        id: LocalDeclId,
        mode: ResolvedTakeLocalValueMode,
    },
    BuildSubscriptValue {
        subscript: SnapshotNodeId,
        evidence_captures: Vec<SnapshotNodeId>,
    },
    Assign {
        place: SnapshotNodeId,
        value: SnapshotNodeId,
        drop: Option<ResolvedLocalDrop>,
    },
    CloneValue {
        source: SnapshotNodeId,
        clone: ResolvedLocalClone,
    },
    CloneClosureEnv(SnapshotNodeId),
    DropClosureEnv(SnapshotNodeId),
    CloneSubscriptValue(SnapshotNodeId),
    DropSubscriptValue(SnapshotNodeId),
    GetFunction {
        function: FunctionId,
        function_path: SnapshotPath,
        function_span: Location,
        inst_data: SnapshotFnInstData,
    },
    GetSubscript {
        subscript: SubscriptId,
        subscript_path: SnapshotPath,
        inst_data: SnapshotFnInstData,
    },
    FunctionApply {
        function: SnapshotNodeId,
        arguments: Vec<SnapshotCallArgument>,
        ty: SnapshotCallImplType,
    },
    SubscriptApply {
        subscript: SnapshotNodeId,
        mut_member: bool,
        arguments: Vec<SnapshotCallArgument>,
        ty: SnapshotCallImplType,
    },
    StaticApply {
        function: FunctionId,
        function_path: Option<SnapshotPath>,
        function_span: Location,
        extra_arguments: Vec<SnapshotNodeId>,
        arguments: Vec<SnapshotCallArgument>,
        argument_names: Vec<String>,
        argument_name_hint_policy: ast::UnnamedArg,
        ty: SnapshotCallImplType,
        inst_data: SnapshotFnInstData,
    },
    GetDictionary(TraitImplId),
    LoadDictionary(ExtraParameterId),
    LoadSubscriptEvidence(ExtraParameterId),
    LoadVariantPayloadStorageEvidence(ExtraParameterId),
    GetDictionaryFunction {
        dictionary: SnapshotNodeId,
        entry_index: crate::types::r#trait::TraitDictionaryEntryIndex,
    },
    CallDictionaryFunction {
        dictionary: SnapshotNodeId,
        entry_index: crate::types::r#trait::TraitDictionaryEntryIndex,
        arguments: Vec<SnapshotCallArgument>,
        ty: SnapshotCallImplType,
    },
    CheckCallDepth,
    CheckFuel,
    Block {
        body: Vec<SnapshotNodeId>,
        cleanup: Vec<LocalDeclId>,
    },
    Return(SnapshotNodeId),
    Yield(SnapshotNodeId),
    WithYielded {
        accessor: SnapshotNodeId,
        binding: LocalDeclId,
        body: SnapshotNodeId,
    },
    WithPlace {
        place: SnapshotNodeId,
        binding: LocalDeclId,
        body: SnapshotNodeId,
    },
    Case {
        value: SnapshotNodeId,
        alternatives: Vec<(SnapshotLiteral, SnapshotNodeId)>,
        default: SnapshotNodeId,
    },
    Loop {
        label: hir::LoopId,
        body: SnapshotNodeId,
    },
    Break {
        label: hir::LoopId,
        value: SnapshotNodeId,
    },
    Continue(hir::LoopId),
}

fn node_id(id: ENodeId) -> SnapshotNodeId {
    id.into_raw().into_u32()
}

fn live_node_id(id: SnapshotNodeId, node_count: usize) -> Result<ENodeId, SnapshotError> {
    if id as usize >= node_count {
        return Err(SnapshotError::InvalidHirNodeReference(id));
    }
    Ok(Idx::from_raw(RawIdx::from_u32(id)))
}

fn path(path: &ast::Path) -> SnapshotPath {
    SnapshotPath(
        path.segments
            .iter()
            .map(|(name, span)| (name.to_string(), *span))
            .collect(),
    )
}

fn live_path(path: &SnapshotPath) -> ast::Path {
    ast::Path {
        segments: path
            .0
            .iter()
            .map(|(name, span)| (name.as_str().into(), *span))
            .collect(),
    }
}

fn effects(value: &EffType) -> Vec<Effect> {
    value.iter().collect()
}

fn live_effects(value: &[Effect]) -> EffType {
    value.iter().copied().collect()
}

fn live_ty(types: &[Type], id: SnapshotTypeId) -> Result<Type, SnapshotError> {
    types
        .get(id.0 as usize)
        .copied()
        .ok_or(SnapshotError::InvalidTypeReference(id.0))
}

fn capture_types(
    values: &[Type],
    graph: &mut SnapshotTypeGraphBuilder<'_>,
) -> Result<Vec<SnapshotTypeId>, SnapshotError> {
    values.iter().map(|value| graph.capture(*value)).collect()
}

fn live_types(values: &[SnapshotTypeId], types: &[Type]) -> Result<Vec<Type>, SnapshotError> {
    values.iter().map(|id| live_ty(types, *id)).collect()
}

impl SnapshotDictionaryReq {
    fn capture(
        value: &DictionaryReq,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(match value {
            DictionaryReq::ProjectionSubscript {
                requirement,
                field,
                subscript_ty,
            } => Self::ProjectionSubscript {
                requirement: *requirement,
                field: field.to_string(),
                subscript_ty: graph.capture_subscript_type(subscript_ty)?,
            },
            DictionaryReq::VariantPayloadStorage {
                variant_ty,
                tag,
                payload_ty,
            } => Self::VariantPayloadStorage {
                variant_ty: graph.capture(*variant_ty)?,
                tag: tag.to_string(),
                payload_ty: graph.capture(*payload_ty)?,
            },
            DictionaryReq::TraitImpl {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
            } => Self::TraitImpl {
                trait_id: *trait_id,
                input_tys: capture_types(input_tys, graph)?,
                output_tys: capture_types(output_tys, graph)?,
                output_effs: output_effs.iter().map(effects).collect(),
            },
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<DictionaryReq, SnapshotError> {
        Ok(match self {
            Self::ProjectionSubscript {
                requirement,
                field,
                subscript_ty,
            } => DictionaryReq::ProjectionSubscript {
                requirement: *requirement,
                field: field.as_str().into(),
                subscript_ty: subscript_ty.materialize(types)?,
            },
            Self::VariantPayloadStorage {
                variant_ty,
                tag,
                payload_ty,
            } => DictionaryReq::VariantPayloadStorage {
                variant_ty: live_ty(types, *variant_ty)?,
                tag: tag.as_str().into(),
                payload_ty: live_ty(types, *payload_ty)?,
            },
            Self::TraitImpl {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
            } => DictionaryReq::TraitImpl {
                trait_id: *trait_id,
                input_tys: live_types(input_tys, types)?,
                output_tys: live_types(output_tys, types)?,
                output_effs: output_effs
                    .iter()
                    .map(|value| live_effects(value))
                    .collect(),
            },
        })
    }
}

impl SnapshotFnInstData {
    fn capture(
        value: &FnInstData,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            dicts_req: value
                .dicts_req
                .iter()
                .map(|value| SnapshotDictionaryReq::capture(value, graph))
                .collect::<Result<_, _>>()?,
            ty_args: capture_types(&value.ty_args, graph)?,
            eff_args: value.eff_args.iter().map(effects).collect(),
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<FnInstData, SnapshotError> {
        Ok(FnInstData {
            dicts_req: self
                .dicts_req
                .iter()
                .map(|value| value.materialize(types))
                .collect::<Result<_, _>>()?,
            ty_args: live_types(&self.ty_args, types)?,
            eff_args: self
                .eff_args
                .iter()
                .map(|value| live_effects(value))
                .collect(),
        })
    }
}

impl SnapshotCallImplType {
    fn capture(
        value: &CallImplType,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            fn_ty: graph.capture_fn_type(&value.fn_ty)?,
            result_convention: value.result_convention,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<CallImplType, SnapshotError> {
        Ok(CallImplType::new(
            self.fn_ty.materialize(types)?,
            self.result_convention,
        ))
    }
}

fn capture_args(values: &[hir::CallArgument<Elaborated>]) -> Vec<SnapshotCallArgument> {
    values
        .iter()
        .map(|value| SnapshotCallArgument {
            value: node_id(value.value),
            passing: value.passing,
        })
        .collect()
}

fn live_args(
    values: &[SnapshotCallArgument],
    node_count: usize,
) -> Result<Vec<hir::CallArgument<Elaborated>>, SnapshotError> {
    values
        .iter()
        .map(|value| {
            Ok(hir::CallArgument {
                value: live_node_id(value.value, node_count)?,
                passing: value.passing,
            })
        })
        .collect()
}

impl SnapshotHirArena {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn capture(
        arena: &ENodeArena,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        let nodes = arena
            .iter()
            .map(|(_, node)| SnapshotNode::capture(node, graph))
            .collect::<Result<_, _>>()?;
        Ok(Self { nodes })
    }

    pub(crate) fn capture_from(
        arena: &ENodeArena,
        start: usize,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        if start > arena.len() {
            return Err(SnapshotError::CheckpointShapeMismatch(format!(
                "HIR starts at {start}, but arena has {} nodes",
                arena.len()
            )));
        }
        let nodes = arena
            .iter()
            .skip(start)
            .map(|(_, node)| SnapshotNode::capture(node, graph))
            .collect::<Result<_, _>>()?;
        Ok(Self { nodes })
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn materialize(&self, types: &[Type]) -> Result<ENodeArena, SnapshotError> {
        let node_count = self.nodes.len();
        let mut arena = Arena::with_capacity(node_count);
        for node in &self.nodes {
            arena.alloc(node.materialize(types, node_count)?);
        }
        Ok(arena)
    }

    pub(crate) fn append_to(
        &self,
        arena: &mut ENodeArena,
        expected_start: usize,
        final_node_count: usize,
        types: &[Type],
    ) -> Result<(), SnapshotError> {
        if arena.len() != expected_start || final_node_count != expected_start + self.nodes.len() {
            return Err(SnapshotError::CheckpointShapeMismatch(format!(
                "HIR checkpoint expected {expected_start}..{final_node_count}, current arena has {} nodes and delta has {}",
                arena.len(),
                self.nodes.len()
            )));
        }
        for node in &self.nodes {
            arena.alloc(node.materialize(types, final_node_count)?);
        }
        Ok(())
    }
}

impl SnapshotNode {
    fn capture(
        node: &ENode,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            kind: SnapshotNodeKind::capture(&node.kind, graph)?,
            ty: graph.capture(node.ty)?,
            effects: effects(&node.effects),
            span: node.span,
        })
    }

    fn materialize(&self, types: &[Type], node_count: usize) -> Result<ENode, SnapshotError> {
        Ok(ENode {
            kind: self.kind.materialize(types, node_count)?,
            ty: live_ty(types, self.ty)?,
            effects: live_effects(&self.effects),
            span: self.span,
        })
    }
}

impl SnapshotNodeKind {
    #[allow(clippy::too_many_lines)]
    fn capture(
        kind: &NodeKind<Elaborated>,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        let ids = |values: &[ENodeId]| values.iter().copied().map(node_id).collect();
        Ok(match kind {
            NodeKind::Uninit => Self::Uninit,
            NodeKind::Immediate(value) => Self::Immediate(SnapshotLiteral::capture(value)?),
            NodeKind::Tuple(values) => Self::Tuple(ids(values)),
            NodeKind::Record(values) => Self::Record(ids(values)),
            NodeKind::Array(values) => Self::Array(ids(values)),
            NodeKind::Variant(value) => Self::Variant {
                tag: value.tag.to_string(),
                payload: node_id(value.payload),
                payload_storage: value.payload_storage,
            },
            NodeKind::BuildClosure(value) => Self::BuildClosure {
                function: node_id(value.function),
                dictionary_captures: ids(&value.dictionary_captures),
                captures: ids(&value.captures),
                captures_value_dictionary: value.captures_value_dictionary.map(node_id),
            },
            NodeKind::Project(value) => Self::Project {
                value: node_id(value.value),
                index: value.index,
            },
            NodeKind::FieldAccess(value) => match *value {},
            NodeKind::ExtractTag(value) => Self::ExtractTag(node_id(*value)),
            NodeKind::LoadLocal(value) => Self::LoadLocal(value.id),
            NodeKind::StoreLocal(value) => Self::StoreLocal {
                value: node_id(value.value),
                id: value.id,
            },
            NodeKind::TakeLocalValue(value) => Self::TakeLocalValue {
                id: value.id,
                mode: value.mode,
            },
            NodeKind::BuildSubscriptValue(value) => Self::BuildSubscriptValue {
                subscript: node_id(value.subscript),
                evidence_captures: ids(&value.evidence_captures),
            },
            NodeKind::Assign(value) => Self::Assign {
                place: node_id(value.place),
                value: node_id(value.value),
                drop: value.drop,
            },
            NodeKind::CloneValue(value) => Self::CloneValue {
                source: node_id(value.source),
                clone: value.clone,
            },
            NodeKind::CloneClosureEnv(value) => Self::CloneClosureEnv(node_id(value.source)),
            NodeKind::DropClosureEnv(value) => Self::DropClosureEnv(node_id(value.target)),
            NodeKind::CloneSubscriptValue(value) => {
                Self::CloneSubscriptValue(node_id(value.source))
            }
            NodeKind::DropSubscriptValue(value) => Self::DropSubscriptValue(node_id(value.target)),
            NodeKind::GetFunction(value) => Self::GetFunction {
                function: value.function,
                function_path: path(&value.function_path),
                function_span: value.function_span,
                inst_data: SnapshotFnInstData::capture(&value.inst_data, graph)?,
            },
            NodeKind::GetSubscript(value) => Self::GetSubscript {
                subscript: value.subscript,
                subscript_path: path(&value.subscript_path),
                inst_data: SnapshotFnInstData::capture(&value.inst_data, graph)?,
            },
            NodeKind::FunctionApply(value) => Self::FunctionApply {
                function: node_id(value.function),
                arguments: capture_args(&value.arguments),
                ty: SnapshotCallImplType::capture(&value.ty, graph)?,
            },
            NodeKind::SubscriptApply(value) => Self::SubscriptApply {
                subscript: node_id(value.subscript),
                mut_member: value.mut_member,
                arguments: capture_args(&value.arguments),
                ty: SnapshotCallImplType::capture(&value.ty, graph)?,
            },
            NodeKind::StaticApply(value) => Self::StaticApply {
                function: value.function,
                function_path: value.function_path.as_ref().map(path),
                function_span: value.function_span,
                extra_arguments: ids(&value.extra_arguments),
                arguments: capture_args(&value.arguments),
                argument_names: value
                    .argument_names
                    .iter()
                    .map(ToString::to_string)
                    .collect(),
                argument_name_hint_policy: value.argument_name_hint_policy,
                ty: SnapshotCallImplType::capture(&value.ty, graph)?,
                inst_data: SnapshotFnInstData::capture(&value.inst_data, graph)?,
            },
            NodeKind::TraitMethodApply(value) => match *value {},
            NodeKind::GetTraitMethod(value) => match *value {},
            NodeKind::GetTraitAssociatedConst(value) => match *value {},
            NodeKind::GetTraitDictionary(value) => match *value {},
            NodeKind::GetDictionary(value) => Self::GetDictionary(value.dictionary),
            NodeKind::LoadDictionary(value) => Self::LoadDictionary(value.extra_parameter),
            NodeKind::LoadSubscriptEvidence(value) => {
                Self::LoadSubscriptEvidence(value.extra_parameter)
            }
            NodeKind::LoadVariantPayloadStorageEvidence(value) => {
                Self::LoadVariantPayloadStorageEvidence(value.extra_parameter)
            }
            NodeKind::GetDictionaryFunction(value) => Self::GetDictionaryFunction {
                dictionary: node_id(value.dictionary),
                entry_index: value.entry_index,
            },
            NodeKind::CallDictionaryFunction(value) => Self::CallDictionaryFunction {
                dictionary: node_id(value.dictionary),
                entry_index: value.entry_index,
                arguments: capture_args(&value.arguments),
                ty: SnapshotCallImplType::capture(&value.ty, graph)?,
            },
            NodeKind::CheckCallDepth => Self::CheckCallDepth,
            NodeKind::CheckFuel => Self::CheckFuel,
            NodeKind::Block(value) => Self::Block {
                body: ids(&value.body),
                cleanup: value.cleanup.clone(),
            },
            NodeKind::Return(value) => Self::Return(node_id(*value)),
            NodeKind::Yield(value) => Self::Yield(node_id(*value)),
            NodeKind::WithYielded(value) => Self::WithYielded {
                accessor: node_id(value.accessor),
                binding: value.binding,
                body: node_id(value.body),
            },
            NodeKind::WithPlace(value) => Self::WithPlace {
                place: node_id(value.place),
                binding: value.binding,
                body: node_id(value.body),
            },
            NodeKind::Case(value) => Self::Case {
                value: node_id(value.value),
                alternatives: value
                    .alternatives
                    .iter()
                    .map(|(literal, node)| Ok((SnapshotLiteral::capture(literal)?, node_id(*node))))
                    .collect::<Result<_, SnapshotError>>()?,
                default: node_id(value.default),
            },
            NodeKind::Loop(value) => Self::Loop {
                label: value.label,
                body: node_id(value.body),
            },
            NodeKind::Break(value) => Self::Break {
                label: value.label,
                value: node_id(value.value),
            },
            NodeKind::Continue(value) => Self::Continue(value.label),
        })
    }

    #[allow(clippy::too_many_lines)]
    fn materialize(
        &self,
        types: &[Type],
        node_count: usize,
    ) -> Result<NodeKind<Elaborated>, SnapshotError> {
        let id = |value| live_node_id(value, node_count);
        let ids = |values: &[SnapshotNodeId]| -> Result<Vec<ENodeId>, SnapshotError> {
            values.iter().map(|value| id(*value)).collect()
        };
        Ok(match self {
            Self::Uninit => NodeKind::Uninit,
            Self::Immediate(value) => NodeKind::Immediate(value.materialize()?),
            Self::Tuple(values) => NodeKind::Tuple(b(ids(values)?.into())),
            Self::Record(values) => NodeKind::Record(b(ids(values)?.into())),
            Self::Array(values) => NodeKind::Array(b(ids(values)?.into())),
            Self::Variant {
                tag,
                payload,
                payload_storage,
            } => NodeKind::Variant(hir::Variant {
                tag: tag.as_str().into(),
                payload: id(*payload)?,
                payload_storage: *payload_storage,
            }),
            Self::BuildClosure {
                function,
                dictionary_captures,
                captures,
                captures_value_dictionary,
            } => NodeKind::BuildClosure(b(hir::BuildClosure {
                function: id(*function)?,
                dictionary_captures: ids(dictionary_captures)?,
                captures: ids(captures)?,
                captures_value_dictionary: captures_value_dictionary.map(id).transpose()?,
            })),
            Self::Project { value, index } => {
                NodeKind::Project(hir::Project::new(id(*value)?, *index))
            }
            Self::ExtractTag(value) => NodeKind::ExtractTag(id(*value)?),
            Self::LoadLocal(local) => NodeKind::LoadLocal(hir::LoadLocal { id: *local }),
            Self::StoreLocal { value, id: local } => NodeKind::StoreLocal(hir::StoreLocal {
                value: id(*value)?,
                id: *local,
            }),
            Self::TakeLocalValue { id: local, mode } => {
                NodeKind::TakeLocalValue(hir::TakeLocalValue {
                    id: *local,
                    mode: *mode,
                })
            }
            Self::BuildSubscriptValue {
                subscript,
                evidence_captures,
            } => NodeKind::BuildSubscriptValue(b(hir::BuildSubscriptValue {
                subscript: id(*subscript)?,
                evidence_captures: ids(evidence_captures)?,
            })),
            Self::Assign { place, value, drop } => NodeKind::Assign(hir::Assignment {
                place: id(*place)?,
                value: id(*value)?,
                drop: *drop,
            }),
            Self::CloneValue { source, clone } => NodeKind::CloneValue(hir::CloneValue {
                source: id(*source)?,
                clone: *clone,
            }),
            Self::CloneClosureEnv(source) => NodeKind::CloneClosureEnv(hir::CloneClosureEnv {
                source: id(*source)?,
            }),
            Self::DropClosureEnv(target) => NodeKind::DropClosureEnv(hir::DropClosureEnv {
                target: id(*target)?,
            }),
            Self::CloneSubscriptValue(source) => {
                NodeKind::CloneSubscriptValue(hir::CloneSubscriptValue {
                    source: id(*source)?,
                })
            }
            Self::DropSubscriptValue(target) => {
                NodeKind::DropSubscriptValue(hir::DropSubscriptValue {
                    target: id(*target)?,
                })
            }
            Self::GetFunction {
                function,
                function_path,
                function_span,
                inst_data,
            } => NodeKind::GetFunction(b(hir::GetFunction {
                function: *function,
                function_path: live_path(function_path),
                function_span: *function_span,
                inst_data: inst_data.materialize(types)?,
            })),
            Self::GetSubscript {
                subscript,
                subscript_path,
                inst_data,
            } => NodeKind::GetSubscript(b(hir::GetSubscript {
                subscript: *subscript,
                subscript_path: live_path(subscript_path),
                inst_data: inst_data.materialize(types)?,
            })),
            Self::FunctionApply {
                function,
                arguments,
                ty,
            } => NodeKind::FunctionApply(b(hir::FunctionApplication {
                function: id(*function)?,
                arguments: live_args(arguments, node_count)?,
                ty: ty.materialize(types)?,
            })),
            Self::SubscriptApply {
                subscript,
                mut_member,
                arguments,
                ty,
            } => NodeKind::SubscriptApply(b(hir::SubscriptApplication {
                subscript: id(*subscript)?,
                mut_member: *mut_member,
                arguments: live_args(arguments, node_count)?,
                ty: ty.materialize(types)?,
            })),
            Self::StaticApply {
                function,
                function_path,
                function_span,
                extra_arguments,
                arguments,
                argument_names,
                argument_name_hint_policy,
                ty,
                inst_data,
            } => NodeKind::StaticApply(b(hir::StaticApplication {
                function: *function,
                function_path: function_path.as_ref().map(live_path),
                function_span: *function_span,
                extra_arguments: ids(extra_arguments)?,
                arguments: live_args(arguments, node_count)?,
                argument_names: argument_names
                    .iter()
                    .map(|name| name.as_str().into())
                    .collect(),
                argument_name_hint_policy: *argument_name_hint_policy,
                ty: ty.materialize(types)?,
                inst_data: inst_data.materialize(types)?,
            })),
            Self::GetDictionary(dictionary) => NodeKind::GetDictionary(hir::GetDictionary {
                dictionary: *dictionary,
            }),
            Self::LoadDictionary(extra_parameter) => {
                NodeKind::LoadDictionary(hir::LoadDictionary {
                    extra_parameter: *extra_parameter,
                })
            }
            Self::LoadSubscriptEvidence(extra_parameter) => {
                NodeKind::LoadSubscriptEvidence(hir::LoadSubscriptEvidence {
                    extra_parameter: *extra_parameter,
                })
            }
            Self::LoadVariantPayloadStorageEvidence(extra_parameter) => {
                NodeKind::LoadVariantPayloadStorageEvidence(
                    hir::LoadVariantPayloadStorageEvidence {
                        extra_parameter: *extra_parameter,
                    },
                )
            }
            Self::GetDictionaryFunction {
                dictionary,
                entry_index,
            } => NodeKind::GetDictionaryFunction(hir::GetDictionaryFunction {
                dictionary: id(*dictionary)?,
                entry_index: *entry_index,
            }),
            Self::CallDictionaryFunction {
                dictionary,
                entry_index,
                arguments,
                ty,
            } => NodeKind::CallDictionaryFunction(b(hir::CallDictionaryFunction {
                dictionary: id(*dictionary)?,
                entry_index: *entry_index,
                arguments: live_args(arguments, node_count)?,
                ty: ty.materialize(types)?,
            })),
            Self::CheckCallDepth => NodeKind::CheckCallDepth,
            Self::CheckFuel => NodeKind::CheckFuel,
            Self::Block { body, cleanup } => NodeKind::Block(b(hir::Block {
                body: b(ids(body)?.into()),
                cleanup: cleanup.clone(),
            })),
            Self::Return(value) => NodeKind::Return(id(*value)?),
            Self::Yield(value) => NodeKind::Yield(id(*value)?),
            Self::WithYielded {
                accessor,
                binding,
                body,
            } => NodeKind::WithYielded(hir::WithYielded {
                accessor: id(*accessor)?,
                binding: *binding,
                body: id(*body)?,
            }),
            Self::WithPlace {
                place,
                binding,
                body,
            } => NodeKind::WithPlace(hir::WithPlace {
                place: id(*place)?,
                binding: *binding,
                body: id(*body)?,
            }),
            Self::Case {
                value,
                alternatives,
                default,
            } => NodeKind::Case(b(hir::Case {
                value: id(*value)?,
                alternatives: alternatives
                    .iter()
                    .map(|(literal, node)| Ok((literal.materialize()?, id(*node)?)))
                    .collect::<Result<_, SnapshotError>>()?,
                default: id(*default)?,
            })),
            Self::Loop { label, body } => NodeKind::Loop(hir::Loop::new(*label, id(*body)?)),
            Self::Break { label, value } => NodeKind::Break(hir::Break::new(*label, id(*value)?)),
            Self::Continue(label) => NodeKind::Continue(hir::Continue::new(*label)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, compiler::snapshot::NativeTypeCatalog};

    #[test]
    fn complete_std_hir_arena_round_trips() {
        let session = CompilerSession::new();
        let catalog = NativeTypeCatalog::std();
        let native_name =
            |native: &crate::types::r#type::BareNativeTypeB| catalog.canonical_name(native);
        let mut graph = SnapshotTypeGraphBuilder::new(&native_name);
        let snapshot =
            SnapshotHirArena::capture(&session.std_module().hir_arena, &mut graph).unwrap();
        let graph = graph.finish().unwrap();
        let types = graph.materialize(&|name| catalog.resolve(name)).unwrap();
        let restored = snapshot.materialize(&types).unwrap();

        assert_eq!(restored.len(), session.std_module().hir_arena.len());
        let native_name =
            |native: &crate::types::r#type::BareNativeTypeB| catalog.canonical_name(native);
        let mut restored_graph = SnapshotTypeGraphBuilder::new(&native_name);
        let recaptured = SnapshotHirArena::capture(&restored, &mut restored_graph).unwrap();
        assert_eq!(recaptured, snapshot);
    }
}
