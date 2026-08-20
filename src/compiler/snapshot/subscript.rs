use crate::{
    module::{
        ProjectionEntry, ProjectionKey, ProjectionReceiverKey, SubscriptDefinition,
        SubscriptMember, SubscriptSignature,
    },
    types::r#type::{FnArgType, Type},
};

use super::{
    SnapshotError, SnapshotTypeGraphBuilder, SnapshotTypeId, semantic::SnapshotConstraint,
    type_graph::SnapshotFnArgType,
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotSubscript {
    args: Vec<SnapshotFnArgType>,
    ret: SnapshotTypeId,
    generic_params: Vec<(String, crate::Location)>,
    generic_effect_params: Vec<(String, crate::Location)>,
    arg_names: Vec<String>,
    constraints: Vec<SnapshotConstraint>,
    doc: Option<String>,
    ref_member: Option<SubscriptMember>,
    mut_member: Option<SubscriptMember>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SnapshotProjectionReceiver {
    Structural(SnapshotTypeId),
    Nominal(crate::module::TypeDefId),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotProjection {
    receiver: SnapshotProjectionReceiver,
    field: String,
    entry: ProjectionEntry,
}

fn capture_args(
    args: &[FnArgType],
    graph: &mut SnapshotTypeGraphBuilder<'_>,
) -> Result<Vec<SnapshotFnArgType>, SnapshotError> {
    args.iter()
        .map(|arg| {
            Ok(SnapshotFnArgType {
                ty: graph.capture(arg.ty)?,
                mut_ty: arg.mut_ty,
            })
        })
        .collect()
}

fn live_type(types: &[Type], id: SnapshotTypeId) -> Result<Type, SnapshotError> {
    types
        .get(id.0 as usize)
        .copied()
        .ok_or(SnapshotError::InvalidTypeReference(id.0))
}

fn live_args(args: &[SnapshotFnArgType], types: &[Type]) -> Result<Vec<FnArgType>, SnapshotError> {
    args.iter()
        .map(|arg| Ok(FnArgType::new(live_type(types, arg.ty)?, arg.mut_ty)))
        .collect()
}

impl SnapshotSubscript {
    pub(crate) fn capture(
        value: &SubscriptDefinition,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        let signature = value
            .resolved_signature()
            .ok_or(SnapshotError::PendingSubscriptInSnapshot)?;
        Ok(Self {
            args: capture_args(&signature.args, graph)?,
            ret: graph.capture(signature.ret)?,
            generic_params: signature
                .generic_params
                .iter()
                .map(|(name, span)| (name.to_string(), *span))
                .collect(),
            generic_effect_params: signature
                .generic_effect_params
                .iter()
                .map(|(name, span)| (name.to_string(), *span))
                .collect(),
            arg_names: signature
                .arg_names
                .iter()
                .map(ToString::to_string)
                .collect(),
            constraints: signature
                .constraints
                .iter()
                .map(|constraint| SnapshotConstraint::capture(constraint, graph))
                .collect::<Result<_, _>>()?,
            doc: signature.doc.clone(),
            ref_member: value.ref_member.clone(),
            mut_member: value.mut_member.clone(),
        })
    }

    pub(crate) fn materialize(&self, types: &[Type]) -> Result<SubscriptDefinition, SnapshotError> {
        Ok(SubscriptDefinition {
            signature: crate::module::SubscriptSignatureState::Resolved(SubscriptSignature {
                args: live_args(&self.args, types)?,
                ret: live_type(types, self.ret)?,
                generic_params: self
                    .generic_params
                    .iter()
                    .map(|(name, span)| (name.as_str().into(), *span))
                    .collect(),
                generic_effect_params: self
                    .generic_effect_params
                    .iter()
                    .map(|(name, span)| (name.as_str().into(), *span))
                    .collect(),
                arg_names: self
                    .arg_names
                    .iter()
                    .map(|name| name.as_str().into())
                    .collect(),
                constraints: self
                    .constraints
                    .iter()
                    .map(|constraint| constraint.materialize(types))
                    .collect::<Result<_, _>>()?,
                doc: self.doc.clone(),
            }),
            ref_member: self.ref_member.clone(),
            mut_member: self.mut_member.clone(),
        })
    }
}

impl SnapshotProjection {
    pub(super) fn stable_cmp(left: &Self, right: &Self) -> Ordering {
        fn receiver_cmp(
            left: &SnapshotProjectionReceiver,
            right: &SnapshotProjectionReceiver,
        ) -> Ordering {
            match (left, right) {
                (
                    SnapshotProjectionReceiver::Structural(left),
                    SnapshotProjectionReceiver::Structural(right),
                ) => left.cmp(right),
                (
                    SnapshotProjectionReceiver::Nominal(left),
                    SnapshotProjectionReceiver::Nominal(right),
                ) => (left.module.as_u32(), left.index.as_u32())
                    .cmp(&(right.module.as_u32(), right.index.as_u32())),
                (SnapshotProjectionReceiver::Structural(_), _) => Ordering::Less,
                (SnapshotProjectionReceiver::Nominal(_), _) => Ordering::Greater,
            }
        }

        receiver_cmp(&left.receiver, &right.receiver).then_with(|| left.field.cmp(&right.field))
    }

    pub(crate) fn capture(
        key: ProjectionKey,
        entry: ProjectionEntry,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            receiver: match key.receiver {
                ProjectionReceiverKey::Structural(ty) => {
                    SnapshotProjectionReceiver::Structural(graph.capture(ty)?)
                }
                ProjectionReceiverKey::Nominal(def) => SnapshotProjectionReceiver::Nominal(def),
            },
            field: key.field.to_string(),
            entry,
        })
    }

    pub(crate) fn materialize(
        &self,
        types: &[Type],
    ) -> Result<(ProjectionKey, ProjectionEntry), SnapshotError> {
        Ok((
            ProjectionKey {
                receiver: match self.receiver {
                    SnapshotProjectionReceiver::Structural(ty) => {
                        ProjectionReceiverKey::Structural(live_type(types, ty)?)
                    }
                    SnapshotProjectionReceiver::Nominal(def) => ProjectionReceiverKey::Nominal(def),
                },
                field: self.field.as_str().into(),
            },
            self.entry,
        ))
    }
}
use std::cmp::Ordering;
