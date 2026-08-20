use crate::{
    Location,
    ast::{Attribute, MetaItem},
    hir::function::CallableDefinition,
    module::TraitId,
    parser::location::InstantiableLocation,
    types::{
        effects::{EffType, Effect, EffectVar},
        r#type::{CallResultConvention, FnArgType, FnType, SubscriptType, Type, TypeVar},
        type_scheme::{ProjectionRequirementKind, PubTypeConstraint, TypeScheme},
    },
};

use super::{
    SnapshotError, SnapshotTypeGraphBuilder, SnapshotTypeId,
    type_graph::{SnapshotFnType, SnapshotSubscriptType},
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SnapshotMetaItem {
    Flag(String, Location),
    NameValue {
        key: (String, Location),
        value: (String, Location),
        span: Location,
    },
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotAttribute {
    pub(crate) path: (String, Location),
    pub(crate) items: Vec<SnapshotMetaItem>,
    pub(crate) span: Location,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SnapshotConstraint {
    TupleAtIndexIs {
        tuple_ty: SnapshotTypeId,
        tuple_span: InstantiableLocation,
        index: usize,
        index_span: InstantiableLocation,
        element_ty: SnapshotTypeId,
    },
    ProjectionSubscriptIs {
        requirement: ProjectionRequirementKind,
        receiver_span: InstantiableLocation,
        field: String,
        field_span: InstantiableLocation,
        subscript_ty: SnapshotSubscriptType,
    },
    TypeHasVariant {
        variant_ty: SnapshotTypeId,
        variant_span: InstantiableLocation,
        tag: String,
        payload_ty: SnapshotTypeId,
        payload_span: InstantiableLocation,
    },
    HaveTrait {
        trait_id: TraitId,
        input_tys: Vec<SnapshotTypeId>,
        output_tys: Vec<SnapshotTypeId>,
        output_effs: Vec<Vec<Effect>>,
        span: InstantiableLocation,
    },
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotCallableDefinition {
    pub(crate) ty_quantifiers: Vec<TypeVar>,
    pub(crate) eff_quantifiers: Vec<EffectVar>,
    pub(crate) ty: SnapshotFnType,
    pub(crate) constraints: Vec<SnapshotConstraint>,
    pub(crate) result_convention: CallResultConvention,
    pub(crate) result_rooted_in: Option<u32>,
    pub(crate) repeatable_addressor: bool,
    pub(crate) generic_params: Vec<(String, Location)>,
    pub(crate) generic_effect_params: Vec<(String, Location)>,
    pub(crate) arg_names: Vec<String>,
    pub(crate) doc: Option<String>,
    pub(crate) attributes: Vec<SnapshotAttribute>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotTypeScheme {
    pub(crate) ty_quantifiers: Vec<TypeVar>,
    pub(crate) eff_quantifiers: Vec<EffectVar>,
    pub(crate) ty: SnapshotTypeId,
    pub(crate) constraints: Vec<SnapshotConstraint>,
}

fn capture_effects(effects: &EffType) -> Vec<Effect> {
    effects.iter().collect()
}

fn materialize_effects(effects: &[Effect]) -> EffType {
    effects.iter().copied().collect()
}

fn ty(types: &[Type], id: SnapshotTypeId) -> Result<Type, SnapshotError> {
    types
        .get(id.0 as usize)
        .copied()
        .ok_or(SnapshotError::InvalidTypeReference(id.0))
}

pub(super) fn capture_attribute(attribute: &Attribute) -> SnapshotAttribute {
    SnapshotAttribute {
        path: (attribute.path.0.to_string(), attribute.path.1),
        items: attribute
            .items
            .iter()
            .map(|item| match item {
                MetaItem::Flag((name, span)) => SnapshotMetaItem::Flag(name.to_string(), *span),
                MetaItem::NameValue { key, value, span } => SnapshotMetaItem::NameValue {
                    key: (key.0.to_string(), key.1),
                    value: (value.0.to_string(), value.1),
                    span: *span,
                },
            })
            .collect(),
        span: attribute.span,
    }
}

pub(super) fn materialize_attribute(attribute: &SnapshotAttribute) -> Attribute {
    Attribute {
        path: (attribute.path.0.as_str().into(), attribute.path.1),
        items: attribute
            .items
            .iter()
            .map(|item| match item {
                SnapshotMetaItem::Flag(name, span) => MetaItem::Flag((name.as_str().into(), *span)),
                SnapshotMetaItem::NameValue { key, value, span } => MetaItem::NameValue {
                    key: (key.0.as_str().into(), key.1),
                    value: (value.0.as_str().into(), value.1),
                    span: *span,
                },
            })
            .collect(),
        span: attribute.span,
    }
}

impl SnapshotConstraint {
    pub(super) fn capture(
        constraint: &PubTypeConstraint,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(match constraint {
            PubTypeConstraint::TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => Self::TupleAtIndexIs {
                tuple_ty: graph.capture(*tuple_ty)?,
                tuple_span: tuple_span.clone(),
                index: *index,
                index_span: index_span.clone(),
                element_ty: graph.capture(*element_ty)?,
            },
            PubTypeConstraint::ProjectionSubscriptIs {
                requirement,
                receiver_span,
                field,
                field_span,
                subscript_ty,
            } => Self::ProjectionSubscriptIs {
                requirement: *requirement,
                receiver_span: receiver_span.clone(),
                field: field.to_string(),
                field_span: field_span.clone(),
                subscript_ty: graph.capture_subscript_type(subscript_ty)?,
            },
            PubTypeConstraint::TypeHasVariant {
                variant_ty,
                variant_span,
                tag,
                payload_ty,
                payload_span,
            } => Self::TypeHasVariant {
                variant_ty: graph.capture(*variant_ty)?,
                variant_span: variant_span.clone(),
                tag: tag.to_string(),
                payload_ty: graph.capture(*payload_ty)?,
                payload_span: payload_span.clone(),
            },
            PubTypeConstraint::HaveTrait {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
                span,
            } => Self::HaveTrait {
                trait_id: *trait_id,
                input_tys: input_tys
                    .iter()
                    .map(|ty| graph.capture(*ty))
                    .collect::<Result<_, _>>()?,
                output_tys: output_tys
                    .iter()
                    .map(|ty| graph.capture(*ty))
                    .collect::<Result<_, _>>()?,
                output_effs: output_effs.iter().map(capture_effects).collect(),
                span: span.clone(),
            },
        })
    }

    pub(super) fn materialize(&self, types: &[Type]) -> Result<PubTypeConstraint, SnapshotError> {
        Ok(match self {
            Self::TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => PubTypeConstraint::TupleAtIndexIs {
                tuple_ty: ty(types, *tuple_ty)?,
                tuple_span: tuple_span.clone(),
                index: *index,
                index_span: index_span.clone(),
                element_ty: ty(types, *element_ty)?,
            },
            Self::ProjectionSubscriptIs {
                requirement,
                receiver_span,
                field,
                field_span,
                subscript_ty,
            } => PubTypeConstraint::ProjectionSubscriptIs {
                requirement: *requirement,
                receiver_span: receiver_span.clone(),
                field: field.as_str().into(),
                field_span: field_span.clone(),
                subscript_ty: subscript_ty.materialize(types)?,
            },
            Self::TypeHasVariant {
                variant_ty,
                variant_span,
                tag,
                payload_ty,
                payload_span,
            } => PubTypeConstraint::TypeHasVariant {
                variant_ty: ty(types, *variant_ty)?,
                variant_span: variant_span.clone(),
                tag: tag.as_str().into(),
                payload_ty: ty(types, *payload_ty)?,
                payload_span: payload_span.clone(),
            },
            Self::HaveTrait {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
                span,
            } => PubTypeConstraint::HaveTrait {
                trait_id: *trait_id,
                input_tys: input_tys
                    .iter()
                    .map(|id| ty(types, *id))
                    .collect::<Result<_, _>>()?,
                output_tys: output_tys
                    .iter()
                    .map(|id| ty(types, *id))
                    .collect::<Result<_, _>>()?,
                output_effs: output_effs
                    .iter()
                    .map(|set| materialize_effects(set))
                    .collect(),
                span: span.clone(),
            },
        })
    }
}

impl SnapshotCallableDefinition {
    pub(crate) fn capture(
        definition: &CallableDefinition,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            ty_quantifiers: definition.ty_scheme.ty_quantifiers.clone(),
            eff_quantifiers: {
                let mut vars = definition
                    .ty_scheme
                    .eff_quantifiers
                    .iter()
                    .copied()
                    .collect::<Vec<_>>();
                vars.sort();
                vars
            },
            ty: graph.capture_fn_type(&definition.ty_scheme.ty)?,
            constraints: definition
                .ty_scheme
                .constraints
                .iter()
                .map(|constraint| SnapshotConstraint::capture(constraint, graph))
                .collect::<Result<_, _>>()?,
            result_convention: definition.result_convention,
            result_rooted_in: definition.result_rooted_in,
            repeatable_addressor: definition.repeatable_addressor,
            generic_params: definition
                .generic_params
                .iter()
                .map(|(name, span)| (name.to_string(), *span))
                .collect(),
            generic_effect_params: definition
                .generic_effect_params
                .iter()
                .map(|(name, span)| (name.to_string(), *span))
                .collect(),
            arg_names: definition
                .arg_names
                .iter()
                .map(ToString::to_string)
                .collect(),
            doc: definition.doc.clone(),
            attributes: definition
                .attributes
                .iter()
                .map(capture_attribute)
                .collect(),
        })
    }

    pub(crate) fn materialize(&self, types: &[Type]) -> Result<CallableDefinition, SnapshotError> {
        let fn_type = self.ty.materialize(types)?;
        Ok(CallableDefinition {
            ty_scheme: TypeScheme {
                ty_quantifiers: self.ty_quantifiers.clone(),
                eff_quantifiers: self.eff_quantifiers.iter().copied().collect(),
                ty: fn_type,
                constraints: self
                    .constraints
                    .iter()
                    .map(|constraint| constraint.materialize(types))
                    .collect::<Result<_, _>>()?,
            },
            result_convention: self.result_convention,
            result_rooted_in: self.result_rooted_in,
            repeatable_addressor: self.repeatable_addressor,
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
            doc: self.doc.clone(),
            attributes: self.attributes.iter().map(materialize_attribute).collect(),
        })
    }
}

impl SnapshotTypeScheme {
    pub(crate) fn capture(
        value: &TypeScheme<Type>,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            ty_quantifiers: value.ty_quantifiers.to_vec(),
            eff_quantifiers: {
                let mut vars = value.eff_quantifiers.iter().copied().collect::<Vec<_>>();
                vars.sort();
                vars
            },
            ty: graph.capture(value.ty)?,
            constraints: value
                .constraints
                .iter()
                .map(|constraint| SnapshotConstraint::capture(constraint, graph))
                .collect::<Result<_, _>>()?,
        })
    }

    pub(crate) fn materialize(&self, types: &[Type]) -> Result<TypeScheme<Type>, SnapshotError> {
        Ok(TypeScheme {
            ty_quantifiers: self.ty_quantifiers.to_vec(),
            eff_quantifiers: self.eff_quantifiers.iter().copied().collect(),
            ty: ty(types, self.ty)?,
            constraints: self
                .constraints
                .iter()
                .map(|constraint| constraint.materialize(types))
                .collect::<Result<_, _>>()?,
        })
    }
}

impl SnapshotFnType {
    pub(crate) fn materialize(&self, types: &[Type]) -> Result<FnType, SnapshotError> {
        Ok(FnType::new(
            self.args
                .iter()
                .map(|arg| Ok(FnArgType::new(ty(types, arg.ty)?, arg.mut_ty)))
                .collect::<Result<_, SnapshotError>>()?,
            ty(types, self.ret)?,
            materialize_effects(&self.effects),
        ))
    }
}

impl SnapshotSubscriptType {
    pub(crate) fn materialize(&self, types: &[Type]) -> Result<SubscriptType, SnapshotError> {
        let member = |member: &super::type_graph::SnapshotSubscriptMemberType| {
            crate::types::r#type::SubscriptMemberType::new(
                materialize_effects(&member.effects),
                member.result_convention,
            )
        };
        Ok(SubscriptType::new(
            self.args
                .iter()
                .map(|arg| Ok(FnArgType::new(ty(types, arg.ty)?, arg.mut_ty)))
                .collect::<Result<_, SnapshotError>>()?,
            ty(types, self.ret)?,
            self.ref_member.as_ref().map(member),
            self.mut_member.as_ref().map(member),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, module::function::CallableOrigin};

    use crate::compiler::snapshot::NativeTypeCatalog;

    #[test]
    fn std_callable_definitions_round_trip_through_snapshot_types() {
        let session = CompilerSession::new();
        let catalog = NativeTypeCatalog::std();
        let native_name =
            |native: &crate::types::r#type::BareNativeTypeB| catalog.canonical_name(native);
        let mut graph = SnapshotTypeGraphBuilder::new(&native_name);

        let functions = session
            .std_module()
            .functions
            .iter()
            .filter(|function| {
                matches!(
                    function.origin,
                    CallableOrigin::Script | CallableOrigin::Native { .. }
                )
            })
            .take(32)
            .collect::<Vec<_>>();
        let definitions = functions
            .iter()
            .map(|function| SnapshotCallableDefinition::capture(&function.definition, &mut graph))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let graph = graph.finish().unwrap();
        let types = graph.materialize(&|name| catalog.resolve(name)).unwrap();

        for (function, definition) in functions.into_iter().zip(definitions) {
            let restored = definition.materialize(&types).unwrap();
            assert_eq!(restored.signature(), function.definition.signature());
            assert_eq!(
                restored.result_rooted_in,
                function.definition.result_rooted_in
            );
            assert_eq!(
                restored.repeatable_addressor,
                function.definition.repeatable_addressor
            );
            assert_eq!(restored.doc, function.definition.doc);
            assert_eq!(
                format!("{:?}", restored.attributes),
                format!("{:?}", function.definition.attributes)
            );
        }
    }
}
