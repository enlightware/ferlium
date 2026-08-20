use crate::{
    Location,
    types::{
        r#trait::{Trait, TraitAssociatedConst, TraitImplPolicy, TraitSpans},
        r#type::{
            Type, TypeAliasEntry, TypeDef, TypeDefProductDocs, TypeDefShapeDocs, TypeDefSlot,
            TypeDefVariantDocs,
        },
    },
};

use super::{
    SnapshotCallableDefinition, SnapshotError, SnapshotTypeGraphBuilder, SnapshotTypeId,
    SnapshotTypeScheme,
    semantic::{SnapshotAttribute, SnapshotConstraint, capture_attribute, materialize_attribute},
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotTypeAlias {
    name: String,
    generic_params: Vec<(String, Location)>,
    ty_var_count: u32,
    ty: SnapshotTypeId,
    doc: Option<String>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
enum SnapshotTypeDefProductDocs {
    Unit,
    Tuple(Vec<Option<String>>),
    Record(Vec<(String, Option<String>)>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
enum SnapshotTypeDefShapeDocs {
    Struct(SnapshotTypeDefProductDocs),
    Enum(Vec<(String, Option<String>, SnapshotTypeDefProductDocs)>),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotTypeDef {
    name: String,
    doc: Option<String>,
    generic_params: Vec<(String, Location)>,
    generic_effect_params: Vec<(String, Location)>,
    shape: SnapshotTypeScheme,
    shape_docs: SnapshotTypeDefShapeDocs,
    span: Location,
    attributes: Vec<SnapshotAttribute>,
    default_variant: Option<String>,
    has_custom_value_impl: bool,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SnapshotTypeDefSlot {
    Reserved {
        name: String,
        generic_params: Vec<(String, Location)>,
        generic_effect_params: Vec<(String, Location)>,
        span: Location,
    },
    Resolved(SnapshotTypeDef),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotTraitAssociatedConst {
    name: String,
    ty: SnapshotTypeId,
    doc: Option<String>,
}

/// A source-owned trait. Native derivers are deliberately not serializable and must be restored by
/// native registration before/after the appropriate source checkpoint.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub(crate) struct SnapshotTrait {
    name: String,
    doc: Option<String>,
    input_type_names: Vec<String>,
    output_type_names: Vec<String>,
    output_effect_names: Vec<String>,
    parent_constraints: Vec<SnapshotConstraint>,
    constraints: Vec<SnapshotConstraint>,
    methods: Vec<(String, SnapshotCallableDefinition)>,
    associated_consts: Vec<SnapshotTraitAssociatedConst>,
    impl_policy: TraitImplPolicy,
    spans: Option<TraitSpans>,
}

fn names(values: &[(ustr::Ustr, Location)]) -> Vec<(String, Location)> {
    values
        .iter()
        .map(|(name, span)| (name.to_string(), *span))
        .collect()
}

fn live_names(values: &[(String, Location)]) -> Vec<(ustr::Ustr, Location)> {
    values
        .iter()
        .map(|(name, span)| (name.as_str().into(), *span))
        .collect()
}

impl SnapshotTypeAlias {
    pub(crate) fn capture(
        value: &TypeAliasEntry,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            name: value.name.to_string(),
            generic_params: names(&value.generic_params),
            ty_var_count: value.ty_var_count,
            ty: graph.capture(value.ty)?,
            doc: value.doc.clone(),
        })
    }

    pub(crate) fn materialize(&self, types: &[Type]) -> Result<TypeAliasEntry, SnapshotError> {
        Ok(TypeAliasEntry {
            name: self.name.as_str().into(),
            generic_params: live_names(&self.generic_params),
            ty_var_count: self.ty_var_count,
            ty: types
                .get(self.ty.0 as usize)
                .copied()
                .ok_or(SnapshotError::InvalidTypeReference(self.ty.0))?,
            doc: self.doc.clone(),
        })
    }
}

impl SnapshotTypeDefProductDocs {
    fn capture(value: &TypeDefProductDocs) -> Self {
        match value {
            TypeDefProductDocs::Unit => Self::Unit,
            TypeDefProductDocs::Tuple(fields) => Self::Tuple(fields.clone()),
            TypeDefProductDocs::Record(fields) => Self::Record(
                fields
                    .iter()
                    .map(|(name, doc)| (name.to_string(), doc.clone()))
                    .collect(),
            ),
        }
    }

    fn materialize(&self) -> TypeDefProductDocs {
        match self {
            Self::Unit => TypeDefProductDocs::Unit,
            Self::Tuple(fields) => TypeDefProductDocs::Tuple(fields.clone()),
            Self::Record(fields) => TypeDefProductDocs::Record(
                fields
                    .iter()
                    .map(|(name, doc)| (name.as_str().into(), doc.clone()))
                    .collect(),
            ),
        }
    }
}

impl SnapshotTypeDefShapeDocs {
    fn capture(value: &TypeDefShapeDocs) -> Self {
        match value {
            TypeDefShapeDocs::Struct(product) => {
                Self::Struct(SnapshotTypeDefProductDocs::capture(product))
            }
            TypeDefShapeDocs::Enum(variants) => Self::Enum(
                variants
                    .iter()
                    .map(|variant| {
                        (
                            variant.name.to_string(),
                            variant.doc.clone(),
                            SnapshotTypeDefProductDocs::capture(&variant.payload),
                        )
                    })
                    .collect(),
            ),
        }
    }

    fn materialize(&self) -> TypeDefShapeDocs {
        match self {
            Self::Struct(product) => TypeDefShapeDocs::Struct(product.materialize()),
            Self::Enum(variants) => TypeDefShapeDocs::Enum(
                variants
                    .iter()
                    .map(|(name, doc, payload)| TypeDefVariantDocs {
                        name: name.as_str().into(),
                        doc: doc.clone(),
                        payload: payload.materialize(),
                    })
                    .collect(),
            ),
        }
    }
}

impl SnapshotTypeDef {
    fn capture(
        value: &TypeDef,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            name: value.name.to_string(),
            doc: value.doc.clone(),
            generic_params: names(&value.generic_params),
            generic_effect_params: names(&value.generic_effect_params),
            shape: SnapshotTypeScheme::capture(&value.shape, graph)?,
            shape_docs: SnapshotTypeDefShapeDocs::capture(&value.shape_docs),
            span: value.span,
            attributes: value.attributes.iter().map(capture_attribute).collect(),
            default_variant: value.default_variant.map(|name| name.to_string()),
            has_custom_value_impl: value.has_custom_value_impl,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<TypeDef, SnapshotError> {
        Ok(TypeDef {
            name: self.name.as_str().into(),
            doc: self.doc.clone(),
            generic_params: live_names(&self.generic_params),
            generic_effect_params: live_names(&self.generic_effect_params),
            shape: self.shape.materialize(types)?,
            shape_docs: self.shape_docs.materialize(),
            span: self.span,
            attributes: self.attributes.iter().map(materialize_attribute).collect(),
            default_variant: self.default_variant.as_deref().map(Into::into),
            has_custom_value_impl: self.has_custom_value_impl,
        })
    }
}

impl SnapshotTypeDefSlot {
    pub(crate) fn capture(
        value: &TypeDefSlot,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(match value {
            TypeDefSlot::Reserved(_) => Self::Reserved {
                name: value.name().to_string(),
                generic_params: names(value.generic_params()),
                generic_effect_params: names(value.generic_effect_params()),
                span: value.span(),
            },
            TypeDefSlot::Resolved(value) => Self::Resolved(SnapshotTypeDef::capture(value, graph)?),
        })
    }

    pub(crate) fn materialize(&self, types: &[Type]) -> Result<TypeDefSlot, SnapshotError> {
        Ok(match self {
            Self::Reserved {
                name,
                generic_params,
                generic_effect_params,
                span,
            } => TypeDefSlot::reserved(
                name.as_str().into(),
                live_names(generic_params),
                live_names(generic_effect_params),
                *span,
            ),
            Self::Resolved(value) => TypeDefSlot::resolved(value.materialize(types)?),
        })
    }
}

impl SnapshotTrait {
    pub(crate) fn capture(
        value: &Trait,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        if !value.derivers.is_empty() {
            return Err(SnapshotError::NativeDeriverInSourceCheckpoint(
                value.name.to_string(),
            ));
        }
        Ok(Self {
            name: value.name.to_string(),
            doc: value.doc.clone(),
            input_type_names: value
                .input_type_names
                .iter()
                .map(ToString::to_string)
                .collect(),
            output_type_names: value
                .output_type_names
                .iter()
                .map(ToString::to_string)
                .collect(),
            output_effect_names: value
                .output_effect_names
                .iter()
                .map(ToString::to_string)
                .collect(),
            parent_constraints: value
                .parent_constraints
                .iter()
                .map(|value| SnapshotConstraint::capture(value, graph))
                .collect::<Result<_, _>>()?,
            constraints: value
                .constraints
                .iter()
                .map(|value| SnapshotConstraint::capture(value, graph))
                .collect::<Result<_, _>>()?,
            methods: value
                .methods
                .iter()
                .map(|(name, definition)| {
                    Ok((
                        name.to_string(),
                        SnapshotCallableDefinition::capture(definition, graph)?,
                    ))
                })
                .collect::<Result<_, SnapshotError>>()?,
            associated_consts: value
                .associated_consts
                .iter()
                .map(|value| {
                    Ok(SnapshotTraitAssociatedConst {
                        name: value.name.to_string(),
                        ty: graph.capture(value.ty)?,
                        doc: value.doc.clone(),
                    })
                })
                .collect::<Result<_, SnapshotError>>()?,
            impl_policy: value.impl_policy,
            spans: value.spans.clone(),
        })
    }

    pub(crate) fn materialize(&self, types: &[Type]) -> Result<Trait, SnapshotError> {
        Ok(Trait {
            name: self.name.as_str().into(),
            doc: self.doc.clone(),
            input_type_names: self
                .input_type_names
                .iter()
                .map(|name| name.as_str().into())
                .collect(),
            output_type_names: self
                .output_type_names
                .iter()
                .map(|name| name.as_str().into())
                .collect(),
            output_effect_names: self
                .output_effect_names
                .iter()
                .map(|name| name.as_str().into())
                .collect(),
            parent_constraints: self
                .parent_constraints
                .iter()
                .map(|value| value.materialize(types))
                .collect::<Result<_, _>>()?,
            constraints: self
                .constraints
                .iter()
                .map(|value| value.materialize(types))
                .collect::<Result<_, _>>()?,
            methods: self
                .methods
                .iter()
                .map(|(name, definition)| {
                    Ok((name.as_str().into(), definition.materialize(types)?))
                })
                .collect::<Result<_, SnapshotError>>()?,
            associated_consts: self
                .associated_consts
                .iter()
                .map(|value| {
                    Ok(TraitAssociatedConst {
                        name: value.name.as_str().into(),
                        ty: types
                            .get(value.ty.0 as usize)
                            .copied()
                            .ok_or(SnapshotError::InvalidTypeReference(value.ty.0))?,
                        doc: value.doc.clone(),
                    })
                })
                .collect::<Result<_, SnapshotError>>()?,
            derivers: Vec::new(),
            impl_policy: self.impl_policy,
            spans: self.spans.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, compiler::snapshot::NativeTypeCatalog};

    #[test]
    fn std_aliases_type_defs_and_source_traits_round_trip() {
        let session = CompilerSession::new();
        let module = session.std_module();
        let catalog = NativeTypeCatalog::std();
        let native_name =
            |native: &crate::types::r#type::BareNativeTypeB| catalog.canonical_name(native);
        let mut graph = SnapshotTypeGraphBuilder::new(&native_name);
        let aliases = module
            .type_aliases
            .type_entries()
            .map(|value| SnapshotTypeAlias::capture(value, &mut graph))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let type_defs = module
            .type_defs
            .as_slice()
            .iter()
            .map(|value| SnapshotTypeDefSlot::capture(value, &mut graph))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let source_traits = module
            .traits
            .iter()
            .filter(|value| value.derivers.is_empty())
            .map(|value| SnapshotTrait::capture(value, &mut graph))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let graph = graph.finish().unwrap();
        let types = graph.materialize(&|name| catalog.resolve(name)).unwrap();

        for (expected, snapshot) in module.type_aliases.type_entries().zip(aliases) {
            let restored = snapshot.materialize(&types).unwrap();
            assert_eq!(restored.name, expected.name);
            assert_eq!(restored.ty, expected.ty);
            assert_eq!(restored.generic_params, expected.generic_params);
        }
        for (expected, snapshot) in module.type_defs.as_slice().iter().zip(type_defs) {
            let restored = snapshot.materialize(&types).unwrap();
            assert_eq!(restored.name(), expected.name());
            assert_eq!(restored.generic_params(), expected.generic_params());
            match (expected, restored) {
                (TypeDefSlot::Resolved(expected), TypeDefSlot::Resolved(restored)) => {
                    assert_eq!(restored.shape, expected.shape);
                    assert_eq!(restored.shape_docs, expected.shape_docs);
                }
                (TypeDefSlot::Reserved(_), TypeDefSlot::Reserved(_)) => {}
                _ => panic!("type definition slot state changed"),
            }
        }
        for (expected, snapshot) in module
            .traits
            .iter()
            .filter(|value| value.derivers.is_empty())
            .zip(source_traits)
        {
            let restored = snapshot.materialize(&types).unwrap();
            assert_eq!(restored.name, expected.name);
            assert_eq!(restored.methods.len(), expected.methods.len());
            assert_eq!(restored.constraints, expected.constraints);
            assert_eq!(restored.parent_constraints, expected.parent_constraints);
        }
    }
}
