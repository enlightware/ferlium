use crate::{
    module::{
        BlanketTraitImplSubKey, ConcreteTraitImplKey, LocalFunctionId, LocalImplId, ModuleId,
        TraitId, TraitImpl, TraitImpls,
    },
    types::{
        effects::{EffType, Effect},
        r#type::Type,
    },
};

use super::{
    SnapshotError, SnapshotLiteral, SnapshotTypeGraphBuilder, SnapshotTypeId,
    semantic::SnapshotConstraint,
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotConcreteKey {
    trait_id: TraitId,
    input_tys: Vec<SnapshotTypeId>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotBlanketSubKey {
    input_tys: Vec<SnapshotTypeId>,
    ty_var_count: u32,
    eff_var_count: u32,
    constraints: Vec<SnapshotConstraint>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct SnapshotTraitImpl {
    output_tys: Vec<SnapshotTypeId>,
    output_effs: Vec<Vec<Effect>>,
    methods: Vec<LocalFunctionId>,
    associated_const_values: Vec<SnapshotLiteral>,
    associated_const_getters: Vec<LocalFunctionId>,
    dictionary_ty: SnapshotTypeId,
    public: bool,
    source_span: Option<crate::Location>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotTraitImpls {
    module_id: ModuleId,
    concrete: Vec<(SnapshotConcreteKey, LocalImplId)>,
    blanket: Vec<(TraitId, SnapshotBlanketSubKey, LocalImplId)>,
    generated_value: Vec<(Vec<SnapshotTypeId>, LocalImplId)>,
    unconstrained_applications: Vec<(SnapshotConcreteKey, LocalImplId)>,
    data: Vec<SnapshotTraitImpl>,
}

fn capture_types(
    values: &[Type],
    graph: &mut SnapshotTypeGraphBuilder<'_>,
) -> Result<Vec<SnapshotTypeId>, SnapshotError> {
    values.iter().map(|value| graph.capture(*value)).collect()
}

fn live_type(types: &[Type], value: SnapshotTypeId) -> Result<Type, SnapshotError> {
    types
        .get(value.0 as usize)
        .copied()
        .ok_or(SnapshotError::InvalidTypeReference(value.0))
}

fn live_types(values: &[SnapshotTypeId], types: &[Type]) -> Result<Vec<Type>, SnapshotError> {
    values
        .iter()
        .map(|value| live_type(types, *value))
        .collect()
}

fn capture_effects(value: &EffType) -> Vec<Effect> {
    value.iter().collect()
}

fn live_effects(value: &[Effect]) -> EffType {
    value.iter().copied().collect()
}

impl SnapshotConcreteKey {
    fn capture(
        value: &ConcreteTraitImplKey,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            trait_id: value.trait_id,
            input_tys: capture_types(&value.input_tys, graph)?,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<ConcreteTraitImplKey, SnapshotError> {
        Ok(ConcreteTraitImplKey::new(
            self.trait_id,
            live_types(&self.input_tys, types)?,
        ))
    }
}

impl SnapshotBlanketSubKey {
    fn capture(
        value: &BlanketTraitImplSubKey,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            input_tys: capture_types(&value.input_tys, graph)?,
            ty_var_count: value.ty_var_count,
            eff_var_count: value.eff_var_count,
            constraints: value
                .constraints
                .iter()
                .map(|value| SnapshotConstraint::capture(value, graph))
                .collect::<Result<_, _>>()?,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<BlanketTraitImplSubKey, SnapshotError> {
        Ok(BlanketTraitImplSubKey {
            input_tys: live_types(&self.input_tys, types)?,
            ty_var_count: self.ty_var_count,
            eff_var_count: self.eff_var_count,
            constraints: self
                .constraints
                .iter()
                .map(|value| value.materialize(types))
                .collect::<Result<_, _>>()?,
        })
    }
}

impl SnapshotTraitImpl {
    fn capture(
        value: &TraitImpl,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        Ok(Self {
            output_tys: capture_types(&value.output_tys, graph)?,
            output_effs: value.output_effs.iter().map(capture_effects).collect(),
            methods: value.methods.clone(),
            associated_const_values: value
                .associated_const_values
                .iter()
                .map(SnapshotLiteral::capture)
                .collect::<Result<_, _>>()?,
            associated_const_getters: value.associated_const_getters.clone(),
            dictionary_ty: graph.capture(value.dictionary_ty)?,
            public: value.public,
            source_span: value.source_span,
        })
    }

    fn materialize(&self, types: &[Type]) -> Result<TraitImpl, SnapshotError> {
        let associated_const_values = self
            .associated_const_values
            .iter()
            .map(SnapshotLiteral::materialize)
            .collect::<Result<Vec<_>, _>>()?;
        let dictionary_value =
            crate::module::build_dictionary_value(&self.methods, &self.associated_const_getters);
        Ok(TraitImpl {
            output_tys: live_types(&self.output_tys, types)?,
            output_effs: self
                .output_effs
                .iter()
                .map(|value| live_effects(value))
                .collect(),
            methods: self.methods.clone(),
            associated_const_values,
            associated_const_getters: self.associated_const_getters.clone(),
            dictionary_value,
            dictionary_ty: live_type(types, self.dictionary_ty)?,
            public: self.public,
            source_span: self.source_span,
        })
    }
}

impl SnapshotTraitImpls {
    pub(crate) fn capture(
        value: &TraitImpls,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        let mut concrete = value
            .concrete_key_to_id
            .iter()
            .map(|(key, id)| Ok((SnapshotConcreteKey::capture(key, graph)?, *id)))
            .collect::<Result<Vec<_>, SnapshotError>>()?;
        concrete.sort_by_key(|(_, id)| id.as_u32());

        let mut blanket = value
            .blanket_key_to_id
            .iter()
            .flat_map(|(trait_id, implementations)| {
                implementations
                    .iter()
                    .map(move |(key, id)| (*trait_id, key, *id))
            })
            .map(|(trait_id, key, id)| {
                Ok((trait_id, SnapshotBlanketSubKey::capture(key, graph)?, id))
            })
            .collect::<Result<Vec<_>, SnapshotError>>()?;
        blanket.sort_by_key(|(_, _, id)| id.as_u32());

        let mut generated_value = value
            .generated_value_key_to_id
            .iter()
            .map(|(key, id)| Ok((capture_types(key, graph)?, *id)))
            .collect::<Result<Vec<_>, SnapshotError>>()?;
        generated_value.sort_by_key(|(_, id)| id.as_u32());

        let mut unconstrained_applications = value
            .unconstrained_application_key_to_id
            .iter()
            .map(|(key, id)| Ok((SnapshotConcreteKey::capture(key, graph)?, *id)))
            .collect::<Result<Vec<_>, SnapshotError>>()?;
        unconstrained_applications.sort_by_key(|(_, id)| id.as_u32());

        Ok(Self {
            module_id: value.module_id,
            concrete,
            blanket,
            generated_value,
            unconstrained_applications,
            data: value
                .data
                .iter()
                .map(|value| SnapshotTraitImpl::capture(value, graph))
                .collect::<Result<_, _>>()?,
        })
    }

    pub(crate) fn materialize(&self, types: &[Type]) -> Result<TraitImpls, SnapshotError> {
        let mut value = TraitImpls::new(self.module_id);
        value.concrete_key_to_id = self
            .concrete
            .iter()
            .map(|(key, id)| Ok((key.materialize(types)?, *id)))
            .collect::<Result<_, SnapshotError>>()?;
        for (trait_id, key, id) in &self.blanket {
            value
                .blanket_key_to_id
                .entry(*trait_id)
                .or_default()
                .insert(key.materialize(types)?, *id);
        }
        value.generated_value_key_to_id = self
            .generated_value
            .iter()
            .map(|(key, id)| Ok((live_types(key, types)?, *id)))
            .collect::<Result<_, SnapshotError>>()?;
        value.unconstrained_application_key_to_id = self
            .unconstrained_applications
            .iter()
            .map(|(key, id)| Ok((key.materialize(types)?, *id)))
            .collect::<Result<_, SnapshotError>>()?;
        value.data = self
            .data
            .iter()
            .map(|value| value.materialize(types))
            .collect::<Result<_, _>>()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, compiler::snapshot::NativeTypeCatalog};

    #[test]
    fn complete_std_trait_impl_tables_round_trip() {
        let session = CompilerSession::new();
        let catalog = NativeTypeCatalog::std();
        let native_name =
            |native: &crate::types::r#type::BareNativeTypeB| catalog.canonical_name(native);
        let mut graph = SnapshotTypeGraphBuilder::new(&native_name);
        let snapshot =
            SnapshotTraitImpls::capture(&session.std_module().impls, &mut graph).unwrap();
        let graph = graph.finish().unwrap();
        let types = graph.materialize(&|name| catalog.resolve(name)).unwrap();
        let restored = snapshot.materialize(&types).unwrap();

        assert_eq!(restored.data.len(), session.std_module().impls.data.len());
        assert_eq!(
            restored.concrete_key_to_id,
            session.std_module().impls.concrete_key_to_id
        );
        assert_eq!(
            restored.blanket_key_to_id,
            session.std_module().impls.blanket_key_to_id
        );
        for (expected, actual) in session.std_module().impls.data.iter().zip(restored.data) {
            assert_eq!(actual.output_tys, expected.output_tys);
            assert_eq!(actual.output_effs, expected.output_effs);
            assert_eq!(actual.methods, expected.methods);
            assert_eq!(
                actual.associated_const_values,
                expected.associated_const_values
            );
            assert_eq!(actual.dictionary_ty, expected.dictionary_ty);
        }
    }
}
