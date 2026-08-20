use crate::{
    FxHashSet,
    module::{Def, Module, ModuleId, TypeDefSlots, id::Id},
    types::r#type::Type,
};

use super::{
    NativeCallableCatalog, SnapshotError, SnapshotHirArena, SnapshotModuleFunction,
    SnapshotProjection, SnapshotSubscript, SnapshotTrait, SnapshotTraitImpls, SnapshotTypeAlias,
    SnapshotTypeDefSlot, SnapshotTypeGraphBuilder,
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ModuleCheckpointShape {
    functions: usize,
    subscripts: usize,
    type_aliases: usize,
    type_defs: usize,
    traits: usize,
    definitions: usize,
    hir_nodes: usize,
}

impl ModuleCheckpointShape {
    pub(crate) fn of(module: &Module) -> Self {
        Self {
            functions: module.functions.len(),
            subscripts: module.subscripts.len(),
            type_aliases: module.type_aliases.type_len(),
            type_defs: module.type_defs.as_slice().len(),
            traits: module.traits.len(),
            definitions: module.def_table.next_id().as_index(),
            hir_nodes: module.hir_arena.len(),
        }
    }
}

/// Semantic additions produced by one embedded Ferlium-source compilation checkpoint.
///
/// Native registration runs between these deltas. Append-only tables retain the native objects;
/// derived/index tables are captured as complete portable replacements so no incremental lookup
/// invariant is left implicit.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub(crate) struct SnapshotModuleCheckpoint {
    before: ModuleCheckpointShape,
    after: ModuleCheckpointShape,
    functions: Vec<SnapshotModuleFunction>,
    subscripts: Vec<SnapshotSubscript>,
    type_aliases: Vec<SnapshotTypeAlias>,
    type_defs: Vec<SnapshotTypeDefSlot>,
    traits: Vec<SnapshotTrait>,
    definitions: Vec<(Def, Option<String>)>,
    projections: Vec<SnapshotProjection>,
    impls: SnapshotTraitImpls,
    hir: SnapshotHirArena,
    deps: Vec<ModuleId>,
}

impl SnapshotModuleCheckpoint {
    pub(crate) fn capture(
        before: ModuleCheckpointShape,
        module: &Module,
        graph: &mut SnapshotTypeGraphBuilder<'_>,
    ) -> Result<Self, SnapshotError> {
        let after = ModuleCheckpointShape::of(module);
        validate_monotonic(before, after)?;

        let functions = module.functions[before.functions..]
            .iter()
            .map(|value| {
                if let crate::module::function::CallableOrigin::Native { canonical_name } =
                    value.origin
                {
                    return Err(SnapshotError::NativeCallableInSourceCheckpoint(
                        canonical_name
                            .map(|name| name.to_string())
                            .unwrap_or_else(|| "<unnamed>".to_owned()),
                    ));
                }
                SnapshotModuleFunction::capture(value, graph)
            })
            .collect::<Result<_, _>>()?;
        let subscripts = module.subscripts[before.subscripts..]
            .iter()
            .map(|value| SnapshotSubscript::capture(value, graph))
            .collect::<Result<_, _>>()?;
        let type_aliases = module
            .type_aliases
            .type_entries()
            .skip(before.type_aliases)
            .map(|value| SnapshotTypeAlias::capture(value, graph))
            .collect::<Result<_, _>>()?;
        // Type definitions can be mutated by later native Value registrations, so each checkpoint
        // carries their complete current portable state.
        let type_defs = module
            .type_defs
            .as_slice()
            .iter()
            .map(|value| SnapshotTypeDefSlot::capture(value, graph))
            .collect::<Result<_, _>>()?;
        let traits = module.traits[before.traits..]
            .iter()
            .map(|value| SnapshotTrait::capture(value, graph))
            .collect::<Result<_, _>>()?;
        let definitions = module
            .def_table
            .iter()
            .skip(before.definitions)
            .map(|(def, name)| (*def, name.map(|name| name.to_string())))
            .collect();
        let mut projections = module
            .projection_subscripts
            .iter()
            .map(|(key, entry)| SnapshotProjection::capture(*key, *entry, graph))
            .collect::<Result<Vec<_>, _>>()?;
        projections.sort_by(SnapshotProjection::stable_cmp);

        Ok(Self {
            before,
            after,
            functions,
            subscripts,
            type_aliases,
            type_defs,
            traits,
            definitions,
            projections,
            impls: SnapshotTraitImpls::capture(&module.impls, graph)?,
            hir: SnapshotHirArena::capture_from(&module.hir_arena, before.hir_nodes, graph)?,
            deps: {
                let mut deps = module.deps.iter().copied().collect::<Vec<_>>();
                deps.sort_by_key(|id| id.as_u32());
                deps
            },
        })
    }

    pub(crate) fn apply(&self, module: &mut Module, types: &[Type]) -> Result<(), SnapshotError> {
        let actual = ModuleCheckpointShape::of(module);
        if actual != self.before {
            return Err(SnapshotError::CheckpointShapeMismatch(format!(
                "expected {:?}, got {:?}",
                self.before, actual
            )));
        }

        self.hir.append_to(
            &mut module.hir_arena,
            self.before.hir_nodes,
            self.after.hir_nodes,
            types,
        )?;
        let empty_native_catalog = NativeCallableCatalog::default();
        module.functions.extend(
            self.functions
                .iter()
                .map(|value| value.materialize(types, &empty_native_catalog, self.after.hir_nodes))
                .collect::<Result<Vec<_>, _>>()?,
        );
        module.subscripts.extend(
            self.subscripts
                .iter()
                .map(|value| value.materialize(types))
                .collect::<Result<Vec<_>, _>>()?,
        );
        for value in &self.type_aliases {
            let value = value.materialize(types)?;
            module.type_aliases.set(
                value.name,
                value.generic_params,
                value.ty_var_count,
                value.ty,
                value.doc,
            );
        }
        let mut type_defs = TypeDefSlots::default();
        for value in &self.type_defs {
            type_defs.push(value.materialize(types)?);
        }
        module.type_defs = type_defs;
        module.traits.extend(
            self.traits
                .iter()
                .map(|value| value.materialize(types))
                .collect::<Result<Vec<_>, _>>()?,
        );
        for (def, name) in &self.definitions {
            match name {
                Some(name) => {
                    module.def_table.insert(name.as_str().into(), *def);
                }
                None => {
                    module.def_table.insert_anonymous(*def);
                }
            }
        }
        module.projection_subscripts = self
            .projections
            .iter()
            .map(|value| value.materialize(types))
            .collect::<Result<_, _>>()?;
        module.impls = self.impls.materialize(types)?;
        module.deps = self.deps.iter().copied().collect::<FxHashSet<_>>();

        let actual = ModuleCheckpointShape::of(module);
        if actual != self.after {
            return Err(SnapshotError::CheckpointShapeMismatch(format!(
                "checkpoint produced {:?}, expected {:?}",
                actual, self.after
            )));
        }
        Ok(())
    }
}

fn validate_monotonic(
    before: ModuleCheckpointShape,
    after: ModuleCheckpointShape,
) -> Result<(), SnapshotError> {
    if after.functions < before.functions
        || after.subscripts < before.subscripts
        || after.type_aliases < before.type_aliases
        || after.type_defs < before.type_defs
        || after.traits < before.traits
        || after.definitions < before.definitions
        || after.hir_nodes < before.hir_nodes
    {
        Err(SnapshotError::CheckpointShapeMismatch(format!(
            "non-monotonic checkpoint {before:?} -> {after:?}"
        )))
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession,
        module::{Path, function::CallableOrigin},
    };

    #[test]
    fn source_checkpoint_rejects_native_callable_bodies() {
        let session = CompilerSession::new();
        let native = session
            .std_module()
            .functions
            .iter()
            .find(|function| matches!(function.origin, CallableOrigin::Native { .. }))
            .unwrap()
            .clone();
        let mut module = Module::new(ModuleId::new(97), Path::single_str("snapshot-test"));
        let before = ModuleCheckpointShape::of(&module);
        module.functions.push(native);
        let native_types = super::super::NativeTypeCatalog::std();
        let native_name =
            |native: &crate::types::r#type::BareNativeTypeB| native_types.canonical_name(native);
        let mut graph = SnapshotTypeGraphBuilder::new(&native_name);

        assert!(matches!(
            SnapshotModuleCheckpoint::capture(before, &module, &mut graph),
            Err(SnapshotError::NativeCallableInSourceCheckpoint(_))
        ));
    }
}
