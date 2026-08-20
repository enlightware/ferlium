use crate::{
    SourceTable,
    module::{Module, function::CallableOrigin},
    std::{self as ferlium_std, StdSourceLoader},
};

use super::{
    ModuleCheckpointShape, NativeTypeCatalog, SnapshotError, SnapshotModuleCheckpoint,
    SnapshotSourceTable, SnapshotTypeGraph, SnapshotTypeGraphBuilder, StdSnapshot,
    StdSnapshotHeader,
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub(crate) struct StdSnapshotPayload {
    sources: SnapshotSourceTable,
    types: SnapshotTypeGraph,
    checkpoints: Vec<SnapshotModuleCheckpoint>,
}

pub(crate) type CompiledStdSnapshot = StdSnapshot<StdSnapshotPayload>;

pub(crate) struct StdSnapshotCaptureError {
    error: SnapshotError,
    sources: SourceTable,
    module: Module,
}

impl StdSnapshotCaptureError {
    pub(crate) fn error(&self) -> &SnapshotError {
        &self.error
    }

    pub(crate) fn into_compiled_std(self: Box<Self>) -> (SourceTable, Module) {
        let Self {
            sources, module, ..
        } = *self;
        (sources, module)
    }
}

impl std::fmt::Debug for StdSnapshotCaptureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("StdSnapshotCaptureError")
            .field(&self.error)
            .finish()
    }
}

struct RecordingLoader<'a, 'g> {
    source_table: &'a mut SourceTable,
    graph: &'a mut SnapshotTypeGraphBuilder<'g>,
    checkpoints: Vec<SnapshotModuleCheckpoint>,
    error: Option<SnapshotError>,
}

impl RecordingLoader<'_, '_> {
    fn record(
        &mut self,
        module: Module,
        compile: impl FnOnce(Module, &mut SourceTable) -> Module,
    ) -> Module {
        if self.error.is_some() {
            return module;
        }
        let before = ModuleCheckpointShape::of(&module);
        let module = compile(module, self.source_table);
        match SnapshotModuleCheckpoint::capture(before, &module, self.graph) {
            Ok(checkpoint) => self.checkpoints.push(checkpoint),
            Err(error) => self.error = Some(error),
        }
        module
    }
}

impl StdSourceLoader for RecordingLoader<'_, '_> {
    fn declare_traits(&mut self, module: Module) -> Module {
        self.record(module, |module, sources| {
            ferlium_std::prelude::declare_traits(module, sources, ferlium_std::STD_MODULE_ID)
        })
    }

    fn add_core(&mut self, module: Module) -> Module {
        self.record(module, |module, sources| {
            ferlium_std::prelude::add_ferlium_core(module, sources, ferlium_std::STD_MODULE_ID)
        })
    }

    fn add_serialization(&mut self, module: Module) -> Module {
        self.record(module, |module, sources| {
            ferlium_std::prelude::add_ferlium_serialization_prelude(
                module,
                sources,
                ferlium_std::STD_MODULE_ID,
            )
        })
    }
}

struct RestoringLoader<'a> {
    checkpoints: std::slice::Iter<'a, SnapshotModuleCheckpoint>,
    types: &'a [crate::types::r#type::Type],
    error: Option<SnapshotError>,
}

impl RestoringLoader<'_> {
    fn restore(&mut self, mut module: Module) -> Module {
        if self.error.is_some() {
            return module;
        }
        let Some(checkpoint) = self.checkpoints.next() else {
            self.error = Some(SnapshotError::CheckpointShapeMismatch(
                "std builder requested more source checkpoints than the snapshot contains"
                    .to_owned(),
            ));
            return module;
        };
        if let Err(error) = checkpoint.apply(&mut module, self.types) {
            self.error = Some(error);
        }
        module
    }
}

impl StdSourceLoader for RestoringLoader<'_> {
    fn declare_traits(&mut self, module: Module) -> Module {
        self.restore(module)
    }

    fn add_core(&mut self, module: Module) -> Module {
        self.restore(module)
    }

    fn add_serialization(&mut self, module: Module) -> Module {
        self.restore(module)
    }
}

impl CompiledStdSnapshot {
    pub(crate) fn capture() -> Result<(Self, Module), Box<StdSnapshotCaptureError>> {
        let native_types = NativeTypeCatalog::std();
        let native_name =
            |native: &crate::types::r#type::BareNativeTypeB| native_types.canonical_name(native);
        let mut graph = SnapshotTypeGraphBuilder::new(&native_name);
        let mut source_table = SourceTable::default();
        let (module, checkpoints, error) = {
            let mut loader = RecordingLoader {
                source_table: &mut source_table,
                graph: &mut graph,
                checkpoints: Vec::new(),
                error: None,
            };
            let module = ferlium_std::build_std(&mut loader);
            (module, loader.checkpoints, loader.error)
        };
        if let Some(error) = error {
            return Err(Box::new(StdSnapshotCaptureError {
                error,
                sources: source_table,
                module,
            }));
        }
        if checkpoints.len() != 3 {
            return Err(Box::new(StdSnapshotCaptureError {
                error: SnapshotError::CheckpointShapeMismatch(format!(
                    "std build produced {} source checkpoints instead of 3",
                    checkpoints.len()
                )),
                sources: source_table,
                module,
            }));
        }
        let native_offer = native_offer(&module, &native_types);
        let types = match graph.finish() {
            Ok(types) => types,
            Err(error) => {
                return Err(Box::new(StdSnapshotCaptureError {
                    error,
                    sources: source_table,
                    module,
                }));
            }
        };
        Ok((
            StdSnapshot {
                header: StdSnapshotHeader::current(native_offer),
                payload: StdSnapshotPayload {
                    sources: SnapshotSourceTable::capture(&source_table),
                    types,
                    checkpoints,
                },
            },
            module,
        ))
    }

    pub(crate) fn restore(&self) -> Result<(SourceTable, Module), SnapshotError> {
        let native_types = NativeTypeCatalog::std();
        let types = self
            .payload
            .types
            .materialize(&|name| native_types.resolve(name))?;
        let mut loader = RestoringLoader {
            checkpoints: self.payload.checkpoints.iter(),
            types: &types,
            error: None,
        };
        let module = ferlium_std::build_std(&mut loader);
        if let Some(error) = loader.error {
            return Err(error);
        }
        if loader.checkpoints.next().is_some() {
            return Err(SnapshotError::CheckpointShapeMismatch(
                "snapshot contains more source checkpoints than the std builder requested"
                    .to_owned(),
            ));
        }
        if !self
            .header
            .matches_current(&native_offer(&module, &native_types))
        {
            return Err(SnapshotError::StaleSnapshot);
        }
        Ok((self.payload.sources.materialize(), module))
    }

    #[cfg(feature = "std-snapshot")]
    pub(crate) fn encode(&self) -> Result<Vec<u8>, postcard::Error> {
        postcard::to_allocvec(self)
    }

    #[cfg(feature = "std-snapshot")]
    pub(crate) fn decode(bytes: &[u8]) -> Result<Self, postcard::Error> {
        postcard::from_bytes(bytes)
    }

    pub(crate) fn captured_sources(&self) -> SourceTable {
        self.payload.sources.materialize()
    }
}

fn native_offer(module: &Module, native_types: &NativeTypeCatalog) -> String {
    let mut offer = module
        .functions
        .iter()
        .filter_map(|function| match function.origin {
            CallableOrigin::Native {
                canonical_name: Some(name),
            } => Some(format!("callable:{name}")),
            _ => None,
        })
        .collect::<Vec<_>>();
    offer.extend(
        native_types
            .canonical_names()
            .map(|name| format!("type:{name}")),
    );
    offer.sort();
    offer.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn std_rebuilds_from_three_source_checkpoints_without_recompiling_source() {
        let (snapshot, expected) = CompiledStdSnapshot::capture().unwrap();
        let (sources, restored) = snapshot.restore().unwrap();

        assert_eq!(sources.len(), snapshot.payload.sources.sources.len());
        assert_eq!(restored.functions.len(), expected.functions.len());
        assert_eq!(restored.subscripts.len(), expected.subscripts.len());
        assert_eq!(
            format!("{:?}", restored.def_table),
            format!("{:?}", expected.def_table),
            "definition table differs after restoration"
        );
        assert_eq!(
            format!("{:?}", restored.impls),
            format!("{:?}", expected.impls),
            "trait implementation tables differ after restoration"
        );
        for (index, (restored, expected)) in restored
            .functions
            .iter()
            .zip(expected.functions.iter())
            .enumerate()
        {
            assert_eq!(
                format!("{:?}", restored.definition),
                format!("{:?}", expected.definition),
                "function definition {index} differs after restoration"
            );
            assert_eq!(
                format!("{:?}", restored.spans),
                format!("{:?}", expected.spans),
                "function spans {index} differ after restoration"
            );
        }
        for (index, (restored, expected)) in restored
            .traits
            .iter()
            .zip(expected.traits.iter())
            .enumerate()
        {
            assert_eq!(
                format!("{restored:?}"),
                format!("{expected:?}"),
                "trait {index} differs after restoration"
            );
        }
        assert_eq!(restored.traits.len(), expected.traits.len());
        assert_eq!(
            restored.type_defs.as_slice().len(),
            expected.type_defs.as_slice().len()
        );
        assert_eq!(restored.impls.data.len(), expected.impls.data.len());
        assert_eq!(restored.hir_arena.len(), expected.hir_arena.len());
        let native_types = NativeTypeCatalog::std();
        assert_eq!(
            native_offer(&restored, &native_types),
            native_offer(&expected, &native_types)
        );

        for (expected, actual) in expected.functions.iter().zip(&restored.functions) {
            assert_eq!(actual.origin, expected.origin);
            assert_eq!(
                actual.definition.signature(),
                expected.definition.signature()
            );
            assert_eq!(actual.parameter_passing, expected.parameter_passing);
        }
        assert_eq!(
            restored.impls.concrete_key_to_id,
            expected.impls.concrete_key_to_id
        );
        assert_eq!(
            restored.impls.blanket_key_to_id,
            expected.impls.blanket_key_to_id
        );
    }

    #[cfg(feature = "std-snapshot")]
    #[test]
    fn encoded_std_snapshot_round_trips() {
        let (snapshot, expected) = CompiledStdSnapshot::capture().unwrap();
        let bytes = snapshot.encode().unwrap();
        let decoded = CompiledStdSnapshot::decode(&bytes).unwrap();
        let (_, restored) = decoded.restore().unwrap();

        assert!(!bytes.is_empty());
        assert_eq!(restored.functions.len(), expected.functions.len());
        assert_eq!(restored.hir_arena.len(), expected.hir_arena.len());
        assert_eq!(restored.impls.data.len(), expected.impls.data.len());
    }
}
