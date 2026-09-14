//! Physical bodies are persistent; native pointers and derived evidence catalogs are not.

use std::panic::{AssertUnwindSafe, catch_unwind};

use super::{
    CacheChecksum, NativeTypeCatalog, SnapshotError, SnapshotTypeGraph, SnapshotTypeGraphBuilder,
    mir::SnapshotMirFunction,
};
use crate::{
    compiler::{CompilerSession, MirArtifacts},
    hir::native_functions::{
        NativeFailureConvention, NativeLayout, NativeParameter, NativeResult,
        NativeResultKnowledge, NativeScalar,
    },
    mir::physical::{BackendReadyMirArtifacts, prepare_physical_mir},
    module::{
        FunctionId, LocalFunctionId, Module, ModuleEnv, ModuleId, function::CallableOrigin, id::Id,
    },
    types::r#type::{BareNativeTypeB, TypeKind},
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub(crate) struct CompiledPhysicalMirSnapshot {
    module: ModuleId,
    module_path: String,
    build_fingerprint: String,
    parent_checksum: CacheChecksum,
    types: SnapshotTypeGraph,
    functions: Vec<Option<SnapshotMirFunction>>,
    native: NativeBindings,
}

impl CompiledPhysicalMirSnapshot {
    pub(crate) fn capture(
        artifacts: &BackendReadyMirArtifacts,
        module: &Module,
        parent_checksum: CacheChecksum,
    ) -> Result<Self, SnapshotError> {
        let catalog = NativeTypeCatalog::std();
        let name = |native: &BareNativeTypeB| catalog.canonical_name(native);
        let mut graph = SnapshotTypeGraphBuilder::new(&name);
        let functions = (0..artifacts.entry_count())
            .map(|index| {
                artifacts
                    .get(LocalFunctionId::from_index(index))
                    .map(|body| SnapshotMirFunction::capture(body, &mut graph))
                    .transpose()
            })
            .collect::<Result<_, _>>()?;
        Ok(Self {
            module: artifacts.module(),
            module_path: module.path().to_string(),
            build_fingerprint: env!("FERLIUM_SEMANTIC_BUILD_FINGERPRINT").into(),
            parent_checksum,
            types: graph.finish()?,
            functions,
            native: NativeBindings::capture(artifacts)?,
        })
    }

    pub(crate) fn encode(&self) -> Result<Vec<u8>, postcard::Error> {
        postcard::to_allocvec(self)
    }

    pub(crate) fn decode(bytes: &[u8]) -> Result<Self, postcard::Error> {
        postcard::from_bytes(bytes)
    }

    pub(crate) fn restore(
        &self,
        parent_checksum: &CacheChecksum,
        optimized: &MirArtifacts,
        module: &Module,
        session: &CompilerSession,
    ) -> Result<BackendReadyMirArtifacts, SnapshotError> {
        // The existing build fingerprint includes target, rustc, features and compiler sources.
        // This is a same-build cache, not a portable Rust ABI or cross-target artifact format.
        if self.module != module.module_id()
            || self.module_path != module.path().to_string()
            || self.build_fingerprint != env!("FERLIUM_SEMANTIC_BUILD_FINGERPRINT")
            || &self.parent_checksum != parent_checksum
        {
            return Err(SnapshotError::StaleSnapshot);
        }
        if self.functions.len() < optimized.entry_count() {
            return Err(SnapshotError::InvalidMir(
                "physical snapshot omits entry slots".into(),
            ));
        }
        for (index, body) in self.functions.iter().enumerate() {
            let id = LocalFunctionId::from_index(index);
            let requires_body = index >= optimized.entry_count()
                || optimized.get(id).is_some()
                || module.get_function_by_id(id).is_some_and(|function| {
                    matches!(
                        function.origin,
                        CallableOrigin::StructuralFieldAddressor { .. }
                            | CallableOrigin::BufferPrimitive(_)
                    )
                });
            if requires_body && body.is_none() {
                return Err(SnapshotError::InvalidMir(
                    "physical snapshot omits a required body".into(),
                ));
            }
        }
        let catalog = NativeTypeCatalog::std();
        let types = self.types.materialize(&|name| catalog.resolve(name))?;
        let functions = self
            .functions
            .iter()
            .map(|body| {
                body.as_ref()
                    .map(|body| body.materialize(&types))
                    .transpose()
            })
            .collect::<Result<_, _>>()?;
        // As with semantic snapshot verification, malformed compiler-owned data is a cache miss
        // in unwind builds. Do not replace the process-wide panic hook.
        let artifacts = catch_unwind(AssertUnwindSafe(|| {
            prepare_physical_mir(
                functions,
                optimized,
                ModuleEnv::new(module, session.raw_modules()),
            )
        }))
        .map_err(|_| SnapshotError::InvalidMir("physical MIR verification failed".into()))?
        .map_err(|error| SnapshotError::InvalidMir(error.to_string()))?;
        if self.native != NativeBindings::capture(&artifacts)? {
            return Err(SnapshotError::InvalidMir(
                "physical native layout/ABI contract changed".into(),
            ));
        }
        Ok(artifacts)
    }
}

/// Canonical names replace Rust TypeIds; code addresses are deliberately absent. The parent
/// snapshot pins the source signatures, including optional-result types, and lifecycle identities.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct NativeBindings {
    layouts: Vec<(Layout, Option<(FunctionId, FunctionId)>)>,
    entries: Vec<(FunctionId, Signature)>,
}

impl NativeBindings {
    fn capture(artifacts: &BackendReadyMirArtifacts) -> Result<Self, SnapshotError> {
        let catalog = NativeTypeCatalog::std();
        let mut layouts = artifacts
            .native_layouts()
            .map(|(layout, lifecycle)| Ok((Layout::capture(layout, &catalog)?, lifecycle)))
            .collect::<Result<Vec<_>, SnapshotError>>()?;
        layouts.sort_by(|a, b| a.0.name.cmp(&b.0.name));
        let mut entries = artifacts
            .native_entries()
            .map(|(id, entry)| {
                let signature = entry.signature();
                let layout = |value| Layout::capture(value, &catalog);
                let parameters = signature
                    .parameters
                    .iter()
                    .map(|parameter| {
                        Ok(match *parameter {
                            NativeParameter::Scalar(value, scalar) => {
                                Parameter::Scalar(layout(value)?, scalar)
                            }
                            NativeParameter::Shared(value) => Parameter::Shared(layout(value)?),
                            NativeParameter::Mutable(value) => Parameter::Mutable(layout(value)?),
                            NativeParameter::Consuming(value) => {
                                Parameter::Consuming(layout(value)?)
                            }
                        })
                    })
                    .collect::<Result<_, SnapshotError>>()?;
                let result = match signature.result {
                    NativeResult::Unit => ResultTransport::Unit,
                    NativeResult::Never => ResultTransport::Never,
                    NativeResult::Scalar(value, scalar) => {
                        ResultTransport::Scalar(layout(value)?, scalar)
                    }
                    NativeResult::Output(value) => ResultTransport::Output(layout(value)?),
                    NativeResult::Optional { payload, .. } => {
                        ResultTransport::Optional(layout(payload)?)
                    }
                    NativeResult::Addressor {
                        pointee,
                        root,
                        mutable,
                    } => ResultTransport::Addressor {
                        pointee: layout(pointee)?,
                        root,
                        mutable,
                    },
                };
                Ok((
                    id,
                    Signature {
                        failure: signature.failure,
                        parameters,
                        result,
                        knowledge: entry.result_knowledge(),
                    },
                ))
            })
            .collect::<Result<Vec<_>, SnapshotError>>()?;
        entries.sort_by_key(|(id, _)| (id.module.as_index(), id.function.as_index()));
        Ok(Self { layouts, entries })
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct Layout {
    name: String,
    size: u64,
    align: u64,
}

impl Layout {
    fn capture(layout: NativeLayout, catalog: &NativeTypeCatalog) -> Result<Self, SnapshotError> {
        let TypeKind::Native(native) = &*layout.ty.data() else {
            return Err(SnapshotError::InvalidMir(
                "native layout has a non-native type".into(),
            ));
        };
        if !native.arguments.is_empty() || native.bare_ty.value_type_id() != Some(layout.rust_type)
        {
            return Err(SnapshotError::InvalidMir(
                "native layout differs from registered Rust type".into(),
            ));
        }
        Ok(Self {
            name: catalog.require_name(&native.bare_ty)?,
            size: layout.size as u64,
            align: layout.align as u64,
        })
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
struct Signature {
    failure: NativeFailureConvention,
    parameters: Vec<Parameter>,
    result: ResultTransport,
    knowledge: NativeResultKnowledge,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
enum Parameter {
    Scalar(Layout, NativeScalar),
    Shared(Layout),
    Mutable(Layout),
    Consuming(Layout),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
enum ResultTransport {
    Unit,
    Never,
    Scalar(Layout, NativeScalar),
    Output(Layout),
    Optional(Layout),
    Addressor {
        pointee: Layout,
        root: u32,
        mutable: bool,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        compiler::{MirOptimization, artifacts::ensure_optimized_mir_artifacts},
        mir::physical::lower_physical_mir,
        std::{STD_MODULE_ID, buffer::expected_primitives},
    };

    #[test]
    fn physical_snapshot_round_trip_and_compatibility() {
        let session = CompilerSession::new();
        ensure_optimized_mir_artifacts(&session, STD_MODULE_ID);
        let module = session.std_module();
        let optimized = session
            .expect_module_entry(STD_MODULE_ID)
            .artifacts()
            .mir(MirOptimization::Enabled)
            .unwrap();
        let physical = lower_physical_mir(
            STD_MODULE_ID,
            optimized,
            ModuleEnv::new(module, session.raw_modules()),
            session.known_callees(),
        )
        .unwrap();
        let snapshot = CompiledPhysicalMirSnapshot::capture(&physical, module, [7; 32]).unwrap();
        let bytes = snapshot.encode().unwrap();
        let decoded = CompiledPhysicalMirSnapshot::decode(&bytes).unwrap();
        let restore = |snapshot: &CompiledPhysicalMirSnapshot| {
            snapshot.restore(&[7; 32], optimized, module, &session)
        };
        let restored = restore(&decoded).unwrap();
        restored
            .validate_native_runtime(ModuleEnv::new(module, session.raw_modules()))
            .unwrap();
        assert_eq!(restored.dictionaries(), physical.dictionaries());
        assert_eq!(restored.dictionary_imports(), physical.dictionary_imports());
        assert_eq!(restored.subscripts(), physical.subscripts());
        assert_eq!(restored.subscript_imports(), physical.subscript_imports());
        assert_eq!(
            CompiledPhysicalMirSnapshot::capture(&restored, module, [7; 32])
                .unwrap()
                .encode()
                .unwrap(),
            bytes
        );

        for mutation in 0..4 {
            let mut stale = decoded.clone();
            match mutation {
                0 => stale.parent_checksum[0] ^= 1,
                1 => stale.build_fingerprint.push_str("-stale"),
                2 => stale.module = ModuleId::new(42),
                _ => stale.module_path.push_str("-other"),
            }
            assert!(matches!(restore(&stale), Err(SnapshotError::StaleSnapshot)));
        }
        let mut stale = decoded.clone();
        stale.native.layouts[0].0.size += 1;
        assert!(
            matches!(restore(&stale), Err(SnapshotError::InvalidMir(message)) if message.contains("layout/ABI"))
        );
        let mut stale = decoded.clone();
        stale.native.entries[0].1.failure = match stale.native.entries[0].1.failure {
            NativeFailureConvention::Infallible => NativeFailureConvention::StatusWithState,
            NativeFailureConvention::StatusWithState => NativeFailureConvention::Infallible,
        };
        assert!(
            matches!(restore(&stale), Err(SnapshotError::InvalidMir(message)) if message.contains("layout/ABI"))
        );
        for (function, primitive) in expected_primitives(module) {
            let mut malformed = decoded.clone();
            malformed.functions[function.as_index()] = None;
            assert!(
                matches!(restore(&malformed), Err(SnapshotError::InvalidMir(message))
                    if message.contains("required body")),
                "a snapshot must retain the body of Buffer::{primitive:?}"
            );
        }
        let mut malformed = decoded;
        malformed.functions.clear();
        assert!(matches!(
            restore(&malformed),
            Err(SnapshotError::InvalidMir(_))
        ));
    }
}
