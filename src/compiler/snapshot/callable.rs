// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use la_arena::{Idx, RawIdx};

use super::SnapshotError;
use crate::{
    containers::b,
    hir::{
        self, Elaborated,
        function::{Function, ScriptFunction, StructuralFieldAddressor},
    },
    module::{ModuleFunction, ProjectionIndex, function::CallableOrigin},
    primitive::BufferPrimitive,
};

/// Process-local implementations indexed by their stable canonical module names.
///
/// Source checkpoints intentionally materialize against an empty catalog: native registrations
/// are replayed around them by the std builder. The test-only constructors exercise native body
/// rebinding independently.
#[derive(Default)]
pub(crate) struct NativeCallableCatalog {
    callables: BTreeMap<String, Function>,
}

impl NativeCallableCatalog {
    #[cfg(test)]
    pub(crate) fn register(
        &mut self,
        canonical_name: impl Into<String>,
        callable: Function,
    ) -> Result<(), SnapshotError> {
        let canonical_name = canonical_name.into();
        if self
            .callables
            .insert(canonical_name.clone(), callable)
            .is_some()
        {
            return Err(SnapshotError::DuplicateNativeCallable(canonical_name));
        }
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn capture_from_functions<'a>(
        functions: impl IntoIterator<Item = &'a ModuleFunction>,
    ) -> Result<Self, SnapshotError> {
        let mut catalog = Self::default();
        for function in functions {
            if let CallableOrigin::Native { canonical_name } = function.origin {
                let name = canonical_name.ok_or(SnapshotError::UnnamedNativeCallable)?;
                catalog.register(name.to_string(), function.code.clone())?;
            }
        }
        Ok(catalog)
    }

    fn resolve(&self, canonical_name: &str) -> Result<Function, SnapshotError> {
        self.callables
            .get(canonical_name)
            .cloned()
            .ok_or_else(|| SnapshotError::UnknownNativeCallable(canonical_name.to_owned()))
    }
}

/// Process-independent reconstruction data for a callable body.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SnapshotFunctionBody {
    Script {
        entry: u32,
        yield_entry: Option<u32>,
        runtime_argument_count: usize,
    },
    Native {
        canonical_name: String,
    },
    BufferPrimitive(BufferPrimitive),
    StructuralFieldAddressor {
        field_index: u32,
        hidden_argument_count: usize,
    },
}

impl SnapshotFunctionBody {
    pub(crate) fn capture(function: &ModuleFunction) -> Result<Self, SnapshotError> {
        Ok(match function.origin {
            CallableOrigin::Script => {
                let script = function
                    .code
                    .as_script()
                    .ok_or(SnapshotError::CallableOriginMismatch)?;
                Self::Script {
                    entry: script.entry_node_id.into_raw().into_u32(),
                    yield_entry: script.yield_node_id.map(|id| id.into_raw().into_u32()),
                    runtime_argument_count: script.runtime_arg_count,
                }
            }
            CallableOrigin::Native { canonical_name } => Self::Native {
                canonical_name: canonical_name
                    .ok_or(SnapshotError::UnnamedNativeCallable)?
                    .to_string(),
            },
            CallableOrigin::StructuralFieldAddressor { field_index } => {
                let hidden_argument_count = function
                    .code
                    .runtime_argument_passing()
                    .expect("structural addressor exposes its runtime arguments")
                    .len()
                    .checked_sub(function.parameter_passing.len())
                    .expect("structural addressor runtime arguments include visible arguments");
                Self::StructuralFieldAddressor {
                    field_index: field_index.as_u32(),
                    hidden_argument_count,
                }
            }
            CallableOrigin::BufferPrimitive(primitive) => Self::BufferPrimitive(primitive),
            CallableOrigin::Transient => return Err(SnapshotError::TransientCallable),
        })
    }

    pub(crate) fn materialize(
        &self,
        catalog: &NativeCallableCatalog,
        hir_node_count: usize,
    ) -> Result<(Function, CallableOrigin), SnapshotError> {
        let node = |index: u32| {
            if index as usize >= hir_node_count {
                Err(SnapshotError::InvalidHirNodeReference(index))
            } else {
                Ok(Idx::<hir::Node<Elaborated>>::from_raw(RawIdx::from_u32(
                    index,
                )))
            }
        };
        Ok(match self {
            Self::Script {
                entry,
                yield_entry,
                runtime_argument_count,
            } => (
                b(ScriptFunction {
                    entry_node_id: node(*entry)?,
                    yield_node_id: yield_entry.map(node).transpose()?,
                    runtime_arg_count: *runtime_argument_count,
                }) as Function,
                CallableOrigin::Script,
            ),
            Self::BufferPrimitive(primitive) => (
                b(*primitive) as Function,
                CallableOrigin::BufferPrimitive(*primitive),
            ),
            Self::Native { canonical_name } => (
                catalog.resolve(canonical_name)?,
                CallableOrigin::Native {
                    canonical_name: Some(canonical_name.as_str().into()),
                },
            ),
            Self::StructuralFieldAddressor {
                field_index,
                hidden_argument_count,
            } => (
                b(StructuralFieldAddressor::new(
                    ProjectionIndex::new(*field_index),
                    *hidden_argument_count,
                )) as Function,
                CallableOrigin::StructuralFieldAddressor {
                    field_index: ProjectionIndex::new(*field_index),
                },
            ),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, std::buffer::expected_primitives};

    #[test]
    fn std_native_callable_bodies_round_trip_by_canonical_name() {
        let session = CompilerSession::new();
        let functions = &session.std_module().functions;
        let catalog = NativeCallableCatalog::capture_from_functions(functions).unwrap();

        for function in functions {
            let body = SnapshotFunctionBody::capture(function).unwrap();
            let (restored, origin) = body
                .materialize(&catalog, session.std_module().hir_arena.len())
                .unwrap();
            assert_eq!(origin, function.origin);
            assert_eq!(
                restored.as_script().is_some(),
                function.code.as_script().is_some()
            );
            assert_eq!(
                restored.visible_parameter_passing(),
                function.code.visible_parameter_passing()
            );
            assert_eq!(
                restored.runtime_argument_passing(),
                function.code.runtime_argument_passing()
            );
        }
    }

    #[test]
    fn buffer_intrinsic_bodies_round_trip_without_native_bindings() {
        let session = CompilerSession::new();
        let catalog = NativeCallableCatalog::default();
        for (id, primitive) in expected_primitives(session.std_module()) {
            let function = session.std_module().get_function_by_id(id).unwrap();
            assert_eq!(function.origin, CallableOrigin::BufferPrimitive(primitive));
            let body = SnapshotFunctionBody::capture(function).unwrap();
            let bytes = postcard::to_allocvec(&body).unwrap();
            let body: SnapshotFunctionBody = postcard::from_bytes(&bytes).unwrap();
            let (restored, origin) = body.materialize(&catalog, 0).unwrap();
            assert_eq!(origin, function.origin);
            assert_eq!(origin, CallableOrigin::BufferPrimitive(primitive));
            assert_eq!(
                restored.runtime_argument_passing(),
                function.code.runtime_argument_passing()
            );
        }
    }
}
