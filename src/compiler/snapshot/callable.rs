use std::collections::BTreeMap;

use la_arena::{Idx, RawIdx};

use crate::{
    containers::b,
    hir::function::{Function, ScriptFunction},
    module::{ModuleFunction, function::CallableOrigin},
};

use super::SnapshotError;

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
    StructuralFieldAddressor {
        field_index: usize,
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
                Self::StructuralFieldAddressor { field_index }
            }
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
                Ok(Idx::<crate::hir::Node<crate::hir::Elaborated>>::from_raw(
                    RawIdx::from_u32(index),
                ))
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
            Self::Native { canonical_name } => (
                catalog.resolve(canonical_name)?,
                CallableOrigin::Native {
                    canonical_name: Some(canonical_name.as_str().into()),
                },
            ),
            Self::StructuralFieldAddressor { field_index } => (
                b(crate::hir::function::StructuralFieldAddressor::new(
                    *field_index,
                )) as Function,
                CallableOrigin::StructuralFieldAddressor {
                    field_index: *field_index,
                },
            ),
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::CompilerSession;

    use super::*;

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
        }
    }
}
