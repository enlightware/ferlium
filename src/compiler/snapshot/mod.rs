//! Stable, process-independent representations of compiled compiler data.
//!
//! Snapshot DTOs deliberately live outside the runtime structures. In particular, they never
//! retain process-local `Type` indices, `Ustr` handles, native trait objects, or function pointers.

#[cfg(all(
    feature = "std-cache",
    not(all(target_arch = "wasm32", target_os = "unknown"))
))]
mod cache;
mod callable;
mod checkpoint;
mod envelope;
mod function;
mod hir;
mod literal;
mod native;
mod semantic;
mod source;
mod std_snapshot;
mod subscript;
mod trait_impl;
mod type_graph;
mod types;

#[cfg(all(
    feature = "std-cache",
    not(all(target_arch = "wasm32", target_os = "unknown"))
))]
pub(crate) use cache::load_or_build_std;
pub(crate) use callable::{NativeCallableCatalog, SnapshotFunctionBody};
pub(crate) use checkpoint::{ModuleCheckpointShape, SnapshotModuleCheckpoint};
#[cfg(all(
    feature = "std-cache",
    not(all(target_arch = "wasm32", target_os = "unknown"))
))]
pub(crate) use envelope::STD_SNAPSHOT_FORMAT_VERSION;
pub(crate) use envelope::{StdSnapshot, StdSnapshotHeader};
pub(crate) use function::SnapshotModuleFunction;
pub(crate) use hir::SnapshotHirArena;
pub(crate) use literal::SnapshotLiteral;
pub(crate) use native::NativeTypeCatalog;
pub(crate) use semantic::{SnapshotCallableDefinition, SnapshotTypeScheme};
pub(crate) use source::SnapshotSourceTable;
#[cfg(all(
    feature = "std-cache",
    not(all(target_arch = "wasm32", target_os = "unknown"))
))]
pub(crate) use std_snapshot::CompiledStdSnapshot;
pub(crate) use subscript::{SnapshotProjection, SnapshotSubscript};
pub(crate) use trait_impl::SnapshotTraitImpls;
pub(crate) use type_graph::{SnapshotTypeGraph, SnapshotTypeGraphBuilder, SnapshotTypeId};
pub(crate) use types::{SnapshotTrait, SnapshotTypeAlias, SnapshotTypeDefSlot};

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SnapshotError {
    UnnamedNativeType(String),
    UnknownNativeType(String),
    InvalidTypeReference(u32),
    IncompleteTypeGraph(u32),
    UnnamedNativeCallable,
    UnknownNativeCallable(String),
    #[cfg(test)]
    DuplicateNativeCallable(String),
    NativeCallableInSourceCheckpoint(String),
    TransientCallable,
    CallableOriginMismatch,
    UnknownNativeLiteral(String),
    InvalidNativeLiteral(String),
    InvalidHirNodeReference(u32),
    NativeDeriverInSourceCheckpoint(String),
    PendingSubscriptInSnapshot,
    CheckpointShapeMismatch(String),
    StaleSnapshot,
}

impl fmt::Display for SnapshotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnnamedNativeType(name) => {
                write!(
                    f,
                    "native Rust type `{name}` has no canonical snapshot name"
                )
            }
            Self::UnknownNativeType(name) => {
                write!(f, "snapshot requires unknown native type `{name}`")
            }
            Self::InvalidTypeReference(index) => {
                write!(f, "snapshot contains invalid type reference {index}")
            }
            Self::IncompleteTypeGraph(index) => {
                write!(f, "snapshot type node {index} was not completed")
            }
            Self::UnnamedNativeCallable => write!(f, "native callable has no canonical name"),
            Self::UnknownNativeCallable(name) => {
                write!(f, "snapshot requires unknown native callable `{name}`")
            }
            #[cfg(test)]
            Self::DuplicateNativeCallable(name) => {
                write!(f, "duplicate native callable catalog entry `{name}`")
            }
            Self::NativeCallableInSourceCheckpoint(name) => {
                write!(
                    f,
                    "source checkpoint unexpectedly contains native callable `{name}`"
                )
            }
            Self::TransientCallable => write!(f, "cannot snapshot a transient callable"),
            Self::CallableOriginMismatch => {
                write!(
                    f,
                    "callable implementation does not match its persistence origin"
                )
            }
            Self::UnknownNativeLiteral(name) => {
                write!(f, "native literal type `{name}` has no snapshot codec")
            }
            Self::InvalidNativeLiteral(message) => write!(f, "invalid native literal: {message}"),
            Self::InvalidHirNodeReference(index) => {
                write!(f, "snapshot contains invalid HIR node reference {index}")
            }
            Self::NativeDeriverInSourceCheckpoint(name) => {
                write!(
                    f,
                    "source checkpoint trait `{name}` unexpectedly owns native derivers"
                )
            }
            Self::PendingSubscriptInSnapshot => {
                write!(
                    f,
                    "cannot snapshot a subscript with an unresolved signature"
                )
            }
            Self::CheckpointShapeMismatch(message) => {
                write!(
                    f,
                    "std checkpoint does not match native build state: {message}"
                )
            }
            Self::StaleSnapshot => write!(f, "compiled std snapshot is stale"),
        }
    }
}

impl std::error::Error for SnapshotError {}
