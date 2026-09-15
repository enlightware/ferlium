// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

pub(crate) mod builder;
pub(crate) mod const_eval;
pub(crate) mod dominance;
pub(crate) mod edit;
pub mod function;
pub mod interpreter;
pub mod operation;
pub mod pass;
#[allow(dead_code)] // The physical lowering boundary precedes its first executor.
pub(crate) mod physical;
pub mod profile;
pub(crate) mod reify;
pub(crate) mod role;
pub(crate) mod site;
pub mod terminator;
pub mod value;
pub(crate) mod verify;

pub use function::{BasicBlock, BlockId, Function, Parameter, ParameterKind};
pub use operation::{CallMetadata, Instantiation, Operation, OperationKind, OperationResult};
pub use value::{ParameterId, Value, ValueId};
