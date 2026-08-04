// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
pub(crate) mod builder;
pub(crate) mod const_eval;
pub(crate) mod edit;
pub mod function;
pub mod interpreter;
pub mod operation;
pub mod pass;
pub(crate) mod reify;
pub mod terminator;
pub mod value;
#[cfg(any(debug_assertions, test))]
pub(crate) mod verify;

pub use function::{BasicBlock, BlockId, Function, Parameter, ParameterKind};
pub use operation::{Operation, OperationKind, OperationResult};
pub use value::{ParameterId, Value, ValueId};
