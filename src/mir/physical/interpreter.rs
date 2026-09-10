// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Physical execution boundary. The checked byte-memory executor will be implemented here.

use crate::{eval::RuntimeError, hir::value::Value, module::FunctionId};

use super::program::ResolvedPhysicalProgram;

/// Deliberately does not fall back to a boxed interpreter or execute guest code.
pub(crate) fn run_entry(
    _program: &ResolvedPhysicalProgram,
    _entry: FunctionId,
) -> Result<Value, RuntimeError> {
    Err(RuntimeError::Backend(
        "Physical MIR execution is not implemented yet; physical MIR is available for inspection."
            .into(),
    ))
}
