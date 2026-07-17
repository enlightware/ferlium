// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

use derive_new::new;

/// Reference-interpreter backend used to execute compiled Ferlium code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExecutionTarget {
    Hir,
    Ssa,
}

impl ExecutionTarget {
    /// All execution targets, in canonical comparison order.
    pub const ALL: [Self; 2] = [Self::Hir, Self::Ssa];
}

/// Default fuel budget for interactive execution.
pub const DEFAULT_INTERACTIVE_FUEL_LIMIT: usize = 100_000;

/// Backend-independent limits applied to one execution.
///
/// HIR and SSA execution consume the same kinds of budget so selecting an execution backend does
/// not change a program's resource policy. Exceeding one of these limits cancels execution through
/// the executor's out-of-band error channel; it does not add the source-language `Fallible` effect
/// or change a function's normal ABI. A `None` fuel limit disables fuel accounting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, new)]
pub struct ExecutionLimits {
    pub call_depth_limit: usize,
    pub fuel_limit: Option<usize>,
}

impl ExecutionLimits {
    pub const DEFAULT_CALL_DEPTH_LIMIT: usize = 128;

    pub const fn with_call_depth_limit(mut self, call_depth_limit: usize) -> Self {
        self.call_depth_limit = call_depth_limit;
        self
    }

    pub const fn with_fuel_limit(mut self, fuel_limit: Option<usize>) -> Self {
        self.fuel_limit = fuel_limit;
        self
    }
}

impl Default for ExecutionLimits {
    fn default() -> Self {
        Self::new(Self::DEFAULT_CALL_DEPTH_LIMIT, None)
    }
}

/// Limits specific to the boxed HIR and SSA reference interpreters.
///
/// `environment_cell_limit` bounds entries in their shared [`EvalCtx`](crate::eval::EvalCtx)
/// environment. A cell may indirectly own an arbitrary heap allocation, so this is a bookkeeping
/// guard rather than a memory quota.
#[derive(Debug, Clone, Copy, PartialEq, Eq, new)]
pub struct ReferenceInterpreterLimits {
    pub execution: ExecutionLimits,
    pub environment_cell_limit: usize,
}

impl ReferenceInterpreterLimits {
    pub const DEFAULT_ENVIRONMENT_CELL_LIMIT: usize = 65_536;

    pub const fn with_call_depth_limit(mut self, call_depth_limit: usize) -> Self {
        self.execution.call_depth_limit = call_depth_limit;
        self
    }

    pub const fn with_fuel_limit(mut self, fuel_limit: Option<usize>) -> Self {
        self.execution.fuel_limit = fuel_limit;
        self
    }

    pub const fn with_environment_cell_limit(mut self, environment_cell_limit: usize) -> Self {
        self.environment_cell_limit = environment_cell_limit;
        self
    }
}

impl Default for ReferenceInterpreterLimits {
    fn default() -> Self {
        Self::new(
            ExecutionLimits::default(),
            Self::DEFAULT_ENVIRONMENT_CELL_LIMIT,
        )
    }
}
