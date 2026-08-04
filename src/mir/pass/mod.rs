// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! The MIR optimization passes and the driver that runs them.
//!
//! A function is opened with [`FunctionEdit`](crate::mir::edit::FunctionEdit), rewritten in place,
//! and closed again — which restores canonical form and re-verifies it. The driver alternates
//! folding and inlining for a bounded number of rounds, because the two feed each other: inlining
//! binds a callee's dictionary parameters to constants, folding then resolves the callee's
//! `dict_entry`s into known function places, and the calls that become direct are new candidates
//! for both. Fold first within a round — it is cheap, it is what makes arguments known, and it
//! shrinks a function before the inliner measures it against its growth budget.
//!
//! Optimization terminates on three independent bounds: the dataflow lattice is monotone within a
//! run, inlining is bounded by its growth budget and the non-recursive restriction, and
//! [`MAX_ROUNDS`](budget::MAX_ROUNDS) bounds the outer loop.
//!
//! The driver is per module and reads the raw stage of every body it consults, so a result never
//! depends on the order functions are optimized in. Inlining may cross module boundaries — that is
//! where most inlinable script callees live — which is sound because function, dictionary and
//! subscript identities are global while constant identities are function-local and remapped into
//! the caller's pool. This is not whole-program optimization: nothing outside the module being
//! optimized is modified.
//!
//! See `doc/plans/partial-evaluation.md`.

pub(crate) mod budget;
pub(crate) mod dataflow;

use crate::{
    compiler::CompilerSession,
    mir::{Function, edit::FunctionEdit},
    module::ModuleEnv,
};

/// Optimizes one function, returning the body to install.
///
/// No pass rewrites anything yet, so this opens the function and closes it again: an empty edit is
/// the identity, which is what keeps optimized MIR byte-identical to raw MIR until a pass actually
/// changes something. The round loop described above arrives with the folding pass, which is the
/// first thing that can report having changed anything.
pub(crate) fn optimize_function(
    function: &Function,
    env: ModuleEnv<'_>,
    _session: &CompilerSession,
) -> Function {
    FunctionEdit::new(function.clone()).finish(env)
}
