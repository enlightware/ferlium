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
pub(crate) mod fold;

use crate::{
    compiler::CompilerSession,
    mir::{Function, edit::FunctionEdit},
    module::{ModuleEnv, ModuleId},
};

/// Optimizes one function, returning the body to install.
///
/// Each round rewrites an immutable function into a new one, so a pass never reads an analysis that
/// its own edits have invalidated. A round that changes nothing ends the loop; the rounds exist
/// because folding and inlining feed each other, and because a chain of folds that crosses block
/// boundaries needs the analysis to be re-run to propagate.
pub(crate) fn optimize_function(
    function: &Function,
    env: ModuleEnv<'_>,
    session: &CompilerSession,
    module_id: ModuleId,
) -> Function {
    let mut current: Option<Function> = None;
    for _round in 0..budget::MAX_ROUNDS {
        let source = current.as_ref().unwrap_or(function);
        let Some(folded) = fold::fold_function(source, env, session, module_id) else {
            break;
        };
        current = Some(folded);
    }
    // An unchanged function is still opened and closed, which re-verifies it and is the identity.
    match current {
        Some(folded) => folded,
        None => FunctionEdit::new(function.clone()).finish(env),
    }
}
