// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Dropping the dictionary parameters a specialization no longer reads.
//!
//! Specializing binds every dictionary parameter to the constant its call site passed, so **a
//! specialization has no live evidence parameter by construction** — `bind_dictionaries` replaces
//! every operand naming one, and `monomorphize`'s own tests assert that none survives. This is
//! therefore not an analysis: the parameters are known dead before the pass looks at anything, and
//! all that remains is to remove them from the signature and from every call that passes them.
//!
//! **Whole-module and after the fact.** A parameter deletion changes every caller, and running it
//! once over the finished artifacts is what keeps it from changing anything else: the optimizer
//! makes every decision — inlining, folding, admission — against the signatures it has always seen,
//! and this pass only narrows the calling convention of bodies nothing will look at again. One
//! module is enough because the set of things that can name a specialization is closed within it:
//!
//! - [`specialize_call_sites`](super::monomorphize::specialize_call_sites) is the only writer of a
//!   specialization into a callee operand, and it requires an `OperationKind::Call`, so a
//!   specialization never reaches a `build_closure`, `clone` or `drop` function operand;
//! - [`redirect_recursion`](super::monomorphize) points a specialization's self-calls at itself,
//!   inside the same module's table;
//! - every cross-module lookup in the driver reads the *raw* stage, which is exactly the HIR
//!   function table and contains no specialization at all.
//!
//! The specialization's HIR metadata stays valid because only *hidden* parameters go:
//! `parameter_passing` describes the visible arguments alone and the return convention is
//! untouched, so the indirection through `Specialization::original` still answers every question
//! asked about a specialized callee.

use crate::{
    compiler::Specialization,
    mir::{
        self, Function, OperationKind, ParameterKind, edit::FunctionEdit,
        terminator::TerminatorKind,
    },
    module::{ModuleId, id::Id},
};

/// Removes every specialization's bound dictionary parameters, and the operands that pass them.
///
/// `functions` is the module's HIR-declared prefix and `specializations` the bodies the optimizer
/// appended past it, which together are every body that can hold such a call.
pub(crate) fn drop_dead_specialization_evidence(
    functions: &mut [Option<Function>],
    specializations: Vec<Specialization>,
    module: ModuleId,
) -> Vec<Specialization> {
    let first_index = functions.len();
    let dropped: Vec<usize> = specializations
        .iter()
        .map(|specialization| dictionary_parameters(&specialization.body))
        .collect();
    if dropped.iter().all(|&count| count == 0) {
        return specializations;
    }

    // How many operands a call to `callee` sheds, or `None` when it names anything else. A
    // specialization of another module cannot occur, so the module check is what makes a bare local
    // index meaningful rather than a coincidence.
    let dropped_at = |callee: &mir::Value| -> Option<usize> {
        let mir::Value::Function(id) = callee else {
            return None;
        };
        if id.module != module {
            return None;
        }
        let count = *dropped.get(id.function.as_index().checked_sub(first_index)?)?;
        (count > 0).then_some(count)
    };

    // Taken by value on both sides: a body is rewritten by moving it through an edit, so nothing
    // here clones a function it is about to replace.
    for slot in functions.iter_mut() {
        if let Some(body) = slot.take() {
            *slot = Some(rewrite(body, 0, &dropped_at));
        }
    }
    specializations
        .into_iter()
        .zip(&dropped)
        .map(|(specialization, &own)| Specialization {
            body: rewrite(specialization.body, own, &dropped_at),
            ..specialization
        })
        .collect()
}

/// The number of dictionary parameters in `body`'s signature.
fn dictionary_parameters(body: &Function) -> usize {
    body.parameters()
        .iter()
        .filter(|parameter| matches!(parameter.kind, ParameterKind::Dictionary))
        .count()
}

/// Narrows one body: its own signature by `own`, and every call it makes to a narrowed callee.
///
/// A body with nothing to change is left alone rather than decomposed and reconstructed for the
/// identity. Rewritten bodies are verified with every other final artifact after this whole-module
/// cleanup completes.
fn rewrite(
    body: Function,
    own: usize,
    dropped_at: &impl Fn(&mir::Value) -> Option<usize>,
) -> Function {
    if own == 0 && !calls_a_narrowed_callee(&body, dropped_at) {
        return body;
    }

    let name = body.name;
    let mut edit = FunctionEdit::new(body);
    if own > 0 {
        edit.remove_parameters(|parameter| matches!(parameter.kind, ParameterKind::Dictionary));
    }
    for block_id in edit.blocks().collect::<Vec<_>>() {
        let block = edit.block_mut(block_id);
        let operations = block
            .operations
            .iter_mut()
            .chain(match &mut block.terminator.kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            });
        for operation in operations {
            let OperationKind::Call { ty, .. } = &operation.kind else {
                continue;
            };
            let Some(count) = dropped_at(&operation.operands[0]) else {
                continue;
            };
            // The operand layout the verifier and the interpreter both read: the callee, the hidden
            // evidence, the visible arguments named by the call-site type, and the return
            // out-pointer. Asserted rather than assumed, because a mismatch would silently shift
            // every argument the callee binds positionally.
            let visible_start = operation.operands.len() - (ty.fn_ty.args.len() + 1);
            assert_eq!(
                visible_start - 1,
                count,
                "MIR function `{}`: a call to a specialization passes {} hidden operands for {} \
                 dictionary parameters",
                name,
                visible_start - 1,
                count
            );
            assert!(
                operation.operands[1..visible_start]
                    .iter()
                    .all(|operand| matches!(operand, mir::Value::Dictionary(_))),
                "MIR function `{}`: a call to a specialization passes hidden evidence that is not \
                 a constant dictionary",
                name
            );
            let mut operands = std::mem::take(&mut operation.operands).into_vec();
            operands.drain(1..visible_start);
            operation.operands = operands.into_boxed_slice();
        }
    }
    edit.finish_unverified()
}

/// Whether any call in `body` names a callee whose signature this pass narrows.
fn calls_a_narrowed_callee(
    body: &Function,
    dropped_at: &impl Fn(&mir::Value) -> Option<usize>,
) -> bool {
    body.blocks().any(|block_id| {
        let block = body.block(block_id);
        let operations = block
            .operations()
            .iter()
            .chain(match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            });
        operations
            .filter(|operation| matches!(operation.kind, OperationKind::Call { .. }))
            .any(|operation| dropped_at(&operation.operands[0]).is_some())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, MirOptimization, module::FunctionId, module::Path};

    /// The whole invariant, over the corpus that has specializations worth counting.
    ///
    /// Two halves that must hold together: a specialization carries no dictionary parameter, and no
    /// call passes one. Checking only the first would pass on a module whose callers still push the
    /// operands, which is exactly the shape that shifts every argument the callee binds
    /// positionally.
    #[test]
    fn no_specialization_in_optimized_std_keeps_or_is_passed_evidence() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let (std_id, _) = session
            .modules()
            .get_by_path(&Path::single_str("std"))
            .expect("the standard library is always registered");
        // Builds both stages, which is the only way to ask for the optimized one.
        session.optimization_report(std_id);
        let optimized = session
            .mir_artifacts_for(std_id, MirOptimization::Enabled)
            .expect("optimized artifacts were just built");
        let raw = session
            .mir_artifacts_for(std_id, MirOptimization::Disabled)
            .expect("the raw stage is built before the optimized one");

        assert!(
            !optimized.specializations().is_empty(),
            "std must specialize something, or this test proves nothing"
        );
        let mut removed = 0;
        for specialization in optimized.specializations() {
            assert_eq!(
                dictionary_parameters(&specialization.body),
                0,
                "specialization `{}` keeps a dictionary parameter it cannot read",
                specialization.name
            );
            let original = specialization.original;
            assert_eq!(
                original.module, std_id,
                "a std specialization of another module's function is not expected here"
            );
            removed += raw.get(original.function).map_or(0, dictionary_parameters);
        }
        assert!(
            removed > 0,
            "no std specialization had evidence to drop, so this test proves nothing"
        );

        let first_index = optimized.bodies().len();
        let bodies = optimized
            .bodies()
            .iter()
            .flatten()
            .chain(optimized.specializations().iter().map(|s| &s.body));
        for body in bodies {
            for block_id in body.blocks() {
                let block = body.block(block_id);
                let operations = block
                    .operations()
                    .iter()
                    .chain(match &block.terminator().kind {
                        TerminatorKind::Invoke { operation, .. } => Some(operation),
                        _ => None,
                    });
                for operation in operations {
                    let OperationKind::Call { ty, .. } = &operation.kind else {
                        continue;
                    };
                    let mir::Value::Function(FunctionId { module, function }) =
                        &operation.operands[0]
                    else {
                        continue;
                    };
                    if *module != std_id || function.as_index() < first_index {
                        continue;
                    }
                    assert_eq!(
                        operation.operands.len(),
                        ty.fn_ty.args.len() + 2,
                        "MIR function `{}` passes hidden evidence to a specialization",
                        body.name
                    );
                }
            }
        }
    }
}
