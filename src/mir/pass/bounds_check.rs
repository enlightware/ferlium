// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Removing the array bounds checks the program has already proved.
//!
//! `array_resolve_index(index, len)` maps a logical index onto an offset and panics when it is out
//! of range. Its whole behaviour is a case split: it returns `index` when `0 <= index < len`,
//! `len + index` when `-len <= index < 0`, and panics otherwise. So proving the first case turns the
//! call into a copy. When the higher-level `array_index(array, index)` accessor survived inlining,
//! the same proof retargets it to the internal `array_offset_unchecked` accessor. In either shape,
//! the panic is the only reason the call can fail, so its `invoke` becomes straight-line code and
//! its error edge dies with it.
//!
//! What goes away is more than one call. The error edge strands its cleanup block, the panic
//! message's `alloca`s become dead, and `dce` collects all of it. That is the same population the
//! plan's cold-path `alloca` item was about.
//!
//! **The proof comes from [`relations`](super::relations), and nothing here weakens it.** This pass
//! asks one question at each call site — do `0 <= index` and `index < len` follow from what is known
//! here — and rewrites only on yes. A refusal is silent and costs a check that was going to run
//! anyway.
//!
//! **After the rounds, not inside them.** This keeps the relational fixed point to one run per
//! candidate body. It cannot save growth already spent copying a checked accessor, but it handles
//! both outcomes of the inliner: a decomposed `array_resolve_index`, and a whole `array_index` call
//! rejected for size or genericity. Moving the analysis into the rounds is a separate compile-time
//! tradeoff, not required for the check-removal semantics.

use crate::{
    Location,
    containers::b,
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        edit::FunctionEdit,
        pass::site::OperationIndex,
        terminator::{Terminator, TerminatorKind},
    },
    module::{FunctionId, id::Id},
};

use super::{
    dataflow::call_operands,
    known_callee::{KnownCallee, KnownCallees},
    relations::{self, Affine, Comparison, Predicate},
};

/// A checked index the analysis proved in range, and what replaces it.
struct Proved {
    block: BlockId,
    /// Where the check sits: an operation index, or the block's terminator.
    operation: Option<OperationIndex>,
    span: Location,
    replacement: Replacement,
    /// The successor a fallible check would have taken on success.
    normal: Option<BlockId>,
}

/// What an eliminated check becomes.
enum Replacement {
    /// `array_resolve_index` in its non-negative case is the identity function.
    ResolvedIndex {
        index: mir::Value,
        destination: mir::Value,
    },
    /// A checked array addressor whose precondition is proved becomes the corresponding unchecked
    /// addressor, preserving its arguments, out-place and generic instantiation.
    UncheckedArrayIndex(Operation),
}

/// Retargets a checked array addressor call to the internal unchecked offset addressor.
fn unchecked_array_index(operation: &Operation, known: &KnownCallees) -> Operation {
    let mut replacement = operation.clone();
    let (callee, effects) = known.array_offset_unchecked();
    replacement.operands[0] = mir::Value::Function(callee);
    let OperationKind::Call { ty, .. } = &mut replacement.kind else {
        unreachable!("an array-index candidate is a call")
    };
    let mut rewritten_ty = (**ty).clone();
    rewritten_ty.fn_ty.effects = effects.clone();
    *ty = b(rewritten_ty);
    replacement
}

/// Replaces every bounds check whose index is provably in range with a copy.
///
/// Returns the rewritten body and how many checks it removed, or `None` when it removed none.
pub(crate) fn eliminate_bounds_checks(
    func: &Function,
    known: &KnownCallees,
    original_of: &dyn Fn(FunctionId) -> Option<FunctionId>,
) -> Option<(Function, usize)> {
    // The analysis is two walks to a fixpoint; most bodies have no check to remove and must not pay
    // for it.
    if !relations::worth_analyzing(func, known, original_of) {
        return None;
    }
    let mut analysis = relations::analyze(func, known, original_of);

    let mut proved = Vec::new();
    for block in func.blocks() {
        let terminator_index = OperationIndex::from_index(func.block(block).operations().len());
        analysis.replay(
            func,
            known,
            original_of,
            block,
            |operation, def, state, interner, context| {
                let OperationKind::Call { ty, .. } = &operation.kind else {
                    return;
                };
                let callee = relations::resolved_callee(operation, known, original_of);
                let Some(call) = call_operands(&operation.operands, ty) else {
                    return;
                };
                if call.arguments.len() != 2 {
                    return;
                }
                let (index_form, length_form, replacement) = match callee {
                    Some(KnownCallee::ArrayResolveIndex) => {
                        let index = call.arguments[0].0;
                        let length = call.arguments[1].0;
                        let Some(index_form) = state.argument_affine(index, interner) else {
                            return;
                        };
                        let Some(length_form) = state.argument_affine(length, interner) else {
                            return;
                        };
                        (
                            index_form,
                            length_form,
                            Replacement::ResolvedIndex {
                                index: index.clone(),
                                destination: call.result.clone(),
                            },
                        )
                    }
                    Some(KnownCallee::ArrayIndex) => {
                        let Some((index, length)) =
                            context.array_index_forms(operation, state, interner)
                        else {
                            return;
                        };
                        (
                            index,
                            length,
                            Replacement::UncheckedArrayIndex(unchecked_array_index(
                                operation, known,
                            )),
                        )
                    }
                    _ => return,
                };
                let zero = Affine::constant(0);
                let in_range = Predicate::between(&zero, Comparison::LessOrEqual, &index_form)
                    .is_some_and(|goal| state.implies(&goal))
                    && Predicate::between(&index_form, Comparison::Less, &length_form)
                        .is_some_and(|goal| state.implies(&goal));
                if !in_range {
                    return;
                }
                let at = def
                    .operation_index()
                    .filter(|index| *index != terminator_index);
                proved.push(Proved {
                    block,
                    operation: at,
                    span: operation.span,
                    replacement,
                    normal: None,
                });
            },
        );
    }
    // The successor a proved terminator falls through to is a property of the block, not of the
    // replay, so it is filled in here rather than inside the visitor.
    for check in &mut proved {
        if check.operation.is_none()
            && let TerminatorKind::Invoke { normal, .. } =
                &func.block(check.block).terminator().kind
        {
            check.normal = Some(*normal);
        }
    }
    proved.retain(|check| check.operation.is_some() || check.normal.is_some());
    if proved.is_empty() {
        return None;
    }

    let removed = proved.len();
    let mut edit = FunctionEdit::new(func.clone());
    for check in proved {
        let replacement = match check.replacement {
            Replacement::ResolvedIndex { index, destination } => {
                Operation::memcpy(check.span, index, destination)
            }
            Replacement::UncheckedArrayIndex(call) => call,
        };
        match check.operation {
            Some(index) => {
                edit.block_mut(check.block)
                    .replace_operation(index.as_index(), replacement);
            }
            None => {
                // Appending keeps the operation indices any other rewrite in this block was planned
                // against, and the terminator loses the error edge a check that cannot fail no
                // longer has.
                let block = edit.block_mut(check.block);
                block.operations.push(replacement);
                block.terminator = Terminator::goto(
                    check.span,
                    check.normal.expect("a terminator check has a normal edge"),
                );
            }
        }
    }
    // A dead error edge strands its cleanup pad, and the surviving successor is left with one
    // predecessor. Both are this pass's own doing, so both are cleaned up here.
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some((edit.finish_unverified(), removed))
}

#[cfg(test)]
mod tests {
    use crate::{CompilerSession, MirOptimization};

    fn optimized(src: &str) -> String {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        session.set_allow_experimental(true);
        session.emit_mir("bounds", src)
    }

    /// The body of a function in the emitted module, which is its optimized stage: `emit_mir`
    /// prints one stage, and the session above has optimization on.
    fn body_of<'a>(module: &'a str, name: &str) -> &'a str {
        module
            .split(&format!("fn {name}("))
            .nth(1)
            .unwrap_or_else(|| panic!("module has no `{name}`:\n{module}"))
    }

    /// The whole point of the item: a loop whose index the program has already bounded stops paying
    /// to check it, and the panic path goes with it.
    #[test]
    fn a_zero_based_range_loop_loses_its_bounds_check() {
        let module = optimized(
            "fn total(mut a: [int]) -> int { let mut t = 0; for i in 0..len(a) { t = t + a[i] }; t }",
        );
        let body = body_of(&module, "total");
        assert!(
            !body.contains("array_resolve_index"),
            "the check must be gone:\n{body}"
        );
        assert!(
            !body.contains("propagate_error"),
            "and with it the error edge it needed:\n{body}"
        );
        assert!(
            body.contains("buffer_slot"),
            "the element access itself must remain:\n{body}"
        );
    }

    /// A successful seed access proves the array non-empty: `0 < len` entails the `1 <= len`
    /// ordering needed for a range starting at one to count upwards. This covers the non-zero
    /// induction initializer and the normal-edge fact together at the rewriting boundary rather
    /// than only in the relational analysis.
    #[test]
    fn a_loop_from_one_after_a_seed_access_loses_its_bounds_check() {
        let module = optimized(
            "fn total(mut a: [int]) -> int { let mut t = a[0]; for i in 1..len(a) { t = t + a[i] }; t }",
        );
        let body = body_of(&module, "total");
        assert_eq!(
            body.matches("array_resolve_index").count(),
            1,
            "the seed remains checked, but the loop access must use what it proved:\n{body}"
        );
    }

    /// Generic element storage keeps the accessor itself uninlined. Both branch accesses returning
    /// establish the upper bound at their join; the explicit guard establishes non-negativity, so
    /// the final checked signed access can use the internal unchecked-offset accessor.
    #[test]
    fn a_proved_uninlined_array_index_becomes_unchecked() {
        let module = optimized(
            "fn get_after_either<A>(a: [A], i: int, c: bool) -> A {\n\
                 if i < 0 {\n\
                     a[0]\n\
                 } else {\n\
                     if c { a[i] } else { a[i] };\n\
                     a[i]\n\
                 }\n\
             }",
        );
        let body = body_of(&module, "get_after_either");
        assert!(
            body.contains("call std::array_offset_unchecked"),
            "the proved whole accessor must be retargeted and demoted from invoke:\n{body}"
        );
    }

    /// Successful signed indexing does not mean the source index was an offset: a negative index
    /// may have succeeded after normalization. Without an independent non-negativity proof the
    /// unchecked-offset accessor would interpret it incorrectly.
    #[test]
    fn a_repeated_possibly_negative_array_index_stays_checked() {
        let module = optimized(
            "fn get_after_either<A>(a: [A], i: int, c: bool) -> A {\n\
                 if c { a[i] } else { a[i] };\n\
                 a[i]\n\
             }",
        );
        let body = body_of(&module, "get_after_either");
        assert!(
            !body.contains("array_offset_unchecked"),
            "a possibly-negative signed index is not an unchecked offset:\n{body}"
        );
        assert!(
            body.contains("array_index"),
            "the final signed check must remain:\n{body}"
        );
    }

    /// An index nothing bounds keeps its check. Removing one that could fail would turn a panic
    /// into whatever the unchecked path does, which is the failure mode this pass has to not have.
    #[test]
    fn an_unbounded_index_keeps_its_check() {
        let module = optimized("fn get(mut a: [int], i: int) -> int { a[i] }");
        let body = body_of(&module, "get");
        assert!(
            body.contains("array_resolve_index") || body.contains("array_index"),
            "an index nothing bounds must still be checked:\n{body}"
        );
    }

    /// A negative index is legal in Ferlium — it counts from the end — so a loop that produces one
    /// must keep its check even though the index is bounded from above.
    #[test]
    fn a_negative_index_keeps_its_check() {
        let module = optimized(
            "fn total(mut a: [int]) -> int { let mut t = 0; for i in 0..len(a) { t = t + a[-i - 1] }; t }",
        );
        let body = body_of(&module, "total");
        assert!(
            body.contains("array_resolve_index") || body.contains("array_index"),
            "an index that may be negative must still be resolved:\n{body}"
        );
    }
}
