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
//! call into a copy, while proving the second turns it into the ordinary wrapping integer addition.
//! When the higher-level `array_index(array, index)` accessor survived inlining, either proof
//! retargets it to the internal `array_offset_unchecked` accessor, materializing `len + index` first
//! in the negative case. In either shape, the panic is the only reason the call can fail, so its
//! `invoke` becomes straight-line code and its error edge dies with it.
//!
//! What goes away is more than one call. The error edge strands its cleanup block, the panic
//! message's `alloca`s become dead, and `dce` collects all of it. That is the same population the
//! plan's cold-path `alloca` item was about.
//!
//! **The proof comes from [`relations`](super::relations), and nothing here weakens it.** This pass
//! asks whether either `0 <= index < len` or `index < 0` and `0 <= len + index < len` follows from
//! what is known at each call site, and rewrites only on yes. A refusal is silent and costs a check
//! that was going to run anyway.
//!
//! **After the rounds, not inside them.** This keeps the relational fixed point to one run per
//! candidate body. It cannot save growth already spent copying a checked accessor, but it handles
//! both outcomes of the inliner: a decomposed `array_resolve_index`, and a whole `array_index` call
//! rejected for size or genericity. Moving the analysis into the rounds is a separate compile-time
//! tradeoff, not required for the check-removal semantics.

use crate::{
    Location,
    containers::b,
    hir::value::LiteralValue,
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        edit::FunctionEdit,
        pass::site::OperationIndex,
        terminator::{Terminator, TerminatorKind},
    },
    module::{FunctionId, ModuleEnv, id::Id},
    std::math::int_type,
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
    /// `array_resolve_index` becomes either the identity or the negative-index normalization.
    ResolvedIndex {
        index: mir::Value,
        length: mir::Value,
        destination: mir::Value,
        normalization: Normalization,
    },
    /// A checked array addressor whose precondition is proved becomes the corresponding unchecked
    /// addressor. A negative source index first needs its normalized logical offset.
    UncheckedArrayIndex {
        operation: Operation,
        array: mir::Value,
        index: mir::Value,
        normalization: Normalization,
    },
}

/// Which branch of signed-index resolution the analysis proved.
#[derive(Clone, Copy)]
enum Normalization {
    NonNegative,
    Negative,
}

/// Retargets a checked array addressor call to the internal unchecked offset addressor.
fn unchecked_array_index(
    operation: &Operation,
    known: &KnownCallees,
    offset: Option<mir::Value>,
) -> Operation {
    let mut replacement = operation.clone();
    let (callee, effects) = known.array_offset_unchecked();
    replacement.operands[0] = mir::Value::Function(callee);
    let OperationKind::Call { ty, .. } = &mut replacement.kind else {
        unreachable!("an array-index candidate is a call")
    };
    let mut rewritten_ty = (**ty).clone();
    rewritten_ty.fn_ty.effects = effects.clone();
    *ty = b(rewritten_ty);
    if let Some(offset) = offset {
        let OperationKind::Call { ty, .. } = &replacement.kind else {
            unreachable!()
        };
        let visible_start = replacement.operands.len() - (ty.fn_ty.args.len() + 1);
        replacement.operands[visible_start + 1] = offset;
    }
    replacement
}

/// Materializes the wrapping integer addition whose affine result the analysis proved in range.
fn add_offset(
    span: Location,
    known: &KnownCallees,
    length: mir::Value,
    index: mir::Value,
    destination: mir::Value,
) -> Operation {
    let (callee, ty) = known.int_add();
    Operation::call(
        span,
        mir::Value::Function(callee),
        [length, index, destination],
        ty.clone(),
    )
}

/// Replaces every bounds check whose index is provably in range with a copy.
///
/// Returns the rewritten body and how many checks it removed, or `None` when it removed none.
pub(crate) fn eliminate_bounds_checks(
    func: &Function,
    env: ModuleEnv<'_>,
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
                                length: length.clone(),
                                destination: call.result.clone(),
                                normalization: Normalization::NonNegative,
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
                            Replacement::UncheckedArrayIndex {
                                operation: operation.clone(),
                                array: call.arguments[0].0.clone(),
                                index: call.arguments[1].0.clone(),
                                normalization: Normalization::NonNegative,
                            },
                        )
                    }
                    _ => return,
                };
                let zero = Affine::constant(0);
                let nonnegative = Predicate::between(&zero, Comparison::LessOrEqual, &index_form)
                    .is_some_and(|goal| state.implies(&goal))
                    && Predicate::between(&index_form, Comparison::Less, &length_form)
                        .is_some_and(|goal| state.implies(&goal));
                let negative = length_form.add(&index_form).is_some_and(|offset| {
                    Predicate::between(&index_form, Comparison::Less, &zero)
                        .is_some_and(|goal| state.implies(&goal))
                        && Predicate::between(&zero, Comparison::LessOrEqual, &offset)
                            .is_some_and(|goal| state.implies(&goal))
                        && Predicate::between(&offset, Comparison::Less, &length_form)
                            .is_some_and(|goal| state.implies(&goal))
                });
                let normalization = if nonnegative {
                    Normalization::NonNegative
                } else if negative {
                    Normalization::Negative
                } else {
                    return;
                };
                let replacement = match replacement {
                    Replacement::ResolvedIndex {
                        index,
                        length,
                        destination,
                        ..
                    } => Replacement::ResolvedIndex {
                        index,
                        length,
                        destination,
                        normalization,
                    },
                    Replacement::UncheckedArrayIndex {
                        operation,
                        array,
                        index,
                        ..
                    } => Replacement::UncheckedArrayIndex {
                        operation,
                        array,
                        index,
                        normalization,
                    },
                };
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
    // Replacing one check can insert several operations, so process each block from the back to
    // keep the operation indices recorded by replay valid. A terminator is ordered after every
    // ordinary operation; appending its replacement does not move any of them.
    proved.sort_by(|left, right| {
        left.block
            .as_index()
            .cmp(&right.block.as_index())
            .then_with(|| {
                right
                    .operation
                    .map_or(usize::MAX, |index| index.as_index())
                    .cmp(&left.operation.map_or(usize::MAX, |index| index.as_index()))
            })
    });
    for check in proved {
        let replacements = match check.replacement {
            Replacement::ResolvedIndex {
                index,
                length,
                destination,
                normalization,
            } => vec![match normalization {
                Normalization::NonNegative => Operation::memcpy(check.span, index, destination),
                Normalization::Negative => {
                    add_offset(check.span, known, length, index, destination)
                }
            }],
            Replacement::UncheckedArrayIndex {
                operation,
                array,
                index,
                normalization,
            } => match normalization {
                Normalization::NonNegative => {
                    vec![unchecked_array_index(&operation, known, None)]
                }
                Normalization::Negative => {
                    let field = edit.add_constant(
                        int_type(),
                        LiteralValue::new_native(known.layouts().array_len.as_index() as isize),
                        &env,
                    );
                    let length_id = edit.new_value();
                    let mut length_operation = Operation::subfield(
                        check.span,
                        array,
                        mir::Value::Constant(field),
                        int_type(),
                    );
                    length_operation.assign_result_id(Some(length_id));

                    let offset_id = edit.new_value();
                    let mut offset = Operation::alloca(check.span, int_type());
                    offset.assign_result_id(Some(offset_id));
                    let offset_place = mir::Value::Register(offset_id);
                    vec![
                        length_operation,
                        offset,
                        add_offset(
                            check.span,
                            known,
                            mir::Value::Register(length_id),
                            index,
                            offset_place.clone(),
                        ),
                        unchecked_array_index(&operation, known, Some(offset_place)),
                    ]
                }
            },
        };
        match check.operation {
            Some(index) => {
                edit.block_mut(check.block)
                    .operations
                    .splice(index.as_index()..=index.as_index(), replacements);
            }
            None => {
                // Appending keeps the operation indices any other rewrite in this block was planned
                // against, and the terminator loses the error edge a check that cannot fail no
                // longer has.
                let block = edit.block_mut(check.block);
                block.operations.extend(replacements);
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

    /// Element values need not be known for the constructor to establish the array's length. This
    /// deliberately uses parameters so constant-array folding cannot prove the access instead.
    #[test]
    fn a_build_array_proves_its_literal_length() {
        let module =
            optimized("fn third(x: int, y: int, z: int) -> int { let a = [x, y, z]; a[2] }");
        let body = body_of(&module, "third");
        assert!(
            !body.contains("array_resolve_index") && !body.contains("array_index"),
            "the constructor's literal length must prove the access in range:\n{body}"
        );
        assert!(
            body.contains("buffer_slot"),
            "only the bounds check, not the element access, should disappear:\n{body}"
        );
    }

    /// The same local fact supplies the upper bound for every yielded index in a literal-sized
    /// range. Unknown elements keep this a relations test rather than a whole-array fold.
    #[test]
    fn a_literal_sized_loop_over_build_array_loses_its_bounds_check() {
        let module = optimized(
            "fn total(x: int, y: int, z: int) -> int {\n\
                 let a = [x, y, z];\n\
                 let mut t = 0;\n\
                 for i in 0..3 { t = t + a[i] };\n\
                 t\n\
             }",
        );
        let body = body_of(&module, "total");
        assert!(
            !body.contains("array_resolve_index") && !body.contains("array_index"),
            "the literal-sized loop must use the constructed length:\n{body}"
        );
    }

    /// Knowing an exact length must not turn a false bound into a proof.
    #[test]
    fn an_out_of_range_build_array_access_stays_checked() {
        let module =
            optimized("fn fourth(x: int, y: int, z: int) -> int { let a = [x, y, z]; a[3] }");
        let body = body_of(&module, "fourth");
        assert!(
            body.contains("array_resolve_index") || body.contains("array_index"),
            "an access at the constructed length must remain checked:\n{body}"
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

    /// The other branch of signed indexing: once guards prove `i < 0` and `0 <= len + i < len`,
    /// the checked resolver becomes exactly the ordinary wrapping addition `len + i`. The source
    /// writes the lower-bound guard explicitly so this tests the rewrite rather than asking the
    /// deliberately syntactic relation domain for an extra overflow lemma.
    #[test]
    fn a_proved_negative_index_is_normalized_without_a_check() {
        let module = optimized(
            "fn from_end(a: [int], i: int) -> int {\n\
                 if i < 0 {\n\
                     if len(a) + i >= 0 { a[i] } else { panic(\"bad index\") }\n\
                 } else {\n\
                     panic(\"not a negative index\")\n\
                 }\n\
             }",
        );
        let body = body_of(&module, "from_end");
        assert!(
            !body.contains("array_resolve_index") && !body.contains("array_index"),
            "the proved negative access must contain no checked indexing call:\n{body}"
        );
        assert!(
            body.matches("Num<std::int>::add").count() >= 2,
            "one addition tests the guard and another materializes the normalized offset:\n{body}"
        );
    }

    /// The whole-accessor rewrite needs one extra step: read the array's length, materialize
    /// `len + i`, then retarget the checked addressor to `array_offset_unchecked`. The unrelated
    /// accesses deliberately spend the fixed inline-growth budget so the final accessor remains
    /// whole; their checks are not the subject of this assertion.
    #[test]
    fn a_proved_whole_negative_array_index_becomes_unchecked() {
        let module = optimized(
            "fn from_end_after_work(work: [int], x: int, y: int, z: int, i: int) -> int {\n\
                 let a = [x, y, z];\n\
                 if i < 0 {\n\
                     if 3 + i >= 0 {\n\
                         work[0]; work[1]; work[2]; work[3];\n\
                         work[4]; work[5]; work[6]; work[7];\n\
                         a[i]\n\
                     } else { panic(\"bad index\") }\n\
                 } else {\n\
                     panic(\"not a negative index\")\n\
                 }\n\
             }",
        );
        let body = body_of(&module, "from_end_after_work");
        assert_eq!(
            body.matches("call std::array_offset_unchecked").count(),
            1,
            "the final whole accessor must use its proved normalized offset:\n{body}"
        );
    }

    /// Negativity alone establishes which normalization branch applies, but not that the result
    /// lies at or above zero. The missing `-len <= i` half must retain the source failure.
    #[test]
    fn a_negative_index_without_a_lower_bound_stays_checked() {
        let module = optimized(
            "fn from_end(a: [int], i: int) -> int {\n\
                 if i < 0 { a[i] } else { panic(\"not a negative index\") }\n\
             }",
        );
        let body = body_of(&module, "from_end");
        assert!(
            body.contains("array_resolve_index") || body.contains("array_index"),
            "a negative index with no lower bound can still be out of range:\n{body}"
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

    /// This reverse index is semantically in range, but deriving `-i - 1 < 0` from `0 <= i` needs a
    /// wrapping-safe entailment lemma the deliberately syntactic relation domain does not have.
    /// Refusing it is conservative; the negative rewrite above applies once both normalized bounds
    /// are actually proved.
    #[test]
    fn an_unproved_reverse_loop_index_keeps_its_check() {
        let module = optimized(
            "fn total(mut a: [int]) -> int { let mut t = 0; for i in 0..len(a) { t = t + a[-i - 1] }; t }",
        );
        let body = body_of(&module, "total");
        assert!(
            body.contains("array_resolve_index") || body.contains("array_index"),
            "a semantically valid but unproved negative index must still be resolved:\n{body}"
        );
    }
}
