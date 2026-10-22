// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Small local MIR rewrites.

use rustc_hash::FxHashMap;

use crate::{
    containers::b,
    hir::value::LiteralValue,
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        edit::FunctionEdit,
        pass::dataflow::static_evidence_operand,
        terminator::{Terminator, TerminatorKind},
        value::{StaticEvidence, ValueId},
    },
    module::ModuleEnv,
};

struct BoolStore {
    value: bool,
    destination: mir::Value,
    join: BlockId,
}

struct BooleanMaterialization {
    block: BlockId,
    condition: mir::Value,
    /// Pattern whose match selects the first arm. Absent for an ordinary boolean condition.
    pattern: Option<LiteralValue>,
    stored_when_selected: bool,
    destination: mir::Value,
    join: BlockId,
}

/// Rewrites boolean materialization diamonds into one value computation and store.
///
/// The matched shape is deliberately strict. Its head is either a boolean `condbr` or a
/// one-case `switch_variant`:
///
/// ```text
/// condbr condition, left, right
/// // or: switch_variant tag [Case => left] default right
/// left:  store true-or-false to dst; br join
/// right: store opposite      to dst; br join
/// ```
///
/// The replacement stores a boolean condition directly. A variant switch first compares the
/// opaque tag with its symbolic case; inverse polarity adds a comparison with `false`. It then
/// jumps to `join`.
pub(crate) fn materialize_boolean_results(func: &Function) -> Option<Function> {
    let rewrites: Vec<_> = func
        .blocks()
        .filter_map(|block| plan_boolean_materialization(func, block))
        .collect();
    if rewrites.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for rewrite in rewrites {
        let span = edit.block(rewrite.block).terminator.span;
        let mut stored_value = rewrite.condition;
        if let Some(pattern) = rewrite.pattern {
            let mut comparison =
                Operation::compare_eq(span, stored_value, mir::Value::Pattern(b(pattern)));
            let result = edit.new_value();
            comparison.assign_result_id(Some(result));
            edit.block_mut(rewrite.block).operations.push(comparison);
            stored_value = mir::Value::Register(result);
        }
        if !rewrite.stored_when_selected {
            let mut comparison = Operation::compare_eq(
                span,
                stored_value,
                mir::Value::Pattern(b(LiteralValue::new_native(false))),
            );
            let result = edit.new_value();
            comparison.assign_result_id(Some(result));
            edit.block_mut(rewrite.block).operations.push(comparison);
            stored_value = mir::Value::Register(result);
        }

        let block = edit.block_mut(rewrite.block);
        block
            .operations
            .push(Operation::store(span, stored_value, rewrite.destination));
        block.terminator = Terminator::goto(span, rewrite.join);
    }
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some(edit.finish_unverified())
}

fn plan_boolean_materialization(func: &Function, block: BlockId) -> Option<BooleanMaterialization> {
    let (condition, pattern, selected_target, other_target) =
        match &func.block(block).terminator().kind {
            TerminatorKind::CondBr {
                condition,
                then_target,
                else_target,
            } => (condition.clone(), None, *then_target, *else_target),
            // A multi-case tail would require redirecting only the two materializing edges while
            // retaining the switch for the other cases. Leave that CFG rewrite to evidence from a
            // real workload rather than growing this local diamond rule speculatively.
            TerminatorKind::SwitchVariant {
                tag,
                cases,
                default,
            } if cases.len() == 1 => (
                tag.clone(),
                Some(LiteralValue::new_variant_tag(cases[0].0)),
                cases[0].1,
                *default,
            ),
            _ => return None,
        };
    if selected_target == other_target {
        return None;
    }

    let selected_store = single_bool_store(func, selected_target)?;
    let other_store = single_bool_store(func, other_target)?;
    if selected_store.join != other_store.join
        || selected_store.destination != other_store.destination
        || selected_store.value == other_store.value
    {
        return None;
    }

    Some(BooleanMaterialization {
        block,
        condition,
        pattern,
        stored_when_selected: selected_store.value,
        destination: selected_store.destination,
        join: selected_store.join,
    })
}

fn single_bool_store(func: &Function, block: BlockId) -> Option<BoolStore> {
    let block = func.block(block);
    let [operation] = block.operations() else {
        return None;
    };
    let OperationKind::Store = operation.kind else {
        return None;
    };
    let [value, destination] = operation.operands.as_ref() else {
        return None;
    };
    let TerminatorKind::Goto { target } = block.terminator().kind else {
        return None;
    };
    Some(BoolStore {
        value: bool_value(func, value)?,
        destination: destination.clone(),
        join: target,
    })
}

/// Replaces each dictionary closed over static evidence only by that static evidence.
///
/// Inlining binds a callee's dictionary parameters to the caller's evidence, so a
/// `build_dictionary` that closed a blanket impl over run-time evidence can end up closing it over
/// constants, such as `Value<Option<HashMapEntry<K, V>>>` once `K` and `V` are known. As a
/// register, its entries are opaque to devirtualization; as static evidence, they resolve to
/// direct calls carrying their captures, which specialization and inlining then reach. Nested
/// closures resolve to a fixpoint, since a capture may itself be such a register.
pub(crate) fn close_static_dictionaries(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let mut closed: FxHashMap<ValueId, StaticEvidence> = FxHashMap::default();
    let static_operand =
        |closed: &FxHashMap<ValueId, StaticEvidence>, operand: &mir::Value| match operand {
            mir::Value::Register(id) => closed.get(id).cloned(),
            _ => static_evidence_operand(operand),
        };
    loop {
        let found = closed.len();
        for operation in func.blocks().flat_map(|block| {
            let block = func.block(block);
            block
                .operations()
                .iter()
                .chain(match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => Some(operation),
                    _ => None,
                })
        }) {
            let OperationKind::BuildDictionary { definition, .. } = operation.kind else {
                continue;
            };
            let Some(result) = operation.result_id() else {
                continue;
            };
            if closed.contains_key(&result) {
                continue;
            }
            let Some(captures) = operation
                .operands
                .iter()
                .map(|operand| static_operand(&closed, operand))
                .collect::<Option<Box<[_]>>>()
            else {
                continue;
            };
            closed.insert(
                result,
                StaticEvidence::Dictionary {
                    definition,
                    captures,
                },
            );
        }
        if closed.len() == found {
            break;
        }
    }
    if closed.is_empty() {
        return None;
    }

    let mut edit = FunctionEdit::new(func.clone());
    for block in edit.blocks().collect::<Vec<_>>() {
        edit.block_mut(block).operations.retain(|operation| {
            operation
                .result_id()
                .is_none_or(|result| !closed.contains_key(&result))
        });
    }
    edit.visit_operands_mut(|operand| {
        if let mir::Value::Register(id) = operand
            && let Some(evidence) = closed.get(id)
        {
            *operand = mir::Value::Evidence(b(evidence.clone()));
        }
    });
    Some(edit.finish(env))
}

pub(super) fn bool_value(func: &Function, value: &mir::Value) -> Option<bool> {
    let literal = match value {
        mir::Value::Constant(id) => &func.constant(*id).representation,
        mir::Value::Pattern(literal) => literal,
        _ => return None,
    };
    literal.as_primitive_ty::<bool>().copied()
}

#[cfg(test)]
mod tests {
    use super::materialize_boolean_results;
    use crate::{
        CompilerSession, Location,
        format::FormatWith,
        hir::{function::ArgConvention, value::LiteralValue},
        mir::{
            self, BlockId, Function, Operation, OperationKind, ParameterId, ParameterKind,
            builder::FunctionBuilder,
            edit::FunctionEdit,
            terminator::{Terminator, TerminatorKind},
        },
        module::id::Id,
        std::{logic::bool_type, math::int_type, option::option_type},
    };

    fn boolean_materialization(value_when_true: bool) -> Function {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let bool_ty = bool_type();
        let mut builder = FunctionBuilder::new("materialize".into(), Default::default());
        let condition = builder.add_parameter(bool_ty, ParameterKind::Value);
        let result = builder.add_parameter(bool_ty, ParameterKind::Return);
        let true_value = builder.add_constant(bool_ty, LiteralValue::new_native(true), &env);
        let false_value = builder.add_constant(bool_ty, LiteralValue::new_native(false), &env);
        let entry = builder.add_block();
        let left = builder.add_block();
        let right = builder.add_block();
        let join = builder.add_block();
        let loaded_condition = mir::Value::Parameter(condition);

        builder.set_terminator(
            entry,
            Terminator::cond_br(span, loaded_condition, left, right),
        );
        builder.append_operation(
            left,
            Operation::store(
                span,
                mir::Value::Constant(if value_when_true {
                    true_value
                } else {
                    false_value
                }),
                mir::Value::Parameter(result),
            ),
        );
        builder.set_terminator(left, Terminator::goto(span, join));
        builder.append_operation(
            right,
            Operation::store(
                span,
                mir::Value::Constant(if value_when_true {
                    false_value
                } else {
                    true_value
                }),
                mir::Value::Parameter(result),
            ),
        );
        builder.set_terminator(right, Terminator::goto(span, join));
        builder.set_terminator(join, Terminator::ret(span));
        builder.finish(env)
    }

    fn variant_boolean_materialization() -> Function {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let bool_ty = bool_type();
        let mut builder = FunctionBuilder::new("materialize_variant".into(), Default::default());
        let variant = builder.add_parameter(
            option_type(int_type()),
            ParameterKind::Place(ArgConvention::Let),
        );
        let result = builder.add_parameter(bool_ty, ParameterKind::Return);
        let true_value = builder.add_constant(bool_ty, LiteralValue::new_native(true), &env);
        let false_value = builder.add_constant(bool_ty, LiteralValue::new_native(false), &env);
        let entry = builder.add_block();
        let some = builder.add_block();
        let other = builder.add_block();
        let join = builder.add_block();
        let tag = builder
            .append_operation(
                entry,
                Operation::extract_tag(span, mir::Value::Parameter(variant)),
            )
            .expect("extract_tag produces an opaque tag");
        builder.set_terminator(
            entry,
            Terminator::switch_variant(span, tag, vec![("Some".into(), some)], other),
        );
        for (block, value) in [(some, true_value), (other, false_value)] {
            builder.append_operation(
                block,
                Operation::store(
                    span,
                    mir::Value::Constant(value),
                    mir::Value::Parameter(result),
                ),
            );
            builder.set_terminator(block, Terminator::goto(span, join));
        }
        builder.set_terminator(join, Terminator::ret(span));
        builder.finish(env)
    }

    #[test]
    fn positive_boolean_materialization_stores_the_condition_directly() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let source = boolean_materialization(true);
        let optimized = materialize_boolean_results(&source)
            .expect("the materialization diamond should be rewritten");
        let rendered = optimized.format_with(&env).to_string();

        assert_eq!(optimized.blocks().count(), 1, "{rendered}");
        let block = optimized.block(optimized.entry());
        assert_eq!(
            block
                .operations()
                .iter()
                .filter(|operation| matches!(operation.kind, OperationKind::CompareEqual))
                .count(),
            0,
            "{rendered}"
        );
        assert!(
            rendered.contains("store %p0 to %p1"),
            "positive polarity should store the original condition directly:\n{rendered}"
        );
    }

    #[test]
    fn inverse_boolean_materialization_compares_with_false() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let source = boolean_materialization(false);
        let optimized = materialize_boolean_results(&source)
            .expect("the materialization diamond should be rewritten");
        let rendered = optimized.format_with(&env).to_string();

        assert_eq!(optimized.blocks().count(), 1, "{rendered}");
        let block = optimized.block(optimized.entry());
        assert!(
            matches!(block.terminator().kind, TerminatorKind::Return { .. }),
            "{rendered}"
        );
        assert_eq!(
            block
                .operations()
                .iter()
                .filter(|operation| matches!(operation.kind, OperationKind::CompareEqual))
                .count(),
            1,
            "{rendered}"
        );
        assert_eq!(
            block
                .operations()
                .iter()
                .filter(|operation| matches!(operation.kind, OperationKind::Store))
                .count(),
            1,
            "{rendered}"
        );
        assert!(
            !rendered.contains("condbr"),
            "the branch should be replaced by direct boolean materialization:\n{rendered}"
        );
        assert!(
            rendered.contains("comp_eq %p0 false"),
            "inverse polarity should compare the original condition with false:\n{rendered}"
        );
    }

    #[test]
    fn variant_boolean_materialization_compares_the_symbolic_case() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let source = variant_boolean_materialization();
        let optimized = materialize_boolean_results(&source)
            .expect("the variant materialization diamond should be rewritten");
        let rendered = optimized.format_with(&env).to_string();

        assert_eq!(optimized.blocks().count(), 1, "{rendered}");
        assert!(!rendered.contains("switch_variant"), "{rendered}");
        assert_eq!(rendered.matches("comp_eq").count(), 1, "{rendered}");
        assert!(rendered.contains("comp_eq %r0 Some"), "{rendered}");
    }

    #[test]
    fn non_literal_store_diamonds_are_left_alone() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let source = boolean_materialization(true);
        let mut altered = FunctionEdit::new(source);
        altered.block_mut(BlockId::from_index(1)).operations[0].operands[0] =
            mir::Value::Parameter(ParameterId::from_index(0));
        let altered = altered.finish(env);

        assert!(materialize_boolean_results(&altered).is_none());
    }
}
