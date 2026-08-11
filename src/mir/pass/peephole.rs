// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Small local MIR rewrites.

use crate::{
    containers::b,
    hir::value::LiteralValue,
    mir::{
        self, BlockId, Function, Operation, OperationKind,
        edit::FunctionEdit,
        terminator::{Terminator, TerminatorKind},
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
    stored_when_true: bool,
    destination: mir::Value,
    join: BlockId,
}

/// Rewrites boolean materialization diamonds into one value computation and store.
///
/// The matched shape is deliberately strict:
///
/// ```text
/// condbr condition, left, right
/// left:  store true-or-false to dst; br join
/// right: store opposite      to dst; br join
/// ```
///
/// The replacement stores `condition` directly when the true arm stores `true`, or stores
/// `comp_eq condition false` for inverse polarity, then jumps to `join`.
pub(crate) fn materialize_boolean_results(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
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
        let stored_value = if rewrite.stored_when_true {
            rewrite.condition
        } else {
            let mut comparison = Operation::compare_eq(
                span,
                rewrite.condition,
                mir::Value::Pattern(b(LiteralValue::new_native(false))),
            );
            let result = edit.new_value();
            comparison.assign_result_id(Some(result));
            edit.block_mut(rewrite.block).operations.push(comparison);
            mir::Value::Register(result)
        };

        let block = edit.block_mut(rewrite.block);
        block
            .operations
            .push(Operation::store(span, stored_value, rewrite.destination));
        block.terminator = Terminator::goto(span, rewrite.join);
    }
    edit.remove_unreachable_blocks();
    edit.merge_blocks_into_predecessors();
    Some(edit.finish(env))
}

fn plan_boolean_materialization(func: &Function, block: BlockId) -> Option<BooleanMaterialization> {
    let TerminatorKind::CondBr {
        condition,
        then_target,
        else_target,
    } = &func.block(block).terminator().kind
    else {
        return None;
    };
    if then_target == else_target {
        return None;
    }

    let then_store = single_bool_store(func, *then_target)?;
    let else_store = single_bool_store(func, *else_target)?;
    if then_store.join != else_store.join
        || then_store.destination != else_store.destination
        || then_store.value == else_store.value
    {
        return None;
    }

    Some(BooleanMaterialization {
        block,
        condition: condition.clone(),
        stored_when_true: then_store.value,
        destination: then_store.destination,
        join: then_store.join,
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

fn bool_value(func: &Function, value: &mir::Value) -> Option<bool> {
    let literal = match value {
        mir::Value::Constant(id) => &func.constant(*id).representation,
        mir::Value::Pattern(literal) => literal,
        _ => return None,
    };
    literal.as_primitive_ty::<bool>().copied()
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, Location,
        format::FormatWith,
        hir::{function::ArgConvention, value::LiteralValue},
        mir::{
            self, Operation, OperationKind, ParameterKind,
            builder::FunctionBuilder,
            terminator::{Terminator, TerminatorKind},
        },
        module::id::Id,
        std::logic::bool_type,
    };

    fn boolean_materialization(value_when_true: bool) -> crate::mir::Function {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();
        let bool_ty = bool_type();
        let mut builder = FunctionBuilder::new("materialize".into(), Default::default());
        let condition =
            builder.add_parameter(bool_ty, ParameterKind::Parameter(ArgConvention::Let));
        let result = builder.add_parameter(bool_ty, ParameterKind::Return);
        let true_value = builder.add_constant(bool_ty, LiteralValue::new_native(true), &env);
        let false_value = builder.add_constant(bool_ty, LiteralValue::new_native(false), &env);
        let entry = builder.add_block();
        let left = builder.add_block();
        let right = builder.add_block();
        let join = builder.add_block();
        let loaded_condition = builder
            .append_operation(
                entry,
                Operation::load(span, mir::Value::Parameter(condition)),
            )
            .expect("load produces a materialized bool");

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

    #[test]
    fn positive_boolean_materialization_stores_the_condition_directly() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let source = boolean_materialization(true);
        let optimized = super::materialize_boolean_results(&source, env)
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
            rendered.contains("store %r0 to %p1"),
            "positive polarity should store the original condition directly:\n{rendered}"
        );
    }

    #[test]
    fn inverse_boolean_materialization_compares_with_false() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let source = boolean_materialization(false);
        let optimized = super::materialize_boolean_results(&source, env)
            .expect("the materialization diamond should be rewritten");
        let rendered = optimized.format_with(&env).to_string();

        assert_eq!(optimized.blocks().count(), 1, "{rendered}");
        let block = optimized.block(optimized.entry());
        assert!(
            matches!(block.terminator().kind, TerminatorKind::Return),
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
            rendered.contains("comp_eq %r0 false"),
            "inverse polarity should compare the original condition with false:\n{rendered}"
        );
    }

    #[test]
    fn non_literal_store_diamonds_are_left_alone() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let source = boolean_materialization(true);
        let mut altered = crate::mir::edit::FunctionEdit::new(source);
        altered
            .block_mut(crate::mir::BlockId::from_index(1))
            .operations[0]
            .operands[0] = mir::Value::Parameter(crate::mir::ParameterId::from_index(0));
        let altered = altered.finish(env);

        assert!(super::materialize_boolean_results(&altered, env).is_none());
    }
}
