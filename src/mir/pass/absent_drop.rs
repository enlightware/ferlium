// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Removal of drops of absent storage.
//!
//! A `drop` acts only on present storage, and does nothing on absent storage (see
//! `mir-uninit-tracking.md`). Lowering relies on that: a scope registers the drops of its locals
//! when it opens, so a failure path can drop a local nothing has initialized yet. Inlining carries
//! such drops onto the failure paths of the inlined body.
//!
//! Physical drop elaboration removes these drops, but only after semantic optimization. Before
//! that, a pass expanding a drop into its destructor, such as the managed split, would read the tag
//! of a variant never built, and refuse. A drop goes when every node it tests is absent on every
//! path to it, by the same [initialization analysis](crate::mir::initialization) as elaboration.
//!
//! One difference: in semantic MIR, a failed operation may leave what it writes partly built, such
//! as a callee's result whose variant shell it stored before failing. Only physical lowering makes
//! a failing callee clear its result. On an error edge, those places are therefore maybe live here.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    mir::{
        BlockId, Function, Operation, OperationKind,
        edit::FunctionEdit,
        initialization::{InitState, Places, Update},
    },
    module::{ModuleEnv, id::Id},
};

/// Removes the drops of storage that is absent on every path reaching them.
pub(crate) fn remove_absent_drops(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let is_drop = |kind: &OperationKind| matches!(kind, OperationKind::Drop { .. });
    if !func.blocks().any(|block| {
        func.block(block)
            .operations()
            .iter()
            .any(|op| is_drop(&op.kind))
    }) {
        return None;
    }
    let places = Places::of(func, env);
    let entries = places.analyze_with(func, |state, op, success| {
        places.transfer(state, op, success);
        if !success {
            leave_writes_maybe_live(&places, state, op);
        }
    });
    let mut absent = FxHashMap::<BlockId, FxHashSet<usize>>::default();
    for block in func.blocks() {
        let Some(mut state) = entries[block.as_index()].clone() else {
            continue;
        };
        for (index, op) in func.block(block).operations().iter().enumerate() {
            if is_drop(&op.kind) {
                let nodes = places.tested_nodes(op);
                if !nodes.is_empty()
                    && nodes
                        .iter()
                        .all(|id| state[id.as_index()] == InitState::Absent)
                {
                    absent.entry(block).or_default().insert(index);
                }
            }
            places.transfer(&mut state, op, true);
        }
    }
    if absent.is_empty() {
        return None;
    }
    let mut edit = FunctionEdit::new(func.clone());
    for (block, indices) in absent {
        let mut index = 0;
        edit.block_mut(block).operations.retain(|_| {
            index += 1;
            !indices.contains(&(index - 1))
        });
    }
    Some(edit.finish_unverified())
}

/// Marks maybe live what `op` writes when it succeeds, as a failure can leave it partly built.
fn leave_writes_maybe_live(places: &Places, state: &mut [InitState], op: &Operation) {
    for (id, update) in places.updates(op, true) {
        if matches!(update, Update::Set(InitState::Live)) {
            state[id.as_index()] = InitState::MaybeLive;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::remove_absent_drops;
    use crate::{
        CompilerSession, ExecutionTarget, Location, MirOptimization, Path,
        hir::value::LiteralValue,
        mir::{
            Function, Operation, OperationKind, ParameterKind, Value, builder::FunctionBuilder,
            terminator::Terminator, verify::verify_function,
        },
        module::{FunctionId, ModuleEnv},
        std::{logic::bool_type, math::int_type},
        types::r#type::{CallResultConvention, Type},
    };

    fn drop_count(body: &Function) -> usize {
        body.blocks()
            .flat_map(|block| body.block(block).operations())
            .filter(|op| matches!(op.kind, OperationKind::Drop { .. }))
            .count()
    }

    /// A slot dropped where it is never, sometimes or always initialized: only the never case is
    /// absent.
    #[test]
    fn only_a_drop_of_storage_absent_on_every_path_is_removed() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "pub fn dispose(x: &mut int) {}",
                "absent_drop",
                Path::single_str("absent_drop"),
            )
            .unwrap()
            .module_id;
        let source = session.expect_fresh_module(module);
        let callee = FunctionId::new(
            module,
            source.get_local_function_id("dispose".into()).unwrap(),
        );
        let env = ModuleEnv::new(source, session.raw_modules());
        let span = Location::new_synthesized();
        for (initialization, removed) in [(None, true), (Some(true), false), (Some(false), false)] {
            let mut builder =
                FunctionBuilder::new("absent_drop".into(), CallResultConvention::Value);
            let condition =
                Value::Parameter(builder.add_parameter(bool_type(), ParameterKind::Value));
            let output =
                Value::Parameter(builder.add_parameter(Type::unit(), ParameterKind::Return));
            let entry = builder.add_block();
            let initialize = builder.add_block();
            let cleanup = builder.add_block();
            let slot = builder
                .append_operation(entry, Operation::alloca(span, int_type()))
                .unwrap();
            let value = Value::Constant(builder.add_constant(
                int_type(),
                LiteralValue::new_native(1isize),
                &env,
            ));
            let unit = Value::Constant(builder.add_constant(
                Type::unit(),
                LiteralValue::new_native(()),
                &env,
            ));
            builder.set_terminator(
                entry,
                match initialization {
                    None => Terminator::goto(span, cleanup),
                    Some(true) => Terminator::cond_br(span, condition, initialize, cleanup),
                    Some(false) => Terminator::goto(span, initialize),
                },
            );
            builder.append_operation(initialize, Operation::store(span, value, slot.clone()));
            builder.set_terminator(initialize, Terminator::goto(span, cleanup));
            builder.append_operation(
                cleanup,
                Operation::drop(span, slot, Value::Function(callee), int_type()),
            );
            builder.append_operation(cleanup, Operation::store(span, unit, output));
            builder.set_terminator(cleanup, Terminator::ret(span));
            let body = builder.finish_unverified();
            match remove_absent_drops(&body, env) {
                Some(cleaned) => {
                    assert!(removed, "{initialization:?}");
                    assert_eq!(drop_count(&cleaned), 0);
                    verify_function(&cleaned, env);
                }
                None => assert!(!removed, "{initialization:?}"),
            }
        }
    }

    /// A failed callee may leave its result partly built: `construct` stores the `Some` shell
    /// before `fail` fails, so the caller's drop on that call's failure edge must stay.
    #[test]
    fn a_failed_calls_result_is_still_dropped() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        let module = session
            .compile(
                "fn fail() -> string { invalid_argument(\"failure\") }\n\
                 fn construct() -> Option<string> { Some(fail()) }\n\
                 pub fn caller() -> int { let value = construct(); 0 }",
                "absent_drop",
                Path::single_str("absent_drop"),
            )
            .unwrap()
            .module_id;
        session
            .prepare_execution_target(ExecutionTarget::Mir, module)
            .expect("MIR preparation failed");
        let source = session.expect_fresh_module(module);
        let caller = source.get_local_function_id("caller".into()).unwrap();
        let env = ModuleEnv::new(source, session.raw_modules());
        let semantic = session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .unwrap();
        let body = semantic.get(caller).unwrap();
        let rendered = body.render_with_source_map(&env).text;
        assert!(
            rendered.contains("invoke") && drop_count(body) == 2,
            "the test needs a dropped result on an error edge:\n{rendered}"
        );
        assert!(remove_absent_drops(body, env).is_none(), "{rendered}");
    }
}
