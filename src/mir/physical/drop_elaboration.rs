// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Elaborate destruction while projections still name logical fields.

use std::mem;

use crate::{
    FxHashMap, FxHashSet,
    compiler::{MirArtifacts, MirOptimization},
    hir::{elaboration::bind_call_type_instantiation, value::LiteralValue},
    mir::{
        BlockId, Function, Operation, OperationKind, ParameterKind, Value,
        edit::FunctionEdit,
        pass::{
            inline::expand_cleanup,
            monomorphize::{drop_redundant_layout_witnesses, map_types},
        },
        terminator::{Terminator, TerminatorKind},
        value::StaticEvidence,
    },
    module::{FunctionId, ModuleEnv, TraitDictionaryEntry, TraitDictionaryId, id::Id},
    std::{logic::bool_type, value::variant_indirect_payload_type},
    types::{
        effects::no_effects,
        r#type::{CallImplType, FnType, Type},
        type_mapper::SimpleInstantiationMapper,
    },
};

use super::{
    initialization::{InitState, LogicalPlaceId, Places, Update},
    variant_payload_release_call,
};

use InitState::{Absent, Live, MaybeLive};

/// Partial values never cross a destructor boundary. Expand their structural cleanup here, then
/// track only initialization facts which are genuinely ambiguous at a destruction/query site.
pub(super) fn elaborate(
    mut body: Function,
    semantic: &MirArtifacts,
    env: ModuleEnv<'_>,
    mut release: impl FnMut(Type, Type) -> FunctionId,
) -> Function {
    if !body.blocks().any(|block| {
        body.block(block).operations().iter().any(|op| {
            matches!(
                op.kind,
                OperationKind::Drop { .. } | OperationKind::IsInitialized
            )
        })
    }) {
        return body;
    }
    let mut edit = FunctionEdit::new(body);
    edit.remove_unreachable_blocks();
    body = edit.finish_unverified();
    loop {
        let places = Places::of(&body, env);
        let entries = places.analyze(&body);
        let mut partial = None;
        'blocks: for block in body.blocks() {
            let Some(mut state) = entries[block.as_index()].clone() else {
                continue;
            };
            for (index, op) in body.block(block).operations().iter().enumerate() {
                if matches!(op.kind, OperationKind::Drop { .. })
                    && let Some(&id) = places.values.get(&op.operands[0])
                    && places.partial(&state, id)
                {
                    partial = Some((
                        block,
                        index,
                        op.clone(),
                        places.nodes[id.as_index()].variant,
                        state[id.as_index()],
                    ));
                    break 'blocks;
                }
                places.transfer(&mut state, op, true);
            }
        }
        let Some((block, index, op, variant, shell)) = partial else {
            return emit_flags(body, places, entries, env);
        };
        let OperationKind::Drop { ty } = op.kind else {
            unreachable!()
        };
        let (callee, mut captures) = resolve_callee(&op.operands[1], &places, env)
            .expect("partial cleanup must have a structural destructor");
        captures.extend_from_slice(&op.operands[2..]);
        // Both sources are semantic MIR: semantic optimization must preserve initialization-
        // aware field Drops unless it proves them unnecessary. Only physical elaboration may
        // turn them into DropInitialized. Specializations can exist only in optimized MIR.
        let source = if callee.module == env.current.module_id() {
            semantic.get(callee.function)
        } else {
            env.modules
                .get(callee.module)
                .and_then(|m| m.mir(MirOptimization::Enabled))
                .and_then(|m| m.get(callee.function))
        }
        .expect("partial cleanup needs a script destructor");
        assert!(
            source.blocks().all(|block| source
                .block(block)
                .operations()
                .iter()
                .all(|op| !matches!(op.kind, OperationKind::DropInitialized { .. }))),
            "partial cleanup requires a semantic destructor template"
        );
        let receiver = source
            .parameters()
            .iter()
            .find(|p| matches!(p.kind, ParameterKind::Parameter(_)))
            .unwrap();
        let mut substitution = FxHashMap::default();
        assert!(
            bind_call_type_instantiation(
                receiver.ty,
                ty,
                &mut substitution,
                &mut FxHashMap::default(),
                &mut FxHashSet::default()
            ),
            "cleanup type instantiation"
        );
        let mut template = FunctionEdit::new(source.clone());
        map_types(
            &mut template,
            &mut SimpleInstantiationMapper::new(&(substitution, FxHashMap::default())),
        );
        drop_redundant_layout_witnesses(&mut template, env);
        let template = template.finish_unverified();

        let mut edit = FunctionEdit::new(body);
        let tail = edit.block_mut(block).operations.split_off(index + 1);
        edit.block_mut(block).operations.pop();
        let continuation = edit.add_block(edit.block(block).terminator.clone());
        edit.block_mut(continuation).operations = tail;
        let cleanup = edit.add_block(Terminator::goto(op.span, continuation));
        if variant && shell != Live {
            let initialized = edit
                .append_operation(
                    block,
                    Operation::is_initialized(op.span, op.operands[0].clone()),
                )
                .expect("initialization query produces a result");
            edit.block_mut(block).terminator =
                Terminator::cond_br(op.span, initialized, cleanup, continuation);
        } else {
            edit.block_mut(block).terminator = Terminator::goto(op.span, cleanup);
        }
        let result = edit
            .append_operation(cleanup, Operation::alloca(op.span, Type::unit()))
            .expect("allocation produces a result");
        captures.extend([op.operands[0].clone(), result]);
        let call = Operation::call(
            op.span,
            Value::Function(callee),
            captures,
            CallImplType::value(FnType::new_mut_resolved(
                [(ty, true)],
                Type::unit(),
                no_effects(),
            )),
        );
        edit.block_mut(cleanup).operations.push(call);
        if variant && let Some(payload) = variant_indirect_payload_type(ty, &env) {
            let operations = variant_payload_release_call(
                &mut edit,
                release(ty, payload),
                op.operands[0].clone(),
                ty,
                op.span,
            );
            edit.block_mut(cleanup).operations.extend(operations);
        }
        edit.block_mut(cleanup)
            .operations
            .push(Operation::clear(op.span, op.operands[0].clone()));
        expand_cleanup(&mut edit, &template, cleanup, 1, env);
        edit.remove_unreachable_blocks();
        edit.reorder_blocks_in_reverse_postorder();
        body = edit.finish_unverified();
    }
}

fn dictionary(value: &Value, places: &Places) -> Option<(TraitDictionaryId, Vec<Value>)> {
    match value {
        Value::Dictionary(id) => Some((*id, vec![])),
        Value::Evidence(evidence) => match &**evidence {
            StaticEvidence::Dictionary {
                definition,
                captures,
            } => Some((
                *definition,
                captures
                    .iter()
                    .map(|c| Value::Evidence(Box::new(c.clone())))
                    .collect(),
            )),
            _ => None,
        },
        Value::Register(id) => {
            let operation = places.definitions.get(id)?;
            let OperationKind::BuildDictionary { definition, .. } = operation.kind else {
                return None;
            };
            Some((definition, operation.operands.to_vec()))
        }
        _ => None,
    }
}

fn resolve_callee(
    value: &Value,
    places: &Places,
    env: ModuleEnv<'_>,
) -> Option<(FunctionId, Vec<Value>)> {
    if let Value::Function(id) = value {
        return Some((*id, vec![]));
    }
    let Value::Register(id) = value else {
        return None;
    };
    let operation = places.definitions.get(id)?;
    let OperationKind::DictEntry { entry_index, .. } = operation.kind else {
        return None;
    };
    let (id, captures) = dictionary(&operation.operands[0], places)?;
    let definition = &env
        .module_by_id(id.module_id)?
        .get_impl_data(id.impl_id)?
        .dictionary_value;
    let TraitDictionaryEntry::Function(function) = definition.entry(entry_index);
    let captures = definition
        .project_entry_captures(entry_index, &captures, || operation.operands[0].clone())?;
    Some((FunctionId::new(id.module_id, function), captures))
}

fn tested_nodes(places: &Places, op: &Operation) -> Vec<LogicalPlaceId> {
    let Some(&id) = places.values.get(&op.operands[0]) else {
        return vec![];
    };
    if matches!(op.kind, OperationKind::IsInitialized) && places.nodes[id.as_index()].variant {
        return vec![id];
    }
    let mut nodes = vec![];
    fn visit(places: &Places, id: LogicalPlaceId, nodes: &mut Vec<LogicalPlaceId>) {
        let node = &places.nodes[id.as_index()];
        if !node.split || node.children.is_empty() {
            nodes.push(id);
            return;
        }
        if node.variant {
            nodes.push(id);
        }
        for &(_, child) in &node.children {
            visit(places, child, nodes);
        }
    }
    visit(places, id, &mut nodes);
    nodes
}

fn emit_flags(
    body: Function,
    places: Places,
    entries: Vec<Option<Vec<InitState>>>,
    env: ModuleEnv<'_>,
) -> Function {
    let mut needed = FxHashSet::default();
    for block in body.blocks() {
        let Some(mut state) = entries[block.as_index()].clone() else {
            continue;
        };
        for op in body.block(block).operations() {
            if matches!(
                op.kind,
                OperationKind::Drop { .. } | OperationKind::IsInitialized
            ) {
                let nodes = tested_nodes(&places, op);
                let any = matches!(op.kind, OperationKind::Drop { .. })
                    && places
                        .values
                        .get(&op.operands[0])
                        .is_some_and(|id| !places.nodes[id.as_index()].structural);
                let decisive = if any { Live } else { Absent };
                if !nodes.iter().any(|id| state[id.as_index()] == decisive) {
                    needed.extend(
                        nodes.into_iter().filter(|&i| {
                            state[i.as_index()] != Live && state[i.as_index()] != Absent
                        }),
                    );
                }
            }
            places.transfer(&mut state, op, true);
        }
    }
    // A flag transferred by Replace also needs the source fact, even if never queried directly.
    debug_assert!(
        body.blocks().all(|block| {
            let TerminatorKind::Invoke { operation, .. } = &body.block(block).terminator().kind
            else {
                return true;
            };
            [false, true].into_iter().all(|success| {
                places
                    .updates(operation, success)
                    .iter()
                    .all(|(_, update)| !matches!(update, Update::Copy(_)))
            })
        }),
        "flag-copy dependencies on Invoke edges must be included below"
    );
    loop {
        let before = needed.len();
        for block in body.blocks() {
            for op in body.block(block).operations() {
                for (to, from) in places.updates(op, true) {
                    if needed.contains(&to)
                        && let Update::Copy(from) = from
                    {
                        needed.insert(from);
                    }
                }
            }
        }
        if needed.len() == before {
            break;
        }
    }
    let blocks = body.blocks().collect::<Vec<_>>();
    let span = body.block(body.entry()).terminator().span;
    let mut edit = FunctionEdit::new(body);
    let true_value =
        Value::Constant(edit.add_constant(bool_type(), LiteralValue::new_native(true), &env));
    let false_value =
        Value::Constant(edit.add_constant(bool_type(), LiteralValue::new_native(false), &env));
    let mut flags = FxHashMap::default();
    let mut prologue = vec![];
    let mut query_slot = None;
    for (index, node) in places.nodes.iter().enumerate() {
        let id = LogicalPlaceId::from_index(index);
        if !needed.contains(&id) {
            continue;
        }
        let mut op = Operation::alloca(span, bool_type());
        let value = edit.assign_new_result(&mut op).unwrap();
        prologue.push(op);
        prologue.push(Operation::store(
            span,
            if node.initial == Live {
                true_value.clone()
            } else {
                false_value.clone()
            },
            value.clone(),
        ));
        flags.insert(id, value);
    }
    for block in blocks {
        let Some(mut state) = entries[block.as_index()].clone() else {
            continue;
        };
        let operations = mem::take(&mut edit.block_mut(block).operations);
        let terminator = edit.block(block).terminator.clone();
        let mut current = block;
        for mut op in operations {
            if matches!(
                op.kind,
                OperationKind::Drop { .. } | OperationKind::IsInitialized
            ) {
                let id = places
                    .values
                    .get(&op.operands[0])
                    .copied()
                    .expect("destruction must refer to a logical place");
                let any = matches!(op.kind, OperationKind::Drop { .. })
                    && !places.nodes[id.as_index()].structural;
                let nodes = tested_nodes(&places, &op);
                // A custom destructor must never silently abandon a partial receiver. Guard on
                // any ownership, leaving DropInitialized's completeness contract to diagnose it.
                // This still accepts control-flow joins of entirely live and entirely absent.
                let status = if any {
                    if nodes.iter().any(|&i| state[i.as_index()] == Live) {
                        Live
                    } else if nodes.iter().all(|&i| state[i.as_index()] == Absent) {
                        Absent
                    } else {
                        MaybeLive
                    }
                } else if matches!(op.kind, OperationKind::IsInitialized)
                    && places.nodes[id.as_index()].variant
                {
                    state[id.as_index()]
                } else {
                    places.status(&state, id)
                };
                let decisive = if any { Live } else { Absent };
                let neutral = if any { Absent } else { Live };
                let short_circuit = if any { &true_value } else { &false_value };
                let identity = if any { &false_value } else { &true_value };
                let value = if nodes.iter().any(|&i| state[i.as_index()] == decisive) {
                    short_circuit.clone()
                } else {
                    let dynamic = nodes
                        .into_iter()
                        .filter(|&i| state[i.as_index()] != neutral)
                        .collect::<Vec<_>>();
                    match dynamic.as_slice() {
                        [] => identity.clone(),
                        [id] => edit
                            .append_operation(current, Operation::load(op.span, flags[id].clone()))
                            .expect("load produces a result"),
                        _ => {
                            // Short-circuit a whole-value query (all) or ownership guard (any).
                            let result = query_slot
                                .get_or_insert_with(|| {
                                    let mut slot = Operation::alloca(op.span, bool_type());
                                    let result = edit.assign_new_result(&mut slot).unwrap();
                                    prologue.push(slot);
                                    result
                                })
                                .clone();
                            edit.block_mut(current).operations.push(Operation::store(
                                op.span,
                                identity.clone(),
                                result.clone(),
                            ));
                            let done = edit.add_block(Terminator::ret(op.span));
                            let decided = edit.add_block(Terminator::goto(op.span, done));
                            edit.block_mut(decided).operations.push(Operation::store(
                                op.span,
                                short_circuit.clone(),
                                result.clone(),
                            ));
                            for id in dynamic {
                                let present = edit
                                    .append_operation(
                                        current,
                                        Operation::load(op.span, flags[&id].clone()),
                                    )
                                    .expect("load produces a result");
                                let next = edit.add_block(Terminator::goto(op.span, done));
                                edit.block_mut(current).terminator = if any {
                                    Terminator::cond_br(op.span, present, decided, next)
                                } else {
                                    Terminator::cond_br(op.span, present, next, decided)
                                };
                                current = next;
                            }
                            edit.block_mut(current).terminator = Terminator::goto(op.span, done);
                            current = done;
                            edit.append_operation(current, Operation::load(op.span, result))
                                .expect("load produces a result")
                        }
                    }
                };
                if matches!(op.kind, OperationKind::IsInitialized) {
                    let mut load = Operation::compare_eq(
                        op.span,
                        value,
                        Value::Pattern(Box::new(LiteralValue::new_native(true))),
                    );
                    load.assign_result_id(op.result_id());
                    edit.block_mut(current).operations.push(load);
                    continue;
                }
                let OperationKind::Drop { ty } = op.kind else {
                    unreachable!()
                };
                places.transfer(&mut state, &op, true);
                // The analysis clears the whole subtree even if the shell/receiver is absent.
                // Do likewise at runtime, on both sides of the destruction guard.
                emit_updates(
                    &mut edit,
                    current,
                    &places,
                    &flags,
                    &op,
                    true,
                    &true_value,
                    &false_value,
                );
                if status == Absent {
                    continue;
                }
                let next = if status == Live {
                    None
                } else {
                    let next = edit.add_block(Terminator::ret(op.span));
                    let drop_block = edit.add_block(Terminator::goto(op.span, next));
                    edit.block_mut(current).terminator =
                        Terminator::cond_br(op.span, value, drop_block, next);
                    current = drop_block;
                    Some(next)
                };
                op.kind = OperationKind::DropInitialized { ty };
                edit.block_mut(current).operations.push(op);
                if let Some(next) = next {
                    current = next;
                }
                continue;
            }
            places.transfer(&mut state, &op, true);
            edit.block_mut(current).operations.push(op.clone());
            emit_updates(
                &mut edit,
                current,
                &places,
                &flags,
                &op,
                true,
                &true_value,
                &false_value,
            );
        }
        edit.block_mut(current).terminator = terminator.clone();
        if let TerminatorKind::Invoke {
            operation,
            normal,
            error,
        } = terminator.kind
        {
            let mut edge = |target, success| {
                if !places
                    .updates(&operation, success)
                    .iter()
                    .any(|(id, _)| flags.contains_key(id))
                {
                    return target;
                }
                let edge = edit.add_block(Terminator::goto(operation.span, target));
                emit_updates(
                    &mut edit,
                    edge,
                    &places,
                    &flags,
                    &operation,
                    success,
                    &true_value,
                    &false_value,
                );
                edge
            };
            let yes_edge = edge(normal, true);
            let no_edge = edge(error, false);
            edit.block_mut(current).terminator =
                Terminator::invoke(operation.span, operation, yes_edge, no_edge);
        }
    }
    edit.block_mut(edit.entry())
        .operations
        .splice(0..0, prologue);
    edit.reorder_blocks_in_reverse_postorder();
    edit.finish_unverified()
}

#[allow(clippy::too_many_arguments)]
fn emit_updates(
    edit: &mut FunctionEdit,
    block: BlockId,
    places: &Places,
    flags: &FxHashMap<LogicalPlaceId, Value>,
    op: &Operation,
    success: bool,
    true_value: &Value,
    false_value: &Value,
) {
    let mut writes = vec![];
    for (id, source) in places.updates(op, success) {
        let Some(flag) = flags.get(&id) else {
            continue;
        };
        let value = match source {
            Update::Copy(source) => edit
                .append_operation(block, Operation::load(op.span, flags[&source].clone()))
                .expect("load produces a result"),
            Update::Set(Live) => true_value.clone(),
            Update::Set(Absent) => false_value.clone(),
            _ => unreachable!(),
        };
        writes.push(Operation::store(op.span, value, flag.clone()));
    }
    edit.block_mut(block).operations.extend(writes);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, ExecutionTarget, Location,
        hir::{function::ArgConvention, value::VariantPayloadStorage},
        mir::{builder::FunctionBuilder, verify::verify_physical_function},
        module::Path,
        std::math::int_type,
        types::r#type::CallResultConvention,
    };

    #[test]
    fn initialization_flags_are_reserved_for_ambiguous_ownership() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        let module = session
            .compile(
                "pub fn dispose(x: &mut int) {}",
                "drop_elaboration",
                Path::single_str("drop_elaboration"),
            )
            .unwrap()
            .module_id;
        session.prepare_execution_target(ExecutionTarget::Mir, module);
        let source = session.expect_fresh_module(module);
        let callee = FunctionId::new(
            module,
            source.get_local_function_id("dispose".into()).unwrap(),
        );
        let env = ModuleEnv::new(source, session.raw_modules());
        let semantic = session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .unwrap();
        let flag_count = |body: &Function| {
            body.blocks()
                .flat_map(|b| body.block(b).operations())
                .filter(|op| matches!(op.kind, OperationKind::Alloca { ty } if ty == bool_type()))
                .count()
        };
        for conditional in [false, true] {
            let span = Location::new_synthesized();
            let mut builder = FunctionBuilder::new("guarded".into(), CallResultConvention::Value);
            let condition = Value::Parameter(
                builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let)),
            );
            let output =
                Value::Parameter(builder.add_parameter(Type::unit(), ParameterKind::Return));
            let entry = builder.add_block();
            let initialize = builder.add_block();
            let cleanup = builder.add_block();
            let condition = builder
                .append_operation(entry, Operation::load(span, condition))
                .unwrap();
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
                if conditional {
                    Terminator::cond_br(span, condition, initialize, cleanup)
                } else {
                    Terminator::goto(span, initialize)
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
            let body = elaborate(
                builder.finish_unverified(),
                semantic,
                env,
                |_, _| unreachable!(),
            );
            verify_physical_function(&body, env);
            assert_eq!(flag_count(&body), usize::from(conditional));
        }
    }

    #[test]
    fn field_drops_preserve_the_parent_completeness_check() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "pub fn dispose(x: &mut int) {} pub fn dispose_pair(x: &mut (int, int)) {}",
                "field_drop",
                Path::single_str("field_drop"),
            )
            .unwrap()
            .module_id;
        let source = session.expect_fresh_module(module);
        let callee = FunctionId::new(
            module,
            source.get_local_function_id("dispose".into()).unwrap(),
        );
        let pair_callee = FunctionId::new(
            module,
            source.get_local_function_id("dispose_pair".into()).unwrap(),
        );
        let env = ModuleEnv::new(source, session.raw_modules());
        let span = Location::new_synthesized();
        let ty = Type::tuple([int_type(); 2]);
        for initialized_drop in [false, true] {
            let mut builder =
                FunctionBuilder::new("field_drop".into(), CallResultConvention::Value);
            let parent = Value::Parameter(builder.add_parameter(ty, ParameterKind::Owned));
            let output =
                Value::Parameter(builder.add_parameter(bool_type(), ParameterKind::Return));
            let entry = builder.add_block();
            let index = Value::Constant(builder.add_constant(
                int_type(),
                LiteralValue::new_native(0isize),
                &env,
            ));
            let field = builder
                .append_operation(
                    entry,
                    Operation::product_subfield(span, parent.clone(), index, int_type(), ty, []),
                )
                .unwrap();
            let drop = if initialized_drop {
                Operation::drop_initialized
            } else {
                Operation::drop
            };
            builder.append_operation(
                entry,
                drop(span, field, Value::Function(callee), int_type()),
            );
            let query = builder
                .append_operation(entry, Operation::is_initialized(span, parent.clone()))
                .unwrap();
            builder.append_operation(entry, Operation::store(span, query, output));
            builder.append_operation(
                entry,
                Operation::drop(span, parent.clone(), Value::Function(pair_callee), ty),
            );
            builder.set_terminator(entry, Terminator::ret(span));
            let body = builder.finish_unverified();
            let mut places = Places::of(&body, env);
            let entries = places.analyze(&body);
            let mut state = entries[entry.as_index()].clone().unwrap();
            let parent = places.values[&parent];
            assert!(places.nodes[parent.as_index()].split);
            assert_eq!(places.status(&state, parent), Live);
            for op in &body.block(entry).operations()[..2] {
                places.transfer(&mut state, op, true);
            }
            assert_eq!(places.status(&state, parent), MaybeLive);
            assert!(places.partial(&state, parent));
            // Re-evaluating a projection aliases the same owner; unlike a new root it must
            // not reset a previously dropped field to live.
            places.transfer(&mut state, &body.block(entry).operations()[0], true);
            assert_eq!(places.status(&state, parent), MaybeLive);

            // For a custom destructor, partial storage is a contract violation, not an absent
            // receiver. Keep the unconditional operation so the checked executor diagnoses it.
            places.nodes[parent.as_index()].structural = false;
            let body = emit_flags(body, places, entries, env);
            assert!(body.blocks().flat_map(|b| body.block(b).operations()).any(|op|
                matches!(op.kind, OperationKind::DropInitialized { ty: dropped } if dropped == ty)
            ));
        }
    }

    #[test]
    fn loop_place_definitions_reset_initialization() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        let module = session
            .compile(
                "pub fn dispose(x: &mut int) {}",
                "loop_places",
                Path::single_str("loop_places"),
            )
            .unwrap()
            .module_id;
        session.prepare_execution_target(ExecutionTarget::Mir, module);
        let source = session.expect_fresh_module(module);
        let callee = FunctionId::new(
            module,
            source.get_local_function_id("dispose".into()).unwrap(),
        );
        let env = ModuleEnv::new(source, session.raw_modules());
        let semantic = session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .unwrap();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("loop_places".into(), CallResultConvention::Value);
        let input = Value::Parameter(builder.add_parameter(
            int_type(),
            ParameterKind::Parameter(ArgConvention::MutableRef),
        ));
        let condition = Value::Parameter(
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let)),
        );
        let output = Value::Parameter(builder.add_parameter(Type::unit(), ParameterKind::Return));
        let entry = builder.add_block();
        let repeat = builder.add_block();
        let done = builder.add_block();
        let one = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(1isize),
            &env,
        ));
        let unit =
            Value::Constant(builder.add_constant(Type::unit(), LiteralValue::new_native(()), &env));
        let pointer = builder
            .append_operation(entry, Operation::alloca_place(span, int_type()))
            .unwrap();
        builder.append_operation(
            entry,
            Operation::store(span, input.clone(), pointer.clone()),
        );
        builder.set_terminator(entry, Terminator::goto(span, repeat));
        builder.append_operation(repeat, Operation::store(span, one.clone(), input.clone()));
        let loaded = builder
            .append_operation(repeat, Operation::load(span, pointer))
            .unwrap();
        builder.append_operation(
            repeat,
            Operation::drop(span, loaded.clone(), Value::Function(callee), int_type()),
        );
        builder.append_operation(repeat, Operation::store(span, one, input));
        let again = builder
            .append_operation(repeat, Operation::load(span, condition))
            .unwrap();
        builder.set_terminator(repeat, Terminator::cond_br(span, again, repeat, done));
        builder.append_operation(done, Operation::store(span, unit, output));
        builder.set_terminator(done, Terminator::ret(span));
        let body = builder.finish_unverified();
        let places = Places::of(&body, env);
        let entries = places.analyze(&body);
        let id = places.values[&loaded];
        let mut state = entries[repeat.as_index()].clone().unwrap();
        assert_eq!(state[id.as_index()], MaybeLive);
        let load = &body.block(repeat).operations()[1];
        places.transfer(&mut state, load, false);
        assert_eq!(
            state[id.as_index()],
            MaybeLive,
            "a failing definition must not reset ownership"
        );
        places.transfer(&mut state, load, true);
        assert_eq!(state[id.as_index()], Live);
        // Fresh runtime storage starts absent every time its definition is evaluated too.
        let mut edit = FunctionEdit::new(body.clone());
        let extent =
            Value::Constant(edit.add_constant(int_type(), LiteralValue::new_native(8isize), &env));
        let allocation = edit
            .append_operation(
                repeat,
                Operation::runtime_alloc(span, int_type(), extent.clone(), extent),
            )
            .unwrap();
        let allocating_body = edit.finish_unverified();
        let allocating_places = Places::of(&allocating_body, env);
        let allocation = allocating_places.values[&allocation];
        let mut state = vec![Live; allocating_places.nodes.len()];
        allocating_places.transfer(
            &mut state,
            allocating_body.block(repeat).operations().last().unwrap(),
            true,
        );
        assert_eq!(state[allocation.as_index()], Absent);
        let body = elaborate(body, semantic, env, |_, _| unreachable!());
        verify_physical_function(&body, env);
        assert_eq!(
            body.blocks()
                .flat_map(|b| body.block(b).operations())
                .filter(|op| matches!(op.kind, OperationKind::DropInitialized { .. }))
                .count(),
            1
        );
        assert!(
            !body
                .blocks()
                .flat_map(|b| body.block(b).operations())
                .any(|op| matches!(op.kind, OperationKind::Alloca { ty } if ty == bool_type())),
            "each new pointee is live, irrespective of the previous iteration"
        );
    }

    #[test]
    fn recursive_replace_paths_are_directional_and_finite() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        let module = session
            .compile(
                "enum Chain { End, Next(Chain) } pub fn dispose(x: &mut Chain) {}",
                "replace_paths",
                Path::single_str("replace_paths"),
            )
            .unwrap()
            .module_id;
        session.prepare_execution_target(ExecutionTarget::Mir, module);
        let source = session.expect_fresh_module(module);
        let semantic = session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .unwrap();
        let ty = semantic
            .get(source.get_local_function_id("dispose".into()).unwrap())
            .unwrap()
            .parameters()[0]
            .ty;
        let env = ModuleEnv::new(source, session.raw_modules());
        let span = Location::new_synthesized();
        let mut builder =
            FunctionBuilder::new("replace_paths".into(), CallResultConvention::NoValue);
        let a = Value::Parameter(builder.add_parameter(ty, ParameterKind::Owned));
        let b = Value::Parameter(builder.add_parameter(ty, ParameterKind::Owned));
        let block = builder.add_block();
        let zero = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(0isize),
            &env,
        ));
        let child = builder
            .append_operation(
                block,
                Operation::variant_payload(span, b.clone(), zero, ty, None),
            )
            .unwrap();
        builder.append_operation(
            block,
            Operation::replace(span, a.clone(), child.clone(), None),
        );
        builder.append_operation(block, Operation::replace(span, a.clone(), b.clone(), None));
        builder.set_terminator(block, Terminator::ret(span));
        let body = builder.finish_unverified();
        // Symmetric merging grows a.next.next... forever for these two replacements.
        let places = Places::of(&body, env);
        assert_eq!(places.nodes.len(), 4);
        let a = places.values[&a];
        let b = places.values[&b];
        let child = places.values[&child];
        let a_child = places.nodes[a.as_index()].children[0].1;
        let mut state = places.nodes.iter().map(|n| n.initial).collect::<Vec<_>>();
        // A wholly absent displaced value must also clear paths known only on the receiver.
        places.set(&mut state, child, Absent);
        places.transfer(&mut state, &body.block(block).operations()[1], true);
        assert_eq!(state[a.as_index()], Absent);
        assert_eq!(state[a_child.as_index()], Absent);
        assert_eq!(state[child.as_index()], Live);
        // Restore a complete replacement before the next operation. Snapshot the displaced
        // partial state before replacing b with a complete value.
        places.set(&mut state, a, Live);
        places.set(&mut state, child, Absent);
        places.transfer(&mut state, &body.block(block).operations()[2], true);
        assert_eq!(state[a.as_index()], Live);
        assert_eq!(state[a_child.as_index()], Absent);
        assert_eq!(places.status(&state, b), Live);
    }

    #[test]
    fn invoke_edges_and_replace_chains_update_flags() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "pub fn make(x: int) -> int { idiv(1, x) }",
                "invoke_flags",
                Path::single_str("invoke_flags"),
            )
            .unwrap()
            .module_id;
        let source = session.expect_fresh_module(module);
        let callee = FunctionId::new(module, source.get_local_function_id("make".into()).unwrap());
        let env = ModuleEnv::new(source, session.raw_modules());
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("invoke_flags".into(), CallResultConvention::Value);
        let input = Value::Parameter(builder.add_parameter(int_type(), ParameterKind::Owned));
        let condition = Value::Parameter(
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let)),
        );
        let output = Value::Parameter(builder.add_parameter(bool_type(), ParameterKind::Return));
        let entry = builder.add_block();
        let attempt = builder.add_block();
        let normal = builder.add_block();
        let failed = builder.add_block();
        let join = builder.add_block();
        let one = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(1isize),
            &env,
        ));
        let x = builder
            .append_operation(entry, Operation::alloca(span, int_type()))
            .unwrap();
        let y = builder
            .append_operation(entry, Operation::alloca(span, int_type()))
            .unwrap();
        let z = builder
            .append_operation(entry, Operation::alloca(span, int_type()))
            .unwrap();
        builder.append_operation(entry, Operation::store(span, one.clone(), y.clone()));
        builder.append_operation(entry, Operation::store(span, one, z.clone()));
        let condition = builder
            .append_operation(entry, Operation::load(span, condition))
            .unwrap();
        builder.set_terminator(entry, Terminator::cond_br(span, condition, attempt, join));
        let mut call = Operation::call(
            span,
            Value::Function(callee),
            [input.clone(), x.clone()],
            CallImplType::value(FnType::new_mut_resolved(
                [(int_type(), false)],
                int_type(),
                no_effects(),
            )),
        );
        let OperationKind::Call { metadata, .. } = &mut call.kind else {
            unreachable!()
        };
        let metadata = metadata.get_or_insert_with(Default::default);
        metadata.owned_arguments.insert(0);
        builder.set_terminator(attempt, Terminator::invoke(span, call, normal, failed));
        builder.set_terminator(normal, Terminator::goto(span, join));
        builder.set_terminator(failed, Terminator::propagate_error(span));
        builder.append_operation(join, Operation::replace(span, y.clone(), x.clone(), None));
        builder.append_operation(join, Operation::replace(span, z.clone(), y.clone(), None));
        let initialized = builder
            .append_operation(join, Operation::is_initialized(span, z))
            .unwrap();
        builder.append_operation(join, Operation::is_initialized(span, input));
        builder.append_operation(join, Operation::store(span, initialized, output));
        builder.set_terminator(join, Terminator::ret(span));
        let body = builder.finish_unverified();
        let places = Places::of(&body, env);
        let entries = places.analyze(&body);
        let body = emit_flags(body, places, entries, env);
        let flags = body
            .block(body.entry())
            .operations()
            .iter()
            .filter(|op| matches!(op.kind, OperationKind::Alloca { ty } if ty == bool_type()))
            .map(|op| Value::Register(op.result_id().unwrap()))
            .collect::<FxHashSet<_>>();
        // z's query needs y's flag, which in turn needs x's; input also needs a flag because
        // the call consumes it only on the attempt path. This exercises the dependency closure.
        assert_eq!(flags.len(), 4);
        let (normal, error) = body
            .blocks()
            .find_map(|block| match body.block(block).terminator().kind {
                TerminatorKind::Invoke { normal, error, .. } => Some((normal, error)),
                _ => None,
            })
            .unwrap();
        let stores = |block| {
            body.block(block)
                .operations()
                .iter()
                .filter_map(|op| {
                    if op.kind != OperationKind::Store || !flags.contains(&op.operands[1]) {
                        return None;
                    }
                    let Value::Constant(id) = op.operands[0] else {
                        panic!("edge update must be constant")
                    };
                    Some(
                        *body
                            .constant(id)
                            .representation
                            .as_primitive_ty::<bool>()
                            .unwrap(),
                    )
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(
            stores(normal),
            [false, true],
            "consume input, initialize result"
        );
        assert_eq!(stores(error), [false], "consume input, leave result absent");
        // Every flag-to-flag transfer reads its old state before the first corresponding write.
        let copies = body
            .blocks()
            .flat_map(|b| body.block(b).operations())
            .filter(|op| matches!(op.kind, OperationKind::Load) && flags.contains(&op.operands[0]))
            .count();
        assert_eq!(copies, 4, "two Replace snapshots and two queries");
    }

    #[test]
    fn absent_variant_drop_clears_payload_flags() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        let module = session
            .compile(
                "enum Chain { End, Next(Chain) } pub fn dispose(x: &mut Chain) {}",
                "shell_flags",
                Path::single_str("shell_flags"),
            )
            .unwrap()
            .module_id;
        session.prepare_execution_target(ExecutionTarget::Mir, module);
        let source = session.expect_fresh_module(module);
        let callee = FunctionId::new(
            module,
            source.get_local_function_id("dispose".into()).unwrap(),
        );
        let ty = session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .unwrap()
            .get(callee.function)
            .unwrap()
            .parameters()[0]
            .ty;
        let env = ModuleEnv::new(source, session.raw_modules());
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("shell_flags".into(), CallResultConvention::Value);
        let parent = Value::Parameter(builder.add_parameter(ty, ParameterKind::Owned));
        let condition = Value::Parameter(
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let)),
        );
        let output = Value::Parameter(builder.add_parameter(bool_type(), ParameterKind::Return));
        let entry = builder.add_block();
        let clear = builder.add_block();
        let query = builder.add_block();
        let present = builder.add_block();
        let absent = builder.add_block();
        let zero = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(0isize),
            &env,
        ));
        let false_value = Value::Constant(builder.add_constant(
            bool_type(),
            LiteralValue::new_native(false),
            &env,
        ));
        let payload = builder
            .append_operation(
                entry,
                Operation::variant_payload(span, parent.clone(), zero, ty, None),
            )
            .unwrap();
        let condition = builder
            .append_operation(entry, Operation::load(span, condition))
            .unwrap();
        builder.set_terminator(entry, Terminator::cond_br(span, condition, clear, query));
        builder.append_operation(clear, Operation::clear(span, payload.clone()));
        builder.append_operation(clear, Operation::clear(span, parent.clone()));
        builder.set_terminator(clear, Terminator::goto(span, query));
        let shell = builder
            .append_operation(query, Operation::is_initialized(span, parent.clone()))
            .unwrap();
        builder.set_terminator(query, Terminator::cond_br(span, shell, present, absent));
        let initialized = builder
            .append_operation(present, Operation::is_initialized(span, payload.clone()))
            .unwrap();
        builder.append_operation(present, Operation::store(span, initialized, output.clone()));
        builder.set_terminator(present, Terminator::ret(span));
        builder.append_operation(
            absent,
            Operation::drop(span, parent.clone(), Value::Function(callee), ty),
        );
        builder.append_operation(absent, Operation::store(span, false_value, output.clone()));
        builder.set_terminator(absent, Terminator::ret(span));
        let body = builder.finish_unverified();
        let places = Places::of(&body, env);
        let entries = places.analyze(&body);
        let state = entries[absent.as_index()].as_ref().unwrap();
        assert_eq!(state[places.values[&parent].as_index()], Absent);
        assert_eq!(state[places.values[&payload].as_index()], MaybeLive);
        let body = emit_flags(body, places, entries, env);
        // Find the absent branch by its literal false result (block ordering is rewritten).
        let absent = body
            .blocks()
            .map(|id| body.block(id))
            .find(|block| {
                block.operations().iter().any(|op| {
                    op.kind == OperationKind::Store
                        && op.operands[1] == output
                        && matches!(op.operands[0], Value::Constant(_))
                })
            })
            .unwrap();
        assert_eq!(
            absent
                .operations()
                .iter()
                .filter(|op| op.kind == OperationKind::Store)
                .count(),
            3,
            "clear both shell and payload flags even though destruction is skipped"
        );
        assert!(
            !absent
                .operations()
                .iter()
                .any(|op| matches!(op.kind, OperationKind::DropInitialized { .. }))
        );
    }

    #[test]
    fn variant_shell_tracks_an_unprojected_payload() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        let module = session
            .compile(
                "enum Chain { End, Next(Chain) } pub fn dispose(x: &mut Chain) {}",
                "unprojected_payload",
                Path::single_str("unprojected_payload"),
            )
            .unwrap()
            .module_id;
        session.prepare_execution_target(ExecutionTarget::Mir, module);
        let source = session.expect_fresh_module(module);
        let ty = session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .unwrap()
            .get(source.get_local_function_id("dispose".into()).unwrap())
            .unwrap()
            .parameters()[0]
            .ty;
        let env = ModuleEnv::new(source, session.raw_modules());
        let span = Location::new_synthesized();
        let mut builder =
            FunctionBuilder::new("unprojected_payload".into(), CallResultConvention::NoValue);
        let replacement = Value::Parameter(builder.add_parameter(ty, ParameterKind::Owned));
        let entry = builder.add_block();
        let target = builder
            .append_operation(entry, Operation::alloca(span, ty))
            .unwrap();
        let shell = builder
            .append_operation(
                entry,
                Operation::variant(
                    span,
                    "Next".into(),
                    ty,
                    ty,
                    Some(VariantPayloadStorage::Indirect),
                    None,
                    None,
                ),
            )
            .unwrap();
        builder.append_operation(entry, Operation::store(span, shell, target.clone()));
        builder.append_operation(
            entry,
            Operation::replace(span, replacement.clone(), target.clone(), None),
        );
        builder.set_terminator(entry, Terminator::ret(span));
        let body = builder.finish_unverified();
        let places = Places::of(&body, env);
        let mut state = places.nodes.iter().map(|n| n.initial).collect::<Vec<_>>();
        for op in body.block(entry).operations() {
            places.transfer(&mut state, op, true);
        }
        let replacement = places.values[&replacement];
        assert_eq!(places.status(&state, replacement), MaybeLive);
        assert_eq!(state[replacement.as_index()], Live);
        assert_eq!(
            state[places.nodes[replacement.as_index()].children[0]
                .1
                .as_index()],
            Absent
        );
        assert_eq!(places.status(&state, places.values[&target]), Live);
    }
}
