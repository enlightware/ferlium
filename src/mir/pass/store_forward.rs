// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Forwarding of registers through single-store local cells.
//!
//! MIR has no φ: a value meeting a join, or leaving an inlined callee through its `@ret`, travels
//! through a cell, and its reader sees `store %v to %cell; …; %x = load %cell`. When `%cell` is a
//! local `TrivialCopy` `alloca` whose only write is that store, `%v` holds a materialized value
//! rather than a place the store would bridge to a pointer, and every other use of `%cell` is a
//! direct read the store dominates, each read yields `%v`: a `load`'s uses are rewritten to `%v`,
//! and a `comp_eq` scrutinee reads `%v` directly. A cell whose every read was forwarded is removed
//! with its store and loads; being `TrivialCopy`, it holds no drop obligation.
//!
//! Registers are defined once, so a store dominating a read also proves `%v` still holds the value
//! stored: `%v`'s definition dominates the store, and no path from it to the read avoids the store.

use rustc_hash::{FxHashMap, FxHashSet};

use super::site::{OperationIndex, OperationSite};
use crate::{
    mir::{
        self, Function, OperationKind,
        dominance::Dominance,
        edit::FunctionEdit,
        role::{ValueRole, ValueRoles},
        value::ValueId,
    },
    module::{ModuleEnv, id::Id},
    types::type_properties::concrete_type_is_trivial_copy,
};

/// Rewrites reads of single-store cells to the stored register, returning `None` when there is none.
pub(crate) fn forward_stored_registers(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let cells = single_store_cells(func, env);
    if cells.is_empty() {
        return None;
    }
    let successors: Vec<Vec<usize>> = func
        .blocks()
        .map(|block| {
            func.block(block)
                .terminator()
                .successors()
                .map(|target| target.as_index())
                .collect()
        })
        .collect();
    let dominance = Dominance::of(&successors, func.entry().as_index());
    let dominates = |store: OperationSite, at: OperationSite| {
        // Within one block, a read before the store belongs to an earlier loop iteration.
        if store.block == at.block {
            store.index.as_index() < at.index.as_index()
        } else {
            dominance.dominates(store.block.as_index(), at.block.as_index())
        }
    };

    let mut loads: FxHashMap<ValueId, ValueId> = FxHashMap::default();
    let mut scrutinees = Vec::new();
    let mut forwarded_reads: FxHashMap<ValueId, usize> = FxHashMap::default();
    for block in func.blocks() {
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let at = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            let Some(mir::Value::Register(cell)) = operation.operands.first() else {
                continue;
            };
            let Some(cell_uses) = cells.get(cell) else {
                continue;
            };
            let (stored, store) = (cell_uses.stored, cell_uses.store);
            if !dominates(store, at) {
                continue;
            }
            *forwarded_reads.entry(*cell).or_default() += 1;
            match operation.kind {
                OperationKind::Load => {
                    if let Some(result) = operation.result_id() {
                        loads.insert(result, stored);
                    }
                }
                OperationKind::CompareEqual => scrutinees.push((at, stored)),
                _ => {}
            }
        }
    }
    if loads.is_empty() && scrutinees.is_empty() {
        return None;
    }
    // A stored register may itself be a forwarded load: resolve chains to their root register.
    let resolve = |mut id: ValueId| {
        while let Some(stored) = loads.get(&id) {
            id = *stored;
        }
        id
    };
    let scrutinees: Vec<_> = scrutinees
        .into_iter()
        .map(|(at, stored)| (at, resolve(stored)))
        .collect();
    let roots: FxHashMap<ValueId, ValueId> =
        loads.keys().map(|load| (*load, resolve(*load))).collect();

    let removed_cells: FxHashSet<ValueId> = forwarded_reads
        .into_iter()
        .filter(|(cell, forwarded)| cells[cell].reads == *forwarded)
        .map(|(cell, _)| cell)
        .collect();

    let mut edit = FunctionEdit::new(func.clone());
    for (at, stored) in scrutinees {
        edit.block_mut(at.block).operations[at.index.as_index()].operands[0] =
            mir::Value::Register(stored);
    }
    edit.visit_operands_mut(|operand| {
        if let mir::Value::Register(id) = operand
            && let Some(stored) = roots.get(id)
        {
            *id = *stored;
        }
    });
    for block in func.blocks() {
        edit.block_mut(block).operations.retain(|operation| {
            let removed = match operation.kind {
                OperationKind::Load => operation
                    .result_id()
                    .is_some_and(|result| loads.contains_key(&result)),
                OperationKind::Alloca { .. } => operation
                    .result_id()
                    .is_some_and(|result| removed_cells.contains(&result)),
                OperationKind::Store => matches!(
                    operation.operands[1],
                    mir::Value::Register(cell) if removed_cells.contains(&cell)
                ),
                _ => false,
            };
            !removed
        });
    }
    Some(edit.finish_unverified())
}

/// A local `TrivialCopy` cell written once, by a store of a materialized register, and otherwise
/// only read.
struct Cell {
    stored: ValueId,
    store: OperationSite,
    reads: usize,
}

/// The single-store cells of `func`.
///
/// A whitelist over every operand occurrence, so an unforeseen use excludes the cell rather than
/// being assumed harmless.
fn single_store_cells(func: &Function, env: ModuleEnv<'_>) -> FxHashMap<ValueId, Cell> {
    #[derive(Default)]
    struct Uses {
        stored: Option<(ValueId, OperationSite)>,
        writes: usize,
        reads: usize,
        opaque: bool,
    }

    // Structural gates first: only allocas receiving a register store are candidates, and types are
    // queried only for the cells the census keeps.
    let register_stores: FxHashSet<ValueId> = func
        .blocks()
        .flat_map(|block| func.block(block).operations())
        .filter_map(
            |operation| match (&operation.kind, operation.operands.as_ref()) {
                (
                    OperationKind::Store,
                    [mir::Value::Register(_), mir::Value::Register(destination)],
                ) => Some(*destination),
                _ => None,
            },
        )
        .collect();
    if register_stores.is_empty() {
        return FxHashMap::default();
    }
    let mut types = FxHashMap::default();
    let mut cells: FxHashMap<ValueId, Uses> = FxHashMap::default();
    for block in func.blocks() {
        for operation in func.block(block).operations() {
            if let OperationKind::Alloca { ty } = &operation.kind
                && let Some(result) = operation.result_id()
                && register_stores.contains(&result)
            {
                types.insert(result, *ty);
                cells.insert(result, Uses::default());
            }
        }
    }
    if cells.is_empty() {
        return FxHashMap::default();
    }
    for block in func.blocks() {
        let basic_block = func.block(block);
        for (index, operation) in basic_block.operations().iter().enumerate() {
            for (position, operand) in operation.operands.iter().enumerate() {
                let mir::Value::Register(cell) = operand else {
                    continue;
                };
                let Some(uses) = cells.get_mut(cell) else {
                    continue;
                };
                match (&operation.kind, position) {
                    (OperationKind::Store, 1) => {
                        uses.writes += 1;
                        uses.stored = match &operation.operands[0] {
                            mir::Value::Register(stored) => Some((
                                *stored,
                                OperationSite {
                                    block,
                                    index: OperationIndex::from_index(index),
                                },
                            )),
                            _ => None,
                        };
                    }
                    (OperationKind::Load | OperationKind::CompareEqual, 0) => uses.reads += 1,
                    _ => uses.opaque = true,
                }
            }
        }
        for operand in basic_block.terminator().operands() {
            if let mir::Value::Register(cell) = operand
                && let Some(uses) = cells.get_mut(cell)
            {
                uses.opaque = true;
            }
        }
    }
    let candidates: Vec<_> = cells
        .into_iter()
        .filter_map(|(cell, uses)| {
            let (stored, store) = uses.stored.filter(|_| {
                uses.writes == 1
                    && !uses.opaque
                    && uses.reads > 0
                    && concrete_type_is_trivial_copy(types[&cell], &env)
            })?;
            Some((
                cell,
                Cell {
                    stored,
                    store,
                    reads: uses.reads,
                },
            ))
        })
        .collect();
    if candidates.is_empty() {
        return FxHashMap::default();
    }
    // A store bridges a place register to a pointer value, which the register itself is not.
    let roles = ValueRoles::derive(func);
    candidates
        .into_iter()
        .filter(|(_, cell)| {
            roles
                .get(&mir::Value::Register(cell.stored), func.constants())
                .is_some_and(|role| matches!(&*role, ValueRole::Materialized(_)))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::forward_stored_registers;
    use crate::{
        CompilerSession, Location,
        containers::b,
        hir::{function::ArgConvention, value::LiteralValue},
        mir::{
            Function, Operation, OperationKind, ParameterKind, Value,
            builder::FunctionBuilder,
            terminator::{Terminator, TerminatorKind},
        },
        std::logic::bool_type,
    };

    /// ```text
    /// %cell = alloca bool
    /// %c = comp_eq %argument false
    /// store %c to %cell
    /// [memcpy %cell to %other]
    /// %read = load %cell
    /// condbr %read, …
    /// ```
    fn stored_then_read(session: &CompilerSession, copied: bool) -> (Function, Value) {
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("stored_then_read".into(), Default::default());
        let argument =
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let));
        let entry = builder.add_block();
        let exit = builder.add_block();
        let cell = builder
            .append_operation(entry, Operation::alloca(span, bool_type()))
            .unwrap();
        let computed = builder
            .append_operation(
                entry,
                Operation::compare_eq(
                    span,
                    Value::Parameter(argument),
                    Value::Pattern(b(LiteralValue::new_native(false))),
                ),
            )
            .unwrap();
        builder.append_operation(
            entry,
            Operation::store(span, computed.clone(), cell.clone()),
        );
        if copied {
            let other = builder
                .append_operation(entry, Operation::alloca(span, bool_type()))
                .unwrap();
            builder.append_operation(entry, Operation::memcpy(span, cell.clone(), other));
        }
        let read = builder
            .append_operation(entry, Operation::load(span, cell))
            .unwrap();
        builder.set_terminator(entry, Terminator::cond_br(span, read, exit, exit));
        builder.set_terminator(exit, Terminator::ret(span));
        (builder.finish(env), computed)
    }

    #[test]
    fn a_dominated_read_takes_the_stored_register_and_the_cell_goes() {
        let session = CompilerSession::new();
        let (source, computed) = stored_then_read(&session, false);
        let forwarded = forward_stored_registers(&source, session.module_env())
            .expect("the read must be forwarded");
        let entry = forwarded.block(forwarded.entry());
        assert!(
            matches!(&entry.terminator().kind, TerminatorKind::CondBr { condition, .. } if *condition == computed)
        );
        assert!(
            entry
                .operations()
                .iter()
                .all(|operation| matches!(operation.kind, OperationKind::CompareEqual)),
            "the cell, its store and its load must be gone"
        );
    }

    /// ```text
    /// %a = alloca bool; %b = alloca bool
    /// store %argument_read to %a; %x = load %a
    /// store %x to %b; %y = load %b
    /// condbr %y, …
    /// ```
    #[test]
    fn a_chain_of_cells_forwards_to_its_root() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("chain".into(), Default::default());
        let argument =
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let));
        let entry = builder.add_block();
        let exit = builder.add_block();
        let root = builder
            .append_operation(entry, Operation::load(span, Value::Parameter(argument)))
            .unwrap();
        let mut stored = root.clone();
        for _ in 0..2 {
            let cell = builder
                .append_operation(entry, Operation::alloca(span, bool_type()))
                .unwrap();
            builder.append_operation(entry, Operation::store(span, stored, cell.clone()));
            stored = builder
                .append_operation(entry, Operation::load(span, cell))
                .unwrap();
        }
        builder.set_terminator(entry, Terminator::cond_br(span, stored, exit, exit));
        builder.set_terminator(exit, Terminator::ret(span));
        let source = builder.finish(env);

        let forwarded = forward_stored_registers(&source, session.module_env())
            .expect("the chain must be forwarded");
        let entry = forwarded.block(forwarded.entry());
        assert!(
            matches!(&entry.terminator().kind, TerminatorKind::CondBr { condition, .. } if *condition == root)
        );
        assert_eq!(
            entry.operations().len(),
            1,
            "only the root load must remain"
        );
    }

    #[test]
    fn a_stored_place_is_not_forwarded() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("stored_place".into(), Default::default());
        let entry = builder.add_block();
        let place = builder
            .append_operation(entry, Operation::alloca(span, bool_type()))
            .unwrap();
        let cell = builder
            .append_operation(entry, Operation::alloca(span, bool_type()))
            .unwrap();
        builder.append_operation(entry, Operation::store(span, place, cell.clone()));
        builder.append_operation(entry, Operation::load(span, cell));
        builder.set_terminator(entry, Terminator::ret(span));
        let source = builder.finish_unverified();
        assert!(forward_stored_registers(&source, env).is_none());
    }

    #[test]
    fn a_cell_with_another_use_is_left_alone() {
        let session = CompilerSession::new();
        let (source, _) = stored_then_read(&session, true);
        assert!(forward_stored_registers(&source, session.module_env()).is_none());
    }
}
