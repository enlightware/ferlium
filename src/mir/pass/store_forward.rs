// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Forwarding through single-assignment local cells.
//!
//! MIR has no φ: a value meeting a join, or leaving an inlined callee through its `@ret`, travels
//! through a cell, and its reader sees `store %v to %cell; …; %x = load %cell`. Inlining also
//! leaves copies between cells, `memcpy %a to %b` or, for a `TrivialCopy` value, `move %a to %b`,
//! where a callee's parameter or temporary received the caller's value.
//!
//! A cell is a local `TrivialCopy` `alloca`, or a pointer slot, written exactly once and otherwise
//! only read directly: loaded, compared, or copied from. Like rustc's `SsaLocals`, such a cell is a
//! value, and a read its write dominates sees:
//! - the stored register, when the write stores a materialized register: a `load`'s uses are
//!   rewritten to it, a `comp_eq` scrutinee reads it, and a copy from the cell stores it;
//! - the stored constant, when the write stores one: a load's uses or a comparison name the
//!   constant, and a copy from the cell stores it;
//! - what another cell holds, when the write copies that cell and its own write dominates the copy:
//!   the read is forwarded to what that cell's reads are forwarded to, or reads it in place when it
//!   lives as long as the function.
//!
//! A cell of function type is also one when its single write stores a function constant, as a
//! non-capturing closure bound to a local lowers: it holds that function and no environment. A call
//! through it calls the function directly, which inlining and call-graph proofs can then see, and
//! its drop has nothing to release. A closure with captures is built by `build_closure` instead, so
//! a store of a bare function never drops an environment.
//!
//! A cell whose every read was forwarded is removed with its write and loads; being `TrivialCopy`,
//! or holding a bare function, it holds no drop obligation.
//!
//! Registers are defined once, so a store dominating a read also proves `%v` still holds the value
//! stored: `%v`'s definition dominates the store, and no path from it to the read avoids the store.
//! A cell written once reaches the same proof: if `%a`'s write dominates the copy to `%b`, and that
//! copy dominates a read of `%b`, every path from `%a`'s last write to the read passes the copy, so
//! `%a` still holds what `%b` received.

use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    local_cells::{self, Access, Allocation, LocalCells, Transfer},
    site::{OperationIndex, OperationSite},
};
use crate::{
    hir::function::ArgConvention,
    mir::{
        self, Function, Operation, OperationKind, ParameterKind,
        dominance::Dominance,
        edit::FunctionEdit,
        role::{ValueRole, ValueRoles},
        terminator::TerminatorKind,
        value::{ConstantId, ValueId},
    },
    module::{FunctionId, ModuleEnv, id::Id},
    types::type_properties::concrete_type_is_trivial_copy,
};

/// Rewrites reads of single-assignment cells to what they hold, returning `None` when there is
/// none.
pub(crate) fn forward_stored_values(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let local = LocalCells::of(func);
    if local.is_empty() {
        return None;
    }
    let census = census(func, env, &local);
    if census.cells.is_empty() {
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
    let dominates = |write: OperationSite, at: OperationSite| {
        // Within one block, a read before the write belongs to an earlier loop iteration.
        if write.block == at.block {
            write.index.as_index() < at.index.as_index()
        } else {
            dominance.dominates(write.block.as_index(), at.block.as_index())
        }
    };
    let targets = targets(func, &census, &dominates);
    if targets.is_empty() {
        return None;
    }

    // Which reads are forwarded, per cell, so that a cell with a read left keeps its storage.
    let mut forwarded_reads: FxHashMap<ValueId, usize> = FxHashMap::default();
    let mut loads: FxHashMap<ValueId, mir::Value> = FxHashMap::default();
    let mut rewrites: Vec<(OperationSite, &Target)> = Vec::new();
    // Drops of cells holding a bare function, which release nothing.
    let mut empty_drops: FxHashSet<OperationSite> = FxHashSet::default();
    for (&cell, target) in &targets {
        let write = census.cells[&cell].write;
        let local_cell = local.get(cell).expect("a census cell is a local cell");
        for cell_use in local.uses(local_cell) {
            let at = cell_use.site;
            let forwardable = match (read_kind(cell_use.access), target) {
                // A bare function is not the ordinary materialized value a load produces.
                (Some(Read::Value), Target::Function(_)) => matches!(
                    cell_use.access,
                    Access::Read(local_cells::Read::Copy) | Access::MoveOut(Transfer::Sized)
                ),
                // Loads, comparisons and copies accept either a register or a pool constant.
                (Some(Read::Value), _) => true,
                (Some(Read::Callee), Target::Function(_)) => true,
                // Only an operation in the block can be removed; an invoked drop stays.
                (Some(Read::Drop), Target::Function(_)) => !cell_use.in_terminator(func),
                _ => false,
            };
            if !forwardable || !dominates(write, at) {
                continue;
            }
            *forwarded_reads.entry(cell).or_default() += 1;
            match (cell_use.access, target) {
                (
                    Access::Read(local_cells::Read::Load),
                    Target::Register(_) | Target::Constant(_),
                ) => {
                    if let Some(result) = operation_at(func, at).result_id() {
                        let stored = match target {
                            Target::Register(id) => mir::Value::Register(*id),
                            Target::Constant(id) => mir::Value::Constant(*id),
                            _ => unreachable!(),
                        };
                        loads.insert(result, stored);
                    }
                }
                (Access::Drop, _) => {
                    empty_drops.insert(at);
                }
                _ => rewrites.push((at, target)),
            }
        }
    }
    if loads.is_empty() && rewrites.is_empty() && empty_drops.is_empty() {
        return None;
    }
    // Resolve substitution chains once, including chains ending in a constant. Each edge is
    // visited at most once before its result is cached; uses then need only one map lookup.
    // Dominance makes the chains acyclic, even when the function's block order is arbitrary.
    let mut roots: FxHashMap<ValueId, mir::Value> = FxHashMap::default();
    let mut path = Vec::new();
    for &load in loads.keys() {
        path.clear();
        let mut value = mir::Value::Register(load);
        while let mir::Value::Register(id) = value {
            if let Some(root) = roots.get(&id) {
                value = root.clone();
                break;
            }
            let Some(stored) = loads.get(&id) else {
                break;
            };
            path.push(id);
            value = stored.clone();
        }
        for &id in &path {
            roots.insert(id, value.clone());
        }
    }
    let resolve = |id: ValueId| roots.get(&id).cloned().unwrap_or(mir::Value::Register(id));

    let removed_cells: FxHashSet<ValueId> = forwarded_reads
        .into_iter()
        .filter(|(cell, forwarded)| census.cells[cell].reads == *forwarded)
        .map(|(cell, _)| cell)
        .collect();
    let mut removed: FxHashSet<OperationSite> = removed_cells
        .iter()
        .map(|cell| census.cells[cell].write)
        .collect();
    removed.extend(empty_drops);

    let mut edit = FunctionEdit::new(func.clone());
    for (at, target) in rewrites {
        // The copy into a removed cell goes with it.
        if removed.contains(&at) {
            continue;
        }
        let block = edit.block_mut(at.block);
        let operation = match block.operations.get_mut(at.index.as_index()) {
            Some(operation) => operation,
            None => match &mut block.terminator.kind {
                TerminatorKind::Invoke { operation, .. } => operation,
                _ => unreachable!("a site past the operations is the invoked one"),
            },
        };
        let stored = match target {
            Target::Register(stored) => resolve(*stored),
            Target::Function(function) => mir::Value::Function(*function),
            Target::Constant(constant) => mir::Value::Constant(*constant),
            Target::Place(place) => {
                operation.operands[0] = place.clone();
                // The place forwarded to keeps its value: a transfer of a `TrivialCopy` value out
                // of it is a copy.
                if operation.kind == OperationKind::Move {
                    operation.kind = OperationKind::Memcpy;
                }
                continue;
            }
        };
        match operation.kind {
            // The callee read through the cell is called directly.
            OperationKind::CompareEqual | OperationKind::Call { .. } => {
                operation.operands[0] = stored;
            }
            // A copy out of a cell holding a value stores that value.
            OperationKind::Memcpy | OperationKind::Move => {
                let destination = operation.operands[1].clone();
                operation.kind = OperationKind::Store;
                operation.operands = Box::new([stored, destination]);
            }
            _ => unreachable!("only reads are forwarded"),
        }
    }
    edit.visit_operands_mut(|operand| {
        if let mir::Value::Register(id) = operand
            && let Some(stored) = roots.get(id)
        {
            *operand = stored.clone();
        }
    });
    for block in func.blocks() {
        let mut index = 0;
        edit.block_mut(block).operations.retain(|operation| {
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            index += 1;
            let removed = match operation.kind {
                OperationKind::Load => operation
                    .result_id()
                    .is_some_and(|result| loads.contains_key(&result)),
                OperationKind::Alloca { .. } | OperationKind::AllocaPlace { .. } => operation
                    .result_id()
                    .is_some_and(|result| removed_cells.contains(&result)),
                _ => removed.contains(&site),
            };
            !removed
        });
    }
    Some(edit.finish_unverified())
}

/// The operation at `site`, an `invoke`'s operation taking the index past the block's operations.
fn operation_at(func: &Function, site: OperationSite) -> &Operation {
    let block = func.block(site.block);
    match block.operations().get(site.index.as_index()) {
        Some(operation) => operation,
        None => match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => operation,
            _ => unreachable!("a forwarded read past the operations is the invoked one"),
        },
    }
}

/// What the reads of a cell are forwarded to.
#[derive(Clone)]
enum Target {
    /// The materialized register the cell holds.
    Register(ValueId),
    /// A place holding the same value for as long as the cell lives: another cell, or a `let`
    /// parameter, which the callee cannot mutate.
    Place(mir::Value),
    /// The function the cell holds, without an environment.
    Function(FunctionId),
    /// The pool constant the cell holds.
    Constant(ConstantId),
}

/// How a cell's single write fills it.
enum Write {
    /// `store %register to %cell`.
    Register(ValueId),
    /// `store <function> to %cell`.
    Function(FunctionId),
    /// `store @constant to %cell`.
    Constant(ConstantId),
    /// `memcpy`/`move %source to %cell`, from a register or a parameter.
    Copy(mir::Value),
}

/// How a forwardable access reads a cell named by its first operand.
enum Read {
    /// A load, a comparison or a copy out of it.
    Value,
    /// A call through the function the cell holds.
    Callee,
    /// The drop of what the cell holds.
    Drop,
}

/// A local cell written once and otherwise only read directly.
struct Cell {
    write: OperationSite,
    how: Write,
    reads: usize,
}

struct Census<'a> {
    local: &'a LocalCells,
    cells: FxHashMap<ValueId, Cell>,
}

impl Census<'_> {
    /// The allocation of `id`, if it is a census cell.
    fn allocation(&self, id: ValueId) -> Option<&local_cells::Cell> {
        self.cells
            .contains_key(&id)
            .then(|| self.local.get(id))
            .flatten()
    }

    /// Whether `place` holds its value while `cell` lives.
    fn outlives(&self, func: &Function, place: &mir::Value, cell: ValueId) -> bool {
        match place {
            mir::Value::Parameter(id) => {
                func.parameters()[id.as_index()].kind
                    == ParameterKind::Parameter(ArgConvention::Let)
            }
            mir::Value::Register(id) => {
                let (Some(place), Some(cell)) = (self.allocation(*id), self.allocation(cell))
                else {
                    return false;
                };
                // Allocated earlier in the same block, it is released no earlier than the cell.
                place.whole_function
                    || (place.site.block == cell.site.block
                        && place.site.index.as_index() < cell.site.index.as_index())
            }
            _ => false,
        }
    }
}

/// How `access` reads a cell, if in a way that can be forwarded.
fn read_kind(access: Access) -> Option<Read> {
    match access {
        Access::Read(
            local_cells::Read::Load | local_cells::Read::Compare | local_cells::Read::Copy,
        )
        // Without a layout witness, a `move` transfers a statically sized representation.
        | Access::MoveOut(Transfer::Sized) => Some(Read::Value),
        Access::Callee => Some(Read::Callee),
        Access::Drop => Some(Read::Drop),
        _ => None,
    }
}

/// The single-assignment cells of `func`.
///
/// A whitelist over every direct use, so an unforeseen use excludes the cell rather than being
/// assumed harmless.
fn census<'a>(func: &Function, env: ModuleEnv<'_>, local: &'a LocalCells) -> Census<'a> {
    let mut cells = FxHashMap::default();
    'cells: for local_cell in local.iter() {
        let ty = match local_cell.allocation {
            Allocation::Value {
                ty,
                witnessed: false,
            } => Some(ty),
            // A pointer slot is always trivially copied.
            Allocation::Place => None,
            Allocation::Value {
                witnessed: true, ..
            } => continue,
        };
        let mut write = None;
        let mut writes = 0;
        let mut reads = 0;
        // Calls through and drops of the cell, which need it to hold a bare function.
        let mut function_reads = 0;
        for cell_use in local.uses(local_cell) {
            match cell_use.access {
                Access::Write(local_cells::Write::Store | local_cells::Write::Copy)
                | Access::MoveIn(Transfer::Sized) => {
                    writes += 1;
                    write = Some(cell_use.site);
                }
                access => match read_kind(access) {
                    Some(Read::Value) => reads += 1,
                    Some(Read::Callee | Read::Drop) => {
                        reads += 1;
                        function_reads += 1;
                    }
                    None => continue 'cells,
                },
            }
        }
        let Some(write) = write.filter(|_| writes == 1) else {
            continue;
        };
        let operation = operation_at(func, write);
        let how = match (&operation.kind, &operation.operands[0]) {
            (OperationKind::Store, mir::Value::Register(stored)) => Write::Register(*stored),
            (OperationKind::Store, mir::Value::Function(function)) => Write::Function(*function),
            (OperationKind::Store, mir::Value::Constant(constant)) => Write::Constant(*constant),
            (
                OperationKind::Memcpy | OperationKind::Move,
                source @ (mir::Value::Register(_) | mir::Value::Parameter(_)),
            ) => Write::Copy(source.clone()),
            _ => continue,
        };
        // A bare function carries no environment to copy or drop; any other value must be
        // representation-copyable, and neither called through nor dropped.
        let valid = match how {
            Write::Function(_) => true,
            _ => function_reads == 0 && ty.is_none_or(|ty| concrete_type_is_trivial_copy(ty, &env)),
        };
        if valid {
            cells.insert(local_cell.id, Cell { write, how, reads });
        }
    }
    Census { local, cells }
}

/// What the reads of each forwardable cell are forwarded to.
fn targets(
    func: &Function,
    census: &Census<'_>,
    dominates: &impl Fn(OperationSite, OperationSite) -> bool,
) -> FxHashMap<ValueId, Target> {
    // A store bridges a place register to a pointer value, which the register itself is not.
    let stores_register = census
        .cells
        .values()
        .any(|cell| matches!(cell.how, Write::Register(_)));
    let roles = stores_register.then(|| ValueRoles::derive(func));
    let materialized = |stored: ValueId| {
        roles.as_ref().is_some_and(|roles| {
            roles
                .get(&mir::Value::Register(stored), func.constants())
                .is_some_and(|role| matches!(&*role, ValueRole::Materialized(_)))
        })
    };

    struct Resolver<'a, D, M> {
        func: &'a Function,
        census: &'a Census<'a>,
        dominates: &'a D,
        materialized: M,
        targets: FxHashMap<ValueId, Option<Target>>,
    }
    impl<D, M> Resolver<'_, D, M>
    where
        D: Fn(OperationSite, OperationSite) -> bool,
        M: Fn(ValueId) -> bool,
    {
        /// `cell`'s target, through the chain of copies it was written by. The chain is finite: each
        /// source's write strictly dominates the next copy.
        fn resolve(&mut self, cell: ValueId) -> Option<Target> {
            if let Some(target) = self.targets.get(&cell) {
                return target.clone();
            }
            // Provisional, so that a malformed cycle ends.
            self.targets.insert(cell, None);
            let this = &self.census.cells[&cell];
            let target = match &this.how {
                Write::Register(stored) => {
                    (self.materialized)(*stored).then_some(Target::Register(*stored))
                }
                Write::Function(function) => Some(Target::Function(*function)),
                Write::Constant(constant) => Some(Target::Constant(*constant)),
                Write::Copy(source) => self.copied(cell, source),
            };
            self.targets.insert(cell, target.clone());
            target
        }

        /// The target of `cell`, written by a copy of `source`.
        fn copied(&mut self, cell: ValueId, source: &mir::Value) -> Option<Target> {
            let outlives = |place: &mir::Value| self.census.outlives(self.func, place, cell);
            let mir::Value::Register(source_id) = source else {
                // A `let` parameter holds its value for the whole call.
                return outlives(source).then(|| Target::Place(source.clone()));
            };
            let write = self.census.cells.get(source_id)?.write;
            if !(self.dominates)(write, self.census.cells[&cell].write) {
                return None;
            }
            match self.resolve(*source_id) {
                Some(Target::Register(stored)) => Some(Target::Register(stored)),
                Some(Target::Constant(constant)) => Some(Target::Constant(constant)),
                // Copies are of representation-copyable values, never of a function value.
                Some(Target::Function(_)) => None,
                Some(Target::Place(place)) if self.census.outlives(self.func, &place, cell) => {
                    Some(Target::Place(place))
                }
                _ => self
                    .census
                    .outlives(self.func, source, cell)
                    .then(|| Target::Place(source.clone())),
            }
        }
    }

    let mut resolver = Resolver {
        func,
        census,
        dominates,
        materialized,
        targets: FxHashMap::default(),
    };
    for &cell in census.cells.keys() {
        resolver.resolve(cell);
    }
    resolver
        .targets
        .into_iter()
        .filter_map(|(cell, target)| Some((cell, target?)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::forward_stored_values;
    use crate::{
        CompilerSession, Location,
        containers::b,
        hir::{function::ArgConvention, value::LiteralValue},
        mir::{
            Function, Operation, OperationKind, ParameterKind, Value,
            builder::FunctionBuilder,
            terminator::{Terminator, TerminatorKind},
            verify::verify_function,
        },
        std::{
            logic::bool_type,
            math::{Float, float_type},
        },
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
        let forwarded = forward_stored_values(&source, session.module_env())
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

        let forwarded = forward_stored_values(&source, session.module_env())
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
    fn constant_loads_forward_through_register_chains_and_across_blocks() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        // Preserve literal representations, including the sign of zero.
        for value in [0.75, 0.0, -0.0] {
            let mut builder = FunctionBuilder::new("constant_reads".into(), Default::default());
            let output = builder.add_parameter(float_type(), ParameterKind::Return);
            let entry = builder.add_block();
            let left = builder.add_block();
            let right = builder.add_block();
            let literal = Value::Constant(builder.add_constant(
                float_type(),
                LiteralValue::new_native(Float::new(value).unwrap()),
                &env,
            ));
            let cell = builder
                .append_operation(entry, Operation::alloca(span, float_type()))
                .unwrap();
            builder.append_operation(entry, Operation::store(span, literal.clone(), cell.clone()));
            let read = builder
                .append_operation(entry, Operation::load(span, cell.clone()))
                .unwrap();
            // A second cell stores a register which itself resolves to the literal.
            let other = builder
                .append_operation(entry, Operation::alloca(span, float_type()))
                .unwrap();
            builder.append_operation(entry, Operation::store(span, read, other.clone()));
            let condition = Value::Constant(builder.add_constant(
                bool_type(),
                LiteralValue::new_native(true),
                &env,
            ));
            builder.set_terminator(entry, Terminator::cond_br(span, condition, left, right));
            for (block, source) in [(left, cell), (right, other)] {
                let read = builder
                    .append_operation(block, Operation::load(span, source))
                    .unwrap();
                builder.append_operation(
                    block,
                    Operation::store(span, read, Value::Parameter(output)),
                );
                builder.set_terminator(block, Terminator::ret(span));
            }
            let source = builder.finish(env);
            let forwarded =
                forward_stored_values(&source, env).expect("constant reads must forward");
            assert!(forwarded.block(entry).operations().is_empty());
            for block in [left, right] {
                let operations = forwarded.block(block).operations();
                assert_eq!(operations.len(), 1);
                assert_eq!(operations[0].operands[0], literal);
                let Value::Constant(id) = operations[0].operands[0] else {
                    panic!("the stored value must be a constant");
                };
                let actual = forwarded
                    .constant(id)
                    .representation
                    .as_primitive_ty::<Float>()
                    .unwrap();
                assert_eq!(actual.into_inner().to_bits(), value.to_bits());
            }
            // Check operand roles and dominance after replacing registers with constants.
            verify_function(&forwarded, env);
            assert!(forward_stored_values(&forwarded, env).is_none());
        }
    }

    #[test]
    fn constant_forwarding_checks_dominance_and_escape() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        for case in [
            "multiple writes",
            "exposed",
            "read before write",
            "branch write",
            "loop",
        ] {
            let mut builder = FunctionBuilder::new(case.into(), Default::default());
            let entry = builder.add_block();
            let body = builder.add_block();
            let exit = builder.add_block();
            let literal = Value::Constant(builder.add_constant(
                bool_type(),
                LiteralValue::new_native(true),
                &env,
            ));
            let cell = builder
                .append_operation(entry, Operation::alloca(span, bool_type()))
                .unwrap();
            let write_block = if case == "branch write" || case == "loop" {
                body
            } else {
                entry
            };
            if case == "read before write" {
                builder.append_operation(entry, Operation::load(span, cell.clone()));
            }
            builder.append_operation(
                write_block,
                Operation::store(span, literal.clone(), cell.clone()),
            );
            if case == "branch write" {
                builder.set_terminator(
                    entry,
                    Terminator::cond_br(span, literal.clone(), body, exit),
                );
            } else {
                builder.set_terminator(entry, Terminator::goto(span, body));
            }
            if case == "multiple writes" {
                builder
                    .append_operation(body, Operation::store(span, literal.clone(), cell.clone()));
            }
            if case == "exposed" {
                builder.append_operation(
                    body,
                    Operation::black_box(span, bool_type(), cell.clone(), None),
                );
            }
            // A write in the loop dominates the read on each iteration and is safe to forward.
            let read = builder
                .append_operation(body, Operation::load(span, cell.clone()))
                .unwrap();
            let then_target = if case == "loop" { body } else { exit };
            builder.set_terminator(body, Terminator::cond_br(span, read, then_target, exit));
            builder.append_operation(exit, Operation::load(span, cell));
            builder.set_terminator(exit, Terminator::ret(span));
            // The undominated cases intentionally model invalid/uninitialized reads.
            let source = builder.finish_unverified();
            let forwarded = forward_stored_values(&source, env);
            if case == "loop" {
                let forwarded = forwarded.expect("initialized loop reads must forward");
                assert!(forwarded.block(body).operations().is_empty());
                assert!(forwarded.block(exit).operations().is_empty());
                assert!(matches!(&forwarded.block(body).terminator().kind,
                    TerminatorKind::CondBr { condition, .. } if *condition == literal));
                verify_function(&forwarded, env);
            } else if case == "branch write" || case == "read before write" {
                let forwarded = forwarded.expect("the dominated read can still forward");
                assert!(matches!(&forwarded.block(body).terminator().kind,
                    TerminatorKind::CondBr { condition, .. } if *condition == literal));
                let retained = if case == "branch write" { exit } else { entry };
                assert!(
                    forwarded
                        .block(retained)
                        .operations()
                        .iter()
                        .any(|op| op.kind == OperationKind::Load)
                );
                assert!(
                    forwarded
                        .block(entry)
                        .operations()
                        .iter()
                        .any(|op| matches!(op.kind, OperationKind::Alloca { .. }))
                );
            } else {
                assert!(forwarded.is_none(), "{case}");
            }
        }
    }

    #[test]
    fn comparisons_read_stored_constants_directly_or_through_chains() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        for chain in ["direct", "load", "copy"] {
            let mut builder = FunctionBuilder::new(chain.into(), Default::default());
            let entry = builder.add_block();
            let exit = builder.add_block();
            let literal = Value::Constant(builder.add_constant(
                bool_type(),
                LiteralValue::new_native(true),
                &env,
            ));
            let cell = builder
                .append_operation(entry, Operation::alloca(span, bool_type()))
                .unwrap();
            builder.append_operation(entry, Operation::store(span, literal.clone(), cell.clone()));
            let source = if chain == "direct" {
                cell
            } else {
                let other = builder
                    .append_operation(entry, Operation::alloca(span, bool_type()))
                    .unwrap();
                if chain == "load" {
                    let read = builder
                        .append_operation(entry, Operation::load(span, cell))
                        .unwrap();
                    builder.append_operation(entry, Operation::store(span, read, other.clone()));
                } else {
                    builder.append_operation(entry, Operation::memcpy(span, cell, other.clone()));
                }
                other
            };
            let test = builder
                .append_operation(
                    entry,
                    Operation::compare_eq(
                        span,
                        source,
                        Value::Pattern(b(LiteralValue::new_native(false))),
                    ),
                )
                .unwrap();
            builder.set_terminator(entry, Terminator::cond_br(span, test, exit, exit));
            builder.set_terminator(exit, Terminator::ret(span));
            let source = builder.finish(env);
            let forwarded =
                forward_stored_values(&source, env).expect("the comparison must forward");
            let operations = forwarded.block(entry).operations();
            assert_eq!(
                operations.len(),
                1,
                "{chain}: only the comparison must remain"
            );
            assert!(operations[0].kind == OperationKind::CompareEqual);
            assert_eq!(operations[0].operands[0], literal);
            verify_function(&forwarded, env);
        }
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
        assert!(forward_stored_values(&source, env).is_none());
    }

    #[test]
    fn a_copy_out_of_a_cell_stores_its_register() {
        let session = CompilerSession::new();
        let (source, computed) = stored_then_read(&session, true);
        let forwarded = forward_stored_values(&source, session.module_env())
            .expect("the copy and the read must be forwarded");
        let operations = forwarded.block(forwarded.entry()).operations();
        let kinds: Vec<_> = operations
            .iter()
            .map(|operation| operation.kind.clone())
            .collect();
        assert!(
            matches!(
                kinds.as_slice(),
                [
                    OperationKind::CompareEqual,
                    OperationKind::Alloca { .. },
                    OperationKind::Store
                ]
            ),
            "only the computation, the other cell and a store to it must remain"
        );
        assert_eq!(operations[2].operands[0], computed);
    }

    /// ```text
    /// b0: %a = alloca bool; %b = alloca bool; %c = alloca bool
    ///     store %argument_read to %a
    ///     br b1
    /// b1: memcpy %a to %b
    ///     move %b to %c
    ///     %y = load %c
    ///     condbr %y, …
    /// ```
    #[test]
    fn copies_between_cells_forward_to_the_stored_register_across_blocks() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("copies".into(), Default::default());
        let argument =
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let));
        let entry = builder.add_block();
        let body = builder.add_block();
        let exit = builder.add_block();
        let root = builder
            .append_operation(entry, Operation::load(span, Value::Parameter(argument)))
            .unwrap();
        let [a, b, c] = [(); 3].map(|()| {
            builder
                .append_operation(entry, Operation::alloca(span, bool_type()))
                .unwrap()
        });
        builder.append_operation(entry, Operation::store(span, root.clone(), a.clone()));
        builder.set_terminator(entry, Terminator::goto(span, body));
        builder.append_operation(body, Operation::memcpy(span, a, b.clone()));
        builder.append_operation(body, Operation::move_value(span, b, c.clone()));
        let read = builder
            .append_operation(body, Operation::load(span, c))
            .unwrap();
        builder.set_terminator(body, Terminator::cond_br(span, read, exit, exit));
        builder.set_terminator(exit, Terminator::ret(span));
        let source = builder.finish(env);

        let forwarded = forward_stored_values(&source, session.module_env())
            .expect("the chain must be forwarded");
        let body = forwarded.block(body);
        assert!(
            matches!(&body.terminator().kind, TerminatorKind::CondBr { condition, .. } if *condition == root)
        );
        assert!(body.operations().is_empty(), "the copies must be gone");
    }

    /// ```text
    /// %a = alloca bool
    /// memcpy %argument to %a
    /// %y = load %a
    /// condbr %y, …
    /// ```
    /// A `let` parameter cannot change during the call, so the read reads it in place.
    #[test]
    fn a_copy_of_a_let_parameter_reads_the_parameter() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("parameter".into(), Default::default());
        let argument =
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let));
        let entry = builder.add_block();
        let exit = builder.add_block();
        let cell = builder
            .append_operation(entry, Operation::alloca(span, bool_type()))
            .unwrap();
        builder.append_operation(
            entry,
            Operation::memcpy(span, Value::Parameter(argument), cell.clone()),
        );
        let read = builder
            .append_operation(entry, Operation::load(span, cell))
            .unwrap();
        builder.set_terminator(entry, Terminator::cond_br(span, read, exit, exit));
        builder.set_terminator(exit, Terminator::ret(span));
        let source = builder.finish(env);

        let forwarded = forward_stored_values(&source, session.module_env())
            .expect("the read must be forwarded");
        let operations = forwarded.block(forwarded.entry()).operations();
        assert_eq!(operations.len(), 1, "only the load must remain");
        assert!(operations[0].kind == OperationKind::Load);
        assert_eq!(operations[0].operands[0], Value::Parameter(argument));
    }

    /// A copy from a cell that is written again later in a loop must not be forwarded: the read
    /// would see the later value.
    #[test]
    fn a_copy_of_a_cell_written_after_it_is_left_alone() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("late_write".into(), Default::default());
        let argument =
            builder.add_parameter(bool_type(), ParameterKind::Parameter(ArgConvention::Let));
        let entry = builder.add_block();
        let body = builder.add_block();
        let exit = builder.add_block();
        let root = builder
            .append_operation(entry, Operation::load(span, Value::Parameter(argument)))
            .unwrap();
        let [a, b] = [(); 2].map(|()| {
            builder
                .append_operation(entry, Operation::alloca(span, bool_type()))
                .unwrap()
        });
        builder.set_terminator(entry, Terminator::goto(span, body));
        // The copy precedes the source's only write, which a later iteration would observe.
        builder.append_operation(body, Operation::memcpy(span, a.clone(), b.clone()));
        builder.append_operation(body, Operation::store(span, root, a));
        let read = builder
            .append_operation(body, Operation::load(span, b))
            .unwrap();
        builder.set_terminator(body, Terminator::cond_br(span, read, body, exit));
        builder.set_terminator(exit, Terminator::ret(span));
        let source = builder.finish_unverified();

        let forwarded = forward_stored_values(&source, env);
        let body = forwarded.as_ref().unwrap_or(&source).block(body);
        assert!(
            body.operations()
                .iter()
                .any(|operation| operation.kind == OperationKind::Memcpy),
            "the copy must stay"
        );
    }
}
