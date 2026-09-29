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
//! - the stored constant, when the write stores one: a copy from the cell stores it;
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

use super::site::{OperationIndex, OperationSite};
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
pub(crate) fn forward_stored_registers(func: &Function, env: ModuleEnv<'_>) -> Option<Function> {
    let census = census(func, env);
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
    let mut loads: FxHashMap<ValueId, ValueId> = FxHashMap::default();
    let mut rewrites: Vec<(OperationSite, &Target)> = Vec::new();
    // Drops of cells holding a bare function, which release nothing.
    let mut empty_drops: FxHashSet<OperationSite> = FxHashSet::default();
    for (at, operation) in sites(func) {
        let Some(mir::Value::Register(cell)) = operation.operands.first() else {
            continue;
        };
        let Some(target) = targets.get(cell) else {
            continue;
        };
        let forwardable = match (read_kind(&operation.kind, operation.operands.len()), target) {
            // Only copies out of it; a load's register cannot become a pool constant.
            (Some(Read::Value), Target::Function(_) | Target::Constant(_)) => {
                matches!(operation.kind, OperationKind::Memcpy | OperationKind::Move)
            }
            (Some(Read::Value), _) => true,
            (Some(Read::Callee), Target::Function(_)) => true,
            // Only an operation in the block can be removed; an invoked drop stays.
            (Some(Read::Drop), Target::Function(_)) => {
                at.index.as_index() < func.block(at.block).operations().len()
            }
            _ => false,
        };
        if !forwardable || !dominates(census.cells[cell].write, at) {
            continue;
        }
        *forwarded_reads.entry(*cell).or_default() += 1;
        match (&operation.kind, target) {
            (OperationKind::Load, Target::Register(stored)) => {
                if let Some(result) = operation.result_id() {
                    loads.insert(result, *stored);
                }
            }
            (OperationKind::Drop { .. }, _) => {
                empty_drops.insert(at);
            }
            _ => rewrites.push((at, target)),
        }
    }
    if loads.is_empty() && rewrites.is_empty() && empty_drops.is_empty() {
        return None;
    }
    // A stored register may itself be a forwarded load: resolve chains to their root register.
    let resolve = |mut id: ValueId| {
        while let Some(stored) = loads.get(&id) {
            id = *stored;
        }
        id
    };
    let roots: FxHashMap<ValueId, ValueId> =
        loads.keys().map(|load| (*load, resolve(*load))).collect();

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
            Target::Register(stored) => mir::Value::Register(resolve(*stored)),
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
            *id = *stored;
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

/// Every operation with its site, an `invoke` terminator's one following the block's operations.
fn sites(func: &Function) -> impl Iterator<Item = (OperationSite, &Operation)> {
    func.blocks().flat_map(move |block| {
        let basic_block = func.block(block);
        let invoked = match &basic_block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => Some(operation),
            _ => None,
        };
        basic_block
            .operations()
            .iter()
            .chain(invoked)
            .enumerate()
            .map(move |(index, operation)| {
                let site = OperationSite {
                    block,
                    index: OperationIndex::from_index(index),
                };
                (site, operation)
            })
    })
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
    /// `memcpy`/`move %source to %cell`.
    Copy(mir::Value),
    /// Anything else, which a read can only see through the cell itself.
    Other,
}

/// How an operation reads a cell named by its first operand.
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
    alloca: OperationSite,
    write: OperationSite,
    how: Write,
    reads: usize,
}

struct Census {
    cells: FxHashMap<ValueId, Cell>,
    /// The cells allocated for the whole function: in the entry block, before any stack mark.
    whole_function: FxHashSet<ValueId>,
}

impl Census {
    /// Whether `place` holds its value while `cell` lives.
    fn outlives(&self, func: &Function, place: &mir::Value, cell: ValueId) -> bool {
        match place {
            mir::Value::Parameter(id) => {
                func.parameters()[id.as_index()].kind
                    == ParameterKind::Parameter(ArgConvention::Let)
            }
            mir::Value::Register(id) => {
                let (Some(place), Some(cell)) = (self.cells.get(id), self.cells.get(&cell)) else {
                    return false;
                };
                // Allocated earlier in the same block, it is released no earlier than the cell.
                self.whole_function.contains(id)
                    || (place.alloca.block == cell.alloca.block
                        && place.alloca.index.as_index() < cell.alloca.index.as_index())
            }
            _ => false,
        }
    }
}

/// How `kind`, with a cell as its first operand, reads it, if in a way that can be forwarded.
fn read_kind(kind: &OperationKind, operand_count: usize) -> Option<Read> {
    match kind {
        OperationKind::Load | OperationKind::CompareEqual | OperationKind::Memcpy => {
            Some(Read::Value)
        }
        // Without a layout witness, a `move` transfers a statically sized representation.
        OperationKind::Move if operand_count == 2 => Some(Read::Value),
        OperationKind::Call { .. } => Some(Read::Callee),
        OperationKind::Drop { .. } => Some(Read::Drop),
        _ => None,
    }
}

/// The single-assignment cells of `func`.
///
/// A whitelist over every operand occurrence, so an unforeseen use excludes the cell rather than
/// being assumed harmless.
fn census(func: &Function, env: ModuleEnv<'_>) -> Census {
    #[derive(Default)]
    struct Uses {
        alloca: Option<OperationSite>,
        write: Option<(Write, OperationSite)>,
        writes: usize,
        reads: usize,
        /// Calls through and drops of the cell, which need it to hold a bare function.
        function_reads: usize,
        opaque: bool,
    }

    let empty = || Census {
        cells: FxHashMap::default(),
        whole_function: FxHashSet::default(),
    };
    // Structural gate first: only allocas receiving a register or function store, or a copy, are
    // candidates, and types are queried only for the cells the census keeps.
    let written: FxHashSet<ValueId> = func
        .blocks()
        .flat_map(|block| func.block(block).operations())
        .filter_map(
            |operation| match (&operation.kind, operation.operands.as_ref()) {
                (
                    OperationKind::Store,
                    [
                        mir::Value::Register(_) | mir::Value::Function(_) | mir::Value::Constant(_),
                        mir::Value::Register(cell),
                    ],
                )
                | (
                    OperationKind::Memcpy | OperationKind::Move,
                    [
                        mir::Value::Register(_) | mir::Value::Parameter(_),
                        mir::Value::Register(cell),
                    ],
                ) => Some(*cell),
                _ => None,
            },
        )
        .collect();
    if written.is_empty() {
        return empty();
    }
    let mut types = FxHashMap::default();
    let mut uses: FxHashMap<ValueId, Uses> = FxHashMap::default();
    let mut whole_function = FxHashSet::default();
    for block in func.blocks() {
        let mut marked = false;
        for (index, operation) in func.block(block).operations().iter().enumerate() {
            let (ty, result) = match (&operation.kind, operation.result_id()) {
                (OperationKind::Alloca { ty }, Some(result)) if operation.operands.is_empty() => {
                    (Some(*ty), result)
                }
                // A pointer slot is always trivially copied.
                (OperationKind::AllocaPlace { .. }, Some(result)) => (None, result),
                (OperationKind::StackSave, _) => {
                    marked = true;
                    continue;
                }
                _ => continue,
            };
            if !written.contains(&result) {
                continue;
            }
            if let Some(ty) = ty {
                types.insert(result, ty);
            }
            if block == func.entry() && !marked {
                whole_function.insert(result);
            }
            uses.insert(
                result,
                Uses {
                    alloca: Some(OperationSite {
                        block,
                        index: OperationIndex::from_index(index),
                    }),
                    ..Uses::default()
                },
            );
        }
    }
    if uses.is_empty() {
        return empty();
    }
    for (site, operation) in sites(func) {
        let copy = matches!(
            read_kind(&operation.kind, operation.operands.len()),
            Some(Read::Value)
        ) && matches!(operation.kind, OperationKind::Memcpy | OperationKind::Move);
        for (position, operand) in operation.operands.iter().enumerate() {
            let mir::Value::Register(cell) = operand else {
                continue;
            };
            let Some(cell_uses) = uses.get_mut(cell) else {
                continue;
            };
            match (&operation.kind, position) {
                (OperationKind::Store, 1) => {
                    cell_uses.writes += 1;
                    let how = match &operation.operands[0] {
                        mir::Value::Register(stored) => Write::Register(*stored),
                        mir::Value::Function(function) => Write::Function(*function),
                        mir::Value::Constant(constant) => Write::Constant(*constant),
                        _ => Write::Other,
                    };
                    cell_uses.write = Some((how, site));
                }
                (OperationKind::Memcpy | OperationKind::Move, 1) if copy => {
                    cell_uses.writes += 1;
                    cell_uses.write = Some((Write::Copy(operation.operands[0].clone()), site));
                }
                (kind, 0) => match read_kind(kind, operation.operands.len()) {
                    Some(Read::Value) => cell_uses.reads += 1,
                    Some(Read::Callee | Read::Drop) => {
                        cell_uses.reads += 1;
                        cell_uses.function_reads += 1;
                    }
                    None => cell_uses.opaque = true,
                },
                _ => cell_uses.opaque = true,
            }
        }
    }
    for block in func.blocks() {
        let terminator = func.block(block).terminator();
        if matches!(terminator.kind, TerminatorKind::Invoke { .. }) {
            continue;
        }
        for operand in terminator.operands() {
            if let mir::Value::Register(cell) = operand
                && let Some(cell_uses) = uses.get_mut(cell)
            {
                cell_uses.opaque = true;
            }
        }
    }
    let cells: FxHashMap<ValueId, Cell> = uses
        .into_iter()
        .filter_map(|(cell, uses)| {
            if uses.writes != 1 || uses.opaque {
                return None;
            }
            let (how, write) = uses.write?;
            // A bare function carries no environment to copy or drop; any other value must be
            // representation-copyable, and neither called through nor dropped.
            let valid = match how {
                Write::Function(_) => true,
                _ => {
                    uses.function_reads == 0
                        && types
                            .get(&cell)
                            .is_none_or(|ty| concrete_type_is_trivial_copy(*ty, &env))
                }
            };
            valid.then_some((
                cell,
                Cell {
                    alloca: uses.alloca?,
                    write,
                    how,
                    reads: uses.reads,
                },
            ))
        })
        .collect();
    let whole_function = whole_function
        .into_iter()
        .filter(|cell| cells.contains_key(cell))
        .collect();
    Census {
        cells,
        whole_function,
    }
}

/// What the reads of each forwardable cell are forwarded to.
fn targets(
    func: &Function,
    census: &Census,
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
        census: &'a Census,
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
                Write::Other => None,
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
    fn a_copy_out_of_a_cell_stores_its_register() {
        let session = CompilerSession::new();
        let (source, computed) = stored_then_read(&session, true);
        let forwarded = forward_stored_registers(&source, session.module_env())
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

        let forwarded = forward_stored_registers(&source, session.module_env())
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

        let forwarded = forward_stored_registers(&source, session.module_env())
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

        let forwarded = forward_stored_registers(&source, env);
        let body = forwarded.as_ref().unwrap_or(&source).block(body);
        assert!(
            body.operations()
                .iter()
                .any(|operation| operation.kind == OperationKind::Memcpy),
            "the copy must stay"
        );
    }
}
