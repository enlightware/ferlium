// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The local cells of a body and every operand naming one directly.
//!
//! Several storage passes ask the same first question about a local allocation: is every use of it
//! one whose effect on the cell they model? Each used to answer it with its own scan and its own
//! table of operation kinds. This module does the scan once per body and classifies each direct
//! operand occurrence with one [`Access`], so the passes differ only in which accesses they admit.
//!
//! A cell is an `alloca` or `alloca_place` result. A *direct* use names that register itself; a use
//! through a projection is the projection's `subfield` operand, classified [`Access::Opaque`]. The
//! classification is a description, not a policy: a pass that models an access maps it to its own
//! notion of read or write, and must treat an unrecognized one as an independent identity.
//!
//! Analysis only, and built from an immutable body: like every other fact in this pipeline, it is
//! rebuilt after a rewrite rather than maintained through one.

use std::ops::Range;

use super::{
    dataflow::call_result_operand_index,
    site::{OperationIndex, OperationSite},
};
use crate::{
    define_id_type,
    hir::function::{ArgConvention, arg_convention_for_arg},
    mir::{self, Function, Operation, OperationKind, ValueId, terminator::TerminatorKind},
    module::id::Id,
    types::r#type::Type,
};

/// How one operand occurrence uses the cell it names.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Access {
    /// Fills the whole cell without reading what it held.
    Write(Write),
    /// Observes the cell's contents without changing them.
    Read(Read),
    /// A `move` or `move_bytes` out of the cell, which leaves it moved-from unless its contents
    /// are `TrivialCopy`.
    MoveOut(Transfer),
    /// A `move` or `move_bytes` into the cell.
    MoveIn(Transfer),
    /// Changes the contents in place: a mutable call argument, `replace`, `clear`, a partial or
    /// environment drop.
    Modify,
    /// The ordinary `drop` of the cell's value.
    Drop,
    /// A call through the function value the cell holds.
    Callee,
    /// Any other use, including projection, storing the cell's address, a call's hidden operands
    /// and terminator operands. The cell must be assumed to have an independent identity.
    Opaque,
}

/// How a [`Access::Write`] fills the cell.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Write {
    /// `store value to cell`.
    Store,
    /// `memcpy place to cell`.
    Copy,
    /// The caller-provided result place of a call.
    CallResult,
    /// The destination of a `clone`.
    Clone,
    /// The destination of a `build_array`.
    BuildArray,
}

/// How a [`Access::Read`] observes the cell.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Read {
    /// `load cell`.
    Load,
    /// The scrutinee of `comp_eq`.
    Compare,
    /// `memcpy cell to place`.
    Copy,
    /// A visible call argument passed under the `Let` convention.
    Argument,
    /// Any other non-mutating reader: a tag or payload-indirection extraction, a `clone` source,
    /// an array element, a `comp_eq` pattern, an allocation or byte-move size.
    Other,
}

/// What a [`Access::MoveOut`] or [`Access::MoveIn`] transfers.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Transfer {
    /// A `move` without a layout witness: a statically sized representation.
    Sized,
    /// A `move` with a run-time layout witness.
    Witnessed,
    /// A `move_bytes`.
    Bytes,
}

/// How the operand at `position` of `operation` uses the place it names.
///
/// Fails safe: an operand slot not listed is [`Access::Opaque`].
pub(crate) fn access(operation: &Operation, position: usize) -> Access {
    match (&operation.kind, position) {
        (OperationKind::Store, 1) => Access::Write(Write::Store),
        (OperationKind::Memcpy, 0) => Access::Read(Read::Copy),
        (OperationKind::Memcpy, 1) => Access::Write(Write::Copy),
        (OperationKind::Move, 0 | 1) => {
            let transfer = if operation.operands.len() == 2 {
                Transfer::Sized
            } else {
                Transfer::Witnessed
            };
            if position == 0 {
                Access::MoveOut(transfer)
            } else {
                Access::MoveIn(transfer)
            }
        }
        (OperationKind::MoveBytes { .. }, 0) => Access::MoveOut(Transfer::Bytes),
        (OperationKind::MoveBytes { .. }, 1) => Access::MoveIn(Transfer::Bytes),
        (OperationKind::MoveBytes { .. }, 2) => Access::Read(Read::Other),
        // Preserve allocation identities: these are partial ownership transfers, not cell moves.
        (OperationKind::MoveRange { .. }, 0 | 1) => Access::Opaque,
        (OperationKind::MoveRange { .. }, 2..=7) => Access::Read(Read::Other),
        (OperationKind::Load, 0) => Access::Read(Read::Load),
        (OperationKind::CompareEqual, 0) => Access::Read(Read::Compare),
        (
            OperationKind::CompareEqual
            | OperationKind::ExtractTag
            | OperationKind::ExtractPayloadIndirection
            | OperationKind::RuntimeAlloc { .. },
            _,
        ) => Access::Read(Read::Other),
        (OperationKind::Clone { .. }, 0) => Access::Read(Read::Other),
        (OperationKind::Clone { .. }, 1) => Access::Write(Write::Clone),
        (OperationKind::BuildArray { .. }, _) => {
            if position + 1 == operation.operands.len() {
                Access::Write(Write::BuildArray)
            } else {
                Access::Read(Read::Other)
            }
        }
        (OperationKind::Drop { .. }, 0) => Access::Drop,
        (
            OperationKind::Replace
            | OperationKind::DropInitialized { .. }
            | OperationKind::Clear
            | OperationKind::DropSubscriptEnv
            | OperationKind::DropClosureEnv,
            0,
        )
        | (OperationKind::Replace, 1) => Access::Modify,
        (OperationKind::Call { .. }, 0) => Access::Callee,
        (OperationKind::Call { ty, .. }, _) => {
            // The layout is `[callee, extras.., args.., ret]`; see `dataflow::CallOperands`.
            let Some(result) = call_result_operand_index(&operation.operands, ty) else {
                return Access::Opaque;
            };
            let arguments = result - ty.fn_ty.args.len();
            if position == result {
                Access::Write(Write::CallResult)
            } else if let Some(argument) = position.checked_sub(arguments) {
                match arg_convention_for_arg(&ty.fn_ty.args[argument]) {
                    ArgConvention::Let => Access::Read(Read::Argument),
                    ArgConvention::MutableRef => Access::Modify,
                }
            } else {
                Access::Opaque
            }
        }
        _ => Access::Opaque,
    }
}

/// What a cell's allocation reserves.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Allocation {
    /// `alloca ty`, statically sized unless it reads a run-time layout witness.
    Value { ty: Type, witnessed: bool },
    /// `alloca_place`: a slot holding a pointer.
    Place,
}

/// One local allocation.
#[derive(Debug)]
pub(crate) struct Cell {
    pub(crate) id: ValueId,
    pub(crate) site: OperationSite,
    pub(crate) allocation: Allocation,
    /// Allocated in the entry block before any stack mark, so that no `stack_restore` releases it.
    pub(crate) whole_function: bool,
    uses: Range<CellUseId>,
}

/// One operand naming a cell directly.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CellUse {
    /// The operation; an `invoke`'s operation, and the operands of any other terminator, take the
    /// index one past the block's last operation.
    pub(crate) site: OperationSite,
    pub(crate) access: Access,
}

impl CellUse {
    /// Whether this use belongs to its block's terminator, including an `invoke`'s operation.
    pub(crate) fn in_terminator(&self, func: &Function) -> bool {
        self.site.index.as_index() == func.block(self.site.block).operations().len()
    }
}

define_id_type!(
    /// The position of a cell in its [`LocalCells`].
    CellId
);

define_id_type!(
    /// The position of a use in its [`LocalCells`], which groups each cell's uses contiguously.
    CellUseId
);

/// Every local cell of a body, with the direct uses of each.
pub(crate) struct LocalCells {
    /// The cell each register allocates, if any.
    index: Vec<Option<CellId>>,
    cells: Vec<Cell>,
    uses: Vec<CellUse>,
}

impl LocalCells {
    pub(crate) fn of(func: &Function) -> Self {
        Self::of_matching(func, |_, _| true)
    }

    /// The cells `keep` selects. A pass interested in a few allocations avoids recording the uses
    /// of every other one.
    pub(crate) fn of_matching(
        func: &Function,
        mut keep: impl FnMut(ValueId, &Allocation) -> bool,
    ) -> Self {
        let mut cells = Vec::new();
        for block in func.blocks() {
            let mut marked = false;
            for (position, operation) in func.block(block).operations().iter().enumerate() {
                let allocation = match &operation.kind {
                    OperationKind::Alloca { ty } => Allocation::Value {
                        ty: *ty,
                        witnessed: !operation.operands.is_empty(),
                    },
                    OperationKind::AllocaPlace { .. } => Allocation::Place,
                    OperationKind::StackSave => {
                        marked = true;
                        continue;
                    }
                    _ => continue,
                };
                let id = operation.result_id().expect("an allocation has a result");
                if !keep(id, &allocation) {
                    continue;
                }
                cells.push(Cell {
                    id,
                    site: OperationSite {
                        block,
                        index: OperationIndex::from_index(position),
                    },
                    allocation,
                    whole_function: block == func.entry() && !marked,
                    uses: CellUseId::from_index(0)..CellUseId::from_index(0),
                });
            }
        }
        if cells.is_empty() {
            return Self {
                index: Vec::new(),
                cells,
                uses: Vec::new(),
            };
        }
        let registers = cells.iter().map(|cell| cell.id.as_index()).max().unwrap() + 1;
        let mut index = vec![None; registers];
        for (position, cell) in cells.iter().enumerate() {
            index[cell.id.as_index()] = Some(CellId::from_index(position));
        }

        // Collect in program order, then group by cell with a counting sort that keeps that order.
        let mut found: Vec<(CellId, CellUse)> = Vec::new();
        // Only an operand naming a cell is classified.
        let mut note =
            |operands: &[mir::Value], site: OperationSite, classify: &dyn Fn(usize) -> Access| {
                for (position, operand) in operands.iter().enumerate() {
                    if let mir::Value::Register(id) = operand
                        && let Some(&Some(cell)) = index.get(id.as_index())
                    {
                        let access = classify(position);
                        found.push((cell, CellUse { site, access }));
                    }
                }
            };
        for block in func.blocks() {
            let basic_block = func.block(block);
            let operations = basic_block.operations();
            for (position, operation) in operations.iter().enumerate() {
                let site = OperationSite {
                    block,
                    index: OperationIndex::from_index(position),
                };
                note(&operation.operands, site, &|position| {
                    access(operation, position)
                });
            }
            let site = OperationSite {
                block,
                index: OperationIndex::from_index(operations.len()),
            };
            let terminator = basic_block.terminator();
            if let TerminatorKind::Invoke { operation, .. } = &terminator.kind {
                note(&operation.operands, site, &|position| {
                    access(operation, position)
                });
            } else {
                note(terminator.operands(), site, &|_| Access::Opaque);
            }
        }
        // Each range first extends from zero over its count, then moves to its place and empties,
        // then advances as uses are placed.
        let advance =
            |id: &mut CellUseId, by: usize| *id = CellUseId::from_index(id.as_index() + by);
        for (cell, _) in &found {
            advance(&mut cells[cell.as_index()].uses.end, 1);
        }
        let mut start = CellUseId::from_index(0);
        for cell in &mut cells {
            let count = cell.uses.end.as_index();
            cell.uses = start..start;
            advance(&mut start, count);
        }
        let placeholder = CellUse {
            site: cells[0].site,
            access: Access::Opaque,
        };
        let mut uses = vec![placeholder; found.len()];
        for (cell, found) in found {
            let range = &mut cells[cell.as_index()].uses;
            uses[range.end.as_index()] = found;
            advance(&mut range.end, 1);
        }
        Self { index, cells, uses }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Every cell, in block and operation order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = &Cell> {
        self.cells.iter()
    }

    /// The cell `id` allocates, if it is one.
    pub(crate) fn get(&self, id: ValueId) -> Option<&Cell> {
        self.position(id).map(|cell| &self.cells[cell.as_index()])
    }

    /// The position of the cell `id` allocates in [`iter`](Self::iter), if it is one.
    pub(crate) fn position(&self, id: ValueId) -> Option<CellId> {
        self.index.get(id.as_index()).copied().flatten()
    }

    /// The direct uses of `cell`, in block and operation order.
    pub(crate) fn uses(&self, cell: &Cell) -> &[CellUse] {
        &self.uses[cell.uses.start.as_index()..cell.uses.end.as_index()]
    }
}

#[cfg(test)]
mod tests {
    use super::{Access, LocalCells, Read, Transfer, Write};
    use crate::{
        CompilerSession, Location,
        hir::value::LiteralValue,
        mir::{self, Operation, builder::FunctionBuilder, terminator::Terminator},
        std::math::int_type,
    };

    #[test]
    fn uses_are_grouped_per_cell_in_program_order() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("cells".into(), Default::default());
        let block = builder.add_block();
        let mut alloca = || {
            builder
                .append_operation(block, Operation::alloca(span, int_type()))
                .unwrap()
        };
        let first = alloca();
        let second = alloca();
        let constant = builder.add_constant(int_type(), LiteralValue::new_native(1isize), &env);
        builder.append_operation(
            block,
            Operation::store(span, mir::Value::Constant(constant), first.clone()),
        );
        let value = builder
            .append_operation(block, Operation::load(span, first.clone()))
            .unwrap();
        builder.append_operation(block, Operation::store(span, value, second.clone()));
        builder.append_operation(
            block,
            Operation::memcpy(span, second.clone(), first.clone()),
        );
        builder.append_operation(
            block,
            Operation::move_value(span, first.clone(), second.clone()),
        );
        builder.set_terminator(block, Terminator::ret(span));
        let func = builder.finish(env);

        let cells = LocalCells::of(&func);
        let accesses = |cell: &mir::Value| {
            let mir::Value::Register(id) = cell else {
                unreachable!("an alloca result is a register")
            };
            let cell = cells.get(*id).unwrap();
            assert!(cell.whole_function);
            cells
                .uses(cell)
                .iter()
                .map(|u| u.access)
                .collect::<Vec<_>>()
        };
        assert_eq!(
            accesses(&first),
            [
                Access::Write(Write::Store),
                Access::Read(Read::Load),
                Access::Write(Write::Copy),
                Access::MoveOut(Transfer::Sized),
            ]
        );
        assert_eq!(
            accesses(&second),
            [
                Access::Write(Write::Store),
                Access::Read(Read::Copy),
                Access::MoveIn(Transfer::Sized),
            ]
        );
    }
}
