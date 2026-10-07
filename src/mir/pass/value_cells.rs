// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Local cells that behave as values: Ferlium's analogue of rustc's `SsaLocals`.
//!
//! MIR has no φ and passes scalars by place, so a value computed once and read later travels
//! through a cell: `store %v to %cell`, a constant stored to become a call operand, or a call's
//! result place. Such a cell is a value when one definition fills it whole, that definition
//! dominates every other use, and every other use only observes the contents. A pass may then
//! treat each read as the definition's value instead of reasoning about the cell's memory.
//!
//! The verdict is a whitelist over the [`LocalCells`] classification. Admitted reads are loads,
//! `comp_eq` scrutinees, copies out, `move`s out of statically sized contents, and visible `Let`
//! call arguments, which the callee may neither mutate nor retain. A cell defined by storing a
//! bare function may also be called through and dropped: it holds no environment. Any other value
//! must be `TrivialCopy`, so a read never transfers ownership and the cell carries no drop
//! obligation.
//!
//! Dominance is per block, and in program order within one; a use before the definition in its
//! block belongs to an earlier iteration and disqualifies the cell. A cell allocated inside a loop
//! is a value within each iteration; moving its definition across iterations is the consumer's
//! proof, which must also respect the stack region releasing it.
//!
//! An invoked call's result is available only on its success edge, which block dominance does not
//! distinguish, so a result place of an `invoke` is not a definition.

use super::{
    local_cells::{self, Access, Allocation, Cell, CellId, CellUse, LocalCells, Transfer},
    site::OperationSite,
};
use crate::{
    mir::{
        self, Function, Operation, OperationKind,
        dominance::Dominance,
        terminator::TerminatorKind,
        value::{ConstantId, ValueId},
    },
    module::{FunctionId, ModuleEnv, id::Id},
    types::{r#type::Type, type_properties::concrete_type_is_trivial_copy},
};

/// What fills a value cell.
#[derive(Clone, Debug)]
pub(crate) enum Definition {
    /// `store %register to %cell`.
    Register(ValueId),
    /// `store <function> to %cell`: a bare function without an environment.
    Function(FunctionId),
    /// `store @constant to %cell`.
    Constant(ConstantId),
    /// `memcpy`/`move %source to %cell`, from a register or a parameter. The source may change
    /// after the copy; the cell keeps what it received.
    Copy(mir::Value),
    /// The result place of a call operation.
    CallResult,
}

/// A local cell holding one value for its whole lifetime.
#[derive(Debug)]
pub(crate) struct ValueCell {
    pub(crate) id: ValueId,
    /// The defining operation.
    pub(crate) site: OperationSite,
    pub(crate) definition: Definition,
    /// The cell's position in its [`LocalCells`].
    position: CellId,
}

/// The value cells of a body.
pub(crate) struct ValueCells<'a> {
    local: &'a LocalCells,
    /// In [`LocalCells`] order.
    cells: Vec<ValueCell>,
}

impl<'a> ValueCells<'a> {
    /// The value cells among `local` every use of which `admit` accepts, including the
    /// definition's. A consumer that cannot use some accesses rejects their cells at the first such
    /// use, before the type query and dominance; dominance is not requested when no cell remains.
    pub(crate) fn of_matching<'d>(
        func: &Function,
        env: ModuleEnv<'_>,
        local: &'a LocalCells,
        admit: impl Fn(Access) -> bool,
        dominance: impl FnOnce() -> &'d Dominance,
    ) -> Self {
        let mut candidates: Vec<_> = local
            .iter()
            .enumerate()
            .filter_map(|(position, cell)| {
                let uses = local.uses(cell);
                shape(func, cell, CellId::from_index(position), uses, &admit)
            })
            .filter(|shape| shape.copyable(env))
            .map(|shape| (shape.value, shape.index))
            .collect();
        if !candidates.is_empty() {
            let dominance = dominance();
            candidates.retain(|(value, definition)| {
                let cell = local.get(value.id).expect("a candidate is a local cell");
                // A use in the defining operation itself, such as an in-place call argument, is
                // not dominated by it.
                local
                    .uses(cell)
                    .iter()
                    .enumerate()
                    .all(|(index, cell_use)| {
                        index == *definition || dominates(dominance, value.site, cell_use.site)
                    })
            });
        }
        let cells = candidates.into_iter().map(|(value, _)| value).collect();
        Self { local, cells }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Every value cell, in [`LocalCells`] order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = &ValueCell> {
        self.cells.iter()
    }

    /// The value cell `id` allocates, if it is one.
    pub(crate) fn get(&self, id: ValueId) -> Option<&ValueCell> {
        let position = self.local.position(id)?;
        let index = self
            .cells
            .binary_search_by_key(&position.as_index(), |cell| cell.position.as_index())
            .ok()?;
        Some(&self.cells[index])
    }

    /// The uses of `cell` other than its definition.
    pub(crate) fn reads(&self, cell: &ValueCell) -> usize {
        let local = self
            .local
            .get(cell.id)
            .expect("a value cell is a local cell");
        self.local.uses(local).len() - 1
    }
}

/// Whether the operation at `definition` executes before the one at `at` on every path reaching it.
///
/// Within one block, a use before the definition belongs to an earlier iteration.
pub(crate) fn dominates(
    dominance: &Dominance,
    definition: OperationSite,
    at: OperationSite,
) -> bool {
    if definition.block == at.block {
        definition.index.as_index() < at.index.as_index()
    } else {
        dominance.dominates(definition.block.as_index(), at.block.as_index())
    }
}

/// The operation at `site`, an `invoke`'s operation taking the index past the block's operations.
pub(crate) fn operation_at(func: &Function, site: OperationSite) -> &Operation {
    let block = func.block(site.block);
    match block.operations().get(site.index.as_index()) {
        Some(operation) => operation,
        None => match &block.terminator().kind {
            TerminatorKind::Invoke { operation, .. } => operation,
            _ => unreachable!("an operation site past the operations is the invoked one"),
        },
    }
}

/// A cell with one definition and otherwise only admitted reads.
struct Shape {
    value: ValueCell,
    /// The position of the definition among the cell's uses.
    index: usize,
    /// The allocated type, `None` for a pointer slot.
    ty: Option<Type>,
    /// Whether the cell is called through or dropped, which needs it to hold a bare function.
    function_uses: bool,
}

impl Shape {
    /// Whether reading the cell copies its value: a bare function carries no environment; any
    /// other value must be `TrivialCopy`, and neither called through nor dropped.
    fn copyable(&self, env: ModuleEnv<'_>) -> bool {
        match self.value.definition {
            Definition::Function(_) => true,
            _ => {
                !self.function_uses
                    && self
                        .ty
                        .is_none_or(|ty| concrete_type_is_trivial_copy(ty, &env))
            }
        }
    }
}

/// `cell`'s definition, if it has exactly one and its other `uses` are admitted reads.
fn shape(
    func: &Function,
    cell: &Cell,
    position: CellId,
    uses: &[CellUse],
    admit: &impl Fn(Access) -> bool,
) -> Option<Shape> {
    let ty = match cell.allocation {
        Allocation::Value {
            ty,
            witnessed: false,
        } => Some(ty),
        // A pointer slot is always trivially copied.
        Allocation::Place => None,
        Allocation::Value {
            witnessed: true, ..
        } => return None,
    };
    let mut found = None;
    let mut function_uses = false;
    for (index, cell_use) in uses.iter().enumerate() {
        if !admit(cell_use.access) {
            return None;
        }
        match cell_use.access {
            Access::Write(local_cells::Write::Store | local_cells::Write::Copy)
            | Access::MoveIn(Transfer::Sized) => {
                if found.replace((cell_use.site, index)).is_some() {
                    return None;
                }
            }
            Access::Write(local_cells::Write::CallResult) if !cell_use.in_terminator(func) => {
                if found.replace((cell_use.site, index)).is_some() {
                    return None;
                }
            }
            Access::Read(
                local_cells::Read::Load
                | local_cells::Read::Compare
                | local_cells::Read::Copy
                | local_cells::Read::Argument,
            )
            // Without a layout witness, a `move` transfers a statically sized representation.
            | Access::MoveOut(Transfer::Sized) => {}
            Access::Callee | Access::Drop => function_uses = true,
            _ => return None,
        }
    }
    let (site, index) = found?;
    let operation = operation_at(func, site);
    let definition = match (&operation.kind, &operation.operands[0]) {
        (OperationKind::Call { .. }, _) => Definition::CallResult,
        (OperationKind::Store, mir::Value::Register(stored)) => Definition::Register(*stored),
        (OperationKind::Store, mir::Value::Function(function)) => Definition::Function(*function),
        (OperationKind::Store, mir::Value::Constant(constant)) => Definition::Constant(*constant),
        (
            OperationKind::Memcpy | OperationKind::Move,
            source @ (mir::Value::Register(_) | mir::Value::Parameter(_)),
        ) => Definition::Copy(source.clone()),
        _ => return None,
    };
    Some(Shape {
        value: ValueCell {
            id: cell.id,
            site,
            definition,
            position,
        },
        index,
        ty,
        function_uses,
    })
}

#[cfg(test)]
mod tests {
    use super::{super::local_cells::LocalCells, Definition, ValueCells};
    use crate::{
        CompilerSession, Location,
        hir::value::LiteralValue,
        mir::{
            self, Operation, Value, builder::FunctionBuilder, dominance::Dominance,
            terminator::Terminator,
        },
        module::{FunctionId, LocalFunctionId, ModuleId},
        std::math::int_type,
        types::{
            effects::no_effects,
            r#type::{CallImplType, FnType},
        },
    };

    #[test]
    fn a_value_cell_has_one_dominating_definition_and_only_reads() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("cells".into(), Default::default());
        let block = builder.add_block();
        let constant = Value::Constant(builder.add_constant(
            int_type(),
            LiteralValue::new_native(3isize),
            &env,
        ));
        let call = |argument: Value, result: Value| {
            Operation::call(
                span,
                Value::Function(FunctionId::new(
                    ModuleId::default(),
                    LocalFunctionId::default(),
                )),
                [argument, result],
                CallImplType::value(FnType::new_mut_resolved(
                    [(int_type(), false)],
                    int_type(),
                    no_effects(),
                )),
            )
        };
        let alloca = |builder: &mut FunctionBuilder| {
            builder
                .append_operation(block, Operation::alloca(span, int_type()))
                .unwrap()
        };
        // A constant made a call operand, and the call's result.
        let operand = alloca(&mut builder);
        builder.append_operation(
            block,
            Operation::store(span, constant.clone(), operand.clone()),
        );
        let result = alloca(&mut builder);
        builder.append_operation(block, call(operand.clone(), result.clone()));
        builder.append_operation(block, Operation::load(span, result.clone()));
        // A call reading the place it defines.
        let in_place = alloca(&mut builder);
        builder.append_operation(block, call(in_place.clone(), in_place.clone()));
        // A read before the only write.
        let early = alloca(&mut builder);
        builder.append_operation(block, Operation::load(span, early.clone()));
        builder.append_operation(block, Operation::store(span, constant, early.clone()));
        builder.set_terminator(block, Terminator::ret(span));
        let func = builder.finish_unverified();

        let local = LocalCells::of(&func);
        let dominance = Dominance::of(&[Vec::new()], 0);
        let values = ValueCells::of_matching(&func, env, &local, |_| true, || &dominance);
        let definition = |cell: &Value| {
            let mir::Value::Register(id) = cell else {
                unreachable!("an alloca result is a register")
            };
            values.get(*id).map(|value| value.definition.clone())
        };
        assert!(matches!(
            definition(&operand),
            Some(Definition::Constant(_))
        ));
        assert!(matches!(definition(&result), Some(Definition::CallResult)));
        assert!(definition(&in_place).is_none());
        assert!(definition(&early).is_none());
    }
}
