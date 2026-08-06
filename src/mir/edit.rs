// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! The mutable form of a MIR function, in which a pass edits it.
//!
//! A canonical [`Function`] is immutable, and [`FunctionBuilder`](crate::mir::builder::FunctionBuilder)
//! builds one from nothing — the right shape for lowering, the wrong one for a pass, which starts
//! from a function that already exists and changes part of it. Rebuilding through the builder makes
//! a pass reconstruct what it did not touch, and renumbers every result identity in the process.
//!
//! [`FunctionEdit`] is the editable form instead: it owns a decomposed function, exposes its blocks
//! for mutation, and restores canonical form in [`finish`](FunctionEdit::finish), which re-verifies
//! the result exactly where the builder does. In between, the function may be inconsistent — that
//! is the point of having a separate type for it.
//!
//! **Identities are stable across an edit.** A [`ValueId`](mir::ValueId) survives editing, and new
//! ones are allocated beyond the highest already in use, so an analysis keyed on value identity
//! stays valid from one pass to the next and an identity edit is genuinely the identity. That costs
//! nothing: the verifier and the interpreter only ever use a `ValueId` as a map key, never as an
//! index. [`BlockId`] is different — it indexes the block table — so blocks stay dense, and the
//! operations that renumber them
//! ([`remove_unreachable_blocks`](FunctionEdit::remove_unreachable_blocks),
//! [`reorder_blocks_in_reverse_postorder`](FunctionEdit::reorder_blocks_in_reverse_postorder) and
//! [`merge_blocks_into_predecessors`](FunctionEdit::merge_blocks_into_predecessors)) are explicit
//! and run on request.
//!
//! The optimization hook opens and closes every body, including those no pass changed, which is what
//! checks the identity property at corpus scale.
#![allow(dead_code)]

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    hir::value::LiteralValue,
    mir::{
        self, BasicBlock, BlockId, Function, Operation, OperationResult, Parameter,
        terminator::{Terminator, TerminatorKind},
        value::{Constant, ConstantId},
    },
    module::{ModuleEnv, id::Id},
    types::r#type::{CallResultConvention, Type},
};

use ustr::Ustr;

/// A basic block being edited: the same content as a [`BasicBlock`], with its parts exposed.
pub(crate) struct EditBlock {
    pub operations: Vec<Operation>,
    pub terminator: Terminator,
}

/// A MIR function in editable form. See the module documentation.
pub(crate) struct FunctionEdit {
    name: Ustr,
    result_convention: CallResultConvention,
    parameters: Vec<Parameter>,
    constants: Vec<Constant>,
    blocks: Vec<EditBlock>,
    /// One past the highest result identity in use, so fresh identities never collide with an
    /// existing one — including one whose defining operation has just been removed.
    next_value_index: usize,
}

impl FunctionEdit {
    /// Opens `func` for editing.
    pub(crate) fn new(func: Function) -> Self {
        let next_value_index = func
            .blocks()
            .flat_map(|block_id| {
                let block = func.block(block_id);
                let terminator_result = match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => operation.result_id(),
                    _ => None,
                };
                block
                    .operations()
                    .iter()
                    .filter_map(Operation::result_id)
                    .chain(terminator_result)
                    .collect::<Vec<_>>()
            })
            .map(|id| id.as_index() + 1)
            .max()
            .unwrap_or(0);

        let (name, result_convention, parameters, constants, blocks) = func.into_parts();
        let blocks = blocks
            .into_iter()
            .map(|block| {
                let (operations, terminator) = block.into_parts();
                EditBlock {
                    operations,
                    terminator,
                }
            })
            .collect();
        Self {
            name,
            result_convention,
            parameters,
            constants,
            blocks,
            next_value_index,
        }
    }

    pub(crate) fn parameters(&self) -> &[Parameter] {
        &self.parameters
    }

    /// Renames the function, for a pass that produces a new one from an existing body — a
    /// specialization, whose name says which original and which instantiation it came from.
    pub(crate) fn set_name(&mut self, name: Ustr) {
        self.name = name;
    }

    /// The parameters, for a pass that rewrites their types. Their count and kinds are part of the
    /// function's calling convention and must not change under an edit.
    pub(crate) fn parameters_mut(&mut self) -> &mut [Parameter] {
        &mut self.parameters
    }

    /// The constant pool, for a pass that rewrites the *types* of existing entries. Adding one goes
    /// through [`Self::add_constant`], which dedups; removing one is [`Self::prune_constants`],
    /// which renumbers.
    pub(crate) fn constants_mut(&mut self) -> &mut [Constant] {
        &mut self.constants
    }

    pub(crate) fn result_convention(&self) -> CallResultConvention {
        self.result_convention
    }

    pub(crate) fn blocks(&self) -> impl Iterator<Item = BlockId> + '_ {
        (0..self.blocks.len()).map(BlockId::from_index)
    }

    pub(crate) fn entry(&self) -> BlockId {
        assert!(!self.blocks.is_empty(), "an edited function has an entry");
        BlockId::from_index(0)
    }

    pub(crate) fn block(&self, block: BlockId) -> &EditBlock {
        &self.blocks[block.as_index()]
    }

    pub(crate) fn block_mut(&mut self, block: BlockId) -> &mut EditBlock {
        &mut self.blocks[block.as_index()]
    }

    /// Appends an empty block, terminated by `terminator`.
    pub(crate) fn add_block(&mut self, terminator: Terminator) -> BlockId {
        let id = BlockId::from_index(self.blocks.len());
        self.blocks.push(EditBlock {
            operations: Vec::new(),
            terminator,
        });
        id
    }

    /// Allocates a result identity for an operation this pass introduces.
    ///
    /// The caller assigns it with [`Operation::assign_result_id`], as the builder does; an
    /// operation that produces no result must not be given one.
    pub(crate) fn new_value(&mut self) -> mir::ValueId {
        let id = mir::ValueId::from_index(self.next_value_index);
        self.next_value_index += 1;
        id
    }

    /// Interns a constant, reusing an identical existing entry. Mirrors the builder's pool, so a
    /// constant added by a pass is indistinguishable from one the emitter produced.
    pub(crate) fn add_constant(
        &mut self,
        ty: Type,
        representation: LiteralValue,
        env: &ModuleEnv<'_>,
    ) -> ConstantId {
        debug_assert!(
            representation.has_representation_type_in(ty, env),
            "MIR constant representation does not match its declared type"
        );
        let constant = Constant { ty, representation };
        if let Some(index) = self.constants.iter().position(|item| item == &constant) {
            return ConstantId::from_index(index);
        }
        let id = ConstantId::from_index(self.constants.len());
        self.constants.push(constant);
        id
    }

    /// Drops every block unreachable from the entry and renumbers the rest.
    ///
    /// This is the only operation that moves a [`BlockId`], and it is explicit because folding a
    /// `condbr` to a `goto` is what strands blocks: a pass decides when its own edits have settled.
    /// Identities of *values* are untouched.
    pub(crate) fn remove_unreachable_blocks(&mut self) {
        let mut reachable = FxHashSet::default();
        let mut worklist = vec![self.entry()];
        while let Some(block) = worklist.pop() {
            if !reachable.insert(block) {
                continue;
            }
            worklist.extend(successors(&self.block(block).terminator));
        }
        if reachable.len() == self.blocks.len() {
            return;
        }

        let mut renumbered = FxHashMap::default();
        let mut next = 0usize;
        for block in self.blocks() {
            if reachable.contains(&block) {
                renumbered.insert(block, BlockId::from_index(next));
                next += 1;
            }
        }
        let mut retained = Vec::with_capacity(next);
        for (index, mut block) in std::mem::take(&mut self.blocks).into_iter().enumerate() {
            if !reachable.contains(&BlockId::from_index(index)) {
                continue;
            }
            for target in successors_mut(&mut block.terminator) {
                *target = renumbered[target];
            }
            retained.push(block);
        }
        self.blocks = retained;
    }

    /// Reorders blocks into reverse postorder, keeping any unreachable block after them.
    ///
    /// A pass that appends a block can leave a *use* before the *definition* it names in block
    /// order. Dominance still holds — the definition's block dominates the use's — but block order
    /// is what MIR's own consumers walk: the verifier resolves an operation's result role from the
    /// role of its operand (a `load`'s type is its pointer's pointee), so it needs the definition to
    /// come first. Reverse postorder gives that for free, since a dominator always precedes what it
    /// dominates in one.
    ///
    /// Like [`remove_unreachable_blocks`](Self::remove_unreachable_blocks) this moves every
    /// [`BlockId`] and is therefore explicit; unlike it, nothing is dropped — an unreachable block
    /// keeps its relative position at the end, because removing it is a separate decision.
    pub(crate) fn reorder_blocks_in_reverse_postorder(&mut self) {
        let mut order = Vec::with_capacity(self.blocks.len());
        let mut visited = FxHashSet::default();
        let mut stack = vec![(self.entry(), 0usize)];
        visited.insert(self.entry());
        while let Some((block, next)) = stack.pop() {
            let successors = successors(&self.block(block).terminator);
            match successors.get(next) {
                Some(successor) => {
                    stack.push((block, next + 1));
                    if visited.insert(*successor) {
                        stack.push((*successor, 0));
                    }
                }
                None => order.push(block),
            }
        }
        order.reverse();
        order.extend(self.blocks().filter(|block| !visited.contains(block)));
        if order
            .iter()
            .enumerate()
            .all(|(index, block)| block.as_index() == index)
        {
            return;
        }

        let mut renumbered = FxHashMap::default();
        for (index, block) in order.iter().enumerate() {
            renumbered.insert(*block, BlockId::from_index(index));
        }
        let mut previous: Vec<Option<EditBlock>> = std::mem::take(&mut self.blocks)
            .into_iter()
            .map(Some)
            .collect();
        self.blocks = order
            .iter()
            .map(|block| {
                previous[block.as_index()]
                    .take()
                    .expect("each block is placed exactly once")
            })
            .collect();
        for block in &mut self.blocks {
            for target in successors_mut(&mut block.terminator) {
                *target = renumbered[target];
            }
        }
    }

    /// Merges every block that has a single predecessor into it, when that predecessor ends in an
    /// unconditional jump.
    ///
    /// Inlining manufactures exactly this shape and nothing else removes it. Splicing a callee
    /// always splits the call site's block — the operations after the call become a continuation —
    /// and joins the pieces with jumps, so a callee of one block arrives as *three*: the call's
    /// block, the callee's body, and the continuation, each edge a jump to a block no one else
    /// reaches. Every later round then walks all three, and the dataflow analysis pays per block.
    ///
    /// **Block order stays correct, and the argument is worth stating** because the verifier depends
    /// on it: it resolves an operation's result role from the role of its operand while walking
    /// blocks in index order, so a definition must *precede* its uses there, not merely dominate
    /// them. Merging moves the successor's operations earlier, to the predecessor's position, which
    /// could in principle overtake a definition they name. It cannot: the successor's only path from
    /// entry runs through the predecessor, so anything dominating the successor dominates the
    /// predecessor too, and therefore already precedes it. Nothing the merged operations name can
    /// live between the two.
    ///
    /// Emptied blocks are left unreachable and dropped by
    /// [`remove_unreachable_blocks`](Self::remove_unreachable_blocks), which is also what renumbers.
    /// Like the other structural operations this moves every [`BlockId`], so it is explicit.
    pub(crate) fn merge_blocks_into_predecessors(&mut self) {
        let mut merged_any = false;
        // A merge can expose another — a chain of jumps collapses one link at a time — so this runs
        // to fixpoint. It terminates because each merge empties one block for good.
        while let Some((predecessor, successor)) = self.next_mergeable_pair() {
            let operations = std::mem::take(&mut self.blocks[successor.as_index()].operations);
            let span = self.blocks[successor.as_index()].terminator.span;
            // Leave the emptied block terminal, so it stops contributing edges to the predecessor
            // counts the next iteration computes.
            let terminator = std::mem::replace(
                &mut self.blocks[successor.as_index()].terminator,
                Terminator::ret(span),
            );
            let block = &mut self.blocks[predecessor.as_index()];
            block.operations.extend(operations);
            block.terminator = terminator;
            merged_any = true;
        }
        if merged_any {
            self.remove_unreachable_blocks();
        }
    }

    /// The next `(predecessor, successor)` pair the above may collapse, if any.
    fn next_mergeable_pair(&self) -> Option<(BlockId, BlockId)> {
        // Incoming *edges*, not distinct predecessors: a `condbr` whose arms share a target counts
        // twice, which correctly disqualifies that target.
        let mut incoming: FxHashMap<BlockId, usize> = FxHashMap::default();
        for block in self.blocks() {
            for target in successors(&self.block(block).terminator) {
                *incoming.entry(target).or_default() += 1;
            }
        }
        self.blocks().find_map(|predecessor| {
            let TerminatorKind::Goto { target } = self.block(predecessor).terminator.kind else {
                return None;
            };
            // The entry block keeps its identity as the function's start, and a self-loop is not a
            // merge.
            if target == self.entry() || target == predecessor {
                return None;
            }
            (incoming.get(&target).copied() == Some(1)).then_some((predecessor, target))
        })
    }

    /// Drops constants no operand names any more, renumbering the rest.
    ///
    /// Like [`remove_unreachable_blocks`](Self::remove_unreachable_blocks) this is explicit rather
    /// than automatic: it moves every [`ConstantId`], so a pass asks for it once its edits have
    /// settled. Value identities are untouched.
    pub(crate) fn prune_constants(&mut self) {
        let mut used = FxHashSet::default();
        self.visit_operands(|operand| {
            if let mir::Value::Constant(id) = operand {
                used.insert(*id);
            }
        });
        if used.len() == self.constants.len() {
            return;
        }

        let mut renumbered = FxHashMap::default();
        let mut retained = Vec::with_capacity(used.len());
        for (index, constant) in std::mem::take(&mut self.constants).into_iter().enumerate() {
            let id = ConstantId::from_index(index);
            if used.contains(&id) {
                renumbered.insert(id, ConstantId::from_index(retained.len()));
                retained.push(constant);
            }
        }
        self.constants = retained;
        self.visit_operands_mut(|operand| {
            if let mir::Value::Constant(id) = operand {
                *id = renumbered[id];
            }
        });
    }

    fn visit_operands(&self, mut visit: impl FnMut(&mir::Value)) {
        for block in &self.blocks {
            for operation in &block.operations {
                operation.operands.iter().for_each(&mut visit);
            }
            visit_terminator_operands(&block.terminator, &mut visit);
        }
    }

    pub(crate) fn visit_operands_mut(&mut self, mut visit: impl FnMut(&mut mir::Value)) {
        for block in &mut self.blocks {
            for operation in &mut block.operations {
                operation.operands.iter_mut().for_each(&mut visit);
            }
            visit_terminator_operands_mut(&mut block.terminator, &mut visit);
        }
    }

    /// Restores canonical form, verifying every MIR invariant in debug and test builds — the same
    /// boundary check [`FunctionBuilder::finish`](crate::mir::builder::FunctionBuilder::finish)
    /// performs.
    pub(crate) fn finish(self, env: ModuleEnv<'_>) -> Function {
        assert!(
            !self.blocks.is_empty(),
            "an edited function has no entry block"
        );
        let blocks = self
            .blocks
            .into_iter()
            .map(|block| BasicBlock::new(block.operations, block.terminator))
            .collect();
        let function = Function::new(
            self.name,
            self.result_convention,
            self.parameters,
            self.constants,
            blocks,
        );
        #[cfg(any(debug_assertions, test))]
        super::verify::verify_function(&function, env);
        #[cfg(not(any(debug_assertions, test)))]
        let _ = env;
        function
    }
}

impl EditBlock {
    /// Replaces the operation at `index`, keeping its result identity if the replacement produces
    /// one. Returns the operation that was there.
    pub(crate) fn replace_operation(
        &mut self,
        index: usize,
        mut operation: Operation,
    ) -> Operation {
        let previous = &self.operations[index];
        if operation.result() != OperationResult::Nothing {
            operation.assign_result_id(previous.result_id());
        }
        std::mem::replace(&mut self.operations[index], operation)
    }
}

fn visit_terminator_operands(terminator: &Terminator, visit: &mut impl FnMut(&mir::Value)) {
    match &terminator.kind {
        TerminatorKind::Invoke { operation, .. } => operation.operands.iter().for_each(visit),
        TerminatorKind::CondBr { condition, .. } => visit(condition),
        TerminatorKind::Yield { place, .. } => visit(place),
        TerminatorKind::Goto { .. }
        | TerminatorKind::Return
        | TerminatorKind::PropagateError
        | TerminatorKind::FailureDuringCleanup => {}
    }
}

fn visit_terminator_operands_mut(
    terminator: &mut Terminator,
    visit: &mut impl FnMut(&mut mir::Value),
) {
    match &mut terminator.kind {
        TerminatorKind::Invoke { operation, .. } => operation.operands.iter_mut().for_each(visit),
        TerminatorKind::CondBr { condition, .. } => visit(condition),
        TerminatorKind::Yield { place, .. } => visit(place),
        TerminatorKind::Goto { .. }
        | TerminatorKind::Return
        | TerminatorKind::PropagateError
        | TerminatorKind::FailureDuringCleanup => {}
    }
}

pub(crate) fn successors(terminator: &Terminator) -> Vec<BlockId> {
    match &terminator.kind {
        TerminatorKind::Goto { target } => vec![*target],
        TerminatorKind::CondBr {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        TerminatorKind::Invoke { normal, error, .. } => vec![*normal, *error],
        TerminatorKind::Yield { resume, .. } => vec![*resume],
        TerminatorKind::Return
        | TerminatorKind::PropagateError
        | TerminatorKind::FailureDuringCleanup => Vec::new(),
    }
}

fn successors_mut(terminator: &mut Terminator) -> Vec<&mut BlockId> {
    match &mut terminator.kind {
        TerminatorKind::Goto { target } => vec![target],
        TerminatorKind::CondBr {
            then_target,
            else_target,
            ..
        } => vec![then_target, else_target],
        TerminatorKind::Invoke { normal, error, .. } => vec![normal, error],
        TerminatorKind::Yield { resume, .. } => vec![resume],
        TerminatorKind::Return
        | TerminatorKind::PropagateError
        | TerminatorKind::FailureDuringCleanup => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, Location, format::FormatWith, mir::builder::FunctionBuilder,
        std::math::int_type,
    };

    /// Building a small function whose entry branches to a block that a later edit strands.
    fn conditional(session: &CompilerSession) -> Function {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("conditional".into(), Default::default());
        let entry = builder.add_block();
        let then_block = builder.add_block();
        let else_block = builder.add_block();

        let flag = builder
            .append_operation(entry, Operation::alloca(span, Type::primitive::<bool>()))
            .unwrap();
        let constant = builder.add_constant(
            Type::primitive::<bool>(),
            LiteralValue::new_native(true),
            &session.module_env(),
        );
        builder.append_operation(
            entry,
            Operation::store(span, mir::Value::Constant(constant), flag.clone()),
        );
        let condition = builder
            .append_operation(entry, Operation::load(span, flag))
            .unwrap();
        builder.set_terminator(
            entry,
            Terminator::cond_br(span, condition, then_block, else_block),
        );
        for block in [then_block, else_block] {
            builder.append_operation(block, Operation::alloca(span, int_type()));
            builder.set_terminator(block, Terminator::ret(span));
        }
        builder.finish(session.module_env())
    }

    /// The invariant the editor exists for: editing nothing changes nothing, byte for byte.
    #[test]
    fn an_empty_edit_is_the_identity() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let source = conditional(&session);
        let rendered = source.format_with(&env).to_string();

        let edited = FunctionEdit::new(source).finish(env);
        assert_eq!(edited.format_with(&env).to_string(), rendered);
    }

    #[test]
    fn fresh_values_do_not_collide_with_existing_ones() {
        let session = CompilerSession::new();
        let source = conditional(&session);
        let highest = source
            .blocks()
            .flat_map(|block| source.block(block).operations().iter())
            .filter_map(Operation::result_id)
            .map(|id| id.as_index())
            .max()
            .expect("the function defines values");

        let mut edit = FunctionEdit::new(source);
        assert_eq!(edit.new_value().as_index(), highest + 1);
        assert_eq!(edit.new_value().as_index(), highest + 2);
    }

    /// Folding a `condbr` into a `goto` strands a block; removing it renumbers targets and leaves
    /// value identities alone.
    #[test]
    fn removing_unreachable_blocks_renumbers_targets_only() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let source = conditional(&session);
        let live_value = source
            .block(BlockId::from_index(2))
            .operations()
            .first()
            .and_then(Operation::result_id)
            .expect("the else block defines a value");

        let mut edit = FunctionEdit::new(source);
        // Take the else branch unconditionally, stranding the then block.
        edit.block_mut(edit.entry()).terminator = Terminator::goto(span, BlockId::from_index(2));
        edit.remove_unreachable_blocks();

        assert_eq!(edit.blocks().count(), 2);
        // The surviving block kept its operation, and so its value identity.
        assert_eq!(
            edit.block(BlockId::from_index(1))
                .operations
                .first()
                .and_then(Operation::result_id),
            Some(live_value)
        );
        let finished = edit.finish(env);
        assert_eq!(finished.blocks().count(), 2);
    }

    #[test]
    fn a_constant_added_by_a_pass_is_interned() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let mut edit = FunctionEdit::new(conditional(&session));
        let existing = edit.add_constant(
            Type::primitive::<bool>(),
            LiteralValue::new_native(true),
            &env,
        );
        assert_eq!(existing.as_index(), 0, "an identical constant is reused");
        let fresh = edit.add_constant(int_type(), LiteralValue::new_native(7isize), &env);
        assert_eq!(fresh.as_index(), 1);
    }
}
