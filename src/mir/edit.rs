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
//! index. [`BlockId`] is different — it indexes the block table — so blocks stay dense and
//! [`remove_unreachable_blocks`](FunctionEdit::remove_unreachable_blocks) is the one operation that
//! renumbers them, explicitly and on request.
//!
//! The optimization hook opens and closes every body without editing it, which is what checks the
//! identity property at corpus scale. The editing operations themselves have no caller until the
//! folding pass lands.
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
    pub(crate) fn replace_operation(&mut self, index: usize, mut operation: Operation) -> Operation {
        let previous = &self.operations[index];
        if operation.result() != OperationResult::Nothing {
            operation.assign_result_id(previous.result_id());
        }
        std::mem::replace(&mut self.operations[index], operation)
    }
}

fn successors(terminator: &Terminator) -> Vec<BlockId> {
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
        CompilerSession, Location,
        format::FormatWith,
        mir::builder::FunctionBuilder,
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
        let existing = edit.add_constant(Type::primitive::<bool>(), LiteralValue::new_native(true), &env);
        assert_eq!(existing.as_index(), 0, "an identical constant is reused");
        let fresh = edit.add_constant(int_type(), LiteralValue::new_native(7isize), &env);
        assert_eq!(fresh.as_index(), 1);
    }
}
