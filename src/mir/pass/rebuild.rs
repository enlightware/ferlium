// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! The identity rewrite: decompose a canonical function and reassemble an equivalent one.

use rustc_hash::FxHashMap;

use crate::{
    mir::{
        self, BasicBlock, BlockId, Function, Operation, OperationResult,
        builder::FunctionBuilder,
        terminator::{Terminator, TerminatorKind},
        value::ConstantId,
    },
    module::{ModuleEnv, id::Id},
};

/// Rebuilds `func` into an equivalent canonical function.
///
/// The result is structurally identical to the input up to value renumbering: reassembly assigns
/// fresh [`ValueId`](mir::ValueId)s in traversal order, which need not match the order the emitter
/// happened to allocate them in. Nothing outside a function references its value identities, so
/// renumbering is unobservable.
///
/// Reassembly goes through [`FunctionBuilder`], so the result is checked by the full MIR verifier
/// in debug and test builds.
pub(crate) fn rebuild_function(func: &Function, env: ModuleEnv<'_>) -> Function {
    let mut rewriter = Rewriter::new(func, env);
    rewriter.rebuild();
    rewriter.finish(env)
}

/// A remap from the identities of a source function to those of the function being assembled.
struct Rewriter<'f> {
    source: &'f Function,
    builder: FunctionBuilder,
    /// Result identities, keyed by source [`ValueId`](mir::ValueId) index.
    ///
    /// Precomputed rather than filled as operations are appended: an operand may refer to a value
    /// defined in a block that dominates the current one without preceding it in block order.
    registers: FxHashMap<mir::ValueId, mir::ValueId>,
    /// Constant-pool identities, keyed by source [`ConstantId`] index.
    ///
    /// The pool deduplicates on insertion, so a source pool built the same way maps one-to-one;
    /// the map keeps that an observation rather than an assumption.
    constants: Vec<ConstantId>,
}

impl<'f> Rewriter<'f> {
    fn new(source: &'f Function, env: ModuleEnv<'_>) -> Self {
        let mut builder = FunctionBuilder::new(source.name, source.result_convention());
        for parameter in source.parameters() {
            builder.add_parameter(parameter.ty, parameter.kind);
        }
        let constants = source
            .constants()
            .iter()
            .map(|constant| {
                builder.add_constant(constant.ty, constant.representation.clone(), &env)
            })
            .collect();
        Self {
            registers: predict_result_identities(source),
            source,
            builder,
            constants,
        }
    }

    fn rebuild(&mut self) {
        // Every block exists before any terminator is written, so a backward or forward branch
        // target is already valid when it is referenced.
        for _ in self.source.blocks() {
            self.builder.add_block();
        }
        for block_id in self.source.blocks() {
            self.rebuild_block(block_id);
        }
    }

    fn rebuild_block(&mut self, block_id: BlockId) {
        let block = self.source.block(block_id);
        for operation in block.operations() {
            let rebuilt = self.rebuild_operation(operation);
            let assigned = self.builder.append_operation(block_id, rebuilt);
            self.check_assigned_result(operation, assigned);
        }
        let terminator = self.rebuild_terminator(block.terminator());
        let assigned = self.builder.set_terminator(block_id, terminator);
        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
            self.check_assigned_result(operation, assigned);
        } else {
            debug_assert!(
                assigned.is_none(),
                "only an invoke terminator defines a value"
            );
        }
    }

    fn rebuild_operation(&self, operation: &Operation) -> Operation {
        let operands = operation
            .operands
            .iter()
            .map(|operand| self.rebuild_operand(operand))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        Operation::from_parts(operation.span, operands, operation.kind.clone())
    }

    fn rebuild_terminator(&self, terminator: &Terminator) -> Terminator {
        let kind = match &terminator.kind {
            TerminatorKind::Goto { target } => TerminatorKind::Goto { target: *target },
            TerminatorKind::CondBr {
                condition,
                then_target,
                else_target,
            } => TerminatorKind::CondBr {
                condition: self.rebuild_operand(condition),
                then_target: *then_target,
                else_target: *else_target,
            },
            TerminatorKind::Invoke {
                operation,
                normal,
                error,
            } => TerminatorKind::Invoke {
                operation: self.rebuild_operation(operation),
                normal: *normal,
                error: *error,
            },
            TerminatorKind::Yield { place, resume } => TerminatorKind::Yield {
                place: self.rebuild_operand(place),
                resume: *resume,
            },
            TerminatorKind::Return => TerminatorKind::Return,
            TerminatorKind::PropagateError => TerminatorKind::PropagateError,
            TerminatorKind::FailureDuringCleanup => TerminatorKind::FailureDuringCleanup,
        };
        Terminator {
            span: terminator.span,
            kind,
        }
    }

    /// Remaps a source operand. Only function-local identities move; function, dictionary,
    /// subscript, parameter, and pattern operands are stable across a rewrite.
    fn rebuild_operand(&self, operand: &mir::Value) -> mir::Value {
        match operand {
            mir::Value::Register(id) => mir::Value::Register(
                *self
                    .registers
                    .get(id)
                    .unwrap_or_else(|| panic!("operand {operand} has no defining operation")),
            ),
            mir::Value::Constant(id) => mir::Value::Constant(self.constants[id.as_index()]),
            other => other.clone(),
        }
    }

    fn check_assigned_result(&self, source: &Operation, assigned: Option<mir::Value>) {
        debug_assert_eq!(
            assigned,
            source
                .result_id()
                .map(|id| mir::Value::Register(self.registers[&id])),
            "reassembly allocated a result identity out of the predicted order"
        );
    }

    fn finish(self, env: ModuleEnv<'_>) -> Function {
        self.builder.finish(env)
    }
}

/// Maps each source result identity to the one reassembly will allocate for it.
///
/// [`FunctionBuilder`] numbers results sequentially as operations are inserted, so the prediction
/// is the traversal order used by [`Rewriter::rebuild`]: for each block, its operations in order,
/// then its terminator's invoked operation.
fn predict_result_identities(source: &Function) -> FxHashMap<mir::ValueId, mir::ValueId> {
    let mut registers = FxHashMap::default();
    let mut next = 0usize;
    let mut allocate = |operation: &Operation| {
        if let Some(id) = operation.result_id() {
            debug_assert_ne!(
                operation.result(),
                OperationResult::Nothing,
                "an operation with a value identity produces a result"
            );
            let previous = registers.insert(id, mir::ValueId::from_index(next));
            debug_assert!(previous.is_none(), "a value is defined exactly once");
            next += 1;
        }
    };
    for block_id in source.blocks() {
        let block: &BasicBlock = source.block(block_id);
        for operation in block.operations() {
            allocate(operation);
        }
        if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
            allocate(operation);
        }
    }
    registers
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, Location,
        format::FormatWith,
        mir::{Operation, builder::FunctionBuilder, terminator::Terminator},
        std::math::int_type,
    };

    use super::rebuild_function;

    /// Builds a small function whose result identities are *not* allocated in traversal order: the
    /// entry block is terminated after the successor block has been filled, so the successor's
    /// values are numbered first.
    #[test]
    fn rebuilding_renumbers_out_of_order_identities_without_changing_structure() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();

        let mut builder = FunctionBuilder::new("out_of_order".into(), Default::default());
        let entry = builder.add_block();
        let next = builder.add_block();

        // Fill the successor first, so its alloca takes value identity 0.
        let in_successor = builder
            .append_operation(next, Operation::alloca(span, int_type()))
            .unwrap();
        builder.set_terminator(next, Terminator::ret(span));

        let in_entry = builder
            .append_operation(entry, Operation::alloca(span, int_type()))
            .unwrap();
        builder.set_terminator(entry, Terminator::goto(span, next));
        assert_eq!(
            in_successor,
            crate::mir::Value::Register(crate::mir::ValueId::new(0))
        );
        assert_eq!(
            in_entry,
            crate::mir::Value::Register(crate::mir::ValueId::new(1))
        );

        let source = builder.finish(env);
        let rebuilt = rebuild_function(&source, env);

        // Traversal order now numbers the entry block's value first, so the rendered forms differ
        // only in those identities; re-rebuilding is a fixed point.
        let renumbered = rebuilt.format_with(&env).to_string();
        assert_ne!(source.format_with(&env).to_string(), renumbered);
        assert_eq!(
            rebuild_function(&rebuilt, env)
                .format_with(&env)
                .to_string(),
            renumbered
        );
    }

    #[test]
    fn rebuilding_preserves_a_function_already_in_traversal_order() {
        let span = Location::new_synthesized();
        let session = CompilerSession::new();
        let env = session.module_env();

        let mut builder = FunctionBuilder::new("in_order".into(), Default::default());
        let block = builder.add_block();
        let place = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        builder.append_operation(block, Operation::clear(span, place));
        builder.set_terminator(block, Terminator::ret(span));

        let source = builder.finish(env);
        let rebuilt = rebuild_function(&source, env);
        assert_eq!(
            source.format_with(&env).to_string(),
            rebuilt.format_with(&env).to_string()
        );
    }
}
