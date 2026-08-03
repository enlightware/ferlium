//! Construction-only state for canonical MIR functions.

use ustr::Ustr;

use crate::{
    hir::value::LiteralValue,
    mir::{
        self, BasicBlock, BlockId, Function, Operation, OperationResult, Parameter, ParameterKind,
        operation::SourceFallibility,
        terminator::{Terminator, TerminatorKind},
        value::{Constant, ConstantId},
    },
    module::{ModuleEnv, id::Id},
    types::r#type::{CallResultConvention, Type},
};

/// A temporarily unterminated block used only while lowering.
struct PendingBlock {
    operations: Vec<Operation>,
    terminator: Option<Terminator>,
}

/// Construction-only state for a MIR function.
///
/// This is the only representation in which forward block targets and missing terminators exist.
/// [`finish`](Self::finish) validates and converts it into canonical [`Function`] storage.
pub(crate) struct FunctionBuilder {
    name: Ustr,
    result_convention: CallResultConvention,
    parameters: Vec<Parameter>,
    constants: Vec<Constant>,
    blocks: Vec<PendingBlock>,
    next_value_index: usize,
}

impl FunctionBuilder {
    pub(crate) fn new(name: Ustr, result_convention: CallResultConvention) -> Self {
        Self {
            name,
            result_convention,
            parameters: Vec::new(),
            constants: Vec::new(),
            blocks: Vec::new(),
            next_value_index: 0,
        }
    }

    pub(crate) fn add_parameter(&mut self, ty: Type, tag: ParameterKind) -> mir::ParameterId {
        let id = mir::ParameterId::from_index(self.parameters.len());
        self.parameters.push(Parameter { ty, kind: tag });
        id
    }

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

    pub(crate) fn add_block(&mut self) -> BlockId {
        let id = BlockId::from_index(self.blocks.len());
        self.blocks.push(PendingBlock {
            operations: Vec::new(),
            terminator: None,
        });
        id
    }

    pub(crate) fn block_is_terminated(&self, block: BlockId) -> bool {
        self.blocks[block.as_index()].terminator.is_some()
    }

    /// Appends a non-terminating operation and returns its result value, if any.
    ///
    /// Intrinsically source-fallible operations are rejected here. `EndProject` is
    /// context-dependent because it obtains its effects from the defining open projection, so
    /// [`finish`](Self::finish) verifies its final `Invoke` form with the rest of the function.
    pub(crate) fn append_operation(
        &mut self,
        block: BlockId,
        mut operation: Operation,
    ) -> Option<mir::Value> {
        assert!(
            !self.block_is_terminated(block),
            "operation inserted after block terminator"
        );
        assert_ne!(
            operation.source_fallibility(),
            SourceFallibility::Fallible,
            "source-fallible operation must be wrapped by an invoke terminator"
        );
        let result = self.assign_result(&mut operation);
        self.blocks[block.as_index()].operations.push(operation);
        result
    }

    /// Terminates a pending block. An invoked operation receives its result identity here.
    pub(crate) fn set_terminator(
        &mut self,
        block: BlockId,
        mut terminator: Terminator,
    ) -> Option<mir::Value> {
        assert!(
            !self.block_is_terminated(block),
            "block already has a terminator"
        );
        let result = match &mut terminator.kind {
            TerminatorKind::Invoke { operation, .. } => self.assign_result(operation),
            _ => None,
        };
        self.blocks[block.as_index()].terminator = Some(terminator);
        result
    }

    fn assign_result(&mut self, operation: &mut Operation) -> Option<mir::Value> {
        let result_id = (operation.result() != OperationResult::Nothing).then(|| {
            let id = mir::ValueId::from_index(self.next_value_index);
            self.next_value_index += 1;
            id
        });
        operation.assign_result_id(result_id);
        result_id.map(mir::Value::Register)
    }

    /// Finalizes the function and verifies every canonical MIR invariant in debug and test builds.
    pub(crate) fn finish(self, env: ModuleEnv<'_>) -> Function {
        assert!(
            !self.blocks.is_empty(),
            "a lowered function has no entry block"
        );
        let blocks = self
            .blocks
            .into_iter()
            .enumerate()
            .map(|(index, block)| {
                BasicBlock::new(
                    block.operations,
                    block.terminator.unwrap_or_else(|| {
                        panic!("MIR block b{index} was not terminated during lowering")
                    }),
                )
            })
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

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, Location,
        mir::{Operation, Value, builder::FunctionBuilder, terminator::Terminator},
        std::math::int_type,
    };

    #[test]
    fn result_value_ids_are_independent_of_operation_locations() {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("independent_value_ids".into(), Default::default());
        let block = builder.add_block();

        let first = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        assert_eq!(
            builder.append_operation(block, Operation::check_fuel(span)),
            None
        );
        let second = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();
        builder.set_terminator(block, Terminator::ret(span));
        let session = CompilerSession::new();
        let _function = builder.finish(session.module_env());

        assert_eq!(first, Value::Register(crate::mir::ValueId::new(0)));
        assert_eq!(second, Value::Register(crate::mir::ValueId::new(1)));
    }

    #[test]
    #[should_panic(expected = "branch targets a missing block")]
    fn finalization_rejects_invalid_block_targets() {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("invalid_target".into(), Default::default());
        let entry = builder.add_block();
        builder.set_terminator(entry, Terminator::goto(span, crate::mir::BlockId::new(1)));

        let session = CompilerSession::new();
        builder.finish(session.module_env());
    }
}
