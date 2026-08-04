use std::fmt;

use ustr::Ustr;

use crate::{
    format::FormatWith,
    hir::function::ArgConvention,
    mir::{
        self, Operation,
        terminator::{Terminator, TerminatorKind},
        value::{Constant, ConstantId},
    },
    module::{ModuleEnv, id::Id},
    types::r#type::{CallResultConvention, Type},
};

/// The origin of a MIR function parameter.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ParameterKind {
    /// A source-visible runtime parameter and its semantic call convention.
    Parameter(ArgConvention),
    /// A pointer to a dictionary or other hidden evidence.
    Dictionary,
    /// The caller-allocated out-pointer through which the function returns its result.
    Return,
}

/// A parameter in a MIR function signature.
#[derive(Clone)]
pub struct Parameter {
    pub ty: Type,
    pub kind: ParameterKind,
}

crate::define_id_type!(
    /// The stable identity of a basic block within a MIR function.
    BlockId
);

/// A finalized MIR basic block.
///
/// Canonical blocks always contain zero or more non-terminating operations followed by exactly one
/// terminator. Forward declarations and temporarily unterminated blocks exist only in
/// [`FunctionBuilder`](crate::mir::builder::FunctionBuilder).
#[derive(Clone)]
pub struct BasicBlock {
    operations: Vec<Operation>,
    terminator: Terminator,
}

impl BasicBlock {
    pub(crate) fn new(operations: Vec<Operation>, terminator: Terminator) -> Self {
        Self {
            operations,
            terminator,
        }
    }

    pub fn operations(&self) -> &[Operation] {
        &self.operations
    }

    pub fn terminator(&self) -> &Terminator {
        &self.terminator
    }

    /// Decomposes the block for editing. Canonical form is restored by
    /// [`FunctionEdit::finish`](crate::mir::edit::FunctionEdit::finish).
    pub(crate) fn into_parts(self) -> (Vec<Operation>, Terminator) {
        (self.operations, self.terminator)
    }
}

/// A canonical Ferlium MIR function.
///
/// Plain immutable data: cloning one is what a pass does before opening it for editing, since the
/// raw stage must survive alongside the optimized one.
#[derive(Clone)]
pub struct Function {
    pub name: Ustr,
    result_convention: CallResultConvention,
    parameters: Vec<Parameter>,
    constants: Vec<Constant>,
    blocks: Vec<BasicBlock>,
}

impl Function {
    pub(crate) fn new(
        name: Ustr,
        result_convention: CallResultConvention,
        parameters: Vec<Parameter>,
        constants: Vec<Constant>,
        blocks: Vec<BasicBlock>,
    ) -> Self {
        Self {
            name,
            result_convention,
            parameters,
            constants,
            blocks,
        }
    }

    pub fn result_convention(&self) -> CallResultConvention {
        self.result_convention
    }

    pub fn parameters(&self) -> &[Parameter] {
        &self.parameters
    }

    pub fn constant(&self, id: ConstantId) -> &Constant {
        &self.constants[id.as_index()]
    }

    pub fn constants(&self) -> &[Constant] {
        &self.constants
    }

    pub fn blocks(&self) -> impl Iterator<Item = BlockId> + '_ {
        (0..self.blocks.len()).map(BlockId::from_index)
    }

    pub fn entry(&self) -> BlockId {
        assert!(
            !self.blocks.is_empty(),
            "a lowered function has an entry block"
        );
        BlockId::from_index(0)
    }

    pub fn block(&self, block: BlockId) -> &BasicBlock {
        &self.blocks[block.as_index()]
    }

    /// Decomposes the function for editing. Canonical form is restored by
    /// [`FunctionEdit::finish`](crate::mir::edit::FunctionEdit::finish), which re-verifies it.
    pub(crate) fn into_parts(
        self,
    ) -> (
        Ustr,
        CallResultConvention,
        Vec<Parameter>,
        Vec<Constant>,
        Vec<BasicBlock>,
    ) {
        (
            self.name,
            self.result_convention,
            self.parameters,
            self.constants,
            self.blocks,
        )
    }
}

impl FormatWith<ModuleEnv<'_>> for Function {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        write!(f, "fn {}(", self.name)?;
        for (i, parameter) in self.parameters.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            let kind = match parameter.kind {
                ParameterKind::Parameter(ArgConvention::Let) => "arg let",
                ParameterKind::Parameter(ArgConvention::MutableRef) => "arg &mut",
                ParameterKind::Dictionary => "extra",
                ParameterKind::Return => "ret",
            };
            write!(
                f,
                "{}: @{} {}",
                mir::Value::Parameter(mir::ParameterId::from_index(i)),
                kind,
                parameter.ty.format_with(env)
            )?;
        }
        write!(f, "):")?;

        for (index, constant) in self.constants.iter().enumerate() {
            write!(
                f,
                "\n  @c{}: {} = {}",
                index,
                constant.ty.format_with(env),
                constant.representation
            )?;
        }

        if !self.blocks.is_empty() {
            writeln!(f)?;
            for block_id in self.blocks() {
                writeln!(f, "  b{}:", block_id.as_u32())?;
                let block = self.block(block_id);
                for operation in block.operations() {
                    write!(f, "    ")?;
                    if let Some(result) = operation.result_id() {
                        write!(f, "{} = ", mir::Value::Register(result))?;
                    }
                    writeln!(f, "{}", operation.format_with(env))?;
                }
                write!(f, "    ")?;
                if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind
                    && let Some(result) = operation.result_id()
                {
                    write!(f, "{} = ", mir::Value::Register(result))?;
                }
                writeln!(f, "{}", block.terminator().format_with(env))?;
            }
        }
        Ok(())
    }
}
