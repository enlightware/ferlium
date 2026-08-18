// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::fmt::{self, Write};

use ustr::Ustr;

use crate::{
    Location,
    format::FormatWith,
    hir::function::ArgConvention,
    mir::{
        self, Operation,
        terminator::{Terminator, TerminatorKind},
        value::{Constant, ConstantId},
    },
    module::{FunctionId, ModuleEnv, id::Id},
    types::r#type::{CallResultConvention, Type},
};

/// The origin of a MIR function parameter.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ParameterKind {
    /// A source-visible runtime parameter and its semantic call convention.
    Parameter(ArgConvention),
    /// An optimized-MIR-only visible parameter that takes ownership of the caller's value.
    /// The callee must leave its incoming place moved out on every exit.
    Owned,
    /// A pointer to a dictionary or other hidden evidence.
    Dictionary,
    /// The caller-allocated out-pointer through which the function returns its result.
    Return,
}

/// A parameter in a MIR function signature.
#[derive(Clone, PartialEq, Eq, Hash)]
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
#[derive(Clone, PartialEq, Eq, Hash)]
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

/// One source-linked range in the textual rendering of a MIR function.
pub(crate) struct RenderedSourceMapEntry {
    pub(crate) from: usize,
    pub(crate) to: usize,
    pub(crate) span: Location,
}

/// A rendered MIR function with best-effort source links for its operations and terminators.
pub(crate) struct RenderedFunction {
    pub(crate) text: String,
    pub(crate) source_map: Vec<RenderedSourceMapEntry>,
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

    /// The number of non-terminating operations in this function.
    pub fn operation_count(&self) -> usize {
        self.blocks
            .iter()
            .map(|block| block.operations().len())
            .sum()
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

    /// Renders this function and records the spans of each non-synthesized operation and
    /// terminator. Textual MIR consumers without source links use this same renderer through
    /// [`FormatWith`], keeping the two forms byte-identical.
    pub(crate) fn render_with_source_map(&self, env: &ModuleEnv<'_>) -> RenderedFunction {
        let mut text = String::new();
        let mut source_map = Vec::new();
        let result = (|| -> fmt::Result {
            write!(text, "fn {}(", self.name)?;
            for (index, parameter) in self.parameters.iter().enumerate() {
                if index != 0 {
                    write!(text, ", ")?;
                }
                let kind = match parameter.kind {
                    ParameterKind::Parameter(ArgConvention::Let) => "arg let",
                    ParameterKind::Parameter(ArgConvention::MutableRef) => "arg &mut",
                    ParameterKind::Owned => "arg owned",
                    ParameterKind::Dictionary => "extra",
                    ParameterKind::Return => "ret",
                };
                write!(
                    text,
                    "{}: @{} {}",
                    mir::Value::Parameter(mir::ParameterId::from_index(index)),
                    kind,
                    parameter.ty.format_with(env)
                )?;
            }
            write!(text, "):")?;

            for (index, constant) in self.constants.iter().enumerate() {
                write!(
                    text,
                    "\n  @c{}: {} = {}",
                    index,
                    constant.ty.format_with(env),
                    constant.representation
                )?;
            }

            if !self.blocks.is_empty() {
                writeln!(text)?;
                for block_id in self.blocks() {
                    writeln!(text, "  b{}:", block_id.as_u32())?;
                    let block = self.block(block_id);
                    for operation in block.operations() {
                        let from = text.len();
                        write!(text, "    ")?;
                        if let Some(result) = operation.result_id() {
                            write!(text, "{} = ", mir::Value::Register(result))?;
                        }
                        writeln!(text, "{}", operation.format_with(env))?;
                        push_rendered_source_map_entry(
                            &mut source_map,
                            from,
                            text.len() - 1,
                            operation.span,
                        );
                    }
                    let terminator = block.terminator();
                    let from = text.len();
                    write!(text, "    ")?;
                    if let TerminatorKind::Invoke { operation, .. } = &terminator.kind
                        && let Some(result) = operation.result_id()
                    {
                        write!(text, "{} = ", mir::Value::Register(result))?;
                    }
                    writeln!(text, "{}", terminator.format_with(env))?;
                    push_rendered_source_map_entry(
                        &mut source_map,
                        from,
                        text.len() - 1,
                        terminator.span,
                    );
                }
            }
            Ok(())
        })();
        result.expect("writing to a string cannot fail");
        RenderedFunction { text, source_map }
    }

    /// Visits every function this body names, wherever it names it.
    ///
    /// The read-only counterpart of
    /// [`FunctionEdit::visit_function_ids_mut`](crate::mir::edit::FunctionEdit::visit_function_ids_mut),
    /// and it must reach exactly the same places: a caller deciding which functions are reachable
    /// and a caller renumbering them have to agree, or a body is kept alive by a reference the
    /// rewrite cannot find, or worse, dropped despite one it could. Both halves are needed and
    /// neither subsumes the other — a callee arrives as an operand, while `build_closure` carries
    /// its function in the operation kind.
    pub(crate) fn visit_function_ids(&self, mut visit: impl FnMut(FunctionId)) {
        let mut visit_operand = |operand: &mir::Value| {
            if let mir::Value::Function(id) = operand {
                visit(*id);
            }
        };
        for block in &self.blocks {
            for operation in &block.operations {
                operation.operands.iter().for_each(&mut visit_operand);
            }
            match &block.terminator.kind {
                TerminatorKind::Invoke { operation, .. } => {
                    operation.operands.iter().for_each(&mut visit_operand)
                }
                TerminatorKind::CondBr { condition, .. } => visit_operand(condition),
                TerminatorKind::Yield { place, .. } => visit_operand(place),
                TerminatorKind::Goto { .. }
                | TerminatorKind::Return
                | TerminatorKind::PropagateError
                | TerminatorKind::FailureDuringCleanup => {}
            }
        }
        for block in &self.blocks {
            for operation in &block.operations {
                if let Some(id) = operation.kind.function_id() {
                    visit(id);
                }
            }
            if let TerminatorKind::Invoke { operation, .. } = &block.terminator.kind
                && let Some(id) = operation.kind.function_id()
            {
                visit(id);
            }
        }
    }

    /// Decomposes the function for editing. Canonical form is restored by either the checked
    /// [`FunctionEdit::finish`](crate::mir::edit::FunctionEdit::finish) boundary or the optimizer's
    /// internal unchecked finish before final artifact verification.
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
        f.write_str(&self.render_with_source_map(env).text)
    }
}

fn push_rendered_source_map_entry(
    source_map: &mut Vec<RenderedSourceMapEntry>,
    from: usize,
    to: usize,
    span: Location,
) {
    if !span.is_synthesized() {
        source_map.push(RenderedSourceMapEntry { from, to, span });
    }
}
