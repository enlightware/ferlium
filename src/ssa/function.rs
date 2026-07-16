use std::fmt;
use ustr::Ustr;

use crate::{
    format::FormatWith,
    hir::function::ArgConvention,
    list,
    module::{ModuleEnv, id::Id},
    ssa::value::{Constant, ConstantId},
    ssa::{self, Instruction, InstructionId, InstructionResult},
    types::r#type::{CallResultConvention, Type},
};

/// The origin of an SSA function parameter.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ParameterTag {
    /// A source-visible runtime parameter and its semantic call convention.
    Parameter(ArgConvention),

    /// A pointer to a dictionary.
    ///
    /// This is used to pass generic parameter witnesses.
    Dictionary,

    /// The caller-allocated out-pointer through which the function returns its result (see the
    /// return conventions in `doc/ssa-ir.md`): a value (`Value`), a place pointer (`AddressorPlace`),
    /// or — for a unit return — a `()` cell. Present on every lowered function as the last parameter;
    /// a `YieldedOnce` accessor keeps it for ABI uniformity but does not write through it (its yielded
    /// place flows out via the driving `project`).
    Return,
}

/// A parameter in the signature of an SSA function.
///
/// Parameters occupy the leading `ssa::Value::Parameter` slots in declaration order: the extra
/// (dictionary/evidence) parameters first, followed by the visible runtime arguments.
pub struct Parameter {
    /// The type of the parameter.
    pub type_: Type,

    /// The origin of the parameter.
    pub tag: ParameterTag,
}

/// A function in the SSA form of Ferlium.
pub struct Function {
    /// The name of the function.
    pub name: Ustr,

    /// The logical result convention, needed to distinguish a value out-pointer (`*T`) from an
    /// addressor result slot containing a place pointer (`**T`).
    result_convention: CallResultConvention,

    /// The parameters of the function, in slot order (extra parameters first, then arguments).
    parameters: Vec<Parameter>,

    /// Typed opaque HIR immediate representations referenced by `Value::Constant` operands.
    constants: Vec<Constant>,

    /// The instructions in the function.
    slots: list::List<Instruction>,

    /// The basic blocks in the function, the first of which being the function's entry.
    blocks: list::List<Option<BlockBounds>>,

    /// Cleanup landing pads for instructions whose implicit exceptional exit must unwind live
    /// locals. Kept sparse because only instructions emitted inside a scope with ownership
    /// obligations need an entry, and consulted only on the exceptional path. The exit may carry a
    /// language failure or out-of-band execution cancellation; neither changes the normal result.
    implicit_unwind_targets: Vec<(InstructionId, BlockId)>,
}

impl Function {
    /// Creates an empty function with the given name and logical result convention.
    pub fn new(name: Ustr, result_convention: CallResultConvention) -> Self {
        Self {
            name,
            result_convention,
            parameters: Vec::new(),
            constants: Vec::new(),
            slots: list::List::new(),
            blocks: list::List::new(),
            implicit_unwind_targets: Vec::new(),
        }
    }

    /// Returns how this function exposes its logical result.
    pub fn result_convention(&self) -> CallResultConvention {
        self.result_convention
    }

    /// Appends a parameter to this function's signature and returns its identity.
    pub fn add_parameter(&mut self, t: Type, tag: ParameterTag) -> ssa::ParameterId {
        let slot = ssa::ParameterId::from_index(self.parameters.len());
        self.parameters.push(Parameter { type_: t, tag });
        slot
    }

    /// Returns this function's parameters in slot order (extra parameters first, then arguments).
    pub fn parameters(&self) -> &[Parameter] {
        &self.parameters
    }

    /// Interns a typed immediate representation and returns its stable function-local identity.
    pub fn add_constant(
        &mut self,
        ty: Type,
        representation: crate::hir::value::LiteralValue,
        env: &ModuleEnv<'_>,
    ) -> ConstantId {
        debug_assert!(
            representation.has_representation_type_in(ty, env),
            "SSA constant representation does not match its declared type"
        );
        let constant = Constant { ty, representation };
        if let Some(index) = self
            .constants
            .iter()
            .position(|existing| existing == &constant)
        {
            return ConstantId::from_index(index);
        }
        let id = ConstantId::from_index(self.constants.len());
        self.constants.push(constant);
        id
    }

    /// Returns the constant identified by `id`.
    pub fn constant(&self, id: ConstantId) -> &Constant {
        &self.constants[id.as_index()]
    }

    /// Returns this function's typed immediate constant pool.
    pub fn constants(&self) -> &[Constant] {
        &self.constants
    }

    /// Returns an iterator over the identities of this function's basic blocks, the first of which
    /// is the entry block.
    pub fn blocks(&self) -> impl Iterator<Item = BlockId> + '_ {
        self.blocks.addresses()
    }

    /// Returns the identity of this function's entry block.
    pub fn entry(&self) -> BlockId {
        self.blocks
            .addresses()
            .next()
            .expect("a lowered function has at least an entry block")
    }

    /// Returns the value of `i`.
    pub fn at(&self, i: InstructionId) -> &Instruction {
        &self.slots[i]
    }

    /// Returns the basic block identified by `b`.
    pub fn block(&self, b: BlockId) -> Block<'_> {
        Block {
            identity: b,
            holder: self,
        }
    }

    /// Returns the basic block identified by `b`.
    pub fn block_mut(&mut self, b: BlockId) -> BlockMut<'_> {
        BlockMut {
            identity: b,
            holder: self,
        }
    }

    /// Appends a basic block to this function and returns it.
    pub fn add_block(&mut self) -> BlockMut<'_> {
        let b = self.blocks.append(None);
        BlockMut {
            identity: b,
            holder: self,
        }
    }

    /// Returns the register assigned by `i`, if any.
    pub fn definition(&self, i: InstructionId) -> Option<ssa::Value> {
        if self.slots[i].result() == InstructionResult::Nothing {
            None
        } else {
            Some(ssa::Value::Register(i))
        }
    }

    /// Records the cleanup landing pad to enter if `instruction` exits exceptionally without an
    /// explicit unwind successor of its own.
    pub fn set_implicit_unwind_target(&mut self, instruction: InstructionId, target: BlockId) {
        debug_assert!(
            self.implicit_unwind_target(instruction).is_none(),
            "an instruction has at most one implicit unwind target"
        );
        self.implicit_unwind_targets.push((instruction, target));
    }

    /// Returns the cleanup landing pad for an implicit exceptional exit at `instruction`.
    pub fn implicit_unwind_target(&self, instruction: InstructionId) -> Option<BlockId> {
        self.implicit_unwind_targets
            .iter()
            .find_map(|&(candidate, target)| (candidate == instruction).then_some(target))
    }

    /// Iterates over the exceptional cleanup edges carried in the function's sparse unwind table.
    pub fn implicit_unwind_targets(&self) -> impl Iterator<Item = (InstructionId, BlockId)> + '_ {
        self.implicit_unwind_targets.iter().copied()
    }
}

impl FormatWith<ModuleEnv<'_>> for Function {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        write!(f, "fn {}(", self.name)?;
        for (i, p) in self.parameters.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            let kind = match p.tag {
                ParameterTag::Parameter(ArgConvention::Let) => "arg let",
                ParameterTag::Parameter(ArgConvention::MutableRef) => "arg &mut",
                ParameterTag::Dictionary => "extra",
                ParameterTag::Return => "ret",
            };
            write!(
                f,
                "{}: @{} {}",
                ssa::Value::Parameter(ssa::ParameterId::from_index(i)),
                kind,
                p.type_.format_with(env)
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

        if !self.slots.is_empty() {
            writeln!(f)?;
            for b in self.blocks.addresses() {
                writeln!(f, "  b{}:", b.raw())?;
                for i in self.block(b).instructions() {
                    write!(
                        f,
                        "    {} = {}",
                        ssa::Value::Register(i),
                        self.at(i).format_with(env)
                    )?;
                    if let Some(unwind) = self.implicit_unwind_target(i) {
                        write!(f, " [unwind b{}]", unwind.raw())?;
                    }
                    writeln!(f)?;
                }
            }
        }

        Ok(())
    }
}

/// The identity of a basic block in the context of its containing function.
pub type BlockId = list::Address;

/// The first and last instructions of a basic block.
#[derive(PartialEq, Eq, Debug)]
struct BlockBounds {
    first: InstructionId,
    last: InstructionId,
}

/// A basic block within `holder`.
pub struct Block<'a> {
    /// The identity of this block.
    identity: BlockId,

    /// A reference to the function containing this block.
    holder: &'a Function,
}

impl<'a> Block<'a> {
    /// Returns the identity of `self`.
    pub fn id(&self) -> BlockId {
        self.identity
    }

    /// Returns `true` iff `self` contains no instruction.
    pub fn is_empty(&self) -> bool {
        self.holder.blocks[self.identity].is_none()
    }

    //noinspection DuplicatedCode
    /// Returns `true` iff the last instruction of `self` is a terminator.
    pub fn is_terminated(&self) -> bool {
        if let Some(bounds) = &self.holder.blocks[self.identity] {
            self.holder.at(bounds.last).is_terminator()
        } else {
            false
        }
    }

    /// Returns an iterator over the instructions in `self`.
    pub fn instructions(&self) -> BlockIterator<'a> {
        match self.holder.blocks[self.identity] {
            Some(BlockBounds { first: a, last: b }) => BlockIterator {
                slots: &self.holder.slots,
                last: Some(b),
                current: Some(a),
            },
            None => BlockIterator {
                slots: &self.holder.slots,
                last: None,
                current: None,
            },
        }
    }
}

pub struct BlockMut<'a> {
    /// The identity of this block.
    identity: BlockId,

    /// A reference to the function containing this block.
    holder: &'a mut Function,
}

/// A basic block in a SSA IR function.
impl BlockMut<'_> {
    /// Returns the identity of `self`.
    pub fn id(&self) -> BlockId {
        self.identity
    }

    /// Returns `true` iff `self` contains no instruction.
    pub fn is_empty(&self) -> bool {
        self.holder.blocks[self.identity].is_none()
    }

    //noinspection DuplicatedCode
    /// Returns `true` iff the last instruction of `self` is a terminator.
    pub fn is_terminated(&self) -> bool {
        if let Some(bounds) = &self.holder.blocks[self.identity] {
            self.holder.at(bounds.last).is_terminator()
        } else {
            false
        }
    }

    /// Adds `s` at the end of `self` and returns its identity.
    pub fn append(&mut self, s: Instruction) -> InstructionId {
        assert!(!self.is_terminated(), "insertion after terminator");
        let i = self.holder.slots.append(s);
        self.set_last(i);
        i
    }

    /// Assigns the last instruction of `self`.
    fn set_last(&mut self, i: InstructionId) {
        let j = self.holder.blocks[self.identity]
            .as_ref()
            .map_or(i, |bs| bs.first);
        self.holder.blocks[self.identity] = Some(BlockBounds { first: j, last: i });
    }
}

/// An iterator over the addresses of the instructions contained in a basic block.
pub struct BlockIterator<'a> {
    /// The instructions containing the subsequence that `self` represents.
    slots: &'a list::List<Instruction>,

    /// The identity of the next element in `self`, if any.
    current: Option<InstructionId>,

    /// The identity of the last element in `self`.
    last: Option<InstructionId>,
}

impl Iterator for BlockIterator<'_> {
    type Item = InstructionId;

    fn next(&mut self) -> Option<InstructionId> {
        if let Some(n) = self.current {
            self.current = if Some(n) != self.last {
                self.slots.address_after(n)
            } else {
                None
            };
            Some(n)
        } else {
            None
        }
    }
}
