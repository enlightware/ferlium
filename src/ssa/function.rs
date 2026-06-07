use std::collections::HashMap;
use std::fmt;

use ustr::Ustr;

use crate::{
    format::FormatWith,
    list,
    module::ModuleEnv,
    ssa,
    ssa::{Instruction, InstructionIdentity, InstructionResult},
    types::r#type::Type,
};

/// A visible runtime argument or a hidden extra parameter.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ParameterKind {
    /// A visible runtime argument, with how it is passed in.
    Argument(ArgumentPassing),

    /// A hidden dictionary/evidence parameter resolving polymorphism.
    Extra,
}

/// How a visible argument is conveyed into the function.
///
/// The callee side of the slot rule in `doc/hir-to-ssa.md` §4: a by-value argument's register holds
/// the value, whereas a by-reference argument's register is a pointer to the caller's storage.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ArgumentPassing {
    /// Held directly in its register (a `TrivialCopy` by-value argument).
    Value,

    /// A pointer to mutable caller storage (an `&mut` / inferred-inout argument).
    MutableReference,

    /// A pointer to shared caller storage (a `&` argument).
    SharedReference,
}

/// A parameter in the signature of an SSA function.
///
/// Parameters occupy the leading `ssa::Value::Parameter` slots in declaration order: the extra
/// (dictionary/evidence) parameters first, followed by the visible runtime arguments.
pub struct Parameter {
    /// The type of the parameter.
    pub ty: Type,

    /// Whether the parameter is a visible argument or a hidden extra parameter.
    pub kind: ParameterKind,
}

/// A function in the SSA form of Ferlium.
pub struct Function {
    /// The name of the function.
    pub name: Ustr,

    /// The parameters of the function, in slot order (extra parameters first, then arguments).
    parameters: Vec<Parameter>,

    /// The instructions in the function.
    slots: list::List<InstructionSlot>,

    /// The basic blocks in the function, the first of which being the function's entry.
    blocks: list::List<Option<BlockBounds>>,

    /// The use chains of the values in this function.
    uses: HashMap<ssa::Value, Vec<Use>>,
}

impl Function {
    /// Creates an instance with the given properties.
    pub fn new(name: Ustr) -> Self {
        Self {
            name,
            parameters: Vec::new(),
            slots: list::List::new(),
            blocks: list::List::new(),
            uses: HashMap::new(),
        }
    }

    /// Appends a parameter to this function's signature and returns its slot.
    pub fn add_parameter(&mut self, t: Type, kind: ParameterKind) -> usize {
        let slot = self.parameters.len();
        self.parameters.push(Parameter { ty: t, kind });
        slot
    }

    /// Returns the value of `i`.
    pub fn at(&self, i: InstructionIdentity) -> &Instruction {
        &self.slots[i].instruction
    }

    /// Returns the basic block identified by `b`.
    pub fn block(&self, b: BlockIdentity) -> Block<'_> {
        Block {
            identity: b,
            holder: self,
        }
    }

    /// Returns the basic block identified by `b`.
    pub fn block_mut(&mut self, b: BlockIdentity) -> BlockMut<'_> {
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
    pub fn definition(&self, i: InstructionIdentity) -> Option<ssa::Value> {
        if self.slots[i].instruction.result() == InstructionResult::Nothing {
            None
        } else {
            Some(ssa::Value::Register(i))
        }
    }

    /// Returns the basic block in which `i` is defined.
    pub fn block_defining(&self, i: InstructionIdentity) -> BlockIdentity {
        self.slots[i].parent
    }

    /// Inserts `s` with `perform` and returns its identity.
    fn insert<F>(&mut self, s: Instruction, perform: F) -> InstructionIdentity
    where
        F: FnOnce(&mut Self, Instruction) -> InstructionIdentity,
    {
        let operands = s.operands.clone();
        let user = perform(self, s);
        for (i, o) in operands.iter().enumerate() {
            self.uses
                .entry(o.clone())
                .or_default()
                .push(Use { user, index: i });
        }
        user
    }
}

impl FormatWith<ModuleEnv<'_>> for Function {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        write!(f, "fn {}(", self.name)?;
        for (i, p) in self.parameters.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            let kind = match p.kind {
                ParameterKind::Argument(ArgumentPassing::Value) => "arg",
                ParameterKind::Argument(ArgumentPassing::MutableReference) => "arg &mut",
                ParameterKind::Argument(ArgumentPassing::SharedReference) => "arg &",
                ParameterKind::Extra => "extra",
            };
            write!(
                f,
                "{}: @{} {}",
                ssa::Value::Parameter(i),
                kind,
                p.ty.format_with(env)
            )?;
        }
        write!(f, "):")?;

        if !self.slots.is_empty() {
            writeln!(f)?;
            for b in self.blocks.addresses() {
                writeln!(f, "  {}:", b.raw())?;
                for i in self.block(b).instructions() {
                    writeln!(
                        f,
                        "    {} = {}",
                        ssa::Value::Register(i),
                        self.at(i).format_with(env)
                    )?;
                }
            }
        }

        Ok(())
    }
}

/// A pair representing the use of a value in an instruction.
#[derive(PartialEq, Eq, Debug)]
pub struct Use {
    /// The ID of the user that contains this use.
    user: InstructionIdentity,

    /// The index of this use in `user`'s operands.
    index: usize,
}

/// The identity of a basic block in the context of its containing function.
pub type BlockIdentity = list::Address;

/// The first and last instructions of a basic block.
#[derive(PartialEq, Eq, Debug)]
struct BlockBounds {
    first: InstructionIdentity,
    last: InstructionIdentity,
}

/// A basic block within `holder`.
pub struct Block<'a> {
    /// The identity of this block.
    identity: BlockIdentity,

    /// A reference to the function containing this block.
    holder: &'a Function,
}

impl<'a> Block<'a> {
    /// Returns the identity of `self`.
    pub fn id(&self) -> BlockIdentity {
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
    identity: BlockIdentity,

    /// A reference to the function containing this block.
    holder: &'a mut Function,
}

/// A basic block in a Hylo IR function.
impl BlockMut<'_> {
    /// Returns the identity of `self`.
    pub fn id(&self) -> BlockIdentity {
        self.identity
    }

    /// Returns `true` iff `self` contains no instruction.
    pub fn is_empty(&self) -> bool {
        self.holder.blocks[self.identity] == None
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
    pub fn append(&mut self, s: Instruction) -> InstructionIdentity {
        assert!(!self.is_terminated(), "insertion after terminator");
        let i = self.holder.insert(s, |f, s| {
            f.slots.append(InstructionSlot {
                instruction: s,
                parent: self.identity,
            })
        });

        self.set_last(i);
        i
    }

    /// Adds `s` at the start of `self` and returns its identity.
    pub fn prepend(&mut self, s: Instruction) -> InstructionIdentity {
        let i = self.holder.insert(s, |f, s| {
            f.slots.prepend(InstructionSlot {
                instruction: s,
                parent: self.identity,
            })
        });

        self.set_first(i);
        i
    }

    /// Assigns the first instruction of `self`.
    fn set_first(&mut self, i: InstructionIdentity) {
        let j = self.holder.blocks[self.identity]
            .as_ref()
            .map_or(i, |bs| bs.last);
        self.holder.blocks[self.identity] = Some(BlockBounds { first: i, last: j });
    }

    /// Assigns the last instruction of `self`.
    fn set_last(&mut self, i: InstructionIdentity) {
        let j = self.holder.blocks[self.identity]
            .as_ref()
            .map_or(i, |bs| bs.first);
        self.holder.blocks[self.identity] = Some(BlockBounds { first: j, last: i });
    }
}

/// An iterator over the addresses of the instructions contained in a basic block.
pub struct BlockIterator<'a> {
    /// The instructions containing the subsequence that `self` represents.
    slots: &'a list::List<InstructionSlot>,

    /// The identity of the next element in `self`, if any.
    current: Option<InstructionIdentity>,

    /// The identity of the last element in `self`.
    last: Option<InstructionIdentity>,
}

impl Iterator for BlockIterator<'_> {
    type Item = InstructionIdentity;

    fn next(&mut self) -> Option<InstructionIdentity> {
        if let Some(n) = self.current {
            self.current = if n != self.last {
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

/// A container wrapping an instruction toghether with additional related properties.
struct InstructionSlot {
    /// The instruction occupying the slot.
    instruction: Instruction,

    /// The basic block containing the instruction.
    parent: BlockIdentity,
}
