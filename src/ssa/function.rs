use std::fmt;
use std::collections::HashMap;

use ustr::Ustr;

use crate::{
  ssa,
  ssa::{Instruction, InstructionIdentity, InstructionResult},
  list,
};

/// A function in the SSA form of Ferlium.
pub struct Function {

  /// The name of the function.
  pub name: Ustr,

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
    Self { name, slots: list::List::new(), blocks: list::List::new(), uses: HashMap::new() }
  }

  /// Returns the value of `i`.
  pub fn at(&self, i: InstructionIdentity) -> &Instruction {
    &self.slots[i].instruction
  }

  /// Returns the basic block identified by `b`.
  pub fn block(&self, b: BlockIdentity) -> Block<'_> {
    Block { identity: b, holder: self }
  }

    /// Returns the basic block identified by `b`.
  pub fn block_mut(&mut self, b: BlockIdentity) -> BlockMut<'_> {
    BlockMut { identity: b, holder: self }
  }

  /// Appends a basic block to this function and returns it.
  pub fn add_block(&mut self) -> BlockMut<'_> {
    let b = self.blocks.append(None);
    BlockMut { identity: b, holder: self }
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
    F: FnOnce(&mut Self, Instruction) -> InstructionIdentity
  {
    let operands = s.operands.clone();
    let user = perform(self, s);
    for (i, o) in operands.iter().enumerate() {
      self.uses.entry(o.clone()).or_default().push(Use { user: user, index: i });
    }
    user
  }

}

impl fmt::Display for Function {

  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "fn {}:", self.name.to_string())?;

    if !self.slots.is_empty() {
      write!(f, "\n")?;
      for b in self.blocks.addresses() {
        write!(f, "  {}:\n", b.raw())?;
        for i in self.block(b).instructions() {
          write!(f, "    {} = {}\n", ssa::Value::Register(i), self.at(i))?;
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
  index: usize

}

/// The identity of a basic block in the context of its containing function.
pub type BlockIdentity = list::Address;

/// The first and last instructions of a basic block.
#[derive(PartialEq, Eq, Debug)]
struct BlockBounds(InstructionIdentity, InstructionIdentity);

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
    self.holder.blocks[self.identity] == None
  }

  /// Returns `true` iff the last instruction of `self` is a terminator.
  pub fn is_terminated(&self) -> bool {
    self.holder.blocks[self.identity]
      .as_ref()
      .map_or(false, |bs| self.holder.at(bs.1).is_terminator())
  }

  /// Returns an iterator over the instructions in `self`.
  pub fn instructions(&self) -> BlockIterator<'a> {
    if let Some(BlockBounds(a, b)) = self.holder.blocks[self.identity] {
      BlockIterator { slots: &self.holder.slots, last: Some(b), current: Some(a) }
    } else {
      BlockIterator { slots: &self.holder.slots, last: None, current: None }
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

  /// Returns `true` iff the last instruction of `self` is a terminator.
  pub fn is_terminated(&self) -> bool {
    self.holder.blocks[self.identity]
      .as_ref()
      .map_or(false, |bs| self.holder.at(bs.1).is_terminator())
  }

  /// Adds `s` at the end of `self` and returns its identity.
  pub fn append(&mut self, s: Instruction) -> InstructionIdentity {
    assert!(!self.is_terminated(), "insertion after terminator");
    let i = self.holder.insert(s, |f, s| {
      f.slots.append(InstructionSlot { instruction: s, parent: self.identity })
    });

    self.set_last(i);
    i
  }

  /// Adds `s` at the start of `self` and returns its identity.
  pub fn prepend(&mut self, s: Instruction) -> InstructionIdentity {
    let i = self.holder.insert(s, |f, s| {
      f.slots.prepend(InstructionSlot { instruction: s, parent: self.identity })
    });

    self.set_first(i);
    i
  }

  /// Assigns the first instruction of `self`.
  fn set_first(&mut self, i: InstructionIdentity) {
    let j = self.holder.blocks[self.identity].as_ref().map_or(i, |bs| bs.1);
    self.holder.blocks[self.identity] = Some(BlockBounds(i, j));
  }

  /// Assigns the last instruction of `self`.
  fn set_last(&mut self, i: InstructionIdentity) {
    let j = self.holder.blocks[self.identity].as_ref().map_or(i, |bs| bs.0);
    self.holder.blocks[self.identity] = Some(BlockBounds(j, i));
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
      self.current = if n != self.last { self.slots.address_after(n) } else { None };
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
  parent: BlockIdentity

}
