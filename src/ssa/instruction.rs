use std::any::Any;
use std::fmt;

use crate::{
  Location, cached_primitive_ty, list, ssa, r#type::{Type}
};

/// The identity of an instruction in the context of its containing funtion.
pub type InstructionIdentity = list::Address;

/// An instruction in the SSA form of Ferlium.
pub struct Instruction {

  /// The region of the code corresponding to this instruction.
  pub span: Location,

  /// The operands of the instruction.
  pub operands: Vec<ssa::Value>,

  /// The kind-specific part of `self`.
  pub kind: Box<dyn InstructionKind>,

}

impl Instruction {

  /// The type of the instruction's result.
  pub fn result(&self) -> InstructionResult {
    self.kind.result(self)
  }

  /// Returns `true` iff `self` is a terminator.
  pub fn is_terminator(&self) -> bool {
    self.kind.is_terminator()
  }

  /// Creates an `alloca` instruction with the given properties.
  pub fn alloca(span: Location, ty: Type) -> Self {
    Instruction { span, operands: vec![], kind: Box::new(Alloca { ty }) }
  }

  /// Creates a 'br' instruction with the given properties.
  pub fn br(span: Location, target: ssa::BlockIdentity) -> Self {
    Instruction { span,operands: vec![], kind: Box::new(UnconditionalBranch {target}) }
  }

  /// Creates a `call` instruction with the given properties.
  pub fn call<T: IntoIterator<Item = ssa::Value>>(
    span: Location, callee: ssa::Value, arguments: T, ty: Type
  ) -> Self {
    let mut operands = vec![callee];
    operands.extend(arguments);
    Instruction { span, operands, kind: Box::new(Call { ty }) }
  }

  /// Creates a `compare_eq` instruction with the given properties.
  pub fn compare_eq(span: Location, v1: ssa::Value, v2: ssa::Value) -> Self {
    Instruction { span, operands: vec![v1, v2], kind: Box::new(CompareEqual {}) }
  }

  /// Creates a `condbr` instruction with the given properties.
  pub fn condbr(
    span: Location, condition: ssa::Value,
    on_success: ssa::BlockIdentity, on_failure: ssa::BlockIdentity
  ) -> Self {
    Instruction {
      span,
      operands: vec![condition],
      kind: Box::new(ConditionalBranch { on_success, on_failure })
    }
  }

  /// Creates a 'load' instruction with the given properties.
  pub fn load(span: Location, source: ssa::Value) -> Self {
    Instruction { span, operands: vec![source], kind: Box::new(Load {}) }
  }

  /// Creates a 'project' instruction accessing the tuple `source` at index `i`
  pub fn project(span: Location, source: ssa::Value, i: usize, ty: Type) -> Self {
    Instruction { span, operands: vec![source], kind: Box::new(Project {index:i, ty:ty}) }
  }

  /// Creates a 'ret' instruction with the given properties.
  pub fn ret(span: Location, value: ssa::Value) -> Self {
    Instruction { span, operands: vec![value], kind: Box::new(Ret {}) }
  }

  /// Creates a 'store' instruction with the given properties.
  pub fn store(span: Location, value: ssa::Value, target: ssa::Value) -> Self {
    Instruction { span, operands: vec![value, target], kind: Box::new(Store {}) }
  }

}

impl fmt::Display for Instruction {

  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.kind.fmt_within(f, self)
  }

}

/// A type encoding the kind-specific contents of an instruction.
pub trait InstructionKind: Any {

  /// The type of the result of `self`, which is the kind-specific part of `whole`.
  fn result(&self, whole: &Instruction) -> InstructionResult { InstructionResult::Nothing }

  /// Returns `true` iff `self` is a terminator.
  fn is_terminator(&self) -> bool { false }

  /// Computes a textual representation of `self`, which is the kind-specific part of `whole`.
  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> std::fmt::Result;

}

/// The type of an instruction's result.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum InstructionResult {

  /// A type expressible in Ferlium.
  Lowered(Type),

  /// The type of a SSA value.
  Same(ssa::Value),

  /// The type of the value referred to by a pointer.
  Pointee(Box<InstructionResult>),

  /// A pointer to a type.
  Pointer(Box<InstructionResult>),

  /// The type of an isntruction that doesn't produce any value.
  Nothing,

}

impl InstructionResult {

  /// Returns the type of a pointee referred to by an instance of `pointer`.
  fn pointee_of(pointer: InstructionResult) -> InstructionResult {
    InstructionResult::Pointee(Box::new(pointer))
  }

  /// Returns the type of a pointer to an instance of `pointee`.
  fn pointer_to(pointee: InstructionResult) -> InstructionResult {
    InstructionResult::Pointer(Box::new(pointee))
  }

}

/// A stack allocation.
struct Alloca {

  /// The type of the allocation.
  pub ty: Type,

}

impl InstructionKind for Alloca {

  fn result(&self, whole: &Instruction) -> InstructionResult {
    InstructionResult::pointer_to(InstructionResult::Lowered(self.ty))
  }

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> fmt::Result {
    write!(f, "alloca {:?}", self.ty)
  }

}

/// A function call in SSA.
struct Call {

  /// The type of the value returned by the callee.
  pub ty: Type,

}

impl InstructionKind for Call {

  fn result(&self, whole: &Instruction) -> InstructionResult {
    InstructionResult::Lowered(self.ty)
  }

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> fmt::Result {
    write!(f, "call {}(", whole.operands[0])?;
    for i in 1..whole.operands.len() {
      if i > 1 { write!(f, ", ")?; }
      write!(f, "{}", whole.operands[i])?;
    }
    write!(f, ")")
  }

}

/// A conditional jump in SSA.
struct ConditionalBranch {

  /// The target of the branch if the condition holds.
  on_success: ssa::BlockIdentity,

  /// The target of the branch if the condition does not hold.
  on_failure: ssa::BlockIdentity,

}

impl InstructionKind for ConditionalBranch {

  fn is_terminator(&self) -> bool {
    true
  }

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> fmt::Result {
    write!(
      f, "condbr {}, %b{}, &b{}",
      whole.operands[0], self.on_success.raw(), self.on_failure.raw())
  }

}

/// A load instruction in SSA, which copies a value stored in memory into a register.
struct Load {}

impl InstructionKind for Load {

  fn result(&self, whole: &Instruction) -> InstructionResult {
    InstructionResult::pointee_of(InstructionResult::Same(whole.operands[0].clone()))
  }

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> fmt::Result {
    write!(f, "load {}", whole.operands[0])
  }

}

/// A project instruction in SSA.
struct Project {

  /// The index to project the tuple to
  index: usize,

  /// The type of the projected value
  ty: Type
}

impl InstructionKind for Project {

  fn result(&self, whole: &Instruction) -> InstructionResult {
      InstructionResult::Lowered(self.ty)
  }

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> std::fmt::Result {
      write!(f, "project {} from {}", self.index, whole.operands[0])
  }

}

/// A return instruction in SSA.
struct Ret {}

impl InstructionKind for Ret {

  fn is_terminator(&self) -> bool {
    true
  }

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> fmt::Result {
    write!(f, "ret {}", whole.operands[0])
  }

}

/// A store instruction in SSA, which writes the contents of a register to memory.
struct Store {}

impl InstructionKind for Store {

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> fmt::Result {
    write!(f, "store {} to {}", whole.operands[0], whole.operands[1])
  }

}

/// A SSA terminator that unconditionally transfers control flow to the start of another block, unconditionally.
struct UnconditionalBranch {
    target: ssa::BlockIdentity
}

impl InstructionKind for UnconditionalBranch {

  fn is_terminator(&self) -> bool {
    true
  }

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> fmt::Result {
    write!(f, "br {}", self.target.raw())
  }
}

struct CompareEqual {}

impl InstructionKind for CompareEqual {

  fn result(&self, whole: &Instruction) -> InstructionResult {
    InstructionResult::pointer_to(InstructionResult::Lowered(cached_primitive_ty!(bool)))
  }

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> std::fmt::Result {
      write!(f, "comp_eq {} {}", whole.operands[0], whole.operands[1])
  }

}
