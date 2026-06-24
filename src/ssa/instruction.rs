use std::any::Any;
use std::fmt;

use ustr::Ustr;

use crate::{
    Location, cached_primitive_ty, format::FormatWith, list, module::ModuleEnv, ssa,
    types::r#type::Type,
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

    /// Returns a borrowed, kind-discriminated view of this instruction.
    ///
    /// This lets backends (e.g. the WASM emitter) match on the instruction kind and read its
    /// kind-specific data without exposing the concrete kind structs or depending on backend
    /// types within this module.
    pub fn view(&self) -> InstructionView<'_> {
        self.kind.view(self)
    }

    /// Creates an `alloca` instruction for storage whose size is known at compile time.
    pub fn alloca(span: Location, ty: Type) -> Self {
        Instruction {
            span,
            operands: vec![],
            kind: Box::new(Alloca { ty }),
        }
    }

    /// Creates an `alloca` instruction for storage whose size is known only at run time.
    ///
    /// `witness` is the place of the `Value` dictionary witnessing the run-time layout of `ty`;
    /// its `SIZE` and `ALIGN` associated const entries determine the size and alignment of the
    /// allocation.
    pub fn alloca_dynamic(span: Location, ty: Type, witness: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![witness],
            kind: Box::new(Alloca { ty }),
        }
    }

    pub fn alloca_place(span: Location, pointing_to: Type) -> Self {
        Instruction {
            span,
            operands: vec![],
            kind: Box::new(AllocaPlace { pointing_to }),
        }
    }

    /// Creates a 'br' instruction with the given properties.
    pub fn br(span: Location, target: ssa::BlockIdentity) -> Self {
        Instruction {
            span,
            operands: vec![],
            kind: Box::new(UnconditionalBranch { target }),
        }
    }

    /// Creates a `call` instruction with the given properties.
    ///
    /// A call yields no register: a callee with a non-`()` result writes it through the return
    /// out-pointer passed as the call's last operand. `result` records the callee's logical return
    /// type as IR metadata.
    pub fn call<T: IntoIterator<Item = ssa::Value>>(
        span: Location,
        callee: ssa::Value,
        arguments: T,
    ) -> Self {
        let mut operands = vec![callee];
        operands.extend(arguments);
        Instruction {
            span,
            operands,
            kind: Box::new(Call {}),
        }
    }

    /// Creates a `compare_eq` instruction with the given properties.
    pub fn compare_eq(span: Location, v1: ssa::Value, v2: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![v1, v2],
            kind: Box::new(CompareEqual {}),
        }
    }

    /// Creates a `condbr` instruction with the given properties.
    pub fn condbr(
        span: Location,
        condition: ssa::Value,
        on_success: ssa::BlockIdentity,
        on_failure: ssa::BlockIdentity,
    ) -> Self {
        Instruction {
            span,
            operands: vec![condition],
            kind: Box::new(ConditionalBranch {
                on_success,
                on_failure,
            }),
        }
    }

    /// Creates a 'load' instruction with the given properties.
    pub fn load(span: Location, source: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![source],
            kind: Box::new(Load {}),
        }
    }

    /// Creates a 'project' instruction accessing the tuple `source` at index `i`
    pub fn project(span: Location, source: ssa::Value, i: usize, ty: Type) -> Self {
        Instruction {
            span,
            operands: vec![source],
            kind: Box::new(Project { index: i, ty }),
        }
    }

    /// Creates a `variant` instruction, which builds a tagged variant *shell* of type `ty`: the
    /// result is a register holding `Value::Variant { tag, <uninitialized payload> }`. The
    /// constructing site stores the shell into the variant's destination and then fills the payload
    /// in place through a projection of that destination (variant payload index `0`), so the
    /// payload aggregate — which may be generic and thus have no `Value` layout witness — is never
    /// materialized into a temporary.
    pub fn variant(span: Location, tag: Ustr, t: Type) -> Self {
        Instruction {
            span,
            operands: vec![],
            kind: Box::new(Variant { tag, type_: t }),
        }
    }

    /// Creates an `extract_tag` instruction, which reads the tag of the variant at the `variant`
    /// place and yields it as an `int` register (matching the HIR interpreter's tag encoding).
    pub fn extract_tag(span: Location, variant: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![variant],
            kind: Box::new(ExtractTag {}),
        }
    }

    /// Creates a 'ret' instruction.
    ///
    /// The return value is not an operand: the function writes its result into the return
    /// out-pointer (the last parameter) before returning.
    pub fn ret(span: Location) -> Self {
        Instruction {
            span,
            operands: vec![],
            kind: Box::new(Ret {}),
        }
    }

    /// Creates a `stack_save` instruction, whose result is a marker for the current top of the
    /// stack.
    ///
    /// Paired with `stack_restore`, this brackets a region (such as a loop body) so that the
    /// temporaries it allocates are reclaimed on every back-edge and exit, bounding stack use.
    pub fn stack_save(span: Location) -> Self {
        Instruction {
            span,
            operands: vec![],
            kind: Box::new(StackSave {}),
        }
    }

    /// Creates a `stack_restore` instruction, which resets the top of the stack to `marker` (the
    /// result of an earlier `stack_save`), reclaiming everything allocated since.
    pub fn stack_restore(span: Location, marker: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![marker],
            kind: Box::new(StackRestore {}),
        }
    }

    /// Creates a 'store' instruction with the given properties.
    pub fn store(span: Location, value: ssa::Value, destination: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![value, destination],
            kind: Box::new(Store {}),
        }
    }

    /// Creates a `memcpy` instruction, which copies the pointee of `source` (a place) into
    /// `destination` (a place) directly, without first materializing it in a register.
    ///
    /// This is the fused form of a `load` immediately followed by a `store` of the loaded value: a
    /// shallow, place-to-place copy. Non-trivial reads are wrapped in `Value::clone` by HIR before
    /// reaching the emitter, so a `memcpy` (like a bare `load`) is a move for non-trivially-copyable
    /// pointees and a copy for trivial ones.
    pub fn memcpy(span: Location, source: ssa::Value, destination: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![source, destination],
            kind: Box::new(Memcpy {}),
        }
    }

    /// Creates a 'drop' instruction.
    ///
    /// Drops the pointee of `target` (a place) by invoking `callee` (a `Value::drop`
    /// implementation, given either as a constant function reference or as a value loaded from a
    /// dictionary), but **only if** the pointee is currently initialized. An already-uninitialized
    /// (moved-out or never-initialized) pointee is left untouched. This init guard is what makes
    /// the inline drops the emitter places at scope-exit edges run exactly once.
    pub fn drop(span: Location, target: ssa::Value, callee: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![target, callee],
            kind: Box::new(Drop {}),
        }
    }
}

impl FormatWith<ModuleEnv<'_>> for Instruction {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        self.kind.fmt_within(f, self, env)
    }
}

/// A type encoding the kind-specific contents of an instruction.
pub trait InstructionKind: Any {
    /// The type of the result of `self`, which is the kind-specific part of `whole`.
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        InstructionResult::Nothing
    }

    /// Returns `true` iff `self` is a terminator.
    fn is_terminator(&self) -> bool {
        false
    }

    /// Returns a borrowed, kind-discriminated view of `self`, which is the kind-specific part of
    /// `whole`. Backends match on this view to lower the instruction.
    fn view<'a>(&'a self, whole: &'a Instruction) -> InstructionView<'a>;

    /// Computes a textual representation of `self`, which is the kind-specific part of `whole`.
    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        env: &ModuleEnv<'_>,
    ) -> fmt::Result;
}

/// A borrowed, kind-discriminated view of an [`Instruction`].
///
/// This is the backend-facing projection of the private instruction-kind structs: it exposes the
/// data each backend needs to lower an instruction without leaking backend types into this module
/// or making the kind structs public. Operands (such as a `load` source or a `store`
/// value/destination) remain available through `Instruction::operands`.
pub enum InstructionView<'a> {
    /// A stack allocation of an instance of `ty`. For a non-statically-sized `ty`, `witness` is
    /// the `Value` dictionary place witnessing its run-time layout (the instruction's sole operand).
    Alloca {
        ty: Type,
        witness: Option<&'a ssa::Value>,
    },

    /// A stack allocation of a pointer to an instance of `pointing_to`.
    AllocaPlace { pointing_to: Type },

    /// A function call. Operand `0` is the callee; the remaining operands are the arguments,
    /// the last of which is the return out-pointer for a non-`()` result.
    Call,

    /// An equality comparison of operands `0` and `1`.
    CompareEqual,

    /// A conditional branch on operand `0`.
    ConditionalBranch {
        on_success: ssa::BlockIdentity,
        on_failure: ssa::BlockIdentity,
    },

    /// An unconditional branch to `target`.
    UnconditionalBranch { target: ssa::BlockIdentity },

    /// A load of the value at the place given by operand `0`.
    Load,

    /// A projection of field `index` (of type `ty`) out of the aggregate place at operand `0`.
    Project { index: usize, ty: Type },

    /// A return. The result, if any, has already been written through the return out-pointer.
    Ret,

    /// A construction of a variant tagged `tag`, wrapping the value moved out of the payload place
    /// at operand `0`.
    Variant { tag: Ustr },

    /// An extraction of the tag of the variant at the place given by operand `0`, yielded as an
    /// `int` register.
    ExtractTag,

    /// A store of operand `0` (a value) into operand `1` (a place).
    Store,

    /// A place-to-place copy of the pointee of operand `0` (a place) into operand `1` (a place),
    /// without materializing it in a register.
    Memcpy,

    /// A capture of the current top of the stack, yielded as a marker register.
    StackSave,

    /// A reset of the top of the stack to the marker at operand `0`.
    StackRestore,

    /// An init-guarded drop of the pointee at operand `0` (a place), invoking operand `1` (a
    /// `Value::drop` callee) only if that pointee is currently initialized.
    Drop,
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

    /// A backend-internal marker for a saved top of the stack (the result of `stack_save`). It is
    /// not a Ferlium-expressible type; it is only consumed by a matching `stack_restore`.
    StackMarker,

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
///
/// The instruction defines a place capable of storing an instance of `ty`, allocated on the
/// stack.
///
/// If `ty` is not statically sized, the instruction carries a single operand: the `Value`
/// dictionary witnessing the run-time layout of `ty` (see `Instruction::alloca_dynamic`).
struct Alloca {
    /// The type of the allocation.
    pub ty: Type,
}

impl InstructionKind for Alloca {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        InstructionResult::pointer_to(InstructionResult::Lowered(self.ty))
    }

    fn view<'a>(&'a self, whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::Alloca {
            ty: self.ty,
            witness: whole.operands.first(),
        }
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        if let Some(witness) = whole.operands.first() {
            write!(f, "alloca {} using {}", self.ty.format_with(env), witness)
        } else {
            write!(f, "alloca {}", self.ty.format_with(env))
        }
    }
}

/// A stack allocation of a pointer to a value.
pub struct AllocaPlace {
    /// The type of object the allocated pointer points to.
    pub pointing_to: Type,
}

impl InstructionKind for AllocaPlace {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        InstructionResult::pointer_to(InstructionResult::pointer_to(InstructionResult::Lowered(
            self.pointing_to,
        )))
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::AllocaPlace {
            pointing_to: self.pointing_to,
        }
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        _whole: &Instruction,
        env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "alloca_place {}", self.pointing_to.format_with(env))
    }
}

/// A function call in SSA.
struct Call {}

impl InstructionKind for Call {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        // Calls do not yield a register: a callee with a non-`()` result writes it through the
        // return out-pointer passed as the call's last operand.
        InstructionResult::Nothing
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::Call
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "call {}(", whole.operands[0])?;
        for i in 1..whole.operands.len() {
            if i > 1 {
                write!(f, ", ")?;
            }
            write!(f, "{}", whole.operands[i])?;
        }
        write!(f, ")")
    }
}

/// A comparison for equality in SSA.
struct CompareEqual {}

impl InstructionKind for CompareEqual {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        InstructionResult::Lowered(cached_primitive_ty!(bool))
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::CompareEqual
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "comp_eq {} {}", whole.operands[0], whole.operands[1])
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

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::ConditionalBranch {
            on_success: self.on_success,
            on_failure: self.on_failure,
        }
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(
            f,
            "condbr {}, %b{}, &b{}",
            whole.operands[0],
            self.on_success.raw(),
            self.on_failure.raw()
        )
    }
}

/// A load instruction in SSA, which copies a value stored in memory into a register.
struct Load {}

impl InstructionKind for Load {
    fn result(&self, whole: &Instruction) -> InstructionResult {
        InstructionResult::pointee_of(InstructionResult::Same(whole.operands[0].clone()))
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::Load
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "load {}", whole.operands[0])
    }
}

/// A project instruction in SSA.
struct Project {
    /// The index to project the tuple to
    index: usize,

    /// The type of the projected value
    ty: Type,
}

impl InstructionKind for Project {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        // The operand is a place (pointer to the aggregate) and the result is a place: a pointer to
        // the projected element. A register value is obtained by `load`ing the result.
        InstructionResult::pointer_to(InstructionResult::Lowered(self.ty))
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::Project {
            index: self.index,
            ty: self.ty,
        }
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "project {} from {}", self.index, whole.operands[0])
    }
}

/// A return instruction in SSA.
struct Ret {}

impl InstructionKind for Ret {
    fn is_terminator(&self) -> bool {
        true
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::Ret
    }

    fn fmt_within(
        &self,
        _f: &mut fmt::Formatter<'_>,
        _whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(_f, "ret")
    }
}

/// A variant shell construction in SSA.
///
/// Yields a `Value::Variant { tag, payload }` whose payload is left uninitialized; the constructing
/// site fills the payload in place after storing the shell into the variant's destination. The
/// memory model is the HIR interpreter's `Value::Variant`.
struct Variant {
    /// The tag of the constructed variant.
    tag: Ustr,

    /// The type of the constructed variant.
    type_: Type,
}

impl InstructionKind for Variant {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        InstructionResult::Lowered(self.type_)
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::Variant { tag: self.tag }
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        let _ = whole;
        write!(f, "variant .{}", self.tag)
    }
}

/// A variant tag extraction in SSA, reading the tag of the variant at the operand place as an `int`.
struct ExtractTag {}

impl InstructionKind for ExtractTag {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        InstructionResult::Lowered(cached_primitive_ty!(isize))
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::ExtractTag
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "extract_tag {}", whole.operands[0])
    }
}

/// A store instruction in SSA, which writes the contents of a register to memory.
struct Store {}

impl InstructionKind for Store {
    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::Store
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "store {} to {}", whole.operands[0], whole.operands[1])
    }
}

/// A place-to-place copy in SSA, which copies the pointee of the source place (operand `0`)
/// into the destination place (operand `1`) without materializing it in a register.
struct Memcpy {}

impl InstructionKind for Memcpy {
    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::Memcpy
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "memcpy {} to {}", whole.operands[0], whole.operands[1])
    }
}

/// A capture of the current top of the stack in SSA.
struct StackSave {}

impl InstructionKind for StackSave {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        InstructionResult::StackMarker
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::StackSave
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        _whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "stack_save")
    }
}

/// A reset of the top of the stack to a previously saved marker in SSA.
struct StackRestore {}

impl InstructionKind for StackRestore {
    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::StackRestore
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "stack_restore {}", whole.operands[0])
    }
}

/// An init-guarded drop in SSA.
///
/// Operand `0` is the place whose pointee is dropped; operand `1` is the `Value::drop` callee. The
/// drop runs only if the pointee is initialized, so a value already moved out (left uninitialized)
/// is skipped.
struct Drop {}

impl InstructionKind for Drop {
    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::Drop
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "drop {} via {}", whole.operands[0], whole.operands[1])
    }
}

/// A SSA terminator that unconditionally transfers control flow to the start of another block.
struct UnconditionalBranch {
    target: ssa::BlockIdentity,
}

impl InstructionKind for UnconditionalBranch {
    fn is_terminator(&self) -> bool {
        true
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::UnconditionalBranch {
            target: self.target,
        }
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        _whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "br {}", self.target.raw())
    }
}
