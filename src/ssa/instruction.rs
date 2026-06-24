use std::any::Any;
use std::fmt;

use ustr::Ustr;

use crate::{
    Location, cached_primitive_ty, format::FormatWith, list,
    module::{ModuleEnv, TraitDictionaryId},
    ssa::{self, value::FunctionReference},
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
    ///
    /// ## Callee contract
    ///
    /// Every callable is a function value — a code identity that may additionally carry *hidden
    /// evidence* (the dictionaries/field-indices a generic instantiation needs) and an owned
    /// *closure environment*. Bare functions, dictionary/witness-table methods, and closures are all
    /// the same kind of value and are called the same way.
    ///
    /// The `callee` operand (operand `0`) is therefore **one of two forms**:
    /// - a constant [`ssa::Value::Function`] — a direct call to a statically known function (no
    ///   hidden evidence, no environment); or
    /// - the **place** of a function value — a function-typed local or parameter, a closure, or a
    ///   method slot `project`ed out of a dictionary/witness-table tuple.
    ///
    /// A function value is **never loaded into a register to be called**; it is always referenced in
    /// place and read *by reference*. This keeps the contract uniform and, crucially, never copies or
    /// moves a non-trivially-copyable closure environment out of its storage. The callee is applied
    /// uniformly: its hidden evidence and (per-call cloned) environment, if any, are prepended ahead
    /// of the visible arguments; a bare function value adds nothing. The same contract governs the
    /// [`drop`](Self::drop) callee.
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

    /// Creates a `project_at` instruction accessing the aggregate place `source` at the **run-time**
    /// field index held in the `index` register (an `int` loaded from a field-index dictionary
    /// parameter). It mirrors `project`, but the index is an operand rather than a static constant:
    /// it lowers a record field access on a generic (row-polymorphic) record (`hir::ProjectAt`),
    /// where the field offset is only known at run time. Like `project`, the result is a place.
    pub fn project_at(span: Location, source: ssa::Value, index: ssa::Value, ty: Type) -> Self {
        Instruction {
            span,
            operands: vec![source, index],
            kind: Box::new(ProjectAt { ty }),
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
    /// Drops the pointee of `target` (a place) by invoking the `Value::drop` implementation named by
    /// `callee`, but **only if** the pointee is currently initialized. An already-uninitialized
    /// (moved-out or never-initialized) pointee is left untouched. This init guard is what makes
    /// the inline drops the emitter places at scope-exit edges run exactly once.
    ///
    /// `callee` follows the same contract as the [`call`](Self::call) callee: it is either a constant
    /// [`ssa::Value::Function`] or the **place** of a function value (e.g. the `Value::drop` method
    /// slot `project`ed out of a dictionary), read by reference and never loaded into a register.
    pub fn drop(span: Location, target: ssa::Value, callee: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![target, callee],
            kind: Box::new(Drop {}),
        }
    }

    /// Creates a `build_closure` instruction, which bundles a function with its captured environment
    /// into a first-class closure value.
    ///
    /// `function` identifies the closure's target (lambda) function; `env_dict` is the `Value`
    /// dictionary witnessing how to clone/drop the captured environment (`None` when there are no
    /// captures). The operands are the capture places, in target-parameter order. The result is a
    /// register holding the closure value (a runtime `FunctionValue`).
    pub fn build_closure(
        span: Location,
        function: FunctionReference,
        env_dict: Option<TraitDictionaryId>,
        ty: Type,
        captures: Vec<ssa::Value>,
    ) -> Self {
        Instruction {
            span,
            operands: captures,
            kind: Box::new(BuildClosure {
                function,
                env_dict,
                ty,
            }),
        }
    }

    /// Creates a `clone_closure_env` instruction, which deep-clones the captured environment of the
    /// closure at the place given by `source`, yielding a fresh closure value of type `ty`.
    pub fn clone_closure_env(span: Location, source: ssa::Value, ty: Type) -> Self {
        Instruction {
            span,
            operands: vec![source],
            kind: Box::new(CloneClosureEnv { ty }),
        }
    }

    /// Creates a `drop_closure_env` instruction, which drops the owned captured environment of the
    /// closure at the place given by `target`.
    pub fn drop_closure_env(span: Location, target: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![target],
            kind: Box::new(DropClosureEnv {}),
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

    /// A function call. Operand `0` is the callee — a constant [`ssa::Value::Function`] or the place
    /// of a function value, read by reference (see [`Instruction::call`] for the full callee
    /// contract). The remaining operands are the arguments, the last of which is the return
    /// out-pointer for a non-`()` result.
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

    /// A projection (of type `ty`) out of the aggregate place at operand `0`, at the run-time field
    /// index held in the `int` register at operand `1`.
    ProjectAt { ty: Type },

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
    /// `Value::drop` callee — a constant function or a function-value place, per the
    /// [`Instruction::call`] callee contract) only if that pointee is currently initialized.
    Drop,

    /// A construction of a closure value bundling the target `function`, the `Value` dictionary
    /// `env_dict` for cloning/dropping the captured environment (if any), and the capture places
    /// (the instruction's operands, in target-parameter order).
    BuildClosure {
        function: &'a FunctionReference,
        env_dict: Option<TraitDictionaryId>,
    },

    /// A deep clone of the captured environment of the closure at the place given by operand `0`,
    /// yielding a fresh closure value.
    CloneClosureEnv,

    /// A drop of the owned captured environment of the closure at the place given by operand `0`.
    DropClosureEnv,
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

/// A dynamic-index project instruction in SSA.
///
/// Like [`Project`], but the field index is a run-time operand (operand `1`, an `int` register)
/// rather than a static constant. It lowers a record field access on a generic (row-polymorphic)
/// record, where the field offset is supplied by a field-index dictionary parameter.
struct ProjectAt {
    /// The type of the projected value.
    ty: Type,
}

impl InstructionKind for ProjectAt {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        // The aggregate operand is a place and the result is a place: a pointer to the projected
        // element. A register value is obtained by `load`ing the result.
        InstructionResult::pointer_to(InstructionResult::Lowered(self.ty))
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::ProjectAt { ty: self.ty }
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(
            f,
            "project at {} from {}",
            whole.operands[1], whole.operands[0]
        )
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

/// A closure construction in SSA.
///
/// Bundles a function reference with its captured environment (the operand places, in
/// target-parameter order) into a runtime `FunctionValue`. `env_dict` is the `Value` dictionary
/// used to clone/drop the captured environment.
struct BuildClosure {
    /// The closure's target (lambda) function.
    function: FunctionReference,

    /// The `Value` dictionary for cloning/dropping the captured environment (`None` when there are
    /// no captures).
    env_dict: Option<TraitDictionaryId>,

    /// The type of the constructed closure value.
    ty: Type,
}

impl InstructionKind for BuildClosure {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        InstructionResult::Lowered(self.ty)
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::BuildClosure {
            function: &self.function,
            env_dict: self.env_dict,
        }
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "build_closure {}(", self.function.name)?;
        for (i, op) in whole.operands.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", op)?;
        }
        write!(f, ")")
    }
}

/// A deep clone of a closure's captured environment in SSA, yielding a fresh closure value.
struct CloneClosureEnv {
    /// The type of the cloned closure value.
    ty: Type,
}

impl InstructionKind for CloneClosureEnv {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        InstructionResult::Lowered(self.ty)
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::CloneClosureEnv
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "clone_closure_env {}", whole.operands[0])
    }
}

/// A drop of a closure's owned captured environment in SSA.
struct DropClosureEnv {}

impl InstructionKind for DropClosureEnv {
    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::DropClosureEnv
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        _env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        write!(f, "drop_closure_env {}", whole.operands[0])
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
