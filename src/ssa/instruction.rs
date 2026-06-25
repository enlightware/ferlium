//! SSA instructions and their contracts.
//!
//! # Operand and result contract
//!
//! Each instruction carries a flat `operands: Vec<ssa::Value>` whose length and per-position meaning
//! are fixed by the instruction kind (documented on each `Instruction::*` constructor below and
//! checked by [`Instruction::verify`]). An operand falls into one of four runtime *roles*; which role
//! a given position expects is part of the contract, but it is **not** recoverable from the
//! `ssa::Value` variant alone (a `Register`/`Parameter` can bind any of them), so the role is
//! enforced where the operand is consumed — by the interpreter's `place_operand` / `value_operand` /
//! `dict_operand` / `stack_marker_operand` resolvers:
//!
//! - **place** — a pointer into storage (the result of an `alloca`/`project`/`dict_entry`, or an
//!   incoming by-pointer parameter). Consumed by `load`, `store`, `project`, `drop`, etc.
//! - **value** — a materialized register or constant (the result of a `load`/`comp_eq`, or a literal
//!   constant). A non-trivially-copyable value has *exactly one* consuming use; reading it again is a
//!   mis-lowering the interpreter catches.
//! - **dictionary** — a symbolic trait dictionary (evidence), consumed by `dict_entry`/`call` and
//!   never materialized as a value.
//! - **stack marker** — a saved stack top produced by `stack_save`, consumed only by `stack_restore`.
//!
//! An instruction either defines a single result register (`InstructionResult` other than `Nothing`)
//! or defines nothing; a result-less instruction's slot must never be read. Three kinds are
//! *terminators* (`ret`, `br`, `condbr`): a terminator appears exactly once, as the last instruction
//! of its block, and every other instruction is a non-terminator. These structural invariants are
//! verified per function by the interpreter (see `Interpreter::verify_function`).

use std::any::Any;
use std::fmt;

use ustr::Ustr;

use crate::{
    Location, cached_primitive_ty,
    format::FormatWith,
    list,
    module::ModuleEnv,
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

    /// Verifies the structural contract of this instruction in isolation: the operand **arity** (and,
    /// for `alloca`/`memcpy`, the optional run-time-layout witness) plus terminator consistency.
    ///
    /// This is the machine-checkable core of the per-instruction contracts documented on each
    /// constructor below. The interpreter runs it over every instruction of a function before
    /// executing it (see `Interpreter::verify_function`), so malformed IR fails fast with a precise
    /// message instead of an out-of-bounds operand index or silently corrupted interpreter state —
    /// the moral equivalent of the undefined behavior such IR would cause in a real backend.
    ///
    /// Operand *role* (place vs value vs dictionary vs marker) is intentionally **not** checked here:
    /// it is not recoverable from the `ssa::Value` variant (a `Register`/`Parameter` binds any role),
    /// so it is enforced at point of use by the interpreter's operand resolvers.
    pub fn verify(&self) {
        let n = self.operands.len();
        use InstructionView as V;
        match self.view() {
            // 1 operand (the layout witness) iff `ty` is not statically sized, else none.
            V::Alloca { witness, .. } => assert_eq!(
                n,
                witness.is_some() as usize,
                "alloca carries the run-time-layout witness iff its type is not statically sized"
            ),
            V::AllocaPlace { .. } => assert_eq!(n, 0, "alloca_place takes no operands"),
            // [callee, args.., ret-out-pointer?]: at least the callee.
            V::Call => assert!(n >= 1, "call needs at least the callee operand"),
            V::CompareEqual => assert_eq!(n, 2, "compare_eq compares exactly two operands"),
            V::ConditionalBranch { .. } => {
                assert_eq!(n, 1, "condbr takes exactly the condition operand")
            }
            V::UnconditionalBranch { .. } => assert_eq!(n, 0, "br takes no operands"),
            V::Load => assert_eq!(n, 1, "load takes exactly the source place"),
            V::Project { .. } => assert_eq!(n, 1, "project takes exactly the aggregate place"),
            V::ProjectAt { .. } => assert_eq!(
                n, 2,
                "project_at takes the aggregate place and the run-time index register"
            ),
            V::DictEntry { .. } => {
                assert_eq!(
                    n, 1,
                    "dict_entry takes exactly the symbolic dictionary operand"
                )
            }
            V::Ret => assert_eq!(
                n, 0,
                "ret takes no operands (the result is written through the return out-pointer)"
            ),
            V::Variant { .. } => {
                assert_eq!(
                    n, 0,
                    "variant builds an uninitialized shell and takes no operands"
                )
            }
            V::ExtractTag => assert_eq!(n, 1, "extract_tag takes exactly the variant place"),
            V::Store => assert_eq!(n, 2, "store takes the value and the destination place"),
            // [source, destination] plus the layout witness iff the pointee is dynamically sized.
            V::Memcpy => assert!(
                n == 2 || n == 3,
                "memcpy takes source and destination places, plus the layout witness iff dynamic"
            ),
            V::StackSave => assert_eq!(n, 0, "stack_save takes no operands"),
            V::StackRestore => assert_eq!(n, 1, "stack_restore takes exactly the saved marker"),
            V::Drop => assert_eq!(
                n, 2,
                "drop takes the target place and the Value::drop callee"
            ),
            // [hidden_dicts.., captures.., env_dict?]: at least the hidden dicts and optional env dict.
            V::BuildClosure {
                num_hidden_dicts,
                has_env_dict,
                ..
            } => assert!(
                n >= num_hidden_dicts + has_env_dict as usize,
                "build_closure needs at least its hidden dictionaries and the optional env dictionary"
            ),
            V::CloneClosureEnv => {
                assert_eq!(n, 1, "clone_closure_env takes exactly the closure place")
            }
            V::DropClosureEnv => {
                assert_eq!(n, 1, "drop_closure_env takes exactly the closure place")
            }
        }
        assert_eq!(
            self.is_terminator(),
            matches!(
                self.view(),
                V::Ret | V::ConditionalBranch { .. } | V::UnconditionalBranch { .. }
            ),
            "is_terminator must agree with the instruction kind (only ret/br/condbr terminate)"
        );
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

    /// Creates an `alloca_place` instruction: stack storage for a *pointer* to an instance of
    /// `pointing_to`. No operands; the result is the place of that pointer slot.
    pub fn alloca_place(span: Location, pointing_to: Type) -> Self {
        Instruction {
            span,
            operands: vec![],
            kind: Box::new(AllocaPlace { pointing_to }),
        }
    }

    /// Creates a `br` (unconditional branch) instruction transferring control to `target`.
    ///
    /// A terminator; takes no operands. `target` must be an existing block of the same function.
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

    /// Creates a `compare_eq` instruction comparing operands `0` (`v1`) and `1` (`v2`) for structural
    /// equality, yielding a `bool` register.
    ///
    /// Both operands are read **non-consumingly** as literal snapshots (a place is borrowed, never
    /// moved), so this is the comparison of a lowered `match`: the scrutinee stays live for the
    /// remaining alternatives and the arm body. Each operand must have a literal form (a scalar
    /// constant, or a place/register whose pointee is a scalar or composite literal).
    pub fn compare_eq(span: Location, v1: ssa::Value, v2: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![v1, v2],
            kind: Box::new(CompareEqual {}),
        }
    }

    /// Creates a `condbr` (conditional branch) instruction: branches to `on_success` if operand `0`
    /// (`condition`) is `true`, otherwise to `on_failure`.
    ///
    /// A terminator. The single operand is a **value** that must resolve to a `bool`; both targets
    /// must be existing blocks of the same function.
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

    /// Creates a `load` instruction reading the value at the place `source` (operand `0`) into a
    /// register.
    ///
    /// `source` must be a **place** whose pointee is currently initialized. A trivially-copyable
    /// pointee (scalar/function) is copied, leaving the place intact; any other pointee is *moved*
    /// out, leaving the place uninitialized — so a non-trivial place has exactly one consuming load.
    /// HIR wraps non-trivial reads that must not move in `Value::clone`, so a bare `load` is always a
    /// move-or-copy, never an aliasing read.
    pub fn load(span: Location, source: ssa::Value) -> Self {
        Instruction {
            span,
            operands: vec![source],
            kind: Box::new(Load {}),
        }
    }

    /// Creates a `project` instruction yielding the **place** of field `i` (of type `ty`) of the
    /// aggregate place `source` (operand `0`).
    ///
    /// `source` must be a place whose pointee is an aggregate with more than `i` fields (or generic
    /// storage that grows to that shape on the first field store); the result is a place, computed
    /// without reading or moving the aggregate. `i` is a compile-time-constant field index — see
    /// [`project_at`](Self::project_at) for the run-time-index form.
    pub fn project(span: Location, source: ssa::Value, i: usize, ty: Type) -> Self {
        Instruction {
            span,
            operands: vec![source],
            kind: Box::new(Project { index: i, ty }),
        }
    }

    /// Creates a `dict_entry` instruction: the symbolic analog of `project` for a trait dictionary.
    ///
    /// `dict` is a symbolic dictionary operand (a constant [`ssa::Value::Dictionary`] or a forwarded
    /// dictionary `Parameter`). The instruction yields the **place** of entry `entry_index` of that
    /// dictionary — a method function value, or an associated const — of type `ty`. `call`, `drop`,
    /// and `memcpy` consume that place exactly as they consume a `project` result, so a later
    /// tuple-lowering pass rewrites `dict_entry N from <symbolic dict>` to
    /// `project N from <materialized witness-table tuple>` one-for-one.
    pub fn dict_entry(span: Location, dict: ssa::Value, entry_index: usize, ty: Type) -> Self {
        Instruction {
            span,
            operands: vec![dict],
            kind: Box::new(DictEntry { entry_index, ty }),
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

    /// Creates a `store` instruction writing the **value** operand `0` (`value`) into the **place**
    /// operand `1` (`destination`), discarding (dropping the storage of) any prior contents.
    ///
    /// Yields no register. `value` is consumed (moved, for a non-trivial value); `destination` must
    /// be a place — generic storage materializes its enclosing aggregate skeleton on demand so a
    /// field store is addressable.
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

    /// Creates a `memcpy` instruction for a value whose size is known only at run time: a move of a
    /// generic (bare-type-variable-typed) pointee. `witness` is the place of the `Value` dictionary
    /// witnessing the run-time layout of the moved value (its `SIZE`/`ALIGN`), exactly as for
    /// [`alloca_dynamic`](Self::alloca_dynamic). The SSA interpreter moves the value shape-agnostically
    /// (the witness is metadata it ignores); a real backend uses the witness to size the copy.
    pub fn memcpy_dynamic(
        span: Location,
        source: ssa::Value,
        destination: ssa::Value,
        witness: ssa::Value,
    ) -> Self {
        Instruction {
            span,
            operands: vec![source, destination, witness],
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
    /// `function` identifies the closure's target (lambda) function. `hidden_dicts` are the symbolic
    /// dictionary operands for the lambda body's hidden `@extra` parameters (the dictionary captures,
    /// in target-parameter order); each is a constant [`ssa::Value::Dictionary`] or a forwarded
    /// dictionary `Parameter`. `env_dict` is the symbolic `Value` dictionary used to clone/drop the
    /// captured value environment (`None` iff there are no value captures). `captures` are the
    /// value-capture places, in target-parameter order.
    ///
    /// Operand layout is `[hidden_dicts…, captures…, env_dict?]`. The result is a register holding
    /// the closure value (a runtime `FunctionValue`).
    pub fn build_closure(
        span: Location,
        function: FunctionReference,
        hidden_dicts: Vec<ssa::Value>,
        env_dict: Option<ssa::Value>,
        ty: Type,
        captures: Vec<ssa::Value>,
    ) -> Self {
        let num_hidden_dicts = hidden_dicts.len();
        let has_env_dict = env_dict.is_some();
        let mut operands = hidden_dicts;
        operands.extend(captures);
        operands.extend(env_dict);
        Instruction {
            span,
            operands,
            kind: Box::new(BuildClosure {
                function,
                num_hidden_dicts,
                has_env_dict,
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

    /// The place of entry `entry_index` (of type `ty`) of the symbolic dictionary at operand `0`.
    /// The symbolic analog of `Project`: a method function value or an associated const, kept
    /// dictionary-symbolic until a later tuple-lowering pass rewrites it to `Project`.
    DictEntry { entry_index: usize, ty: Type },

    /// A return. The result, if any, has already been written through the return out-pointer.
    Ret,

    /// A construction of a tagged variant *shell* (`tag` with an uninitialized payload), yielded as a
    /// register. Takes **no operands**: the payload is filled in place through a projection of the
    /// shell's destination, so a generic payload is never materialized in a temporary (see
    /// [`Instruction::variant`]).
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

    /// A construction of a closure value bundling the target `function` with its captured
    /// environment. Operand layout is `[hidden_dicts…, captures…, env_dict?]`: `num_hidden_dicts`
    /// leading symbolic dictionary operands feed the lambda body's hidden `@extra` parameters, the
    /// value-capture places follow, and a trailing symbolic `Value`-dictionary operand (present iff
    /// `has_env_dict`) clones/drops the captured value environment.
    BuildClosure {
        function: &'a FunctionReference,
        num_hidden_dicts: usize,
        has_env_dict: bool,
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

/// A dictionary-entry instruction in SSA: the symbolic analog of [`Project`] for a trait
/// dictionary (see [`Instruction::dict_entry`]).
struct DictEntry {
    /// The index of the entry within the dictionary (methods first, then associated consts).
    entry_index: usize,

    /// The type of the entry (a method's function type, or an associated const's type).
    ty: Type,
}

impl InstructionKind for DictEntry {
    fn result(&self, _whole: &Instruction) -> InstructionResult {
        // Like `Project`: the result is the place of the entry; a register value is obtained by
        // `load`ing it, and a method callee is read by reference at the `call`/`drop`.
        InstructionResult::pointer_to(InstructionResult::Lowered(self.ty))
    }

    fn view<'a>(&'a self, _whole: &'a Instruction) -> InstructionView<'a> {
        InstructionView::DictEntry {
            entry_index: self.entry_index,
            ty: self.ty,
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
            "dict_entry {} from {}",
            self.entry_index, whole.operands[0]
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
        write!(f, "memcpy {} to {}", whole.operands[0], whole.operands[1])?;
        if let Some(witness) = whole.operands.get(2) {
            write!(f, " using {}", witness)?;
        }
        Ok(())
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
/// Bundles a function reference with its captured environment into a runtime `FunctionValue`.
/// Operand layout is `[hidden_dicts…, captures…, env_dict?]`: `num_hidden_dicts` leading symbolic
/// dictionary operands feed the lambda body's hidden `@extra` parameters, the value-capture places
/// follow, and a trailing symbolic `Value`-dictionary operand (present iff `has_env_dict`) clones/
/// drops the captured value environment.
struct BuildClosure {
    /// The closure's target (lambda) function.
    function: FunctionReference,

    /// Number of leading symbolic dictionary operands feeding the lambda body's `@extra` params.
    num_hidden_dicts: usize,

    /// Whether the final operand is the symbolic `Value` dictionary for the captured environment
    /// (`true` iff there are value captures).
    has_env_dict: bool,

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
            num_hidden_dicts: self.num_hidden_dicts,
            has_env_dict: self.has_env_dict,
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
