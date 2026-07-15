//! SSA instructions and their contracts.
//!
//! # Operand and result contract
//!
//! Each instruction carries a flat `operands: Box<[ssa::Value]>` whose length and per-position meaning
//! are fixed by the instruction kind (documented on each `Instruction::*` constructor below and
//! checked by [`Instruction::verify`]). An operand falls into one of four runtime *roles*; which role
//! a given position expects is part of the contract, but it is **not** recoverable from the
//! `ssa::Value` variant alone (a `Register`/`Parameter` can bind any of them), so the role is
//! enforced where the operand is consumed — by the interpreter's `place_operand` / `value_operand` /
//! `dict_operand` / `stack_marker_operand` resolvers:
//!
//! - **place** — a pointer into storage (the result of an `alloca`/`subfield`/`dict_entry`, or an
//!   incoming by-pointer parameter). Consumed by `load`, `store`, `subfield`, `drop`, etc.
//! - **value** — a materialized register or constant (the result of a `load`/`comp_eq`, or a literal
//!   constant). A non-trivially-copyable value has *exactly one* consuming use; reading it again is a
//!   mis-lowering the interpreter catches.
//! - **dictionary** — a symbolic trait dictionary (evidence), consumed by `dict_entry`/`call` and
//!   never materialized as a value.
//! - **stack marker** — a saved stack top produced by `stack_save`, consumed only by `stack_restore`.
//!
//! An instruction either defines a single result register (`InstructionResult` other than `Nothing`)
//! or defines nothing; a result-less instruction's slot must never be read. Some kinds are
//! *terminators* (`ret`, `br`, `condbr`, `invoke`, `resume`, and fallible runtime checks, as
//! classified by [`InstructionKind::is_terminator`]): a terminator appears exactly once, as the
//! last instruction of its block, and
//! every other instruction is a non-terminator. These structural invariants are verified per function
//! by the interpreter (see `Interpreter::verify_function`).

use std::fmt;

use ustr::Ustr;

use crate::{
    Location, cached_primitive_ty,
    format::FormatWith,
    list,
    module::{FunctionId, ModuleEnv},
    ssa,
    types::r#type::Type,
};

/// The identity of an instruction in the context of its containing funtion.
pub type InstructionIdentity = list::Address;

/// An instruction in the SSA form of Ferlium.
pub struct Instruction {
    /// The region of the code corresponding to this instruction.
    pub span: Location,

    /// The operands of the instruction.
    pub operands: Box<[ssa::Value]>,

    /// The kind-specific part of `self`.
    pub kind: InstructionKind,
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

    /// Verifies the structural contract of this instruction in isolation (the operand **arity**, and
    /// the data-dependent operand count for `alloca`/`move`/`build_closure`).
    pub fn verify(&self) {
        self.kind.verify(self);
    }

    /// Creates an `alloca` instruction for storage whose size is known at compile time.
    pub fn alloca(span: Location, ty: Type) -> Self {
        Instruction {
            span,
            operands: Box::new([]),
            kind: InstructionKind::Alloca { ty },
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
            operands: Box::new([witness]),
            kind: InstructionKind::Alloca { ty },
        }
    }

    /// Creates an `alloca_place` instruction: stack storage for a *pointer* to an instance of
    /// `pointing_to`. No operands; the result is the place of that pointer slot.
    pub fn alloca_place(span: Location, pointing_to: Type) -> Self {
        Instruction {
            span,
            operands: Box::new([]),
            kind: InstructionKind::AllocaPlace { pointing_to },
        }
    }

    /// Creates a `br` (unconditional branch) instruction transferring control to `target`.
    ///
    /// A terminator; takes no operands. `target` must be an existing block of the same function.
    pub fn br(span: Location, target: ssa::BlockIdentity) -> Self {
        Instruction {
            span,
            operands: Box::new([]),
            kind: InstructionKind::UnconditionalBranch { target },
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
            operands: operands.into_boxed_slice(),
            kind: InstructionKind::Call,
        }
    }

    /// Creates an `invoke` instruction: a *fallible* call that, on a raised [`RuntimeError`], diverts
    /// control to the `unwind` cleanup landing pad instead of propagating straight out of the frame.
    ///
    /// A terminator with two successors (the SSA analog of LLVM `invoke`): on normal completion
    /// control transfers to `normal` (the continuation block holding the instructions that follow the
    /// call); on a raised error it transfers to `unwind` (a pad block that drops the frame's still-live
    /// locals and then `br`s to an enclosing pad or `resume`s). The operand layout is identical to
    /// [`call`](Self::call) (`[callee, args.., ret-out]`) and the callee contract is the same; only
    /// *fallible* calls that have cleanup to run on the error path are lowered as `invoke` — an
    /// infallible call, or one with nothing to clean up in its frame, stays a plain [`call`](Self::call).
    ///
    /// [`RuntimeError`]: crate::eval::RuntimeError
    pub fn invoke<T: IntoIterator<Item = ssa::Value>>(
        span: Location,
        callee: ssa::Value,
        arguments: T,
        normal: ssa::BlockIdentity,
        unwind: ssa::BlockIdentity,
    ) -> Self {
        let mut operands = vec![callee];
        operands.extend(arguments);
        Instruction {
            span,
            operands: operands.into_boxed_slice(),
            kind: InstructionKind::Invoke { normal, unwind },
        }
    }

    /// Creates a `resume` instruction, which *continues* the unwind a cleanup pad interrupted: it
    /// hands the in-flight [`RuntimeError`] back to this function's caller so propagation carries on
    /// up the stack.
    ///
    /// Named after LLVM's `resume` (the third of `invoke`/`landingpad`/`resume`). It is not a *throw*:
    /// the error was already raised — by the original fallible call — and is merely *paused* while the
    /// pad runs the frame's drops. `resume` lifts that pause. A terminator with no successors (like
    /// [`ret`](Self::ret)): it is the last instruction of an outermost cleanup pad, reached after that
    /// pad and the pads it chains from have dropped the frame's live locals. The caller's
    /// [`invoke`](Self::invoke) at the originating call site catches the resumed error and routes it
    /// into the caller's own pad — giving the cross-frame unwind.
    ///
    /// [`RuntimeError`]: crate::eval::RuntimeError
    pub fn resume(span: Location) -> Self {
        Instruction {
            span,
            operands: Box::new([]),
            kind: InstructionKind::Resume,
        }
    }

    /// Creates a `project` instruction: the *enter* half of a scoped (`YieldedOnce`) subscript
    /// access. It runs the subscript accessor `callee` (a `YieldedOnce` member) to its single
    /// `yield`, suspending the accessor frame, and **exposes the yielded place as this instruction's
    /// result register** (a place of pointee type `ty`). The body that uses the place runs next; the
    /// matching [`end_project`](Self::end_project), keyed by this result register, resumes the
    /// accessor's slide (epilogue).
    ///
    /// Operands are `[callee, args..]` with the same callee contract as [`call`](Self::call), where
    /// `args` are the accessor's extra (dictionary) and visible arguments. Unlike `call` there is no
    /// trailing return out-pointer: the accessor's nominal return is unused on the yielded path (the
    /// place flows out as this instruction's result register). Mirrors the HIR interpreter's
    /// `call_accessor_until_yield`.
    pub fn project<T: IntoIterator<Item = ssa::Value>>(
        span: Location,
        callee: ssa::Value,
        arguments: T,
        ty: Type,
    ) -> Self {
        let mut operands = vec![callee];
        operands.extend(arguments);
        Instruction {
            span,
            operands: operands.into_boxed_slice(),
            kind: InstructionKind::Project { ty },
        }
    }

    /// Creates a `yield` instruction: inside a `YieldedOnce` accessor body, it exposes the **place**
    /// at operand `0` to the driving [`project`](Self::project) site and suspends the accessor frame.
    /// The instructions after it form the accessor's slide (epilogue), reached only when the matching
    /// [`end_project`](Self::end_project) resumes the frame. Mirrors the HIR `Yield`.
    pub fn r#yield(span: Location, place: ssa::Value) -> Self {
        Instruction {
            span,
            operands: Box::new([place]),
            kind: InstructionKind::Yield,
        }
    }

    /// Creates an `end_project` instruction: the *leave* half of a scoped subscript access. Operand
    /// `0` is the place a [`project`](Self::project) exposed; this resumes that suspended accessor
    /// from after its `yield`, runs its slide to completion, and reclaims the accessor frame. Mirrors
    /// the HIR interpreter's `resume_suspended_accessor_epilogue`. Distinct from the unwind
    /// [`resume`](Self::resume).
    pub fn end_project(span: Location, place: ssa::Value) -> Self {
        Instruction {
            span,
            operands: Box::new([place]),
            kind: InstructionKind::EndProject,
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
            operands: Box::new([v1, v2]),
            kind: InstructionKind::CompareEqual,
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
            operands: Box::new([condition]),
            kind: InstructionKind::ConditionalBranch {
                on_success,
                on_failure,
            },
        }
    }

    /// Creates a `load` instruction reading the value at the place `source` (operand `0`) into a
    /// register.
    ///
    /// `source` must be a **place** whose pointee has a representation-copyable value (currently an
    /// internal place pointer). The source stays initialized. Ownership transfers are explicit
    /// [`move_value`](Self::move_value) instructions rather than a run-time choice made by `load`.
    pub fn load(span: Location, source: ssa::Value) -> Self {
        Instruction {
            span,
            operands: Box::new([source]),
            kind: InstructionKind::Load,
        }
    }

    /// Creates a `subfield` instruction yielding the **place** of the field (of type `ty`) of the
    /// aggregate place `source` (operand `0`) at the field index given by the `int` value `index`
    /// (operand `1`).
    ///
    /// `source` must be a place whose pointee is an aggregate with more than `index` fields (or
    /// generic storage that grows to that shape on the first field store); the result is a place,
    /// computed without reading or moving the aggregate. `index` is an ordinary `int` value operand —
    /// usually a typed [`ssa::Value::Constant`] from the containing function's pool (a tuple/record
    /// field at a known position), but a register when the offset is only known at run time.
    /// Keeping the index a value operand — rather than splitting static and dynamic forms — matches
    /// how a backend (LLVM `getelementptr`) takes the index as an IR value regardless.
    pub fn subfield(span: Location, source: ssa::Value, index: ssa::Value, ty: Type) -> Self {
        Instruction {
            span,
            operands: Box::new([source, index]),
            kind: InstructionKind::Subfield { ty },
        }
    }

    /// Creates a `dict_entry` instruction: the symbolic analog of `subfield` for a trait dictionary.
    ///
    /// `dict` is a symbolic dictionary operand (a constant [`ssa::Value::Dictionary`] or a forwarded
    /// dictionary `Parameter`). The instruction yields the **place** of entry `entry_index` of that
    /// dictionary — a method function value, or an associated const — of type `ty`. `call`, `drop`,
    /// and `memcpy` consume that place exactly as they consume a `subfield` result, so a later
    /// tuple-lowering pass rewrites `dict_entry N from <symbolic dict>` to
    /// `subfield N from <materialized witness-table tuple>` one-for-one.
    pub fn dict_entry(span: Location, dict: ssa::Value, entry_index: usize, ty: Type) -> Self {
        Instruction {
            span,
            operands: Box::new([dict]),
            kind: InstructionKind::DictEntry { entry_index, ty },
        }
    }

    /// Creates a `subscript_member` instruction: the member-resolving analog of [`dict_entry`]
    /// (Instruction::dict_entry) for a first-class subscript.
    ///
    /// `subscript` is a symbolic subscript operand (a constant [`ssa::Value::Subscript`] or a
    /// forwarded evidence `Parameter`). The instruction yields the **place** of the subscript's
    /// `ref`/`mut` member — a function value of type `ty` bundling the subscript's captured hidden
    /// evidence — which a `call`/`project` consumes by reference exactly like a closure callee.
    pub fn subscript_member(
        span: Location,
        subscript: ssa::Value,
        mut_member: bool,
        ty: Type,
    ) -> Self {
        Instruction {
            span,
            operands: Box::new([subscript]),
            kind: InstructionKind::SubscriptMember { mut_member, ty },
        }
    }

    /// Creates a `build_subscript` instruction, which bundles the symbolic subscript at operand `0`
    /// with captured hidden evidence — the remaining operands, each a symbolic dictionary or
    /// subscript operand — yielding a first-class subscript value of type `ty`. With no captures it
    /// reads the subscript operand into a fresh first-class value (the lowering of a subscript
    /// clone).
    pub fn build_subscript(
        span: Location,
        subscript: ssa::Value,
        evidence: Vec<ssa::Value>,
        ty: Type,
    ) -> Self {
        let mut operands = vec![subscript];
        operands.extend(evidence);
        Instruction {
            span,
            operands: operands.into_boxed_slice(),
            kind: InstructionKind::BuildSubscript { ty },
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
            operands: Box::new([]),
            kind: InstructionKind::Variant { tag, ty: t },
        }
    }

    /// Creates an `extract_tag` instruction, which reads the tag of the variant at the `variant`
    /// place and yields it as an `int` register (matching the HIR interpreter's tag encoding).
    pub fn extract_tag(span: Location, variant: ssa::Value) -> Self {
        Instruction {
            span,
            operands: Box::new([variant]),
            kind: InstructionKind::ExtractTag,
        }
    }

    /// Creates a 'ret' instruction.
    ///
    /// The return value is not an operand: the function writes its result into the return
    /// out-pointer (the last parameter) before returning.
    pub fn ret(span: Location) -> Self {
        Instruction {
            span,
            operands: Box::new([]),
            kind: InstructionKind::Ret,
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
            operands: Box::new([]),
            kind: InstructionKind::StackSave,
        }
    }

    /// Creates a `stack_restore` instruction, which resets the top of the stack to `marker` (the
    /// result of an earlier `stack_save`), reclaiming everything allocated since.
    pub fn stack_restore(span: Location, marker: ssa::Value) -> Self {
        Instruction {
            span,
            operands: Box::new([marker]),
            kind: InstructionKind::StackRestore,
        }
    }

    /// Creates a runtime call-depth guard corresponding to HIR `CheckCallDepth`.
    pub fn check_call_depth(span: Location) -> Self {
        Instruction {
            span,
            operands: Box::new([]),
            kind: InstructionKind::CheckCallDepth { successors: None },
        }
    }

    /// Creates a runtime fuel guard corresponding to HIR `CheckFuel`.
    pub fn check_fuel(span: Location) -> Self {
        Instruction {
            span,
            operands: Box::new([]),
            kind: InstructionKind::CheckFuel { successors: None },
        }
    }

    /// Creates a call-depth guard with explicit normal and unwind successors.
    pub fn invoke_check_call_depth(
        span: Location,
        normal: ssa::BlockIdentity,
        unwind: ssa::BlockIdentity,
    ) -> Self {
        Instruction {
            span,
            operands: Box::new([]),
            kind: InstructionKind::CheckCallDepth {
                successors: Some((normal, unwind)),
            },
        }
    }

    /// Creates a fuel guard with explicit normal and unwind successors.
    pub fn invoke_check_fuel(
        span: Location,
        normal: ssa::BlockIdentity,
        unwind: ssa::BlockIdentity,
    ) -> Self {
        Instruction {
            span,
            operands: Box::new([]),
            kind: InstructionKind::CheckFuel {
                successors: Some((normal, unwind)),
            },
        }
    }

    /// Creates a `store` instruction writing the **value** operand `0` (`value`) into the **place**
    /// operand `1` (`destination`).
    ///
    /// A `store` **drops nothing**: `destination` must hold no live resource — a husk, or a
    /// resource-free value overwritten in place — so the emitter owes an explicit `drop` before
    /// overwriting a resource-owning pointee. Yields no register; `value` is consumed (moved, for a
    /// non-trivial value).
    pub fn store(span: Location, value: ssa::Value, destination: ssa::Value) -> Self {
        Instruction {
            span,
            operands: Box::new([value, destination]),
            kind: InstructionKind::Store,
        }
    }

    /// Creates a `clear` instruction that marks the storage at `destination` absent. The previous
    /// state must already own no resource; clearing is initialization bookkeeping, not a semantic
    /// drop.
    pub fn clear(span: Location, destination: ssa::Value) -> Self {
        Instruction {
            span,
            operands: Box::new([destination]),
            kind: InstructionKind::Clear,
        }
    }

    /// Creates a `memcpy` instruction: a pure, **source-preserving** copy of the pointee of `source`
    /// (a place) into `destination` (a place), without first materializing it in a register.
    ///
    /// The pointee must **own no resource** — a scalar, a bare function, or an aggregate built only
    /// from such. Any resource-owning copy is lowered through `Value::clone` (a `call`) by HIR before
    /// reaching the emitter, and an ownership transfer uses [`move_value`](Self::move_value); a bare
    /// `memcpy` never moves its source out.
    ///
    /// **Requirement:** the pointee must have a **statically known layout** — a real backend sizes the
    /// copy from the type alone. Copies are always statically sized; a generic transfer is a
    /// [`move_dynamic`](Self::move_dynamic), never a `memcpy`.
    pub fn memcpy(span: Location, source: ssa::Value, destination: ssa::Value) -> Self {
        Instruction {
            span,
            operands: Box::new([source, destination]),
            kind: InstructionKind::Memcpy,
        }
    }

    /// Creates a `move` instruction: a **source-consuming** ownership transfer of the whole pointee of
    /// `source` (a place) into `destination` (a place). The source is left moved-out. For a
    /// statically-sized pointee; a generic (run-time-layout) transfer uses
    /// [`move_dynamic`](Self::move_dynamic). Unlike a copy, a move needs no `Value::clone`; unlike
    /// `memcpy`, it consumes the source.
    pub fn move_value(span: Location, source: ssa::Value, destination: ssa::Value) -> Self {
        Instruction {
            span,
            operands: Box::new([source, destination]),
            kind: InstructionKind::Move,
        }
    }

    /// Creates a `move` instruction for a value whose size is known only at run time: a move of a
    /// generic (bare-type-variable-typed) pointee. `witness` is the place of the `Value` dictionary
    /// witnessing the run-time layout of the moved value (its `SIZE`/`ALIGN`), exactly as for
    /// [`alloca_dynamic`](Self::alloca_dynamic). The SSA interpreter moves the value shape-agnostically
    /// (the witness is metadata it ignores); a real backend uses the witness to size the copy.
    pub fn move_dynamic(
        span: Location,
        source: ssa::Value,
        destination: ssa::Value,
        witness: ssa::Value,
    ) -> Self {
        Instruction {
            span,
            operands: Box::new([source, destination, witness]),
            kind: InstructionKind::Move,
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
            operands: Box::new([target, callee]),
            kind: InstructionKind::Drop,
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
    /// value-capture places, in target-parameter order; construction consumes their values into the
    /// closure's owned environment.
    ///
    /// Operand layout is `[hidden_dicts…, captures…, env_dict?]`. The result is a register holding
    /// the closure value (a runtime `FunctionValue`).
    pub fn build_closure(
        span: Location,
        function: FunctionId,
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
            operands: operands.into_boxed_slice(),
            kind: InstructionKind::BuildClosure {
                function,
                num_hidden_dicts,
                has_env_dict,
                ty,
            },
        }
    }

    /// Creates a `clone_closure_env` instruction, which deep-clones the captured environment of the
    /// closure at the place given by `source`, yielding a fresh closure value of type `ty`.
    pub fn clone_closure_env(span: Location, source: ssa::Value, ty: Type) -> Self {
        Instruction {
            span,
            operands: Box::new([source]),
            kind: InstructionKind::CloneClosureEnv { ty },
        }
    }

    /// Creates a `drop_closure_env` instruction, which drops the owned captured environment of the
    /// closure at the place given by `target`.
    pub fn drop_closure_env(span: Location, target: ssa::Value) -> Self {
        Instruction {
            span,
            operands: Box::new([target]),
            kind: InstructionKind::DropClosureEnv,
        }
    }
}

/// The kind-specific metadata of an SSA instruction.
///
/// Operands stay in [`Instruction::operands`] so generic SSA traversals can inspect and rewrite
/// them uniformly. This enum contains only metadata whose shape is specific to an instruction.
pub enum InstructionKind {
    /// Stack storage for a value of `ty`, optionally using a run-time layout witness.
    Alloca { ty: Type },
    /// Stack storage for a pointer to a value of `pointing_to`.
    AllocaPlace { pointing_to: Type },
    /// A statically or dynamically resolved function call.
    Call,
    /// A fallible call with normal and unwind successors.
    Invoke {
        normal: ssa::BlockIdentity,
        unwind: ssa::BlockIdentity,
    },
    /// Continue propagating an error after running a cleanup pad.
    Resume,
    /// Enter a scoped subscript accessor and expose its yielded place.
    Project { ty: Type },
    /// Yield a place from a scoped subscript accessor.
    Yield,
    /// Resume and finish a scoped subscript accessor.
    EndProject,
    /// Compare a runtime value with compile-time literal-pattern metadata.
    CompareEqual,
    /// Branch according to a boolean operand.
    ConditionalBranch {
        on_success: ssa::BlockIdentity,
        on_failure: ssa::BlockIdentity,
    },
    /// Unconditionally branch to `target`.
    UnconditionalBranch { target: ssa::BlockIdentity },
    /// Read a representation-copyable value from a place without consuming it.
    Load,
    /// Project a field place from an aggregate place.
    Subfield { ty: Type },
    /// Project a function entry place from a symbolic dictionary.
    DictEntry { entry_index: usize, ty: Type },
    /// Resolve a member function place from a symbolic subscript.
    SubscriptMember { mut_member: bool, ty: Type },
    /// Bundle a symbolic subscript with its captured evidence.
    BuildSubscript { ty: Type },
    /// Return after the result has been written through the return place.
    Ret,
    /// Construct a tagged variant shell whose payload is initialized separately.
    Variant { tag: Ustr, ty: Type },
    /// Read a variant tag as an integer.
    ExtractTag,
    /// Store a value into unoccupied place storage.
    Store,
    /// Mark place storage absent without semantic drop.
    Clear,
    /// Copy a statically sized, resource-free representation between places.
    Memcpy,
    /// Transfer ownership between places, optionally using a run-time layout witness.
    Move,
    /// Save the current stack top.
    StackSave,
    /// Restore a previously saved stack top.
    StackRestore,
    /// Enforce the configured script call-depth limit.
    CheckCallDepth {
        successors: Option<(ssa::BlockIdentity, ssa::BlockIdentity)>,
    },
    /// Consume one unit of optional execution fuel.
    CheckFuel {
        successors: Option<(ssa::BlockIdentity, ssa::BlockIdentity)>,
    },
    /// Semantically drop an initialized value through its `Value::drop` function.
    Drop,
    /// Construct a closure from a function and its captured environment.
    BuildClosure {
        function: FunctionId,
        num_hidden_dicts: usize,
        has_env_dict: bool,
        ty: Type,
    },
    /// Deep-clone a closure's captured environment.
    CloneClosureEnv { ty: Type },
    /// Drop a closure's captured environment.
    DropClosureEnv,
}

impl FormatWith<ModuleEnv<'_>> for Instruction {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        self.kind.fmt_within(f, self, env)
    }
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

impl InstructionKind {
    fn result(&self, whole: &Instruction) -> InstructionResult {
        use InstructionKind::*;

        match self {
            Alloca { ty } => InstructionResult::pointer_to(InstructionResult::Lowered(*ty)),
            AllocaPlace { pointing_to } => InstructionResult::pointer_to(
                InstructionResult::pointer_to(InstructionResult::Lowered(*pointing_to)),
            ),
            Project { ty }
            | Subfield { ty }
            | DictEntry { ty, .. }
            | SubscriptMember { ty, .. } => {
                InstructionResult::pointer_to(InstructionResult::Lowered(*ty))
            }
            CompareEqual => InstructionResult::Lowered(cached_primitive_ty!(bool)),
            Load => {
                InstructionResult::pointee_of(InstructionResult::Same(whole.operands[0].clone()))
            }
            BuildSubscript { ty }
            | Variant { ty, .. }
            | BuildClosure { ty, .. }
            | CloneClosureEnv { ty } => InstructionResult::Lowered(*ty),
            ExtractTag => InstructionResult::Lowered(cached_primitive_ty!(isize)),
            StackSave => InstructionResult::StackMarker,
            Call
            | Invoke { .. }
            | Resume
            | Yield
            | EndProject
            | ConditionalBranch { .. }
            | UnconditionalBranch { .. }
            | Ret
            | Store
            | Clear
            | Memcpy
            | Move
            | StackRestore
            | CheckCallDepth { .. }
            | CheckFuel { .. }
            | Drop
            | DropClosureEnv => InstructionResult::Nothing,
        }
    }

    fn is_terminator(&self) -> bool {
        matches!(
            self,
            Self::Invoke { .. }
                | Self::Resume
                | Self::ConditionalBranch { .. }
                | Self::UnconditionalBranch { .. }
                | Self::Ret
                | Self::CheckCallDepth {
                    successors: Some(_)
                }
                | Self::CheckFuel {
                    successors: Some(_)
                }
        )
    }

    fn verify(&self, whole: &Instruction) {
        use InstructionKind::*;

        match self {
            Alloca { .. } => assert!(
                whole.operands.len() <= 1,
                "alloca takes the run-time-layout witness iff its type is not statically sized (0 or 1 operand)"
            ),
            AllocaPlace { .. } => {
                assert!(whole.operands.is_empty(), "alloca_place takes no operands")
            }
            Call => assert!(
                !whole.operands.is_empty(),
                "call needs at least the callee operand"
            ),
            Invoke { .. } => assert!(
                !whole.operands.is_empty(),
                "invoke needs at least the callee operand"
            ),
            Resume => assert!(whole.operands.is_empty(), "resume takes no operands"),
            Project { .. } => assert!(
                !whole.operands.is_empty(),
                "project needs at least the callee operand"
            ),
            Yield => assert_eq!(
                whole.operands.len(),
                1,
                "yield takes exactly the place to expose"
            ),
            EndProject => assert_eq!(
                whole.operands.len(),
                1,
                "end_project takes exactly the projected place"
            ),
            CompareEqual => assert_eq!(
                whole.operands.len(),
                2,
                "compare_eq compares exactly two operands"
            ),
            ConditionalBranch { .. } => assert_eq!(
                whole.operands.len(),
                1,
                "condbr takes exactly the condition operand"
            ),
            UnconditionalBranch { .. } => {
                assert!(whole.operands.is_empty(), "br takes no operands")
            }
            Load => assert_eq!(
                whole.operands.len(),
                1,
                "load takes exactly the source place"
            ),
            Subfield { .. } => assert_eq!(
                whole.operands.len(),
                2,
                "subfield takes the aggregate place and the int field-index value"
            ),
            DictEntry { .. } => assert_eq!(
                whole.operands.len(),
                1,
                "dict_entry takes exactly the symbolic dictionary operand"
            ),
            SubscriptMember { .. } => assert_eq!(
                whole.operands.len(),
                1,
                "subscript_member takes exactly the symbolic subscript operand"
            ),
            BuildSubscript { .. } => assert!(
                !whole.operands.is_empty(),
                "build_subscript takes the symbolic subscript operand plus its evidence captures"
            ),
            Ret => assert!(
                whole.operands.is_empty(),
                "ret takes no operands (the result is written through the return out-pointer)"
            ),
            Variant { .. } => assert!(
                whole.operands.is_empty(),
                "variant builds an uninitialized shell and takes no operands"
            ),
            ExtractTag => assert_eq!(
                whole.operands.len(),
                1,
                "extract_tag takes exactly the variant place"
            ),
            Store => assert_eq!(
                whole.operands.len(),
                2,
                "store takes the value and the destination place"
            ),
            Clear => assert_eq!(
                whole.operands.len(),
                1,
                "clear takes exactly the destination place"
            ),
            Memcpy => assert_eq!(
                whole.operands.len(),
                2,
                "memcpy is a pure copy of a statically-sized, owns-nothing pointee: source and destination only"
            ),
            Move => assert!(
                matches!(whole.operands.len(), 2 | 3),
                "move takes source and destination places, plus the layout witness iff dynamic"
            ),
            StackSave => {
                assert!(whole.operands.is_empty(), "stack_save takes no operands")
            }
            StackRestore => assert_eq!(
                whole.operands.len(),
                1,
                "stack_restore takes exactly the saved marker"
            ),
            CheckCallDepth { .. } | CheckFuel { .. } => {
                assert!(whole.operands.is_empty(), "runtime checks take no operands")
            }
            Drop => assert_eq!(
                whole.operands.len(),
                2,
                "drop takes the target place and the Value::drop callee"
            ),
            BuildClosure {
                num_hidden_dicts,
                has_env_dict,
                ..
            } => assert!(
                whole.operands.len() >= *num_hidden_dicts + *has_env_dict as usize,
                "build_closure needs at least its hidden dictionaries and the optional env dictionary"
            ),
            CloneClosureEnv { .. } => assert_eq!(
                whole.operands.len(),
                1,
                "clone_closure_env takes exactly the closure place"
            ),
            DropClosureEnv => assert_eq!(
                whole.operands.len(),
                1,
                "drop_closure_env takes exactly the closure place"
            ),
        }
    }

    fn fmt_within(
        &self,
        f: &mut fmt::Formatter<'_>,
        whole: &Instruction,
        env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        use InstructionKind::*;

        match self {
            Alloca { ty } => {
                write!(f, "alloca {}", ty.format_with(env))?;
                if let Some(witness) = whole.operands.first() {
                    write!(f, " using {}", witness.format_with(env))?;
                }
                Ok(())
            }
            AllocaPlace { pointing_to } => {
                write!(f, "alloca_place {}", pointing_to.format_with(env))
            }
            Call => {
                write!(f, "call ")?;
                fmt_callee_and_args(f, whole, env)
            }
            Invoke { normal, unwind } => {
                write!(f, "invoke ")?;
                fmt_callee_and_args(f, whole, env)?;
                write!(f, " -> b{} unwind b{}", normal.raw(), unwind.raw())
            }
            Resume => write!(f, "resume"),
            Project { .. } => {
                write!(f, "project ")?;
                fmt_callee_and_args(f, whole, env)
            }
            Yield => write!(f, "yield {}", whole.operands[0].format_with(env)),
            EndProject => write!(f, "end_project {}", whole.operands[0].format_with(env)),
            CompareEqual => write!(
                f,
                "comp_eq {} {}",
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env)
            ),
            ConditionalBranch {
                on_success,
                on_failure,
            } => write!(
                f,
                "condbr {}, b{}, b{}",
                whole.operands[0].format_with(env),
                on_success.raw(),
                on_failure.raw()
            ),
            UnconditionalBranch { target } => write!(f, "br b{}", target.raw()),
            Load => write!(f, "load {}", whole.operands[0].format_with(env)),
            Subfield { .. } => write!(
                f,
                "subfield {} from {}",
                whole.operands[1].format_with(env),
                whole.operands[0].format_with(env)
            ),
            DictEntry { entry_index, .. } => write!(
                f,
                "dict_entry {} from {}",
                entry_index,
                whole.operands[0].format_with(env)
            ),
            SubscriptMember { mut_member, .. } => write!(
                f,
                "subscript_member {} from {}",
                if *mut_member { "mut" } else { "ref" },
                whole.operands[0].format_with(env)
            ),
            BuildSubscript { .. } => {
                write!(f, "build_subscript {}", whole.operands[0].format_with(env))?;
                if whole.operands.len() > 1 {
                    write!(f, " capturing (")?;
                    for (i, operand) in whole.operands[1..].iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", operand.format_with(env))?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Ret => write!(f, "ret"),
            Variant { tag, .. } => write!(f, "variant .{tag}"),
            ExtractTag => write!(f, "extract_tag {}", whole.operands[0].format_with(env)),
            Store => write!(
                f,
                "store {} to {}",
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env)
            ),
            Clear => write!(f, "clear {}", whole.operands[0].format_with(env)),
            Memcpy => write!(
                f,
                "memcpy {} to {}",
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env)
            ),
            Move => {
                write!(
                    f,
                    "move {} to {}",
                    whole.operands[0].format_with(env),
                    whole.operands[1].format_with(env)
                )?;
                if let Some(witness) = whole.operands.get(2) {
                    write!(f, " using {}", witness.format_with(env))?;
                }
                Ok(())
            }
            StackSave => write!(f, "stack_save"),
            StackRestore => write!(f, "stack_restore {}", whole.operands[0].format_with(env)),
            CheckCallDepth { successors } => fmt_runtime_check(f, "check_call_depth", *successors),
            CheckFuel { successors } => fmt_runtime_check(f, "check_fuel", *successors),
            Drop => write!(
                f,
                "drop {} via {}",
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env)
            ),
            BuildClosure { function, .. } => {
                write!(
                    f,
                    "build_closure {}(",
                    ssa::Value::Function(*function).format_with(env)
                )?;
                for (i, operand) in whole.operands.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", operand.format_with(env))?;
                }
                write!(f, ")")
            }
            CloneClosureEnv { .. } => write!(
                f,
                "clone_closure_env {}",
                whole.operands[0].format_with(env)
            ),
            DropClosureEnv => write!(f, "drop_closure_env {}", whole.operands[0].format_with(env)),
        }
    }
}

fn fmt_callee_and_args(
    f: &mut fmt::Formatter<'_>,
    whole: &Instruction,
    env: &ModuleEnv<'_>,
) -> fmt::Result {
    write!(f, "{}(", whole.operands[0].format_with(env))?;
    for (i, operand) in whole.operands[1..].iter().enumerate() {
        if i != 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", operand.format_with(env))?;
    }
    write!(f, ")")
}

fn fmt_runtime_check(
    f: &mut fmt::Formatter<'_>,
    name: &str,
    successors: Option<(ssa::BlockIdentity, ssa::BlockIdentity)>,
) -> fmt::Result {
    write!(f, "{name}")?;
    if let Some((normal, unwind)) = successors {
        write!(f, " -> b{} unwind b{}", normal.raw(), unwind.raw())?;
    }
    Ok(())
}
