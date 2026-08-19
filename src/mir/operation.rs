// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! MIR operations, terminators, and their contracts.
//!
//! # Operand and result contract
//!
//! Each operation carries a flat `operands: Box<[mir::Value]>` whose length and per-position meaning
//! are fixed by the operation kind (documented on each `Operation::*` constructor below and
//! checked by [`Operation::verify`]). An operand falls into one of four *roles*. A
//! `Register`/`Parameter` does not encode its role, so the per-function MIR verifier derives it from
//! signatures and defining operations before execution:
//!
//! - **place** — a pointer into storage (the result of an `alloca`/`subfield`/`dict_entry`, or an
//!   incoming by-pointer parameter). Consumed by `load`, `store`, `subfield`, `drop`, etc.
//! - **value** — a materialized register or constant (the result of a `load`/`comp_eq`, or a literal
//!   constant). An owned materialized value has *exactly one* consuming use.
//! - **dictionary** — a symbolic trait dictionary (evidence), consumed by `dict_entry`/`call` and
//!   never materialized as a value.
//! - **stack marker** — an immutable saved stack top produced by `stack_save`, used only by
//!   `stack_restore`. A marker may be restored more than once.
//!
//! An operation either defines a single stable result value (`OperationResult` other than
//! `Nothing`) or defines nothing. Every block owns zero or more operations followed by exactly one
//! [`Terminator`](crate::mir::terminator::Terminator). Operations never carry intra-function
//! successors; all normal and source-failure control flow is explicit in the terminator.

use std::fmt;

use itertools::Itertools;
use ustr::Ustr;

use crate::{
    Location, cached_primitive_ty,
    containers::{B, DenseBitSet, b},
    format::FormatWith,
    hir::value::VariantPayloadStorage,
    mir,
    module::{FunctionId, ModuleEnv},
    types::{
        effects::{EffType, Effect, PrimitiveEffect},
        r#trait::TraitDictionaryEntryIndex,
        r#type::{CallImplType, Type},
        type_inference::substitution::InstSubst,
        type_like::TypeLike,
        type_scheme::TypeScheme,
    },
};

/// A non-terminating operation in Ferlium MIR.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Operation {
    /// The function-local identity assigned to this operation's result, if it has one.
    ///
    /// Constructors leave this unset; inserting the operation into a function assigns it.
    result_id: Option<mir::ValueId>,

    /// The region of the code corresponding to this operation.
    pub span: Location,

    /// The operands of the operation.
    pub operands: Box<[mir::Value]>,

    /// The kind-specific part of `self`.
    pub kind: OperationKind,
}

impl Operation {
    /// Returns the parts which determine an operation's run-time behavior.
    ///
    /// The exhaustive destructure is intentional: an added field must be classified here rather
    /// than silently omitted by optimizations which compare operations while deliberately ignoring
    /// their function-local result identity and source span.
    pub(crate) fn kind_and_operands(&self) -> (&OperationKind, &[mir::Value]) {
        let Self {
            result_id: _,
            span: _,
            operands,
            kind,
        } = self;
        (kind, operands)
    }

    /// Returns the stable identity assigned to this operation's result, if any.
    pub fn result_id(&self) -> Option<mir::ValueId> {
        self.result_id
    }

    /// Assigns this operation's result identity when it is inserted into a function.
    pub(crate) fn assign_result_id(&mut self, result_id: Option<mir::ValueId>) {
        debug_assert!(
            self.result_id.is_none(),
            "an operation is inserted only once"
        );
        debug_assert_eq!(
            result_id.is_some(),
            self.result() != OperationResult::Nothing,
            "exactly result-producing operations receive a value identity"
        );
        self.result_id = result_id;
    }

    /// The type of the operation's result.
    pub fn result(&self) -> OperationResult {
        self.kind.result(self)
    }

    /// Whether this operation's result is an owned value which must be consumed exactly once.
    ///
    /// Most result registers merely denote a place or a `TrivialCopy` representation. Constructors
    /// that transfer ownership into a `store` are different: removing that store must retain the
    /// producer or arrange another consuming use.
    pub fn result_requires_consuming_use(&self) -> bool {
        match &self.kind {
            OperationKind::Variant { .. } | OperationKind::CloneClosureEnv { .. } => true,
            OperationKind::BuildClosure {
                num_hidden_dicts,
                has_env_dict,
                ..
            } => {
                let captures =
                    self.operands.len() - *num_hidden_dicts as usize - usize::from(*has_env_dict);
                captures != 0
            }
            _ => false,
        }
    }

    /// Whether two operations are the same, with operands compared by `operand_eq` rather than
    /// directly.
    ///
    /// For a consumer that must treat some operands as equal despite differing — specialization
    /// hash-consing, where two copies of one function name *themselves* by different ids. Everything
    /// else is compared with the derived equality.
    ///
    /// Destructured exhaustively on purpose: a field added to an operation later stops this
    /// compiling rather than silently dropping out of a comparison whose answer decides that two
    /// bodies are interchangeable.
    pub(crate) fn eq_by_operands(
        &self,
        other: &Self,
        operand_eq: &impl Fn(&mir::Value, &mir::Value) -> bool,
    ) -> bool {
        let Self {
            result_id,
            span,
            operands,
            kind,
        } = self;
        *result_id == other.result_id
            && *span == other.span
            && *kind == other.kind
            && operands.len() == other.operands.len()
            && operands
                .iter()
                .zip(other.operands.iter())
                .all(|(own, other)| operand_eq(own, other))
    }

    /// Rebuilds an operation from its parts, without a result identity.
    ///
    /// Inlining decomposes a callee's operation and reassembles it with the caller's operands; the
    /// per-kind constructors above remain the only way to create one during lowering.
    pub(crate) fn from_parts(
        span: Location,
        operands: Box<[mir::Value]>,
        kind: OperationKind,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands,
            kind,
        }
    }

    /// Classifies whether this operation can raise a source-level failure.
    ///
    /// Sandbox violations are deliberately not represented here: they leave the MIR CFG through
    /// executor management. An operation classified as `Fallible` is valid only inside
    /// [`TerminatorKind::Invoke`](crate::mir::terminator::TerminatorKind::Invoke); the verifier
    /// resolves context-dependent operations before enforcing the same rule.
    pub fn source_fallibility(&self) -> SourceFallibility {
        let effects = match &self.kind {
            OperationKind::Call { ty, .. } | OperationKind::Project { ty, .. } => ty.effects(),
            // The defining `Project` carries the accessor type. Resolving this case therefore
            // requires the function-local role of the operand.
            OperationKind::EndProject => return SourceFallibility::FromOpenProjection,
            _ => return SourceFallibility::Infallible,
        };
        if effects.contains(Effect::Primitive(PrimitiveEffect::Fallible)) || effects.has_variables()
        {
            SourceFallibility::Fallible
        } else {
            SourceFallibility::Infallible
        }
    }

    /// Verifies the structural contract of this operation in isolation (the operand **arity**, and
    /// the data-dependent operand count for `alloca`/`move`/`build_closure`).
    pub fn verify(&self) {
        assert_eq!(
            self.result_id.is_some(),
            self.result() != OperationResult::Nothing,
            "exactly result-producing operations have a value identity"
        );
        self.kind.verify(self);
    }

    /// Creates an `alloca` operation for storage whose size is known at compile time.
    pub fn alloca(span: Location, ty: Type) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([]),
            kind: OperationKind::Alloca { ty },
        }
    }

    /// Creates an `alloca` operation for storage whose size is known only at run time.
    ///
    /// `witness` is the place of the `Value` dictionary witnessing the run-time layout of `ty`;
    /// its `SIZE` and `ALIGN` associated const entries determine the size and alignment of the
    /// allocation.
    pub fn alloca_dynamic(span: Location, ty: Type, witness: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([witness]),
            kind: OperationKind::Alloca { ty },
        }
    }

    /// Creates an `alloca_place` operation: stack storage for a *pointer* to an instance of
    /// `pointing_to`. No operands; the result is the place of that pointer slot.
    pub fn alloca_place(span: Location, pointing_to: Type) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([]),
            kind: OperationKind::AllocaPlace { pointing_to },
        }
    }

    /// Creates a `call` operation with the given properties.
    ///
    /// A call yields no register: every callee, including one returning `()`, writes its result
    /// through the return out-pointer passed as the call's last operand.
    ///
    /// ## Callee contract
    ///
    /// Every callable is a function value — a code identity that may additionally carry *hidden
    /// evidence* (the dictionaries/field-indices a generic instantiation needs) and an owned
    /// *closure environment*. Bare functions, dictionary/witness-table methods, and closures are all
    /// the same kind of value and are called the same way.
    ///
    /// The `callee` operand (operand `0`) is therefore **one of two forms**:
    /// - a constant [`mir::Value::Function`] — a direct call to a statically known function (no
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
    pub fn call<T: IntoIterator<Item = mir::Value>>(
        span: Location,
        callee: mir::Value,
        arguments: T,
        ty: CallImplType,
    ) -> Self {
        Self::instantiated_call(span, callee, arguments, ty, None)
    }

    /// Creates a `call` operation that records how it instantiated a generic callee.
    ///
    /// See [`Instantiation`] and `doc/generic-instantiation.md`.
    pub fn instantiated_call<T: IntoIterator<Item = mir::Value>>(
        span: Location,
        callee: mir::Value,
        arguments: T,
        ty: CallImplType,
        instantiation: Option<Instantiation>,
    ) -> Self {
        let mut operands = vec![callee];
        operands.extend(arguments);
        Operation {
            result_id: None,
            span,
            operands: operands.into_boxed_slice(),
            kind: OperationKind::Call {
                ty: b(ty),
                metadata: instantiation.map(|instantiation| {
                    b(CallMetadata {
                        instantiation: Some(instantiation),
                        owned_arguments: DenseBitSet::empty(),
                    })
                }),
            },
        }
    }

    /// Creates a `project` operation: the *enter* half of a scoped (`YieldedOnce`) subscript
    /// access. It runs the subscript accessor `callee` (a `YieldedOnce` member) to its single
    /// `yield`, suspending the accessor frame, and **exposes the yielded place as this operation's
    /// result register** (a place of pointee type `ty`). The body that uses the place runs next; the
    /// matching [`end_project`](Self::end_project), keyed by this result register, resumes the
    /// accessor's slide (epilogue).
    ///
    /// Operands are `[callee, args..]` with the same callee contract as [`call`](Self::call), where
    /// `args` are the accessor's extra (dictionary) and visible arguments. Unlike `call` there is no
    /// trailing return out-pointer: the accessor's nominal return is unused on the yielded path (the
    /// place flows out as this operation's result register). Mirrors the HIR interpreter's
    /// `call_accessor_until_yield`.
    pub fn project<T: IntoIterator<Item = mir::Value>>(
        span: Location,
        callee: mir::Value,
        arguments: T,
        yielded: Type,
        ty: CallImplType,
    ) -> Self {
        let mut operands = vec![callee];
        operands.extend(arguments);
        Operation {
            result_id: None,
            span,
            operands: operands.into_boxed_slice(),
            kind: OperationKind::Project { yielded, ty: b(ty) },
        }
    }

    /// Creates an `end_project` operation: the *leave* half of a scoped subscript access. Operand
    /// `0` is the place a [`project`](Self::project) exposed; this resumes that suspended accessor
    /// from after its `yield`, runs its slide to completion, and reclaims the accessor frame. Mirrors
    /// the HIR interpreter's `resume_suspended_accessor_epilogue`.
    pub fn end_project(span: Location, place: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([place]),
            kind: OperationKind::EndProject,
        }
    }

    /// Creates a `compare_eq` operation comparing operands `0` (`v1`) and `1` (`v2`) for structural
    /// equality, yielding a `bool` register.
    ///
    /// Both operands are read **non-consumingly** as literal snapshots (a place is borrowed, never
    /// moved), so this is the comparison of a lowered `match`: the scrutinee stays live for the
    /// remaining alternatives and the arm body. Each operand must have a literal form (a scalar
    /// constant, or a place/register whose pointee is a scalar or composite literal).
    pub fn compare_eq(span: Location, v1: mir::Value, v2: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([v1, v2]),
            kind: OperationKind::CompareEqual,
        }
    }

    /// Creates a `load` operation reading the value at the place `source` (operand `0`) into a
    /// register.
    ///
    /// `source` must be a **place** whose pointee has a representation-copyable value (currently an
    /// internal place pointer). The source stays initialized. Ownership transfers are explicit
    /// [`move_value`](Self::move_value) operations rather than a run-time choice made by `load`.
    pub fn load(span: Location, source: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([source]),
            kind: OperationKind::Load,
        }
    }

    /// Creates a `subfield` operation yielding the **place** of the field (of type `ty`) of the
    /// aggregate place `source` (operand `0`) at the field index given by the `int` value `index`
    /// (operand `1`).
    ///
    /// `source` must be a place whose pointee is an aggregate with more than `index` fields (or
    /// generic storage that grows to that shape on the first field store); the result is a place,
    /// computed without reading or moving the aggregate. `index` is an ordinary `int` value operand —
    /// usually a typed [`mir::Value::Constant`] from the containing function's pool (a tuple/record
    /// field at a known position), but a register when the offset is only known at run time.
    /// Keeping the index a value operand — rather than splitting static and dynamic forms — matches
    /// how a backend (LLVM `getelementptr`) takes the index as an IR value regardless.
    pub fn subfield(span: Location, source: mir::Value, index: mir::Value, ty: Type) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([source, index]),
            kind: OperationKind::Subfield { ty },
        }
    }

    /// Creates a `dict_entry` operation: the symbolic analog of `subfield` for a trait dictionary.
    ///
    /// `dict` is a symbolic dictionary operand (a constant [`mir::Value::Dictionary`] or a forwarded
    /// dictionary `Parameter`). The operation yields the **place** of entry `entry_index` of that
    /// dictionary — a method function value, or an associated const — of type `ty`. `call`, `drop`,
    /// and `memcpy` consume that place exactly as they consume a `subfield` result, so a later
    /// tuple-lowering pass rewrites `dict_entry N from <symbolic dict>` to
    /// `subfield N from <materialized witness-table tuple>` one-for-one.
    pub fn dict_entry(
        span: Location,
        dict: mir::Value,
        entry_index: TraitDictionaryEntryIndex,
        ty: Type,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([dict]),
            kind: OperationKind::DictEntry { entry_index, ty },
        }
    }

    /// Creates a `subscript_member` operation: the member-resolving analog of
    /// [`Operation::dict_entry`] for a first-class subscript.
    ///
    /// `subscript` is a symbolic subscript operand (a constant [`mir::Value::Subscript`] or a
    /// forwarded evidence `Parameter`). The operation yields the **place** of the subscript's
    /// `ref`/`mut` member — a function value of type `ty` bundling the subscript's captured hidden
    /// evidence — which a `call`/`project` consumes by reference exactly like a closure callee.
    pub fn subscript_member(
        span: Location,
        subscript: mir::Value,
        mut_member: bool,
        ty: Type,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([subscript]),
            kind: OperationKind::SubscriptMember { mut_member, ty },
        }
    }

    /// Creates a `build_subscript` operation, which bundles the symbolic subscript at operand `0`
    /// with captured hidden evidence — the remaining operands, each a symbolic dictionary or
    /// subscript operand — yielding a first-class subscript value of type `ty`. With no captures it
    /// reads the subscript operand into a fresh first-class value (the lowering of a subscript
    /// clone).
    pub fn build_subscript(
        span: Location,
        subscript: mir::Value,
        evidence: Vec<mir::Value>,
        ty: Type,
    ) -> Self {
        let mut operands = vec![subscript];
        operands.extend(evidence);
        Operation {
            result_id: None,
            span,
            operands: operands.into_boxed_slice(),
            kind: OperationKind::BuildSubscript { ty },
        }
    }

    /// Creates a `variant` operation, which builds a tagged variant *shell* of type `ty`: the
    /// result is a register holding `Value::Variant { tag, <uninitialized payload> }`. The
    /// constructing site stores the shell into the variant's destination and then fills the payload
    /// in place through a projection of that destination (variant payload index `0`), so the
    /// payload aggregate — which may be generic and thus have no `Value` layout witness — is never
    /// materialized into a temporary.
    pub fn variant(
        span: Location,
        tag: Ustr,
        t: Type,
        storage: Option<VariantPayloadStorage>,
        evidence: Option<mir::Value>,
    ) -> Self {
        assert_eq!(storage.is_none(), evidence.is_some());
        Operation {
            result_id: None,
            span,
            operands: evidence.into_iter().collect(),
            kind: OperationKind::Variant {
                tag,
                ty: t,
                storage,
            },
        }
    }

    /// Creates a fresh array from representation-copyable element operands and initializes
    /// `destination` with it.
    ///
    /// Every element operand is read non-consumingly, either as a materialized value or through a
    /// place. Consequently `element_ty` must be statically `TrivialCopy`: building an array of
    /// values with semantic clone/drop behaviour requires a `Value` dictionary and is deliberately
    /// left to the existing in-place lowering. The trailing destination must name uninitialized
    /// `[element_ty]` storage.
    pub fn build_array<T: IntoIterator<Item = mir::Value>>(
        span: Location,
        element_ty: Type,
        elements: T,
        destination: mir::Value,
    ) -> Self {
        let mut operands: Vec<_> = elements.into_iter().collect();
        operands.push(destination);
        Operation {
            result_id: None,
            span,
            operands: operands.into_boxed_slice(),
            kind: OperationKind::BuildArray { element_ty },
        }
    }

    /// Creates an `extract_tag` operation, which reads the tag of the variant at the `variant`
    /// place and yields it as an `int` register (matching the HIR interpreter's tag encoding).
    ///
    /// The result is the *semantic* tag — the session-local interned identity a `VariantTag` pattern
    /// compares against — not the raw ABI field. The canonical layout stores a `u32` whose high bit
    /// records indirect payload storage (see `doc/abi.md`), so a backend reading that field owes the
    /// mask and the widening to `int`. The reference interpreter keeps the tag symbolically and
    /// interns it here, so the two never diverge; a concrete backend must arrange that itself. The
    /// identity always fits 31 bits, which `CompilerSession::variant_tag_id` asserts, so the widened
    /// value is non-negative on a 32-bit target too.
    pub fn extract_tag(span: Location, variant: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([variant]),
            kind: OperationKind::ExtractTag,
        }
    }

    /// Creates a `stack_save` operation, whose result is a marker for the current top of the
    /// stack.
    ///
    /// Paired with `stack_restore`, this brackets a region (such as a loop body) so that the
    /// temporaries it allocates are reclaimed on every back-edge and exit, bounding stack use. The
    /// marker is an immutable frontier and may be restored repeatedly.
    pub fn stack_save(span: Location) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([]),
            kind: OperationKind::StackSave,
        }
    }

    /// Creates a `stack_restore` operation, which resets the top of the stack to `marker` (the
    /// result of an earlier `stack_save`), reclaiming everything allocated since.
    pub fn stack_restore(span: Location, marker: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([marker]),
            kind: OperationKind::StackRestore,
        }
    }

    /// Creates a runtime call-depth guard corresponding to HIR `CheckCallDepth`.
    pub fn check_call_depth(span: Location) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([]),
            kind: OperationKind::CheckCallDepth,
        }
    }

    /// Creates a runtime fuel guard corresponding to HIR `CheckFuel`.
    pub fn check_fuel(span: Location) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([]),
            kind: OperationKind::CheckFuel,
        }
    }

    /// Creates a `store` operation writing the **value** operand `0` (`value`) into the **place**
    /// operand `1` (`destination`).
    ///
    /// A `store` **drops nothing**: `destination` must carry no live semantic drop obligation — it
    /// is absent or contains a `TrivialCopy` representation — so the emitter owes an explicit
    /// `drop` before overwriting a managed/custom-drop pointee. Yields no register; `value` is
    /// consumed (moved, for a non-trivial value).
    pub fn store(span: Location, value: mir::Value, destination: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([value, destination]),
            kind: OperationKind::Store,
        }
    }

    /// Creates a `clear` operation that marks the storage at `destination` absent. The previous
    /// state must carry no live semantic drop obligation; clearing is initialization bookkeeping,
    /// not a semantic drop.
    pub fn clear(span: Location, destination: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([destination]),
            kind: OperationKind::Clear,
        }
    }

    /// Creates a `memcpy` operation: a pure, **source-preserving** copy of the pointee of `source`
    /// (a place) into `destination` (a place), without first materializing it in a register.
    ///
    /// The pointee must be concrete `TrivialCopy`. Any other copy is lowered through `Value::clone`
    /// (a `call`) by HIR before reaching the emitter, and an ownership transfer uses
    /// [`move_value`](Self::move_value); a bare `memcpy` never moves its source out.
    ///
    /// **Requirement:** the pointee must have a **statically known layout** — a real backend sizes the
    /// copy from the type alone. Copies are always statically sized; a generic transfer is a
    /// [`move_dynamic`](Self::move_dynamic), never a `memcpy`.
    pub fn memcpy(span: Location, source: mir::Value, destination: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([source, destination]),
            kind: OperationKind::Memcpy,
        }
    }

    /// Creates a `move` operation: a **source-consuming** ownership transfer of the whole pointee of
    /// `source` (a place) into `destination` (a place). The source is left moved-out. For a
    /// statically-sized pointee; a generic (run-time-layout) transfer uses
    /// [`move_dynamic`](Self::move_dynamic). Unlike a copy, a move needs no `Value::clone`; unlike
    /// `memcpy`, it consumes the source.
    pub fn move_value(span: Location, source: mir::Value, destination: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([source, destination]),
            kind: OperationKind::Move,
        }
    }

    /// Creates a `move` operation for a value whose size is known only at run time: a move of a
    /// generic (bare-type-variable-typed) pointee. `witness` is the place of the `Value` dictionary
    /// witnessing the run-time layout of the moved value (its `SIZE`/`ALIGN`), exactly as for
    /// [`alloca_dynamic`](Self::alloca_dynamic). The MIR interpreter moves the value shape-agnostically
    /// (the witness is metadata it ignores); a real backend uses the witness to size the copy.
    pub fn move_dynamic(
        span: Location,
        source: mir::Value,
        destination: mir::Value,
        witness: mir::Value,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([source, destination, witness]),
            kind: OperationKind::Move,
        }
    }

    /// Creates a 'drop' operation.
    ///
    /// Drops the pointee of `target` (a place) by invoking the `Value::drop` implementation named by
    /// `callee`, but **only if** the pointee is currently initialized. An already-uninitialized
    /// (moved-out or never-initialized) pointee is left untouched. This init guard is what makes
    /// the inline drops the emitter places at scope-exit edges run exactly once.
    ///
    /// `callee` follows the same contract as the [`call`](Self::call) callee: it is either a constant
    /// [`mir::Value::Function`] or the **place** of a function value (e.g. the `Value::drop` method
    /// slot `project`ed out of a dictionary), read by reference and never loaded into a register.
    pub fn drop(span: Location, target: mir::Value, callee: mir::Value, ty: Type) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([target, callee]),
            kind: OperationKind::Drop { ty },
        }
    }

    /// Creates a `clone` operation.
    ///
    /// Copies the pointee of `source` (a place) into `destination` (an uninitialized place) by
    /// invoking the `Value::clone` implementation named by `callee`, which follows the same contract
    /// as [`drop`](Self::drop)'s. The destination takes on the drop obligation the copy creates.
    ///
    /// Source-infallible: `Value::clone` is declared with an empty effect row, and a fallible impl
    /// is rejected at compile time, so a clone never needs an `invoke`.
    pub fn clone_value(
        span: Location,
        source: mir::Value,
        destination: mir::Value,
        callee: mir::Value,
        ty: Type,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([source, destination, callee]),
            kind: OperationKind::Clone { ty },
        }
    }

    /// Creates a `build_closure` operation, which bundles a function with its captured environment
    /// into a first-class closure value.
    ///
    /// `function` identifies the closure's target (lambda) function. `hidden_dicts` are the symbolic
    /// dictionary operands for the lambda body's hidden `@extra` parameters (the dictionary captures,
    /// in target-parameter order); each is a constant [`mir::Value::Dictionary`] or a forwarded
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
        hidden_dicts: Vec<mir::Value>,
        env_dict: Option<mir::Value>,
        ty: Type,
        captures: Vec<mir::Value>,
    ) -> Self {
        let num_hidden_dicts = u32::try_from(hidden_dicts.len())
            .expect("a closure cannot capture more than u32::MAX hidden dictionaries");
        let has_env_dict = env_dict.is_some();
        let mut operands = hidden_dicts;
        operands.extend(captures);
        operands.extend(env_dict);
        Operation {
            result_id: None,
            span,
            operands: operands.into_boxed_slice(),
            kind: OperationKind::BuildClosure {
                function,
                num_hidden_dicts,
                has_env_dict,
                ty,
            },
        }
    }

    /// Creates a `clone_closure_env` operation, which deep-clones the captured environment of the
    /// closure at the place given by `source`, yielding a fresh closure value of type `ty`.
    pub fn clone_closure_env(span: Location, source: mir::Value, ty: Type) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([source]),
            kind: OperationKind::CloneClosureEnv { ty },
        }
    }

    /// Creates a `drop_closure_env` operation, which drops the owned captured environment of the
    /// closure at the place given by `target`.
    pub fn drop_closure_env(span: Location, target: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([target]),
            kind: OperationKind::DropClosureEnv,
        }
    }
}

/// Whether an operation can raise a source-level failure.
///
/// Sandbox violations are outside this classification. `EndProject` is context-dependent because
/// its accessor type belongs to the open projection defined by its operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceFallibility {
    /// The operation cannot raise a source failure.
    Infallible,
    /// The operation can raise and must be represented by `Invoke`.
    Fallible,
    /// Fallibility comes from the operation's defining open projection.
    FromOpenProjection,
}

/// How a call site instantiated a generic callee: the type and effect arguments its quantifiers
/// stand for, positionally.
///
/// Carried down from HIR's `FnInstData` rather than recovered by matching the callee's generic
/// signature against this call's concrete one. Written in the type environment of the *containing*
/// function, so a generic caller records its own quantifiers; substituting the container therefore
/// composes the two instantiations. See `doc/generic-instantiation.md`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Instantiation {
    pub ty_args: Vec<Type>,
    pub eff_args: Vec<EffType>,
}

/// Optional metadata carried only by calls that need it.
///
/// Keeping this behind the existing optional box preserves the compact representation of the
/// overwhelmingly common non-generic, borrowing call. Monomorphization uses `instantiation`; the
/// final ownership-transfer pass uses `owned_arguments`, indexed by visible argument position.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct CallMetadata {
    pub(crate) instantiation: Option<Instantiation>,
    pub(crate) owned_arguments: DenseBitSet,
}

impl Instantiation {
    /// Builds the substitution taking the callee's quantifiers to what this call site instantiated
    /// them at, in the callee's own variable numbering.
    ///
    /// The arguments are positional against `scheme`'s quantifiers, `eff_quantifiers` being a set
    /// and so ordered the one way `TypeScheme`'s `Hash` impl orders it. Panics if the lengths
    /// disagree: that is a lowering bug, and the MIR verifier reports it with the callee named.
    pub fn substitution<Ty: TypeLike>(&self, scheme: &TypeScheme<Ty>) -> InstSubst {
        assert_eq!(
            self.ty_args.len(),
            scheme.ty_quantifiers.len(),
            "instantiation records {} type arguments for {} quantifiers",
            self.ty_args.len(),
            scheme.ty_quantifiers.len()
        );
        (
            scheme
                .ty_quantifiers
                .iter()
                .copied()
                .zip(self.ty_args.iter().copied())
                .collect(),
            scheme
                .eff_quantifiers
                .iter()
                .sorted()
                .copied()
                .zip(self.eff_args.iter().cloned())
                .collect(),
        )
    }
}

/// The kind-specific metadata of a MIR operation.
///
/// Operands stay in [`Operation::operands`] so generic MIR traversals can inspect and rewrite
/// them uniformly. This enum contains only metadata whose shape is specific to an operation.
#[derive(Clone, PartialEq, Eq, Hash, strum::EnumDiscriminants)]
#[strum_discriminants(
    name(OperationKindDiscriminant),
    derive(Hash, PartialOrd, Ord, strum::Display),
    strum(serialize_all = "snake_case")
)]
pub enum OperationKind {
    /// Stack storage for a value of `ty`, optionally using a run-time layout witness.
    Alloca { ty: Type },
    /// Stack storage for a pointer to a value of `pointing_to`.
    AllocaPlace { pointing_to: Type },
    /// A statically or dynamically resolved function call with its instantiated call-site type.
    /// Optional metadata records generic instantiation and optimized ownership transfer. Both are
    /// boxed to keep every operation compact; most calls need no metadata at all.
    Call {
        ty: B<CallImplType>,
        metadata: Option<B<CallMetadata>>,
    },
    /// Enter a scoped subscript accessor and expose its yielded place.
    /// The call-site type is boxed for the same compactness reason as [`Self::Call`].
    Project { yielded: Type, ty: B<CallImplType> },
    /// Resume and finish a scoped subscript accessor.
    EndProject,
    /// Compare a runtime value with compile-time literal-pattern metadata.
    CompareEqual,
    /// Read a representation-copyable value from a place without consuming it.
    Load,
    /// Project a field place from an aggregate place.
    Subfield { ty: Type },
    /// Project a function entry place from a symbolic dictionary.
    DictEntry {
        entry_index: TraitDictionaryEntryIndex,
        ty: Type,
    },
    /// Resolve a member function place from a symbolic subscript.
    SubscriptMember { mut_member: bool, ty: Type },
    /// Bundle a symbolic subscript with its captured evidence.
    BuildSubscript { ty: Type },
    /// Construct a tagged variant shell whose payload is initialized separately.
    Variant {
        tag: Ustr,
        ty: Type,
        /// `None` means operand 0 carries forwarded generic storage evidence.
        storage: Option<VariantPayloadStorage>,
    },
    /// Construct a fresh array from `TrivialCopy` elements into a trailing destination place.
    BuildArray { element_ty: Type },
    /// Read a variant tag as an integer.
    ExtractTag,
    /// Store a value into unoccupied place storage.
    Store,
    /// Mark place storage absent without semantic drop.
    Clear,
    /// Copy a statically sized `TrivialCopy` representation between places.
    Memcpy,
    /// Transfer ownership between places, optionally using a run-time layout witness.
    Move,
    /// Save the current stack top.
    StackSave,
    /// Restore a previously saved stack top.
    StackRestore,
    /// Enforce the configured script call-depth limit.
    CheckCallDepth,
    /// Consume one unit of optional execution fuel.
    CheckFuel,
    /// Semantically copy a value through its `Value::clone` function.
    ///
    /// The counterpart of [`Self::Memcpy`]: both copy, but a `memcpy` duplicates a representation
    /// while a `clone` runs the type's own copying logic. Which one lowering emits is decided by
    /// whether the type is trivially copyable.
    Clone { ty: Type },
    /// Semantically drop an initialized value through its `Value::drop` function.
    Drop { ty: Type },
    /// Construct a closure from a function and its captured environment.
    BuildClosure {
        function: FunctionId,
        num_hidden_dicts: u32,
        has_env_dict: bool,
        ty: Type,
    },
    /// Deep-clone a closure's captured environment.
    CloneClosureEnv { ty: Type },
    /// Drop a closure's captured environment.
    DropClosureEnv,
}

impl OperationKind {
    /// Visits every function this kind names *itself*, rather than through an operand.
    ///
    /// A call names its callee in operand 0 as a [`mir::Value::Function`], which any operand walk
    /// reaches; `build_closure` is the one kind holding a [`FunctionId`] where no operand walk can
    /// see it. Whole-module renumbering has to reach both, and a reference it misses is a dangling
    /// id rather than a missed opportunity, so this match is exhaustive on purpose: a kind that
    /// later carries a function stops this compiling instead of being silently skipped.
    pub(crate) fn visit_function_ids_mut(&mut self, mut visit: impl FnMut(&mut FunctionId)) {
        use OperationKind::*;
        match self {
            BuildClosure { function, .. } => visit(function),
            Alloca { .. }
            | AllocaPlace { .. }
            | Call { .. }
            | Project { .. }
            | EndProject
            | CompareEqual
            | Load
            | Subfield { .. }
            | DictEntry { .. }
            | SubscriptMember { .. }
            | BuildSubscript { .. }
            | Variant { .. }
            | BuildArray { .. }
            | ExtractTag
            | Store
            | Clear
            | Memcpy
            | Move
            | StackSave
            | StackRestore
            | CheckCallDepth
            | CheckFuel
            | Clone { .. }
            | Drop { .. }
            | CloneClosureEnv { .. }
            | DropClosureEnv => {}
        }
    }

    /// The function this kind names *itself*, if it names one.
    ///
    /// The read-only twin of [`visit_function_ids_mut`](Self::visit_function_ids_mut), for the
    /// callers that only want to know which functions a body reaches and must not pay a body clone
    /// to ask. Exhaustive for the same reason, and the two must agree: a kind that starts carrying a
    /// function stops both compiling.
    pub(crate) fn function_id(&self) -> Option<FunctionId> {
        use OperationKind::*;
        match self {
            BuildClosure { function, .. } => Some(*function),
            Alloca { .. }
            | AllocaPlace { .. }
            | Call { .. }
            | Project { .. }
            | EndProject
            | CompareEqual
            | Load
            | Subfield { .. }
            | DictEntry { .. }
            | SubscriptMember { .. }
            | BuildSubscript { .. }
            | Variant { .. }
            | BuildArray { .. }
            | ExtractTag
            | Store
            | Clear
            | Memcpy
            | Move
            | StackSave
            | StackRestore
            | CheckCallDepth
            | CheckFuel
            | Clone { .. }
            | Drop { .. }
            | CloneClosureEnv { .. }
            | DropClosureEnv => None,
        }
    }
}

impl FormatWith<ModuleEnv<'_>> for Operation {
    fn fmt_with(&self, f: &mut fmt::Formatter<'_>, env: &ModuleEnv<'_>) -> fmt::Result {
        self.kind.fmt_within(f, self, env)
    }
}

/// The type of an operation's result.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum OperationResult {
    /// A type expressible in Ferlium.
    Lowered(Type),

    /// The type of a MIR value.
    Same(mir::Value),

    /// The type of the value referred to by a pointer.
    Pointee(Box<OperationResult>),

    /// A pointer to a type.
    Pointer(Box<OperationResult>),

    /// A backend-internal marker for a saved top of the stack (the result of `stack_save`). It is
    /// not a Ferlium-expressible type; it is only consumed by a matching `stack_restore`.
    StackMarker,

    /// An operation that does not produce a value.
    Nothing,
}

impl OperationResult {
    /// Returns the type of a pointee referred to by an instance of `pointer`.
    fn pointee_of(pointer: OperationResult) -> OperationResult {
        OperationResult::Pointee(Box::new(pointer))
    }

    /// Returns the type of a pointer to an instance of `pointee`.
    fn pointer_to(pointee: OperationResult) -> OperationResult {
        OperationResult::Pointer(Box::new(pointee))
    }
}

impl OperationKind {
    fn result(&self, whole: &Operation) -> OperationResult {
        use OperationKind::*;

        match self {
            Alloca { ty } => OperationResult::pointer_to(OperationResult::Lowered(*ty)),
            AllocaPlace { pointing_to } => OperationResult::pointer_to(
                OperationResult::pointer_to(OperationResult::Lowered(*pointing_to)),
            ),
            Project { yielded: ty, .. }
            | Subfield { ty }
            | DictEntry { ty, .. }
            | SubscriptMember { ty, .. } => {
                OperationResult::pointer_to(OperationResult::Lowered(*ty))
            }
            CompareEqual => OperationResult::Lowered(cached_primitive_ty!(bool)),
            Load => OperationResult::pointee_of(OperationResult::Same(whole.operands[0].clone())),
            BuildSubscript { ty }
            | Variant { ty, .. }
            | BuildClosure { ty, .. }
            | CloneClosureEnv { ty } => OperationResult::Lowered(*ty),
            ExtractTag => OperationResult::Lowered(cached_primitive_ty!(isize)),
            StackSave => OperationResult::StackMarker,
            Call { .. }
            | BuildArray { .. }
            | EndProject
            | Store
            | Clear
            | Memcpy
            | Move
            | StackRestore
            | CheckCallDepth
            | CheckFuel
            | Clone { .. }
            | Drop { .. }
            | DropClosureEnv => OperationResult::Nothing,
        }
    }

    fn verify(&self, whole: &Operation) {
        use OperationKind::*;

        match self {
            Alloca { .. } => assert!(
                whole.operands.len() <= 1,
                "alloca takes the run-time-layout witness iff its type is not statically sized (0 or 1 operand)"
            ),
            AllocaPlace { .. } => {
                assert!(whole.operands.is_empty(), "alloca_place takes no operands")
            }
            Call { .. } => assert!(
                whole.operands.len() >= 2,
                "call needs the callee and a trailing result place"
            ),
            Project { .. } => assert!(
                !whole.operands.is_empty(),
                "project needs at least the callee operand"
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
            Variant { storage, .. } => assert_eq!(
                whole.operands.len(),
                usize::from(storage.is_none()),
                "variant takes one evidence operand exactly when its storage mode is dynamic"
            ),
            BuildArray { .. } => assert!(
                !whole.operands.is_empty(),
                "build_array takes zero or more elements and a trailing destination place"
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
                "memcpy is a pure copy of a statically-sized TrivialCopy pointee: source and destination only"
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
            CheckCallDepth | CheckFuel => {
                assert!(whole.operands.is_empty(), "runtime checks take no operands")
            }
            Drop { .. } => assert_eq!(
                whole.operands.len(),
                2,
                "drop takes the target place and the Value::drop callee"
            ),
            Clone { .. } => assert_eq!(
                whole.operands.len(),
                3,
                "clone takes the source and destination places and the Value::clone callee"
            ),
            BuildClosure {
                num_hidden_dicts,
                has_env_dict,
                ..
            } => assert!(
                whole.operands.len() >= *num_hidden_dicts as usize + *has_env_dict as usize,
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
        whole: &Operation,
        env: &ModuleEnv<'_>,
    ) -> fmt::Result {
        use OperationKind::*;

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
            Call { ty, metadata } => {
                write!(f, "call ")?;
                fmt_callee_and_args(
                    f,
                    whole,
                    env,
                    metadata
                        .as_deref()
                        .map(|metadata| (&metadata.owned_arguments, ty.fn_ty.args.len())),
                )
            }
            Project { .. } => {
                write!(f, "project ")?;
                fmt_callee_and_args(f, whole, env, None)
            }
            EndProject => write!(f, "end_project {}", whole.operands[0].format_with(env)),
            CompareEqual => write!(
                f,
                "comp_eq {} {}",
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env)
            ),
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
            Variant { tag, .. } => write!(f, "variant {tag}"),
            BuildArray { element_ty } => {
                write!(f, "build_array<{}> [", element_ty.format_with(env))?;
                let (destination, elements) = whole
                    .operands
                    .split_last()
                    .expect("build_array has a trailing destination");
                for (index, element) in elements.iter().enumerate() {
                    if index != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", element.format_with(env))?;
                }
                write!(f, "] to {}", destination.format_with(env))
            }
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
            CheckCallDepth => write!(f, "check_call_depth"),
            CheckFuel => write!(f, "check_fuel"),
            // The type is printed bare, as `alloca` prints its own: it is what decides whether the
            // semantic form is still needed after substitution, and for a dictionary-dispatched
            // callee it is not recoverable from the rest of the line.
            Drop { ty } => write!(
                f,
                "drop {} {} via {}",
                ty.format_with(env),
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env)
            ),
            Clone { ty } => write!(
                f,
                "clone {} {} to {} via {}",
                ty.format_with(env),
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env),
                whole.operands[2].format_with(env)
            ),
            BuildClosure { function, .. } => {
                write!(
                    f,
                    "build_closure {}(",
                    mir::Value::Function(*function).format_with(env)
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
    whole: &Operation,
    env: &ModuleEnv<'_>,
    owned: Option<(&DenseBitSet, usize)>,
) -> fmt::Result {
    write!(f, "{}(", whole.operands[0].format_with(env))?;
    let visible_start = owned.map(|(_, visible)| whole.operands.len() - visible - 1);
    for (i, operand) in whole.operands[1..].iter().enumerate() {
        if i != 0 {
            write!(f, ", ")?;
        }
        if let (Some((owned, _)), Some(visible_start)) = (owned, visible_start)
            && i + 1 >= visible_start
            && i + 1 < whole.operands.len() - 1
            && owned.contains(i + 1 - visible_start)
        {
            write!(f, "move ")?;
        }
        write!(f, "{}", operand.format_with(env))?;
    }
    write!(f, ")")
}

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use super::{Operation, OperationKind};
    use crate::{
        CompilerSession, Location, format::FormatWith, hir::value::VariantPayloadStorage,
        types::r#type::Type,
    };
    use ustr::ustr;

    #[test]
    #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn operation_representation_stays_compact() {
        // Boxing call-site signatures prevents the largest operation variant from inflating every
        // operation in a basic block.
        assert_eq!(size_of::<OperationKind>(), 24);
        assert_eq!(
            size_of::<Operation>(),
            if cfg!(target_pointer_width = "64") {
                56
            } else {
                48
            }
        );
    }

    #[test]
    fn variant_operation_renders_its_tag_without_a_prefix() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let tag = ustr("Some");
        let operation = Operation::variant(
            Location::new_synthesized(),
            tag,
            Type::variant([(tag, Type::unit())]),
            Some(VariantPayloadStorage::Inline),
            None,
        );

        assert_eq!(operation.format_with(&env).to_string(), "variant Some");
    }
}
