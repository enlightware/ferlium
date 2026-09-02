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
//! checked by [`Operation::verify`]). An operand falls into one of several *roles*. A
//! `Register`/`Parameter` does not encode its role, so the per-function MIR verifier derives it from
//! signatures and defining operations before execution:
//!
//! - **place** — addressable storage (the result of an `alloca`/`subfield`/`dict_entry`, or an
//!   incoming by-pointer parameter). Places are borrowed and consumed by `load`, `store`,
//!   `subfield`, `drop`, etc.
//! - **value** — a materialized register or constant (the result of a `load`/`comp_eq`, or a literal
//!   constant). A pointer value can also be dereferenced by place-consuming operations.
//! - **variant tag** — an opaque semantic tag produced by `extract_tag`, comparable only with
//!   symbolic variant-tag pattern data.
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
    module::{FunctionId, ModuleEnv, TraitDictionaryId},
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

    /// Whether this operation's result carries ownership which must be consumed exactly once on
    /// every returning control-flow path that executes the definition.
    ///
    /// Most result registers merely denote a borrowed place or a `TrivialCopy` representation.
    /// Constructors and fresh run-time allocations transfer ownership into a `store` or explicit
    /// deallocation; removing that consuming operation must retain or redirect the obligation.
    pub fn result_requires_consuming_use(&self) -> bool {
        match &self.kind {
            OperationKind::RuntimeAlloc { .. }
            | OperationKind::Variant { .. }
            | OperationKind::BuildSubscript { .. }
            | OperationKind::CloneSubscriptEnv { .. }
            | OperationKind::CloneClosureEnv { .. } => true,
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

    /// Allocates an explicitly sized run-time region and returns its base as a materialized pointer
    /// to `pointee`.
    ///
    /// `size` is the complete byte extent, which may hold any number of adjacent `pointee` values;
    /// `align` is the allocation's positive power-of-two alignment. The fresh allocation is
    /// uninitialized and remains live until its address is transferred to owning storage or passed
    /// to [`Self::runtime_dealloc`]. A zero-byte allocation is valid and reclaimable.
    pub fn runtime_alloc(
        span: Location,
        pointee: Type,
        size: mir::Value,
        align: mir::Value,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([size, align]),
            kind: OperationKind::RuntimeAlloc { pointee },
        }
    }

    /// Deallocates the run-time allocation identified by `address`.
    ///
    /// The target runtime recovers the allocation's byte extent and alignment from the address;
    /// neither is repeated in MIR. The allocation's initialized values must already have been
    /// dropped and its owning storage must be cleared separately.
    pub fn runtime_dealloc(span: Location, address: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([address]),
            kind: OperationKind::RuntimeDealloc,
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
    /// Both operands are read **non-consumingly**, so this is the comparison of a lowered `match`:
    /// the scrutinee stays live for the remaining alternatives and the arm body. An ordinary
    /// pattern reads a literal snapshot of a scalar or composite Ferlium value. A symbolic
    /// `VariantTag` pattern instead requires the opaque tag result of `extract_tag`.
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

    /// Creates a product-field projection with the direct member-layout evidence required to
    /// compute its physical byte offset. The boxed interpreters use the logical index and ignore
    /// the evidence; physical lowering consumes it when the aggregate layout remains open.
    ///
    /// `source` is an aggregate place containing `index`, or generic storage which takes that
    /// aggregate shape on its first field store. The ordinary Ferlium `int` index yields the field
    /// place without reading or moving the aggregate and lets static and run-time indices share one
    /// operation through physical lowering.
    pub fn product_subfield(
        span: Location,
        source: mir::Value,
        index: mir::Value,
        ty: Type,
        aggregate_ty: Type,
        layout_witnesses: impl IntoIterator<Item = (Type, mir::Value)>,
    ) -> Self {
        let (layout_witness_tys, witnesses): (Vec<_>, Vec<_>) =
            layout_witnesses.into_iter().unzip();
        let mut operands = vec![source, index];
        operands.extend(witnesses);
        Operation {
            result_id: None,
            span,
            operands: operands.into_boxed_slice(),
            kind: OperationKind::Subfield {
                ty,
                variant_payload: false,
                has_layout_witness: false,
                product: Some(Box::new(ProductProjectionMetadata {
                    aggregate_ty,
                    layout_witness_tys: layout_witness_tys.into_boxed_slice(),
                })),
            },
        }
    }

    /// Creates a physical byte-address projection from `base` to a place of `ty`.
    ///
    /// `base` is an address-bearing place and `byte_offset` is a materialized Ferlium `int`.
    /// Physical lowering guarantees that the resulting address is within the same allocation and
    /// aligned for `ty`.
    pub fn address_offset(
        span: Location,
        base: mir::Value,
        byte_offset: mir::Value,
        ty: Type,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([base, byte_offset]),
            kind: OperationKind::AddressOffset { ty },
        }
    }

    /// Creates a physical byte-address projection to a slot containing a place of `pointing_to`.
    /// Loading the result yields the stored place rather than the pointee value.
    pub fn address_offset_place(
        span: Location,
        base: mir::Value,
        byte_offset: mir::Value,
        pointing_to: Type,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([base, byte_offset]),
            kind: OperationKind::AddressOffsetPlace { pointing_to },
        }
    }

    /// Creates a place projection for the complete payload `ty` of an already established variant
    /// case. The stored tag supplies inline/indirect classification. `layout_witness` is present
    /// exactly when `ty` has a run-time-dependent layout and supplies `Value<ty>`.
    pub fn variant_payload(
        span: Location,
        source: mir::Value,
        index: mir::Value,
        ty: Type,
        layout_witness: Option<mir::Value>,
    ) -> Self {
        let has_layout_witness = layout_witness.is_some();
        let mut operands = vec![source, index];
        operands.extend(layout_witness);
        Operation {
            result_id: None,
            span,
            operands: operands.into_boxed_slice(),
            kind: OperationKind::Subfield {
                ty,
                variant_payload: true,
                has_layout_witness,
                product: None,
            },
        }
    }

    /// Creates a `dict_entry` operation: the symbolic analog of `subfield` for a trait dictionary.
    ///
    /// `dict` is a symbolic dictionary operand (a constant [`mir::Value::Dictionary`] or a forwarded
    /// dictionary `Parameter`). The operation yields the **place** of entry `entry_index` of that
    /// dictionary — a method function value, or an associated const — of type `ty`. `call`, `drop`,
    /// and `memcpy` consume that place exactly as they consume a `subfield` result. Physical MIR
    /// retains this projection together with relocatable metadata for the referenced definition;
    /// whole-program assembly selects its target representation.
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

    /// Closes a dictionary definition over its ordered hidden-evidence captures.
    pub fn build_dictionary(
        span: Location,
        definition: TraitDictionaryId,
        captures: Vec<mir::Value>,
        ty: Type,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands: captures.into_boxed_slice(),
            kind: OperationKind::BuildDictionary { definition, ty },
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

    /// Creates non-owning closed subscript evidence by appending `captures` to `subscript`'s
    /// existing evidence environment. HIR elaboration flattens ordinary construction onto an open
    /// symbolic base.
    pub fn build_subscript_evidence(
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
            kind: OperationKind::BuildSubscriptEvidence { ty },
        }
    }

    /// Materializes closed subscript evidence as an owned first-class subscript value.
    pub fn build_subscript(span: Location, subscript: mir::Value, ty: Type) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([subscript]),
            kind: OperationKind::BuildSubscript { ty },
        }
    }

    /// Deep-clones the environment of the first-class subscript at `source`.
    pub fn clone_subscript_env(span: Location, source: mir::Value, ty: Type) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([source]),
            kind: OperationKind::CloneSubscriptEnv { ty },
        }
    }

    /// Drops the owned environment of the first-class subscript at `target`.
    pub fn drop_subscript_env(span: Location, target: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([target]),
            kind: OperationKind::DropSubscriptEnv,
        }
    }

    /// Borrows one callable member from a closed subscript without copying its environment.
    pub fn borrow_subscript_member(
        span: Location,
        subscript: mir::Value,
        mut_member: bool,
        ty: Type,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([subscript]),
            kind: OperationKind::BorrowSubscriptMember { mut_member, ty },
        }
    }

    /// Creates a `variant` operation, which builds a tagged variant *shell* of type `ty`: the
    /// result is a register holding `Value::Variant { tag, <uninitialized payload> }`. The
    /// constructing site stores the shell into the variant's destination and then fills the payload
    /// in place through a projection of that destination (variant payload index `0`), so the
    /// payload aggregate is never materialized into a temporary. A generic payload nevertheless
    /// carries its `Value` layout witness so physical lowering can calculate its case-specific
    /// offset and allocate indirect storage.
    pub fn variant(
        span: Location,
        tag: Ustr,
        t: Type,
        payload_ty: Type,
        storage: Option<VariantPayloadStorage>,
        storage_evidence: Option<mir::Value>,
        layout_witness: Option<mir::Value>,
    ) -> Self {
        assert_eq!(storage.is_none(), storage_evidence.is_some());
        let has_layout_witness = layout_witness.is_some();
        let mut operands = storage_evidence.into_iter().collect::<Vec<_>>();
        operands.extend(layout_witness);
        Operation {
            result_id: None,
            span,
            operands: operands.into_boxed_slice(),
            kind: OperationKind::Variant {
                tag,
                metadata: b(VariantMetadata { ty: t, payload_ty }),
                storage,
                has_layout_witness,
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

    /// Creates an `extract_tag` operation, which reads the semantic tag of the variant at the
    /// `variant` place and yields it as an opaque MIR `tag` value.
    ///
    /// The result is the *semantic* tag — the session-local interned identity a `VariantTag` pattern
    /// compares against — not the raw ABI field. The canonical layout stores a `u32` whose high bit
    /// records indirect payload storage (see `doc/abi.md`), so a backend reading that field owes the
    /// mask. The reference interpreter keeps the tag symbolically. A concrete backend resolves the
    /// symbol through the compilation session's tag table only when lowering this opaque value to
    /// the ABI's 31-bit numeric identity.
    pub fn extract_tag(span: Location, variant: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([variant]),
            kind: OperationKind::ExtractTag,
        }
    }

    /// Reads whether the active variant payload is stored through an owning pointer.
    ///
    /// This is a physical-MIR operation over the representation bit packed into the stored tag.
    /// Unlike [`Self::extract_tag`], its result is an ordinary materialized `bool` suitable for
    /// control flow inside generated payload addressors.
    pub fn extract_payload_indirection(span: Location, variant: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([variant]),
            kind: OperationKind::ExtractPayloadIndirection,
        }
    }

    /// Tests whether a physical place currently contains an initialized value.
    ///
    /// Dense executors implement this with the drop flag associated with the place. The operation
    /// lets physical lowering spell conditional cleanup as ordinary control flow without exposing
    /// the executor's flag storage layout in MIR.
    pub fn is_initialized(span: Location, place: mir::Value) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([place]),
            kind: OperationKind::IsInitialized,
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

    /// Creates a physical ownership transfer of one initialized `ty` value using an explicit byte
    /// extent. The source becomes absent and the previously absent destination becomes initialized.
    pub fn move_bytes(
        span: Location,
        ty: Type,
        source: mir::Value,
        destination: mir::Value,
        size: mir::Value,
    ) -> Self {
        Operation {
            result_id: None,
            span,
            operands: Box::new([source, destination, size]),
            kind: OperationKind::MoveBytes { ty },
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
    /// Optimizations may append hidden evidence captured by a resolved dictionary entry after it.
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
    /// as [`drop`](Self::drop)'s. Optimizations may append hidden evidence captured by a resolved
    /// dictionary entry after it. The destination takes on the drop obligation the copy creates.
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

/// Static types needed to lower a variant shell and its selected payload.
///
/// This is boxed in [`OperationKind::Variant`] so the uncommon pair does not enlarge every MIR
/// operation.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct VariantMetadata {
    pub(crate) ty: Type,
    pub(crate) payload_ty: Type,
}

/// Static product identity and the run-time member layouts carried by a `subfield` operation.
///
/// `layout_witness_tys` is positional against the evidence operands following the aggregate and
/// logical field index. It contains every direct member whose inline layout is not static in the
/// containing function.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ProductProjectionMetadata {
    pub(crate) aggregate_ty: Type,
    pub(crate) layout_witness_tys: Box<[Type]>,
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
    /// An explicitly sized run-time allocation whose base is interpreted as a pointer to
    /// `pointee`.
    RuntimeAlloc { pointee: Type },
    /// Pointer-only release of a run-time allocation.
    RuntimeDealloc,
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
    Subfield {
        ty: Type,
        /// True when this selects a variant's complete case payload rather than a product field.
        variant_payload: bool,
        /// True when operand 2 carries `Value<ty>` layout evidence.
        has_layout_witness: bool,
        /// Product identity and layout-evidence schema, when physical product layout applies.
        product: Option<B<ProductProjectionMetadata>>,
    },
    /// Project a place by a physical byte offset while retaining its allocation provenance.
    AddressOffset { ty: Type },
    /// Project a slot containing a place by a physical byte offset.
    AddressOffsetPlace { pointing_to: Type },
    /// Project a function entry place from a symbolic dictionary.
    DictEntry {
        entry_index: TraitDictionaryEntryIndex,
        ty: Type,
    },
    /// Close a trait dictionary definition over hidden evidence operands.
    BuildDictionary {
        definition: TraitDictionaryId,
        ty: Type,
    },
    /// Resolve a member function place from a symbolic subscript.
    SubscriptMember { mut_member: bool, ty: Type },
    /// Close symbolic subscript evidence over additional evidence operands.
    BuildSubscriptEvidence { ty: Type },
    /// Materialize closed subscript evidence as an owned first-class value.
    BuildSubscript { ty: Type },
    /// Deep-clone a first-class subscript's owned environment.
    CloneSubscriptEnv { ty: Type },
    /// Drop a first-class subscript's owned environment.
    DropSubscriptEnv,
    /// Borrow a callable member from a closed subscript environment.
    BorrowSubscriptMember { mut_member: bool, ty: Type },
    /// Construct a tagged variant shell whose payload is initialized separately.
    Variant {
        tag: Ustr,
        metadata: B<VariantMetadata>,
        /// `None` means operand 0 carries forwarded generic storage evidence.
        storage: Option<VariantPayloadStorage>,
        /// When true, the last operand carries `Value<payload_ty>` layout evidence.
        has_layout_witness: bool,
    },
    /// Construct a fresh array from `TrivialCopy` elements into a trailing destination place.
    BuildArray { element_ty: Type },
    /// Read a variant's semantic tag as an opaque MIR value.
    ExtractTag,
    /// Read the physical indirection bit of a variant's stored tag.
    ExtractPayloadIndirection,
    /// Read the physical initialization flag associated with a place.
    IsInitialized,
    /// Store a value into unoccupied place storage.
    Store,
    /// Mark place storage absent without semantic drop.
    Clear,
    /// Copy a statically sized `TrivialCopy` representation between places.
    Memcpy,
    /// Transfer ownership between places, optionally using a run-time layout witness.
    Move,
    /// Transfer ownership between places using an explicit physical byte extent.
    MoveBytes { ty: Type },
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
            | RuntimeAlloc { .. }
            | RuntimeDealloc
            | Call { .. }
            | Project { .. }
            | EndProject
            | CompareEqual
            | Load
            | Subfield { .. }
            | AddressOffset { .. }
            | AddressOffsetPlace { .. }
            | DictEntry { .. }
            | BuildDictionary { .. }
            | SubscriptMember { .. }
            | BuildSubscriptEvidence { .. }
            | BuildSubscript { .. }
            | CloneSubscriptEnv { .. }
            | DropSubscriptEnv
            | BorrowSubscriptMember { .. }
            | Variant { .. }
            | BuildArray { .. }
            | ExtractTag
            | ExtractPayloadIndirection
            | IsInitialized
            | Store
            | Clear
            | Memcpy
            | Move
            | MoveBytes { .. }
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
            | RuntimeAlloc { .. }
            | RuntimeDealloc
            | Call { .. }
            | Project { .. }
            | EndProject
            | CompareEqual
            | Load
            | Subfield { .. }
            | AddressOffset { .. }
            | AddressOffsetPlace { .. }
            | DictEntry { .. }
            | BuildDictionary { .. }
            | SubscriptMember { .. }
            | BuildSubscriptEvidence { .. }
            | BuildSubscript { .. }
            | CloneSubscriptEnv { .. }
            | DropSubscriptEnv
            | BorrowSubscriptMember { .. }
            | Variant { .. }
            | BuildArray { .. }
            | ExtractTag
            | ExtractPayloadIndirection
            | IsInitialized
            | Store
            | Clear
            | Memcpy
            | Move
            | MoveBytes { .. }
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

    /// A materialized pointer value to a type.
    MaterializedPointer(Box<OperationResult>),

    /// A callable borrowing a first-class subscript environment for one invocation.
    BorrowedCallable(Type),

    /// An opaque semantic variant-tag identity. It is compiler-internal, equality-comparable only,
    /// and has no Ferlium-expressible type.
    VariantTag,

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

    /// Returns the type of a materialized pointer to an instance of `pointee`.
    fn materialized_pointer_to(pointee: OperationResult) -> OperationResult {
        OperationResult::MaterializedPointer(Box::new(pointee))
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
            RuntimeAlloc { pointee } => {
                OperationResult::materialized_pointer_to(OperationResult::Lowered(*pointee))
            }
            Project { yielded: ty, .. }
            | Subfield { ty, .. }
            | AddressOffset { ty }
            | DictEntry { ty, .. }
            | SubscriptMember { ty, .. } => {
                OperationResult::pointer_to(OperationResult::Lowered(*ty))
            }
            BorrowSubscriptMember { ty, .. } => OperationResult::BorrowedCallable(*ty),
            AddressOffsetPlace { pointing_to } => OperationResult::pointer_to(
                OperationResult::pointer_to(OperationResult::Lowered(*pointing_to)),
            ),
            CompareEqual => OperationResult::Lowered(cached_primitive_ty!(bool)),
            Load => OperationResult::pointee_of(OperationResult::Same(whole.operands[0].clone())),
            BuildDictionary { ty, .. } | BuildSubscriptEvidence { ty } => {
                OperationResult::Lowered(*ty)
            }
            BuildSubscript { ty }
            | CloneSubscriptEnv { ty }
            | BuildClosure { ty, .. }
            | CloneClosureEnv { ty } => OperationResult::Lowered(*ty),
            Variant { metadata, .. } => OperationResult::Lowered(metadata.ty),
            ExtractTag => OperationResult::VariantTag,
            ExtractPayloadIndirection => OperationResult::Lowered(cached_primitive_ty!(bool)),
            IsInitialized => OperationResult::Lowered(cached_primitive_ty!(bool)),
            StackSave => OperationResult::StackMarker,
            Call { .. }
            | BuildArray { .. }
            | EndProject
            | Store
            | Clear
            | Memcpy
            | Move
            | MoveBytes { .. }
            | RuntimeDealloc
            | StackRestore
            | CheckCallDepth
            | CheckFuel
            | Clone { .. }
            | Drop { .. }
            | DropSubscriptEnv
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
            RuntimeAlloc { .. } => assert_eq!(
                whole.operands.len(),
                2,
                "runtime_alloc takes the byte size and alignment"
            ),
            RuntimeDealloc => assert_eq!(
                whole.operands.len(),
                1,
                "runtime_dealloc takes exactly the allocation address"
            ),
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
            Subfield {
                variant_payload,
                has_layout_witness,
                product,
                ..
            } => {
                assert!(
                    product.is_none() || (!*variant_payload && !*has_layout_witness),
                    "product and variant subfield metadata are mutually exclusive"
                );
                assert_eq!(
                    product.is_some(),
                    !*variant_payload,
                    "a product subfield names its aggregate, while a variant-payload subfield does not"
                );
                assert_eq!(
                    whole.operands.len(),
                    2 + usize::from(*has_layout_witness)
                        + product
                            .as_ref()
                            .map_or(0, |product| product.layout_witness_tys.len()),
                    "subfield takes the aggregate place, the int field-index value, and optional layout evidence"
                );
            }
            AddressOffset { .. } => assert_eq!(
                whole.operands.len(),
                2,
                "address_offset takes a base place and a materialized byte offset"
            ),
            AddressOffsetPlace { .. } => assert_eq!(
                whole.operands.len(),
                2,
                "address_offset_place takes a base place and a materialized byte offset"
            ),
            DictEntry { .. } => assert_eq!(
                whole.operands.len(),
                1,
                "dict_entry takes exactly the symbolic dictionary operand"
            ),
            BuildDictionary { .. } => assert!(
                !whole.operands.is_empty(),
                "build_dictionary is only needed for a definition with captures"
            ),
            SubscriptMember { .. } => assert_eq!(
                whole.operands.len(),
                1,
                "subscript_member takes exactly the symbolic subscript operand"
            ),
            BuildSubscriptEvidence { .. } => assert!(
                !whole.operands.is_empty(),
                "build_subscript_evidence takes a base plus its evidence captures"
            ),
            BuildSubscript { .. } => assert_eq!(
                whole.operands.len(),
                1,
                "build_subscript takes exactly one closed subscript-evidence operand"
            ),
            CloneSubscriptEnv { .. } => assert_eq!(
                whole.operands.len(),
                1,
                "clone_subscript_env takes exactly the source subscript place"
            ),
            DropSubscriptEnv => assert_eq!(
                whole.operands.len(),
                1,
                "drop_subscript_env takes exactly the target subscript place"
            ),
            BorrowSubscriptMember { .. } => assert_eq!(
                whole.operands.len(),
                1,
                "borrow_subscript_member takes exactly one closed subscript operand"
            ),
            Variant {
                storage,
                has_layout_witness,
                ..
            } => assert_eq!(
                whole.operands.len(),
                usize::from(storage.is_none()) + usize::from(*has_layout_witness),
                "variant takes storage evidence when dynamic and payload layout evidence when required"
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
            ExtractPayloadIndirection => assert_eq!(
                whole.operands.len(),
                1,
                "extract_payload_indirection takes exactly the variant place"
            ),
            IsInitialized => assert_eq!(
                whole.operands.len(),
                1,
                "is_initialized takes exactly one place",
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
            MoveBytes { .. } => assert_eq!(
                whole.operands.len(),
                3,
                "move_bytes takes source, destination and byte size"
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
            Drop { .. } => assert!(
                whole.operands.len() >= 2,
                "drop takes the target place, the Value::drop callee, and optional hidden evidence"
            ),
            Clone { .. } => assert!(
                whole.operands.len() >= 3,
                "clone takes the source and destination places, the Value::clone callee, and optional hidden evidence"
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
            RuntimeAlloc { pointee } => write!(
                f,
                "runtime_alloc {} size {} align {}",
                pointee.format_with(env),
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env)
            ),
            RuntimeDealloc => write!(f, "runtime_dealloc {}", whole.operands[0].format_with(env)),
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
            Subfield {
                variant_payload,
                has_layout_witness,
                product,
                ..
            } => {
                if *variant_payload {
                    write!(
                        f,
                        "variant_payload from {}",
                        whole.operands[0].format_with(env)
                    )?;
                } else {
                    write!(
                        f,
                        "subfield {} from {}",
                        whole.operands[1].format_with(env),
                        whole.operands[0].format_with(env)
                    )?;
                }
                if *has_layout_witness {
                    write!(f, " via {}", whole.operands[2].format_with(env))?;
                }
                if let Some(product) = product {
                    for witness in &whole.operands[2..2 + product.layout_witness_tys.len()] {
                        write!(f, " via {}", witness.format_with(env))?;
                    }
                }
                Ok(())
            }
            AddressOffset { .. } => write!(
                f,
                "address_offset {} by {}",
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env)
            ),
            AddressOffsetPlace { .. } => write!(
                f,
                "address_offset_place {} by {}",
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env)
            ),
            DictEntry { entry_index, .. } => write!(
                f,
                "dict_entry {} from {}",
                entry_index,
                whole.operands[0].format_with(env)
            ),
            BuildDictionary { definition, .. } => {
                write!(
                    f,
                    "build_dictionary dict(m{}:i{})",
                    definition.module_id, definition.impl_id
                )?;
                for capture in &whole.operands {
                    write!(f, " {}", capture.format_with(env))?;
                }
                Ok(())
            }
            SubscriptMember { mut_member, .. } => write!(
                f,
                "subscript_member {} from {}",
                if *mut_member { "mut" } else { "ref" },
                whole.operands[0].format_with(env)
            ),
            BuildSubscriptEvidence { .. } => {
                write!(
                    f,
                    "build_subscript_evidence {}",
                    whole.operands[0].format_with(env)
                )?;
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
            BuildSubscript { .. } => {
                write!(f, "build_subscript {}", whole.operands[0].format_with(env))
            }
            CloneSubscriptEnv { .. } => write!(
                f,
                "clone_subscript_env {}",
                whole.operands[0].format_with(env)
            ),
            DropSubscriptEnv => write!(
                f,
                "drop_subscript_env {}",
                whole.operands[0].format_with(env)
            ),
            BorrowSubscriptMember { mut_member, .. } => write!(
                f,
                "borrow_subscript_member {} from {}",
                if *mut_member { "mut" } else { "ref" },
                whole.operands[0].format_with(env)
            ),
            Variant {
                tag,
                storage,
                has_layout_witness,
                ..
            } => {
                write!(f, "variant {tag}")?;
                let mut index = 0;
                if storage.is_none() {
                    write!(f, " storage via {}", whole.operands[index].format_with(env))?;
                    index += 1;
                }
                if *has_layout_witness {
                    write!(f, " layout via {}", whole.operands[index].format_with(env))?;
                }
                Ok(())
            }
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
            ExtractPayloadIndirection => write!(
                f,
                "extract_payload_indirection {}",
                whole.operands[0].format_with(env)
            ),
            IsInitialized => write!(f, "is_initialized {}", whole.operands[0].format_with(env)),
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
            MoveBytes { ty } => write!(
                f,
                "move_bytes {} {} to {} size {}",
                ty.format_with(env),
                whole.operands[0].format_with(env),
                whole.operands[1].format_with(env),
                whole.operands[2].format_with(env)
            ),
            StackSave => write!(f, "stack_save"),
            StackRestore => write!(f, "stack_restore {}", whole.operands[0].format_with(env)),
            CheckCallDepth => write!(f, "check_call_depth"),
            CheckFuel => write!(f, "check_fuel"),
            // The type is printed bare, as `alloca` prints its own: it is what decides whether the
            // semantic form is still needed after substitution, and for a dictionary-dispatched
            // callee it is not recoverable from the rest of the line.
            Drop { ty } => {
                write!(
                    f,
                    "drop {} {} via {}",
                    ty.format_with(env),
                    whole.operands[0].format_with(env),
                    whole.operands[1].format_with(env)
                )?;
                format_hidden_evidence(f, &whole.operands[2..], env)
            }
            Clone { ty } => {
                write!(
                    f,
                    "clone {} {} to {} via {}",
                    ty.format_with(env),
                    whole.operands[0].format_with(env),
                    whole.operands[1].format_with(env),
                    whole.operands[2].format_with(env)
                )?;
                format_hidden_evidence(f, &whole.operands[3..], env)
            }
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

fn format_hidden_evidence(
    f: &mut fmt::Formatter<'_>,
    evidence: &[mir::Value],
    env: &ModuleEnv<'_>,
) -> fmt::Result {
    if evidence.is_empty() {
        return Ok(());
    }
    write!(f, " with (")?;
    for (index, operand) in evidence.iter().enumerate() {
        if index != 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", operand.format_with(env))?;
    }
    write!(f, ")")
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

    use super::{Operation, OperationKind, OperationResult};
    use crate::{
        CompilerSession, Location,
        format::FormatWith,
        hir::value::VariantPayloadStorage,
        mir::{ParameterId, Value},
        types::r#type::{SubscriptType, Type},
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
            Type::unit(),
            Some(VariantPayloadStorage::Inline),
            None,
            None,
        );

        assert_eq!(operation.format_with(&env).to_string(), "variant Some");
    }

    #[test]
    fn runtime_allocation_result_is_a_typed_pointer_independent_of_its_extent() {
        let operation = Operation::runtime_alloc(
            Location::new_synthesized(),
            Type::unit(),
            Value::Parameter(ParameterId::new(0)),
            Value::Parameter(ParameterId::new(1)),
        );

        assert_eq!(
            operation.result(),
            OperationResult::MaterializedPointer(Box::new(OperationResult::Lowered(Type::unit())))
        );
        assert!(operation.result_requires_consuming_use());
    }

    #[test]
    fn first_class_subscript_construction_and_clone_produce_owned_values() {
        let span = Location::new_synthesized();
        let ty = Type::subscript_type(SubscriptType::new(vec![], Type::unit(), None, None));
        let source = Value::Parameter(ParameterId::new(0));

        let build = Operation::build_subscript(span, source.clone(), ty);
        let clone = Operation::clone_subscript_env(span, source.clone(), ty);
        let drop = Operation::drop_subscript_env(span, source);

        assert!(build.result_requires_consuming_use());
        assert!(clone.result_requires_consuming_use());
        assert_eq!(drop.result(), OperationResult::Nothing);
    }
}
