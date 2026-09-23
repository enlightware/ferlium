// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! What a MIR value *is*: a place, a materialized Ferlium value, an opaque tag, or compile-time
//! evidence.
//!
//! [`mir::Value::Register`] deliberately does not encode this — an operand slot may accept more
//! than one role (`comp_eq` reads a place, a Ferlium value, or an opaque tag), and a uniform flat
//! operand array is what keeps alpha-equivalence, hash-consing and operand substitution generic
//! across passes. The role is instead a property of the *defining* operation, recovered here.
//!
//! Almost every [`OperationResult`] is self-contained. The exception is `Load`, whose result is
//! `Pointee(Same(operands[0]))`: it reads one operand's role. That single step is why this module
//! offers two entry points rather than a pure function per operation.
//!
//! - [`ValueRoles::for_signature`] plus [`ValueRoles::define`] is the incremental form, used while
//!   *lowering*. It relies on operands being defined before the operation that reads them is
//!   appended, which [`FunctionBuilder`](crate::mir::builder::FunctionBuilder) guarantees by
//!   handing each result back from the append that created it. It exists to report a bad operand
//!   at the exact insertion point, so it is debug-and-test only.
//! - [`ValueRoles::derive`] is the batch form, for a finished function. It resolves each role on
//!   demand so that *block* order — which MIR does not constrain to be a definition order — cannot
//!   matter.
//!
//! Both share one resolver, so the two can never disagree.
//!
//! The checking entry points also guard physical artifacts in release builds.
//! [`check_function_operand_roles`] checks operand slots without a [`ModuleEnv`] or control-flow
//! dataflow and returns the derived roles for reuse. Physical verification and the semantic artifact
//! and snapshot boundaries run it before heavier analyses to diagnose the offending operand slot.

use std::{borrow::Cow, fmt};

use ustr::Ustr;

use crate::{
    containers::{B, b},
    format::FormatWith,
    mir::{
        self, Function, Operation, OperationKind, OperationResult, Parameter, ParameterKind,
        ValueId,
        site::{OperationIndex, OperationSite},
        terminator::TerminatorKind,
        value::{Constant, ConstantId, StaticEvidence},
    },
    module::{ModuleEnv, id::Id},
    std::math::int_type,
    types::r#type::{CallImplType, CallResultConvention, Type, TypeKind},
};

/// A type as MIR sees it: a lowered Ferlium type, or a pointer to one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MirType {
    Lowered(Type),
    Pointer(B<MirType>),
}

impl MirType {
    pub(crate) fn pointer_to(pointee: MirType) -> Self {
        Self::Pointer(b(pointee))
    }

    pub(crate) fn format(&self, env: &ModuleEnv<'_>) -> String {
        match self {
            Self::Lowered(ty) => ty.format_with(env).to_string(),
            Self::Pointer(pointee) => pointee.format_as_pointer_pointee(env),
        }
    }

    /// Formats `self` behind a pointer sigil, preserving the boundary between the MIR pointer and
    /// a lowered type whose own syntax has lower precedence.
    fn format_as_pointer_pointee(&self, env: &ModuleEnv<'_>) -> String {
        match self {
            Self::Lowered(ty) if lowered_type_needs_pointer_parentheses(*ty, env) => {
                format!("*({})", ty.format_with(env))
            }
            _ => format!("*{}", self.format(env)),
        }
    }

    /// Formats `self` after the `place` keyword, preserving the boundary between the place and a
    /// lowered type whose own syntax has lower precedence.
    fn format_as_place_pointee(&self, env: &ModuleEnv<'_>) -> String {
        match self {
            Self::Lowered(ty) if lowered_type_needs_pointer_parentheses(*ty, env) => {
                format!("({})", ty.format_with(env))
            }
            _ => self.format(env),
        }
    }

    pub(crate) fn is_fully_concrete(&self) -> bool {
        use crate::types::type_like::TypeLike;

        match self {
            Self::Lowered(ty) => ty.is_constant(),
            Self::Pointer(pointee) => pointee.is_fully_concrete(),
        }
    }
}

/// The role of a MIR value: what a reader of that value holds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ValueRole {
    Materialized(MirType),
    Place(MirType),
    /// An opaque semantic variant tag, not a Ferlium value or raw ABI tag word.
    VariantTag,
    Dictionary,
    Subscript,
    /// Opaque evidence selecting the inline or indirect representation of a variant payload.
    VariantPayloadStorage,
    Function,
    /// A callable paired with a borrow of its subscript environment.
    BorrowedCallable(Type),
    Pattern,
    StackMarker,
    /// A yielded place paired with the accessor contract whose slide must be ended exactly once.
    OpenProjection {
        yielded: Type,
        accessor: B<CallImplType>,
    },
}

impl ValueRole {
    /// The pointee type reached by reading through this value as a place, if it is one.
    pub(crate) fn place_pointee_type(&self) -> Option<MirType> {
        match self {
            Self::Place(ty) => Some(ty.clone()),
            Self::Materialized(MirType::Pointer(ty)) => Some((**ty).clone()),
            Self::OpenProjection { yielded, .. } => Some(MirType::Lowered(*yielded)),
            _ => None,
        }
    }

    /// Renders this role the way a definition site annotates it, `place int` for addressable
    /// storage holding an `int` and `int` for the value itself.
    pub(crate) fn annotation(&self, env: &ModuleEnv<'_>) -> String {
        match self {
            Self::Materialized(ty) => ty.format(env),
            Self::Place(ty) => format!("place {}", ty.format_as_place_pointee(env)),
            Self::VariantTag => "tag".to_string(),
            Self::Dictionary => "dict".to_string(),
            Self::Subscript => "subscript".to_string(),
            Self::VariantPayloadStorage => "layout".to_string(),
            Self::Function => "fn".to_string(),
            Self::BorrowedCallable(ty) => {
                format!("borrowed {}", ty.format_with(env))
            }
            Self::Pattern => "pattern".to_string(),
            Self::StackMarker => "stack".to_string(),
            Self::OpenProjection { yielded, .. } => {
                let yielded = MirType::Lowered(*yielded).format_as_place_pointee(env);
                format!("open place {yielded}")
            }
        }
    }
}

/// Whether a lowered type needs grouping when it follows MIR's prefix `*` pointer sigil.
fn lowered_type_needs_pointer_parentheses(ty: Type, env: &ModuleEnv<'_>) -> bool {
    if env.type_alias_name(ty).is_some() {
        return false;
    }
    matches!(
        &*ty.data(),
        TypeKind::Variant(_) | TypeKind::Function(_) | TypeKind::Subscript(_)
    )
}

/// The predicates used by operand checking, compiled with the checks themselves.
impl ValueRole {
    pub(crate) fn is_callee_operand(&self) -> bool {
        matches!(
            self,
            Self::Function
                | Self::BorrowedCallable(_)
                | Self::Place(_)
                | Self::Materialized(MirType::Pointer(_))
        )
    }

    /// Whether this value can be used where a place is expected.
    ///
    /// A *materialized pointer* qualifies: loading an `alloca_place` slot yields the pointer it
    /// holds as a value, and that pointer is a perfectly good place to read through. This is the
    /// single reason a role has to carry its [`MirType`] rather than just a discriminant.
    pub(crate) fn is_place_operand(&self) -> bool {
        matches!(
            self,
            Self::Place(_) | Self::Materialized(MirType::Pointer(_)) | Self::OpenProjection { .. }
        )
    }

    pub(crate) fn is_materialized(&self) -> bool {
        matches!(
            self,
            Self::Materialized(_) | Self::Function | Self::Subscript
        )
    }

    pub(crate) fn is_evidence(&self) -> bool {
        matches!(
            self,
            Self::Dictionary | Self::Subscript | Self::VariantPayloadStorage | Self::Place(_)
        )
    }

    /// The type this role exposes, if it has one.
    pub(crate) fn materialized_type(&self) -> Option<&MirType> {
        match self {
            Self::Materialized(ty) => Some(ty),
            _ => None,
        }
    }

    /// The type this role wraps, whether it is held directly or pointed at.
    pub(crate) fn inner_type(&self) -> Option<&MirType> {
        match self {
            Self::Materialized(ty) | Self::Place(ty) => Some(ty),
            _ => None,
        }
    }
}

/// The role of every value in one MIR function.
///
/// Registers are stored densely by [`mir::ValueId`]; every other [`mir::Value`] form is answered
/// from the signature, the constant pool, or the value itself.
#[derive(Clone, Debug, Default)]
pub(crate) struct ValueRoles {
    parameters: Vec<ValueRole>,
    /// Indexed by [`mir::ValueId`], and sparse: dropping an operation does not renumber the ones
    /// that remain, so an optimized body leaves ids nothing defines.
    registers: Vec<Option<ValueRole>>,
    /// Registers whose result reads their own role, directly or through a chain. Empty in any
    /// well-formed function; kept so the diagnostic can say *why* a role is missing.
    cyclic: Vec<ValueId>,
}

impl ValueRoles {
    /// Number of slots in the sparse register-role table.
    #[cfg(target_arch = "wasm32")]
    pub(crate) fn register_count(&self) -> usize {
        self.registers.len()
    }

    /// The roles a signature fixes, with no register defined yet.
    pub(crate) fn for_signature(
        parameters: &[Parameter],
        result_convention: CallResultConvention,
    ) -> Self {
        Self {
            parameters: parameters
                .iter()
                .map(|parameter| parameter_role(parameter, result_convention))
                .collect(),
            registers: Vec::new(),
            cyclic: Vec::new(),
        }
    }

    /// Appends the role a newly declared parameter takes.
    #[cfg(any(debug_assertions, test))]
    pub(crate) fn push_parameter(
        &mut self,
        parameter: &Parameter,
        result_convention: CallResultConvention,
    ) {
        self.parameters
            .push(parameter_role(parameter, result_convention));
    }

    /// Records the role of `operation`'s result as it is inserted.
    #[cfg(any(debug_assertions, test))]
    pub(crate) fn define(
        &mut self,
        func_name: Ustr,
        value_id: ValueId,
        operation: &Operation,
        result: OperationResult,
        constants: &[Constant],
    ) {
        let role = self
            .compute(operation, result, constants)
            .unwrap_or_else(|| {
                panic!(
                    "MIR function `{func_name}`: value {value_id} is defined by an operation whose \
                 result reads an operand with no role yet"
                )
            });
        let index = value_id.as_index();
        if self.registers.len() <= index {
            self.registers.resize(index + 1, None);
        }
        assert!(
            self.registers[index].is_none(),
            "MIR function `{func_name}`: value {value_id} has more than one definition"
        );
        self.registers[index] = Some(role);
    }

    /// Derives every role in a finished function.
    ///
    /// Total by construction: a register whose role cannot be resolved — an undefined operand, a
    /// result cycle, a value defined twice — is left unset rather than panicking, so that a
    /// renderer can annotate a malformed function instead of aborting inside the diagnostic that
    /// was about to report it.
    pub(crate) fn derive(func: &Function) -> Self {
        let mut roles = Self::for_signature(func.parameters(), func.result_convention());

        fn define<'a>(definitions: &mut Vec<Option<&'a Operation>>, operation: &'a Operation) {
            let Some(id) = operation.result_id() else {
                return;
            };
            let index = id.as_index();
            if definitions.len() <= index {
                definitions.resize(index + 1, None);
            }
            definitions[index] = Some(operation);
        }

        let mut definitions: Vec<Option<&Operation>> = Vec::new();
        for block in func.blocks() {
            let block = func.block(block);
            for operation in block.operations() {
                define(&mut definitions, operation);
            }
            if let TerminatorKind::Invoke { operation, .. } = &block.terminator().kind {
                define(&mut definitions, operation);
            }
        }

        roles.registers.resize(definitions.len(), None);
        let mut resolving = Vec::new();
        for index in 0..definitions.len() {
            roles.ensure(
                ValueId::from_index(index),
                &definitions,
                func.constants(),
                &mut resolving,
            );
        }
        roles
    }

    /// Resolves one register's role, and every role its result reads, into the table.
    fn ensure(
        &mut self,
        value_id: ValueId,
        definitions: &[Option<&Operation>],
        constants: &[Constant],
        resolving: &mut Vec<ValueId>,
    ) {
        let index = value_id.as_index();
        if self.registers.get(index).is_some_and(Option::is_some) {
            return;
        }
        if resolving.contains(&value_id) {
            self.cyclic.push(value_id);
            return;
        }
        let Some(Some(operation)) = definitions.get(index) else {
            return;
        };
        let result = operation.result();
        if let Some(dependency) = result_dependency(&result) {
            resolving.push(value_id);
            self.ensure(dependency, definitions, constants, resolving);
            resolving.pop();
        }
        if let Some(role) = self.compute(operation, result, constants) {
            self.registers[index] = Some(role);
        }
    }

    /// The role `operation`'s result takes, or `None` if an operand it reads has none yet.
    ///
    /// `result` is passed in rather than recomputed: [`Operation::result`] boxes for a pointer or
    /// pointee result, and every caller already needed it.
    fn compute(
        &self,
        operation: &Operation,
        result: OperationResult,
        constants: &[Constant],
    ) -> Option<ValueRole> {
        if let OperationKind::Project { yielded, ty } = &operation.kind {
            return Some(ValueRole::OpenProjection {
                yielded: *yielded,
                accessor: ty.clone(),
            });
        }
        if matches!(operation.kind, OperationKind::BuildDictionary { .. }) {
            return Some(ValueRole::Dictionary);
        }
        if matches!(operation.kind, OperationKind::BuildSubscriptEvidence { .. }) {
            return Some(ValueRole::Subscript);
        }
        self.resolve_result(result, constants)
    }

    fn resolve_result(&self, result: OperationResult, constants: &[Constant]) -> Option<ValueRole> {
        Some(match result {
            OperationResult::Lowered(ty) => ValueRole::Materialized(MirType::Lowered(ty)),
            OperationResult::Pointer(pointee) => {
                ValueRole::Place(self.resolve_result_type(*pointee, constants)?)
            }
            OperationResult::MaterializedPointer(pointee) => ValueRole::Materialized(
                MirType::pointer_to(self.resolve_result_type(*pointee, constants)?),
            ),
            OperationResult::BorrowedCallable(ty) => ValueRole::BorrowedCallable(ty),
            OperationResult::Pointee(pointer) => match self.resolve_result(*pointer, constants)? {
                ValueRole::Place(ty) => ValueRole::Materialized(ty),
                ValueRole::Materialized(MirType::Pointer(ty)) => ValueRole::Materialized(*ty),
                ValueRole::OpenProjection { yielded, .. } => {
                    ValueRole::Materialized(MirType::Lowered(yielded))
                }
                other => panic!("`Pointee` result refers to non-place role {other:?}"),
            },
            OperationResult::Same(value) => self.get(&value, constants)?.into_owned(),
            OperationResult::VariantTag => ValueRole::VariantTag,
            OperationResult::StackMarker => ValueRole::StackMarker,
            OperationResult::Nothing => panic!("result-less operation was given a result id"),
        })
    }

    fn resolve_result_type(
        &self,
        result: OperationResult,
        constants: &[Constant],
    ) -> Option<MirType> {
        Some(match result {
            OperationResult::Lowered(ty) => MirType::Lowered(ty),
            OperationResult::Pointer(inner) => {
                MirType::pointer_to(self.resolve_result_type(*inner, constants)?)
            }
            OperationResult::MaterializedPointer(inner) => {
                MirType::pointer_to(self.resolve_result_type(*inner, constants)?)
            }
            OperationResult::Same(value) => match self.get(&value, constants)?.into_owned() {
                ValueRole::Materialized(ty) | ValueRole::Place(ty) => ty,
                ValueRole::OpenProjection { yielded, .. } => MirType::Lowered(yielded),
                other => panic!("type requested for non-typed role {other:?}"),
            },
            OperationResult::Pointee(pointer) => match self.resolve_result(*pointer, constants)? {
                ValueRole::Place(ty) => ty,
                ValueRole::Materialized(MirType::Pointer(ty)) => *ty,
                ValueRole::OpenProjection { yielded, .. } => MirType::Lowered(yielded),
                other => panic!("pointee type requested from {other:?}"),
            },
            OperationResult::VariantTag
            | OperationResult::BorrowedCallable(_)
            | OperationResult::StackMarker
            | OperationResult::Nothing => {
                panic!("non-value result used as a value type")
            }
        })
    }

    /// The role of `value`, or `None` if it is a register whose role could not be resolved.
    ///
    /// Borrowed where the table already holds the role, which is the common case and the one on
    /// the checking path; only the roles a `Value` implies by itself are constructed here.
    pub(crate) fn get(
        &self,
        value: &mir::Value,
        constants: &[Constant],
    ) -> Option<Cow<'_, ValueRole>> {
        Some(match value {
            mir::Value::Constant(id) => Cow::Owned(ValueRole::Materialized(MirType::Lowered(
                constant_ty(constants, *id),
            ))),
            mir::Value::Dictionary(_) => Cow::Owned(ValueRole::Dictionary),
            mir::Value::Subscript(_) => Cow::Owned(ValueRole::Subscript),
            mir::Value::Evidence(evidence) => Cow::Owned(match &**evidence {
                StaticEvidence::Dictionary { .. } => ValueRole::Dictionary,
                StaticEvidence::Subscript { .. } => ValueRole::Subscript,
                StaticEvidence::VariantPayloadStorage(_) => ValueRole::VariantPayloadStorage,
            }),
            mir::Value::Function(_) => Cow::Owned(ValueRole::Function),
            mir::Value::Pattern(_) => Cow::Owned(ValueRole::Pattern),
            mir::Value::Parameter(id) => Cow::Borrowed(self.parameters.get(id.as_index())?),
            mir::Value::Register(id) => Cow::Borrowed(self.registers.get(id.as_index())?.as_ref()?),
        })
    }
}

/// Diagnostics used only by the operand checks.
impl ValueRoles {
    /// Whether `value_id` was left unresolved because its result reads itself.
    pub(crate) fn is_cyclic(&self, value_id: ValueId) -> bool {
        self.cyclic.contains(&value_id)
    }

    /// The role of `value`, panicking with `func_name` in the message if there is none.
    pub(crate) fn expect(
        &self,
        func_name: Ustr,
        value: &mir::Value,
        constants: &[Constant],
    ) -> Cow<'_, ValueRole> {
        self.get(value, constants).unwrap_or_else(|| {
            if let mir::Value::Register(id) = value
                && self.is_cyclic(*id)
            {
                panic!("MIR function `{func_name}`: value {id} takes its role from itself");
            }
            panic!("MIR function `{func_name}`: undefined operand {value}")
        })
    }
}

fn constant_ty(constants: &[Constant], id: ConstantId) -> Type {
    constants[id.as_index()].ty
}

fn parameter_role(parameter: &Parameter, result_convention: CallResultConvention) -> ValueRole {
    let ty = parameter.ty;
    match parameter.kind {
        ParameterKind::Dictionary => ValueRole::Dictionary,
        ParameterKind::Parameter(_) | ParameterKind::Owned => {
            ValueRole::Place(MirType::Lowered(ty))
        }
        ParameterKind::Return if result_convention.returns_place() => {
            ValueRole::Place(MirType::pointer_to(MirType::Lowered(ty)))
        }
        ParameterKind::Return => ValueRole::Place(MirType::Lowered(ty)),
    }
}

/// The register whose role `result` reads, if any.
///
/// A result nests one child per level and ends in at most one `Same`, so there is never more
/// than one.
fn result_dependency(result: &OperationResult) -> Option<ValueId> {
    match result {
        OperationResult::Same(mir::Value::Register(value_id)) => Some(*value_id),
        OperationResult::Pointee(inner)
        | OperationResult::Pointer(inner)
        | OperationResult::MaterializedPointer(inner) => result_dependency(inner),
        _ => None,
    }
}

/// Checks the role each operand slot of `operation` requires.
///
/// This is the role half of MIR verification, split out so that lowering can run it at insertion
/// in every build. It deliberately checks only what roles alone decide; representation compatibility
/// needs a [`ModuleEnv`] and stays in [`verify`](crate::mir::verify).
pub(crate) fn check_operand_roles(
    roles: &ValueRoles,
    func_name: Ustr,
    at: &dyn fmt::Display,
    operation: &Operation,
    constants: &[Constant],
) {
    let operands = &operation.operands;
    let role = |index: usize| roles.expect(func_name, &operands[index], constants);
    let place = |index: usize| {
        let role = role(index);
        assert!(
            role.is_place_operand(),
            "MIR function `{func_name}` {at}: operand {index} must be a place, got {role:?}"
        );
    };
    let value = |index: usize| {
        let role = role(index);
        assert!(
            role.is_materialized() || role.materialized_type().is_some(),
            "MIR function `{func_name}` {at}: operand {index} must be a materialized value, got {role:?}"
        );
    };
    let evidence = |index: usize| {
        let role = role(index);
        assert!(
            role.is_evidence(),
            "MIR function `{func_name}` {at}: operand {index} must be evidence, got {role:?}"
        );
    };

    match &operation.kind {
        OperationKind::Alloca { .. } => {
            if !operands.is_empty() {
                evidence(0);
            }
        }
        OperationKind::RuntimeAlloc { .. } => {
            for index in 0..operands.len() {
                let role = role(index);
                assert!(
                    matches!(
                        &*role,
                        ValueRole::Materialized(MirType::Lowered(ty))
                            if *ty == int_type()
                    ),
                    "MIR function `{func_name}` {at}: runtime_alloc operand {index} must be a materialized int, got {role:?}"
                );
            }
        }
        OperationKind::RuntimeDealloc => {
            let role = role(0);
            let allocation_address = matches!(
                &*role,
                ValueRole::Materialized(MirType::Pointer(pointee))
                    if matches!(&**pointee, MirType::Lowered(_))
            );
            assert!(
                allocation_address,
                "MIR function `{func_name}` {at}: runtime_dealloc requires a materialized allocation pointer, got {role:?}"
            );
        }
        OperationKind::Variant {
            storage,
            has_layout_witness,
            ..
        } => {
            let mut index = 0;
            if storage.is_none() {
                evidence(index);
                index += 1;
            }
            if *has_layout_witness {
                evidence(index);
            }
        }
        OperationKind::BuildArray { .. } => {
            let (_, elements) = operands
                .split_last()
                .expect("build_array has a trailing destination");
            for (index, element) in elements.iter().enumerate() {
                let role = roles.expect(func_name, element, constants);
                assert!(
                    matches!(*role, ValueRole::Place(_) | ValueRole::Materialized(_)),
                    "MIR function `{func_name}` {at}: build_array element operand {index} must be \
                     a value or place, got {role:?}"
                );
            }
            place(operands.len() - 1);
        }
        OperationKind::AllocaPlace { .. }
        | OperationKind::StackSave
        | OperationKind::CheckCallDepth
        | OperationKind::CheckFuel => {}
        OperationKind::Call { ty, .. } | OperationKind::Project { ty, .. } => {
            let visible_start = operands
                .len()
                .checked_sub(
                    ty.fn_ty.args.len()
                        + usize::from(
                            !matches!(operation.kind, OperationKind::Project { .. })
                                && ty.result_convention.has_result_place(),
                        ),
                )
                .filter(|start| *start >= 1)
                .unwrap_or_else(|| {
                    panic!(
                        "MIR function `{func_name}` {at}: too few operands for the call-site type"
                    )
                });
            let callee = role(0);
            assert!(
                callee.is_callee_operand(),
                "MIR function `{func_name}` {at}: callee must be a function or function place, \
                 got {callee:?}"
            );
            for index in 1..visible_start {
                evidence(index);
            }
            for offset in 0..ty.fn_ty.args.len() {
                place(visible_start + offset);
            }
            if matches!(operation.kind, OperationKind::Call { .. })
                && ty.result_convention.has_result_place()
            {
                let result = role(operands.len() - 1);
                assert!(
                    result.is_place_operand(),
                    "MIR function `{func_name}` {at}: the trailing call result operand must be a \
                     place, got {result:?}"
                );
            }
        }
        OperationKind::EndProject => {
            let role = role(0);
            assert!(
                matches!(*role, ValueRole::OpenProjection { .. }),
                "MIR function `{func_name}` {at}: end_project requires an open projection, got \
                 {role:?}"
            );
        }
        OperationKind::ExtractTag
        | OperationKind::ExtractPayloadIndirection
        | OperationKind::IsInitialized
        | OperationKind::Clear
        | OperationKind::DropSubscriptEnv
        | OperationKind::CloneSubscriptEnv { .. }
        | OperationKind::DropClosureEnv
        | OperationKind::CloneClosureEnv { .. } => place(0),
        OperationKind::CompareEqual => {
            let scrutinee = role(0);
            let pattern = role(1);
            assert!(
                matches!(*pattern, ValueRole::Pattern),
                "MIR function `{func_name}` {at}: comparison pattern must be compile-time data, \
                 got {pattern:?}"
            );
            let variant_pattern = match &operands[1] {
                mir::Value::Pattern(pattern) => pattern.as_variant_tag().is_some(),
                _ => false,
            };
            if variant_pattern {
                assert!(
                    matches!(*scrutinee, ValueRole::VariantTag),
                    "MIR function `{func_name}` {at}: a variant-tag pattern requires an opaque tag \
                     scrutinee, got {scrutinee:?}"
                );
            } else {
                assert!(
                    scrutinee.is_place_operand() || scrutinee.materialized_type().is_some(),
                    "MIR function `{func_name}` {at}: comparison scrutinee must be a place or \
                     Ferlium value, got {scrutinee:?}"
                );
            }
        }
        OperationKind::Load => place(0),
        OperationKind::Subfield {
            has_layout_witness,
            product,
            ..
        } => {
            place(0);
            value(1);
            if *has_layout_witness {
                evidence(2);
            }
            if let Some(product) = product {
                for index in 2..2 + product.layout_witness_tys.len() {
                    evidence(index);
                }
            }
        }
        OperationKind::AddressOffset { .. } | OperationKind::AddressOffsetPlace { .. } => {
            place(0);
            value(1);
            if operands.len() == 3 {
                value(2);
            }
        }
        OperationKind::DictEntry { .. }
        | OperationKind::SubscriptMember { .. }
        | OperationKind::BorrowSubscriptMember { .. } => evidence(0),
        OperationKind::BuildDictionary { .. } => {
            for index in 0..operands.len() {
                evidence(index);
            }
        }
        OperationKind::BuildSubscriptEvidence { .. } => {
            for index in 0..operands.len() {
                evidence(index);
            }
        }
        OperationKind::BuildSubscript { .. } => evidence(0),
        OperationKind::Store => {
            let stored = role(0);
            assert!(
                stored.materialized_type().is_some()
                    || stored.is_place_operand()
                    || stored.is_materialized(),
                "MIR function `{func_name}` {at}: stored operand must be a value or place \
                 pointer, got {stored:?}"
            );
            place(1);
        }
        OperationKind::Memcpy | OperationKind::Move | OperationKind::Replace => {
            place(0);
            place(1);
            if operands.len() == 3 {
                evidence(2);
            }
        }
        OperationKind::BlackBox { .. } => {
            place(0);
            if operands.len() == 2 {
                evidence(1);
            }
        }
        OperationKind::MoveBytes { .. } => {
            place(0);
            place(1);
            let size = role(2);
            assert!(
                matches!(&*size, ValueRole::Materialized(MirType::Lowered(ty)) if *ty == int_type()),
                "MIR function `{func_name}` {at}: move_bytes size must be a materialized int, got {size:?}"
            );
        }
        OperationKind::StackRestore => {
            let role = role(0);
            assert!(
                matches!(*role, ValueRole::StackMarker),
                "MIR function `{func_name}` {at}: stack_restore needs a stack marker, got {role:?}"
            );
        }
        OperationKind::Drop { .. } | OperationKind::DropInitialized { .. } => {
            place(0);
            let callee = role(1);
            assert!(
                matches!(*callee, ValueRole::Function | ValueRole::Place(_)),
                "MIR function `{func_name}` {at}: drop callee must be a function or function \
                 place, got {callee:?}"
            );
            for index in 2..operands.len() {
                evidence(index);
            }
        }
        OperationKind::Clone { .. } => {
            place(0);
            place(1);
            let callee = role(2);
            assert!(
                matches!(*callee, ValueRole::Function | ValueRole::Place(_)),
                "MIR function `{func_name}` {at}: clone callee must be a function or function \
                 place, got {callee:?}"
            );
            for index in 3..operands.len() {
                evidence(index);
            }
        }
        OperationKind::BuildClosure {
            num_hidden_dicts,
            has_env_dict,
            ..
        } => {
            for index in 0..*num_hidden_dicts as usize {
                evidence(index);
            }
            let captures_end = operands.len() - usize::from(*has_env_dict);
            for index in *num_hidden_dicts as usize..captures_end {
                place(index);
            }
            if *has_env_dict {
                evidence(captures_end);
            }
        }
    }
}

/// Checks the role each operand slot of a terminator requires. See [`check_operand_roles`].
pub(crate) fn check_terminator_operand_roles(
    roles: &ValueRoles,
    func_name: Ustr,
    at: &dyn fmt::Display,
    terminator: &TerminatorKind,
    constants: &[Constant],
) {
    match terminator {
        TerminatorKind::CondBr { condition, .. } => {
            let role = roles.expect(func_name, condition, constants);
            assert!(
                role.is_materialized() || role.materialized_type().is_some(),
                "MIR function `{func_name}` {at}: branch condition must be a materialized value, \
                 got {role:?}"
            );
        }
        TerminatorKind::SwitchVariant { tag, .. } => {
            let role = roles.expect(func_name, tag, constants);
            assert!(
                matches!(*role, ValueRole::VariantTag),
                "MIR function `{func_name}` {at}: switch_variant operand must be an opaque tag, \
                 got {role:?}"
            );
        }
        TerminatorKind::Yield { place, .. } => {
            let role = roles.expect(func_name, place, constants);
            assert!(
                role.is_place_operand(),
                "MIR function `{func_name}` {at}: yielded operand must be a place, got {role:?}"
            );
        }
        TerminatorKind::Invoke { operation, .. } => {
            check_operand_roles(roles, func_name, at, operation, constants)
        }
        TerminatorKind::Goto { .. }
        | TerminatorKind::Return
        | TerminatorKind::PropagateError
        | TerminatorKind::FailureDuringCleanup
        | TerminatorKind::InvariantFailure { .. } => {}
    }
}

/// Checks every operand slot in a whole function against the role it requires.
///
/// The role half of verification over a finished body. Unlike
/// [`verify_function`](crate::mir::verify::verify_function) this needs no [`ModuleEnv`] or control-flow
/// dataflow — one walk over the operations after deriving roles — so it runs before the heavier checks.
///
/// Editing has no single insertion point to check at:
/// [`block_mut`](crate::mir::edit::FunctionEdit::block_mut) hands a pass raw access to a block's
/// operations. Checking the finished body instead covers every rewrite, including those.
/// Returns the derived roles so subsequent verification of the unchanged body can reuse them.
pub(crate) fn check_function_operand_roles(func: &Function) -> ValueRoles {
    let roles = ValueRoles::derive(func);
    let constants = func.constants();
    for block in func.blocks() {
        let operations = func.block(block).operations();
        for (index, operation) in operations.iter().enumerate() {
            let at = OperationSite {
                block,
                index: OperationIndex::from_index(index),
            };
            check_operand_roles(&roles, func.name, &at, operation, constants);
        }
        let at = OperationSite {
            block,
            index: OperationIndex::from_index(operations.len()),
        };
        check_terminator_operand_roles(
            &roles,
            func.name,
            &at,
            &func.block(block).terminator().kind,
            constants,
        );
    }
    roles
}

#[cfg(test)]
mod tests {
    use ustr::ustr;

    use crate::{
        Location,
        mir::{Operation, Value, builder::FunctionBuilder, value::StaticEvidence},
        module::{LocalImplId, LocalSubscriptId, ModuleId, SubscriptId, TraitDictionaryId},
        std::math::int_type,
        types::r#type::Type,
    };

    #[test]
    fn variant_payload_storage_constant_is_valid_dictionary_capture_evidence() {
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("layout_capture".into(), Default::default());
        let block = builder.add_block();
        let definition = TraitDictionaryId::new(ModuleId::new(0), LocalImplId::new(0));
        let capture = Value::Evidence(Box::new(StaticEvidence::VariantPayloadStorage(true)));

        builder.append_operation(
            block,
            Operation::build_dictionary(span, definition, vec![capture], int_type()),
        );
    }

    #[test]
    #[should_panic(expected = "stored operand must be a value or place pointer, got VariantTag")]
    fn opaque_variant_tag_cannot_be_stored_as_a_ferlium_integer() {
        let span = Location::new_synthesized();
        let tag = ustr("Some");
        let variant_ty = Type::variant([(tag, Type::unit())]);
        let mut builder = FunctionBuilder::new("bad_tag_store".into(), Default::default());
        let block = builder.add_block();
        let variant = builder
            .append_operation(block, Operation::alloca(span, variant_ty))
            .unwrap();
        let extracted = builder
            .append_operation(block, Operation::extract_tag(span, variant))
            .unwrap();
        let integer = builder
            .append_operation(block, Operation::alloca(span, int_type()))
            .unwrap();

        builder.append_operation(block, Operation::store(span, extracted, integer));
    }

    #[test]
    #[should_panic(
        expected = "stored operand must be a value or place pointer, got BorrowedCallable"
    )]
    fn borrowed_subscript_member_cannot_escape_into_storage() {
        let span = Location::new_synthesized();
        let mut builder =
            FunctionBuilder::new("bad_borrowed_callable_store".into(), Default::default());
        let block = builder.add_block();
        let borrowed = builder
            .append_operation(
                block,
                Operation::borrow_subscript_member(
                    span,
                    Value::Subscript(SubscriptId::new(ModuleId::new(0), LocalSubscriptId::new(0))),
                    false,
                    Type::unit(),
                ),
            )
            .unwrap();
        let destination = builder
            .append_operation(block, Operation::alloca(span, Type::unit()))
            .unwrap();

        builder.append_operation(block, Operation::store(span, borrowed, destination));
    }
}
