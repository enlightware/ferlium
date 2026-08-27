// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Physical MIR lowering and readiness verification.

use std::fmt;

use rustc_hash::FxHashMap;
use ustr::Ustr;

use crate::{
    Location,
    compiler::MirArtifacts,
    hir::{dictionary::DictionaryReq, function::ArgConvention, value::LiteralValue},
    mir::{
        self, Function, Operation, OperationKind, ParameterKind, Value,
        builder::FunctionBuilder,
        edit::FunctionEdit,
        pass::known_callee::KnownCallees,
        terminator::{Terminator, TerminatorKind},
    },
    module::{FunctionId, LocalFunctionId, ModuleEnv, ModuleId, ProjectionIndex, id::Id},
    std::{
        core_traits_names::VALUE_TRAIT_NAME,
        math::int_type,
        ordering::{ORDERING_EQUAL, ORDERING_GREATER},
        value::{
            ProductLayoutOrder, ProductLayoutSpec, ProductMemberLayout, ProductMemberStorage,
            VALUE_ALIGN_ASSOC_CONST_INDEX, VALUE_SIZE_ASSOC_CONST_INDEX, product_layout_spec,
            value_layout_getter_entry,
        },
    },
    types::{
        effects::no_effects,
        r#trait::TraitAssociatedConstIndex,
        r#type::{CallImplType, CallResultConvention, FnType, Type},
    },
};

/// A physical-lowering or readiness failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BackendReadinessError {
    InvalidPhysicalEntry {
        owner: FunctionId,
        target: FunctionId,
    },
    UnresolvedPhysicalOperation {
        function: FunctionId,
        operation: &'static str,
    },
    InvalidProductProjection {
        function: FunctionId,
    },
    UnsupportedIndirectProductMember {
        function: FunctionId,
    },
    InvalidPhysicalCall {
        owner: FunctionId,
        target: FunctionId,
        expected: usize,
        actual: usize,
    },
}

impl fmt::Display for BackendReadinessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPhysicalEntry { owner, target } => write!(
                f,
                "physical entry m{}:f{} refers to unavailable entry m{}:f{}",
                owner.module, owner.function, target.module, target.function
            ),
            Self::UnresolvedPhysicalOperation {
                function,
                operation,
            } => write!(
                f,
                "physical entry m{}:f{} retains unresolved `{operation}`",
                function.module, function.function
            ),
            Self::InvalidProductProjection { function } => write!(
                f,
                "physical entry m{}:f{} contains an invalid product projection",
                function.module, function.function
            ),
            Self::UnsupportedIndirectProductMember { function } => write!(
                f,
                "physical entry m{}:f{} projects an indirect product member before its ownership operations have been lowered",
                function.module, function.function
            ),
            Self::InvalidPhysicalCall {
                owner,
                target,
                expected,
                actual,
            } => write!(
                f,
                "physical call in m{}:f{} passes {actual} operands to m{}:f{}, which expects {expected}",
                owner.module, owner.function, target.module, target.function
            ),
        }
    }
}

impl std::error::Error for BackendReadinessError {}

/// Physical MIR whose readiness invariants have been checked.
pub(crate) struct BackendReadyMirArtifacts {
    module: ModuleId,
    entries: Vec<Option<Function>>,
}

impl BackendReadyMirArtifacts {
    pub(crate) fn module(&self) -> ModuleId {
        self.module
    }

    pub(crate) fn entry_count(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn get(&self, id: LocalFunctionId) -> Option<&Function> {
        self.entries.get(id.as_index())?.as_ref()
    }
}

/// Lower one module's complete optimized MIR artifact set and verify the result.
pub(crate) fn lower_physical_mir(
    module: ModuleId,
    semantic: &MirArtifacts,
    env: ModuleEnv<'_>,
    known: &KnownCallees,
) -> Result<BackendReadyMirArtifacts, BackendReadinessError> {
    assert_eq!(
        env.current.module_id(),
        module,
        "physical lowering needs the source module's environment"
    );
    let mut entries = semantic.cloned_entries();
    let helper_base = FunctionId::new(module, LocalFunctionId::from_index(entries.len()));
    let mut lowerer = PhysicalLowerer::new(helper_base, env, known);
    for (index, entry) in entries.iter_mut().enumerate() {
        if let Some(body) = entry.take() {
            *entry = Some(lowerer.lower_body(
                FunctionId::new(module, LocalFunctionId::from_index(index)),
                body,
            )?);
        }
    }
    entries.extend(lowerer.helpers.into_iter().map(Some));
    let artifacts = BackendReadyMirArtifacts { module, entries };
    verify_physical_mir(&artifacts, env)?;
    Ok(artifacts)
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ProductAddressorKey {
    aggregate_ty: Type,
    field_index: ProjectionIndex,
}

struct PhysicalLowerer<'a> {
    helper_base: FunctionId,
    env: ModuleEnv<'a>,
    known: &'a KnownCallees,
    helper_ids: FxHashMap<ProductAddressorKey, FunctionId>,
    helpers: Vec<Function>,
}

impl<'a> PhysicalLowerer<'a> {
    fn new(helper_base: FunctionId, env: ModuleEnv<'a>, known: &'a KnownCallees) -> Self {
        Self {
            helper_base,
            env,
            known,
            helper_ids: FxHashMap::default(),
            helpers: Vec::new(),
        }
    }

    fn lower_body(
        &mut self,
        function: FunctionId,
        body: Function,
    ) -> Result<Function, BackendReadinessError> {
        let candidates = body
            .blocks()
            .flat_map(|block| {
                body.block(block)
                    .operations()
                    .iter()
                    .enumerate()
                    .filter(|(_, operation)| {
                        matches!(
                            operation.kind,
                            OperationKind::Subfield {
                                variant_payload: false,
                                ..
                            }
                        )
                    })
                    .map(move |(index, operation)| (block, index, operation.clone()))
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return Ok(body);
        }

        let mut edit = FunctionEdit::new(body);
        for (block, index, operation) in candidates.into_iter().rev() {
            self.lower_product_projection(function, &mut edit, block, index, operation)?;
        }
        Ok(edit.finish_unverified())
    }

    fn lower_product_projection(
        &mut self,
        function: FunctionId,
        edit: &mut FunctionEdit,
        block: mir::BlockId,
        operation_index: usize,
        operation: Operation,
    ) -> Result<(), BackendReadinessError> {
        let OperationKind::Subfield {
            ty: field_ty,
            product: Some(product),
            ..
        } = &operation.kind
        else {
            return Err(BackendReadinessError::InvalidProductProjection { function });
        };
        let field_index = constant_index(&operation.operands[1], edit)
            .ok_or(BackendReadinessError::InvalidProductProjection { function })?;
        let spec = product_layout_spec(product.aggregate_ty, operation.span, &self.env)
            .ok_or(BackendReadinessError::InvalidProductProjection { function })?;
        let Some(member) = spec.members.get(field_index.as_index()).copied() else {
            return Err(BackendReadinessError::InvalidProductProjection { function });
        };
        if member.ty != *field_ty {
            return Err(BackendReadinessError::InvalidProductProjection { function });
        }
        // An indirect member's slot owns its pointee allocation. Construction, move, clone and drop
        // must be expanded while the logical projection is still visible; only then can remaining
        // borrows become address_offset_place plus load.
        if member.storage == ProductMemberStorage::Indirect {
            return Err(BackendReadinessError::UnsupportedIndirectProductMember { function });
        }
        let expected_witnesses = spec
            .members
            .iter()
            .filter(|member| member.static_layout.is_none())
            .map(|member| member.ty)
            .collect::<Vec<_>>();
        if expected_witnesses.as_slice() != product.layout_witness_tys.as_ref() {
            return Err(BackendReadinessError::InvalidProductProjection { function });
        }

        let result = operation
            .result_id()
            .ok_or(BackendReadinessError::InvalidProductProjection { function })?;
        if let Some(offset) = spec.static_field_offset(field_index) {
            let offset = isize::try_from(offset)
                .map_err(|_| BackendReadinessError::InvalidProductProjection { function })?;
            let constant =
                edit.add_constant(int_type(), LiteralValue::new_native(offset), &self.env);
            let base = operation.operands[0].clone();
            let offset = Value::Constant(constant);
            match member.storage {
                ProductMemberStorage::Inline => {
                    let mut replacement =
                        Operation::address_offset(operation.span, base, offset, *field_ty);
                    replacement.assign_result_id(Some(result));
                    edit.replace_operation_sequence(block, operation_index, [replacement]);
                }
                ProductMemberStorage::Indirect => {
                    let mut slot_operation =
                        Operation::address_offset_place(operation.span, base, offset, *field_ty);
                    let slot = edit
                        .assign_new_result(&mut slot_operation)
                        .expect("address_offset_place produces a place slot");
                    let mut load = Operation::load(operation.span, slot);
                    load.assign_result_id(Some(result));
                    edit.replace_operation_sequence(block, operation_index, [slot_operation, load]);
                }
            }
            return Ok(());
        }

        let key = ProductAddressorKey {
            aggregate_ty: product.aggregate_ty,
            field_index,
        };
        let helper = self.intern_product_addressor(key, &spec);
        let mut out_operation = Operation::alloca_place(operation.span, *field_ty);
        let out = edit
            .assign_new_result(&mut out_operation)
            .expect("alloca_place produces a place");
        let call_ty = product_addressor_call_type(product.aggregate_ty, *field_ty);
        let mut arguments = operation.operands[2..].to_vec();
        arguments.push(operation.operands[0].clone());
        arguments.push(out.clone());
        let call = Operation::call(operation.span, Value::Function(helper), arguments, call_ty);
        let mut load = Operation::load(operation.span, out);
        load.assign_result_id(Some(result));
        edit.replace_operation_sequence(block, operation_index, [out_operation, call, load]);
        Ok(())
    }

    fn intern_product_addressor(
        &mut self,
        key: ProductAddressorKey,
        spec: &ProductLayoutSpec,
    ) -> FunctionId {
        if let Some(id) = self.helper_ids.get(&key) {
            return *id;
        }
        let id = FunctionId::new(
            self.helper_base.module,
            LocalFunctionId::from_index(self.helper_base.function.as_index() + self.helpers.len()),
        );
        let body = build_product_addressor(&key, spec, self.helpers.len(), self.known, self.env);
        self.helpers.push(body);
        self.helper_ids.insert(key, id);
        id
    }
}

fn constant_index(value: &Value, edit: &FunctionEdit) -> Option<ProjectionIndex> {
    let Value::Constant(id) = value else {
        return None;
    };
    edit.constant(*id)
        .representation
        .as_primitive_ty::<isize>()
        .and_then(|index| usize::try_from(*index).ok())
        .and_then(|index| ProjectionIndex::try_from(index).ok())
}

fn product_addressor_call_type(aggregate_ty: Type, field_ty: Type) -> CallImplType {
    CallImplType::new(
        FnType::new_mut_resolved([(aggregate_ty, true)], field_ty, no_effects()),
        CallResultConvention::ADDRESSOR_PLACE,
    )
}

fn build_product_addressor(
    key: &ProductAddressorKey,
    spec: &ProductLayoutSpec,
    helper_index: usize,
    known: &KnownCallees,
    env: ModuleEnv<'_>,
) -> Function {
    let span = Location::new_synthesized();
    let name = Ustr::from(&format!("#physical:product_addressor:{helper_index}"));
    let mut builder = FunctionBuilder::new(name, CallResultConvention::ADDRESSOR_PLACE);
    let value_trait = env.expect_std_trait_id(VALUE_TRAIT_NAME);
    let member_witnesses = spec
        .members
        .iter()
        .map(|member| {
            member.static_layout.is_none().then(|| {
                let requirement =
                    DictionaryReq::new_trait_impl(value_trait, vec![member.ty], vec![], vec![]);
                Value::Parameter(builder.add_parameter(
                    requirement.to_dict_type_in_env(&env),
                    ParameterKind::Dictionary,
                ))
            })
        })
        .collect::<Vec<_>>();
    let base = Value::Parameter(builder.add_parameter(
        key.aggregate_ty,
        ParameterKind::Parameter(ArgConvention::MutableRef),
    ));
    let field = spec.members[key.field_index.as_index()];
    let destination = Value::Parameter(builder.add_parameter(field.ty, ParameterKind::Return));
    let entry = builder.add_block();

    match spec.order {
        ProductLayoutOrder::Positional => build_positional_product_addressor(
            builder,
            entry,
            key,
            spec,
            &member_witnesses,
            base,
            destination,
            known,
            span,
            env,
        ),
        ProductLayoutOrder::CompactRecord => build_compact_record_addressor(
            builder,
            entry,
            key,
            spec,
            &member_witnesses,
            base,
            destination,
            known,
            span,
            env,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn build_positional_product_addressor(
    mut builder: FunctionBuilder,
    block: mir::BlockId,
    key: &ProductAddressorKey,
    spec: &ProductLayoutSpec,
    member_witnesses: &[Option<Value>],
    base: Value,
    destination: Value,
    known: &KnownCallees,
    span: Location,
    env: ModuleEnv<'_>,
) -> Function {
    let mut offset = int_constant_place(&mut builder, block, 0, span, env);
    for (index, member) in spec.members.iter().enumerate() {
        let align = member_layout_place(
            &mut builder,
            block,
            *member,
            member_witnesses[index].as_ref(),
            VALUE_ALIGN_ASSOC_CONST_INDEX,
            span,
            env,
        );
        offset = align_up_place(&mut builder, block, offset, align, known, span, env);
        if index == key.field_index.as_index() {
            return finish_product_addressor(
                builder,
                block,
                *member,
                base,
                destination,
                offset,
                span,
            );
        }
        let size = member_layout_place(
            &mut builder,
            block,
            *member,
            member_witnesses[index].as_ref(),
            VALUE_SIZE_ASSOC_CONST_INDEX,
            span,
            env,
        );
        offset = int_binary(&mut builder, block, known.int_add(), offset, size, span);
    }
    unreachable!("the product addressor field was validated against the layout recipe")
}

#[allow(clippy::too_many_arguments)]
fn build_compact_record_addressor(
    mut builder: FunctionBuilder,
    mut block: mir::BlockId,
    key: &ProductAddressorKey,
    spec: &ProductLayoutSpec,
    member_witnesses: &[Option<Value>],
    base: Value,
    destination: Value,
    known: &KnownCallees,
    span: Location,
    env: ModuleEnv<'_>,
) -> Function {
    let target = key.field_index.as_index();
    let target_static_layout = spec.members[target].static_layout;
    let mut static_offset = 0isize;
    if let Some(target_layout) = target_static_layout {
        for (candidate, member) in spec.members.iter().enumerate() {
            if candidate == target {
                continue;
            }
            let Some(candidate_layout) = member.static_layout else {
                continue;
            };
            if spec.compact_member_precedes(
                ProjectionIndex::from_index(candidate),
                key.field_index,
                candidate_layout.align.cmp(&target_layout.align),
            ) {
                static_offset = static_offset
                    .checked_add(
                        candidate_layout
                            .size
                            .try_into()
                            .expect("Value size fits in int"),
                    )
                    .expect("product offset fits in int");
            }
        }
    }
    let offset = int_constant_place(&mut builder, block, static_offset, span, env);
    let target_align = member_layout_place(
        &mut builder,
        block,
        spec.members[target],
        member_witnesses[target].as_ref(),
        VALUE_ALIGN_ASSOC_CONST_INDEX,
        span,
        env,
    );
    // Compact order is decreasing alignment. Every preceding member's power-of-two alignment is
    // therefore a multiple of the target alignment, and its size is a multiple of that alignment;
    // summing preceding sizes already produces an aligned target offset without padding.
    for (candidate, member) in spec.members.iter().enumerate() {
        if candidate == target {
            continue;
        }
        let candidate_index = ProjectionIndex::from_index(candidate);
        if member.static_layout.is_some() && target_static_layout.is_some() {
            continue;
        }
        let candidate_align = member_layout_place(
            &mut builder,
            block,
            *member,
            member_witnesses[candidate].as_ref(),
            VALUE_ALIGN_ASSOC_CONST_INDEX,
            span,
            env,
        );
        let add = builder.add_block();
        let next = builder.add_block();
        let ordering = binary_call(
            &mut builder,
            block,
            known.int_cmp(),
            candidate_align,
            target_align.clone(),
            span,
        );
        let tag = append_result(&mut builder, block, Operation::extract_tag(span, ordering));
        let mut cases = vec![(Ustr::from(ORDERING_GREATER), add)];
        if spec.compact_member_precedes(candidate_index, key.field_index, std::cmp::Ordering::Equal)
        {
            cases.push((Ustr::from(ORDERING_EQUAL), add));
        }
        builder.set_terminator(block, Terminator::switch_variant(span, tag, cases, next));

        add_member_size_to_offset(
            &mut builder,
            add,
            *member,
            member_witnesses[candidate].as_ref(),
            &offset,
            known,
            span,
            env,
        );
        builder.set_terminator(add, Terminator::goto(span, next));
        block = next;
    }
    finish_product_addressor(
        builder,
        block,
        spec.members[target],
        base,
        destination,
        offset,
        span,
    )
}

fn finish_product_addressor(
    mut builder: FunctionBuilder,
    block: mir::BlockId,
    member: ProductMemberLayout,
    base: Value,
    destination: Value,
    offset: Value,
    span: Location,
) -> Function {
    let byte_offset = append_result(&mut builder, block, Operation::load(span, offset));
    let address = match member.storage {
        ProductMemberStorage::Inline => append_result(
            &mut builder,
            block,
            Operation::address_offset(span, base, byte_offset, member.ty),
        ),
        ProductMemberStorage::Indirect => {
            let slot = append_result(
                &mut builder,
                block,
                Operation::address_offset_place(span, base, byte_offset, member.ty),
            );
            append_result(&mut builder, block, Operation::load(span, slot))
        }
    };
    builder.append_operation(block, Operation::store(span, address, destination));
    builder.set_terminator(block, Terminator::ret(span));
    builder.finish_unverified()
}

fn append_result(
    builder: &mut FunctionBuilder,
    block: mir::BlockId,
    operation: Operation,
) -> Value {
    builder
        .append_operation(block, operation)
        .expect("the generated operation produces a result")
}

fn int_constant_place(
    builder: &mut FunctionBuilder,
    block: mir::BlockId,
    value: isize,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    let constant = builder.add_constant(int_type(), LiteralValue::new_native(value), &env);
    let place = append_result(builder, block, Operation::alloca(span, int_type()));
    builder.append_operation(
        block,
        Operation::store(span, Value::Constant(constant), place.clone()),
    );
    place
}

fn value_layout_place(
    builder: &mut FunctionBuilder,
    block: mir::BlockId,
    dictionary: Value,
    associated_const: TraitAssociatedConstIndex,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    let (entry, getter_ty) = value_layout_getter_entry(&env, associated_const);
    let getter = append_result(
        builder,
        block,
        Operation::dict_entry(
            span,
            dictionary,
            entry,
            Type::function_type(getter_ty.clone()),
        ),
    );
    let result = append_result(builder, block, Operation::alloca(span, int_type()));
    builder.append_operation(
        block,
        Operation::call(
            span,
            getter,
            [result.clone()],
            CallImplType::value(getter_ty),
        ),
    );
    result
}

fn member_layout_place(
    builder: &mut FunctionBuilder,
    block: mir::BlockId,
    member: ProductMemberLayout,
    witness: Option<&Value>,
    associated_const: TraitAssociatedConstIndex,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    if let Some(layout) = member.static_layout {
        let value = if associated_const == VALUE_SIZE_ASSOC_CONST_INDEX {
            layout.size
        } else {
            debug_assert_eq!(associated_const, VALUE_ALIGN_ASSOC_CONST_INDEX);
            layout.align
        };
        return int_constant_place(
            builder,
            block,
            value.try_into().expect("Value layout fits in int"),
            span,
            env,
        );
    }
    value_layout_place(
        builder,
        block,
        witness
            .expect("an open member has Value layout evidence")
            .clone(),
        associated_const,
        span,
        env,
    )
}

#[allow(clippy::too_many_arguments)]
fn add_member_size_to_offset(
    builder: &mut FunctionBuilder,
    block: mir::BlockId,
    member: ProductMemberLayout,
    witness: Option<&Value>,
    offset: &Value,
    known: &KnownCallees,
    span: Location,
    env: ModuleEnv<'_>,
) {
    let size = member_layout_place(
        builder,
        block,
        member,
        witness,
        VALUE_SIZE_ASSOC_CONST_INDEX,
        span,
        env,
    );
    let sum = int_binary(builder, block, known.int_add(), offset.clone(), size, span);
    let sum = append_result(builder, block, Operation::load(span, sum));
    builder.append_operation(block, Operation::store(span, sum, offset.clone()));
}

fn align_up_place(
    builder: &mut FunctionBuilder,
    block: mir::BlockId,
    offset: Value,
    align: Value,
    known: &KnownCallees,
    span: Location,
    env: ModuleEnv<'_>,
) -> Value {
    let one = int_constant_place(builder, block, 1, span, env);
    let align_minus_one = int_binary(builder, block, known.int_sub(), align.clone(), one, span);
    let upper = int_binary(
        builder,
        block,
        known.int_add(),
        offset,
        align_minus_one,
        span,
    );
    let negated_align = int_unary(builder, block, known.int_neg(), align, span);
    int_binary(
        builder,
        block,
        known.int_bit_and(),
        upper,
        negated_align,
        span,
    )
}

fn int_binary(
    builder: &mut FunctionBuilder,
    block: mir::BlockId,
    callee: (FunctionId, &CallImplType),
    left: Value,
    right: Value,
    span: Location,
) -> Value {
    debug_assert_eq!(callee.1.ret(), int_type());
    binary_call(builder, block, callee, left, right, span)
}

fn binary_call(
    builder: &mut FunctionBuilder,
    block: mir::BlockId,
    callee: (FunctionId, &CallImplType),
    left: Value,
    right: Value,
    span: Location,
) -> Value {
    let result = append_result(builder, block, Operation::alloca(span, callee.1.ret()));
    builder.append_operation(
        block,
        Operation::call(
            span,
            Value::Function(callee.0),
            [left, right, result.clone()],
            callee.1.clone(),
        ),
    );
    result
}

fn int_unary(
    builder: &mut FunctionBuilder,
    block: mir::BlockId,
    callee: (FunctionId, &CallImplType),
    value: Value,
    span: Location,
) -> Value {
    let result = append_result(builder, block, Operation::alloca(span, int_type()));
    builder.append_operation(
        block,
        Operation::call(
            span,
            Value::Function(callee.0),
            [value, result.clone()],
            callee.1.clone(),
        ),
    );
    result
}

fn verify_physical_mir(
    artifacts: &BackendReadyMirArtifacts,
    _env: ModuleEnv<'_>,
) -> Result<(), BackendReadinessError> {
    let module = artifacts.module;
    for index in 0..artifacts.entry_count() {
        let function = LocalFunctionId::from_index(index);
        let Some(body) = artifacts.get(function) else {
            continue;
        };
        let function_id = FunctionId::new(module, function);

        #[cfg(any(debug_assertions, test, feature = "std-snapshot"))]
        {
            mir::role::check_function_operand_roles(body);
        }

        for block in body.blocks() {
            let block = body.block(block);
            for operation in block.operations() {
                verify_physical_operation(artifacts, function_id, operation)?;
            }
            match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => {
                    verify_physical_operation(artifacts, function_id, operation)?;
                }
                _ => verify_local_function_operands(
                    module,
                    artifacts.entry_count(),
                    function_id,
                    block.terminator().operands().iter(),
                )?,
            }
        }
    }
    Ok(())
}

fn verify_physical_operation(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    operation: &Operation,
) -> Result<(), BackendReadinessError> {
    if matches!(
        operation.kind,
        OperationKind::Subfield {
            variant_payload: false,
            ..
        }
    ) {
        return Err(BackendReadinessError::UnresolvedPhysicalOperation {
            function: owner,
            operation: "subfield",
        });
    }
    verify_local_function_operands(
        artifacts.module,
        artifacts.entry_count(),
        owner,
        operation.operands.iter(),
    )?;
    if let Some(target) = operation.kind.function_id() {
        verify_local_function_target(artifacts.module, artifacts.entry_count(), owner, target)?;
    }
    verify_direct_call(artifacts, owner, operation)
}

fn verify_direct_call(
    artifacts: &BackendReadyMirArtifacts,
    owner: FunctionId,
    operation: &Operation,
) -> Result<(), BackendReadinessError> {
    if !matches!(operation.kind, OperationKind::Call { .. }) {
        return Ok(());
    }
    let Some(Value::Function(target)) = operation.operands.first() else {
        return Ok(());
    };
    if target.module != artifacts.module {
        return Ok(());
    }
    let Some(target_body) = artifacts.get(target.function) else {
        return Ok(());
    };
    let expected = target_body.parameters().len();
    let actual = operation.operands.len() - 1;
    if actual != expected {
        return Err(BackendReadinessError::InvalidPhysicalCall {
            owner,
            target: *target,
            expected,
            actual,
        });
    }
    Ok(())
}

fn verify_local_function_operands<'a>(
    module: ModuleId,
    entry_count: usize,
    owner: FunctionId,
    operands: impl Iterator<Item = &'a Value>,
) -> Result<(), BackendReadinessError> {
    for operand in operands {
        let Value::Function(target) = operand else {
            continue;
        };
        verify_local_function_target(module, entry_count, owner, *target)?;
    }
    Ok(())
}

fn verify_local_function_target(
    module: ModuleId,
    entry_count: usize,
    owner: FunctionId,
    target: FunctionId,
) -> Result<(), BackendReadinessError> {
    if target.module == module && target.function.as_index() >= entry_count {
        return Err(BackendReadinessError::InvalidPhysicalEntry { owner, target });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, ExecutionTarget,
        compiler::MirOptimization,
        module::{ModuleEnv, Path},
        std::ordering::ordering_type,
    };

    use super::*;

    fn compile(session: &mut CompilerSession, source: &str, name: &str) -> ModuleId {
        session
            .compile(source, name, Path::single_str(name))
            .expect("test module should compile")
            .module_id
    }

    fn lower(
        session: &mut CompilerSession,
        module: ModuleId,
    ) -> Result<(BackendReadyMirArtifacts, LocalFunctionId), BackendReadinessError> {
        session.set_mir_optimization(MirOptimization::Enabled);
        session.prepare_execution_target(ExecutionTarget::Mir, module);
        let semantic = session
            .mir_artifacts_for(module, MirOptimization::Enabled)
            .expect("optimized MIR was just prepared");
        let first_helper = LocalFunctionId::from_index(semantic.entry_count());
        let known = session.known_callees();
        let physical = lower_physical_mir(
            module,
            semantic,
            ModuleEnv::new(session.expect_fresh_module(module), session.raw_modules()),
            known,
        )?;
        Ok((physical, first_helper))
    }

    #[test]
    fn identity_lowering_retains_every_semantic_entry() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn identity(value: int) -> int { value }",
            "identity",
        );
        let identity = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr::ustr("identity"))
            .unwrap();

        let (physical, _) = lower(&mut session, module).unwrap();
        assert_eq!(physical.module(), module);
        assert!(physical.get(identity).is_some());
    }

    #[test]
    fn a_static_product_projection_becomes_a_byte_offset() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn second(value: (bool, int)) -> int { value.1 }",
            "subfield",
        );
        let second = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr::ustr("second"))
            .unwrap();
        let (physical, _) = lower(&mut session, module).unwrap();
        let body = physical.get(second).unwrap();
        assert!(body.blocks().any(|block| {
            body.block(block)
                .operations()
                .iter()
                .any(|operation| matches!(operation.kind, OperationKind::AddressOffset { .. }))
        }));
        assert!(
            !body
                .blocks()
                .any(|block| body
                    .block(block)
                    .operations()
                    .iter()
                    .any(|operation| matches!(
                        operation.kind,
                        OperationKind::Subfield {
                            variant_payload: false,
                            ..
                        }
                    )))
        );
    }

    #[test]
    fn equivalent_dynamic_product_addressors_share_one_helper() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn right<A, B>(value: (A, B)) -> B { value.1 }\n\
             fn right_again<A, B>(value: (A, B)) -> B { value.1 }",
            "generic_subfield",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        assert_eq!(
            physical.entry_count() - first_helper.as_index(),
            1,
            "equivalent product layout recipes should share one generated addressor"
        );
        let helper = physical.get(first_helper).unwrap();
        assert!(helper.blocks().any(|block| {
            helper
                .block(block)
                .operations()
                .iter()
                .any(|operation| matches!(operation.kind, OperationKind::AddressOffset { .. }))
        }));
    }

    #[test]
    fn an_open_record_addressor_orders_members_by_runtime_alignment() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn field_a<A>(value: { a: A, b: int }) -> A { value.a }\n\
             fn field_b<A>(value: { a: A, b: int }) -> int { value.b }",
            "generic_record_subfield",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        assert_eq!(physical.entry_count() - first_helper.as_index(), 2);
        let mut case_counts = (first_helper.as_index()..physical.entry_count())
            .flat_map(|index| {
                let helper = physical.get(LocalFunctionId::from_index(index)).unwrap();
                helper.blocks().filter_map(|block| {
                    let TerminatorKind::SwitchVariant { cases, .. } =
                        &helper.block(block).terminator().kind
                    else {
                        return None;
                    };
                    Some(cases.len())
                })
            })
            .collect::<Vec<_>>();
        case_counts.sort_unstable();
        assert_eq!(case_counts, [1, 2]);

        let mut checked_comparisons = 0;
        for index in first_helper.as_index()..physical.entry_count() {
            let helper = physical.get(LocalFunctionId::from_index(index)).unwrap();
            let comparison_result = helper
                .blocks()
                .flat_map(|block| helper.block(block).operations())
                .find_map(|operation| {
                    let OperationKind::Call { ty, .. } = &operation.kind else {
                        return None;
                    };
                    (ty.ret() == ordering_type())
                        .then(|| operation.operands.last().cloned())
                        .flatten()
                });
            let Some(Value::Register(comparison_result)) = comparison_result else {
                continue;
            };
            checked_comparisons += 1;
            let comparison_slot_ty = helper
                .blocks()
                .flat_map(|block| helper.block(block).operations())
                .find_map(|operation| {
                    (operation.result_id() == Some(comparison_result)).then_some(&operation.kind)
                })
                .and_then(|kind| match kind {
                    OperationKind::Alloca { ty } => Some(*ty),
                    _ => None,
                });
            assert_eq!(comparison_slot_ty, Some(ordering_type()));
        }
        assert_eq!(checked_comparisons, 2);
    }

    #[test]
    fn positional_addressors_only_materialize_layouts_through_the_target() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn middle<A, B>(value: (int, A, B)) -> A { value.1 }",
            "generic_positional_subfield",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        assert_eq!(physical.entry_count() - first_helper.as_index(), 1);
        let helper = physical.get(first_helper).unwrap();
        let layout_getters = helper
            .blocks()
            .flat_map(|block| helper.block(block).operations())
            .filter(|operation| matches!(operation.kind, OperationKind::DictEntry { .. }))
            .count();
        assert_eq!(
            layout_getters, 1,
            "only the target alignment is needed; its size and B's layout are unused"
        );
    }

    #[test]
    fn compact_addressors_fold_static_member_ordering() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn field_d<A>(value: { a: A, b: int, c: int, d: int }) -> int { value.d }",
            "partially_static_record_subfield",
        );
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        let int_add = session.known_callees().int_add().0;
        assert_eq!(physical.entry_count() - first_helper.as_index(), 1);
        let helper = physical.get(first_helper).unwrap();
        let switches = helper
            .blocks()
            .filter(|block| {
                matches!(
                    helper.block(*block).terminator().kind,
                    TerminatorKind::SwitchVariant { .. }
                )
            })
            .count();
        assert_eq!(
            switches, 1,
            "the static b/c ordering does not require a run-time comparison"
        );
        let additions = helper
            .blocks()
            .flat_map(|block| helper.block(block).operations())
            .filter(|operation| operation.operands.first() == Some(&Value::Function(int_add)))
            .count();
        assert_eq!(
            additions, 1,
            "the sizes of b and c are folded into the initial offset; only A is added conditionally"
        );
    }

    #[test]
    fn generic_product_construction_uses_physical_addressors() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn pair<A, B>(left: A, right: B) -> (A, B) { (left, right) }",
            "generic_product_construction",
        );
        let pair = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr::ustr("pair"))
            .unwrap();
        let (physical, first_helper) = lower(&mut session, module).unwrap();
        let body = physical.get(pair).unwrap();

        assert!(
            !body
                .blocks()
                .any(|block| body
                    .block(block)
                    .operations()
                    .iter()
                    .any(|operation| matches!(
                        operation.kind,
                        OperationKind::Subfield {
                            variant_payload: false,
                            ..
                        }
                    )))
        );
        assert_eq!(
            physical.entry_count() - first_helper.as_index(),
            1,
            "field zero has a constant offset and the second open member needs an addressor"
        );
    }

    #[test]
    fn an_indirect_recursive_member_waits_for_ownership_lowering() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "enum List { Nil, Cons(int, List) }\n\
             fn tail(value: List) -> List {\n\
                 match value { Cons(head, tail) => tail, Nil => List::Nil }\n\
             }",
            "indirect_product_member",
        );
        let error = match lower(&mut session, module) {
            Ok(_) => panic!("indirect product lowering must wait for ownership expansion"),
            Err(error) => error,
        };
        let BackendReadinessError::UnsupportedIndirectProductMember { function } = error else {
            panic!("unexpected physical-lowering error: {error}");
        };
        assert_eq!(function.module, module);
    }
}
