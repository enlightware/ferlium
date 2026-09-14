//! Access contracts for initialized borrowed storage. No operation may open an initialization
//! gap in a native member, including when it flows through ordinary generic mutable parameters.

use super::*;
use crate::types::r#type::TypeKind;
use crate::{
    hir::native_functions::NativeParameter, mir::pass::dataflow::call_operands,
    types::type_properties::concrete_type_is_trivial_copy,
};

const LIVE: u8 = 1;
const READ_ONLY: u8 = 2;
const INTERIOR: u8 = 4;
// Callee provenance travels through the same register/storage transfers as place permissions.
const SHARED_ADDRESSOR: u8 = 8;

fn add(map: &mut FxHashMap<Value, u8>, value: &Value, flags: u8) -> bool {
    if flags == 0 {
        return false;
    }
    let old = map.entry(value.clone()).or_default();
    let changed = *old | flags != *old;
    *old |= flags;
    changed
}

pub(super) fn verify(
    body: &Function,
    id: FunctionId,
    original: FunctionId,
    helper_base: FunctionId,
    signatures: &FxHashMap<FunctionId, NativeSignature>,
    buffers: &FxHashMap<FunctionId, BufferPrimitive>,
    env: ModuleEnv<'_>,
) -> Result<(), BackendReadinessError> {
    let trusted_addressor = |target: FunctionId| {
        (target.module == helper_base.module
            && target.function.as_index() >= helper_base.function.as_index())
            || buffers.contains_key(&target)
            || env
                .module_by_id(target.module)
                .and_then(|module| module.get_function_by_id(target.function))
                .is_some_and(|function| {
                    matches!(
                        function.origin,
                        CallableOrigin::StructuralFieldAddressor { .. }
                    )
                })
    };
    let lifecycle = is_value_drop_function(original, &env) || trusted_addressor(original);
    let mut places = FxHashMap::default();
    let mut contents = FxHashMap::default();
    for (&function, signature) in signatures {
        if matches!(
            signature.result,
            NativeResult::Addressor { mutable: false, .. }
        ) {
            places.insert(Value::Function(function), SHARED_ADDRESSOR);
        }
    }
    if !lifecycle {
        for (index, parameter) in body.parameters().iter().enumerate() {
            if parameter.kind == ParameterKind::Parameter(ArgConvention::MutableRef) {
                places.insert(Value::Parameter(ParameterId::from_index(index)), LIVE);
            }
        }
    }
    let operations = body
        .blocks()
        .flat_map(|block| {
            let block = body.block(block);
            block
                .operations()
                .iter()
                .chain(match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => Some(operation),
                    _ => None,
                })
        })
        .collect::<Vec<_>>();
    // Pointer storage is flow-insensitive and joins permissions conservatively. A result produced
    // by Invoke only exists on its success edge; adding its restriction globally is conservative.
    let mut changed = true;
    while changed {
        changed = false;
        for op in &operations {
            let operands = &op.operands;
            let result = op.result_id().map(Value::Register);
            match &op.kind {
                OperationKind::Subfield { .. }
                | OperationKind::AddressOffset { .. }
                | OperationKind::AddressOffsetPlace { .. } => {
                    let flags = places.get(&operands[0]).copied().unwrap_or(0);
                    if flags & INTERIOR != 0 {
                        changed |= add(&mut places, result.as_ref().unwrap(), flags);
                    }
                    let flags = contents.get(&operands[0]).copied().unwrap_or(0);
                    changed |= add(&mut contents, result.as_ref().unwrap(), flags);
                }
                OperationKind::Store => {
                    let flags = places.get(&operands[0]).copied().unwrap_or(0);
                    changed |= add(&mut contents, &operands[1], flags);
                    // Callable storage can be called through a stored/reloaded pointer to it.
                    changed |= add(&mut places, &operands[1], flags & SHARED_ADDRESSOR);
                }
                OperationKind::Load => {
                    let flags = contents.get(&operands[0]).copied().unwrap_or(0);
                    changed |= add(&mut places, result.as_ref().unwrap(), flags);
                }
                OperationKind::Move | OperationKind::Memcpy => {
                    let flags = contents.get(&operands[0]).copied().unwrap_or(0);
                    changed |= add(&mut contents, &operands[1], flags);
                    changed |= add(&mut places, &operands[1], flags & SHARED_ADDRESSOR);
                }
                OperationKind::SubscriptMember {
                    mut_member: false, ..
                } => {
                    changed |= add(&mut places, result.as_ref().unwrap(), SHARED_ADDRESSOR);
                    // Member resolution yields callable storage, which can itself be copied.
                    changed |= add(&mut contents, result.as_ref().unwrap(), SHARED_ADDRESSOR);
                }
                OperationKind::BorrowSubscriptMember {
                    mut_member: false, ..
                } => {
                    changed |= add(&mut places, result.as_ref().unwrap(), SHARED_ADDRESSOR);
                }
                OperationKind::Call { ty, .. }
                    if ty.result_convention == CallResultConvention::ADDRESSOR_PLACE =>
                {
                    let call = call_operands(operands, ty).expect("verified call shape");
                    let signature = match call.callee {
                        Value::Function(id) => signatures.get(id),
                        _ => None,
                    };
                    let callee_flags = places.get(call.callee).copied().unwrap_or(0)
                        | contents.get(call.callee).copied().unwrap_or(0);
                    let flags = match signature.map(|signature| signature.result) {
                        Some(NativeResult::Addressor { mutable, .. }) => {
                            LIVE | INTERIOR | if mutable { 0 } else { READ_ONLY }
                        }
                        // Addressor interfaces can be implemented by a native member. Destruction
                        // and compiler-owned Buffer bodies separately own partial storage.
                        _ if !lifecycle
                            && !matches!(call.callee, Value::Function(id) if trusted_addressor(*id)) =>
                        {
                            LIVE | INTERIOR
                        }
                        _ => 0,
                    } | if callee_flags & SHARED_ADDRESSOR != 0 {
                        READ_ONLY
                    } else {
                        0
                    };
                    changed |= add(&mut contents, call.result, flags);
                }
                _ => {}
            }
        }
    }
    let roles = ValueRoles::derive(body);
    let flags = |value: &Value| places.get(value).copied().unwrap_or(0);
    let error = |operation| BackendReadinessError::InvalidNativeInteriorAccess {
        function: id,
        operation,
    };
    let consume = |value: &Value| {
        if flags(value) & LIVE != 0 {
            Err(error("consuming access"))
        } else {
            Ok(())
        }
    };
    let write = |value: &Value, replace: bool| {
        let access = flags(value);
        if access & READ_ONLY != 0 {
            return Err(error("mutable access to shared member"));
        }
        if !replace && access & LIVE != 0 {
            let trivial = roles
                .get(value, body.constants())
                .and_then(|role| role.place_pointee_type())
                .is_some_and(|ty| matches!(ty, MirType::Lowered(ty) if concrete_type_is_trivial_copy(ty, &env)));
            if !trivial {
                return Err(error("owning write without replace"));
            }
        }
        Ok(())
    };
    for op in operations {
        let operands = &op.operands;
        match &op.kind {
            OperationKind::Subfield { .. }
            | OperationKind::AddressOffset { .. }
            | OperationKind::AddressOffsetPlace { .. } => {
                let native_pointee = roles
                    .get(&operands[0], body.constants())
                    .and_then(|role| role.place_pointee_type())
                    .is_some_and(|ty| match ty {
                        MirType::Lowered(ty) => {
                            matches!(&*ty.data(), TypeKind::Native(_))
                                && buffer_element_type(ty).is_none()
                        }
                        _ => false,
                    });
                if flags(&operands[0]) & INTERIOR != 0 && native_pointee {
                    return Err(error("native member offset computation"));
                }
            }
            OperationKind::Clear
            | OperationKind::Drop { .. }
            | OperationKind::DropSubscriptEnv
            | OperationKind::RuntimeDealloc => consume(&operands[0])?,
            OperationKind::Move | OperationKind::MoveBytes { .. } => {
                consume(&operands[0])?;
                write(&operands[1], false)?;
            }
            OperationKind::Store | OperationKind::Memcpy | OperationKind::Clone { .. } => {
                write(&operands[1], false)?;
            }
            OperationKind::Replace => {
                consume(&operands[0])?;
                write(&operands[1], true)?;
            }
            OperationKind::Call { ty, metadata } => {
                let call = call_operands(operands, ty).expect("verified call shape");
                for (index, (argument, passing)) in call.arguments.iter().enumerate() {
                    if *passing == ArgConvention::MutableRef && flags(argument) & READ_ONLY != 0 {
                        return Err(error("mutable call through shared member"));
                    }
                    if metadata
                        .as_ref()
                        .is_some_and(|metadata| metadata.owned_arguments.contains(index))
                    {
                        consume(argument)?;
                    }
                    if let Value::Function(target) = call.callee {
                        let consumes = signatures.get(target).is_some_and(|signature| {
                            matches!(
                                signature.parameters.get(index),
                                Some(NativeParameter::Consuming(_))
                            )
                        }) || (index == 0 && is_value_drop_function(*target, &env));
                        if consumes {
                            consume(argument)?;
                        }
                    }
                }
                write(call.result, false)?;
            }
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession,
        hir::native_functions::{NativeFailureConvention, NativeLayout},
        std::string::String as NativeString,
    };

    #[test]
    fn native_member_physical_access_checks_aliases_and_consuming_entries() {
        let session = CompilerSession::new();
        let env = ModuleEnv::new(session.std_module(), session.raw_modules());
        let module = session.modules().next_id();
        let owner = FunctionId::new(module, LocalFunctionId::from_index(0));
        let addressor = FunctionId::new(module, LocalFunctionId::from_index(1));
        let destroy = FunctionId::new(module, LocalFunctionId::from_index(2));
        let helpers = FunctionId::new(module, LocalFunctionId::from_index(3));
        let layout = NativeLayout::of::<NativeString>();
        let span = Location::new_synthesized();
        for mutable in [false, true] {
            for consuming in [false, true] {
                let mut f = FunctionBuilder::new("access".into(), CallResultConvention::Value);
                let receiver = Value::Parameter(f.add_parameter(layout.ty, ParameterKind::Owned));
                let replacement =
                    Value::Parameter(f.add_parameter(layout.ty, ParameterKind::Owned));
                let block = f.add_block();
                let slot = append_result(&mut f, block, Operation::alloca_place(span, layout.ty));
                let ty = CallImplType::new(
                    FnType::new_mut_resolved([(layout.ty, mutable)], layout.ty, no_effects()),
                    CallResultConvention::ADDRESSOR_PLACE,
                );
                f.append_operation(
                    block,
                    Operation::call(
                        span,
                        Value::Function(addressor),
                        [receiver, slot.clone()],
                        ty,
                    ),
                );
                let member = append_result(&mut f, block, Operation::load(span, slot));
                // Carry the pointer through another slot, as a returned/forwarded place does.
                let alias = append_result(&mut f, block, Operation::alloca_place(span, layout.ty));
                f.append_operation(block, Operation::store(span, member, alias.clone()));
                let member = append_result(&mut f, block, Operation::load(span, alias));
                if consuming {
                    let unit = append_result(&mut f, block, Operation::alloca(span, Type::unit()));
                    let ty = CallImplType::new(
                        FnType::new_mut_resolved([(layout.ty, true)], Type::unit(), no_effects()),
                        CallResultConvention::Value,
                    );
                    f.append_operation(
                        block,
                        Operation::call(span, Value::Function(destroy), [member, unit], ty),
                    );
                } else {
                    f.append_operation(block, Operation::replace(span, replacement, member, None));
                }
                f.set_terminator(block, Terminator::ret(span));
                let signatures = FxHashMap::from_iter([
                    (
                        addressor,
                        NativeSignature {
                            failure: NativeFailureConvention::Infallible,
                            parameters: vec![if mutable {
                                NativeParameter::Mutable(layout)
                            } else {
                                NativeParameter::Shared(layout)
                            }],
                            result: NativeResult::Addressor {
                                pointee: layout,
                                root: 0,
                                mutable,
                            },
                        },
                    ),
                    (
                        destroy,
                        NativeSignature {
                            failure: NativeFailureConvention::Infallible,
                            parameters: vec![NativeParameter::Consuming(layout)],
                            result: NativeResult::Unit,
                        },
                    ),
                ]);
                let result = verify(
                    &f.finish_unverified(),
                    owner,
                    owner,
                    helpers,
                    &signatures,
                    &FxHashMap::default(),
                    env,
                );
                assert_eq!(
                    result.is_ok(),
                    mutable && !consuming,
                    "mutable={mutable}, consuming={consuming}: {result:?}"
                );
            }
        }
    }

    #[test]
    fn native_member_indirect_callees_preserve_shared_access() {
        let session = CompilerSession::new();
        let env = ModuleEnv::new(session.std_module(), session.raw_modules());
        let module = session.modules().next_id();
        let owner = FunctionId::new(module, LocalFunctionId::from_index(0));
        let addressor = FunctionId::new(module, LocalFunctionId::from_index(1));
        let helpers = FunctionId::new(module, LocalFunctionId::from_index(2));
        let layout = NativeLayout::of::<NativeString>();
        let span = Location::new_synthesized();
        // Exercise known native functions and both forms of subscript member lookup,
        // through pointer storage as well as whole callable-storage transfers.
        for mutable in [false, true] {
            for source in 0..3 {
                for transfer in 0..3 {
                    // BorrowedCallable cannot be stored or copied; it is only callable directly.
                    if source == 2 && transfer != 0 {
                        continue;
                    }
                    let mut f =
                        FunctionBuilder::new("indirect_access".into(), CallResultConvention::Value);
                    let receiver =
                        Value::Parameter(f.add_parameter(layout.ty, ParameterKind::Owned));
                    let replacement =
                        Value::Parameter(f.add_parameter(layout.ty, ParameterKind::Owned));
                    let block = f.add_block();
                    let fn_ty =
                        FnType::new_mut_resolved([(layout.ty, mutable)], layout.ty, no_effects());
                    let callable_ty = Type::function_type(fn_ty.clone());
                    let callee = match source {
                        0 => {
                            // Calls use callable storage, not a loaded function representation.
                            let slot =
                                append_result(&mut f, block, Operation::alloca(span, callable_ty));
                            f.append_operation(
                                block,
                                Operation::store(span, Value::Function(addressor), slot.clone()),
                            );
                            slot
                        }
                        _ => {
                            let subscript = Value::Subscript(SubscriptId::new(
                                module,
                                LocalSubscriptId::from_index(0),
                            ));
                            let operation = if source == 1 {
                                Operation::subscript_member(span, subscript, mutable, callable_ty)
                            } else {
                                Operation::borrow_subscript_member(
                                    span,
                                    subscript,
                                    mutable,
                                    callable_ty,
                                )
                            };
                            append_result(&mut f, block, operation)
                        }
                    };
                    let callee = if source == 2 {
                        callee
                    } else if transfer == 0 {
                        let slot = append_result(
                            &mut f,
                            block,
                            Operation::alloca_place(span, callable_ty),
                        );
                        f.append_operation(block, Operation::store(span, callee, slot.clone()));
                        append_result(&mut f, block, Operation::load(span, slot))
                    } else {
                        let slot =
                            append_result(&mut f, block, Operation::alloca(span, callable_ty));
                        let operation = if transfer == 1 {
                            Operation::memcpy(span, callee, slot.clone())
                        } else {
                            Operation::move_value(span, callee, slot.clone())
                        };
                        f.append_operation(block, operation);
                        slot
                    };
                    let slot =
                        append_result(&mut f, block, Operation::alloca_place(span, layout.ty));
                    f.append_operation(
                        block,
                        Operation::call(
                            span,
                            callee,
                            [receiver, slot.clone()],
                            CallImplType::new(fn_ty, CallResultConvention::ADDRESSOR_PLACE),
                        ),
                    );
                    let member = append_result(&mut f, block, Operation::load(span, slot));
                    f.append_operation(block, Operation::replace(span, replacement, member, None));
                    f.set_terminator(block, Terminator::ret(span));
                    let signatures = FxHashMap::from_iter([(
                        addressor,
                        NativeSignature {
                            failure: NativeFailureConvention::Infallible,
                            parameters: vec![if mutable {
                                NativeParameter::Mutable(layout)
                            } else {
                                NativeParameter::Shared(layout)
                            }],
                            result: NativeResult::Addressor {
                                pointee: layout,
                                root: 0,
                                mutable,
                            },
                        },
                    )]);
                    let result = verify(
                        &f.finish_unverified(),
                        owner,
                        owner,
                        helpers,
                        &signatures,
                        &FxHashMap::default(),
                        env,
                    );
                    if mutable {
                        result.unwrap();
                    } else {
                        assert!(
                            matches!(
                                result,
                                Err(BackendReadinessError::InvalidNativeInteriorAccess {
                                    operation: "mutable access to shared member",
                                    ..
                                })
                            ),
                            "source={source}, transfer={transfer}: {result:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn native_member_generic_mutable_parameters_cannot_be_cleared() {
        let session = CompilerSession::new();
        let env = ModuleEnv::new(session.std_module(), session.raw_modules());
        let owner = FunctionId::new(session.modules().next_id(), LocalFunctionId::from_index(0));
        let helpers = FunctionId::new(owner.module, LocalFunctionId::from_index(1));
        let mut f = FunctionBuilder::new("generic_clear".into(), CallResultConvention::Value);
        let parameter = Value::Parameter(f.add_parameter(
            Type::variable_id(0),
            ParameterKind::Parameter(ArgConvention::MutableRef),
        ));
        let block = f.add_block();
        f.append_operation(
            block,
            Operation::clear(Location::new_synthesized(), parameter),
        );
        f.set_terminator(block, Terminator::ret(Location::new_synthesized()));
        assert!(
            verify(
                &f.finish_unverified(),
                owner,
                owner,
                helpers,
                &FxHashMap::default(),
                &FxHashMap::default(),
                env
            )
            .is_err()
        );
    }
}
