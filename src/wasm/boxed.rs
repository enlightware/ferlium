// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Temporary physical-storage to boxed-`Value` bridge for differential tests.

use std::alloc::Layout;

use crate::{
    CompilerSession, FxHashMap, Location, ModuleEnv,
    hir::{
        native_functions::NativeEntry,
        value::{Value, VariantPayloadStorage},
    },
    module::{FunctionId, ProjectionIndex, id::Id},
    std::{
        array::array_type_def,
        buffer::{Buffer, buffer_element_type},
        logic::bool_type,
        math::{Float, float_type, int_type},
        value::{
            product_layout_spec, structural_variant, value_layout_for_type, variant_payload_offset,
            variant_payload_storage_for_type,
        },
    },
    types::r#type::{Type, TypeKind},
};

use super::runtime;

pub(super) type NativeOutputs = FxHashMap<Type, unsafe fn(*mut u8) -> Value>;

pub(super) fn native_outputs(
    program: &crate::mir::physical::program::ResolvedPhysicalProgram<'_>,
) -> NativeOutputs {
    let mut outputs = NativeOutputs::default();
    for module in program.modules() {
        for (_, native) in module.native_entries() {
            let Some(output) = NativeEntry::host_output(native) else {
                continue;
            };
            let ty = match native.signature().result {
                crate::hir::native_functions::NativeResult::Output(layout)
                | crate::hir::native_functions::NativeResult::Optional {
                    payload: layout, ..
                } => layout.ty,
                _ => continue,
            };
            outputs.insert(ty, output);
        }
    }
    outputs
}

fn error(message: impl Into<String>) -> String {
    message.into()
}

pub(super) fn result_layout(
    session: &CompilerSession,
    owner: FunctionId,
    ty: Type,
) -> Result<Layout, String> {
    let env = session
        .modules()
        .env_for(session.expect_fresh_module(owner.module));
    layout(ty, &env)
}

fn layout(ty: Type, env: &ModuleEnv<'_>) -> Result<Layout, String> {
    let layout = value_layout_for_type(ty, Location::new_synthesized(), env)
        .map_err(|failure| format!("boxed Wasm result layout: {failure:?}"))?;
    Layout::from_size_align(layout.size as usize, layout.align as usize)
        .map_err(|_| error("invalid boxed Wasm result layout"))
}

fn array_element_type(ty: Type) -> Option<Type> {
    let data = ty.data();
    let TypeKind::Named(named) = &*data else {
        return None;
    };
    if named.def == array_type_def() && named.params.len() == 1 {
        Some(named.params[0])
    } else {
        None
    }
}

fn structural_type(mut ty: Type, env: &ModuleEnv<'_>) -> Result<Type, String> {
    let mut seen = crate::FxHashSet::default();
    loop {
        // Array is a named type whose boxed representation has dedicated Buffer ownership. Stop
        // before unfolding it, including when another named representation resolves to Array.
        if array_element_type(ty).is_some() {
            return Ok(ty);
        }
        if !seen.insert(ty) {
            return Err(error("recursive named result representation"));
        }
        let data = ty.data().clone();
        let TypeKind::Named(named) = data else {
            return Ok(ty);
        };
        ty = env
            .type_def(named.def)
            .instantiated_shape_with_effects(&named.params, &named.effect_params);
    }
}

fn read_usize(address: *mut u8) -> usize {
    // This module exists only on wasm32, where compiled pointers and `usize` are both i32.
    unsafe { address.cast::<usize>().read() }
}

fn product_offsets(ty: Type, env: &ModuleEnv<'_>) -> Result<Vec<(Type, usize)>, String> {
    let spec = product_layout_spec(ty, Location::new_synthesized(), env)
        .ok_or_else(|| error("expected boxed Wasm product result"))?;
    spec.members
        .iter()
        .enumerate()
        .map(|(index, member)| {
            spec.static_field_offset(ProjectionIndex::from_index(index))
                .map(|offset| (member.ty, offset))
                .ok_or_else(|| error("open boxed Wasm product layout"))
        })
        .collect()
}

/// Reject result shapes the temporary boxed boundary cannot consume before guest code runs.
pub(super) fn validate_result(
    session: &CompilerSession,
    owner: FunctionId,
    outputs: &NativeOutputs,
    ty: Type,
) -> Result<(), String> {
    fn visit(
        ty: Type,
        env: &ModuleEnv<'_>,
        outputs: &NativeOutputs,
        seen: &mut crate::FxHashSet<Type>,
    ) -> Result<(), String> {
        if !seen.insert(ty) {
            return Ok(());
        }
        layout(ty, env)?;
        let structural = structural_type(ty, env)?;
        if let Some(element) = array_element_type(structural) {
            let fields = product_offsets(structural, env)?;
            if fields.len() != 4 || buffer_element_type(fields[1].0) != Some(element) {
                return Err(error("unexpected compiled Array representation"));
            }
            return visit(element, env, outputs, seen);
        }
        if structural == Type::unit()
            || structural == bool_type()
            || structural == int_type()
            || structural == float_type()
        {
            return Ok(());
        }
        if product_layout_spec(structural, Location::new_synthesized(), env).is_some() {
            for (member, _) in product_offsets(structural, env)? {
                visit(member, env, outputs, seen)?;
            }
            return Ok(());
        }
        if let Some((_, cases)) = structural_variant(structural, env) {
            for (tag, payload) in cases.iter() {
                variant_payload_storage_for_type(ty, *tag, Location::new_synthesized(), env)
                    .map_err(|failure| format!("boxed Wasm variant storage: {failure:?}"))?;
                visit(*payload, env, outputs, seen)?;
            }
            return Ok(());
        }
        match &*structural.data() {
            TypeKind::Native(_) if outputs.contains_key(&structural) => Ok(()),
            TypeKind::Native(_) => Err(error("native boxed Wasm result has no export glue")),
            TypeKind::Function(_) | TypeKind::Subscript(_) => {
                Err(error("host callable results are unsupported"))
            }
            TypeKind::Never => Ok(()),
            TypeKind::Variable(_) | TypeKind::Named(_) => {
                Err(error("unresolved boxed Wasm result type"))
            }
            TypeKind::Tuple(_) | TypeKind::Record(_) | TypeKind::Variant(_) => {
                unreachable!("structural cases handled above")
            }
        }
    }

    let env = session
        .modules()
        .env_for(session.expect_fresh_module(owner.module));
    visit(ty, &env, outputs, &mut crate::FxHashSet::default())
}

enum DecodeTask {
    Visit {
        ty: Type,
        address: *mut u8,
    },
    Product(usize),
    Variant {
        tag: ustr::Ustr,
        storage: VariantPayloadStorage,
        unit: bool,
        allocation: Option<*mut u8>,
    },
    Array {
        capacity: usize,
        len: usize,
        start: usize,
        allocation: *mut u8,
    },
}

/// Consume one complete physical result and reconstruct the boxed reference representation.
///
/// This intentionally exists only for the shared differential harness. Production bindings keep
/// using direct typed ABIs and never box values or cross JavaScript with them. Callers validate
/// the result shape before execution. An error here therefore reports corrupt backend storage;
/// reclaiming that storage without running destructors belongs to runtime-domain poisoning.
pub(super) fn export(
    session: &CompilerSession,
    owner: FunctionId,
    outputs: &NativeOutputs,
    ty: Type,
    address: *mut u8,
) -> Result<Value, String> {
    let env = session
        .modules()
        .env_for(session.expect_fresh_module(owner.module));
    let mut tasks = vec![DecodeTask::Visit { ty, address }];
    let mut values = Vec::new();
    let result = (|| {
        while let Some(task) = tasks.pop() {
            match task {
                DecodeTask::Visit { ty, address } => {
                    let structural = structural_type(ty, &env)?;
                    if let Some(element) = array_element_type(structural) {
                        let fields = product_offsets(structural, &env)?;
                        if fields.len() != 4 || buffer_element_type(fields[1].0) != Some(element) {
                            return Err(error("unexpected compiled Array representation"));
                        }
                        let capacity = read_usize(unsafe { address.add(fields[0].1) });
                        let allocation = read_usize(unsafe { address.add(fields[1].1) }) as *mut u8;
                        let len = read_usize(unsafe { address.add(fields[2].1) });
                        let start = read_usize(unsafe { address.add(fields[3].1) });
                        if len > capacity
                            || (capacity == 0 && (len != 0 || start != 0))
                            || (capacity != 0 && start >= capacity)
                        {
                            return Err(error("invalid boxed Wasm Array bounds"));
                        }
                        if allocation.is_null() {
                            return Err(error("null boxed Wasm Buffer allocation"));
                        }
                        let element_layout = layout(element, &env)?;
                        let required = element_layout
                            .size()
                            .checked_mul(capacity)
                            .ok_or_else(|| error("boxed Wasm Buffer size overflow"))?;
                        // SAFETY: the result owns the Buffer pointer produced by the runtime.
                        let allocation_layout = unsafe { runtime::payload_layout(allocation) };
                        if allocation_layout.size() < required
                            || (capacity != 0 && allocation_layout.align() < element_layout.align())
                        {
                            return Err(error(format!(
                                "boxed Wasm Buffer allocation layout mismatch: capacity {capacity}, \
                                 element {}:{}, allocation {}:{}",
                                element_layout.size(),
                                element_layout.align(),
                                allocation_layout.size(),
                                allocation_layout.align(),
                            )));
                        }
                        tasks.push(DecodeTask::Array {
                            capacity,
                            len,
                            start,
                            allocation,
                        });
                        for offset in (0..len).rev() {
                            let index = (start + offset) % capacity;
                            tasks.push(DecodeTask::Visit {
                                ty: element,
                                // SAFETY: the allocation check above covers every capacity slot.
                                address: unsafe { allocation.add(index * element_layout.size()) },
                            });
                        }
                        continue;
                    }

                    if structural == Type::unit() {
                        values.push(Value::unit());
                    } else if structural == bool_type() {
                        values.push(Value::native(unsafe { address.cast::<u8>().read() != 0 }));
                    } else if structural == int_type() {
                        values.push(Value::native(unsafe { address.cast::<isize>().read() }));
                    } else if structural == float_type() {
                        values.push(Value::native(unsafe { address.cast::<Float>().read() }));
                    } else if product_layout_spec(ty, Location::new_synthesized(), &env).is_some() {
                        let fields = product_offsets(ty, &env)?;
                        tasks.push(DecodeTask::Product(fields.len()));
                        tasks.extend(fields.into_iter().rev().map(|(ty, offset)| {
                            DecodeTask::Visit {
                                ty,
                                // SAFETY: product_layout_spec supplied an in-bounds field offset.
                                address: unsafe { address.add(offset) },
                            }
                        }));
                    } else if let Some((_, cases)) = structural_variant(ty, &env) {
                        let raw = unsafe { address.cast::<u32>().read() };
                        let (tag_id, storage) = VariantPayloadStorage::decode_tag(raw);
                        let tag = session
                            .variant_tag_name(tag_id)
                            .ok_or_else(|| error("unknown boxed Wasm variant tag"))?;
                        let payload = cases
                            .iter()
                            .find_map(|(candidate, payload)| {
                                (*candidate == tag).then_some(*payload)
                            })
                            .ok_or_else(|| error("boxed Wasm variant tag/type mismatch"))?;
                        let expected = variant_payload_storage_for_type(
                            ty,
                            tag,
                            Location::new_synthesized(),
                            &env,
                        )
                        .map_err(|failure| format!("boxed Wasm variant storage: {failure:?}"))?;
                        if storage != expected {
                            return Err(error("boxed Wasm variant storage mismatch"));
                        }
                        let payload_layout = layout(payload, &env)?;
                        let field = unsafe {
                            address.add(variant_payload_offset(if storage.is_indirect() {
                                align_of::<usize>() as u32
                            } else {
                                payload_layout.align() as u32
                            }) as usize)
                        };
                        let allocation =
                            storage.is_indirect().then(|| read_usize(field) as *mut u8);
                        let payload_address = allocation.unwrap_or(field);
                        if payload_address.is_null() {
                            return Err(error("null boxed Wasm variant payload"));
                        }
                        tasks.push(DecodeTask::Variant {
                            tag,
                            storage,
                            unit: payload == Type::unit(),
                            allocation,
                        });
                        tasks.push(DecodeTask::Visit {
                            ty: payload,
                            address: payload_address,
                        });
                    } else {
                        match &*structural.data() {
                            TypeKind::Native(_) => {
                                let output = outputs.get(&structural).ok_or_else(|| {
                                    error("native boxed Wasm result has no export glue")
                                })?;
                                values.push(unsafe { output(address) });
                            }
                            TypeKind::Function(_) | TypeKind::Subscript(_) => {
                                return Err(error("host callable results are unsupported"));
                            }
                            TypeKind::Never => {
                                return Err(error("successful never-valued Wasm result"));
                            }
                            TypeKind::Variable(_) | TypeKind::Named(_) => {
                                return Err(error("unresolved boxed Wasm result type"));
                            }
                            TypeKind::Tuple(_) | TypeKind::Record(_) | TypeKind::Variant(_) => {
                                unreachable!("structural cases handled above")
                            }
                        }
                    }
                }
                DecodeTask::Product(count) => {
                    let fields = values.split_off(values.len() - count);
                    values.push(Value::tuple(fields));
                }
                DecodeTask::Variant {
                    tag,
                    storage,
                    unit,
                    allocation,
                } => {
                    let payload = values.pop().unwrap();
                    if let Some(allocation) = allocation {
                        // SAFETY: the payload was consumed and no live value remains in the block.
                        unsafe { runtime::release(allocation) };
                    }
                    values.push(if unit {
                        payload.discard_storage();
                        Value::unit_variant(tag)
                    } else {
                        Value::variant_with_storage(tag, storage, payload)
                    });
                }
                DecodeTask::Array {
                    capacity,
                    len,
                    start,
                    allocation,
                } => {
                    let elements = values.split_off(values.len() - len);
                    let mut buffer = Buffer::with_capacity(capacity);
                    for (offset, value) in elements.into_iter().enumerate() {
                        *buffer.get_mut((start + offset) % capacity).unwrap() = value;
                    }
                    // SAFETY: every initialized element was moved out and all remaining slots were
                    // absent; the raw backing allocation no longer owns source values.
                    unsafe { runtime::release(allocation) };
                    values.push(Value::tuple([
                        Value::native(capacity as isize),
                        Value::native(buffer),
                        Value::native(len as isize),
                        Value::native(start as isize),
                    ]));
                }
            }
        }
        values
            .pop()
            .filter(|_| values.is_empty())
            .ok_or_else(|| error("boxed Wasm result traversal imbalance"))
    })();
    if result.is_err() {
        for value in values {
            value.discard_storage();
        }
    }
    result
}
