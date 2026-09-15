// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Bodies for retained compiler-owned Buffer entries. Direct calls still use the local expansion;
//! dictionaries, addressors and first-class references keep their original function identities.

use super::*;
use crate::{
    primitive::INVALID_BUFFER_CLONE,
    std::{
        STD_MODULE_ID,
        string::{STRING_FROM_STATIC_FUNCTION_NAME, StaticStr, static_str_type},
    },
};
use ustr::ustr;

pub(super) fn entries(env: ModuleEnv<'_>) -> FxHashMap<FunctionId, BufferPrimitive> {
    let std = env
        .module_by_id(STD_MODULE_ID)
        .expect("physical lowering requires std");
    std.functions
        .iter()
        .enumerate()
        .filter_map(|(index, function)| {
            let CallableOrigin::BufferPrimitive(primitive) = function.origin else {
                return None;
            };
            Some((
                FunctionId::new(STD_MODULE_ID, LocalFunctionId::from_index(index)),
                primitive,
            ))
        })
        .collect()
}

impl PhysicalLowerer<'_> {
    pub(super) fn lower_buffer_entry(
        &mut self,
        id: FunctionId,
        kind: BufferPrimitive,
    ) -> Result<Function, BackendReadinessError> {
        let module = self.env.module_by_id(id.module).unwrap();
        let function = module.get_function_by_id(id.function).unwrap();
        let definition = &function.definition;
        let signature = &definition.ty_scheme.ty;
        if kind == BufferPrimitive::Drop {
            let ty = signature.args[0].ty;
            let mut body = build_buffer_drop(
                ty,
                buffer_element_type(ty).unwrap(),
                id.function.as_index(),
                self.env,
            );
            body.name = module.get_function_name_by_id(id.function).unwrap();
            return self.lower_body(id, id, body);
        }
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new(
            module.get_function_name_by_id(id.function).unwrap(),
            definition.result_convention,
        );
        let passing = function
            .code
            .runtime_argument_passing()
            .expect("Buffer primitives specify passing modes");
        assert_eq!(
            signature.args.len(),
            passing.len(),
            "Buffer primitive passing modes must cover every declared argument"
        );
        let arguments = signature
            .args
            .iter()
            .zip(passing)
            .map(|(arg, passing)| {
                Value::Parameter(builder.add_parameter(arg.ty, ParameterKind::Parameter(*passing)))
            })
            .collect::<Vec<_>>();
        let destination =
            Value::Parameter(builder.add_parameter(signature.ret, ParameterKind::Return));
        let block = builder.add_block();
        match kind {
            BufferPrimitive::Slot
            | BufferPrimitive::WithCapacity
            | BufferPrimitive::MoveInto
            | BufferPrimitive::Move
            | BufferPrimitive::Take
            | BufferPrimitive::Drop => {
                builder.append_operation(
                    block,
                    Operation::call(
                        span,
                        Value::Function(id),
                        arguments.into_iter().chain([destination]),
                        CallImplType::new(signature.clone(), definition.result_convention),
                    ),
                );
            }
            BufferPrimitive::Equal => {
                let value =
                    builder.add_constant(bool_type(), LiteralValue::new_native(false), &self.env);
                builder.append_operation(
                    block,
                    Operation::store(span, Value::Constant(value), destination),
                );
            }
            BufferPrimitive::Hash => {
                finish_unit_result(&mut builder, block, destination, span, self.env);
                return self.lower_body(id, id, builder.finish_unverified());
            }
            BufferPrimitive::ToString => {
                let literal = builder.add_constant(
                    static_str_type(),
                    LiteralValue::new_native(StaticStr::new("<buffer>")),
                    &self.env,
                );
                let callee = module
                    .get_local_function_id(ustr(STRING_FROM_STATIC_FUNCTION_NAME))
                    .unwrap();
                let literal_place = append_result(
                    &mut builder,
                    block,
                    Operation::alloca(span, static_str_type()),
                );
                builder.append_operation(
                    block,
                    Operation::store(span, Value::Constant(literal), literal_place.clone()),
                );
                let ty = module
                    .get_function_by_id(callee)
                    .unwrap()
                    .definition
                    .ty_scheme
                    .ty
                    .clone();
                builder.append_operation(
                    block,
                    Operation::call(
                        span,
                        Value::Function(FunctionId::new(id.module, callee)),
                        [literal_place, destination],
                        CallImplType::value(ty),
                    ),
                );
            }
            BufferPrimitive::Clone => {
                builder.set_terminator(
                    block,
                    Terminator::invariant_failure(span, ustr(INVALID_BUFFER_CLONE)),
                );
                return self.lower_body(id, id, builder.finish_unverified());
            }
        }
        builder.set_terminator(block, Terminator::ret(span));
        self.lower_body(id, id, builder.finish_unverified())
    }
}
