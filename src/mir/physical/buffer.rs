//! Bodies for retained compiler-owned Buffer entries. Direct calls still use the local expansion;
//! dictionaries, addressors and first-class references keep their original function identities.

use super::*;
use crate::std::{
    STD_MODULE_ID,
    buffer::{INVALID_BUFFER_CLONE, buffer_type},
    core_traits_names::INSPECT_TRAIT_NAME,
    string::{STRING_FROM_STATIC_FUNCTION_NAME, StaticStr, static_str_type},
    value::{
        INSPECT_METHOD_INDEX, VALUE_CLONE_METHOD_INDEX, VALUE_EQ_METHOD_INDEX,
        VALUE_HASH_METHOD_INDEX, VALUE_TO_STRING_METHOD_INDEX,
    },
};
use crate::types::r#trait::TraitMethodIndex;
use ustr::ustr;

#[derive(Clone, Copy)]
pub(super) enum BufferEntry {
    Storage(KnownCallee),
    Equal,
    Format,
    Hash,
    Clone,
}

pub(super) fn entries(
    env: ModuleEnv<'_>,
    known: &KnownCallees,
) -> FxHashMap<FunctionId, BufferEntry> {
    let std = env
        .module_by_id(STD_MODULE_ID)
        .expect("physical lowering requires std");
    let mut entries = FxHashMap::default();
    for index in 0..std.function_count() {
        let id = FunctionId::new(STD_MODULE_ID, LocalFunctionId::from_index(index));
        if let Some(kind) = known.resolve(id, |_| None).filter(|kind| kind.is_buffer()) {
            entries.insert(id, BufferEntry::Storage(kind));
        }
    }
    for trait_name in [VALUE_TRAIT_NAME, INSPECT_TRAIT_NAME] {
        let trait_id = env.expect_std_trait_id(trait_name);
        let implementations = std
            .get_blanket_impl_by_key(&trait_id)
            .expect("std Buffer traits must have blanket implementations");
        let (_, &id) = implementations
            .iter()
            .find(|(key, _)| key.input_tys == [buffer_type(Type::variable_id(0))])
            .expect("std must implement Value and Inspect for Buffer<A>");
        let implementation = std
            .get_impl_data(id)
            .expect("std Buffer implementation identity must resolve");
        let method = |index: TraitMethodIndex| {
            FunctionId::new(
                STD_MODULE_ID,
                *implementation
                    .methods
                    .get(index.as_index())
                    .expect("std Buffer implementation must contain the required trait method"),
            )
        };
        if trait_name == INSPECT_TRAIT_NAME {
            entries.insert(method(INSPECT_METHOD_INDEX), BufferEntry::Format);
        } else {
            for (index, kind) in [
                (VALUE_EQ_METHOD_INDEX, BufferEntry::Equal),
                (VALUE_TO_STRING_METHOD_INDEX, BufferEntry::Format),
                (VALUE_HASH_METHOD_INDEX, BufferEntry::Hash),
                (VALUE_CLONE_METHOD_INDEX, BufferEntry::Clone),
            ] {
                entries.insert(method(index), kind);
            }
        }
    }
    entries
}

impl PhysicalLowerer<'_> {
    pub(super) fn lower_buffer_entry(
        &mut self,
        id: FunctionId,
        kind: BufferEntry,
    ) -> Result<Function, BackendReadinessError> {
        let module = self.env.module_by_id(id.module).unwrap();
        let function = module.get_function_by_id(id.function).unwrap();
        let definition = &function.definition;
        let signature = &definition.ty_scheme.ty;
        if let BufferEntry::Storage(KnownCallee::BufferDrop) = kind {
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
            BufferEntry::Storage(_) => {
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
            BufferEntry::Equal => {
                let value =
                    builder.add_constant(bool_type(), LiteralValue::new_native(false), &self.env);
                builder.append_operation(
                    block,
                    Operation::store(span, Value::Constant(value), destination),
                );
            }
            BufferEntry::Hash => {
                finish_unit_result(&mut builder, block, destination, span, self.env);
                return self.lower_body(id, id, builder.finish_unverified());
            }
            BufferEntry::Format => {
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
            BufferEntry::Clone => {
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
