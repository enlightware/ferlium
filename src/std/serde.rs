// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::ustr;

use crate::{
    Location,
    ast::UnnamedArg,
    cached_ty,
    compiler::error::InternalCompilationError,
    containers::{SVec2, b},
    hir::hir_syn::native_str,
    hir::value::{LiteralValue, ustr_to_isize},
    hir::{self, CallArgument, NodeArena, NodeId},
    hir::{
        function::CallableDefinition,
        value_dispatch::{
            prepare_generated_call_arguments_with_locals, static_apply_generated_with_locals,
        },
    },
    module::{
        self, LocalDecl, LocalDeclId, Module, PendingFunctionBody, PendingLocalClone,
        ProjectionIndex, ResolvedLocalClone, TraitId, TraitImplId, id::Id,
    },
    std::{
        array::array_type,
        core_traits_names::{DESERIALIZE_TRAIT_NAME, SERIALIZE_TRAIT_NAME, VALUE_TRAIT_NAME},
        data_value::data_value_record_entry_type,
        math::int_type,
        string::{string_type, string_value},
        value::VALUE_CLONE_METHOD_INDEX,
    },
    types::effects::{EffType, PrimitiveEffect},
    types::mutability::MutVal,
    types::r#trait::{Deriver, Trait, TraitMethodIndex},
    types::trait_solver::TraitSolver,
    types::r#type::{
        CallImplType, CallResultConvention, FnArgType, FnType, Type, TypeKind, tuple_type,
    },
    types::type_like::TypeLike,
};

use super::data_value::data_value_type;

pub const SERIALIZE_FN_NAME: &str = "serialize";
pub const DESERIALIZE_FN_NAME: &str = "deserialize";

fn alloc_synth_node(arena: &mut NodeArena, kind: hir::NodeKind, ty: Type) -> NodeId {
    arena.alloc(hir::Node::new(
        kind,
        ty,
        EffType::empty(),
        Location::new_synthesized(),
    ))
}

#[allow(clippy::too_many_arguments)]
fn build_serialize_projection(
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
    trait_id: TraitId,
    span: Location,
    locals: &mut Vec<LocalDecl>,
    self_id: LocalDeclId,
    self_ty: Type,
    index: usize,
    member_ty: Type,
) -> Result<NodeId, InternalCompilationError> {
    use hir::hir_syn::*;

    let load_node = alloc_synth_node(arena, load_local(self_id), self_ty);
    let project_node = alloc_synth_node(
        arena,
        project(load_node, ProjectionIndex::from_index(index)),
        member_ty,
    );
    let function =
        solver.solve_impl_method(trait_id, &[member_ty], TraitMethodIndex(0), span, arena)?;
    static_apply_generated_with_locals(
        arena,
        locals,
        solver,
        function,
        [(project_node, member_ty)],
        data_value_type(),
        span,
    )
}

fn record_payload_type() -> Type {
    cached_ty!(|| {
        let element_ty = tuple_type([string_type(), data_value_type()]);
        array_type(element_ty)
    })
}

#[derive(Debug, Clone)]
struct AlgebraicTypeSerializeDeriver;
impl Deriver for AlgebraicTypeSerializeDeriver {
    fn derive_impl(
        &self,
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use hir::hir_syn::*;

        // safety checks
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        // Allocate a node in the arena with empty effects and synthesized span.
        let n = |arena: &mut NodeArena, kind: hir::NodeKind, ty: Type| -> NodeId {
            arena.alloc(hir::Node::new(
                kind,
                ty,
                EffType::empty(),
                Location::new_synthesized(),
            ))
        };

        // Helper to create a sequence-shaped DataValue alternative.
        let build_serialize_to_seq = |arena: &mut NodeArena, nodes, tag| {
            let array_ty = array_type(data_value_type());
            let array_node = n(arena, array(nodes), array_ty);
            let payload_ty = tuple_type([array_ty]);
            let payload = n(arena, tuple([array_node]), payload_ty);
            n(arena, variant(ustr(tag), payload), data_value_type())
        };

        let ty_data = ty.data().clone();
        if let TypeKind::Named(named) = ty_data {
            let inner_ty = solver
                .type_def(named.def)
                .instantiated_shape_with_effects(&named.params, &named.effect_params);
            // serialize the inner type
            return Ok(Some(solver.solve_impl(
                trait_id,
                &[inner_ty],
                span,
                arena,
            )?));
        }
        if !matches!(
            ty_data,
            TypeKind::Tuple(_) | TypeKind::Record(_) | TypeKind::Variant(_)
        ) {
            return Ok(None);
        }
        let snapshot = solver.snapshot_derived_impl_state();
        let impl_id =
            solver.reserve_concrete_impl_from_code_entries(trait_id, input_types, &[], &[], []);

        let mut body_arena = NodeArena::default();
        let arena = &mut body_arena;
        let mut locals = vec![local("self", ty)];
        let l_self_id = LocalDeclId::from_index(0);

        // derive tuple, record, and enum serialization
        let root = if let TypeKind::Tuple(tys) = ty_data {
            /*
            Example source code for serialization of a tuple:
            impl Serialize {
                fn serialize(t: (_, _)) {
                    Array([
                        serialize(t.0),
                        serialize(t.1),
                    ])
                }
            }

            Example corresponding HIR:
            DataValue with tag: Array
                build tuple (
                    build array [
                        serialize(t.0),
                        serialize(t.1),
                    ]
                )
            */

            let nodes = tys
                .into_iter()
                .enumerate()
                .map(|(index, ty_i)| {
                    // serialize the i-th element
                    build_serialize_projection(
                        arena,
                        solver,
                        trait_id,
                        span,
                        &mut locals,
                        l_self_id,
                        ty,
                        index,
                        ty_i,
                    )
                })
                .collect::<Result<SVec2<_>, _>>()?;
            Some(build_serialize_to_seq(arena, nodes, "Tuple"))
        } else if let TypeKind::Record(fields) = ty_data {
            /*
            Example source code for serialization of a record:
            impl Serialize {
                fn serialize(r: {a: _, b: _}) {
                    Record([
                        (
                            String("a"),
                            serialize(r.0)
                        ),
                        (
                            String("b"),
                            serialize(r.1)
                        ),
                    ])
                }
            }

            Example corresponding HIR:
            DataValue with tag: Record
                build tuple (
                    build array [
                        build tuple (
                            value: "a",
                            serialize(r.0),
                        ),
                        build tuple (
                            value: "b"
                            serialize(r.1),
                        ),
                    ]
                )
            */
            let nodes = fields
                .into_iter()
                .enumerate()
                .map(|(index, (name, ty_i))| {
                    let tag = n(arena, native_str(&name), string_type());
                    let payload = build_serialize_projection(
                        arena,
                        solver,
                        trait_id,
                        span,
                        &mut locals,
                        l_self_id,
                        ty,
                        index,
                        ty_i,
                    )?;
                    let entry = n(arena, tuple([tag, payload]), data_value_record_entry_type());
                    Ok(entry)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            Some(build_serialize_to_seq(arena, nodes, "Record"))
        } else if let TypeKind::Variant(variants) = ty_data {
            // Store Ferlium enum variants explicitly in the serialization data model.
            /*
            impl Serialize {
                fn serialize(v: Variant1 | Variant2(_)) {
                    match v {
                        Variant1 => Variant({ name: "Variant1", payload: Unit }),
                        Variant2(x) => Variant({ name: "Variant2", payload: serialize(x) }),
                    }
                }
            }
            */
            // Build the enum serialization cases.
            let alternatives = variants
                .into_iter()
                .map(|(tag, payload_ty)| {
                    let name_node = n(arena, native_str(&tag), string_type());
                    let payload_node = if payload_ty != Type::unit() {
                        build_serialize_projection(
                            arena,
                            solver,
                            trait_id,
                            span,
                            &mut locals,
                            l_self_id,
                            ty,
                            0,
                            payload_ty,
                        )?
                    } else {
                        let unit_payload = n(arena, native(()), Type::unit());
                        n(
                            arena,
                            variant(ustr("Unit"), unit_payload),
                            data_value_type(),
                        )
                    };
                    let enum_record_ty = Type::record(vec![
                        (ustr("name"), string_type()),
                        (ustr("payload"), data_value_type()),
                    ]);
                    let enum_record = n(arena, record([name_node, payload_node]), enum_record_ty);
                    let code = n(
                        arena,
                        variant(ustr("Variant"), enum_record),
                        data_value_type(),
                    );
                    let tag_value = LiteralValue::new_native(ustr_to_isize(tag));
                    Ok((tag_value, code))
                })
                .collect::<Result<Vec<_>, _>>()?;
            // build the match node
            let load_node = n(arena, load_local(l_self_id), ty);
            let extract_tag_node = n(arena, extract_tag(load_node), int_type());
            let root = n(
                arena,
                case_from_complete_alternatives(extract_tag_node, alternatives),
                data_value_type(),
            );
            Some(root)
        } else {
            None
        };
        let Some(root) = root else {
            solver.rollback_derived_impl_state(snapshot);
            return Ok(None);
        };
        solver.replace_concrete_impl_code_entries(
            impl_id,
            trait_id,
            input_types,
            &[],
            &[],
            [(PendingFunctionBody::new(body_arena, root), locals)],
        );
        Ok(Some(TraitImplId::new(
            solver.current_type_items.module.id,
            impl_id,
        )))
    }
}

#[derive(Debug, Clone)]
struct AlgebraicTypeDeserializeDeriver;
impl Deriver for AlgebraicTypeDeserializeDeriver {
    fn derive_impl(
        &self,
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use hir::hir_syn::*;

        // safety checks
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        // helpers to synthesize HIR
        let n = |arena: &mut NodeArena, kind: hir::NodeKind, ty: Type| -> NodeId {
            arena.alloc(hir::Node::new(
                kind,
                ty,
                EffType::empty(),
                Location::new_synthesized(),
            ))
        };

        // Build the deserialization of a DataValue into a value of type `ty`.
        let build_deserialize = |arena: &mut NodeArena,
                                 locals: &mut Vec<LocalDecl>,
                                 solver: &mut TraitSolver,
                                 data: NodeId,
                                 ty: Type| {
            let function =
                solver.solve_impl_method(trait_id, &[ty], TraitMethodIndex(0), span, arena)?;
            static_apply_generated_with_locals(
                arena,
                locals,
                solver,
                function,
                [(data, data_value_type())],
                ty,
                Location::new_synthesized(),
            )
        };

        // derive tuple, record, and enum deserialization
        let ty_data = ty.data().clone();
        if let TypeKind::Named(named) = ty_data {
            let inner_ty = solver
                .type_def(named.def)
                .instantiated_shape_with_effects(&named.params, &named.effect_params);
            // deserialize the inner type
            return Ok(Some(solver.solve_impl(
                trait_id,
                &[inner_ty],
                span,
                arena,
            )?));
        }
        if !matches!(
            ty_data,
            TypeKind::Tuple(_) | TypeKind::Record(_) | TypeKind::Variant(_)
        ) {
            return Ok(None);
        }
        let snapshot = solver.snapshot_derived_impl_state();
        let impl_id =
            solver.reserve_concrete_impl_from_code_entries(trait_id, input_types, &[], &[], []);

        let mut body_arena = NodeArena::default();
        let arena = &mut body_arena;
        let mut locals = vec![local("data", data_value_type())];
        let l_data_value_id = LocalDeclId::from_index(0);
        let load_data_value = n(arena, load_local(l_data_value_id), data_value_type());
        let node = if let TypeKind::Tuple(tys) = ty_data {
            /*
            Example source code for deserialization of a tuple:
            impl Deserialize {
                fn deserialize(data: DataValue) -> (_, _) {
                    let arr = std::data_value_to_tuple(data);
                    (
                        deserialize(arr[0]),
                        deserialize(arr[1]),
                    )
                }
            }
            */
            // extract the tuple payload from the data value
            let get_array = build_data_value_to_tuple(arena, &mut locals, solver, load_data_value)?;
            let data_value_ty = data_value_type();
            let array_ty = array_type(data_value_ty);
            let value_trait_id = solver.std_trait_id(VALUE_TRAIT_NAME);
            let data_value_clone =
                PendingLocalClone::Resolved(ResolvedLocalClone::Static(solver.solve_impl_method(
                    value_trait_id,
                    &[data_value_ty],
                    VALUE_CLONE_METHOD_INDEX,
                    span,
                    arena,
                )?));
            // store it at 1
            let (store_array, l_array_id) = store_new_local(
                get_array,
                1,
                "array",
                MutVal::constant(),
                array_ty,
                &mut locals,
            );
            let store_array = n(arena, store_array, Type::unit());
            // build deserialization of each element
            let build_elements = tys
                .into_iter()
                .enumerate()
                .map(|(i, ty_i)| {
                    // get the array payload of the data value
                    let get_array = n(arena, load_local(l_array_id), array_ty);
                    // get the i-th element
                    let index_node = n(
                        arena,
                        immediate(LiteralValue::new_native(i as isize)),
                        int_type(),
                    );
                    let array_index = solver.get_subscript_member(
                        span,
                        &module::Path::single_str("std"),
                        ustr("array_index"),
                        false,
                    )?;
                    let arguments = vec![get_array, index_node];
                    let ty = FnType::new(
                        vec![
                            FnArgType::new_by_val(array_ty),
                            FnArgType::new_by_val(int_type()),
                        ],
                        data_value_ty,
                        EffType::empty(),
                    );
                    let mut arguments = arguments;
                    let prepared = prepare_generated_call_arguments_with_locals(
                        arena,
                        &mut locals,
                        solver,
                        &mut arguments,
                        &ty.args,
                        span,
                    )?;
                    let arguments =
                        CallArgument::from_values_and_passing(arguments, prepared.argument_passing);
                    assert!(prepared.temp_stores.is_empty());
                    let index_place = n(
                        arena,
                        hir::NodeKind::StaticApply(b(hir::StaticApplication {
                            function: array_index,
                            function_path: None,
                            function_span: span,
                            extra_arguments: vec![],
                            arguments,
                            argument_names: vec![ustr("array"), ustr("index")],
                            argument_name_hint_policy: UnnamedArg::All,
                            ty: CallImplType::new(ty, CallResultConvention::ADDRESSOR_PLACE),
                            inst_data: hir::FnInstData::none(),
                        })),
                        data_value_ty,
                    );
                    let index_node = n(
                        arena,
                        hir::NodeKind::CloneValue(hir::CloneValue {
                            source: index_place,
                            clone: data_value_clone,
                        }),
                        data_value_ty,
                    );
                    // deserialize the i-th element
                    build_deserialize(arena, &mut locals, solver, index_node, ty_i)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            // build the tuple node
            let build_tuple = n(arena, tuple(build_elements), ty);
            // `array` is read, not consumed, so it is still live here and must be dropped.
            Some(n(
                arena,
                block_with_cleanup([store_array, build_tuple], vec![l_array_id]),
                ty,
            ))
        } else if let TypeKind::Record(fields) = ty_data {
            /*
            Example source code for deserialization of a record:
            impl Deserialize {
                fn deserialize(data: DataValue) -> {a: _, b: _} {
                    let o = std::data_value_to_record(data);
                    {
                        a: deserialize(std::expect_data_value_record_entry(o, "a")),
                        b: deserialize(std::expect_data_value_record_entry(o, "b")),
                    }
                }
            }
            */
            // Extract the record payload from the data value.
            let get_record =
                build_data_value_to_record(arena, &mut locals, solver, load_data_value)?;
            let record_ty = record_payload_type();
            // store it at 1
            let (store_record, l_record_id) = store_new_local(
                get_record,
                1,
                "record",
                MutVal::constant(),
                record_ty,
                &mut locals,
            );
            let store_record = n(arena, store_record, Type::unit());
            // build deserialization of each field
            let build_elements = fields
                .into_iter()
                .map(|(name, ty)| {
                    // get the record payload
                    let load_record = n(arena, load_local(l_record_id), record_payload_type());
                    // get the name-th element out of the record array
                    let get_entry = build_expect_data_value_record_entry(
                        arena,
                        &mut locals,
                        solver,
                        load_record,
                        &name,
                    )?;
                    // deserialize the name-th element
                    let function = solver.solve_impl_method(
                        trait_id,
                        &[ty],
                        TraitMethodIndex(0),
                        span,
                        arena,
                    )?;
                    static_apply_generated_with_locals(
                        arena,
                        &mut locals,
                        solver,
                        function,
                        [(get_entry, data_value_type())],
                        ty,
                        Location::new_synthesized(),
                    )
                })
                .collect::<Result<SVec2<_>, _>>()?;
            // build the record node
            let build_record = n(arena, record(build_elements), ty);
            // `record` is read, not consumed, so it is still live here and must be dropped.
            Some(n(
                arena,
                block_with_cleanup([store_record, build_record], vec![l_record_id]),
                ty,
            ))
        } else if let TypeKind::Variant(variants) = ty_data {
            // Deserialize explicit enum variant data, while the helper also accepts the
            // adjacent-tagged record shape produced by the JSON codec.
            /*
            impl Deserialize {
                fn deserialize(data: DataValue) -> Variant1 | Variant2(x) {
                    let variant = std::data_value_to_variant(data);
                    match variant.name {
                        "Variant1" => Variant1,
                        "Variant2" => {
                            Variant2(deserialize(variant.payload))
                        },
                        _ => panic!("Unknown enum variant tag")
                    }
                }
            }
            */
            // extract the variant payload
            let get_variant =
                build_data_value_to_variant(arena, &mut locals, solver, load_data_value)?;
            let variant_data_value_ty = variant_payload_type();
            // store it at 1
            let (store_variant, l_variant_id) = store_new_local(
                get_variant,
                1,
                "variant",
                MutVal::constant(),
                variant_data_value_ty,
                &mut locals,
            );
            let store_variant = n(arena, store_variant, Type::unit());
            // Load the variant name from local 1.
            let load_variant_id = n(arena, load_local(l_variant_id), variant_payload_type());
            let get_name = n(
                arena,
                project(load_variant_id, ProjectionIndex::from_index(0)),
                string_type(),
            );
            // Build the data extraction for each enum alternative.
            let variant_cases = variants
                .into_iter()
                .map(|(tag, payload_ty)| {
                    let tag_value = string_value(&tag)
                        .to_literal_value()
                        .expect("enum variant tag strings should always lower to literal values");
                    let build_variant = if payload_ty != Type::unit() {
                        // variant with payload
                        let load_variant_for_payload =
                            n(arena, load_local(l_variant_id), variant_payload_type());
                        let get_data = n(
                            arena,
                            project(load_variant_for_payload, ProjectionIndex::from_index(1)),
                            data_value_type(),
                        );
                        let deserialize =
                            build_deserialize(arena, &mut locals, solver, get_data, payload_ty)?;
                        n(arena, variant(tag, deserialize), ty)
                    } else {
                        // variant without payload
                        let payload = n(arena, native(()), Type::unit());
                        n(arena, variant(tag, payload), ty)
                    };
                    Ok((tag_value, build_variant))
                })
                .collect::<Result<Vec<_>, _>>()?;
            // build the match node
            let panic_node = build_panic(arena, &mut locals, solver, "Unknown enum variant tag")?;
            let match_type = n(arena, case(get_name, variant_cases, panic_node), ty);
            // `variant` is read, not consumed (the match borrows `variant.name`), so it must be dropped.
            Some(n(
                arena,
                block_with_cleanup([store_variant, match_type], vec![l_variant_id]),
                ty,
            ))
        } else {
            None // deserialization of rest not yet supported
        };
        let Some(root) = node else {
            solver.rollback_derived_impl_state(snapshot);
            return Ok(None);
        };
        solver.replace_concrete_impl_code_entries(
            impl_id,
            trait_id,
            input_types,
            &[],
            &[],
            [(PendingFunctionBody::new(body_arena, root), locals)],
        );
        Ok(Some(TraitImplId::new(
            solver.current_type_items.module.id,
            impl_id,
        )))
    }
}

pub fn add_to_module(to: &mut Module) {
    // Traits
    let var0_ty = Type::variable_id(0);
    use CallableDefinition as Def;

    // Serialize trait
    let serialize_trait = Trait::new_with_self_input_type(
        SERIALIZE_TRAIT_NAME,
        "A type that can be serialized into a data value.",
        [],
        [(
            SERIALIZE_FN_NAME,
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [var0_ty],
                    data_value_type(),
                    EffType::single_primitive(PrimitiveEffect::Fallible),
                ),
                ["self"],
                "Serialize this value into a data value.",
            ),
        )],
    )
    .with_deriver(AlgebraicTypeSerializeDeriver);
    to.add_trait(serialize_trait);

    // Deserialize trait
    let deserialize_trait = Trait::new_with_self_input_type(
        DESERIALIZE_TRAIT_NAME,
        "A type that can be deserialized from a data value.",
        [],
        [(
            DESERIALIZE_FN_NAME,
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [data_value_type()],
                    var0_ty,
                    EffType::single_primitive(PrimitiveEffect::Fallible),
                ),
                ["data"],
                "Deserialize a data value into a value of this type.",
            ),
        )],
    )
    .with_deriver(AlgebraicTypeDeserializeDeriver);
    to.add_trait(deserialize_trait);

    // Trait implementations for basic types are in the prelude.
}

// Build a node that fetches the panic function node from the trait solver, importing it if necessary.
fn build_panic(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    solver: &mut TraitSolver,
    message: &str,
) -> Result<NodeId, InternalCompilationError> {
    let span = Location::new_synthesized();

    // helpers to synthesize HIR
    let n = |arena: &mut NodeArena, kind, ty| {
        arena.alloc(hir::Node::new(kind, ty, EffType::empty(), span))
    };

    let build_string = n(arena, native_str(message), string_type());
    let function = solver.get_function(span, &module::Path::single_str("std"), ustr("panic"))?;
    static_apply_generated_with_locals(
        arena,
        locals,
        solver,
        function,
        [(build_string, string_type())],
        Type::never(),
        span,
    )
}

fn build_data_value_to_tuple(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    solver: &mut TraitSolver,
    data_value_node: NodeId,
) -> Result<NodeId, InternalCompilationError> {
    build_data_value_to_x(
        arena,
        locals,
        solver,
        "tuple",
        array_type(data_value_type()),
        data_value_node,
    )
}

fn build_data_value_to_record(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    solver: &mut TraitSolver,
    data_value_node: NodeId,
) -> Result<NodeId, InternalCompilationError> {
    build_data_value_to_x(
        arena,
        locals,
        solver,
        "record",
        record_payload_type(),
        data_value_node,
    )
}

fn variant_payload_type() -> Type {
    Type::record(vec![
        (ustr("name"), string_type()),
        (ustr("payload"), data_value_type()),
    ])
}

fn build_data_value_to_variant(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    solver: &mut TraitSolver,
    data_value_node: NodeId,
) -> Result<NodeId, InternalCompilationError> {
    build_data_value_to_x(
        arena,
        locals,
        solver,
        "variant",
        variant_payload_type(),
        data_value_node,
    )
}

fn build_data_value_to_x(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    solver: &mut TraitSolver,
    what: &str,
    ret_ty: Type,
    data_value_node: NodeId,
) -> Result<NodeId, InternalCompilationError> {
    let span = Location::new_synthesized();

    let function = solver.get_function(
        span,
        &module::Path::single_str("std"),
        ustr(&format!("data_value_to_{what}")),
    )?;
    static_apply_generated_with_locals(
        arena,
        locals,
        solver,
        function,
        [(data_value_node, data_value_type())],
        ret_ty,
        span,
    )
}

// Build a node that gets an entry from a data-value record payload [(string, DataValue)].
fn build_expect_data_value_record_entry(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    solver: &mut TraitSolver,
    fields: NodeId,
    name: &str,
) -> Result<NodeId, InternalCompilationError> {
    use hir::hir_syn::*;
    let span = Location::new_synthesized();

    // types
    let element_ty = tuple_type([string_type(), data_value_type()]);
    let payload_ty = array_type(element_ty);

    let name_node = alloc_synth_node(arena, native_str(name), string_type());
    let function = solver.get_function(
        span,
        &module::Path::single_str("std"),
        ustr("expect_data_value_record_entry"),
    )?;
    static_apply_generated_with_locals(
        arena,
        locals,
        solver,
        function,
        [(fields, payload_ty), (name_node, string_type())],
        data_value_type(),
        span,
    )
}
