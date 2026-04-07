// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::ustr;

use std::sync::Arc;

use crate::{
    Location, cached_ty,
    containers::SVec2,
    effects::{EffType, PrimitiveEffect},
    error::InternalCompilationError,
    function::FunctionDefinition,
    ir::{self, NodeArena, NodeId},
    ir_syn,
    module::{self, LocalDeclId, Module, TraitImplId, id::Id},
    mutability::MutVal,
    std::{
        array::array_type,
        math::int_type,
        string::{string_type, string_value},
        variant::variant_object_entry_type,
    },
    r#trait::{Deriver, TraitRef},
    trait_solver::TraitSolver,
    r#type::{FnType, Type, TypeKind, tuple_type},
    type_like::TypeLike,
    value::{Value, ustr_to_isize},
};

use super::variant::variant_type;

pub const SERIALIZE_TRAIT_NAME: &str = "Serialize";
pub const DESERIALIZE_TRAIT_NAME: &str = "Deserialize";

pub const SERIALIZE_FN_NAME: &str = "serialize";
pub const DESERIALIZE_FN_NAME: &str = "deserialize";

fn object_payload_type() -> Type {
    cached_ty!(|| {
        let element_ty = tuple_type([string_type(), variant_type()]);
        array_type(element_ty)
    })
}

#[derive(Debug, Clone)]
struct AlgebraicTypeSerializeDeriver;
impl Deriver for AlgebraicTypeSerializeDeriver {
    fn derive_impl(
        &self,
        trait_ref: &TraitRef,
        input_types: &[Type],
        span: Location,
        arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use ir_syn::*;

        // safety checks
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        // Allocate a node in the arena with empty effects and synthesized span.
        let n = |arena: &mut NodeArena, kind: ir::NodeKind, ty: Type| -> NodeId {
            arena.alloc(ir::Node::new(
                kind,
                ty,
                EffType::empty(),
                Location::new_synthesized(),
            ))
        };

        // helper to create the concrete trait implementation for sequences
        let build_serialize_to_seq =
            |arena: &mut NodeArena, nodes, tag, locals, solver: &mut TraitSolver| {
                let array_ty = array_type(variant_type());
                let array_node = n(arena, array(nodes), array_ty);
                let payload_ty = tuple_type([array_ty]);
                let payload = n(arena, tuple([array_node]), payload_ty);
                let root = n(arena, variant(ustr(tag), payload), variant_type());
                TraitImplId::Local(solver.add_concrete_impl_from_code(
                    root,
                    locals,
                    trait_ref,
                    input_types,
                    [],
                ))
            };

        let locals = vec![local("self", ty)];
        let l_self_id = LocalDeclId::from_index(0);

        // helper to build the serialization of a member of a tuple
        let mut build_serialize_i = |arena: &mut NodeArena, index, ty| {
            // load function parameter (that is a tuple in memory)
            let load_node = n(arena, load(0, l_self_id), ty);
            // project the i-th element
            let project_node = n(arena, project(load_node, index), ty);
            // serialize the i-th element
            let function = solver.solve_impl_method(trait_ref, &[ty], 0, span, arena)?;
            let apply = n(
                arena,
                static_apply_pure(function, [(project_node, ty)], variant_type(), span),
                variant_type(),
            );
            Ok(apply)
        };

        // derive tuple, record, variant serialization
        let ty_data = ty.data().clone();
        if let TypeKind::Tuple(tys) = ty_data {
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

            Example corresponding IR:
            variant with tag: Array
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
                    build_serialize_i(arena, index, ty_i)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            Ok(Some(build_serialize_to_seq(
                arena, nodes, "Array", locals, solver,
            )))
        } else if let TypeKind::Record(fields) = ty_data {
            /*
            Example source code for serialization of a record:
            impl Serialize {
                fn serialize(r: {a: _, b: _}) {
                    Object([
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

            Example corresponding IR:
            variant with tag: Object
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
                    let payload = build_serialize_i(arena, index, ty_i)?;
                    let entry = n(arena, tuple([tag, payload]), variant_object_entry_type());
                    Ok(entry)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            Ok(Some(build_serialize_to_seq(
                arena, nodes, "Object", locals, solver,
            )))
        } else if let TypeKind::Variant(variants) = ty_data {
            // default to adjacently tagged into an object, with tag = "type", content = "data"
            /*
            impl Serialize {
                fn serialize(v: Variant1 | Variant2(_)) {
                    match v {
                        Variant1 => Object([
                            (String("type"), String("Variant1")),
                        ]),
                        Variant2(x) => Object([
                            (String("type"), String("Variant2")),
                            (String("data"), serialize(x)),
                        ]),
                    }
                }
            }
            */
            // Build the different variants
            let alternatives = variants
                .into_iter()
                .map(|(tag, payload_ty)| {
                    let tag_node = n(arena, native_str(&tag), string_type());
                    let tag_tuple_ty = tuple_type([string_type()]);
                    let tag_tuple_node = n(arena, tuple([tag_node]), tag_tuple_ty);
                    let tag_variant_node = n(
                        arena,
                        variant(ustr("String"), tag_tuple_node),
                        variant_type(),
                    );
                    let type_str = n(arena, native_str("type"), string_type());
                    let tag_entry = n(
                        arena,
                        tuple([type_str, tag_variant_node]),
                        variant_object_entry_type(),
                    );
                    let array_ty = array_type(variant_object_entry_type());
                    let array_node = if payload_ty != Type::unit() {
                        // variant with payload
                        let payload_node = build_serialize_i(arena, 0, payload_ty)?;
                        let data_str = n(arena, native_str("data"), string_type());
                        let payload_entry = n(
                            arena,
                            tuple([data_str, payload_node]),
                            variant_object_entry_type(),
                        );
                        n(arena, array([tag_entry, payload_entry]), array_ty)
                    } else {
                        // variant without payload
                        n(arena, array([tag_entry]), array_ty)
                    };
                    let payload_ty = tuple_type([array_ty]);
                    let payload = n(arena, tuple([array_node]), payload_ty);
                    let code = n(arena, variant(ustr("Object"), payload), variant_type());
                    let tag_value = Value::native(ustr_to_isize(tag));
                    Ok((tag_value, code))
                })
                .collect::<Result<Vec<_>, _>>()?;
            // build the match node
            let load_node = n(arena, load(0, l_self_id), ty);
            let extract_tag_node = n(arena, extract_tag(load_node), int_type());
            let root = n(
                arena,
                case_from_complete_alternatives(extract_tag_node, alternatives),
                variant_type(),
            );
            let local_impl_id =
                solver.add_concrete_impl_from_code(root, locals, trait_ref, input_types, []);
            Ok(Some(TraitImplId::Local(local_impl_id)))
        } else if let TypeKind::Named(named) = ty_data {
            let inner_ty = named.instantiated_shape();
            // serialize the inner type
            Ok(Some(solver.solve_impl(
                trait_ref,
                &[inner_ty],
                span,
                arena,
            )?))
            /*
            if let Some(variant) = ty_def.shape.data().as_variant() {
                // default to adjacently tagged, with tag = "type", content = "data"
                // enum like, todo
                Err(internal_compilation_error!( Unsupported {
                    reason: "Serialization of enum-like named types is not yet supported.".to_string(),
                    span,
                }))
            } else {
                // struct-like, serialize the inner type
                /*
                Example source code for serialization of a struct-like named type:
                impl Serialize {
                    fn serialize(s: S) {
                        serialize(s)
                    }
                }
                */
                Ok(Some(solver.get_impl(trait_ref, &[ty_def.shape], span)?))
            }
            */
        } else {
            Ok(None)
        }
    }
}

#[derive(Debug, Clone)]
struct AlgebraicTypeDeserializeDeriver;
impl Deriver for AlgebraicTypeDeserializeDeriver {
    fn derive_impl(
        &self,
        trait_ref: &TraitRef,
        input_types: &[Type],
        span: Location,
        arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use ir_syn::*;

        // safety checks
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        // helpers to synthesize IR
        let n = |arena: &mut NodeArena, kind: ir::NodeKind, ty: Type| -> NodeId {
            arena.alloc(ir::Node::new(
                kind,
                ty,
                EffType::empty(),
                Location::new_synthesized(),
            ))
        };

        // build the deserialization of a variant into a value of type `ty`
        let build_deserialize =
            |arena: &mut NodeArena, solver: &mut TraitSolver, variant: NodeId, ty: Type| {
                let function = solver.solve_impl_method(trait_ref, &[ty], 0, span, arena)?;
                Ok(n(
                    arena,
                    static_apply_pure(
                        function,
                        [(variant, variant_type())],
                        ty,
                        Location::new_synthesized(),
                    ),
                    ty,
                ))
            };

        // derive tuple, record, variant serialization
        let mut locals = vec![local("variant", variant_type())];
        let l_variant_id = LocalDeclId::from_index(0);
        let ty_data = ty.data().clone();
        let load_variant = n(arena, load(0, l_variant_id), variant_type());
        let node = if let TypeKind::Tuple(tys) = ty_data {
            /*
            Example source code for deserialization of a tuple:
            impl Deserialize {
                fn deserialize(v: Variant) -> (_, _) {
                    let arr = std::variant_to_array(v);
                    (
                        deserialize(arr[0]),
                        deserialize(arr[1]),
                    )
                }
            }
            */
            // extract the array payload of the array variant
            let get_array = build_variant_to_array(arena, solver, load_variant)?;
            let array_ty = array_type(variant_type());
            // store it at 1
            let (store_array, l_array_id) = store_new(
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
                    // get the array payload of the array variant
                    let get_array = n(arena, load(1, l_array_id), array_ty);
                    // get the i-th element
                    let index_kind = index_immediate(arena, get_array, i as isize);
                    let index_node = n(arena, index_kind, variant_type());
                    // deserialize the i-th element
                    build_deserialize(arena, solver, index_node, ty_i)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            // build the tuple node
            let build_tuple = n(arena, tuple(build_elements), ty);
            // assemble the final node
            Some(n(arena, block([store_array, build_tuple]), ty))
        } else if let TypeKind::Record(fields) = ty_data {
            /*
            Example source code for deserialization of a record:
            impl Deserialize {
                fn deserialize(v: Variant) -> {a: _, b: _} {
                    let o = std::variant_to_object(v);
                    {
                        a: deserialize(std::expect_variant_object_entry(arr, "a")),
                        b: deserialize(std::expect_variant_object_entry(arr, "b")),
                    }
                }
            }
            */
            // extract the array payload of the array variant
            let get_object = build_variant_to_object(arena, solver, load_variant)?;
            let object_ty = object_payload_type();
            // store it at 1
            let (store_object, l_object_id) = store_new(
                get_object,
                1,
                "object",
                MutVal::constant(),
                object_ty,
                &mut locals,
            );
            let store_object = n(arena, store_object, Type::unit());
            // build deserialization of each field
            let build_elements = fields
                .into_iter()
                .map(|(name, ty)| {
                    // get the payload of the object variant
                    let load_object = n(arena, load(1, l_object_id), object_payload_type());
                    // get the name-th element out of the object array
                    let get_entry =
                        build_expect_variant_object_entry(arena, solver, load_object, &name)?;
                    // deserialize the name-th element
                    let function = solver.solve_impl_method(trait_ref, &[ty], 0, span, arena)?;
                    Ok(n(
                        arena,
                        static_apply_pure(
                            function,
                            [(get_entry, variant_type())],
                            ty,
                            Location::new_synthesized(),
                        ),
                        ty,
                    ))
                })
                .collect::<Result<SVec2<_>, _>>()?;
            // build the record node
            let build_record = n(arena, record(build_elements), ty);
            // assemble the final node
            Some(n(arena, block([store_object, build_record]), ty))
        } else if let TypeKind::Variant(variants) = ty_data {
            // default to adjacently tagged into an object, with tag = "type", content = "data"
            /*
            impl Deserialize {
                fn deserialize(v: Variant) -> Variant1 | Variant2(x) {
                    let variant_object = std::variant_to_object(v);
                    match std::variant_to_string(std::expect_variant_object_entry(variant_object, "type")) {
                        "Variant1" => Variant1,
                        "Variant2" => {
                            Variant2(deserialize(std::expect_variant_object_entry(variant_object, "data")))
                        },
                        _ => panic!("Unknown variant tag type")
                    }
                }
            }
            */
            // extract the array payload of the array variant
            let get_object = build_variant_to_object(arena, solver, load_variant)?;
            let object_ty = object_payload_type();
            // store it at 1
            let (store_object, l_object_id) = store_new(
                get_object,
                1,
                "object",
                MutVal::constant(),
                object_ty,
                &mut locals,
            );
            let store_object = n(arena, store_object, Type::unit());
            // load the object payload from env 1
            let load_object_id = n(arena, load(1, l_object_id), object_payload_type());
            // build the type string extraction
            let get_type =
                build_expect_variant_object_entry(arena, solver, load_object_id, "type")?;
            let get_string_type = build_variant_to_string(arena, solver, get_type)?;
            // build the data extraction for each variant.
            let variant_cases = variants
                .into_iter()
                .map(|(tag, payload_ty)| {
                    let tag_value = string_value(&tag);
                    let build_variant = if payload_ty != Type::unit() {
                        // variant with payload
                        let load_object_for_data =
                            n(arena, load(1, l_object_id), object_payload_type());
                        let get_data = build_expect_variant_object_entry(
                            arena,
                            solver,
                            load_object_for_data,
                            "data",
                        )?;
                        let deserialize = build_deserialize(arena, solver, get_data, payload_ty)?;
                        n(arena, variant(tag, deserialize), ty)
                    } else {
                        // variant without payload
                        n(arena, unit_variant(tag), ty)
                    };
                    Ok((tag_value, build_variant))
                })
                .collect::<Result<Vec<_>, _>>()?;
            // build the match node
            let panic_node = build_panic(arena, solver, "Unknown variant tag type")?;
            let match_type = n(arena, case(get_string_type, variant_cases, panic_node), ty);
            // assemble the final node
            Some(n(arena, block([store_object, match_type]), ty))
        } else if let TypeKind::Named(named) = ty_data {
            let inner_ty = named.instantiated_shape();
            // deserialize the inner type
            return Ok(Some(solver.solve_impl(
                trait_ref,
                &[inner_ty],
                span,
                arena,
            )?));
        } else {
            None // deserialization of rest not yet supported
        };
        Ok(node.map(|root| {
            TraitImplId::Local(solver.add_concrete_impl_from_code(
                root,
                locals,
                trait_ref,
                input_types,
                [],
            ))
        }))
    }
}

pub fn add_to_module(to: &mut Module) {
    // Traits
    let var0_ty = Type::variable_id(0);
    use FunctionDefinition as Def;

    // Serialize trait
    let mut serialize_trait = TraitRef::new_with_self_input_type(
        SERIALIZE_TRAIT_NAME,
        "A type that can be serialized into a variant.",
        [],
        [(
            SERIALIZE_FN_NAME,
            Def::new_infer_quantifiers(
                FnType::new_by_val([var0_ty], variant_type(), EffType::empty()),
                ["self"],
                "Serialize this value into a variant.",
            ),
        )],
    );
    Arc::get_mut(&mut serialize_trait.0)
        .unwrap()
        .derives
        .push(Box::new(AlgebraicTypeSerializeDeriver));
    to.add_trait(serialize_trait);

    // Deserialize trait
    let mut deserialize_trait = TraitRef::new_with_self_input_type(
        DESERIALIZE_TRAIT_NAME,
        "A type that can be deserialized from a variant.",
        [],
        [(
            DESERIALIZE_FN_NAME,
            Def::new_infer_quantifiers(
                FnType::new_by_val(
                    [variant_type()],
                    var0_ty,
                    EffType::single_primitive(PrimitiveEffect::Fallible),
                ),
                ["variant"],
                "Deserialize a variant into a value of this type.",
            ),
        )],
    );
    Arc::get_mut(&mut deserialize_trait.0)
        .unwrap()
        .derives
        .push(Box::new(AlgebraicTypeDeserializeDeriver));
    to.add_trait(deserialize_trait);

    // Trait implementations for basic types are in the prelude.
}

// Build a node that fetches the panic function node from the trait solver, importing it if necessary.
fn build_panic(
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
    message: &str,
) -> Result<NodeId, InternalCompilationError> {
    use ir_syn::*;
    let span = Location::new_synthesized();

    // helpers to synthesize IR
    let n = |arena: &mut NodeArena, kind, ty| {
        arena.alloc(ir::Node::new(kind, ty, EffType::empty(), span))
    };

    let build_string = n(arena, native_str(message), string_type());
    let function = solver.get_function(span, &module::Path::single_str("std"), ustr("panic"))?;
    Ok(n(
        arena,
        static_apply_pure(
            function,
            [(build_string, string_type())],
            Type::never(),
            span,
        ),
        Type::never(),
    ))
}

fn build_variant_to_array(
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
    variant_node: NodeId,
) -> Result<NodeId, InternalCompilationError> {
    build_variant_to_x(
        arena,
        solver,
        "array",
        array_type(variant_type()),
        variant_node,
    )
}

fn build_variant_to_object(
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
    variant_node: NodeId,
) -> Result<NodeId, InternalCompilationError> {
    build_variant_to_x(arena, solver, "object", object_payload_type(), variant_node)
}

fn build_variant_to_string(
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
    variant_node: NodeId,
) -> Result<NodeId, InternalCompilationError> {
    build_variant_to_x(arena, solver, "string", string_type(), variant_node)
}

fn build_variant_to_x(
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
    what: &str,
    ret_ty: Type,
    variant_node: NodeId,
) -> Result<NodeId, InternalCompilationError> {
    use ir_syn::*;
    let span = Location::new_synthesized();

    // helpers to synthesize IR
    let n = |arena: &mut NodeArena, kind, ty| {
        arena.alloc(ir::Node::new(kind, ty, EffType::empty(), span))
    };

    let function = solver.get_function(
        span,
        &module::Path::single_str("std"),
        ustr(&format!("variant_to_{what}")),
    )?;
    Ok(n(
        arena,
        static_apply_pure(function, [(variant_node, variant_type())], ret_ty, span),
        ret_ty,
    ))
}

// Build a node that gets an entry from a variant object payload [(string, Variant)].
fn build_expect_variant_object_entry(
    arena: &mut NodeArena,
    solver: &mut TraitSolver,
    fields: NodeId,
    name: &str,
) -> Result<NodeId, InternalCompilationError> {
    use ir_syn::*;
    let span = Location::new_synthesized();

    // types
    let element_ty = tuple_type([string_type(), variant_type()]);
    let payload_ty = array_type(element_ty);

    // helpers to synthesize IR
    let n = |arena: &mut NodeArena, kind, ty| {
        arena.alloc(ir::Node::new(kind, ty, EffType::empty(), span))
    };

    let name_node = n(arena, native_str(name), string_type());
    let function = solver.get_function(
        span,
        &module::Path::single_str("std"),
        ustr("expect_variant_object_entry"),
    )?;
    Ok(n(
        arena,
        static_apply_pure(
            function,
            [(fields, payload_ty), (name_node, string_type())],
            variant_type(),
            span,
        ),
        variant_type(),
    ))
}
