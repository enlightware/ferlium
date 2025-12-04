// Copyright 2025 Enlightware GmbH
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
    ir::{self, Node},
    ir_syn,
    module::{Module, TraitImplId},
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
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use ir_syn::*;

        // safety checks
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        // helpers to synthesize IR
        let n = |kind, ty| ir::Node::new(kind, ty, EffType::empty(), span);

        // helper to create the concrete trait implementation for sequences
        let build_serialize_to_seq = |nodes, tag, solver: &mut TraitSolver| {
            let array_ty = array_type(variant_type());
            let array = n(array(nodes), array_ty);
            let payload_ty = tuple_type([array_ty]);
            let payload = n(tuple([array]), payload_ty);
            let code = n(variant(ustr(tag), payload), variant_type());
            TraitImplId::Local(solver.add_concrete_impl_from_code(code, trait_ref, input_types, []))
        };

        // helper to build the serialization of a member of a tuple
        let mut build_serialize_i = |index, ty| {
            // load function parameter (that is a tuple in memory)
            let load = n(load(0), ty);
            // project the i-th element
            let project = n(project(load, index), ty);
            // serialize the i-th element
            let function = solver.solve_impl_method(trait_ref, &[ty], 0, span)?;
            let apply = n(
                static_apply_pure(function, [(project, ty)], variant_type(), span),
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
                    build_serialize_i(index, ty_i)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            Ok(Some(build_serialize_to_seq(nodes, "Array", solver)))
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
                    let tag = n(native_str(&name), string_type());
                    let payload = build_serialize_i(index, ty_i)?;
                    let entry = n(tuple([tag, payload]), variant_object_entry_type());
                    Ok(entry)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            Ok(Some(build_serialize_to_seq(nodes, "Object", solver)))
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
                    let tag_node = n(native_str(&tag), string_type());
                    let tag_tuple_ty = tuple_type([string_type()]);
                    let tag_tuple_node = n(tuple([tag_node]), tag_tuple_ty);
                    let tag_variant_node =
                        n(variant(ustr("String"), tag_tuple_node), variant_type());
                    let tag_entry = n(
                        tuple([n(native_str("type"), string_type()), tag_variant_node]),
                        variant_object_entry_type(),
                    );
                    let array_ty = array_type(variant_object_entry_type());
                    let array = if payload_ty != Type::unit() {
                        // variant with payload
                        let payload_node = build_serialize_i(0, payload_ty)?;
                        let payload_entry = n(
                            tuple([n(native_str("data"), string_type()), payload_node]),
                            variant_object_entry_type(),
                        );
                        n(array([tag_entry, payload_entry]), array_ty)
                    } else {
                        // variant without payload
                        n(array([tag_entry]), array_ty)
                    };
                    let payload_ty = tuple_type([array_ty]);
                    let payload = n(tuple([array]), payload_ty);
                    let code = n(variant(ustr("Object"), payload), variant_type());
                    let tag_value = Value::native(ustr_to_isize(tag));
                    Ok((tag_value, code))
                })
                .collect::<Result<Vec<_>, _>>()?;
            // build the match node
            let load = n(load(0), ty);
            let extract_tag = n(extract_tag(load), int_type());
            let code = n(
                case_from_complete_alternatives(extract_tag, alternatives),
                variant_type(),
            );
            let local_impl_id =
                solver.add_concrete_impl_from_code(code, trait_ref, input_types, []);
            Ok(Some(TraitImplId::Local(local_impl_id)))
        } else if let TypeKind::Named(named) = ty_data {
            let ty_def = named.def;
            // serialize the inner type
            Ok(Some(solver.solve_impl(trait_ref, &[ty_def.shape], span)?))
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
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use ir_syn::*;

        // safety checks
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        // helpers to synthesize IR
        let n = |kind, ty| ir::Node::new(kind, ty, EffType::empty(), span);

        // build the deserialization of a variant into a value of type `ty`
        let build_deserialize = |solver: &mut TraitSolver, variant: Node, ty: Type| {
            let function = solver.solve_impl_method(trait_ref, &[ty], 0, span)?;
            Ok(n(
                static_apply_pure(function, [(variant, variant_type())], ty, span),
                ty,
            ))
        };

        // derive tuple, record, variant serialization
        let ty_data = ty.data().clone();
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
            let load_variant = n(load(0), variant_type());
            let get_array = build_variant_to_array(solver, load_variant, span)?;
            let array_ty = array_type(variant_type());
            // store it at 1
            let store_array = n(store(get_array, 1, ustr("array")), Type::unit());
            // build deserialization of each element
            let build_elements = tys
                .into_iter()
                .enumerate()
                .map(|(i, ty_i)| {
                    // get the array payload of the array variant
                    let get_array = n(load(1), array_ty);
                    // get the i-th element
                    let index = n(index_immediate(get_array, i as isize), variant_type());
                    // deserialize the i-th element
                    build_deserialize(solver, index, ty_i)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            // build the tuple node
            let build_tuple = n(tuple(build_elements), ty);
            // assemble the final node
            Some(n(block([store_array, build_tuple]), ty))
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
            let load_variant = n(load(0), variant_type());
            let get_object = build_variant_to_object(solver, load_variant, span)?;
            // store it at 1
            let store_object = n(store(get_object, 1, ustr("object")), Type::unit());
            // build deserialization of each field
            let build_elements = fields
                .into_iter()
                .map(|(name, ty)| {
                    // get the payload of the object variant
                    let load_object = n(load(1), object_payload_type());
                    // get the name-th element out of the object array
                    let get_entry =
                        build_expect_variant_object_entry(solver, load_object, &name, span)?;
                    // deserialize the name-th element
                    let function = solver.solve_impl_method(trait_ref, &[ty], 0, span)?;
                    Ok(n(
                        static_apply_pure(function, [(get_entry, variant_type())], ty, span),
                        ty,
                    ))
                })
                .collect::<Result<SVec2<_>, _>>()?;
            // build the record node
            let build_record = n(record(build_elements), ty);
            // assemble the final node
            Some(n(block([store_object, build_record]), ty))
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
            let load_variant = n(load(0), variant_type());
            let get_object = build_variant_to_object(solver, load_variant, span)?;
            // store it at 1
            let store_object = n(store(get_object, 1, ustr("object")), Type::unit());
            // load the object payload from env 1
            let load_object = n(load(1), object_payload_type());
            // build the type string extraction
            let get_type =
                build_expect_variant_object_entry(solver, load_object.clone(), "type", span)?;
            let get_string_type = build_variant_to_string(solver, get_type, span)?;
            // build the data extraction for each variant.
            let variant_cases = variants
                .into_iter()
                .map(|(tag, payload_ty)| {
                    let tag_value = string_value(&tag);
                    let build_variant = if payload_ty != Type::unit() {
                        // variant with payload
                        let get_data = build_expect_variant_object_entry(
                            solver,
                            load_object.clone(),
                            "data",
                            span,
                        )?;
                        let deserialize = build_deserialize(solver, get_data, payload_ty)?;
                        n(variant(tag, deserialize), ty)
                    } else {
                        // variant without payload
                        n(unit_variant(tag), ty)
                    };
                    Ok((tag_value, build_variant))
                })
                .collect::<Result<Vec<_>, _>>()?;
            // build the match node
            let match_type = n(
                case(
                    get_string_type,
                    variant_cases,
                    build_panic(solver, span, "Unknown variant tag type")?,
                ),
                ty,
            );
            // assemble the final node
            Some(n(block([store_object, match_type]), ty))
        } else if let TypeKind::Named(named) = ty_data {
            let ty_def = named.def;
            // deserialize the inner type
            return Ok(Some(solver.solve_impl(trait_ref, &[ty_def.shape], span)?));
        } else {
            None // deserialization of rest not yet supported
        };
        Ok(node.map(|n| {
            TraitImplId::Local(solver.add_concrete_impl_from_code(n, trait_ref, input_types, []))
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
                ["value"],
                "Serialize this value into a variant.",
            ),
        )],
    );
    Arc::get_mut(&mut serialize_trait.0)
        .unwrap()
        .derives
        .push(Box::new(AlgebraicTypeSerializeDeriver));
    to.traits.push(serialize_trait);

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
    to.traits.push(deserialize_trait);

    // Trait implementations for basic types are in the prelude.
}

// Build a node that fetches the panic function node from the trait solver, importing it if necessary.
fn build_panic(
    solver: &mut TraitSolver,
    span: Location,
    message: &str,
) -> Result<Node, InternalCompilationError> {
    use ir_syn::*;
    // helpers to synthesize IR
    let n = |kind, ty| ir::Node::new(kind, ty, EffType::empty(), span);

    let build_string = n(native_str(message), string_type());
    let function = solver.get_function(ustr("std"), ustr("panic"))?;
    Ok(n(
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
    solver: &mut TraitSolver,
    variant_node: Node,
    span: Location,
) -> Result<Node, InternalCompilationError> {
    build_variant_to_x(
        solver,
        "array",
        array_type(variant_type()),
        variant_node,
        span,
    )
}

fn build_variant_to_object(
    solver: &mut TraitSolver,
    variant_node: Node,
    span: Location,
) -> Result<Node, InternalCompilationError> {
    build_variant_to_x(solver, "object", object_payload_type(), variant_node, span)
}

fn build_variant_to_string(
    solver: &mut TraitSolver,
    variant_node: Node,
    span: Location,
) -> Result<Node, InternalCompilationError> {
    build_variant_to_x(solver, "string", string_type(), variant_node, span)
}

fn build_variant_to_x(
    solver: &mut TraitSolver,
    what: &str,
    ret_ty: Type,
    variant_node: Node,
    span: Location,
) -> Result<Node, InternalCompilationError> {
    use ir_syn::*;
    // helpers to synthesize IR
    let n = |kind, ty| ir::Node::new(kind, ty, EffType::empty(), span);

    let function = solver.get_function(ustr("std"), ustr(&format!("variant_to_{what}")))?;
    Ok(n(
        static_apply_pure(function, [(variant_node, variant_type())], ret_ty, span),
        ret_ty,
    ))
}

// Build a node that gets an entry from a variant object payload [(string, Variant)].
fn build_expect_variant_object_entry(
    solver: &mut TraitSolver,
    fields: Node,
    name: &str,
    span: Location,
) -> Result<Node, InternalCompilationError> {
    use ir_syn::*;

    // types
    let element_ty = tuple_type([string_type(), variant_type()]);
    let payload_ty = array_type(element_ty);

    // helpers to synthesize IR
    let n = |kind, ty| ir::Node::new(kind, ty, EffType::empty(), span);

    let name = n(native_str(name), string_type());
    let function = solver.get_function(ustr("std"), ustr("expect_variant_object_entry"))?;
    Ok(n(
        static_apply_pure(
            function,
            [(fields, payload_ty), (name, string_type())],
            variant_type(),
            span,
        ),
        variant_type(),
    ))
}
