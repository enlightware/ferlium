// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::{str::FromStr, sync::Arc};

use crate::{
    containers::{b, SVec2},
    effects::EffType,
    error::InternalCompilationError,
    function::{FunctionDefinition, ScriptFunction},
    ir::{self, Node},
    ir_syn,
    module::Module,
    r#trait::{Deriver, TraitRef},
    r#type::{tuple_type, FnType, Type, TypeKind},
    std::{
        array::array_type,
        math::int_type,
        string::{string_type, String as Str},
        variant::variant_object_entry_type,
    },
    trait_solver::{ConcreteTraitImpl, TraitImpls},
    type_like::TypeLike,
    value::{ustr_to_isize, Value},
    Location,
};

use super::variant::variant_type;

pub const SERIALIZE_TRAIT_NAME: &str = "Serialize";
pub const DESERIALIZE_TRAIT_NAME: &str = "Deserialize";

pub const SERIALIZE_FN_NAME: &str = "serialize";
pub const DESERIALIZE_FN_NAME: &str = "deserialize";

#[derive(Debug, Clone)]
struct ProductTypeDeriver;
impl Deriver for ProductTypeDeriver {
    fn derive_impl(
        &self,
        trait_ref: &TraitRef,
        input_types: &[Type],
        span: Location,
        impls: &mut TraitImpls,
    ) -> Result<Option<ConcreteTraitImpl>, InternalCompilationError> {
        use ir_syn::*;

        // safety checks
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        // helpers to synthesize IR
        let n = |kind, ty| ir::Node::new(kind, ty, EffType::empty(), span);

        // helper to create a concrete trait implementation from a single function defined by code
        let concrete_trait_from_code = |code: Node| {
            let function = ScriptFunction::new(code);
            let functions = Value::tuple([Value::function(b(function))]);
            ConcreteTraitImpl::from_functions(functions)
        };

        // helper to create the concrete trait implementation for sequences
        let build_serialize_to_seq = |nodes, tag| {
            let array_ty = array_type(variant_type());
            let array = n(array(nodes), array_ty);
            let payload_ty = tuple_type([array_ty]);
            let payload = n(tuple([array]), payload_ty);
            let code = n(variant(tag, payload), variant_type());
            concrete_trait_from_code(code)
        };

        // helper to build the serialization a member
        let mut build_serialize_fn = |index, ty| {
            // load function parameter (that is a tuple in memory)
            let load = n(load(0), ty);
            // project the i-th element
            let project = n(project(load, index), ty);
            // serialize the i-th element
            let functions = impls.get_functions(trait_ref, &[ty], span)?;
            let function = functions.unwrap_fn_tuple_index(0);
            let apply = n(
                ir_syn::static_apply(
                    function.clone(),
                    FnType::new_by_val([ty], variant_type(), EffType::empty()),
                    span,
                    vec![project],
                ),
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
                    build_serialize_fn(index, ty_i)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            Ok(Some(build_serialize_to_seq(nodes, "Array")))
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
                    let tag = n(native(Str::from_str(&name).unwrap()), string_type());
                    let payload = build_serialize_fn(index, ty_i)?;
                    let entry = n(tuple([tag, payload]), variant_object_entry_type());
                    Ok(entry)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            Ok(Some(build_serialize_to_seq(nodes, "Object")))
        } else if let TypeKind::Variant(variants) = ty_data {
            // default to adjacently tagged into an object, with tag = "type", content = "data"
            /*
            impl Serialize {
                fn serialize(v: V) {
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
                    let tag_node = n(
                        native(Str::from_str(&tag.to_string()).unwrap()),
                        string_type(),
                    );
                    let tag_tuple_ty = tuple_type([string_type()]);
                    let tag_tuple_node = n(tuple([tag_node]), tag_tuple_ty);
                    let tag_variant_node = n(variant("String", tag_tuple_node), variant_type());
                    let tag_entry = n(
                        tuple([
                            n(native(Str::from_str("type").unwrap()), string_type()),
                            tag_variant_node,
                        ]),
                        variant_object_entry_type(),
                    );
                    let array_ty = array_type(variant_object_entry_type());
                    let array = if payload_ty != Type::unit() {
                        // variant with payload
                        let payload_node = build_serialize_fn(0, payload_ty)?;
                        let payload_entry = n(
                            tuple([
                                n(native(Str::from_str("data").unwrap()), string_type()),
                                payload_node,
                            ]),
                            variant_object_entry_type(),
                        );
                        n(array([tag_entry, payload_entry]), array_ty)
                    } else {
                        // variant without payload
                        n(array([tag_entry]), array_ty)
                    };
                    let payload_ty = tuple_type([array_ty]);
                    let payload = n(tuple([array]), payload_ty);
                    let code = n(variant("Object", payload), variant_type());
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
            Ok(Some(concrete_trait_from_code(code)))
        } else if let TypeKind::Named(named) = ty_data {
            let ty_def = named.def;
            // serialize the inner type
            Ok(Some(ConcreteTraitImpl::from_functions(
                impls.get_functions(trait_ref, &[ty_def.shape], span)?,
            )))
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
                Ok(Some(ConcreteTraitImpl::from_functions(
                    impls.get_functions(trait_ref, &[ty_def.shape], span)?,
                )))
            }
            */
        } else {
            Ok(None)
        }
    }
}

pub fn add_to_module(to: &mut Module) {
    // Traits
    let var0_ty = Type::variable_id(0);
    use FunctionDefinition as Def;
    let mut serialize_trait = TraitRef::new(
        SERIALIZE_TRAIT_NAME,
        1,
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
        .push(Box::new(ProductTypeDeriver));
    to.traits.push(serialize_trait);
    let deserialize_trait = TraitRef::new(
        DESERIALIZE_TRAIT_NAME,
        1,
        [],
        [(
            DESERIALIZE_FN_NAME,
            Def::new_infer_quantifiers(
                FnType::new_by_val([variant_type()], var0_ty, EffType::empty()),
                ["variant"],
                "Deserialize a variant into a value of this type.",
            ),
        )],
    );
    to.traits.push(deserialize_trait);

    // Trait implementations are in the prelude.
}
