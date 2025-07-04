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
    ir, ir_syn,
    module::Module,
    r#trait::{Deriver, TraitRef},
    r#type::{tuple_type, FnType, Type, TypeKind},
    std::{
        array::array_type,
        string::{string_type, String as Str},
    },
    trait_solver::{ConcreteTraitImpl, TraitImpls},
    type_like::TypeLike,
    value::Value,
    Location,
};

use super::variant::script_variant_type;

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

        // helper to create the concrete trait implementation for sequences
        let build_serialize_to_seq = |nodes| {
            let array_ty = array_type(script_variant_type());
            let array = n(array(nodes), array_ty);
            let payload_ty = tuple_type([array_ty]);
            let payload = n(tuple([array]), payload_ty);
            let code = n(variant("Seq", payload), script_variant_type());
            let function = ScriptFunction::new(code);
            let functions = Value::tuple([Value::function(b(function))]);
            ConcreteTraitImpl {
                output_tys: vec![],
                functions,
            }
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
                    FnType::new_by_val([ty], script_variant_type(), EffType::empty()),
                    span,
                    vec![project],
                ),
                script_variant_type(),
            );
            Ok(apply)
        };

        // derive tuple and record serialization
        let ty_data = ty.data().clone();
        if let TypeKind::Tuple(tys) = ty_data {
            /*
            Example source code for serialization of a tuple:
            impl Serialize {
                fn serialize(t: (_, _)) {
                    Seq([
                        serialize(t.0),
                        serialize(t.1),
                    ])
                }
            }

            Example corresponding IR:
            variant with tag: Seq
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
            Ok(Some(build_serialize_to_seq(nodes)))
        } else if let TypeKind::Record(fields) = ty_data {
            /*
            Example source code for serialization of a record:
            impl Serialize {
                fn serialize(r: {a: _, b: _}) {
                    Seq([
                        Seq([
                            String("a"),
                            serialize(r.0)
                        ]),
                        Seq([
                            String("b"),
                            serialize(r.1)
                        ]),
                    ])
                }
            }

            Example corresponding IR:
            variant with tag: Seq
                build tuple (
                    build array [
                        variant with tag: Seq
                            build tuple (
                                build array [
                                    variant with tag: String
                                        value: "a"
                                    serialize(r.0),
                                ]
                            ),
                        variant with tag: Seq
                            build tuple (
                                build array [
                                    variant with tag: String
                                        value: "b"
                                    serialize(r.1),
                                ]
                            ),
                    ]
                )
            */
            let nodes = fields
                .into_iter()
                .enumerate()
                .map(|(index, (name, ty_i))| {
                    // variant with tag: String and name
                    let tag = n(native(Str::from_str(&name).unwrap()), string_type());
                    let tag_payload_ty = tuple_type([string_type()]);
                    let tag_payload = n(tuple([tag]), tag_payload_ty);
                    let tag = n(variant("String", tag_payload), script_variant_type());
                    // serialize the i-th element
                    let payload = build_serialize_fn(index, ty_i)?;
                    // field entry
                    let array_ty = array_type(script_variant_type());
                    let array = n(array([tag, payload]), array_ty);
                    let variant_payload_ty = tuple_type([array_ty]);
                    let variant_payload = n(tuple([array]), variant_payload_ty);
                    let entry = n(variant("Seq", variant_payload), script_variant_type());
                    Ok(entry)
                })
                .collect::<Result<SVec2<_>, _>>()?;
            Ok(Some(build_serialize_to_seq(nodes)))
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
                FnType::new_by_val([var0_ty], script_variant_type(), EffType::empty()),
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
                FnType::new_by_val([script_variant_type()], var0_ty, EffType::empty()),
                ["variant"],
                "Deserialize a variant into a value of this type.",
            ),
        )],
    );
    to.traits.push(deserialize_trait);

    // Trait implementations are in the prelude.
}
