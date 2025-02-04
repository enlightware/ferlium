// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    cached_ty,
    effects::EffType,
    function::FunctionDefinition,
    module::Module,
    r#trait::TraitRef,
    r#type::{variant_type, FnType, Type},
};

pub const ORD_TRAIT_NAME: &str = "Ord";

pub const ORDERING_LESS: &str = "Less";
pub const ORDERING_EQUAL: &str = "Equal";
pub const ORDERING_GREATER: &str = "Greater";

pub fn ordering_type() -> Type {
    cached_ty!(|| variant_type(&[
        (ORDERING_LESS, Type::unit()),
        (ORDERING_EQUAL, Type::unit()),
        (ORDERING_GREATER, Type::unit()),
    ]))
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.types.set("Ordering", ordering_type());

    // Traits
    let var0_ty = Type::variable_id(0);
    let binary_fn_ty = FnType::new_by_val(&[var0_ty, var0_ty], ordering_type(), EffType::empty());
    use FunctionDefinition as Def;
    let ord_trait = TraitRef::new(
        ORD_TRAIT_NAME,
        1,
        0,
        [(
            "cmp",
            Def::new_infer_quantifiers(
                binary_fn_ty.clone(),
                &["lhs", "rhs"],
                "Returns an `Ordering` between `lhs` and `rhs`.",
            ),
        )],
    );
    to.traits.push(ord_trait.clone());
}
