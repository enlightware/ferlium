// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use crate::{
    hir::function::CallableDefinition,
    module::Module,
    std::product_value_deriver::ProductValueDeriver,
    types::effects::EffType,
    types::r#trait::Trait,
    types::r#type::{FnType, Type},
};

use CallableDefinition as Def;

pub fn empty_trait() -> Trait {
    let var_ty = Type::variable_id(0);
    Trait::new_with_self_input_type(
        "Empty",
        "A type with a canonical empty value, typically used as the identity for concatenation.",
        [],
        [(
            "empty",
            Def::new_infer_quantifiers(
                FnType::new_by_val([], var_ty, EffType::empty()),
                [],
                "Returns the empty value for this type.",
            ),
        )],
    )
    .with_deriver(ProductValueDeriver)
}

pub fn add_to_module(to: &mut Module) {
    to.add_trait(empty_trait());
}
