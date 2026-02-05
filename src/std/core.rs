// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::sync::LazyLock;

use crate::{module::Module, r#trait::TraitRef, r#type::Type};

pub static REPR_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    TraitRef::new_with_self_input_type(
        "Repr",
        "Marker trait for types whose value is the same representation as one of another type. Used in Rust-style struct and enums (new types) to allow matches and projections on the underlying representation.",
        ["Is"],
        [],
    )
});

pub fn add_to_module(to: &mut Module) {
    // Add the unit type `()`
    to.add_type_alias_str("()", Type::unit());

    // Add the `Repr` trait
    to.add_trait(REPR_TRAIT.clone());

    // All types implement `Repr` to themselves, but to avoid overlapping
    // blanket implementations, this is implemented manually in the code.
    // let ty_var0 = Type::variable_id(0);
    // to.impls.add_blanket(coercible_trait, [ty_var0], [ty_var0], 1, [], []);
}
