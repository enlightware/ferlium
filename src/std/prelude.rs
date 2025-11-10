// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{add_code_to_module, format::FormatWithData, module::Module, module::Modules};

pub fn add_to_module(to: &mut Module) {
    // The prelude code is split into multiple parts
    // to allow dependencies between trait implementations.
    let codes = [
        // First compiles basic comparison functions.
        include_str!("prelude/comparison.fer"),
        // Then most of the core traits.
        include_str!("prelude/core_traits.fer"),
        // These functions depend on array iterator being available,
        // so they are compiled in a next batch.
        include_str!("prelude/core_traits_dependent.fer"),
    ];
    for code in codes {
        add_code_to_module(code, to, &Modules::new_empty(), true).unwrap_or_else(|e| {
            panic!(
                "Failed to add prelude to module: {}",
                FormatWithData::new(&e, &code)
            )
        });
    }
}
