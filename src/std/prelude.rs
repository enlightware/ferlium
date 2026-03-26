// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    Modules, add_code_to_module,
    format::FormatWithData,
    location::SourceTable,
    module::{Module, ModuleId},
};

macro_rules! prelude {
    ($name:literal) => {
        ($name, include_str!(concat!("prelude/", $name)))
    };
}

pub fn add_to_module(
    mut to: Module,
    source_table: &mut SourceTable,
    module_id: ModuleId,
) -> Module {
    // The prelude code is split into multiple parts
    // to allow dependencies between trait implementations.
    let codes = [
        // First compiles basic comparison functions.
        prelude!("comparison.fer"),
        // Then most of the core traits.
        prelude!("core_traits.fer"),
        // These functions depend on array iterator being available.
        prelude!("core_traits_dependent.fer"),
        // Json depends on expect_variant_object_entry being available.
        prelude!("json.fer"),
    ];
    let other_modules = Modules::default();
    for (name, code) in codes {
        to = add_code_to_module(name, code, to, module_id, &other_modules, source_table)
            .unwrap_or_else(|e| {
                panic!(
                    "Failed to add prelude to module: {}",
                    FormatWithData::new(&e, source_table)
                )
            });
    }
    to
}
