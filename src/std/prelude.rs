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
    module::{Module, ModuleId},
    parser::location::SourceTable,
};

macro_rules! prelude {
    ($name:literal) => {
        ($name, include_str!(concat!("prelude/", $name)))
    };
}

fn add_chunks(
    mut to: Module,
    source_table: &mut SourceTable,
    module_id: ModuleId,
    chunks: impl IntoIterator<Item = (&'static str, &'static str)>,
    failure_context: &str,
) -> Module {
    let other_modules = Modules::default();
    for (name, code) in chunks {
        to = add_code_to_module(name, code, to, module_id, &other_modules, source_table)
            .unwrap_or_else(|e| {
                panic!(
                    "Failed to {failure_context}: {}",
                    FormatWithData::new(&e, source_table)
                )
            });
    }
    to
}

pub fn declare_traits(to: Module, source_table: &mut SourceTable, module_id: ModuleId) -> Module {
    add_chunks(
        to,
        source_table,
        module_id,
        [prelude!("core_traits.fer")],
        "declare traits to module",
    )
}

pub fn add_ferlium_core(to: Module, source_table: &mut SourceTable, module_id: ModuleId) -> Module {
    add_chunks(
        to,
        source_table,
        module_id,
        [
            // Comparison operators are needed by the array primitives below.
            prelude!("comparison.fer"),
            // Defines the array type and primitives used by array indexing.
            prelude!("array_type.fer"),
        ],
        "add Ferlium core to module",
    )
}

pub fn add_ferlium_prelude(
    to: Module,
    source_table: &mut SourceTable,
    module_id: ModuleId,
) -> Module {
    // The prelude code is split into multiple parts
    // to allow dependencies between trait implementations.
    let codes = [
        // Then most of the core traits and generic iterator adaptors.
        prelude!("core_impls.fer"),
        // Defines the Ferlium Array implementation.
        prelude!("array.fer"),
        // Array serde depends on the array Value blanket impl being visible.
        prelude!("array_serde.fer"),
        // These functions depend on array iterator being available.
        prelude!("core_impls_dependent.fer"),
        // Keep hash-based containers isolated so they can be toggled during step-by-step debugging.
        prelude!("hash_collections.fer"),
        // Json depends on expect_variant_object_entry being available.
        prelude!("json.fer"),
    ];
    add_chunks(to, source_table, module_id, codes, "add prelude to module")
}
