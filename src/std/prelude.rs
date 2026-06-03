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
    // The prelude code is split into multiple files to allow dependencies between
    // trait implementations while keeping std construction as one ordered step.
    add_chunks(
        to,
        source_table,
        module_id,
        [
            // Comparison operators are needed by the array primitives below.
            prelude!("comparison.fer"),
            // Defines the array type and primitives used by array indexing.
            // The compiler depends on array being the first type def in std (index 0).
            prelude!("array_type.fer"),
            // Core trait implementations.
            prelude!("core_impls.fer"),
            // Defines the Ferlium Array implementation.
            prelude!("array.fer"),
            // These functions depend on array iterator being available.
            prelude!("core_impls_dependent.fer"),
            // HashSet and HashMap are ordinary collection types; serde impls are loaded later.
            prelude!("hash_collections.fer"),
            // DataValue is the serialization data model; native serde registration follows it.
            prelude!("data_value.fer"),
        ],
        "add Ferlium core to module",
    )
}

pub fn add_ferlium_serialization_prelude(
    to: Module,
    source_table: &mut SourceTable,
    module_id: ModuleId,
) -> Module {
    let codes = [
        prelude!("serde_impl.fer"),
        // Json depends on data-value object helpers being available.
        prelude!("json.fer"),
        prelude!("data_text.fer"),
    ];
    add_chunks(
        to,
        source_table,
        module_id,
        codes,
        "add serialization prelude to module",
    )
}
