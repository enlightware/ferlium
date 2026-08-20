// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    Location,
    module::{self, Module, ModuleId},
    parser::location::SourceTable,
};

pub mod array_type;
pub use array_type as array;
pub mod buffer;
pub mod cast;
pub mod core;
pub mod core_traits_names;
mod data_text;
pub mod data_value;
pub mod default;
pub mod empty;
pub mod flow;
pub mod hash;
mod json;
pub mod logic;
pub mod math;
pub mod mem;
pub mod option;
pub mod ordering;
pub(crate) mod prelude;
mod product_value_deriver;
pub mod serde;
pub mod string;
pub mod value;

pub(crate) static STD_MODULE_ID: ModuleId = ModuleId::new(0);

pub fn std_module(source_table: &mut SourceTable) -> Module {
    build_std(&mut CompilingStdSourceLoader { source_table })
}

/// Supplies the three Ferlium-source checkpoints interleaved with native std registration.
///
/// The ordinary implementation compiles the embedded sources. A compiled-std snapshot loader
/// restores the corresponding semantic deltas instead, while the surrounding Rust registrations
/// still run in their original order and reconstruct process-local native objects.
pub(crate) trait StdSourceLoader {
    fn declare_traits(&mut self, module: Module) -> Module;
    fn add_core(&mut self, module: Module) -> Module;
    fn add_serialization(&mut self, module: Module) -> Module;
}

struct CompilingStdSourceLoader<'a> {
    source_table: &'a mut SourceTable,
}

impl StdSourceLoader for CompilingStdSourceLoader<'_> {
    fn declare_traits(&mut self, module: Module) -> Module {
        prelude::declare_traits(module, self.source_table, STD_MODULE_ID)
    }

    fn add_core(&mut self, module: Module) -> Module {
        prelude::add_ferlium_core(module, self.source_table, STD_MODULE_ID)
    }

    fn add_serialization(&mut self, module: Module) -> Module {
        prelude::add_ferlium_serialization_prelude(module, self.source_table, STD_MODULE_ID)
    }
}

pub(crate) fn build_std(loader: &mut impl StdSourceLoader) -> Module {
    let mut module = Module::new(STD_MODULE_ID, module::Path::single_str("std"));
    // Built-in or derivable
    value::add_to_module(&mut module);
    default::add_to_module(&mut module);
    cast::add_to_module(&mut module);
    core::add_to_module(&mut module);
    hash::add_to_module(&mut module);
    empty::add_to_module(&mut module);
    flow::add_to_module(&mut module);
    module = loader.declare_traits(module);
    // mem::add_to_module(&mut module);
    logic::add_to_module(&mut module);
    math::add_to_module(&mut module);
    buffer::add_to_module(&mut module);
    string::add_to_module(&mut module);
    module = loader.add_core(module);
    data_value::set_data_value_type_def(data_value::find_data_value_type_def(&module));
    serde::add_to_module(&mut module);
    json::add_to_module(&mut module);
    data_text::add_to_module(&mut module);
    loader.add_serialization(module)
}

pub fn new_module_using_std(module_id: ModuleId, path: module::Path) -> Module {
    let mut new_module = Module::new(module_id, path);
    new_module.add_wildcard_use(module::Path::single_str("std"), Location::new_synthesized());
    new_module
}
