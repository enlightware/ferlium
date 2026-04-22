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
    location::SourceTable,
    module::{self, Module, ModuleId},
};

pub mod array;
pub mod cast;
pub mod core;
pub mod core_traits_names;
pub mod default;
pub mod empty;
pub mod flow;
pub mod io;
mod json;
pub mod logic;
pub mod math;
pub mod mem;
pub mod option;
pub mod ordering;
mod prelude;
mod product_value_deriver;
pub mod serde;
pub mod string;
pub mod value;
pub mod variant;

pub(crate) static STD_MODULE_ID: ModuleId = ModuleId(0);

pub fn std_module(source_table: &mut SourceTable) -> Module {
    let mut module = Module::new(STD_MODULE_ID);
    // Built-in or derivable
    value::add_to_module(&mut module);
    core::add_to_module(&mut module);
    default::add_to_module(&mut module);
    empty::add_to_module(&mut module);
    flow::add_to_module(&mut module);
    cast::add_to_module(&mut module);
    module = prelude::declare_traits(module, source_table, STD_MODULE_ID);
    // mem::add_to_module(&mut module);
    logic::add_to_module(&mut module);
    math::add_to_module(&mut module);
    array::add_to_module(&mut module);
    io::add_to_module(&mut module);
    string::add_to_module(&mut module);
    variant::add_to_module(&mut module);
    serde::add_to_module(&mut module);
    json::add_to_module(&mut module);
    prelude::add_impls(module, source_table, STD_MODULE_ID)
}

pub fn new_module_using_std(module_id: ModuleId) -> Module {
    let mut new_module = Module::new(module_id);
    new_module.add_wildcard_use(module::Path::single_str("std"), Location::new_synthesized());
    new_module
}
