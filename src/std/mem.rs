// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
// Note: disabled for now until we have a borrow checker
// use crate::{module::Module, value::Value};

// use ustr::ustr;

// pub fn swap(a: &mut Value, b: &mut Value) {
//     std::mem::swap(a, b);
// }

// pub fn add_to_module(to: &mut Module) {
//     to.functions.insert(
//         ustr("swap"),
//         BinaryNativeFnMMP::description_gen0_gen0(swap),
//     );
// }
