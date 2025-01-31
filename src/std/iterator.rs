// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::r#type::{tuple_type, Type};

use super::option::gen_option_type;

// Note: not used currently until we have algebraic data types in the compiler
pub fn iterator_type() -> Type {
    Type::function_by_val(&[], tuple_type([gen_option_type(), Type::new_local(0)]))
}
