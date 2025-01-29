// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{r#type::Type, value::Value};
use ustr::ustr;

pub fn option_type(inner: Type) -> Type {
    Type::variant(vec![(ustr("None"), Type::unit()), (ustr("Some"), inner)])
}

pub fn gen_option_type() -> Type {
    option_type(Type::variable_id(0))
}

pub fn none() -> Value {
    Value::variant(ustr("None"), Value::unit())
}

pub fn some(value: Value) -> Value {
    Value::variant(ustr("Some"), value)
}
