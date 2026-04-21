// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::ustr;

use crate::{
    cached_ty,
    r#type::{Type, variant_type},
    value::Value,
};

pub const ORDERING_LESS: &str = "Less";
pub const ORDERING_EQUAL: &str = "Equal";
pub const ORDERING_GREATER: &str = "Greater";

pub fn ordering_type() -> Type {
    cached_ty!(|| variant_type([
        (ORDERING_LESS, Type::unit()),
        (ORDERING_EQUAL, Type::unit()),
        (ORDERING_GREATER, Type::unit()),
    ]))
}

pub(crate) fn compare<T>(lhs: T, rhs: T) -> Value
where
    T: std::cmp::Ord,
{
    use std::cmp::Ordering::*;
    match lhs.cmp(&rhs) {
        Less => Value::unit_variant(ustr(ORDERING_LESS)),
        Equal => Value::unit_variant(ustr(ORDERING_EQUAL)),
        Greater => Value::unit_variant(ustr(ORDERING_GREATER)),
    }
}
