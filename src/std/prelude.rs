// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    add_code_to_module,
    module::{Module, Modules},
};
use indoc::indoc;

pub fn add_to_module(to: &mut Module) {
    add_code_to_module(
        indoc! {"
            fn lt(lhs, rhs) {
                match cmp(lhs, rhs) {
                    Less => true,
                    _ => false,
                }
            }

            fn le(lhs, rhs) {
                match cmp(lhs, rhs) {
                    Greater => false,
                    _ => true,
                }
            }

            fn gt(lhs, rhs) {
                match cmp(lhs, rhs) {
                    Greater => true,
                    _ => false,
                }
            }

            fn ge(lhs, rhs) {
                match cmp(lhs, rhs) {
                    Less => false,
                    _ => true,
                }
            }

            fn min(lhs, rhs) {
                match cmp(lhs, rhs) {
                    Less => lhs,
                    _ => rhs,
                }
            }

            fn max(lhs, rhs) {
                match cmp(lhs, rhs) {
                    Greater => lhs,
                    _ => rhs,
                }
            }

            fn clamp(value, min_bound, max_bound) {
                if gt(min_bound, max_bound) {
                    panic(\"min_bound must be less than or equal to max_bound\")
                } else {
                    max(min_bound, min(value, max_bound))
                }
            }
        "},
        to,
        &Modules::new(),
    )
    .unwrap();
}
