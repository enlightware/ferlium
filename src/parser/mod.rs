// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use lalrpop_util::lalrpop_mod;

pub mod escapes;
pub mod helpers;
pub mod location;

lalrpop_mod!(
    #[allow(clippy::ptr_arg,clippy::type_complexity,clippy::needless_return)]
    #[rustfmt::skip]
    grammar,
    "/parser/parser.rs"
);

pub(crate) use grammar::*;
pub(crate) use helpers::describe_parse_error;
