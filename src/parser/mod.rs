// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

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
