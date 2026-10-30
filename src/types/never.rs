// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::fmt::{self, Display};

use ustr::Ustr;

use crate::{Location, compiler::error::InternalCompilationError, internal_compilation_error};

/// The name under which the bottom type is displayed.
pub(crate) const NEVER_NAME: &str = "never";

/// Rejects a variant tag or type name that would display like the bottom type.
pub(crate) fn reject_reserved_name(
    name: Ustr,
    span: Location,
) -> Result<(), InternalCompilationError> {
    if name == NEVER_NAME {
        Err(internal_compilation_error!(ReservedName { name, span }))
    } else {
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Never {}

impl Display for Never {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}
