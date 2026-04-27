// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use core::panic;
use std::fmt::{self, Display};

use enum_as_inner::EnumAsInner;
use ustr::Ustr;

use crate::parser::location::{Location, SourceTable};

use super::MutabilityMustBeContext;

/// Runtime error

#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum RuntimeErrorKind {
    Aborted(Option<String>),
    DivisionByZero,
    RemainderByZero,
    InvalidArgument(Ustr),
    ArrayAccessOutOfBounds { index: isize, len: usize },
    RecursionLimitExceeded { limit: usize },
    // TODO: add execution duration limit exhausted
}

impl Display for RuntimeErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RuntimeErrorKind::*;
        match self {
            Aborted(msg) => match msg {
                Some(msg) => write!(f, "Aborted: {msg}"),
                None => write!(f, "Aborted"),
            },
            DivisionByZero => write!(f, "Division by zero"),
            RemainderByZero => write!(f, "Remainder by zero"),
            InvalidArgument(reason) => write!(f, "Invalid argument: {reason}"),
            ArrayAccessOutOfBounds { index, len } => {
                write!(
                    f,
                    "Array access out of bounds: index {index} for length {len}"
                )
            }
            RecursionLimitExceeded { limit } => {
                write!(f, "Recursion limit exceeded: limit is {limit}")
            }
        }
    }
}

pub fn resolve_must_be_mutable_ctx(
    current_span: Location,
    reason_span: Location,
    ctx: MutabilityMustBeContext,
    source_table: &SourceTable,
) -> (Location, Location) {
    use MutabilityMustBeContext::*;
    match ctx {
        Value => (current_span, reason_span),
        FnTypeArg(index) => {
            if let Some(src) = source_table.get_source_text(reason_span.source_id()) {
                let arg_span = extract_ith_fn_arg(src, reason_span, index);
                (arg_span, current_span)
            } else {
                (current_span, reason_span)
            }
        }
    }
}

pub fn extract_ith_fn_arg(src: &str, span: Location, index: usize) -> Location {
    let fn_text = &src[span.as_range()];
    let bytes = fn_text.as_bytes();
    let mut count = 0;
    let mut args_start = fn_text.len();

    // Iterate backwards through the string within the span to find the start of the argument list
    for i in (0..fn_text.len()).rev() {
        match bytes[i] as char {
            ')' => count += 1,
            '(' => {
                count -= 1;
                if count == 0 {
                    args_start = i;
                    break;
                }
            }
            _ => {}
        }
    }

    // Extracting the arguments from the located position
    if args_start == fn_text.len() {
        return span;
    }
    let args_section = &fn_text[args_start + 1..fn_text.len() - 1]; // Strip the outer parentheses
    let mut arg_count = 0;
    let mut start = 0;

    count = 0; // Reset count for argument extraction
    for (i, char) in args_section.char_indices() {
        match char {
            '(' => count += 1,
            ')' => count -= 1,
            ',' if count == 0 => {
                if arg_count == index {
                    return Location::new(
                        span.start() + args_start as u32 + 1 + start as u32,
                        span.start() + args_start as u32 + 1 + i as u32,
                        span.source_id(),
                    );
                }
                arg_count += 1;
                start = i + 1;
            }
            _ => {}
        }
    }

    // Handling the last argument
    if arg_count == index && start < args_section.len() {
        return Location::new(
            span.start() + args_start as u32 + 1 + start as u32,
            span.start() + args_start as u32 + 1 + args_section.len() as u32,
            span.source_id(),
        );
    }

    panic!("Argument {index} not found");
}

#[cfg(test)]
mod tests {
    use crate::{SourceId, module::id::Id};

    use super::*;

    #[test]
    fn extract_ith_fn_arg_single() {
        let src = "(|x| x)((1+2))";
        let span = Location::new_usize(0, src.len(), SourceId::from_index(1));
        let expected = ["(1+2)"];
        for (index, expected) in expected.into_iter().enumerate() {
            let arg_span = extract_ith_fn_arg(src, span, index);
            assert_eq!(&src[arg_span.as_range()], expected);
        }
    }

    #[test]
    fn extract_ith_fn_arg_multi() {
        let src = "(|x,y| x*y)(12, (1 + 3))";
        let span = Location::new_usize(0, src.len(), SourceId::from_index(1));
        let expected = ["12", " (1 + 3)"];
        for (index, expected) in expected.into_iter().enumerate() {
            let arg_span = extract_ith_fn_arg(src, span, index);
            assert_eq!(&src[arg_span.as_range()], expected);
        }
    }
}
