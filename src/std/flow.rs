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
    compiler::error::SourceFailureKind,
    hir::native_functions::{NativeFallibleFn0, NativeFallibleFnR},
    module::Module,
    std::string::String as Str,
    types::{
        effects::{PrimitiveEffect, effect},
        never::Never,
    },
};

fn abort() -> Result<Never, SourceFailureKind> {
    Err(SourceFailureKind::Aborted(None))
}

fn panic(msg: &Str) -> Result<Never, SourceFailureKind> {
    Err(SourceFailureKind::Aborted(Some(msg.as_ref().to_string())))
}

fn invalid_argument(msg: &Str) -> Result<Never, SourceFailureKind> {
    Err(SourceFailureKind::InvalidArgument(msg.as_ref().to_string()))
}

pub fn add_to_module(to: &mut Module) {
    to.add_function(
        ustr("abort"),
        NativeFallibleFn0::from_rust_never(abort).description(
            [],
            "Aborts the program.",
            effect(PrimitiveEffect::Fallible),
        ),
    );
    to.add_function(
        ustr("panic"),
        NativeFallibleFnR::from_rust_never(panic).description(
            ["msg"],
            "Aborts the program with a message.",
            effect(PrimitiveEffect::Fallible),
        ),
    );
    to.add_function(
        ustr("invalid_argument"),
        NativeFallibleFnR::from_rust_never(invalid_argument).description(
            ["msg"],
            "Aborts the program with an invalid argument error.",
            effect(PrimitiveEffect::Fallible),
        ),
    );
}
