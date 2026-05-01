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
    compiler::error::RuntimeErrorKind,
    hir::function::{NullaryNativeFnFN, UnaryNativeFnRFN},
    module::Module,
    std::string::String as Str,
    types::effects::{PrimitiveEffect, effect},
    types::r#type::{FnType, Type},
    types::type_scheme::TypeScheme,
};

use super::string::string_type;

fn abort() -> Result<(), RuntimeErrorKind> {
    Err(RuntimeErrorKind::Aborted(None))
}

fn panic(msg: &Str) -> Result<(), RuntimeErrorKind> {
    Err(RuntimeErrorKind::Aborted(Some(msg.as_ref().to_string())))
}

fn invalid_argument(msg: &Str) -> Result<(), RuntimeErrorKind> {
    Err(RuntimeErrorKind::InvalidArgument(ustr(msg.as_ref())))
}

pub fn add_to_module(to: &mut Module) {
    // Control flow operation
    // Note: we use no_effects() for now as non-termination is modelled purely in the return type
    to.add_function(
        ustr("abort"),
        NullaryNativeFnFN::description_with_ty_scheme(
            abort,
            [],
            "Aborts the program.",
            TypeScheme::new_just_type(FnType::new_by_val(
                [],
                Type::never(),
                effect(PrimitiveEffect::Fallible),
            )),
        ),
    );
    to.add_function(
        ustr("panic"),
        UnaryNativeFnRFN::description_with_ty_scheme(
            panic,
            ["msg"],
            "Aborts the program with a message.",
            TypeScheme::new_just_type(FnType::new_by_val(
                [string_type()],
                Type::never(),
                effect(PrimitiveEffect::Fallible),
            )),
        ),
    );
    to.add_function(
        ustr("invalid_argument"),
        UnaryNativeFnRFN::description_with_ty_scheme(
            invalid_argument,
            ["msg"],
            "Aborts the program with an invalid argument error.",
            TypeScheme::new_just_type(FnType::new_by_val(
                [string_type()],
                Type::never(),
                effect(PrimitiveEffect::Fallible),
            )),
        ),
    );
}
