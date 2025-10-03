// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ustr::ustr;

use crate::{
    effects::no_effects,
    error::RuntimeError,
    function::{NullaryNativeFnFN, UnaryNativeFnNFN},
    module::Module,
    std::string::String as Str,
    r#type::{FnType, Type},
    type_scheme::TypeScheme,
};

use super::string::string_type;

fn abort() -> Result<(), RuntimeError> {
    Err(RuntimeError::Aborted(None))
}

fn panic(msg: Str) -> Result<(), RuntimeError> {
    Err(RuntimeError::Aborted(Some(msg.into())))
}

pub fn add_to_module(to: &mut Module) {
    // Control flow operation
    // Note: we use no_effects() for now as non-termination is modelled purely in the return type
    to.add_named_function(
        ustr("abort"),
        NullaryNativeFnFN::description_with_ty_scheme(
            abort,
            [],
            Some("Aborts the program."),
            TypeScheme::new_just_type(FnType::new_by_val([], Type::never(), no_effects())),
        ),
    );
    to.add_named_function(
        ustr("panic"),
        UnaryNativeFnNFN::description_with_ty_scheme(
            panic,
            ["msg"],
            Some("Aborts the program with a message."),
            TypeScheme::new_just_type(FnType::new_by_val(
                [string_type()],
                Type::never(),
                no_effects(),
            )),
        ),
    );
}
