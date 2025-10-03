// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{cell::OnceCell, rc::Rc, str::FromStr};

use crate::{
    module::{finalize_module_pending_functions, Module, ModuleEnv, Modules, Use},
    r#type::{bare_native_type, Type, TypeKind},
    value::Value,
};

use array::Array;
use math::{Float, Int};
use ustr::ustr;

pub mod array;
pub mod core;
pub mod flow;
pub mod io;
pub mod iterator;
pub mod logic;
pub mod math;
pub mod mem;
pub mod option;
pub mod ordering;
mod prelude;
pub mod range;
pub mod serde;
pub mod string;
pub mod variant;

thread_local! {
    static STD_MODULE: OnceCell<Rc<Module>> = const { OnceCell::new() };
}

pub fn std_module() -> Rc<Module> {
    STD_MODULE.with(|cell| {
        cell.get_or_init(|| {
            let module = Rc::new({
                let mut module = Module::default();
                core::add_to_module(&mut module);
                flow::add_to_module(&mut module);
                // mem::add_to_module(&mut module);
                logic::add_to_module(&mut module);
                ordering::add_to_module(&mut module);
                math::add_to_module(&mut module);
                range::add_to_module(&mut module);
                array::add_to_module(&mut module);
                io::add_to_module(&mut module);
                string::add_to_module(&mut module);
                variant::add_to_module(&mut module);
                iterator::add_to_module(&mut module);
                serde::add_to_module(&mut module);
                prelude::add_to_module(&mut module);
                module
            });
            // No need to link because std has no imports.
            finalize_module_pending_functions(&module);
            module
        })
        .clone()
    })
}

pub fn new_std_modules() -> Modules {
    let mut modules: Modules = Default::default();
    modules.modules.insert(ustr("std"), std_module());
    modules
}

pub fn new_module_using_std() -> Module {
    let mut new_module = Module::default();
    new_module.uses.push(Use::All(ustr("std")));
    new_module
}

#[derive(Debug, Clone)]
pub struct StdModuleEnv {
    others: Modules,
    pub current: Module,
}
impl Default for StdModuleEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl StdModuleEnv {
    pub fn new() -> Self {
        Self {
            others: new_std_modules(),
            current: new_module_using_std(),
        }
    }
    pub fn get(&self) -> ModuleEnv<'_> {
        ModuleEnv {
            others: &self.others,
            current: &self.current,
            within_std: false,
        }
    }
}

pub fn default_value_for_type(ty: Type) -> Option<Value> {
    use TypeKind::*;
    match &*ty.data() {
        Variable(_) => None,
        Native(native_type) => {
            if native_type.bare_ty == bare_native_type::<()>() {
                Some(Value::unit())
            } else if native_type.bare_ty == bare_native_type::<bool>() {
                Some(Value::native(false))
            } else if native_type.bare_ty == bare_native_type::<Int>() {
                Some(Value::native(0))
            } else if native_type.bare_ty == bare_native_type::<Float>() {
                Some(Value::native::<Float>(Float::new(0.0).unwrap()))
            } else if native_type.bare_ty == bare_native_type::<string::String>() {
                Some(Value::native(string::String::from_str("").unwrap()))
            } else if native_type.bare_ty == bare_native_type::<Array>() {
                Some(Value::native(Array::new()))
            } else {
                None
            }
        }
        Tuple(tys) => tys
            .iter()
            .map(|ty| default_value_for_type(*ty))
            .collect::<Option<Vec<_>>>()
            .map(Value::tuple),
        Record(fields) => fields
            .iter()
            .map(|(_, ty)| default_value_for_type(*ty))
            .collect::<Option<Vec<_>>>()
            .map(Value::tuple),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use ustr::ustr;

    use ordered_float::NotNan;

    use crate::{
        r#type::{tuple_type, Type},
        std::{
            array::{array_type, Array},
            logic::bool_type,
            math::{float_type, int_type},
            string::{self, string_type},
        },
        value::Value,
    };

    #[test]
    fn default_value_for_type() {
        use super::default_value_for_type as def_val;
        assert_eq!(def_val(Type::unit()), Some(Value::unit()));
        assert_eq!(def_val(bool_type()), Some(Value::native(false)));
        assert_eq!(def_val(int_type()), Some(Value::native(0_isize)));
        assert_eq!(
            def_val(float_type()),
            Some(Value::native(NotNan::new(0.0_f64).unwrap()))
        );
        assert_eq!(
            def_val(string_type()),
            Some(Value::native(string::String::from_str("").unwrap()))
        );
        assert_eq!(
            def_val(array_type(int_type())),
            Some(Value::native(Array::new()))
        );
        assert_eq!(
            def_val(array_type(float_type())),
            Some(Value::native(Array::new()))
        );
        assert_eq!(
            def_val(tuple_type([int_type(), bool_type()])),
            Some(Value::tuple([Value::native(0_isize), Value::native(false)]))
        );
        assert_eq!(
            def_val(Type::record([
                (ustr("a"), int_type()),
                (ustr("b"), bool_type())
            ])),
            Some(Value::tuple([Value::native(0_isize), Value::native(false)]))
        );
    }
}
