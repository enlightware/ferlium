// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::fmt;

use ferlium::{
    effects::no_effects,
    function::{BinaryNativeFnNNN, FunctionRef},
    module::{FmtWithModuleEnv, ModuleEnv, Modules},
    r#type::{
        bare_native_type, record_type, store_types, tuple_type, variant_type, Type, TypeKind,
    },
    std::{
        math::{float_type, int_type},
        std_module,
    },
    value::{NativeDisplay, Value},
};
use ustr::ustr;

fn println(value: &impl FmtWithModuleEnv, data: &ModuleEnv) {
    println!("{}", value.format_with(data));
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct List(Vec<Value>);

impl NativeDisplay for List {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, v) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{v}")?;
        }
        write!(f, "]")
    }
}

fn main() {
    // basic types
    let int = int_type();
    let u32 = Type::primitive::<u32>();
    let float = float_type();
    let string = Type::primitive::<String>();
    let empty_tuple = Type::unit();
    let gen0 = Type::variable_id(0);

    // environment
    let other_modules = Modules::new();
    let mut current_module = std_module();
    current_module.types.set("u32", u32);
    current_module.types.set("string", string);
    current_module
        .types
        .set_bare_native("list", bare_native_type::<List>());
    let module_env = ModuleEnv::new(&current_module, &other_modules);

    // test type printing
    println!("Some types:\n");
    let st = record_type(&[("ty", gen0), ("name", string), ("age", int)]);
    println(&st, &module_env);

    let variant = variant_type(&[("i", int), ("s", string)]);
    println(&variant, &module_env);
    let variant = variant_type(&[("i", int), ("f", float), ("u32", u32)]);
    println(&variant, &module_env);

    // ADT recursive list
    let adt_list_element = TypeKind::Tuple(vec![gen0, Type::new_local(1)]);
    let adt_list = TypeKind::Variant(vec![
        (ustr("Nil"), empty_tuple),
        (ustr("Cons"), Type::new_local(0)),
    ]);
    // add them to the universe as a batch
    let adt_list = store_types(&[adt_list_element, adt_list])[1];
    println(&adt_list, &module_env);

    // native list
    let list = Type::native::<List>(vec![gen0]);
    let list_int = Type::native::<List>(vec![int]);
    println(&list, &module_env);
    println(&list_int, &module_env);

    // functions
    let functions = [
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::Add::add as fn(isize, isize) -> isize,
            ["left", "right"],
            None,
            no_effects(),
        ),
        BinaryNativeFnNNN::description_with_default_ty(
            std::ops::Sub::sub as fn(isize, isize) -> isize,
            ["left", "right"],
            None,
            no_effects(),
        ),
    ];
    let add_fn_ty = functions[0].definition.ty_scheme.clone();
    println!("{}", add_fn_ty.display_rust_style(&module_env));
    let add_fn = FunctionRef::new_strong(&functions[0].code);
    let _sub_fn = FunctionRef::new_strong(&functions[1].code);
    let add_value = Value::Function((add_fn.clone(), None));

    // some interesting functions and types
    let option = variant_type(&[("None", empty_tuple), ("Some", gen0)]);
    print!("Option: ");
    println(&option, &module_env);
    let iterator_gen0 = Type::function_by_val(&[], tuple_type([option, Type::new_local(0)]));
    println!("Iterator: ");
    println(&iterator_gen0, &module_env);

    // test printing values
    println!("\nSome values:\n");
    let v_int = Value::Native(Box::new(11_isize));
    println!("{v_int}");
    let v_list_int = Value::Native(Box::new(List(vec![
        Value::native(11_isize),
        Value::native(22_isize),
    ])));
    println!("{v_list_int}");
    println!("{add_value}");
}
