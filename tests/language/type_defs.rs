// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ferlium::error::{DuplicatedFieldContext, DuplicatedVariantContext};
use ferlium::r#type::Type;
use ferlium::std::logic::bool_type;
use ferlium::std::math::{float_type, int_type};
use ferlium::std::string::string_type;
use ferlium::value::Value;
use test_log::test;

use indoc::indoc;
use ustr::ustr;

use crate::common::{bool, compile, fail_compilation, float, int, run, string};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn define_enum_types() {
    let mod_src = indoc! { r#"
        // Basic unit variants
        enum SimpleColor {
            Red,
            Green,
            Blue
        }

        // Single-type variants
        enum Option {
            Some(int),
            None
        }
        enum Option2 {
            Some(int),
            None,
        }

        // Multi-type tuple variants
        enum Player {
            Basic(string),
            Positioned(string, int, int),
            FullData(string, int, int, float)
        }

        // Record-style variants
        enum Event {
            Click { x: int, y: int },
            KeyPress { key: string, shift: bool },
            Resize { width: int, height: int }
        }

        // Mixed variants in same enum
        enum Message {
            Quit,
            Move { x: int, y: int },
            Write(string),
            ChangeColor(int, int, int),
            Callback((int) -> int)
        }

        // Empty enum
        enum Empty {}
    "# };
    let module = compile(mod_src).0.module;

    let simple_color = module.type_defs.get(&ustr("SimpleColor")).unwrap();
    assert_eq!(simple_color.name, ustr("SimpleColor"));
    let simple_color = simple_color.shape.data().as_variant().unwrap().clone();
    assert_eq!(
        simple_color,
        [
            (ustr("Blue"), Type::unit()),
            (ustr("Green"), Type::unit()),
            (ustr("Red"), Type::unit()),
        ]
    );

    let option_type = module.type_defs.get(&ustr("Option")).unwrap();
    assert_eq!(option_type.name, ustr("Option"));
    let option_type = option_type.shape.data().as_variant().unwrap().clone();
    assert_eq!(
        option_type,
        [
            (ustr("None"), Type::unit()),
            (ustr("Some"), Type::tuple([int_type()])),
        ]
    );

    let option2_type = module.type_defs.get(&ustr("Option2")).unwrap();
    assert_eq!(option2_type.name, ustr("Option2"));
    let option2_type = option2_type.shape.data().as_variant().unwrap().clone();
    assert_eq!(option2_type, option_type);

    let player_type = module.type_defs.get(&ustr("Player")).unwrap();
    assert_eq!(player_type.name, ustr("Player"));
    let player_type = player_type.shape.data().as_variant().unwrap().clone();
    assert_eq!(
        player_type,
        [
            (ustr("Basic"), Type::tuple([string_type()])),
            (
                ustr("FullData"),
                Type::tuple([string_type(), int_type(), int_type(), float_type()])
            ),
            (
                ustr("Positioned"),
                Type::tuple([string_type(), int_type(), int_type()])
            ),
        ]
    );

    let event_type = module.type_defs.get(&ustr("Event")).unwrap();
    assert_eq!(event_type.name, ustr("Event"));
    let event_type = event_type.shape.data().as_variant().unwrap().clone();
    assert_eq!(
        event_type,
        [
            (
                ustr("Click"),
                Type::record([(ustr("x"), int_type()), (ustr("y"), int_type())])
            ),
            (
                ustr("KeyPress"),
                Type::record([(ustr("key"), string_type()), (ustr("shift"), bool_type())])
            ),
            (
                ustr("Resize"),
                Type::record([(ustr("height"), int_type()), (ustr("width"), int_type())])
            ),
        ]
    );

    let message_type = module.type_defs.get(&ustr("Message")).unwrap();
    assert_eq!(message_type.name, ustr("Message"));
    let message_type = message_type.shape.data().as_variant().unwrap().clone();
    assert_eq!(
        message_type,
        [
            (
                ustr("Callback"),
                Type::tuple([Type::function_by_val([int_type()], int_type())]),
            ),
            (
                ustr("ChangeColor"),
                Type::tuple([int_type(), int_type(), int_type()])
            ),
            (
                ustr("Move"),
                Type::record([(ustr("x"), int_type()), (ustr("y"), int_type())])
            ),
            (ustr("Quit"), Type::unit()),
            (ustr("Write"), Type::tuple([string_type()])),
        ]
    );

    let empty_type = module.type_defs.get(&ustr("Empty")).unwrap();
    assert_eq!(empty_type.name, ustr("Empty"));
    assert!(empty_type.shape.data().is_never());

    assert_eq!(
        fail_compilation("enum Invalid { A, B, A }")
            .into_inner()
            .into_duplicated_variant()
            .unwrap()
            .3,
        DuplicatedVariantContext::Enum
    );
    assert_eq!(
        fail_compilation("enum Invalid { A, B, A(int) }")
            .into_inner()
            .into_duplicated_variant()
            .unwrap()
            .3,
        DuplicatedVariantContext::Enum
    );
    assert_eq!(
        fail_compilation("enum Invalid { A, B, A { a: int } }")
            .into_inner()
            .into_duplicated_variant()
            .unwrap()
            .3,
        DuplicatedVariantContext::Enum
    );
    assert_eq!(
        fail_compilation("enum Invalid { A, B { a: T | T(int) } }")
            .into_inner()
            .into_duplicated_variant()
            .unwrap()
            .3,
        DuplicatedVariantContext::Variant
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_record_enum_values() {
    assert_eq!(
        run(indoc! { r#"
            enum Message {
                Quit,
                Move { x: int, y: int },
            }

            Message::Move { y: 30 + 10, x: 30 }
        "# }),
        Value::raw_variant(ustr("Move"), Value::tuple([int(30), int(40)]))
    );

    let mod_src = indoc! { "
        enum Message {
            Quit,
            Flag { v0: bool, v1: bool }
        }
    " };
    assert_eq!(
        run(&format!(
            "{mod_src} Message::Flag {{ v1: false, v0: true }}"
        )),
        Value::raw_variant(ustr("Flag"), Value::tuple([bool(true), bool(false)]))
    );

    assert_eq!(
        *fail_compilation(&format!(r#"{mod_src} Message::Flag {{ v0: true }}"#))
            .as_missing_struct_field()
            .unwrap()
            .1,
        "v1"
    );
    assert_eq!(
        *fail_compilation(&format!(
            r#"{mod_src} Message::Flag {{ v1: false, v0: true, v2: false }}"#
        ))
        .as_invalid_struct_field()
        .unwrap()
        .1,
        "v2"
    );
    fail_compilation(&format!(
        r#"{mod_src} Message::Flag {{ v1: false, v0: 1.0 }}"#
    ))
    .expect_type_mismatch("float", "bool");

    // shorthand syntax when variable name matches field name
    run(&format!(
        r#"{mod_src} let v0 = true; let v1 = false; Message::Flag {{ v0, v1 }}"#
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_tuple_enum_values() {
    assert_eq!(
        run(indoc! { r#"
            enum Player {
                Basic(string),
                Positioned(int, int),
            }

            Player::Positioned(30 + 10, 0)
        "# }),
        Value::raw_variant(ustr("Positioned"), Value::tuple([int(40), int(0)]))
    );

    let mod_src = indoc! { "
        enum Player {
            Basic(string),
            State(bool)
        }
    " };
    assert_eq!(
        run(&format!(r#"{mod_src} Player::Basic("ok")"#)),
        Value::raw_variant(ustr("Basic"), Value::tuple([string("ok")]))
    );
    assert_eq!(
        run(&format!("{mod_src} Player::State(false)")),
        Value::raw_variant(ustr("State"), Value::tuple([bool(false)]))
    );
    fail_compilation(&format!("{mod_src} Player::State(1.0)"))
        .expect_type_mismatch("float", "bool");
    fail_compilation(&format!("{mod_src} Player::State()")).expect_wrong_number_of_arguments(1, 0);
    fail_compilation(&format!("{mod_src} Player::State(true, 1.0)"))
        .expect_wrong_number_of_arguments(1, 2);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_mix_enum_values() {
    let mod_src = indoc! { r#"
        enum Message {
            Quit,
            Move { x: int, y: int },
            Write(string),
            ChangeColor(int, int, int),
            Callback((int) -> int)
        }
    "# };

    assert_eq!(
        run(&format!("{mod_src} Message::Quit")),
        Value::raw_variant(ustr("Quit"), Value::unit())
    );

    assert_eq!(
        run(&format!("{mod_src} Message::Move {{ x: 30, y: 40 }}")),
        Value::raw_variant(ustr("Move"), Value::tuple(vec![int(30), int(40)]))
    );

    assert_eq!(
        run(&format!(r#"{mod_src} Message::Write("Hello, world!")"#)),
        Value::raw_variant(ustr("Write"), Value::tuple(vec![string("Hello, world!")])),
    );

    assert_eq!(
        run(&format!("{mod_src} Message::ChangeColor(255, 0, 0)")),
        Value::raw_variant(
            ustr("ChangeColor"),
            Value::tuple(vec![int(255), int(0), int(0)])
        )
    );

    let value = run(&format!("{mod_src} Message::Callback(|x| x + 1)"));
    assert_eq!(value.as_variant().unwrap().tag, ustr("Callback"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn enum_projections() {
    assert_eq!(
        run(indoc! { r#"
            enum Action {
                Quit,
                Jump(float),
                Move { x: float, y: float },
            }

            let f = |a| match a {
                Quit => 0.0,
                Jump(h) => h,
                Move { y, x } => x - y,
            };

            f(Action::Move { x: 30.0, y: 40.0 }) + f(Action::Jump(5.0)) + f(Action::Quit)
        "# }),
        float(-5.0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn define_struct_types() {
    let mod_src = indoc! { r#"
        // Empty struct
        struct Empty {}

        // Struct with fields
        struct Person {
            name: string,
            age: int,
            is_active: bool
        }

        // Struct with fields
        struct Person2 {
            name: string,
            age: int,
            is_active: bool,
        }

        // Newtype struct
        struct Email(string)

        // Tuple struct
        struct Point(int, int)

        // Tuple struct
        struct Point2(int, int,)

        // Struct with function pointer
        struct Callable {
            callback: (string) -> ()
        }
    "# };
    let module = compile(mod_src).0.module;

    let empty_type = module.type_defs.get(&ustr("Empty")).unwrap();
    assert_eq!(empty_type.name, ustr("Empty"));
    let empty_type_shape = empty_type.shape.data().as_record().unwrap().clone();
    assert_eq!(empty_type_shape, vec![]);

    let person_type = module.type_defs.get(&ustr("Person")).unwrap();
    assert_eq!(person_type.name, ustr("Person"));
    let person_type_shape = person_type.shape.data().as_record().unwrap().clone();
    assert_eq!(
        person_type_shape,
        vec![
            (ustr("age"), int_type()),
            (ustr("is_active"), bool_type()),
            (ustr("name"), string_type()),
        ]
    );

    let person2_type = module.type_defs.get(&ustr("Person2")).unwrap();
    assert_eq!(person2_type.name, ustr("Person2"));
    let person2_type_shape = person2_type.shape.data().as_record().unwrap().clone();
    assert_eq!(person2_type_shape, person_type_shape);

    let email_type = module.type_defs.get(&ustr("Email")).unwrap();
    assert_eq!(email_type.name, ustr("Email"));
    let email_type_shape = email_type.shape.data().as_tuple().unwrap().clone();
    assert_eq!(email_type_shape, vec![string_type()]);

    let point_type = module.type_defs.get(&ustr("Point")).unwrap();
    assert_eq!(point_type.name, ustr("Point"));
    let point_type_shape = point_type.shape.data().as_tuple().unwrap().clone();
    assert_eq!(point_type_shape, vec![int_type(), int_type()]);

    let point2_type = module.type_defs.get(&ustr("Point2")).unwrap();
    assert_eq!(point2_type.name, ustr("Point2"));
    let point2_type_shape = point2_type.shape.data().as_tuple().unwrap().clone();
    assert_eq!(point2_type_shape, vec![int_type(), int_type()]);

    let callable_type = module.type_defs.get(&ustr("Callable")).unwrap();
    assert_eq!(callable_type.name, ustr("Callable"));
    let callable_type_shape = callable_type.shape.data().as_record().unwrap().clone();
    assert_eq!(
        callable_type_shape,
        vec![(
            ustr("callback"),
            Type::function_by_val([string_type()], Type::unit())
        ),]
    );

    assert_eq!(
        fail_compilation("struct Invalid { a: int, a: int }")
            .into_inner()
            .into_duplicated_field()
            .unwrap()
            .3,
        DuplicatedFieldContext::Struct
    );
    assert_eq!(
        fail_compilation("struct Invalid { a: int, b: string, a: float }")
            .into_inner()
            .into_duplicated_field()
            .unwrap()
            .3,
        DuplicatedFieldContext::Struct
    );
    assert_eq!(
        fail_compilation("struct Invalid { a: int, b: { a: int, a: float } }")
            .into_inner()
            .into_duplicated_field()
            .unwrap()
            .3,
        DuplicatedFieldContext::Record
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_record_struct_values() {
    assert_eq!(
        run(indoc! { r#"
            struct Person {
                name: string,
                age: int,
                is_active: bool
            }

            Person {
                name: "Alice",
                age: 20 + 10,
                is_active: true
            }
        "# }),
        Value::tuple(vec![int(30), bool(true), string("Alice")])
    );

    let mod_src = "struct Person { name: string, is_active: bool }";
    assert_eq!(
        run(&format!(
            r#"{mod_src} Person {{ name: "Alice", is_active: true }}"#
        )),
        Value::tuple(vec![bool(true), string("Alice")])
    );

    assert_eq!(
        *fail_compilation(&format!(r#"{mod_src} Person {{ name: "Alice" }}"#))
            .as_missing_struct_field()
            .unwrap()
            .1,
        "is_active"
    );
    assert_eq!(
        *fail_compilation(&format!(
            r#"{mod_src} Person {{ name: "Alice", is_active: true, age: 20.2 }}"#
        ))
        .as_invalid_struct_field()
        .unwrap()
        .1,
        "age"
    );
    fail_compilation(&format!(
        r#"{mod_src} Person {{ name: "Alice", is_active: 1.2 }}"#
    ))
    .expect_type_mismatch("float", "bool");

    // shorthand syntax when variable name matches field name
    run(&format!(
        r#"{mod_src} let name = "Alice"; let is_active = true; Person {{ name, is_active }}"#
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_empty_struct_values() {
    assert_eq!(run(r#"struct Empty; Empty"#), Value::unit());
    assert_eq!(run(r#"struct Empty2 {} Empty2 {}"#), Value::empty_tuple());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_tuple_struct_values() {
    assert_eq!(
        run(r#"struct Email(string) Email(string_concat("h", "i"))"#),
        Value::tuple(vec![string("hi")])
    );
    assert_eq!(
        run(r#"struct Email(string) Email("hi")"#),
        Value::tuple(vec![string("hi")])
    );

    assert_eq!(
        run(r#"struct Email((string, )) Email((string_concat("h", "i"), ))"#),
        Value::tuple(vec![Value::tuple(vec![string("hi")])])
    );
    assert_eq!(
        run(r#"struct Email((string, )) Email(("hi", ))"#),
        Value::tuple(vec![Value::tuple(vec![string("hi")])])
    );

    assert_eq!(
        run(r#"struct Point(int, int) Point(1 + 0, 2)"#),
        Value::tuple(vec![int(1), int(2)])
    );
    assert_eq!(
        run(r#"struct Point(float, float) Point(1.0, 2.0)"#),
        Value::tuple(vec![float(1.0), float(2.0)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn struct_projections() {
    assert_eq!(run(r#"struct Email(string) Email("hi").0"#), string("hi"));

    assert_eq!(
        run(r#"struct Person(string, int) Person("John", 30).0"#),
        string("John")
    );

    assert_eq!(
        run(r#"struct Person { name: string, age: int } Person { name: "John", age: 30 }.name"#),
        string("John")
    );

    assert_eq!(
        run(r#"struct Age(int) struct Person(string, Age) Person("John", Age(30)).0"#),
        string("John")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn same_module_references() {
    assert_eq!(
        run(indoc! { r#"
            struct Age(int)
            struct Name(string)
            struct Person { name: Name, age: Age }

            fn get_name(person: Person) { person.name }
            fn get_age(person: Person) { person.age }
            fn get_data(person: Person) { (get_name(person).0, get_age(person).0) }

            get_data(Person { name: Name("John"), age: Age(30) })
        "# }),
        tuple!(string("John"), int(30))
    );

    assert_eq!(
        fail_compilation("struct A { a: A }")
            .into_inner()
            .into_unsupported()
            .unwrap()
            .1,
        "Self-referential type paths are not supported, but `A` refers to itself"
    );
    assert_eq!(
        fail_compilation("enum A { X(A) }")
            .into_inner()
            .into_unsupported()
            .unwrap()
            .1,
        "Self-referential type paths are not supported, but `A` refers to itself"
    );
    assert_eq!(
        fail_compilation("enum A { X(B) } struct B { a: A }")
            .into_inner()
            .into_unsupported()
            .unwrap()
            .1,
        "Cyclic types are not supported, but `B` indirectly refers to itself"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_annotations() {
    let mod_src = indoc! { r#"
        struct Age(int)
        struct Person1 { age: Age }
        struct Person2 { age: Age }

        fn age(d) { d.age.0 }
        fn age1(d: Person1) { d.age.0 }
    "# };
    assert_eq!(
        run(&format!(r"{mod_src} age(Person1 {{ age: Age(30) }})")),
        int(30)
    );
    assert_eq!(
        run(&format!(r"{mod_src} age1(Person1 {{ age: Age(30) }})")),
        int(30)
    );
    assert_eq!(
        run(&format!(r"{mod_src} age(Person2 {{ age: Age(30) }})")),
        int(30)
    );
    assert_eq!(run(&format!(r"{mod_src} age({{ age: Age(30) }})")), int(30));
    let error = fail_compilation(&format!(r"{mod_src} age1(Person2 {{ age: Age(30) }})"))
        .into_inner()
        .into_named_type_mismatch()
        .unwrap();
    assert_eq!((error.0.as_str(), error.3.as_str()), ("Person2", "Person1"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn double_newtype() {
    let mod_src = indoc! { r#"
        struct Person(string)
        struct Creature(Person)
    "# };
    assert_eq!(
        run(&format!(r#"{mod_src} Creature(Person("Alice")).0.0"#)),
        string("Alice")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn attributes() {
    // Helper to get attributes of a type definition
    let attrs = |code, name| {
        compile(code)
            .0
            .module
            .type_defs
            .get(&ustr(name))
            .unwrap()
            .attributes
            .clone()
    };

    // No attributes by default
    let attributes = attrs(
        indoc! { r#"
            enum SimpleColor { Red, Green, Blue }
        "# },
        "SimpleColor",
    );
    assert!(attributes.is_empty());

    // Flag attribute
    let attributes = attrs(
        indoc! { r#"
            #[flag]
            enum SimpleColor { Red, Green, Blue }
        "# },
        "SimpleColor",
    );
    assert_eq!(attributes.len(), 1);
    assert_eq!(attributes[0].path.0, ustr("flag"));

    // Multiple attributes
    let attributes = attrs(
        indoc! { r#"
            #[flag]
            #[path(name = "value")]
            #[multi(name1 = "value1", name2 = "value2")]
            enum SimpleColor { Red, Green, Blue }
        "# },
        "SimpleColor",
    );
    assert_eq!(attributes.len(), 3);
    assert_eq!(attributes[0].path.0, ustr("flag"));
    assert_eq!(attributes[1].path.0, ustr("path"));
    assert_eq!(attributes[1].items.len(), 1);
    assert_eq!(
        attributes[1].items[0].as_name_value().unwrap().0 .0,
        ustr("name")
    );
    assert_eq!(
        attributes[1].items[0].as_name_value().unwrap().1 .0,
        ustr("value")
    );
    assert_eq!(attributes[2].path.0, ustr("multi"));
    assert_eq!(attributes[2].items.len(), 2);
    let item1 = attributes[2].items[0].as_name_value().unwrap();
    assert_eq!(item1.0 .0, ustr("name1"));
    assert_eq!(item1.1 .0, ustr("value1"));
    let item2 = attributes[2].items[1].as_name_value().unwrap();
    assert_eq!(item2.0 .0, ustr("name2"));
    assert_eq!(item2.1 .0, ustr("value2"));

    // Also works on structs
    let attributes = attrs(
        indoc! { r#"
            #[flag]
            #[path(name = "value")]
            #[multi(name1 = "value1", name2 = "value2")]
            struct Person {
                name: string,
                age: int,
                is_active: bool
            }
        "# },
        "Person",
    );
    assert_eq!(attributes.len(), 3);
    assert_eq!(attributes[0].path.0, ustr("flag"));
    assert_eq!(attributes[1].path.0, ustr("path"));
    assert_eq!(attributes[1].items.len(), 1);
    assert_eq!(
        attributes[1].items[0].as_name_value().unwrap().0 .0,
        ustr("name")
    );
    assert_eq!(
        attributes[1].items[0].as_name_value().unwrap().1 .0,
        ustr("value")
    );
    assert_eq!(attributes[2].path.0, ustr("multi"));
    assert_eq!(attributes[2].items.len(), 2);
    let item1 = attributes[2].items[0].as_name_value().unwrap();
    assert_eq!(item1.0 .0, ustr("name1"));
    assert_eq!(item1.1 .0, ustr("value1"));
    let item2 = attributes[2].items[1].as_name_value().unwrap();
    assert_eq!(item2.0 .0, ustr("name2"));
    assert_eq!(item2.1 .0, ustr("value2"));
}
