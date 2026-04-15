// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//

use indoc::indoc;
use ustr::ustr;

use ferlium::std::option::some;

use crate::harness::{TestSession, float, int, string};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_aliases() {
    let mut session = TestSession::new();

    // Test simple type alias
    let result = session.run(indoc! { r#"
        type MyInt = int;

        fn use_int(x: MyInt) -> MyInt {
            x + 1
        }

        use_int(42)
    "# });
    assert_eq!(result, int(43));

    // Test tuple type alias
    let result = session.run(indoc! { r#"
        type Point = (int, int);

        fn add_coords(p: Point) -> int {
            p.0 + p.1
        }

        add_coords((10, 20))
    "# });
    assert_eq!(result, int(30));

    // Test record type alias
    let result = session.run(indoc! { r#"
        type Person = { name: string, age: int };

        fn get_name(p: Person) -> string {
            p.name
        }

        get_name({ name: "Alice", age: 30 })
    "# });
    assert_eq!(result, string("Alice"));

    // Test variant type alias
    let result = session.run(indoc! { r#"
        type Shape = Circle(float) | Rectangle { width: float, height: float };

        fn area(s: Shape) -> float {
            match s {
                Circle(r) => 3.14 * r * r,
                Rectangle { width, height } => width * height,
            }
        }

        area(Circle(5.0))
    "# });
    assert_eq!(result, float(3.14 * 5.0 * 5.0));

    // Test array type alias
    let result = session.run(indoc! { r#"
        type IntArray = [int];

        fn first(arr: IntArray) -> int {
            arr[0]
        }

        first([1, 2, 3])
    "# });
    assert_eq!(result, int(1));

    // Test function type alias
    let result = session.run(indoc! { r#"
        type IntToInt = (int) -> int;

        fn apply(f: IntToInt, x: int) -> int {
            f(x)
        }

        apply(|x| x * 2, 21)
    "# });
    assert_eq!(result, int(42));

    // Test nested type alias
    let result = session.run(indoc! { r#"
        type Coord = { x: int, y: int };
        type Entry = (string, Coord);
        type Entries = [Entry];

        fn get_first_x(entries: Entries) -> int {
            entries[0].1.x
        }

        get_first_x([("point1", { x: 5, y: 10 })])
    "# });
    assert_eq!(result, int(5));

    // Verify the type alias is stored in the module
    let module = session.compile_and_get_module(indoc! { r#"
        type MyInt = int;

        fn dummy() -> int { 0 }
    "# });
    assert!(module.get_type_alias(ustr("MyInt")).is_some());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn keyword_type_is_acceptable() {
    let mut session = TestSession::new();
    assert_eq!(session.run("({type: 1}: {type: int}).type"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn native_generic_type_aliases_in_explicit_typing() {
    // Native generic type aliases (registered via add_bare_native_type_alias_str) must be
    // resolvable as types in Ferlium code, including in function signatures, impl headers,
    // and trait output bindings.
    let mut session = TestSession::new();

    // A function that explicitly names a native generic type alias in its signature.
    let result = session.run(indoc! { r#"
        fn my_next(iter: &mut array_iterator<int>) -> None | Some(int) {
            array_iterator_next(iter)
        }
        let mut it = iter([10, 20, 30]);
        my_next(it)
    "# });
    assert_eq!(result, some(int(10)));

    // Using a native generic type alias in return type position.
    let result = session.run(indoc! { r#"
        fn make_iter(arr: [int]) -> array_iterator<int> {
            iter(arr)
        }
        let mut it = make_iter([5, 6, 7]);
        next(it)
    "# });
    assert_eq!(result, some(int(5)));

    // Using a native generic type alias in a type annotation.
    let result = session.run(indoc! { r#"
        let mut it = (iter([42]): array_iterator<int>);
        next(it)
    "# });
    assert_eq!(result, some(int(42)));

    // Using a native generic type alias in a trait impl method signature.
    let result = session.run(indoc! { r#"
        struct Wrapper<A> { arr: [A] }
        impl<A> Iterator for <Self = Wrapper<A> |-> Item = A> {
            fn next(w: &mut Wrapper<A>) -> None | Some(A) {
                let mut it = (iter(w.arr): array_iterator<A>);
                next(it)
            }
        }
        let mut w = Wrapper { arr: [99, 88] };
        next(w)
    "# });
    assert_eq!(result, some(int(99)));
}
