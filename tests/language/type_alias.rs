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

use ferlium::{format::FormatWith, module::ModuleEnv, std::option::some};

use crate::harness::{TestSession, float, int, string};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

fn format_compiled_module(session: &mut TestSession, src: &str) -> String {
    let module_id = session.compile(src).module_id;
    let module = session.session().expect_fresh_module(module_id);
    module.format_with(session.session().modules()).to_string()
}

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
    assert_val_eq!(result, int(43));

    // Test tuple type alias
    let result = session.run(indoc! { r#"
        type Point = (int, int);

        fn add_coords(p: Point) -> int {
            p.0 + p.1
        }

        add_coords((10, 20))
    "# });
    assert_val_eq!(result, int(30));

    // Test record type alias
    let result = session.run(indoc! { r#"
        type Person = { name: string, age: int };

        fn get_name(p: Person) -> string {
            p.name
        }

        get_name({ name: "Alice", age: 30 })
    "# });
    assert_val_eq!(result, string("Alice"));

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
    assert_val_eq!(result, float(3.14 * 5.0 * 5.0));

    // Test array type alias
    let result = session.run(indoc! { r#"
        type IntArray = [int];

        fn first(arr: IntArray) -> int {
            arr[0]
        }

        first([1, 2, 3])
    "# });
    assert_val_eq!(result, int(1));

    // Test function type alias
    let result = session.run(indoc! { r#"
        type IntToInt = (int) -> int;

        fn apply(f: IntToInt, x: int) -> int {
            f(x)
        }

        apply(|x| x * 2, 21)
    "# });
    assert_val_eq!(result, int(42));

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
    assert_val_eq!(result, int(5));

    // Verify the type alias is stored in the module
    let module = session.compile_and_get_module(indoc! { r#"
        type MyInt = int;

        fn dummy() -> int { 0 }
    "# });
    assert!(module.get_type_alias(ustr("MyInt")).is_some());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_type_aliases() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! { r#"
            type List = Nil | Cons(int, List);

            let xs: List = Cons(1, Cons(2, Nil));
            match xs {
                Cons(a, tail) => match tail {
                    Cons(b, tail2) => match tail2 {
                        Nil => a + b,
                        Cons(c, rest) => c,
                    },
                    Nil => 0,
                },
                Nil => 0,
            }
        "# }),
        int(3)
    );

    assert_val_eq!(
        session.run(indoc! { r#"
            type A = Done | Next(B);
            type B = Back(A);

            let value: A = Next(Back(Done));
            match value {
                Next(b) => match b {
                    Back(a) => match a {
                        Done => 1,
                        Next(next) => 0,
                    },
                },
                Done => 0,
            }
        "# }),
        int(1)
    );

    session
        .fail_compilation("type A = A;")
        .expect_infinite_type_product_cycle("A");

    assert_val_eq!(
        session.run(indoc! { r#"
            type List<T> = Nil | Cons(T, List<T>);

            let xs: List<int> = Cons(1, Cons(2, Nil));
            match xs {
                Cons(a, tail) => match tail {
                    Cons(b, tail2) => match tail2 {
                        Nil => a + b,
                        Cons(c, rest) => c,
                    },
                    Nil => 0,
                },
                Nil => 0,
            }
        "# }),
        int(3)
    );

    assert_val_eq!(
        session.run(indoc! { r#"
            type A<T> = End(T) | Next(B<T>);
            type B<T> = Back(A<T>);

            let value: A<int> = Next(Back(End(7)));
            match value {
                Next(b) => match b {
                    Back(a) => match a {
                        End(value) => value,
                        Next(next) => 0,
                    },
                },
                End(value) => value,
            }
        "# }),
        int(7)
    );

    session
        .fail_compilation("type Weird<T> = Done | Next(Weird<(T, T)>);")
        .expect_non_regular_recursive_generic_shape("Weird");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_generic_alias_formatting_preserves_recursive_only_arguments() {
    let mut session = TestSession::new();
    let rendered = format_compiled_module(
        &mut session,
        indoc! { r#"
            type Tree<A, B> = Leaf(A) | Node2(Tree<A, B>, Tree<A, B>);

            fn id(tree: Tree<int, string>) {
                tree
            }
        "# },
    );

    assert!(
        rendered.contains("Tree<A, B>: Leaf (A) | Node2 (Tree<A, B>, Tree<A, B>)"),
        "recursive alias body should keep recursive-only arguments, got:\n{rendered}"
    );
    assert!(
        rendered.contains("fn id(tree: Tree<int, _>) -> Tree<int, _>"),
        "recursive alias use should keep a placeholder for the erased recursive-only argument, got:\n{rendered}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn non_recursive_phantom_alias_does_not_capture_plain_type_formatting() {
    let mut session = TestSession::new();
    let rendered = format_compiled_module(
        &mut session,
        indoc! { r#"
            type Phantom<T> = int;

            fn id(x: int) {
                x
            }
        "# },
    );

    assert!(
        rendered.contains("fn id(x: int) -> int"),
        "non-recursive phantom aliases should not rename plain concrete types, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("fn id(x: Phantom"),
        "non-recursive phantom alias unexpectedly captured int formatting, got:\n{rendered}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_alias_recovery_prefers_shorter_name_then_alphabetic_name() {
    let mut session = TestSession::new();
    let rendered = format_compiled_module(
        &mut session,
        indoc! { r#"
            type Longer<A> = Leaf(A) | Node(Longer<A>);
            type B<A> = Leaf(A) | Node(B<A>);

            fn id(x: Longer<int>) {
                x
            }
        "# },
    );

    assert!(
        rendered.contains("fn id(x: B<int>) -> B<int>"),
        "equally informative aliases should prefer the shorter name, got:\n{rendered}"
    );

    let rendered = format_compiled_module(
        &mut session,
        indoc! { r#"
            type Zed<A> = Leaf(A) | Node(Zed<A>);
            type Aaa<A> = Leaf(A) | Node(Aaa<A>);

            fn id(x: Zed<int>) {
                x
            }
        "# },
    );

    assert!(
        rendered.contains("fn id(x: Aaa<int>) -> Aaa<int>"),
        "equally informative aliases with equal-length names should prefer alphabetic order, got:\n{rendered}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_alias_recovery_prefers_current_module_over_imported_modules() {
    let mut session = TestSession::new();
    session
        .try_compile_module("dep", "type A<T> = Leaf(T) | Node(A<T>);")
        .expect("dependency module should compile");
    let module_id = session
        .try_compile_module(
            "user",
            indoc! { r#"
                type Longer<T> = Leaf(T) | Node(Longer<T>);

                fn id(x: Longer<int>) {
                    x
                }
            "# },
        )
        .expect("user module should compile")
        .module_id;
    let module = session.session().expect_fresh_module(module_id);
    let rendered = module.format_with(session.session().modules()).to_string();

    assert!(
        rendered.contains("fn id(x: Longer<int>) -> Longer<int>"),
        "current-module aliases should beat shorter imported aliases, got:\n{rendered}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_alias_recovery_handles_alias_to_imported_alias() {
    let mut session = TestSession::new();
    session
        .try_compile_module("dep", "type A<T> = Leaf(T) | Node(A<T>);")
        .expect("dependency module should compile");
    let module_id = session
        .try_compile_module(
            "user",
            indoc! { r#"
                type Longer<T> = dep::A<T>;

                fn id(x: Longer<int>) {
                    x
                }
            "# },
        )
        .expect("user module should compile")
        .module_id;
    let module = session.session().expect_fresh_module(module_id);
    let rendered = module.format_with(session.session().modules()).to_string();

    assert!(
        rendered.contains("fn id(x: Longer<int>) -> Longer<int>"),
        "current-module alias-to-alias definitions should keep the local alias spelling, got:\n{rendered}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_type_aliases() {
    let mut session = TestSession::new();

    // Simple generic alias with one parameter
    let result = session.run(indoc! { r#"
        type Wrapped<A> = (A, string);

        fn wrap(x: int) -> Wrapped<int> {
            (x, "hello")
        }

        wrap(42).0
    "# });
    assert_val_eq!(result, int(42));

    // Generic alias with two parameters
    let result = session.run(indoc! { r#"
        type Pair<A, B> = (A, B);

        fn make_pair(a: int, b: string) -> Pair<int, string> {
            (a, b)
        }

        make_pair(1, "two").0
    "# });
    assert_val_eq!(result, int(1));

    // Generic alias used in function argument position
    let result = session.run(indoc! { r#"
        type Pair<A, B> = (A, B);

        fn first(p: Pair<int, string>) -> int {
            p.0
        }

        first((10, "x"))
    "# });
    assert_val_eq!(result, int(10));

    // Generic alias wrapping a record type
    let result = session.run(indoc! { r#"
        type Named<A> = { name: string, value: A };

        fn get_value(n: Named<int>) -> int {
            n.value
        }

        get_value({ name: "x", value: 99 })
    "# });
    assert_val_eq!(result, int(99));

    // Generic alias wrapping an array
    let result = session.run(indoc! { r#"
        type List<A> = [A];

        fn head(xs: List<int>) -> int {
            xs[0]
        }

        head([7, 8, 9])
    "# });
    assert_val_eq!(result, int(7));

    // Generic alias wrapping a variant type
    let result = session.run(indoc! { r#"
        type Maybe<A> = Nothing | Just(A);

        fn unwrap_or(m: Maybe<int>, default: int) -> int {
            match m {
                Nothing => default,
                Just(x) => x,
            }
        }

        unwrap_or(Just(42), 0)
    "# });
    assert_val_eq!(result, int(42));

    // Generic alias wrapping a function type
    let result = session.run(indoc! { r#"
        type Transform<A, B> = (A) -> B;

        fn apply(f: Transform<int, int>, x: int) -> int {
            f(x)
        }

        apply(|x| x * 3, 10)
    "# });
    assert_val_eq!(result, int(30));

    // Nested generic aliases
    let result = session.run(indoc! { r#"
        type Pair<A, B> = (A, B);
        type IntPair = Pair<int, int>;

        fn sum(p: IntPair) -> int {
            p.0 + p.1
        }

        sum((3, 4))
    "# });
    assert_val_eq!(result, int(7));

    // Generic alias used with a named type (struct)
    let result = session.run(indoc! { r#"
        struct Box<A> { value: A }
        type BoxedInt = Box<int>;

        fn unbox(b: BoxedInt) -> int {
            b.value
        }

        unbox(Box { value: 55 })
    "# });
    assert_val_eq!(result, int(55));

    // Generic alias to a struct with where constraints: constraints must be instantiated properly
    let result = session.run(indoc! { r#"
        struct MapIterator<I, T, O>
        where
            I: Iterator<Item = T>
        {
            iterator: I,
            mapper: (T) -> O,
        }

        impl<I, T, O> Iterator for MapIterator<I, T, O>
        where
            I: Iterator<Item = T>
        {
            fn next(it: &mut MapIterator<I, T, O>) -> None | Some(O) {
                match next(it.iterator) {
                    Some(data) => Some(it.mapper(data)),
                    None => None,
                }
            }
        }

        type Mapper<I, T, O> = MapIterator<I, T, O>;

        let mut m: Mapper<array_iterator<int>, int, int> = MapIterator {
            iterator: iter([1, 2, 3]),
            mapper: |x| x * 2,
        };
        let mut total = 0;
        for v in m {
            total += v;
        };
        total
    "# });
    assert_val_eq!(result, int(12));

    // Verify generic type alias is stored in the module
    let module_id = session
        .compile(indoc! { r#"
        type Pair<A, B> = (A, B);

        fn dummy() -> int { 0 }
    "# })
        .module_id;
    let module = session.session().expect_fresh_module(module_id);
    let entry = module.get_type_alias(ustr("Pair"));
    assert!(entry.is_some());
    assert_eq!(entry.unwrap().param_count(), 2);
    let rendered = module.format_with(session.session().modules()).to_string();
    assert!(rendered.contains("Pair<A, B>: (A, B)"));

    let module_id = session
        .compile(indoc! { r#"
        type Option<T> = Some(T) | None;

        fn func(x) -> (Some(int) | None) {
            None
        }
    "# })
        .module_id;
    let module = session.session().expect_fresh_module(module_id);
    let module_env = ModuleEnv::new(module, session.session().modules());
    let fn_def = module
        .get_function(ustr("func"))
        .unwrap()
        .definition
        .clone();
    assert_eq!(
        fn_def.ty_scheme.ty().format_with(&module_env).to_string(),
        "(A) -> Option<int>"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn keyword_type_is_acceptable() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run("({type: 1}: {type: int}).type"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_type_aliases_in_explicit_typing() {
    // Generic type aliases must be resolvable as types in Ferlium code, including in
    // function signatures, impl headers, and trait output bindings.
    let mut session = TestSession::new();

    // A function that explicitly names a generic type alias in its signature.
    let result = session.run(indoc! { r#"
        fn my_next(iter: &mut array_iterator<int>) -> None | Some(int) {
            array_iterator_next(iter)
        }
        let mut it = iter([10, 20, 30]);
        my_next(it)
    "# });
    assert_val_eq!(result, some(int(10)));

    // Using a generic type alias in return type position.
    let result = session.run(indoc! { r#"
        fn make_iter(arr: [int]) -> array_iterator<int> {
            iter(arr)
        }
        let mut it = make_iter([5, 6, 7]);
        next(it)
    "# });
    assert_val_eq!(result, some(int(5)));

    // Using a generic type alias in a type annotation.
    let result = session.run(indoc! { r#"
        let mut it = (iter([42]): array_iterator<int>);
        next(it)
    "# });
    assert_val_eq!(result, some(int(42)));

    // Using a generic type alias in a trait impl method signature.
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
    assert_val_eq!(result, some(int(99)));
}
