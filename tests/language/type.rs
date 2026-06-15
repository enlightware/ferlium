// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ferlium::{
    compiler::error::CompilationErrorImpl,
    format::{FormatWith, FormatWithData},
    hir::value::Value,
    std::{
        array::array_type,
        data_value,
        logic::bool_type,
        math::{float_type, int_type},
        string::string_type,
    },
    types::effects::{EffType, PrimitiveEffect, effect, effects},
    types::r#type::{FnType, Type, record_type, tuple_type, variant_type},
};

use indoc::indoc;

use ustr::ustr;

use crate::harness::{TestSession, float, int, string};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn primitive() {
    let mut session = TestSession::new();
    assert_eq!(session.resolve_defined_type("()").unwrap(), Type::unit());
    assert_eq!(session.resolve_defined_type("bool").unwrap(), bool_type());
    assert_eq!(session.resolve_defined_type("int").unwrap(), int_type());
    assert_eq!(session.resolve_defined_type("float").unwrap(), float_type());
    assert_eq!(
        session.resolve_defined_type("string").unwrap(),
        string_type()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tuple() {
    let mut session = TestSession::new();
    assert_eq!(
        session.resolve_defined_type("(int,)").unwrap(),
        tuple_type([int_type()])
    );
    assert_eq!(
        session.resolve_defined_type("(int, int)").unwrap(),
        tuple_type([int_type(), int_type()])
    );
    assert_eq!(
        session.resolve_defined_type("(int, int, int)").unwrap(),
        tuple_type([int_type(), int_type(), int_type()])
    );
    assert_eq!(
        session.resolve_defined_type("(int, float)").unwrap(),
        tuple_type([int_type(), float_type()])
    );
    assert_eq!(
        session
            .resolve_defined_type("(int, (bool, string))")
            .unwrap(),
        tuple_type([int_type(), tuple_type([bool_type(), string_type()])])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn record() {
    let mut session = TestSession::new();
    assert_eq!(
        session.resolve_defined_type("{a: int}").unwrap(),
        record_type([("a", int_type())])
    );
    assert_eq!(
        session.resolve_defined_type("{a: int,}").unwrap(),
        record_type([("a", int_type())])
    );
    assert_eq!(
        session.resolve_defined_type("{a: int, b: bool}").unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        session.resolve_defined_type("{a: int, b: bool, }").unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        session.resolve_defined_type("{b: bool, a: int}").unwrap(),
        record_type([("a", int_type()), ("b", bool_type())])
    );
    assert_eq!(
        session.resolve_defined_type("{b: bool, a: int}").unwrap(),
        session.resolve_defined_type("{a: int, b: bool}").unwrap(),
    );
    assert_eq!(
        session
            .resolve_defined_type("{a: int, b: { c: bool, d: float } }")
            .unwrap(),
        record_type([
            ("a", int_type()),
            ("b", record_type([("c", bool_type()), ("d", float_type())]))
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variant() {
    let mut session = TestSession::new();
    assert_eq!(
        session.resolve_defined_type("Some(int)|None").unwrap(),
        variant_type([("Some", tuple_type([int_type()])), ("None", Type::unit()),])
    );
    assert_eq!(
        session
            .resolve_defined_type("RGB (int, int, int) | Color(string)")
            .unwrap(),
        variant_type([
            ("RGB", tuple_type([int_type(), int_type(), int_type()])),
            ("Color", tuple_type([string_type()])),
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parentheses() {
    let mut session = TestSession::new();
    assert_eq!(session.resolve_defined_type("int").unwrap(), int_type());
    assert_eq!(session.resolve_defined_type("(int)").unwrap(), int_type());
    assert_eq!(session.resolve_defined_type("((int))").unwrap(), int_type());
    assert_eq!(
        session.resolve_defined_type("(((int)))").unwrap(),
        int_type()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_type() {
    let mut session = TestSession::new();
    assert_eq!(
        session.resolve_defined_type("() -> ()").unwrap(),
        Type::function_by_val_with_effects([], Type::unit(), EffType::empty())
    );
    assert_eq!(
        session.resolve_defined_type("(int) -> int").unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        session.resolve_defined_type("((int)) -> int").unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        session.resolve_defined_type("(int) -> (int)").unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        session.resolve_defined_type("(int) -> (int,)").unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            tuple_type([int_type()]),
            EffType::empty()
        )
    );
    assert_eq!(
        session.resolve_defined_type("(int, float) -> ()").unwrap(),
        Type::function_by_val_with_effects(
            [int_type(), float_type()],
            Type::unit(),
            EffType::empty()
        )
    );
    assert_eq!(
        session
            .resolve_defined_type("((int, float)) -> ()")
            .unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            Type::unit(),
            EffType::empty()
        )
    );
    assert_eq!(
        session
            .resolve_defined_type("((int, float)) -> (bool, string)")
            .unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            tuple_type([bool_type(), string_type()]),
            EffType::empty()
        )
    );
    assert_eq!(
        session.resolve_defined_type("(&mut [int]) -> int").unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(int_type()), true)],
            int_type(),
            EffType::empty()
        ))
    );
    assert_eq!(
        session
            .resolve_defined_type("(&mut [float], &mut int) -> ()")
            .unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(float_type()), true), (int_type(), true)],
            Type::unit(),
            EffType::empty()
        ))
    );

    assert_eq!(
        session.resolve_holed_type("() -> ()").unwrap(),
        Type::function_by_val_with_effects([], Type::unit(), EffType::single_variable_id(0))
    );
    assert_eq!(
        session.resolve_holed_type("(int) -> int").unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("((int)) -> int").unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("(int) -> (int)").unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("(int) -> (int,)").unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            tuple_type([int_type()]),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("(int, float) -> ()").unwrap(),
        Type::function_by_val_with_effects(
            [int_type(), float_type()],
            Type::unit(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("((int, float)) -> ()").unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            Type::unit(),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session
            .resolve_holed_type("((int, float)) -> (bool, string)")
            .unwrap(),
        Type::function_by_val_with_effects(
            [tuple_type([int_type(), float_type()])],
            tuple_type([bool_type(), string_type()]),
            EffType::single_variable_id(0)
        )
    );
    assert_eq!(
        session.resolve_holed_type("(&mut [int]) -> int").unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(int_type()), true)],
            int_type(),
            EffType::single_variable_id(0)
        ))
    );
    assert_eq!(
        session
            .resolve_holed_type("(&mut [float], &mut int) -> ()")
            .unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(float_type()), true), (int_type(), true)],
            Type::unit(),
            EffType::single_variable_id(0)
        ))
    );
    assert_eq!(
        session.resolve_defined_type("((int) -> int ! ())").unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        session
            .resolve_defined_type("((int) -> int ! fallible)")
            .unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            effect(PrimitiveEffect::Fallible)
        )
    );
    assert_eq!(
        session
            .resolve_defined_type("((int) -> int ! (write, read))")
            .unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            effects(&[PrimitiveEffect::Read, PrimitiveEffect::Write])
        )
    );
    assert_eq!(
        session.resolve_holed_type("((int) -> int ! ())").unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty())
    );
    assert_eq!(
        session.resolve_defined_type("(int) -> int ! read").unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), effect(PrimitiveEffect::Read))
    );
    assert_eq!(
        session
            .resolve_defined_type("(int) -> int ! (read, write)")
            .unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            int_type(),
            effects(&[PrimitiveEffect::Read, PrimitiveEffect::Write])
        )
    );
    assert_eq!(
        session.resolve_holed_type("((int) -> int ! read)").unwrap(),
        Type::function_by_val_with_effects([int_type()], int_type(), effect(PrimitiveEffect::Read))
    );
    assert_eq!(
        session
            .resolve_defined_type("() -> (int) -> int ! read")
            .unwrap(),
        Type::function_by_val_with_effects(
            [],
            Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty()),
            effect(PrimitiveEffect::Read)
        )
    );
    assert_eq!(
        session
            .resolve_defined_type("(int) -> ((int) -> int ! read)")
            .unwrap(),
        Type::function_by_val_with_effects(
            [int_type()],
            Type::function_by_val_with_effects(
                [int_type()],
                int_type(),
                effect(PrimitiveEffect::Read)
            ),
            EffType::empty()
        )
    );
    assert!(
        format!(
            "{}",
            FormatWithData::new(
                &session
                    .resolve_defined_type("((int) -> int ! unknown)")
                    .unwrap_err(),
                session.source_table(),
            )
        )
        .contains("Cannot find effect `unknown`")
    );
    assert_eq!(
        session
            .resolve_defined_type("(() -> ((int) -> int) ! read)")
            .unwrap(),
        Type::function_by_val_with_effects(
            [],
            Type::function_by_val_with_effects([int_type()], int_type(), EffType::empty()),
            effect(PrimitiveEffect::Read)
        )
    );

    assert!(
        format!(
            "{}",
            FormatWithData::new(
                &session.resolve_defined_type("(&mut int)").unwrap_err(),
                session.source_table(),
            )
        )
        .starts_with(
            "Parsing failed: types outside function arguments cannot be &mut in `&mut int`"
        )
    );
    assert!(
        format!(
            "{}",
            FormatWithData::new(
                &session.resolve_defined_type("(&mut int,)").unwrap_err(),
                session.source_table(),
            )
        )
        .starts_with(
            "Parsing failed: types outside function arguments cannot be &mut in `&mut int`"
        )
    );
    assert!(
        format!(
            "{}",
            FormatWithData::new(
                &session
                    .resolve_defined_type("(bool, float, &mut int)")
                    .unwrap_err(),
                session.source_table(),
            )
        )
        .starts_with(
            "Parsing failed: types outside function arguments cannot be &mut in `&mut int`"
        )
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_types() {
    let mut session = TestSession::new();
    assert_eq!(
        session.resolve_holed_type("_").unwrap(),
        Type::variable_id(0)
    );
    assert_eq!(
        session.resolve_holed_type("(int, _)").unwrap(),
        tuple_type([int_type(), Type::variable_id(0)])
    );
    assert_eq!(
        session.resolve_holed_type("(_, _)").unwrap(),
        tuple_type([Type::variable_id(0), Type::variable_id(0)])
    );
    assert_eq!(
        session
            .resolve_holed_type("(&mut [_], &mut int) -> _")
            .unwrap(),
        Type::function_type(FnType::new_mut_resolved(
            [(array_type(Type::variable_id(0)), true), (int_type(), true)],
            Type::variable_id(0),
            EffType::single_variable_id(0)
        ))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn complex_type() {
    let mut session = TestSession::new();
    assert_eq!(
        session
            .resolve_defined_type("[{name: string, age: int, nick: Some(string) | None}]")
            .unwrap(),
        array_type(record_type([
            ("name", string_type()),
            ("age", int_type()),
            (
                "nick",
                variant_type([
                    ("Some", tuple_type([string_type()])),
                    ("None", Type::unit()),
                ])
            )
        ]))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn variant_type_ascription() {
    let mut session = TestSession::new();
    let result = session.run(indoc! { r#"
        fn score(value) -> int {
            match value {
                Some { value } => value,
                Pair(x, y) => x + y,
                Empty => 0,
            }
        }

        let record: Some { value: int } | Pair(int, int) | Empty = Some { value: 40 };
        let tuple: Some { value: int } | Pair(int, int) | Empty = Pair(1, 2);
        let unit: Some { value: int } | Pair(int, int) | Empty = Empty;

        (
            score(record),
            score(tuple),
            score(unit),
        )
    "# });
    assert_val_eq!(result, tuple!(int(40), int(3), int(0)),);

    // Limitation: to avoid a conflict, return types instantiate the grammar without record variants.
    let err = session.fail_compilation(indoc! { r#"
        fn invalid() -> Some { value: int } | Pair(int, int) {
            Empty
        }
    "# });
    match err.into_inner() {
        CompilationErrorImpl::ParsingFailed(_) => {}
        other => {
            panic!("expected parsing failure for record-style variant return types, got {other:?}")
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ret_type_overloading() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            fn f() { let a = 0; a }
            ((f(): int), (f(): float))
        "# }),
        tuple!(int(0), float(0.0)),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn returning_data_value_array_is_properly_unified() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(indoc! { r#"
        fn make_data_value_array() -> DataValue {
            DataValue::Array([])
        }
    "# });

    let fn_def = &module
        .get_function(ustr("make_data_value_array"))
        .unwrap()
        .definition;
    assert_eq!(
        fn_def.ty_scheme.ty().ret,
        data_value::data_value_type(),
        "Expected return type to be DataValue"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn data_value_type_in_function_signature() {
    let mut session = TestSession::new();
    // Test that DataValue is preserved in function signatures instead of appearing unfolded.
    let module_id = session
        .compile(indoc! { r#"
        fn process_data_value(v: DataValue) -> DataValue {
            v
        }

        fn process_data_value_entries(entries: [(string, DataValue)]) -> DataValue {
            entries[0].1
        }
    "# })
        .module_id;

    // Check first function
    let module = session.session().expect_fresh_module(module_id);
    let fn_def1 = &module
        .get_function(ustr("process_data_value"))
        .unwrap()
        .definition;
    let sig1 = fn_def1
        .ty_scheme
        .ty()
        .clone()
        .format_with(&session.std_module_env())
        .to_string();

    // The signature should contain "DataValue", not the unfolded type.
    assert!(
        sig1.contains("DataValue"),
        "Expected 'DataValue' in signature, got: {}",
        sig1
    );
    assert!(
        !sig1.contains("Array ([Self])"),
        "Type alias should not be unfolded, got: {}",
        sig1
    );

    // Check second function
    let fn_def2 = &module
        .get_function(ustr("process_data_value_entries"))
        .unwrap()
        .definition;
    let sig2 = fn_def2
        .ty_scheme
        .ty()
        .format_with(&session.std_module_env())
        .to_string();

    let arg_ty = fn_def2.ty_scheme.ty().args[0].ty;
    let arg_ty_data = arg_ty.data();
    if let Some(arr) = arg_ty_data.as_native() {
        let elem_data = arr.arguments[0].data();
        if let Some(tup) = elem_data.as_tuple() {
            assert_eq!(
                tup[1],
                data_value::data_value_type(),
                "Tuple element should be the canonical DataValue type from std"
            );
        } else {
            panic!("Expected array element to be a tuple");
        }
    }

    // The signature should contain "DataValue", not the unfolded type.
    assert!(
        sig2.contains("DataValue"),
        "Expected 'DataValue' in signature, got: {}",
        sig2
    );
    assert!(
        !sig2.contains("Array ([Self])"),
        "Type alias should not be unfolded, got: {}",
        sig2
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_impl_for_specified() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            struct S(string)
            struct Wrapper<T>(T)
            impl Ord for S {
                fn cmp(self, other: S) {
                    cmp(len(self.0), len(other.0))
                }
            }
            impl Cast for <int, S> {
                fn cast(self) -> S {
                    S(f"hello {self}")
                }
            }
            impl<T> Cast for <From = T, To = Wrapper<T>> {
                fn cast(self) -> Wrapper<T> {
                    Wrapper(self)
                }
            }
            let left = ((1: int) as S).0;
            let wrapped: Wrapper<int> = cast(2);
            let right = wrapped.0;
            f"{left} / {right}"
        "# }),
        string("hello 1 / 2")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_impl_where_clause_is_used_for_selection() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! { r#"
            struct Wrapper<T>(T)

            impl<T> SizedSeq for Wrapper<T>
            where
                T: Iterator<Item = int>
            {
                fn len(self) {
                    3
                }
            }

            impl SizedSeq for Wrapper<int> {
                fn len(self) {
                    self.0
                }
            }

            len(Wrapper(0..3 |> iter())) + len(Wrapper(5))
        "# }),
        int(8)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_impl_orphan_rule() {
    let mut session = TestSession::new();
    let err = session.fail_compilation(indoc! { r#"
        impl Ord for int {
            fn cmp(self, other: int) {
                cmp(self, other)
            }
        }
    "# });
    match err.into_inner() {
        CompilationErrorImpl::TraitImplOrphanRuleViolation { .. } => {}
        other => panic!("expected TraitImplOrphanRuleViolation, got {other:?}"),
    }

    session
        .try_compile_module("a", "pub struct ForeignCounter(int)")
        .unwrap();
    let err = session
        .try_compile_module(
            "b",
            indoc! { r#"
                impl SizedSeq for a::ForeignCounter {
                    fn len(counter: a::ForeignCounter) {
                        counter.0
                    }
                }
            "# },
        )
        .expect_err("expected orphan rule violation for foreign named type");
    match err.into_inner() {
        CompilationErrorImpl::TraitImplOrphanRuleViolation { .. } => {}
        other => panic!("expected TraitImplOrphanRuleViolation, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn overlapping_concrete_trait_impls_are_rejected() {
    let mut session = TestSession::new();
    let err = session.fail_compilation(indoc! { r#"
        struct S(int)

        impl Ord for S {
            fn cmp(self, other: S) {
                cmp(self.0, other.0)
            }
        }

        impl Ord for S {
            fn cmp(self, other: S) {
                cmp(other.0, self.0)
            }
        }
    "# });
    match err.into_inner() {
        CompilationErrorImpl::OverlappingTraitImpls { .. } => {}
        other => panic!("expected OverlappingTraitImpls, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn overlapping_trait_impls_with_where_clauses_are_rejected() {
    let mut session = TestSession::new();
    let err = session.fail_compilation(indoc! { r#"
        struct CounterIter {
            next: int,
            end: int,
        }

        impl Iterator for CounterIter {
            fn next(it: &mut CounterIter) -> None | Some(int) {
                if it.next < it.end {
                    let current = it.next;
                    it.next += 1;
                    Some(current)
                } else {
                    None
                }
            }
        }

        struct Wrapper<T>(T)

        impl<T> SizedSeq for Wrapper<T>
            where
                T: Iterator<Item = int>
            {
                fn len(self) {
                    0
                }
            }

        impl SizedSeq for Wrapper<CounterIter> {
            fn len(self) {
                0
            }
        }
    "# });
    match err.into_inner() {
        CompilationErrorImpl::OverlappingTraitImpls { .. } => {}
        other => panic!("expected OverlappingTraitImpls, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn overlapping_blanket_trait_impls_are_rejected() {
    let mut session = TestSession::new();
    let err = session.fail_compilation(indoc! { r#"
        struct Wrapper<T>(T)

        impl<T> Cast for <From = T, To = Wrapper<T>> {
            fn cast(self) -> Wrapper<T> {
                Wrapper(self)
            }
        }

        impl Cast for <From = int, To = Wrapper<int>> {
            fn cast(self) -> Wrapper<int> {
                Wrapper(self + 1)
            }
        }
    "# });
    match err.into_inner() {
        CompilationErrorImpl::OverlappingTraitImpls { .. } => {}
        other => panic!("expected OverlappingTraitImpls, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn impl_overlap_accounts_for_trait_output_bindings() {
    let mut session = TestSession::new();
    session.compile(indoc! { r#"
        trait Adapter<Self |-> Output> {
            fn adapt(value: Self) -> Output;
        }

        impl<I, T> Adapter for <Self = I |-> Output = I>
        where
            I: Iterator<Item = T>,
            I: Value
        {
            fn adapt(value: I) -> I {
                value
            }
        }

        impl<A> Adapter for <Self = [A] |-> Output = ArrayIterator<A>>
        where
            A: Value
        {
            fn adapt(value: [A]) -> ArrayIterator<A> {
                iter(value)
            }
        }
    "# });
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn matching_trait_output_bindings_still_reject_real_overlap() {
    let mut session = TestSession::new();
    let err = session.fail_compilation(indoc! { r#"
        trait Adapter<Self |-> Output> {
            fn adapt(value: Self) -> Output;
        }

        struct CounterIter {
            next: int,
            end: int,
        }

        impl Iterator for CounterIter {
            fn next(it: &mut CounterIter) -> None | Some(int) {
                if it.next < it.end {
                    let current = it.next;
                    it.next += 1;
                    Some(current)
                } else {
                    None
                }
            }
        }

        impl<I, T> Adapter for <Self = I |-> Output = I>
        where
            I: Iterator<Item = T>,
            I: Value
        {
            fn adapt(value: I) -> I {
                value
            }
        }

        impl Adapter for <Self = CounterIter |-> Output = CounterIter> {
            fn adapt(value: CounterIter) -> CounterIter {
                value
            }
        }
    "# });
    match err.into_inner() {
        CompilationErrorImpl::OverlappingTraitImpls { .. } => {}
        other => panic!("expected OverlappingTraitImpls, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_variant_value_derivation() {
    let mut session = TestSession::new();
    let code = indoc! { r#"
        fn buggy(s: string) -> DataValue {
            (deserialize(parse_json(s)) : DataValue)
        }
    "# };
    session.compile(code);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_method_circular_deps() {
    let mut session = TestSession::new();
    session.compile(indoc! { r#"
        struct S(string)
        impl Ord for S {
            fn cmp(self, other: S) {
                cmp(ls(self.0), ls(other.0))
            }
        }
        fn ls(s: string) -> int {
            len(s)
        }
        fn test() {
            let a = S("hello");
            let b = S("world!");
            cmp(a, b)
        }
    "# });
}
