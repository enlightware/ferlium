// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use crate::harness::{TestSession, int};
use ferlium::{compiler::error::CompilationErrorImpl, hir::value::Value};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_generic_struct_auto_derives_value() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(
            r#"
            struct Wrapper<T>(T)

            fn clone_wrapper<T>(value: T) -> Wrapper<T>
            where
                T: Value
            {
                let mut wrapped = Wrapper(value);
                wrapped
            }

            clone_wrapper(41).0
            "#
        ),
        int(41)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn auto_derived_struct_value_clone_uses_field_clone() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(
            r#"
            struct Probe(int)
            struct Wrapper<T>(T)

            impl Value for Probe {
                fn eq(left: Probe, right: Probe) -> bool {
                    left.0 == right.0
                }

                fn to_string(value: Probe) -> string {
                    to_string(value.0)
                }

                fn hash(value: Probe, state: &mut hasher) {
                    hash(value.0, state)
                }

                fn clone(source: Probe, target: &mut Probe) {
                    target = Probe(source.0 + 10);
                }

                fn drop(target: &mut Probe) {}
            }

            let original = Wrapper(Probe(5));
            let mut cloned = original;
            (original.0.0, cloned.0.0)
            "#
        ),
        tuple!(int(5), int(15))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_generic_enum_auto_derives_value() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(
            r#"
            struct Probe(int)

            enum Boxed<T> {
                Empty,
                Item(T),
            }

            impl Value for Probe {
                fn eq(left: Probe, right: Probe) -> bool {
                    left.0 == right.0
                }

                fn to_string(value: Probe) -> string {
                    to_string(value.0)
                }

                fn hash(value: Probe, state: &mut hasher) {
                    hash(value.0, state)
                }

                fn clone(source: Probe, target: &mut Probe) {
                    target = Probe(source.0 + 10);
                }

                fn drop(target: &mut Probe) {}
            }

            fn clone_boxed<T>(value: Boxed<T>) -> Boxed<T>
            where
                T: Value
            {
                let mut boxed = value;
                boxed
            }

            match clone_boxed(Boxed::Item(Probe(7))) {
                Item(value) => value.0,
                Empty => 0,
            }
            "#
        ),
        int(17)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn explicit_concrete_value_impl_suppresses_auto_blanket_impl() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(
            r#"
            struct Wrapper<T>(T)

            impl Value for Wrapper<int> {
                fn eq(left: Wrapper<int>, right: Wrapper<int>) -> bool {
                    left.0 == right.0
                }

                fn to_string(value: Wrapper<int>) -> string {
                    "custom"
                }

                fn hash(value: Wrapper<int>, state: &mut hasher) {
                    hash(value.0, state)
                }

                fn clone(source: Wrapper<int>, target: &mut Wrapper<int>) {
                    target = Wrapper(source.0 + 10);
                }

                fn drop(target: &mut Wrapper<int>) {}
            }

            let original = Wrapper(1);
            let mut cloned = original;
            cloned.0
            "#
        ),
        int(11)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn value_impl_for_foreign_named_adt_is_rejected() {
    let mut session = TestSession::new();
    session
        .try_compile_module("a", "struct Foreign(int)")
        .unwrap();
    let err = session
        .try_compile_module(
            "b",
            r#"
            impl Value for a::Foreign {
                fn eq(left: a::Foreign, right: a::Foreign) -> bool {
                    left.0 == right.0
                }

                fn to_string(value: a::Foreign) -> string {
                    to_string(value.0)
                }

                fn hash(value: a::Foreign, state: &mut hasher) {
                    hash(value.0, state)
                }

                fn clone(source: a::Foreign, target: &mut a::Foreign) {
                    target = source;
                }

                fn drop(target: &mut a::Foreign) {}
            }
            "#,
        )
        .expect_err("expected foreign Value impl to be rejected");
    match err.into_inner() {
        CompilationErrorImpl::TraitImplOrphanRuleViolation { .. } => {}
        other => panic!("expected TraitImplOrphanRuleViolation, got {other:?}"),
    }
}
