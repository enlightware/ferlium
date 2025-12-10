// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use ustr::ustr;

use super::common::TestSession;
use ferlium::{effects::*, module::LocalImplId};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

pub fn test_mod(session: &mut TestSession, src: &str, f: &str, exp_eff: EffType) {
    let module = session.compile(src);
    let effects = module
        .module
        .get_unique_own_function(ustr(f))
        .unwrap()
        .definition
        .ty_scheme
        .ty()
        .effects
        .clone();
    assert_eq!(effects, exp_eff);
}

fn test_expr(session: &mut TestSession, src: &str, exp_eff: EffType) {
    let module = session.compile(src);
    let effects = module.expr.unwrap().expr.effects.clone();
    assert_eq!(effects, exp_eff);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_mod() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    test_mod(
        &mut session,
        "fn r() { effects::read() } fn w() { effects::write() }",
        "r",
        effect(Read),
    );
    test_mod(
        &mut session,
        "fn r() { effects::read() } fn w() { effects::write() }",
        "w",
        effect(Write),
    );
    test_mod(
        &mut session,
        "fn rw() { effects::write(); effects::read() }",
        "rw",
        effects(&[Read, Write]),
    );
    test_mod(
        &mut session,
        "fn rw() { effects::write(); effects::read() } fn o() { rw() } ",
        "o",
        effects(&[Read, Write]),
    );
    test_mod(
        &mut session,
        "fn r() { effects::read() } fn t1() { r() } fn t2() { t1() }",
        "t2",
        effect(Read),
    );
    test_mod(
        &mut session,
        "fn rw() { effects::write(); effects::read() } fn o() { ((rw, ).0)() } ",
        "o",
        effects(&[Read, Write]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_expr() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    test_expr(
        &mut session,
        "let a = |f| f(); a(|| effects::write())",
        effect(Write),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_variance() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // passing pure to read
    test_mod(
        &mut session,
        "fn pure() { () } fn f() { effects::take_read(pure) } ",
        "f",
        effect(Read),
    );

    // passing read to read
    test_mod(
        &mut session,
        "fn f() { effects::take_read(effects::read) } ",
        "f",
        effect(Read),
    );
    test_mod(
        &mut session,
        "fn r() { effects::read() } fn f() { effects::take_read(r) } ",
        "f",
        effect(Read),
    );

    // passing write to read, should fail
    session
        .fail_compilation("fn f() { effects::take_read(effects::write) }")
        .expect_invalid_effect_dependency(effect(Write), effect(Read));
    session
        .fail_compilation("fn w() { effects::write() } fn f() { effects::take_read(w) }")
        .expect_invalid_effect_dependency(effect(Write), effect(Read));

    // passing read, write to read, should fail
    session
        .fail_compilation("fn f() { effects::take_read(effects::read_write) }")
        .expect_invalid_effect_dependency(effects(&[Read, Write]), effect(Read));
    session
        .fail_compilation(
            "fn rw() { effects::read(); effects::write() } fn f() { effects::take_read(rw) }",
        )
        .expect_invalid_effect_dependency(effects(&[Read, Write]), effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_from_fn_value() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let code1 = "fn a(f) { f() } fn b() { a(|| effects::write()) }";
    test_mod(&mut session, code1, "a", effect_var(0));
    test_mod(&mut session, code1, "b", effect(Write));

    let code2 = "fn a(f, g) { b(f); f(); g(); () } fn b(f) { a(f, || effects::write()) }";
    test_mod(
        &mut session,
        code2,
        "a",
        effect(Write).union(&effect_vars(&[0, 1])),
    );
    test_mod(
        &mut session,
        code2,
        "b",
        effect(Write).union(&effect_var(0)),
    );

    let code3 = "fn b(f) { a(f, || effects::write()) } fn a(f, g) { b(f); f(); g(); () } ";
    test_mod(
        &mut session,
        code3,
        "a",
        effect(Write).union(&effect_vars(&[0, 1])),
    );
    test_mod(
        &mut session,
        code3,
        "b",
        effect(Write).union(&effect_var(0)),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_recursive_fns() {
    let mut session = TestSession::new();

    test_mod(
        &mut session,
        "fn a(f) { b(f); f() } fn b(f) { a(f) }",
        "b",
        effect_var(0),
    );

    test_mod(
        &mut session,
        "fn a(f, g) { b(f, g); f() } fn b(f, g) { a(f, g); g() }",
        "a",
        effect_vars(&[0, 1]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_of_fn_called_multiple_times() {
    let mut session = TestSession::new();

    test_mod(
        &mut session,
        "fn a(f) { f(); f(); f(); () }",
        "a",
        effect_var(0),
    );
    test_mod(
        &mut session,
        "fn a(f, g) { f(); g(); g(); f(); f(); g(); () }",
        "a",
        effect_vars(&[0, 1]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_fn_type_ascription() {
    let mut session = TestSession::new();

    test_mod(
        &mut session,
        "fn g(f: (() -> (), () -> ())) { (f.0(), f.1()) }",
        "g",
        effect_vars(&[0, 1]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_impl_effect_must_not_have_more_than_def_effects() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // Serialize trait method is not fallible, but implementation calls panic which is fallible.
    session
        .fail_compilation(
            r#"
        struct S;
        impl Serialize {
            fn serialize(x: S) {
                if true { std::panic("cannot serialize!") } else { None }
            }
        }
        "#,
        )
        .expect_trait_method_effect_mismatch(
            "Serialize",
            "serialize",
            &EffType::empty(),
            &effect(Fallible),
        );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_impl_effect_must_have_at_least_def_effects() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // Deserialize trait method is fallible, pure implementation is OK (subset).
    let module = session
        .compile(
            r#"
        struct S;
        impl Deserialize {
            fn deserialize(v) {
                S
            }
        }
        "#,
        )
        .module;
    let fn_id = module
        .impls
        .get_impl_by_local_id(LocalImplId::from_index(0))
        .methods[0];
    let effects = &module
        .get_own_function_by_id(fn_id)
        .unwrap()
        .definition
        .ty_scheme
        .ty()
        .effects;
    assert_eq!(effects, &effect(Fallible));
}
