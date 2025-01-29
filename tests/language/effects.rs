// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use super::common::{compile, fail_compilation};
use painturscript::effects::*;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

pub fn test_mod(src: &str, f: &str, exp_eff: EffType) {
    let (module, others) = compile(src);
    let effects = module
        .module
        .get_local_function(f)
        .unwrap()
        .definition
        .ty_scheme
        .ty()
        .effects
        .clone();
    assert_eq!(effects, exp_eff);
    drop(others);
}

fn test_expr(src: &str, exp_eff: EffType) {
    let (module, others) = compile(src);
    let effects = module.expr.unwrap().expr.effects.clone();
    assert_eq!(effects, exp_eff);
    drop(others);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_mod() {
    use PrimitiveEffect::*;

    test_mod(
        "fn r() { effects::read() } fn w() { effects::write() }",
        "r",
        effect(Read),
    );
    test_mod(
        "fn r() { effects::read() } fn w() { effects::write() }",
        "w",
        effect(Write),
    );
    test_mod(
        "fn rw() { effects::write(); effects::read() }",
        "rw",
        effects(&[Read, Write]),
    );
    test_mod(
        "fn rw() { effects::write(); effects::read() } fn o() { rw() } ",
        "o",
        effects(&[Read, Write]),
    );
    test_mod(
        "fn r() { effects::read() } fn t1() { r() } fn t2() { t1() }",
        "t2",
        effect(Read),
    );
    test_mod(
        "fn rw() { effects::write(); effects::read() } fn o() { ((rw, ).0)() } ",
        "o",
        effects(&[Read, Write]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_expr() {
    use PrimitiveEffect::*;

    test_expr("let a = |f| f(); a(|| effects::write())", effect(Write));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_variance() {
    use PrimitiveEffect::*;

    // passing pure to read
    test_mod(
        "fn pure() { () } fn f() { effects::take_read(pure) } ",
        "f",
        effect(Read),
    );

    // passing read to read
    test_mod(
        "fn f() { effects::take_read(effects::read) } ",
        "f",
        effect(Read),
    );
    test_mod(
        "fn r() { effects::read() } fn f() { effects::take_read(r) } ",
        "f",
        effect(Read),
    );

    // passing write to read, should fail
    fail_compilation("fn f() { effects::take_read(effects::write) }")
        .expect_invalid_effect_dependency(effect(Write), effect(Read));
    fail_compilation("fn w() { effects::write() } fn f() { effects::take_read(w) }")
        .expect_invalid_effect_dependency(effect(Write), effect(Read));

    // passing read, write to read, should fail
    fail_compilation("fn f() { effects::take_read(effects::read_write) }")
        .expect_invalid_effect_dependency(effects(&[Read, Write]), effect(Read));
    fail_compilation(
        "fn rw() { effects::read(); effects::write() } fn f() { effects::take_read(rw) }",
    )
    .expect_invalid_effect_dependency(effects(&[Read, Write]), effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_from_fn_value() {
    use PrimitiveEffect::*;

    let code1 = "fn a(f) { f() } fn b() { a(|| effects::write()) }";
    test_mod(code1, "a", effect_var(0));
    test_mod(code1, "b", effect(Write));

    let code2 = "fn a(f, g) { b(f); f(); g(); () } fn b(f) { a(f, || effects::write()) }";
    test_mod(code2, "a", effect(Write).union(&effect_vars(&[0, 1])));
    test_mod(code2, "b", effect(Write).union(&effect_var(0)));

    // FIXME: this is buggy, as the function order should have no effect
    // let code2 = "fn b(f) { a(f, || effects::write()) } fn a(f, g) { b(f); f(); g(); () } ";
    // test_mod(code2, "a", effect(Write).union(&effect_vars(&[0, 1])));
    // test_mod(code2, "b", effect(Write).union(&effect_var(0)));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_recursive_fns() {
    test_mod("fn a(f) { b(f); f() } fn b(f) { a(f) }", "b", effect_var(0));

    test_mod(
        "fn a(f, g) { b(f, g); f() } fn b(f, g) { a(f, g); g() }",
        "a",
        effect_vars(&[0, 1]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_of_fn_called_multiple_times() {
    test_mod("fn a(f) { f(); f(); f(); () }", "a", effect_var(0));
    test_mod(
        "fn a(f, g) { f(); g(); g(); f(); f(); g(); () }",
        "a",
        effect_vars(&[0, 1]),
    );
}
