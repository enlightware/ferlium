// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use test_log::test;

use indoc::indoc;
use ustr::ustr;

use crate::harness::{TestSession, int};
use ferlium::{
    compiler::{
        error::{CompilationErrorImpl, UnsafeFeature},
        test_support::raw_modules,
    },
    hir::test_support::emit_expr_unsafe,
    module::{LocalImplId, id::Id},
    parse_module_and_expr,
    std::{core_traits_names::DESERIALIZE_TRAIT_NAME, new_module_using_std},
    types::effects::*,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

pub fn test_mod(session: &mut TestSession, src: &str, f: &str, exp_eff: EffType) {
    let module = session.compile_and_get_module(src);
    let effects = module
        .get_function(ustr(f))
        .unwrap()
        .definition
        .ty_scheme
        .ty()
        .effects
        .clone();
    assert_eq!(effects, exp_eff, "effect mismatch for function {f}");
}

fn test_expr(session: &mut TestSession, src: &str, exp_eff: EffType) {
    let module_and_expr = session.compile(src);
    let module_id = module_and_expr.module_id;
    let expr = module_and_expr.expr.unwrap();
    let arena = &session.session().expect_fresh_module(module_id).hir_arena;
    let effects = arena[expr.expr].effects.clone();
    assert_eq!(effects, exp_eff);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_mod() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let mod_src = "fn r() { effects::read() } fn w() { effects::write() }";
    test_mod(&mut session, mod_src, "r", effect(Read));
    test_mod(&mut session, mod_src, "w", effect(Write));
    let mod_src = "fn rw() { effects::write(); effects::read() }";
    test_mod(&mut session, mod_src, "rw", effects(&[Read, Write]));
    let mod_src = "fn rw() { effects::write(); effects::read() } fn o() { rw() } ";
    test_mod(&mut session, mod_src, "o", effects(&[Read, Write]));
    let mod_src = "fn r() { effects::read() } fn t1() { r() } fn t2() { t1() }";
    test_mod(&mut session, mod_src, "t2", effect(Read));
    let mod_src = "fn rw() { effects::write(); effects::read() } fn o() { ((rw, ).0)() } ";
    test_mod(&mut session, mod_src, "o", effects(&[Read, Write]));
    let mod_src = "fn exits_loop() { loop { break } }";
    test_mod(&mut session, mod_src, "exits_loop", effect(Fallible));
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
    test_expr(
        &mut session,
        "loop { break effects::read() }",
        effects(&[Fallible, Read]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fn_variance() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // passing pure to read
    let mod_src = "fn pure() { () } fn f() { effects::take_read(pure) } ";
    test_mod(&mut session, mod_src, "f", effect(Read));

    // passing read to read
    let mod_src = "fn f() { effects::take_read(effects::read) } ";
    test_mod(&mut session, mod_src, "f", effect(Read));
    let mod_src = "fn r() { effects::read() } fn f() { effects::take_read(r) } ";
    test_mod(&mut session, mod_src, "f", effect(Read));

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

    let mod_src = "fn a(f) { f() } fn b() { a(|| effects::write()) }";
    test_mod(&mut session, mod_src, "a", effect_var(0));
    test_mod(&mut session, mod_src, "b", effect(Write));

    let mod_src = "fn a(f, g) { b(f); f(); g(); () } fn b(f) { a(f, || effects::write()) }";
    test_mod(
        &mut session,
        mod_src,
        "a",
        effects(&[Fallible, Write]).union(&effect_vars(&[0, 1])),
    );
    test_mod(
        &mut session,
        mod_src,
        "b",
        effects(&[Fallible, Write]).union(&effect_var(0)),
    );

    let mod_src = "fn b(f) { a(f, || effects::write()) } fn a(f, g) { b(f); f(); g(); () } ";
    test_mod(
        &mut session,
        mod_src,
        "a",
        effects(&[Fallible, Write]).union(&effect_vars(&[0, 1])),
    );
    test_mod(
        &mut session,
        mod_src,
        "b",
        effects(&[Fallible, Write]).union(&effect_var(0)),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn branch_returning_composed_closures_unifies_multiple_effect_variables() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let mod_src = indoc! {r#"
        fn choose(flag, f, g, h, k) {
            if flag {
                |x| g(f(x))
            } else {
                |x| k(h(x))
            }
        }

        fn call_read_write() {
            let composed = choose(
                true,
                |x| { effects::read(); x },
                |x| x,
                |x| x,
                |x| { effects::write(); x },
            );
            composed(1)
        }
    "#};
    test_mod(
        &mut session,
        mod_src,
        "call_read_write",
        effects(&[Read, Write]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_recursive_fns() {
    let mut session = TestSession::new();
    use PrimitiveEffect::Fallible;

    let mod_src = "fn a(f) { b(f); f() } fn b(f) { a(f) }";
    test_mod(
        &mut session,
        mod_src,
        "b",
        effect(Fallible).union(&effect_var(0)),
    );

    let mod_src = "fn a(f, g) { b(f, g); f() } fn b(f, g) { a(f, g); g() }";
    test_mod(
        &mut session,
        mod_src,
        "a",
        effect(Fallible).union(&effect_vars(&[0, 1])),
    );

    let mod_src = "fn apply(f) { f() } fn rf() { apply(rf) }";
    test_mod(&mut session, mod_src, "rf", effect(Fallible));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_of_fn_called_multiple_times() {
    let mut session = TestSession::new();

    let mod_src = "fn a(f) { f(); f(); f(); () }";
    test_mod(&mut session, mod_src, "a", effect_var(0));
    let mod_src = "fn a(f, g) { f(); g(); g(); f(); f(); g(); () }";
    test_mod(&mut session, mod_src, "a", effect_vars(&[0, 1]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_in_fn_type_ascription() {
    let mut session = TestSession::new();
    use PrimitiveEffect::*;

    let mod_src = "fn g(f: (() -> (), () -> ())) { (f.0(), f.1()) }";
    test_mod(&mut session, mod_src, "g", effect_vars(&[0, 1]));
    let mod_src = "fn g(f: ((() -> () ! ()), (() -> () ! read))) { (f.0(), f.1()) }";
    test_mod(&mut session, mod_src, "g", effect(Read));
    let mod_src = "fn g(f: ((() -> () ! fallible), (() -> () ! (read, write)))) { (f.0(), f.1()) }";
    test_mod(
        &mut session,
        mod_src,
        "g",
        effects(&[Fallible, Read, Write]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_access_must_be_fallible() {
    use PrimitiveEffect::*;
    let mut session = TestSession::new();

    let mod_src = "fn f(a: [_]) { a[0] } ";
    test_mod(&mut session, mod_src, "f", effect(Fallible));
    let mod_src = "fn f() { let mut a = []; a[0] = 1; } ";
    test_mod(&mut session, mod_src, "f", effect(Fallible));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_unsafe_is_rejected_in_user_code() {
    let mut session = TestSession::new();

    match session
        .fail_compilation("effects_unsafe { [1][0] }")
        .into_inner()
    {
        CompilationErrorImpl::UnsafeFeatureUseNotAllowed { feature, .. } => {
            assert_eq!(feature, UnsafeFeature::EffectsUnsafe);
        }
        other => panic!("expected UnsafeFeatureUseNotAllowed error, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn effects_unsafe_erases_effects_in_std_context() {
    let session = TestSession::new();
    let source_id = session.source_table().next_id();
    let mod_src = "effects_unsafe { [1][0] }";
    let (_module, expr, arena) = parse_module_and_expr(mod_src, source_id, true)
        .expect("std-context expression should parse");
    let mut module = new_module_using_std(
        ferlium::module::ModuleId::new(0),
        ferlium::module::Path::single_str("$effects_unsafe_test"),
    );
    let compiled = emit_expr_unsafe(
        expr.expect("expected expression"),
        &arena,
        &mut module,
        raw_modules(session.session()),
        vec![],
    )
    .expect("std-context expression should compile");

    assert_eq!(module.hir_arena[compiled.expr].effects, EffType::empty());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_resolve_to_impl_effects() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // The TestEff impl for int is pure, the one for bool has the read effect.
    let mod_src = indoc! {r#"
        fn pure_project(x: int) -> int { testing::TestEff::eff_project(x) }
        fn effectful_project(x: bool) -> int { testing::TestEff::eff_project(x) }
    "#};
    test_mod(&mut session, mod_src, "pure_project", EffType::empty());
    test_mod(&mut session, mod_src, "effectful_project", effect(Read));

    // The same resolution happens for expressions.
    test_expr(
        &mut session,
        "testing::TestEff::eff_project(1)",
        EffType::empty(),
    );
    test_expr(
        &mut session,
        "testing::TestEff::eff_project(true)",
        effect(Read),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_are_quantified_in_generic_functions() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // The generic function's effect is the trait's output effect variable,
    // which gets resolved at concrete call sites through the trait constraint.
    let mod_src = indoc! {r#"
        fn generic_project(x) { testing::TestEff::eff_project(x) }
        fn call_pure(y: int) -> int { generic_project(y) }
        fn call_effectful(y: bool) -> int { generic_project(y) }
    "#};
    test_mod(&mut session, mod_src, "generic_project", effect_var(0));
    test_mod(&mut session, mod_src, "call_pure", EffType::empty());
    test_mod(&mut session, mod_src, "call_effectful", effect(Read));

    // The generic function's scheme carries the effect variable in the
    // trait constraint's output effects.
    let module = session.compile_and_get_module(mod_src);
    let def = &module
        .get_function(ustr("generic_project"))
        .unwrap()
        .definition;
    let output_effs = def
        .ty_scheme
        .constraints
        .iter()
        .find_map(|constraint| {
            let (_, _, _, output_effs, _) = constraint.as_have_trait()?;
            (!output_effs.is_empty()).then(|| output_effs.clone())
        })
        .expect("expected a trait constraint with output effects");
    assert_eq!(output_effs, vec![effect_var(0)]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_propagate_through_blanket_impls() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // The blanket TestEff impl over Option<T> forwards the effect of T's impl.
    let mod_src = indoc! {r#"
        fn pure_project() -> int { testing::TestEff::eff_project(testing::some_int(1)) }
        fn effectful_project() -> int { testing::TestEff::eff_project(testing::some_bool(true)) }
    "#};
    test_mod(&mut session, mod_src, "pure_project", EffType::empty());
    test_mod(&mut session, mod_src, "effectful_project", effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn associated_effect_bindings_accept_parenthesized_values() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let mod_src = indoc! {r#"
        trait Do<Self |-> ! Eff> {
            fn do(value: Self) ! Eff;
        }

        struct Pure;
        struct Single;
        struct Trailing;
        struct Union;

        impl Do for <Self = Pure |-> ! Eff = ()> {
            fn do(value: Pure) {}
        }
        impl Do for <Self = Single |-> ! Eff = (read)> {
            fn do(value: Single) { effects::read() }
        }
        impl Do for <Self = Trailing |-> ! Eff = (read,)> {
            fn do(value: Trailing) { effects::read() }
        }
        impl Do for <Self = Union |-> ! Eff = (read, write)> {
            fn do(value: Union) { effects::read(); effects::write() }
        }

        fn call_pure() { do(Pure) }
        fn call_single() { do(Single) }
        fn call_trailing() { do(Trailing) }
        fn call_union() { do(Union) }
    "#};

    test_mod(&mut session, mod_src, "call_pure", EffType::empty());
    test_mod(&mut session, mod_src, "call_single", effect(Read));
    test_mod(&mut session, mod_src, "call_trailing", effect(Read));
    test_mod(&mut session, mod_src, "call_union", effects(&[Read, Write]));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concrete_trait_output_effect_does_not_leak_inference_slot() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let mod_src = indoc! {r#"
        trait Do<Self |-> ! Eff> {
            fn do(value: Self) ! Eff;
        }

        struct ReadOnly;
        impl Do for <Self = ReadOnly |-> ! Eff = read> {
            fn do(value: ReadOnly) { effects::read() }
        }

        fn call_read() { do(ReadOnly) }
    "#};

    test_mod(&mut session, mod_src, "call_read", effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_dispatch_at_runtime() {
    let mut session = TestSession::new();

    // Trait output effects are compile-time only and do not change dispatch.
    assert_val_eq!(session.run("testing::TestEff::eff_project(21)"), int(42));
    assert_val_eq!(session.run("testing::TestEff::eff_project(true)"), int(1));
    assert_val_eq!(session.run("testing::TestEff::eff_project(false)"), int(0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_are_rejected_in_restricted_contexts() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // The TestEff impl for string has the write effect, so a callback using it
    // cannot be passed where only the read effect is allowed.
    session
        .fail_compilation(
            r#"fn f() { effects::take_read(|| { testing::TestEff::eff_project("s"); () }) }"#,
        )
        .expect_invalid_effect_dependency(effect(Write), effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_multiple_slots_resolve_independently() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // The TestEffPair impl for bool has read in its first effect slot and
    // write in its second one; each method must resolve to its own slot.
    let mod_src = indoc! {r#"
        fn first(x: bool) -> int { testing::TestEffPair::eff_pair_first(x) }
        fn second(x: bool) -> int { testing::TestEffPair::eff_pair_second(x) }
        fn both(x: bool) -> int { testing::TestEffPair::eff_pair_first(x) + testing::TestEffPair::eff_pair_second(x) }
    "#};
    test_mod(&mut session, mod_src, "first", effect(Read));
    test_mod(&mut session, mod_src, "second", effect(Write));
    test_mod(&mut session, mod_src, "both", effects(&[Read, Write]));

    // The same holds through generic functions, where each slot is quantified
    // by its own effect variable.
    let generic_src = indoc! {r#"
        fn generic_first(x) { testing::TestEffPair::eff_pair_first(x) }
        fn generic_second(x) { testing::TestEffPair::eff_pair_second(x) }
        fn generic_both(x) { testing::TestEffPair::eff_pair_first(x) + testing::TestEffPair::eff_pair_second(x) }
        fn call_first(y: bool) -> int { generic_first(y) }
        fn call_second(y: bool) -> int { generic_second(y) }
        fn call_both(y: bool) -> int { generic_both(y) }
    "#};
    test_mod(&mut session, generic_src, "generic_first", effect_var(0));
    test_mod(&mut session, generic_src, "generic_second", effect_var(0));
    test_mod(
        &mut session,
        generic_src,
        "generic_both",
        effect_vars(&[0, 1]),
    );
    test_mod(&mut session, generic_src, "call_first", effect(Read));
    test_mod(&mut session, generic_src, "call_second", effect(Write));
    test_mod(
        &mut session,
        generic_src,
        "call_both",
        effects(&[Read, Write]),
    );

    // Effects are compile-time only; both methods dispatch normally.
    assert_val_eq!(
        session.run("testing::TestEffPair::eff_pair_first(true)"),
        int(1)
    );
    assert_val_eq!(
        session.run("testing::TestEffPair::eff_pair_second(true)"),
        int(2)
    );

    // A read-only context accepts the first (read) slot but rejects the
    // second (write) one.
    session.compile(
        r#"fn ok() { effects::take_read(|| { testing::TestEffPair::eff_pair_first(true); () }) }"#,
    );
    session
        .fail_compilation(
            r#"fn bad() { effects::take_read(|| { testing::TestEffPair::eff_pair_second(true); () }) }"#,
        )
        .expect_invalid_effect_dependency(effect(Write), effect(Read));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_output_effects_can_join_multiple_effect_variables() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    let concrete_src = indoc! {r#"
        fn pure_join() -> int { let x: int = 1; let y: int = 2; testing::TestEffJoin::eff_join((x, y)) }
        fn read_join() -> int { let x: int = 1; testing::TestEffJoin::eff_join((x, true)) }
        fn write_join() -> int { let x: int = 1; testing::TestEffJoin::eff_join((x, "s")) }
        fn read_write_join() -> int { testing::TestEffJoin::eff_join((true, "s")) }
    "#};
    test_mod(&mut session, concrete_src, "pure_join", EffType::empty());
    test_mod(&mut session, concrete_src, "read_join", effect(Read));
    test_mod(&mut session, concrete_src, "write_join", effect(Write));
    test_mod(
        &mut session,
        concrete_src,
        "read_write_join",
        effects(&[Read, Write]),
    );

    let generic_src = indoc! {r#"
        fn generic_join(a, b) { testing::TestEffJoin::eff_join((a, b)) }
        fn call_pure() -> int { let x: int = 1; let y: int = 2; generic_join(x, y) }
        fn call_read() -> int { let x: int = 1; generic_join(x, true) }
        fn call_write() -> int { let x: int = 1; generic_join(x, "s") }
        fn call_read_write() -> int { generic_join(true, "s") }
    "#};
    test_mod(&mut session, generic_src, "generic_join", effect_var(0));
    test_mod(&mut session, generic_src, "call_pure", EffType::empty());
    test_mod(&mut session, generic_src, "call_read", effect(Read));
    test_mod(&mut session, generic_src, "call_write", effect(Write));
    test_mod(
        &mut session,
        generic_src,
        "call_read_write",
        effects(&[Read, Write]),
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_impl_effect_must_not_have_more_than_def_effects() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // Pure trait method cannot be implemented with a fallible body.
    session
        .fail_compilation(
            r#"
        trait Pure<Self> {
            fn pure(x: Self);
        }

        struct S;

        impl Pure for S {
            fn pure(x: S) {
                panic("not pure")
            }
        }
        "#,
        )
        .expect_trait_method_effect_mismatch("Pure", "pure", &EffType::empty(), &effect(Fallible));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_impl_effect_must_have_at_least_def_effects() {
    use PrimitiveEffect::*;

    let mut session = TestSession::new();

    // Deserialize trait method is fallible, pure implementation is OK (subset).
    let mod_src = indoc! { r#"
	    struct S;
	    impl Deserialize {
	        fn deserialize(v) {
	            S
	        }
	    }
    "# };
    let deserialize_trait = session.std_trait(DESERIALIZE_TRAIT_NAME);
    let module = session.compile_and_get_module(mod_src);
    let deserialize_impl = (0..module.impl_count())
        .map(LocalImplId::from_index)
        .find(|&id| {
            let trait_id = module.get_impl_trait_key_by_id(id).unwrap().trait_id();
            trait_id == deserialize_trait
        })
        .unwrap();
    let fn_id = module.get_impl_data(deserialize_impl).unwrap().methods[0];
    let effects = &module
        .get_function_by_id(fn_id)
        .unwrap()
        .definition
        .ty_scheme
        .ty()
        .effects;
    assert_eq!(effects, &effect(Fallible));
}
