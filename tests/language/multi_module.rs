// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use test_log::test;

use ferlium::{
    CompilerSession, DiagnosticSeverity, ExecutionTarget, Path,
    compiler::error::{CompilationErrorImpl, External},
    compiler::test_support::{
        module_compilation_revision, module_diagnostics_len, module_entry_exists,
        module_has_compiled_version, module_has_mir_artifacts, module_is_stale, module_latest_deps,
        module_mir_function_slots, module_source_version,
    },
    format::FormatWith,
    hir::value::Value,
    module::{ConcreteTraitImplKey, ModuleId, Visibility, id::Id},
    types::r#type::Type,
};
use indoc::{formatdoc, indoc};
use ustr::ustr;

use crate::harness::{TestSession, expected_tuple, int, string};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

// ── Helpers ──────────────────────────────────────────────────────────────────

/// Compile `code` as a module named `name` (single-segment path) and return
/// its [`ModuleId`]. Panics only if the compiler returns `Err`; a stale result
/// (e.g. due to stale dependencies) is still considered a success.
fn compile_module(session: &mut TestSession, name: &str, code: &str) -> ModuleId {
    session
        .try_compile_module(name, code)
        .unwrap_or_else(|e| panic!("compile_module({name:?}) failed unexpectedly: {e:?}"))
        .module_id
}

/// Assert that the module `id` is fresh (not stale).
#[track_caller]
fn assert_fresh(session: &TestSession, id: ModuleId, label: &str) {
    assert!(
        !module_is_stale(session.session(), id).unwrap(),
        "{label} should be fresh"
    );
}

/// Assert that the module `id` is stale.
#[track_caller]
fn assert_stale(session: &TestSession, id: ModuleId, label: &str) {
    assert!(
        module_is_stale(session.session(), id).unwrap(),
        "{label} should be stale"
    );
}

/// Recompile `name` with syntactically invalid code, asserting the call returns
/// `Err` so the test fails loudly if the language ever accepts the garbage.
fn break_module(session: &mut TestSession, name: &str) {
    assert!(
        session
            .try_compile_module(name, "this is not valid ferlium !!!")
            .is_err(),
        "breaking module {name:?} should produce a compilation error"
    );
}

fn tree_module_src() -> &'static str {
    indoc! { r#"
        pub enum Tree<T> {
            Leaf(T),
            Node(Tree<T>, Tree<T>),
        }
    "# }
}

fn tree_sum_call_src(module_name: &str) -> String {
    format!(
        "{module_name}::sum(data::Tree::Node(data::Tree::Node(data::Tree::Leaf(2), data::Tree::Leaf(3)), data::Tree::Leaf(4)))"
    )
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_function_is_hidden_across_modules_by_default() {
    let mut session = TestSession::new();

    compile_module(&mut session, "base", "fn val() -> int { 1 }");
    assert!(
        session
            .try_compile_module("user", "pub fn result() -> int { base::val() }")
            .is_err(),
        "module-local functions should not be callable from another module"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_struct_constructor_is_hidden_across_modules_by_default() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            struct Hidden {
                value: int,
            }
        "# },
    );
    assert!(
        session
            .try_compile_module(
                "user",
                "pub fn result() -> int { let hidden = base::Hidden { value: 1 }; hidden.value }",
            )
            .is_err(),
        "module-local struct constructors should not be callable from another module"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_enum_variant_constructor_is_hidden_across_modules_by_default() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            enum Hidden {
                Value(int),
            }
        "# },
    );
    assert!(
        session
            .try_compile_module("user", "pub fn result() { base::Hidden::Value(1) }",)
            .is_err(),
        "module-local enum variant constructors should not be callable from another module"
    );
}

fn private_repr_struct_module_src(with_marker: bool) -> String {
    let source = indoc! { r#"
        pub trait ToInt<Self> {
            fn to_int(value: Self) -> int;
        }

        #[private_repr]
        pub struct Secret {
            value: int,
        }

        pub fn make(value: int) -> Secret {
            Secret { value }
        }

        pub fn value(value: Secret) -> int {
            value.value
        }

        impl ToInt for Secret {
            fn to_int(value: Secret) -> int {
                value.value
            }
        }
    "# };
    if with_marker {
        source
            .replacen("value: int,", "value: int,\n    marker: string,", 1)
            .replacen(
                "Secret { value }",
                "Secret { value, marker: \"secret\" }",
                1,
            )
    } else {
        source.to_owned()
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_named_type_keeps_owner_generated_value_impl_private() {
    let mut session = TestSession::new();
    let base_id = compile_module(&mut session, "base", "struct Hidden(int)");

    let value_trait_id = session
        .session()
        .std_module()
        .get_trait_id_str("Value")
        .expect("std Value trait should be registered");
    let base = session.session().expect_fresh_module(base_id);
    let hidden = Type::named(
        base.get_type_def_id(ustr("Hidden"))
            .expect("Hidden type should be registered"),
        [],
    );
    let key = ConcreteTraitImplKey::new(value_trait_id, vec![hidden]);
    let impl_id = *base
        .get_concrete_impl_by_key(&key)
        .expect("Hidden should have an owner-generated Value implementation");

    assert!(
        !base.get_impl_data(impl_id).unwrap().public,
        "a private named type's generated Value implementation must stay private"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_repr_type_can_be_named_and_used_through_public_trait_impls() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", &private_repr_struct_module_src(false));
    let user_id = compile_module(
        &mut session,
        "user",
        indoc! { r#"
            pub fn duplicate(value: base::Secret) -> (base::Secret, base::Secret) {
                (value, value)
            }

            pub fn result() -> int {
                let pair = duplicate(base::make(5));
                base::ToInt::to_int(pair.0) + base::ToInt::to_int(pair.1)
            }
        "# },
    );

    let base = session.session().expect_fresh_module(base_id);
    assert!(
        base.iter_named_functions()
            .any(|(name, _)| name.as_str().contains("Value<base::Secret>")),
        "the owner should contain the generated Value implementation"
    );
    let user = session.session().expect_fresh_module(user_id);
    assert_eq!(
        user.function_count(),
        2,
        "the consumer should reuse the public owner's Value implementation"
    );
    assert!(
        user.iter_named_functions()
            .all(|(name, _)| !name.as_str().contains("Value<base::Secret>")),
        "the consumer should not regenerate Value methods for the foreign named type"
    );
    assert_val_eq!(session.run("user::result()"), int(10));

    // The generated implementation belongs to the published base revision. Changing the hidden
    // representation must rebuild both that implementation and consumers which reference it.
    session
        .try_compile_module("base", &private_repr_struct_module_src(true))
        .expect("changing the owner's private representation should recompile its consumers");
    assert_fresh(&session, base_id, "base after representation change");
    assert_fresh(&session, user_id, "user after representation change");
    let user = session.session().expect_fresh_module(user_id);
    assert!(
        user.iter_named_functions()
            .all(|(name, _)| !name.as_str().contains("Value<base::Secret>")),
        "the recompiled consumer should still reuse the owner's Value implementation"
    );
    assert_val_eq!(session.run("user::result()"), int(10));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn foreign_generic_value_layout_uses_the_owner_dictionary() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            #[private_repr]
            pub struct Pair<T>(T, T)

            pub fn pair<T>(left: T, right: T) -> Pair<T> {
                Pair(left, right)
            }
        "# },
    );
    compile_module(
        &mut session,
        "user",
        indoc! { r#"
            struct Wrap<T> {
                pair: base::Pair<T>,
                marker: int,
            }

            fn layout<T>(pair: base::Pair<T>) -> int {
                Value::<Wrap<T>>::SIZE + Value::<Wrap<T>>::ALIGN
            }

            pub fn result() -> int {
                layout(base::pair(1, 2))
            }
        "# },
    );

    assert_val_eq!(
        session.run("user::result()"),
        int((4 * std::mem::size_of::<usize>()) as isize)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn public_generic_value_impl_can_use_a_private_representation() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            struct Cell<T>(T)

            #[private_repr]
            pub struct Wrapper<T>(Cell<T>)

            pub fn make(value: int) -> Wrapper<int> {
                Wrapper(Cell(value))
            }

            pub fn value(wrapper: Wrapper<int>) -> int {
                wrapper.0.0
            }
        "# },
    );
    compile_module(
        &mut session,
        "user",
        indoc! { r#"
            pub fn duplicate(
                value: base::Wrapper<int>,
            ) -> (base::Wrapper<int>, base::Wrapper<int>) {
                (value, value)
            }

            pub fn result() -> int {
                let pair = duplicate(base::make(9));
                base::value(pair.0) + base::value(pair.1)
            }
        "# },
    );

    assert_val_eq!(session.run("user::result()"), int(18));
    assert!(
        session
            .try_compile_module(
                "repr_user",
                "pub fn unwrap(value: base::Wrapper<int>) -> int { value.0.0 }",
            )
            .is_err(),
        "reusing the owner's Value implementation must not expose its representation"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_repr_struct_can_be_constructed_and_projected_in_defining_module() {
    let mut session = TestSession::new();

    compile_module(&mut session, "base", &private_repr_struct_module_src(false));

    assert_val_eq!(session.run("base::value(base::make(7))"), int(7));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_repr_struct_constructor_is_hidden_across_modules() {
    let mut session = TestSession::new();

    compile_module(&mut session, "base", &private_repr_struct_module_src(false));
    assert!(
        session
            .try_compile_module(
                "user",
                "pub fn result() -> int { base::value(base::Secret { value: 1 }) }",
            )
            .is_err(),
        "private_repr struct constructors should not be callable from another module"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_repr_struct_fields_are_hidden_across_modules() {
    let mut session = TestSession::new();

    compile_module(&mut session, "base", &private_repr_struct_module_src(false));
    assert!(
        session
            .try_compile_module(
                "user",
                "pub fn result() -> int { let value = base::make(1); value.value }",
            )
            .is_err(),
        "private_repr struct fields should not be projectable from another module"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn public_projection_subscript_exposes_private_repr_across_modules() {
    let mut session = TestSession::new();
    session.allow_experimental();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            #[private_repr]
            pub struct Secret {
                inner: [int],
            }

            pub fn make(value: int) -> Secret {
                Secret { inner: [value] }
            }

            pub subscript Secret.value(self) -> int {
                ref mut {
                    return self.inner[0]
                }
            }
        "# },
    );
    compile_module(
        &mut session,
        "user",
        indoc! { r#"
            fn read_value<T>(value: &mut T) -> int {
                value.value
            }

            pub fn direct() -> int {
                let mut secret = base::make(11);
                secret.value
            }

            pub fn generic() -> int {
                let mut secret = base::make(13);
                read_value(secret)
            }

            pub fn write() -> int {
                let mut secret = base::make(1);
                secret.value = 17;
                secret.value
            }
        "# },
    );

    assert_val_eq!(session.run("user::direct()"), int(11));
    assert_val_eq!(session.run("user::generic()"), int(13));
    assert_val_eq!(session.run("user::write()"), int(17));
}

fn private_repr_enum_module_src() -> &'static str {
    indoc! { r#"
        #[private_repr]
        pub enum Secret {
            Empty,
            Value(int),
        }

        pub fn make(value: int) -> Secret {
            Secret::Value(value)
        }

        pub fn value(value: Secret) -> int {
            match value {
                Secret::Empty => 0,
                Secret::Value(v) => v,
            }
        }
    "# }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_repr_enum_variant_constructor_is_hidden_across_modules() {
    let mut session = TestSession::new();

    compile_module(&mut session, "base", private_repr_enum_module_src());
    assert!(
        session
            .try_compile_module("user", "pub fn result() { base::Secret::Value(1) }",)
            .is_err(),
        "private_repr enum variant constructors should not be callable from another module"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_repr_enum_patterns_are_hidden_across_modules() {
    let mut session = TestSession::new();

    compile_module(&mut session, "base", private_repr_enum_module_src());
    assert!(
        session
            .try_compile_module(
                "user",
                indoc! { r#"
                    pub fn result() -> int {
                        match base::make(1) {
                            base::Secret::Empty => 0,
                            base::Secret::Value(value) => value,
                        }
                    }
                "# },
            )
            .is_err(),
        "private_repr enum variants should not be destructurable from another module"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn pub_function_is_visible_across_modules() {
    let mut session = TestSession::new();

    compile_module(&mut session, "base", "pub fn val() -> int { 1 }");
    compile_module(
        &mut session,
        "user",
        "pub fn result() -> int { base::val() }",
    );

    assert_val_eq!(session.run("user::result()"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generated_function_value_methods_and_lambdas_are_private() {
    let mut session = TestSession::new();
    let module_id = compile_module(
        &mut session,
        "base",
        indoc! { r#"
            fn id(x: int) -> int { x }

            pub fn function_values_equal() -> bool {
                id == id
            }

            pub fn call_lambda() -> int {
                let f = |x| x + 1;
                f(1)
            }
        "# },
    );
    let module = session.session().expect_fresh_module(module_id);

    let function_value_eq = ustr("$_ferlium_function_value_eq");
    assert_eq!(
        module.symbol_visibility(function_value_eq),
        Some(Visibility::Module)
    );
    assert!(
        !module
            .public_symbols()
            .any(|name| name == function_value_eq)
    );

    let lambda_name = module
        .own_symbols()
        .find(|name| name.as_str().starts_with("$lambda$"))
        .expect("module should contain a generated lambda function name");
    assert_eq!(
        module.symbol_visibility(lambda_name),
        Some(Visibility::Module)
    );
    assert!(!module.public_symbols().any(|name| name == lambda_name));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generated_trait_artifacts_are_private() {
    let mut session = TestSession::new();
    let module_id = compile_module(
        &mut session,
        "base",
        "pub fn mapped(values: [int]) -> [int] { map(values, |x| x + 1) }",
    );
    let module = session.session().expect_fresh_module(module_id);
    let generated = module
        .own_symbols()
        .filter(|name| name.as_str().contains("MapIterator"))
        .collect::<Vec<_>>();
    assert!(
        !generated.is_empty(),
        "the map application should generate iterator dictionary artifacts"
    );
    for &name in &generated {
        assert_eq!(
            module.symbol_visibility(name),
            Some(Visibility::Module),
            "generated trait artifact `{name}` must stay inside its module"
        );
        assert!(!module.public_symbols().any(|public| public == name));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generated_trait_method_names_use_qualified_type_names() {
    let mut session = TestSession::new();
    let module_id = compile_module(
        &mut session,
        "base",
        indoc! { r#"
            pub trait ToInt<Self> {
                fn to_int(value: Self) -> int;
            }

            pub struct Wrapped(int)

            impl ToInt for int {
                fn to_int(value: int) -> int {
                    value
                }
            }

            impl ToInt for Wrapped {
                fn to_int(value: Wrapped) -> int {
                    value.0
                }
            }
        "# },
    );
    let module = session.session().expect_fresh_module(module_id);
    let names = module
        .iter_named_functions()
        .map(|(name, _)| name.to_string())
        .collect::<Vec<_>>();
    let to_int_names = names
        .iter()
        .filter(|name| name.starts_with("ToInt<"))
        .collect::<Vec<_>>();

    assert!(
        names
            .iter()
            .any(|name| name.starts_with("ToInt<std::int>::to_int#impl:")),
        "expected native impl name in {names:?}"
    );
    assert!(
        names
            .iter()
            .any(|name| name.starts_with("ToInt<base::Wrapped>::to_int#impl:"))
    );
    assert!(
        to_int_names
            .iter()
            .all(|name| !name.split('<').skip(1).any(|part| part
                .chars()
                .next()
                .is_some_and(|ch| ch.is_ascii_digit())
                && part.contains('-'))),
        "generated trait method names should not contain interned type identities: {names:?}"
    );
    assert!(
        to_int_names.iter().all(|name| {
            let hash = name.split("#impl:").nth(1).unwrap_or_default();
            hash.len() == 8 && hash.chars().all(|ch| ch.is_ascii_hexdigit())
        }),
        "generated impl names should use an 8-character hash suffix: {to_int_names:?}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generated_trait_method_names_disambiguate_impls_with_same_inputs() {
    let mut session = TestSession::new();
    let module_id = compile_module(
        &mut session,
        "base",
        indoc! { r#"
            pub trait Adapter<Self |-> Output> {
                fn adapt(value: Self) -> Output;
            }
            pub trait Small<Self> {}
            pub trait Big<Self> {}

            // Two candidates each, so neither constraint improves `A` to a concrete type.
            impl Small for [int] {}
            impl Small for [bool] {}
            impl Big for [float] {}
            impl Big for [string] {}

            impl<A> Adapter for <Self = [A] |-> Output = [A]>
            where
                [A]: Small
            {
                fn adapt(value: [A]) -> [A] {
                    value
                }
            }

            impl<A> Adapter for <Self = [A] |-> Output = ArrayIterator<A>>
            where
                [A]: Big
            {
                fn adapt(value: [A]) -> ArrayIterator<A> {
                    iter(value)
                }
            }
        "# },
    );
    let module = session.session().expect_fresh_module(module_id);
    let adapter_names = module
        .iter_named_functions()
        .map(|(name, _)| name.to_string())
        .filter(|name| name.starts_with("Adapter<[A]>::adapt"))
        .collect::<Vec<_>>();

    assert_eq!(
        adapter_names.len(),
        2,
        "expected both Adapter impl methods in {adapter_names:?}"
    );
    assert!(
        adapter_names.iter().all(|name| name.contains("#impl:")),
        "generated impl names should include stable disambiguators: {adapter_names:?}"
    );
    assert_ne!(
        adapter_names[0], adapter_names[1],
        "impl methods with the same readable prefix but different constraints must not collide"
    );
    assert_eq!(
        adapter_names
            .iter()
            .map(|name| name.split("#impl:").next().unwrap())
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        1,
        "test should exercise identical readable prefixes: {adapter_names:?}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn coherence_checks_imported_prerequisites_with_their_private_impls() {
    // `base`'s public `P` impl for arrays requires a private `Hidden` impl, which resolution uses
    // when checking that prerequisite. Both `R` impls therefore apply to `[int]`.
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            trait Hidden<Self> {}
            pub trait P<Self> {}
            struct W<T>(T)
            impl<T> Hidden for W<T> {}
            impl<T> P for [T] where W<T>: Hidden {}
        "# },
    );
    let err = session
        .try_compile_module(
            "user",
            indoc! { r#"
                pub trait Q<Self> {}
                pub trait R<Self> {}
                impl<T> Q for [T] {}
                impl<T> R for [T] where [T]: base::P {}
                impl<T> R for [T] where [T]: Q {}
            "# },
        )
        .unwrap_err();
    match err.into_inner() {
        CompilationErrorImpl::OverlappingTraitImpls { .. } => {}
        other => panic!("expected OverlappingTraitImpls, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn public_trait_method_is_visible_across_modules() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            pub trait ToInt<Self> {
                fn to_int(value: Self) -> int;
            }

            impl ToInt for int {
                fn to_int(value: int) -> int {
                    value
                }
            }
        "# },
    );
    compile_module(
        &mut session,
        "user",
        "pub fn result() -> int { base::ToInt::to_int(42) }",
    );

    assert_val_eq!(session.run("user::result()"), int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn module_qualified_method_name_does_not_resolve_trait_method() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            pub trait ToInt<Self> {
                fn to_int(value: Self) -> int;
            }

            impl ToInt for int {
                fn to_int(value: int) -> int {
                    value
                }
            }
        "# },
    );

    assert!(
        session
            .try_compile_module("user", "pub fn result() -> int { base::to_int(42) }")
            .is_err(),
        "module-qualified method names must not scan traits in the module"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn imported_trait_method_is_visible_through_trait_path() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            pub trait ToInt<Self> {
                fn to_int(value: Self) -> int;
            }

            impl ToInt for int {
                fn to_int(value: int) -> int {
                    value
                }
            }
        "# },
    );
    compile_module(
        &mut session,
        "user",
        indoc! { r#"
            use base::ToInt;

            pub fn result() -> int {
                ToInt::to_int(42)
            }
        "# },
    );

    assert_val_eq!(session.run("user::result()"), int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unrelated_explicit_import_does_not_make_trait_method_unqualified() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            pub fn helper() -> int {
                0
            }

            pub trait ToInt<Self> {
                fn to_int(value: Self) -> int;
            }

            impl ToInt for int {
                fn to_int(value: int) -> int {
                    value
                }
            }
        "# },
    );

    assert!(
        session
            .try_compile_module(
                "user",
                indoc! { r#"
                    use base::helper;

                    pub fn result() -> int {
                        to_int(42)
                    }
                "# },
            )
            .is_err(),
        "importing one symbol must not expose unrelated trait methods as unqualified calls"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn module_qualified_inferred_trait_associated_const_resolves() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            pub trait HasConst<Self> {
                const C: Self;
            }

            impl HasConst for int {
                const C = 42;
            }
        "# },
    );
    compile_module(
        &mut session,
        "user",
        "pub fn result() -> int { base::HasConst::C }",
    );

    assert_val_eq!(session.run("user::result()"), int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_trait_method_is_hidden_across_modules() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            trait Hidden<Self> {
                fn hidden(value: Self) -> Self;
            }
        "# },
    );
    assert!(
        session
            .try_compile_module(
                "user",
                "pub fn result() -> int { let f = base::Hidden::hidden; 0 }",
            )
            .is_err(),
        "methods of module-local traits should not be visible across modules"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn impl_for_private_type_is_not_visible_across_modules() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            pub trait ToInt<Self> {
                fn to_int(value: Self) -> int;
            }

            struct Hidden;

            pub fn make_hidden() -> Hidden {
                Hidden
            }

            impl ToInt for Hidden {
                fn to_int(value: Hidden) -> int {
                    1
                }
            }
        "# },
    );
    assert!(
        session
            .try_compile_module(
                "user",
                indoc! { r#"
                    pub fn result() -> int {
                        base::ToInt::to_int(base::make_hidden())
                    }
                "# },
            )
            .is_err(),
        "impls involving private types should not be visible across modules"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn public_impl_can_use_private_helper_impls_from_defining_module() {
    let mut session = TestSession::new();

    compile_module(
        &mut session,
        "base",
        indoc! { r#"
            trait Hidden<Self> {
                fn hidden_value(value: Self) -> int;
            }

            pub trait Public<Self> {
                fn public_value(value: Self) -> int;
            }

            pub struct Wrapper<T>(T)

            impl<T> Hidden for Wrapper<T> {
                fn hidden_value(value: Wrapper<T>) -> int {
                    7
                }
            }

            impl<T> Public for Wrapper<T> {
                fn public_value(value: Wrapper<T>) -> int {
                    hidden_value(value)
                }
            }
        "# },
    );
    compile_module(
        &mut session,
        "user",
        indoc! { r#"
            pub fn result() -> int {
                base::Public::public_value(base::Wrapper(1))
            }
        "# },
    );

    assert_val_eq!(session.run("user::result()"), int(7));
    assert!(
        session
            .try_compile_module(
                "hidden_user",
                "pub fn result() -> int { base::Hidden::hidden_value(base::Wrapper(1)) }",
            )
            .is_err(),
        "private helper trait methods should remain hidden across modules"
    );
}

/// When a dependency fails to (re)compile, the failing module *and* every
/// module that (directly or transitively) depends on it must be marked stale.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn stale_propagates_on_dep_failure() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "pub fn val() -> int { 1 }");
    let user_id = compile_module(
        &mut session,
        "user",
        "pub fn result() -> int { base::val() }",
    );

    assert_fresh(&session, base_id, "base (initial)");
    assert_fresh(&session, user_id, "user (initial)");

    break_module(&mut session, "base");

    assert_stale(&session, base_id, "base after breakage");
    assert_stale(&session, user_id, "user after base breakage (transitive)");
}

/// After a broken dependency is fixed, its direct stale dependent must be
/// automatically cascade-recompiled and become fresh again.
/// The recompiled dependent must also produce the correct value at run-time.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cascade_recompile_direct_dep() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "pub fn val() -> int { 1 }");
    let user_id = compile_module(
        &mut session,
        "user",
        "pub fn result() -> int { base::val() }",
    );

    break_module(&mut session, "base");
    assert_stale(&session, base_id, "base");
    assert_stale(&session, user_id, "user");

    // Fix base — user must be cascade-recompiled automatically.
    session
        .try_compile_module("base", "pub fn val() -> int { 1 }")
        .expect("fixing base should succeed");

    assert_fresh(&session, base_id, "base after fix");
    assert_fresh(&session, user_id, "user after cascade recompile");

    // Verify the module is really compiled (not a phantom fresh entry).
    assert!(
        module_has_compiled_version(session.session(), user_id).unwrap(),
        "user must have a compiled module after cascade recompile"
    );

    // Verify run-time correctness.
    assert_val_eq!(session.run("user::result()"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn successful_dependency_recompile_rebuilds_direct_dependent() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "pub fn val() -> int { 1 }");
    let user_id = compile_module(
        &mut session,
        "user",
        "pub fn result() -> int { base::val() }",
    );
    let initial_user_revision = module_compilation_revision(session.session(), user_id).unwrap();

    session
        .try_compile_module("base", "pub fn val() -> int { 2 }")
        .expect("updating base should succeed");

    assert_fresh(&session, base_id, "base after update");
    assert_fresh(&session, user_id, "user after cascade recompile");
    assert!(
        module_compilation_revision(session.session(), user_id)
            .unwrap()
            .as_index()
            > initial_user_revision.as_index(),
        "the dependent should be recompiled against the new base revision"
    );
    assert_val_eq!(session.run("user::result()"), int(2));
}

/// Cascade recompilation propagates transitively through a linear chain
/// A → B → C: fixing A must ultimately make C fresh too.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cascade_recompile_chain() {
    let mut session = TestSession::new();

    let a_id = compile_module(&mut session, "a", "pub fn val() -> int { 1 }");
    let b_id = compile_module(&mut session, "b", "pub fn val() -> int { a::val() + 1 }");
    let c_id = compile_module(&mut session, "c", "pub fn val() -> int { b::val() + 1 }");

    assert_fresh(&session, a_id, "a (initial)");
    assert_fresh(&session, b_id, "b (initial)");
    assert_fresh(&session, c_id, "c (initial)");

    break_module(&mut session, "a");
    assert_stale(&session, a_id, "a");
    assert_stale(&session, b_id, "b");
    assert_stale(&session, c_id, "c");

    // Fix a — b is recompiled (a is fresh), which then recompiles c.
    session
        .try_compile_module("a", "pub fn val() -> int { 1 }")
        .expect("fixing a should succeed");

    assert_fresh(&session, a_id, "a after fix");
    assert_fresh(&session, b_id, "b after cascade");
    assert_fresh(&session, c_id, "c after transitive cascade");

    // Verify run-time correctness end-to-end.
    assert_val_eq!(session.run("c::val()"), int(3));
}

/// Diamond dependency: base → {b, c} → d.
/// After base is broken and fixed all four modules must end up fresh.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cascade_recompile_diamond() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "pub fn val() -> int { 1 }");
    let b_id = compile_module(&mut session, "b", "pub fn val() -> int { base::val() }");
    let c_id = compile_module(&mut session, "c", "pub fn val() -> int { base::val() }");
    let d_id = compile_module(
        &mut session,
        "d",
        "pub fn val() -> int { b::val() + c::val() }",
    );

    assert_fresh(&session, base_id, "base (initial)");
    assert_fresh(&session, b_id, "b (initial)");
    assert_fresh(&session, c_id, "c (initial)");
    assert_fresh(&session, d_id, "d (initial)");

    break_module(&mut session, "base");
    assert_stale(&session, base_id, "base");
    assert_stale(&session, b_id, "b");
    assert_stale(&session, c_id, "c");
    assert_stale(&session, d_id, "d");

    session
        .try_compile_module("base", "pub fn val() -> int { 1 }")
        .expect("fixing base should succeed");

    assert_fresh(&session, base_id, "base after fix");
    assert_fresh(&session, b_id, "b after cascade");
    assert_fresh(&session, c_id, "c after cascade");
    assert_fresh(&session, d_id, "d after diamond cascade");

    assert_val_eq!(session.run("d::val()"), int(2));
}

/// A module compiled for the *first time* while one of its dependencies is
/// already stale must have its source info recorded so that it can be
/// cascade-recompiled automatically once the dependency is fixed.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cascade_recompile_first_compile_with_stale_dep() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "pub fn val() -> int { 42 }");

    // Break base (old module is preserved inside the entry, so user can still
    // be compiled against it — but will be marked stale due to stale dep).
    break_module(&mut session, "base");
    assert_stale(&session, base_id, "base");

    // Compile user for the first time while base is stale.
    let user_id = compile_module(
        &mut session,
        "user",
        "pub fn result() -> int { base::val() }",
    );
    assert_stale(&session, user_id, "user (first compile with stale dep)");

    // Fix base — user should be cascade-recompiled.
    session
        .try_compile_module("base", "pub fn val() -> int { 42 }")
        .expect("fixing base should succeed");

    assert_fresh(&session, base_id, "base after fix");
    assert_fresh(&session, user_id, "user after cascade recompile");

    assert_val_eq!(session.run("user::result()"), int(42));
}

/// When a module is *re*compiled and its new version introduces a dependency
/// on a *stale* module, the module's own existing dependents must be marked
/// stale as well — not just the module itself.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn stale_propagates_when_new_dep_introduced() {
    let mut session = TestSession::new();

    let base_id = compile_module(&mut session, "base", "pub fn val() -> int { 1 }");
    // mid initially has NO dependency on base.
    let mid_id = compile_module(&mut session, "mid", "pub fn val() -> int { 2 }");
    // top depends on mid.
    let top_id = compile_module(&mut session, "top", "pub fn val() -> int { mid::val() }");

    assert_fresh(&session, base_id, "base (initial)");
    assert_fresh(&session, mid_id, "mid (initial)");
    assert_fresh(&session, top_id, "top (initial)");

    // Break base; only base becomes stale — mid/top don't depend on it yet.
    break_module(&mut session, "base");
    assert_stale(&session, base_id, "base");
    assert_fresh(&session, mid_id, "mid (no base dep yet)");
    assert_fresh(&session, top_id, "top (no base dep yet)");

    // Re-compile mid so it NOW depends on the stale base.
    compile_module(&mut session, "mid", "pub fn val() -> int { base::val() }");

    // mid is stale because base is stale; top must also be stale because it
    // depends on mid which just became stale.
    assert_stale(&session, mid_id, "mid after gaining stale dep");
    assert_stale(&session, top_id, "top after mid gained stale dep");

    // Fix base — mid and top should both be cascade-recompiled.
    session
        .try_compile_module("base", "pub fn val() -> int { 1 }")
        .expect("fixing base should succeed");

    assert_fresh(&session, base_id, "base after fix");
    assert_fresh(&session, mid_id, "mid after cascade");
    assert_fresh(&session, top_id, "top after cascade");

    assert_val_eq!(session.run("top::val()"), int(1));
}

/// Attempting to introduce a circular dependency during *re*compilation must be
/// rejected with a [`CircularImportDependency`] error and must **not** cause
/// infinite recursion in the cascade recompilation pipeline.
///
/// The cycle detection guard (`find_module_deps_cycle` in `lib.rs`) acts as the
/// firewall: it fires before any cascade recompile is scheduled, so the pipeline
/// can never enter a cycle. This test ensures that guard is functional.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn no_infinite_recursion_on_circular_dep() {
    let mut session = TestSession::new();

    // Establish a linear chain: b depends on a.
    let a_id = compile_module(&mut session, "a", "pub fn val() -> int { 1 }");
    let b_id = compile_module(&mut session, "b", "pub fn val() -> int { a::val() + 1 }");

    assert_fresh(&session, a_id, "a (initial)");
    assert_fresh(&session, b_id, "b (initial)");

    // Attempting to recompile `a` so it now depends on `b` would create the
    // cycle a → b → a.  The compiler must reject this with a
    // CircularImportDependency error rather than entering infinite recursion.
    let err = session
        .try_compile_module("a", "pub fn val() -> int { b::val() }")
        .unwrap_err();

    // The error must be the cycle-detection variant.
    err.as_circular_import_dependency()
        .expect("expected a CircularImportDependency error for a → b → a cycle");

    // After the rejected recompile, both modules must be stale:
    //   • a — compilation failed, so update_with_compilation_error marks it stale.
    //   • b — mark_stale_transitively propagates staleness from a to b.
    assert_stale(&session, a_id, "a after rejected circular recompile");
    assert_stale(&session, b_id, "b after a became stale");

    // The session must still be in a consistent state: both entries must still
    // exist and be query-able (no panic, no missing entries).
    assert!(
        module_entry_exists(session.session(), a_id),
        "a's entry must still exist after rejected circular recompile"
    );
    assert!(
        module_entry_exists(session.session(), b_id),
        "b's entry must still exist after rejected circular recompile"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn qualified_enum_patterns_resolve_direct_foreign_module_path() {
    let mut session = TestSession::new();
    compile_module(&mut session, "data", tree_module_src());
    compile_module(
        &mut session,
        "direct",
        indoc! { r#"
            pub fn sum(tree) {
                match tree {
                    data::Tree::Leaf(v) => v,
                    data::Tree::Node(l, r) => sum(l) + sum(r),
                }
            }
        "# },
    );

    assert_val_eq!(session.run(&tree_sum_call_src("direct")), int(9));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn qualified_enum_patterns_resolve_imported_foreign_type() {
    let mut session = TestSession::new();
    compile_module(&mut session, "data", tree_module_src());
    compile_module(
        &mut session,
        "through_use",
        indoc! { r#"
            use data::Tree;

            pub fn sum(tree) {
                match tree {
                    Tree::Leaf(v) => v,
                    Tree::Node(l, r) => sum(l) + sum(r),
                }
            }
        "# },
    );

    assert_val_eq!(session.run(&tree_sum_call_src("through_use")), int(9));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn module_source_versions_and_compilation_revisions_are_tracked() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            "fn val() -> int { 1 }",
            "tracked",
            Path::single_str("tracked"),
        )
        .expect("initial compile should succeed")
        .module_id;

    assert_eq!(
        module_source_version(&session, module_id)
            .unwrap()
            .as_index(),
        0
    );
    assert_eq!(
        module_compilation_revision(&session, module_id)
            .unwrap()
            .as_index(),
        0
    );

    session
        .update_module_source(module_id, "fn val() -> int { 2 }")
        .expect("source update should be accepted");
    let changed = session.modules().info(module_id).unwrap();
    assert_eq!(changed.source_version().unwrap().as_index(), 1);
    assert_eq!(changed.compilation_revision().as_index(), 1);
    assert!(changed.diagnostics().is_empty());
    assert_eq!(
        session.get_module_source(module_id).unwrap().source,
        "fn val() -> int { 2 }"
    );

    session
        .update_module_source(module_id, "fn val() -> int { 2 }")
        .expect("same-source update should still compile");
    let unchanged = session.modules().info(module_id).unwrap();
    assert_eq!(unchanged.source_version().unwrap().as_index(), 1);
    assert_eq!(unchanged.compilation_revision().as_index(), 2);
    assert!(unchanged.diagnostics().is_empty());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn successful_compilation_records_and_clears_warnings() {
    let mut session = CompilerSession::new();
    let source = "fn value() -> int { return 1; 999 }";
    let module_id = session
        .compile(source, "warnings", Path::single_str("warnings"))
        .expect("unreachable code is a warning, not an error")
        .module_id;

    let diagnostics = session.modules().info(module_id).unwrap().diagnostics();
    assert_eq!(diagnostics.len(), 2);
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity == DiagnosticSeverity::Warning)
    );
    let messages_and_spans = diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.message.as_str(),
                source[diagnostic.location.as_range()].trim(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        messages_and_spans,
        [("needless return", "return 1"), ("unreachable code", "999"),]
    );
    let module = session.expect_fresh_module(module_id);
    let rendered = module.format_with(&session.modules()).to_string();
    assert!(
        !rendered.contains("999"),
        "unreachable literal should not survive in final HIR:\n{rendered}"
    );

    session
        .update_module_source(module_id, "fn value() -> int { 1 }")
        .expect("clean replacement should compile");
    assert!(
        session
            .modules()
            .info(module_id)
            .unwrap()
            .diagnostics()
            .is_empty()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn final_return_reports_needless_return_instead_of_the_closing_brace() {
    let mut session = CompilerSession::new();
    let source = indoc! { r#"
        fn value() -> int {
            return 1;
        }
    "# };
    let module_id = session
        .compile(
            source,
            "needless_return",
            Path::single_str("needless_return"),
        )
        .expect("tail return should compile")
        .module_id;

    let diagnostics = session.modules().info(module_id).unwrap().diagnostics();
    assert_eq!(diagnostics.len(), 1);
    let warning = &diagnostics[0];
    assert_eq!(warning.severity, DiagnosticSeverity::Warning);
    assert_eq!(warning.message, "needless return");
    assert_eq!(&source[warning.location.as_range()], "return 1");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn final_return_before_unreachable_code_is_still_needless() {
    let mut session = CompilerSession::new();
    let source = indoc! { r#"
        fn value(x) {
            if x == 0 {
                return 2;
            };
            return 1;
            let a = 4;
        }
    "# };
    let module_id = session
        .compile(
            source,
            "needless_return_before_dead_code",
            Path::single_str("needless_return_before_dead_code"),
        )
        .expect("a tail return followed by dead code should compile")
        .module_id;

    let diagnostics = session.modules().info(module_id).unwrap().diagnostics();
    assert_eq!(diagnostics.len(), 2);
    let messages_and_spans = diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.message.as_str(),
                source[diagnostic.location.as_range()].trim(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        messages_and_spans,
        [
            ("needless return", "return 1"),
            ("unreachable code", "let a = 4;"),
        ]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn separate_unreachable_regions_in_one_function_are_all_reported() {
    let mut session = CompilerSession::new();
    let source = indoc! { r#"
        fn diverge(x) {
            if x == 0 {
                loop {};
                let a = 4;
            } else {
                loop {};
                let b = 5;
            }
        }
    "# };
    let module_id = session
        .compile(
            source,
            "multiple_unreachable_regions",
            Path::single_str("multiple_unreachable_regions"),
        )
        .expect("multiple unreachable regions should remain non-fatal")
        .module_id;

    let diagnostics = session.modules().info(module_id).unwrap().diagnostics();
    assert_eq!(diagnostics.len(), 2);
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.message == "unreachable code")
    );
    let warned = diagnostics
        .iter()
        .map(|diagnostic| source[diagnostic.location.as_range()].trim())
        .collect::<Vec<_>>();
    assert_eq!(warned, ["let a = 4;", "let b = 5;"]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unreachable_warning_covers_the_entire_dead_suffix() {
    let mut session = CompilerSession::new();
    let source = indoc! { r#"
        fn f(x) {
            loop {};
            let a = 4;
            return 1;
            let b = 3;
        }
    "# };
    let module_id = session
        .compile(
            source,
            "entire_unreachable_suffix",
            Path::single_str("entire_unreachable_suffix"),
        )
        .expect("an unreachable suffix should remain non-fatal")
        .module_id;

    let diagnostics = session.modules().info(module_id).unwrap().diagnostics();
    assert_eq!(diagnostics.len(), 1);
    let warning = &diagnostics[0];
    assert_eq!(warning.message, "unreachable code");
    let warned = source[warning.location.as_range()].trim();
    assert_eq!(
        warned.lines().map(str::trim).collect::<Vec<_>>(),
        ["let a = 4;", "return 1;", "let b = 3;"]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn early_return_is_not_reported_as_needless() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            "fn value(flag: bool) -> int { if flag { return 1; }; 2 }",
            "early_return",
            Path::single_str("early_return"),
        )
        .expect("early return should compile")
        .module_id;

    assert!(
        session
            .modules()
            .info(module_id)
            .unwrap()
            .diagnostics()
            .is_empty()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn tail_returns_in_branches_and_lambdas_are_reported_as_needless() {
    let mut session = CompilerSession::new();
    let source = indoc! { r#"
        fn choose(flag: bool) -> int {
            if flag { return 1; } else { 2 }
        }

        fn callback() -> int {
            let f = || { return 3; };
            f()
        }
    "# };
    let module_id = session
        .compile(
            source,
            "nested_needless_returns",
            Path::single_str("nested_needless_returns"),
        )
        .expect("tail returns in branches and lambdas should compile")
        .module_id;

    let diagnostics = session.modules().info(module_id).unwrap().diagnostics();
    assert_eq!(diagnostics.len(), 2);
    assert!(
        diagnostics
            .iter()
            .all(|warning| warning.message == "needless return")
    );
    let warned = diagnostics
        .iter()
        .map(|warning| source[warning.location.as_range()].trim())
        .collect::<Vec<_>>();
    assert_eq!(warned, ["return 1", "return 3"]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unreachable_aggregate_suffix_reports_its_full_extent() {
    let mut session = CompilerSession::new();
    let source = "fn value() -> int { let x = ({ return 1 }, 999, 1000); x }";
    let module_id = session
        .compile(source, "aggregate", Path::single_str("aggregate"))
        .expect("dead tuple members should not constrain inference")
        .module_id;

    let diagnostics = session.modules().info(module_id).unwrap().diagnostics();
    assert_eq!(diagnostics.len(), 2);
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity == DiagnosticSeverity::Warning)
    );
    let warned = diagnostics
        .iter()
        .map(|diagnostic| source[diagnostic.location.as_range()].trim())
        .collect::<Vec<_>>();
    assert_eq!(warned, ["999, 1000", "x"]);
    let rendered = session
        .expect_fresh_module(module_id)
        .format_with(&session.modules())
        .to_string();
    assert!(!rendered.contains("999"));
    assert!(!rendered.contains("1000"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn failed_compilation_reports_warnings_beside_errors() {
    let mut session = CompilerSession::new();
    let source = indoc! { r#"
        fn broken(flag: bool) -> bool {
            if flag { return true; 999 };
            1
        }
    "# };
    assert!(
        session
            .compile(source, "diagnostics", Path::single_str("diagnostics"))
            .is_err()
    );
    let module_id = session
        .modules()
        .id_by_path(&Path::single_str("diagnostics"))
        .expect("failed source module should remain registered");
    let diagnostics = session.modules().info(module_id).unwrap().diagnostics();
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Warning)
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mir_artifacts_follow_the_published_module_revision() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile_for(
            ExecutionTarget::Mir,
            "fn value() -> int { 1 }",
            "artifacts",
            Path::single_str("artifacts"),
        )
        .expect("initial MIR compile should succeed")
        .module_id;

    assert_eq!(module_has_mir_artifacts(&session, module_id), Some(true));
    assert_eq!(module_mir_function_slots(&session, module_id), Some(1));
    let initial_revision = module_compilation_revision(&session, module_id).unwrap();

    session
        .prepare_execution_target(ExecutionTarget::Mir, module_id)
        .expect("MIR preparation failed");
    assert_eq!(
        module_compilation_revision(&session, module_id),
        Some(initial_revision),
        "reusing artifacts must not change the module revision"
    );

    session
        .update_module_source(
            module_id,
            "fn value() -> int { 2 } fn other() -> int { value() }",
        )
        .expect("MIR-enabled recompilation should succeed");
    assert_eq!(module_has_mir_artifacts(&session, module_id), Some(true));
    assert_eq!(module_mir_function_slots(&session, module_id), Some(2));

    session
        .update_module_source(module_id, "this is not valid Ferlium")
        .expect("failed source compilation is recorded in the module entry");
    assert_eq!(
        module_has_mir_artifacts(&session, module_id),
        Some(false),
        "stale entries must not expose old artifacts as current"
    );

    session
        .update_module_source(module_id, "fn value() -> int { 3 }")
        .expect("a valid update should recover the module");
    assert_eq!(module_has_mir_artifacts(&session, module_id), Some(true));
    assert_eq!(module_mir_function_slots(&session, module_id), Some(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn mir_compilation_prepares_script_dependencies() {
    let mut session = CompilerSession::new();
    let base_id = session
        .compile(
            "pub fn value() -> int { 41 }",
            "base",
            Path::single_str("base"),
        )
        .expect("base should compile as HIR")
        .module_id;
    assert_eq!(module_has_mir_artifacts(&session, base_id), Some(false));

    let user_id = session
        .compile_for(
            ExecutionTarget::Mir,
            "fn main() -> int { base::value() + 1 }",
            "user",
            Path::single_str("user"),
        )
        .expect("MIR user should compile")
        .module_id;
    assert_eq!(module_has_mir_artifacts(&session, base_id), Some(true));
    assert_eq!(module_has_mir_artifacts(&session, user_id), Some(true));

    let main = session
        .expect_fresh_module(user_id)
        .get_local_function_id(ustr("main"))
        .expect("user should define main");
    assert_val_eq!(
        session
            .run_entry(ExecutionTarget::Mir, user_id, main, vec![])
            .unwrap(),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn failed_module_source_update_records_diagnostics_and_keeps_last_good_module() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            "fn val() -> int { 1 }",
            "broken",
            Path::single_str("broken"),
        )
        .expect("initial compile should succeed")
        .module_id;

    session
        .update_module_source(module_id, "this is not valid ferlium !!!")
        .expect("source update should be accepted even when compilation fails");
    let update = session.modules().info(module_id).unwrap();

    assert_eq!(update.source_version().unwrap().as_index(), 1);
    assert_eq!(update.compilation_revision().as_index(), 1);
    assert!(!update.diagnostics().is_empty());
    assert_eq!(
        module_diagnostics_len(&session, module_id).unwrap(),
        update.diagnostics().len()
    );
    assert!(module_is_stale(&session, module_id).unwrap());
    assert!(
        session
            .expect_compiled_module(module_id)
            .get_function(ferlium::ustr("val"))
            .is_some(),
        "last good module should remain available after failed update"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn dependency_query_apis_report_direct_reverse_and_affected_modules() {
    let mut session = CompilerSession::new();
    let base_id = session
        .compile(
            "pub fn val() -> int { 1 }",
            "base",
            Path::single_str("base"),
        )
        .expect("base should compile")
        .module_id;
    let mid_id = session
        .compile(
            "pub fn val() -> int { base::val() }",
            "mid",
            Path::single_str("mid"),
        )
        .expect("mid should compile")
        .module_id;
    let top_id = session
        .compile(
            "pub fn val() -> int { mid::val() }",
            "top",
            Path::single_str("top"),
        )
        .expect("top should compile")
        .module_id;

    assert!(
        module_latest_deps(&session, mid_id)
            .unwrap()
            .contains(&base_id)
    );
    assert_eq!(session.get_module_reverse_deps(base_id), vec![mid_id]);

    let affected = session.get_modules_affected_by(base_id);
    assert!(affected.contains(&mid_id));
    assert!(affected.contains(&top_id));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn imported_trait_impl_records_value_dependency() {
    let mut session = CompilerSession::new();
    let base_id = session
        .compile(
            indoc! { r#"
                pub trait ToInt<Self> {
                    fn to_int(value: Self) -> int;
                }

                impl ToInt for int {
                    fn to_int(value: int) -> int {
                        value
                    }
                }
            "# },
            "base",
            Path::single_str("base"),
        )
        .expect("base should compile")
        .module_id;
    let user_id = session
        .compile(
            indoc! { r#"
                use base::ToInt;

                pub fn result() -> int {
                    ToInt::to_int(42)
                }
            "# },
            "user",
            Path::single_str("user"),
        )
        .expect("user should compile")
        .module_id;

    assert!(
        module_latest_deps(&session, user_id)
            .unwrap()
            .contains(&base_id)
    );
    assert_eq!(session.get_module_reverse_deps(base_id), vec![user_id]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn value_to_string_renders_int_correctly() {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile("", "<test>", Path::single_str("test"))
        .unwrap()
        .module_id;

    let rendered = session
        .value_to_string(
            module_id,
            Value::native(42isize),
            Type::primitive::<isize>(),
        )
        .unwrap();

    assert_eq!(rendered, "42");
}

const CONV_MODULE: &str = "pub trait Conv<A, B> { fn conv(a: A, b: B) -> int; }\npub trait Use<Self> { fn use_(x: Self) -> int; }";

/// Whether compiling `name` with `code` fails with an error that `matches` accepts.
fn module_fails_with(
    session: &mut TestSession,
    name: &str,
    code: &str,
    matches: impl FnOnce(&CompilationErrorImpl<External>) -> bool,
) -> bool {
    let error = session
        .try_compile_module(name, code)
        .err()
        .unwrap_or_else(|| panic!("compiling {name:?} should fail"));
    matches(&error.into_inner())
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_impl_of_a_foreign_trait_is_owned_by_its_first_local_input() {
    let a = "use c::Conv;\npub struct X;\nimpl<T> Conv for <A = X, B = T> { fn conv(a, b) { 1 } }";
    let crossing =
        "use c::Conv;\npub struct Y;\nimpl<T> Conv for <A = T, B = Y> { fn conv(a, b) { 2 } }";
    // A bare type parameter before the local type could cross another module's impl, as `a`'s,
    // whatever the order of compilation.
    for with_a_first in [true, false] {
        let mut session = TestSession::new();
        compile_module(&mut session, "c", CONV_MODULE);
        if with_a_first {
            compile_module(&mut session, "a", a);
        }
        assert!(module_fails_with(
            &mut session,
            "b",
            crossing,
            |e| matches!(e, CompilationErrorImpl::TraitImplOrphanRuleViolation { .. })
        ));
    }
    // Wrapping the generic input in a local type, or covering it, makes the impl own its
    // applications.
    let mut session = TestSession::new();
    compile_module(&mut session, "c", CONV_MODULE);
    compile_module(&mut session, "a", a);
    compile_module(
        &mut session,
        "b",
        "use c::Conv;\npub struct Y;\npub struct Src<T>(T)\nimpl<T> Conv for <A = Src<T>, B = Y> { fn conv(a, b) { 2 } }\nimpl<T> Conv for <A = [T], B = Y> { fn conv(a, b) { 3 } }",
    );
    assert_val_eq!(
        session.run("c::Conv::conv(a::X, 0) * 100 + c::Conv::conv(b::Src(0), b::Y) * 10 + c::Conv::conv([0], b::Y)"),
        int(123)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_impl_is_private_only_through_its_owning_input() {
    // Private: owned by a private type, or of a private trait.
    let mut session = TestSession::new();
    compile_module(&mut session, "c", CONV_MODULE);
    compile_module(
        &mut session,
        "a",
        "use c::Conv;\nstruct X;\nstruct H;\npub struct W<T>(T)\ntrait Local<Self> { fn local(x: Self) -> int; }\nimpl<T> Conv for <A = X, B = T> { fn conv(a, b) { 1 } }\nimpl<T> Local for W<T> { fn local(x) { 2 } }\nimpl Local for H { fn local(x) { 3 } }",
    );
    // Public, as owned by a public constructor, but mentioning a private type.
    for code in [
        "use c::Conv;\nstruct Hidden;\npub struct W<T>(T)\nimpl<T> Conv for <A = W<Hidden>, B = T> { fn conv(a, b) { 1 } }",
        "pub trait Get<Self |-> Out> { fn get(x: Self) -> Out; }\nstruct Hidden;\nimpl<T> Get for <Self = T |-> Out = Hidden> { fn get(x: T) -> Hidden { Hidden } }",
        "pub trait Pair<A, B> { fn pair(a: A, b: B) -> int; }\nstruct Hidden;\nimpl<T> Pair for <A = T, B = Hidden> { fn pair(a, b) { 1 } }",
    ] {
        let mut session = TestSession::new();
        compile_module(&mut session, "c", CONV_MODULE);
        assert!(
            module_fails_with(&mut session, "a", code, |e| matches!(
                e,
                CompilationErrorImpl::PublicTraitImplMentionsPrivateType { .. }
            )),
            "{code}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_private_impl_conflicting_with_a_dependency_is_rejected_in_its_module() {
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "c",
        "pub trait Get<Self> { fn get(x: Self) -> int; }\nimpl<T> Get for T { fn get(x) { 1 } }",
    );
    assert!(module_fails_with(
        &mut session,
        "a",
        "use c::Get;\nstruct X;\nimpl Get for X { fn get(x) { 2 } }",
        |e| matches!(e, CompilationErrorImpl::OverlappingTraitImpls { .. })
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn evidence_built_in_a_private_scope_is_not_reused_outside() {
    // `a`'s `Use` impl solves `Conv<X, T>` in `a`'s private scope; outside, `a`'s private impl
    // is invisible, whether the private scope solved that application before or not.
    let a = "use c::{Conv, Use};\nstruct X;\npub struct P<T>(T)\npub fn make_x() { X }\nimpl<T> Conv for <A = X, B = T> { fn conv(a, b) { 1 } }\nimpl<T> Use for P<T> where Conv<X, T> { fn use_(x) { conv(X, x.0) } }";
    for program in [
        "c::Conv::conv(a::make_x(), 0)",
        "let i = c::Use::use_(a::P(0));\nlet o = c::Conv::conv(a::make_x(), 0);\no * 10 + i",
    ] {
        let mut session = TestSession::new();
        compile_module(&mut session, "c", CONV_MODULE);
        compile_module(&mut session, "a", a);
        assert!(session.try_compile(program).is_err(), "{program}");
    }
    let mut session = TestSession::new();
    compile_module(&mut session, "c", CONV_MODULE);
    compile_module(&mut session, "a", a);
    assert_val_eq!(session.run("c::Use::use_(a::P(0))"), int(1));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_consumer_requirement_does_not_inherit_a_providers_private_scope() {
    // `a`'s public `Use` impl needs `a`'s private `Conv` impl, solved in `a`'s scope; the
    // consumer's own request for the same application is solved in the consumer's scope, where
    // that impl is invisible, whatever the order of the calls.
    let c = "pub trait Conv<A, B |-> Out> { fn conv(a: A, b: B) -> Out; }\npub trait Use<Self |-> Out> { fn use_(x: Self) -> Out; }";
    let a = "use c::{Conv, Use};\nstruct X;\npub struct P<T>(T)\npub fn make_x() { X }\nimpl<T> Conv for <A = X, B = T |-> Out = int> { fn conv(a: X, b: T) -> int { 1 } }\nimpl<T, O> Use for <Self = P<T> |-> Out = O> where Conv<A = X, B = T |-> Out = O> { fn use_(x: P<T>) -> O { conv(X, x.0) } }";
    let session = || {
        let mut session = TestSession::new();
        compile_module(&mut session, "c", c);
        compile_module(&mut session, "a", a);
        session
    };
    assert_val_eq!(session().run("c::Use::use_(a::P(0))"), int(1));
    for program in [
        "c::Conv::conv(a::make_x(), 0)",
        "let i = c::Use::use_(a::P(0));\nlet o = c::Conv::conv(a::make_x(), 0);\ni * 10 + o",
        "let o = c::Conv::conv(a::make_x(), 0);\nlet i = c::Use::use_(a::P(0));\ni * 10 + o",
        "fn f() -> int { let i = c::Use::use_(a::P(0)); let o = c::Conv::conv(a::make_x(), 0); i * 10 + o }\nf()",
    ] {
        assert!(session().try_compile(program).is_err(), "{program}");
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_derivation_made_elsewhere_does_not_override_a_private_impl_in_its_scope() {
    // Outside `a`, `X<int>` is inspected by derivation; in `a`'s scope, by `a`'s private impl.
    let a = "struct X<T>(T)\npub struct P<T>(T)\npub fn make_x() { X(0) }\nimpl<T> Inspect for X<T> { fn inspect(x: X<T>) -> string { \"custom\" } }\npub trait Use<Self> { fn use_(x: Self) -> string ! fallible; }\nimpl<T> Use for P<T> where X<T>: Inspect { fn use_(x: P<T>) -> string { inspect(X(x.0)) } }";
    for program in [
        "let o = inspect(a::make_x());\nlet i = a::Use::use_(a::P(0));\nf\"{o}/{i}\"",
        "let i = a::Use::use_(a::P(0));\nlet o = inspect(a::make_x());\nf\"{o}/{i}\"",
    ] {
        let mut session = TestSession::new();
        compile_module(&mut session, "a", a);
        assert_val_eq!(session.run(program), string("X (0)/custom"), "{program}");
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn public_impls_build_private_evidence_from_the_consumers_evidence() {
    let declarations = [
        "impl<T> Hidden for [T] where T: Inspect { fn hidden(x: [T]) -> string { inspect(x[0]) } }",
        "impl<T> Use for P<T> where [T]: Hidden { fn use_(x: P<T>) -> string { hidden([x.0]) } }",
    ];
    for reverse in [false, true] {
        let mut declarations = declarations;
        if reverse {
            declarations.reverse();
        }
        let provider = format!(
            r#"
            struct Cb<T>(T)
            trait Run<Self |-> ! E> {{ fn run(x: Self) -> int ! E; }}
            impl<! E> Run for <Self = Cb<(() -> int ! E)> |-> ! E = E> {{
                fn run(x: Cb<(() -> int ! E)>) -> int {{ x.0() }}
            }}
            struct X<T>(T)
            impl<T> Inspect for X<T> where T: Run<! E = ()> {{
                fn inspect(x: X<T>) -> string {{ "custom" }}
            }}
            pub fn make_x() {{ X(Cb(|| idiv(4, 2))) }}
            trait Hidden<Self> {{ fn hidden(x: Self) -> string ! fallible; }}
            pub struct P<T>(T)
            pub trait Use<Self> {{ fn use_(x: Self) -> string ! fallible; }}
            {}
        "#,
            declarations.join("\n")
        );
        for program in [
            "let o = inspect(a::make_x()); let i = a::Use::use_(a::P(a::make_x())); f\"{o}/{i}\"",
            "let i = a::Use::use_(a::P(a::make_x())); let o = inspect(a::make_x()); f\"{o}/{i}\"",
        ] {
            let mut session = TestSession::new();
            compile_module(&mut session, "a", &provider);
            assert_val_eq!(
                session.run(program),
                string("X (Cb (<function>))/X (Cb (<function>))")
            );
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_requirements_fail_at_the_public_impl_definition() {
    for hidden_impl in [
        "",
        "impl<T> Hidden for [T] where [[T]]: Hidden { fn hidden(x: [T]) -> int { hidden([x]) } }",
    ] {
        let mut session = TestSession::new();
        let source = format!(
            r#"
            trait Hidden<Self> {{ fn hidden(x: Self) -> int; }}
            pub struct P<T>(T)
            pub trait Use<Self> {{ fn use_(x: Self) -> int; }}
            {hidden_impl}
            impl<T> Use for P<T> where [T]: Hidden {{ fn use_(x: P<T>) -> int {{ hidden([x.0]) }} }}
        "#
        );
        assert!(
            module_fails_with(&mut session, "a", &source, |e| matches!(
                e,
                CompilationErrorImpl::PrivateRequirementInPublicContract { .. }
            )),
            "{source}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_possible_specialization_prevents_private_derivation() {
    let mut session = TestSession::new();
    assert!(
        session
            .try_compile_module(
                "a",
                r#"
        struct X<T>(T)
        impl Inspect for X<int> { fn inspect(x: X<int>) -> string { "custom" } }
        pub struct P<T>(T)
        pub trait Use<Self> { fn use_(x: Self) -> string ! fallible; }
        impl<T> Use for P<T> where X<T>: Inspect {
            fn use_(x: P<T>) -> string { inspect(X(x.0)) }
        }
    "#
            )
            .is_err()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn exported_functions_reduce_private_requirements() {
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "a",
        r#"
        trait Hidden<Self> { fn hidden(x: Self) -> string ! fallible; }
        impl<T> Hidden for [T] where T: Inspect {
            fn hidden(x: [T]) -> string { inspect(x[0]) }
        }
        pub fn f<T>(x: T) -> string { hidden([x]) }
    "#,
    );
    assert_val_eq!(session.run("a::f(7)"), string("7"));
    assert!(
        session
            .try_compile_module(
                "b",
                r#"
        trait Hidden<Self> { fn hidden(x: Self) -> int; }
        pub fn f<T>(x: T) -> int { hidden(x) }
    "#
            )
            .is_err()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn exported_recursive_groups_with_an_effect_generic_reduce_private_requirements() {
    // The functions are inferred one by one against the contracts of the group, which are in
    // the public form for all of them: the calls of the group pass the evidence of that form.
    for g in [
        "fn g<T, ! E>(x: T, n: int, k: () -> int ! E) -> string { f(x, n, k) }",
        "fn g(x, n, k) { f(x, n, k) }",
    ] {
        let functions = [
            "pub fn f<T, ! E>(x: T, n: int, k: () -> int ! E) -> string { if n == 0 { k(); hidden([x]) } else { g(x, n - 1, k) } }",
            g,
        ];
        for reverse in [false, true] {
            let mut functions = functions;
            if reverse {
                functions.reverse();
            }
            let mut session = TestSession::new();
            compile_module(
                &mut session,
                "a",
                &format!(
                    r#"
                trait Hidden<Self> {{ fn hidden(x: Self) -> string ! fallible; }}
                impl<T> Hidden for [T] where T: Inspect {{
                    fn hidden(x: [T]) -> string {{ inspect(x[0]) }}
                }}
                {}
            "#,
                    functions.join("\n")
                ),
            );
            assert_val_eq!(
                session.run("a::f(7, 2, || 1)"),
                string("7"),
                "{g}, reversed: {reverse}"
            );
        }
    }
    // A requirement that reduces to nothing.
    assert_val_eq!(
        TestSession::new().run(indoc! { "
            trait Hidden<Self> { fn hidden(x: Self) -> int; }
            impl<T> Hidden for [T] {
                fn hidden(x: [T]) -> int { len(x) }
            }
            pub fn f<T, ! E>(x: T, n: int, g: () -> int ! E) -> int {
                if n == 0 {
                    g();
                    hidden([x])
                } else {
                    f(x, n - 1, g)
                }
            }
            f(true, 1, || 2) + 1
        " }),
        int(2)
    );
    // The public form names an output that the private requirement did not.
    for h_first in [false, true] {
        let f = indoc! { "
            pub fn f<T, ! E>(x: T, n: int, g: () -> int ! E) -> string {
                if n == 0 {
                    g();
                    hidden([x])
                } else {
                    h(x, n - 1, g)
                }
            }
        " };
        let h = "fn h<T, ! E>(x: T, n: int, g: () -> int ! E) -> string { f(x, n, g) }\n";
        let functions = if h_first {
            format!("{h}{f}")
        } else {
            format!("{f}{h}")
        };
        let src = format!(
            indoc! { "
                pub trait Read<Self |-> Out> {{
                    fn read(x: Self) -> Out;
                }}
                trait Hidden<Self> {{
                    fn hidden(x: Self) -> string ! fallible;
                }}
                impl<T, O> Hidden for [T] where T: Read<Out = O>, O: Inspect {{
                    fn hidden(x: [T]) -> string {{ inspect(read(x[0])) }}
                }}
                impl Read for <Self = int |-> Out = int> {{
                    fn read(x: int) -> int {{ x }}
                }}
                {}
                f(7, 2, || 1)
            " },
            functions
        );
        assert_val_eq!(TestSession::new().run(&src), string("7"), "{functions}");
    }
    // A private impl for every type determines the output, and so the type of the result.
    assert_val_eq!(
        TestSession::new().run(indoc! { "
            trait Hidden<Self |-> Out> {
                fn hidden(x: Self) -> Out;
            }
            impl<T> Hidden for <Self = T |-> Out = int> {
                fn hidden(x: T) -> int { 7 }
            }
            pub fn f<T, ! E>(x: T, n: int, g: () -> int ! E) {
                if n == 0 {
                    g();
                    hidden(x)
                } else {
                    f(x, n - 1, g)
                }
            }
            f(true, 1, || 2) + 1
        " }),
        int(8)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn exported_recursive_groups_reduce_private_requirements() {
    let functions = [
        "pub fn f<T>(x: T, n: int) -> string { if n == 0 { hidden([x]) } else { g(x, n - 1) } }",
        "fn g<T>(x: T, n: int) -> string { f(x, n) }",
    ];
    for reverse in [false, true] {
        let mut functions = functions;
        if reverse {
            functions.reverse();
        }
        let mut session = TestSession::new();
        compile_module(
            &mut session,
            "a",
            &format!(
                r#"
            trait Hidden<Self> {{ fn hidden(x: Self) -> string ! fallible; }}
            impl<T> Hidden for [T] where T: Inspect {{
                fn hidden(x: [T]) -> string {{ inspect(x[0]) }}
            }}
            {}
        "#,
                functions.join("\n")
            ),
        );
        assert_val_eq!(session.run("a::f(7, 2)"), string("7"));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn exported_subscripts_reduce_private_requirements() {
    // A subscript that other modules can use publishes its requirements as an exported function
    // does, once for its bodies, which are one definition: here `[T]: Hidden` becomes
    // `T: Inspect`, also for the value of the subscript that a body takes.
    let hidden = indoc! { r#"
        trait Hidden<Self |-> ! E> { fn hidden(x: Self) -> int ! E; }
        impl<T> Hidden for <Self = [T] |-> ! E = fallible> where T: Inspect {
            fn hidden(x) { string_len(inspect(x[0])) }
        }
    "# };
    let ref_body = indoc! { r#"
        ref {
            let local = if depth == 0 {
                slot + hidden([key])
            } else {
                let accessor = cell;
                slot->[accessor](key, depth - 1)
            };
            yield local
        }
    "# };
    let mut_body = indoc! { r#"
        mut {
            let mut local = if depth == 0 {
                slot + hidden([key])
            } else {
                slot->[cell](key, depth - 1)
            };
            yield local;
            slot = local
        }
    "# };
    for bodies in [
        format!("{ref_body}{mut_body}"),
        format!("{mut_body}{ref_body}"),
    ] {
        for signature in [
            "<T>(slot: &mut int, key: T, depth: int)",
            "(slot: &mut int, key, depth: int)",
        ] {
            let mut session = TestSession::new();
            session.allow_experimental();
            compile_module(
                &mut session,
                "a",
                &format!(
                    indoc! { r#"
                        {}
                        pub subscript cell{} -> int {{
                        {}
                        }}

                        pub fn read() -> int {{
                            let mut slot = 1;
                            slot->[cell](12345, 2)
                        }}

                        pub fn write() -> int {{
                            let mut slot = 1;
                            slot->[cell]("ab", 2) += 10;
                            slot
                        }}
                    "# },
                    hidden, signature, bodies
                ),
            );
            compile_module(
                &mut session,
                "b",
                indoc! { r#"
                    use a::cell;

                    pub fn read() -> int {
                        let accessor = cell;
                        let mut slot = 1;
                        slot->[accessor](12345, 2)
                    }

                    pub fn write() -> int {
                        let accessor = cell;
                        let mut slot = 1;
                        slot->[accessor]("ab", 2) += 10;
                        slot
                    }

                    fn read_any(key) -> int {
                        let accessor = cell;
                        let mut slot = 1;
                        slot->[accessor](key, 2)
                    }

                    pub fn read_bool() -> int {
                        read_any(true)
                    }
                "# },
            );
            for (expr, expected) in [
                ("a::read()", 6),
                ("a::write()", 15),
                ("b::read()", 6),
                ("b::write()", 15),
                ("b::read_bool()", 5),
            ] {
                assert_val_eq!(session.run(expr), int(expected), "{expr}, {signature}");
            }
        }
    }

    // Bodies that require different private things publish them together, in one order; the
    // public form of one names an output that its private requirement did not.
    for reverse in [false, true] {
        let mut bodies = [
            "ref { let local = slot + hidden([key]); yield local }",
            "mut { let mut local = slot + hidden_read([key]); yield local; slot = local }",
        ];
        if reverse {
            bodies.reverse();
        }
        let mut session = TestSession::new();
        session.allow_experimental();
        compile_module(
            &mut session,
            "a",
            &format!(
                indoc! { r#"
                    {}
                    pub trait Read<Self |-> Out> {{
                        fn read(x: Self) -> Out;
                    }}
                    impl Read for <Self = int |-> Out = int> {{
                        fn read(x: int) -> int {{ x }}
                    }}
                    trait HiddenRead<Self> {{
                        fn hidden_read(x: Self) -> int ! fallible;
                    }}
                    impl<T, O> HiddenRead for [T] where T: Read<Out = O>, O: Inspect {{
                        fn hidden_read(x: [T]) -> int {{ string_len(inspect(read(x[0]))) }}
                    }}
                    pub subscript cell(slot: &mut int, key) -> int {{
                        {}
                        {}
                    }}
                "# },
                hidden, bodies[0], bodies[1]
            ),
        );
        compile_module(
            &mut session,
            "b",
            indoc! { r#"
                use a::cell;

                fn write_any(key) -> int {
                    let accessor = cell;
                    let mut slot = 1;
                    slot->[accessor](key) += 10;
                    slot->[accessor](key)
                }

                pub fn write() -> int {
                    write_any(12345)
                }
            "# },
        );
        assert_val_eq!(session.run("b::write()"), int(21), "reversed: {reverse}");
    }

    // The same for a subscript declared as a field, which another module reads as a field.
    let mut session = TestSession::new();
    session.allow_experimental();
    compile_module(
        &mut session,
        "a",
        &format!(
            indoc! { r#"
                {}
                #[private_repr]
                pub struct Secret<T> {{
                    raw: T,
                }}

                pub fn make<T>(raw: T) -> Secret<T> {{
                    Secret {{ raw }}
                }}

                pub subscript Secret<T>.value(self) -> int {{
                    ref {{
                        let local = hidden([self.raw]);
                        yield local
                    }}
                }}
            "# },
            hidden
        ),
    );
    compile_module(
        &mut session,
        "b",
        indoc! { r#"
            fn get(x) {
                x.value
            }

            pub fn direct() -> int {
                a::make(12345).value
            }

            pub fn generic() -> int {
                get(a::make(true))
            }
        "# },
    );
    assert_val_eq!(session.run("b::direct()"), int(5));
    assert_val_eq!(session.run("b::generic()"), int(4));
    assert!(
        module_fails_with(
            &mut session,
            "c",
            indoc! { r#"
                fn pure_only(f: () -> int ! ()) -> int {
                    f()
                }

                pub fn read() -> int {
                    pure_only(|| a::make(12345).value)
                }
            "# },
            |e| matches!(e, CompilationErrorImpl::InvalidEffectInclusion { .. })
        ),
        "the effect of the reduced requirement is that of the subscript"
    );

    // A requirement that does not reduce is refused where the subscript is defined, written or
    // not, and accepted for a subscript of the module alone.
    let hidden = "trait Hidden<Self> { fn hidden(x: Self) -> int; }\n";
    let body = "{ ref { let local = slot + hidden(key); yield local } }";
    for (subscript, private_requirement) in [
        ("pub subscript cell<T>(slot: &mut int, key: T) -> int", true),
        (
            "pub subscript cell<T>(slot: &mut int, key: T) -> int where T: Hidden",
            true,
        ),
        ("subscript cell<T>(slot: &mut int, key: T) -> int", false),
    ] {
        let source = format!("{hidden}{subscript} {body}");
        let mut session = TestSession::new();
        session.allow_experimental();
        if private_requirement {
            assert!(
                module_fails_with(&mut session, "a", &source, |e| matches!(
                    e,
                    CompilationErrorImpl::PrivateRequirementInPublicContract { .. }
                )),
                "{source}"
            );
        } else {
            compile_module(&mut session, "a", &source);
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_reduction_determines_inferred_function_outputs() {
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "a",
        r#"
        trait Hidden<Self |-> Out> { fn hidden(x: Self) -> Out; }
        impl<T> Hidden for <Self = [T] |-> Out = int> {
            fn hidden(x: [T]) -> int { len(x) }
        }
        pub fn f<T>(x: T) { hidden([x]) }
    "#,
    );
    assert_val_eq!(session.run("a::f(true) + 1"), int(2));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_reduction_quantifies_outputs_of_its_public_leaves() {
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "a",
        r#"
        pub trait Read<Self |-> Out> { fn read(x: Self) -> Out; }
        trait Hidden<Self> { fn hidden(x: Self) -> string ! fallible; }
        impl<T, O> Hidden for [T] where T: Read<Out = O>, O: Inspect {
            fn hidden(x: [T]) -> string { inspect(read(x[0])) }
        }
        pub fn f<T>(x: T) -> string { hidden([x]) }
        pub struct P<T>(T)
        pub trait Use<Self> { fn use_(x: Self) -> string ! fallible; }
        impl<T> Use for P<T> where [T]: Hidden {
            fn use_(x: P<T>) -> string { hidden([x.0]) }
        }
    "#,
    );
    compile_module(
        &mut session,
        "b",
        r#"
        use a::Read;
        pub struct X;
        impl Read for <Self = X |-> Out = int> { fn read(x: X) -> int { 7 } }
    "#,
    );
    assert_val_eq!(session.run("a::f(b::X)"), string("7"));
    assert_val_eq!(session.run("a::Use::use_(a::P(b::X))"), string("7"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_recursive_value_evidence_is_constructed_in_exported_bodies() {
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "a",
        r#"
        enum List<T> { Empty, Cons(T, List<T>) }
        pub fn f<T>(x: T) -> string where T: Value {
            let values: List<T> = List::Cons(x, List::Empty);
            to_string(values)
        }
    "#,
    );
    assert_val_eq!(
        session.run("a::f(7)"),
        string("List::Cons (7, List::Empty)")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn public_value_evidence_builds_a_private_custom_field_dictionary() {
    let mut session = TestSession::new();
    session.allow_unsafe();
    compile_module(
        &mut session,
        "a",
        r#"
        pub trait Read<Self |-> Out> { fn read(x: Self) -> Out; }
        impl Read for <Self = int |-> Out = int> { fn read(x: int) -> int { x } }
        impl Read for <Self = bool |-> Out = bool> { fn read(x: bool) -> bool { x } }
        struct Cell<T>(T)
        impl<T, O> Value for Cell<T> where T: Value, T: Read<Out = O>, O: Value {
            fn eq(x: Cell<T>, y: Cell<T>) -> bool { eq(x.0, y.0) }
            fn to_string(x: Cell<T>) -> string { to_string(read(x.0)) }
            fn hash(x: Cell<T>, state: &mut hasher) { hash(x.0, state) }
            fn clone(x: Cell<T>) -> Cell<T> { Cell(x.0) }
            fn drop(x: &mut Cell<T>) {}
        }
        #[private_repr]
        pub struct Outer<T>(Cell<T>)
        pub fn make<T>(x: T) -> Outer<T> { Outer(Cell(x)) }
    "#,
    );
    assert_val_eq!(
        session.run("to_string((a::make(7), a::make(true)))"),
        string("(Outer (7), Outer (true))")
    );
    compile_module(
        &mut session,
        "b",
        r#"
        use a::Read;
        struct Local<T>(T)
        impl<T, O> Read for <Self = Local<T> |-> Out = O> where T: Read<Out = O> {
            fn read(x: Local<T>) -> O { read(x.0) }
        }
        pub fn rendered<T>(x: T) -> string { to_string(a::make(Local(x))) }
    "#,
    );
    assert_val_eq!(session.run("b::rendered(7)"), string("Outer (7)"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_dictionary_construction_preserves_distinct_phantom_arguments() {
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "a",
        r#"
        struct Tag<T>(int)
        pub fn tags<T, U>(x: T, y: U) -> string {
            let a: Tag<T> = Tag(0);
            let b: Tag<U> = Tag(0);
            to_string((a, b))
        }
    "#,
    );
    assert_val_eq!(
        session.run("a::tags(7, true)"),
        string("(Tag (0), Tag (0))")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn reducing_outputs_rechecks_the_public_impl_head() {
    let mut session = TestSession::new();
    assert!(module_fails_with(
        &mut session,
        "a",
        r#"
        struct Hidden;
        trait Conv<Self |-> Out> { fn conv(x: Self) -> Out; }
        impl<T> Conv for <Self = [T] |-> Out = Hidden> {
            fn conv(x: [T]) -> Hidden { Hidden }
        }
        pub struct P<T>(T)
        pub trait Get<Self |-> Out> { fn get(x: Self) -> Out; }
        impl<T, O> Get for <Self = P<T> |-> Out = O> where [T]: Conv<Out = O> {
            fn get(x: P<T>) -> O { conv([x.0]) }
        }
    "#,
        |e| matches!(
            e,
            CompilationErrorImpl::PublicTraitImplMentionsPrivateType { .. }
        )
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn public_leaves_are_conditions_not_specializations_of_the_impl_head() {
    let impls = [
        "impl Read for [int] { fn read(x: [int]) -> int { 7 } }",
        "impl<T> Hidden for [T] where [T]: Read { fn hidden(x: [T]) -> int { read(x) } }",
    ];
    for reverse in [false, true] {
        let mut impls = impls;
        if reverse {
            impls.reverse();
        }
        let mut session = TestSession::new();
        compile_module(
            &mut session,
            "a",
            &format!(
                r#"
            pub trait Read<Self> {{ fn read(x: Self) -> int; }}
            trait Hidden<Self> {{ fn hidden(x: Self) -> int; }}
            {}
            pub fn f<T>(x: T) -> int {{ hidden([x]) }}
        "#,
                impls.join("\n")
            ),
        );
        assert_val_eq!(session.run("a::f(0)"), int(7));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn written_impl_bounds_publish_the_consumers_requirement_after_projection() {
    let impls = [
        "impl Read for [int] { fn read(x: [int]) -> int { 7 } }",
        "impl<T> Hidden for [T] where [T]: Read { fn hidden(x: [T]) -> int { read(x) } }",
        "impl<T> Use for P<T> where [T]: Hidden { fn use_it(x: P<T>) -> int { hidden([x.0]) } }",
    ];
    for reverse in [false, true] {
        let mut impls = impls;
        if reverse {
            impls.reverse();
        }
        let mut session = TestSession::new();
        compile_module(
            &mut session,
            "a",
            &format!(
                "pub trait Read<Self> {{ fn read(x: Self) -> int; }}
                 trait Hidden<Self> {{ fn hidden(x: Self) -> int; }}
                 pub trait Use<Self> {{ fn use_it(x: Self) -> int; }}
                 pub struct P<T>(T)
                 {}
                 pub fn f<T>(x: P<T>) -> int {{ hidden([x.0]) }}",
                impls.join("\n"),
            ),
        );
        compile_module(
            &mut session,
            "b",
            "use a::Read;
             pub fn g<T>(x: T) -> int where [T]: Read {
                 a::Use::use_it(a::P(x)) + a::f(a::P(x))
             }",
        );
        assert_val_eq!(
            session.run("a::Use::use_it(a::P(0)) + a::f(a::P(0))"),
            int(14)
        );
        assert_val_eq!(session.run("b::g(0)"), int(14));
        session.fail_compilation("a::Use::use_it(a::P(true))");
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_impls_cannot_choose_an_exported_functions_return_only_quantifier() {
    let int_impl = "impl Def for int { fn def() -> int { 0 } }";
    let bool_impl = "impl Def for bool { fn def() -> bool { false } }";
    for impls in [
        vec![int_impl],
        vec![int_impl, bool_impl],
        vec![bool_impl, int_impl],
    ] {
        for function_first in [false, true] {
            let mut session = TestSession::new();
            let function = "pub fn g() { def() }";
            let impls = impls.join("\n");
            let items = if function_first {
                format!("{function}\n{impls}")
            } else {
                format!("{impls}\n{function}")
            };
            let source = format!("trait Def<Self> {{ fn def() -> Self; }}\n{items}");
            assert!(
                module_fails_with(&mut session, "a", &source, |error| {
                    matches!(
                        error,
                        CompilationErrorImpl::PrivateRequirementInPublicContract { .. }
                    )
                }),
                "{source}"
            );
        }
    }
    let mut session = TestSession::new();
    let definition = session.compile_and_get_fn_def(
        &format!("trait Def<Self> {{ fn def() -> Self; }}\n{int_impl}\nfn h() {{ def() }}"),
        "h",
    );
    assert_eq!(definition.ty_scheme.ty_quantifiers.len(), 1);
    assert_eq!(definition.ty_scheme.constraints.len(), 1);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recorded_private_evidence_is_shared_across_calls_functions_and_lambdas() {
    let mut session = TestSession::new();
    let id = compile_module(
        &mut session,
        "shared",
        r#"
        trait Hidden<Self> { fn hidden(x: Self) -> string ! fallible; }
        impl<T> Hidden for [T] where T: Inspect {
            fn hidden(x: [T]) -> string { inspect(x[0]) }
        }
        pub fn twice<T>(x: T, y: T) -> string { concat(hidden([x]), hidden([y])) }
        pub fn once<T>(x: T) -> string { hidden([x]) }
        pub fn in_lambda<T>(x: T) -> string {
            let f = || hidden([x]);
            f()
        }
        "#,
    );
    let module = session.session().expect_fresh_module(id);
    let thunks = module
        .own_symbols()
        .filter(|name| name.as_str().starts_with("__uniform_dictionary_"))
        .collect::<Vec<_>>();
    assert_eq!(
        thunks.len(),
        1,
        "the same selected impl needs one thunk: {thunks:?}"
    );
    assert_val_eq!(session.run("shared::twice(7, 8)"), string("78"));
    assert_val_eq!(session.run("shared::once(true)"), string("true"));
    assert_val_eq!(session.run("shared::in_lambda(9)"), string("9"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_requirement_errors_use_the_declarations_generic_names() {
    for (name, source) in [
        (
            "function",
            "trait Hidden<Self> { fn hidden(x: Self) -> int; } pub fn f<Element>(x: Element) -> int { hidden(x) }",
        ),
        (
            "implementation",
            "trait Hidden<Self> { fn hidden(x: Self) -> int; } pub struct P<T>(T) pub trait Use<Self> { fn use_(x: Self) -> int; } impl<Element> Use for P<Element> where Element: Hidden { fn use_(x: P<Element>) -> int { hidden(x.0) } }",
        ),
    ] {
        let mut session = TestSession::new();
        assert!(module_fails_with(
            &mut session,
            name,
            source,
            |error| matches!(error,
                CompilationErrorImpl::PrivateRequirementInPublicContract { requirement, .. } if requirement == "Element: Hidden"
            )
        ));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_selection_does_not_choose_a_public_prerequisites_output() {
    let int_impl = "impl Hidden2 for int { fn hidden2(x: int) -> int { x } }";
    let bool_impl = "impl Hidden2 for bool { fn hidden2(x: bool) -> int { 0 } }";
    for impls in [
        vec![int_impl],
        vec![int_impl, bool_impl],
        vec![bool_impl, int_impl],
    ] {
        for prerequisites in [
            "T: Read<Out = O>, O: Hidden2",
            "O: Hidden2, T: Read<Out = O>",
        ] {
            for item in [
                "pub fn f<T>(x: T) -> int { hidden2(read(x)) }".to_owned(),
                format!(
                    "impl<T, O> Hidden for [T] where {prerequisites} {{ fn hidden(x: [T]) -> int {{ hidden2(read(x[0])) }} }} pub fn f<T>(x: T) -> int {{ hidden([x]) }}"
                ),
                format!(
                    "impl<T, O> Use for P<T> where {prerequisites} {{ fn use_(x: P<T>) -> int {{ hidden2(read(x.0)) }} }}"
                ),
            ] {
                let declarations = format!("{}\n{item}", impls.join("\n"));
                let source = format!(
                    r#"
                    pub trait Read<Self |-> Out> {{ fn read(x: Self) -> Out; }}
                    trait Hidden2<Self> {{ fn hidden2(x: Self) -> int; }}
                    trait Hidden<Self> {{ fn hidden(x: Self) -> int ! fallible; }}
                    pub struct P<T>(T)
                    pub trait Use<Self> {{ fn use_(x: Self) -> int; }}
                    {declarations}
                "#
                );
                let mut session = TestSession::new();
                assert!(
                    module_fails_with(&mut session, "a", &source, |error| matches!(
                        error,
                        CompilationErrorImpl::PrivateRequirementInPublicContract { .. }
                    )),
                    "{source}"
                );
            }
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_uniform_private_output_can_determine_a_later_private_input() {
    for body in [
        "same(read(x), conv([x]))",
        "same(conv([x]), read(x))",
        "let y = read(x); let r = hidden(y); same(y, conv([x])); r",
        "let y = read(x); same(y, conv([x])); hidden(y)",
    ] {
        let mut session = TestSession::new();
        compile_module(
            &mut session,
            "a",
            &format!(
                r#"
            pub trait Read<Self |-> Out> {{ fn read(x: Self) -> Out; }}
            trait Conv<Self |-> Out> {{ fn conv(x: Self) -> Out; }}
            impl<T> Conv for <Self = [T] |-> Out = int> {{
                fn conv(x: [T]) -> int {{ 1 }}
            }}
            trait Hidden<Self> {{ fn hidden(x: Self) -> int; }}
            impl Hidden for int {{ fn hidden(x: int) -> int {{ x }} }}
            impl Hidden for bool {{ fn hidden(x: bool) -> int {{ 0 }} }}
            fn same<T>(x: T, y: T) -> T {{ x }}
            pub fn f<T>(x: T) -> int {{ {body} }}
        "#
            ),
        );
        compile_module(
            &mut session,
            "b",
            r#"
            pub struct X;
            use a::Read;
            impl Read for <Self = X |-> Out = int> {
                fn read(x: X) -> int { 1 }
            }
        "#,
        );
        assert_val_eq!(session.run("a::f(b::X)"), int(1), "{body}");
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recorded_private_captures_preserve_distinct_effect_bounds() {
    let impls = [
        "impl<T> H1 for W<T> where W<T>: Hid<! E = ()> { fn h1(x: W<T>) -> int { hid(x) } }",
        "impl<T> H2 for W<T> where W<T>: Hid<! E = (fallible)> { fn h2(x: W<T>) -> int { hid(x) } }",
    ];
    for reverse in [false, true] {
        let mut impls = impls;
        if reverse {
            impls.reverse();
        }
        for body in [
            "h1(W(x)) + h2(W(x)) + hid(W(x))",
            "hid(W(x)) + h2(W(x)) + h1(W(x))",
            "h2(W(x)) + h1(W(x)) + hid(W(x))",
        ] {
            let provider = format!(
                r#"
                pub trait Run<Self |-> ! E> {{ fn run(x: Self) -> int ! E; }}
                struct W<T>(T)
                trait Hid<Self |-> ! E> {{ fn hid(x: Self) -> int ! E; }}
                impl<T, ! E> Hid for <Self = W<T> |-> ! E = E> where T: Run<! E = E> {{
                    fn hid(x: W<T>) -> int {{ run(x.0) }}
                }}
                trait H1<Self> {{ fn h1(x: Self) -> int; }}
                trait H2<Self> {{ fn h2(x: Self) -> int ! fallible; }}
                {}
                pub fn f<T>(x: T) -> int {{ {body} }}
            "#,
                impls.join("\n")
            );
            let mut session = TestSession::new();
            compile_module(&mut session, "a", &provider);
            compile_module(
                &mut session,
                "b",
                r#"
                pub struct X;
                use a::Run;
                impl Run for <Self = X |-> ! E = ()> {
                    fn run(x: X) -> int { 2 }
                }
                pub struct Y;
                impl Run for <Self = Y |-> ! E = (fallible)> {
                    fn run(x: Y) -> int { idiv(4, 2) }
                }
            "#,
            );
            assert_val_eq!(session.run("a::f(b::X)"), int(6), "{provider}");
            assert!(session.try_compile("a::f(b::Y)").is_err(), "{provider}");
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generated_recursive_value_constructs_custom_members_from_self() {
    for array_backed in [false, true] {
        let custom = r#"
        impl<T> Value for Cell<T> where T: Value {
            fn eq(x: Cell<T>, y: Cell<T>) -> bool { eq(x.0, y.0) }
            fn to_string(x: Cell<T>) -> string {
                match x.0 {
                    Some(value) => effects_unsafe { let inner = CELL_CONTENT; f"Cell({inner})" },
                    None => "Cell(empty)",
                }
            }
            fn hash(x: Cell<T>, state: &mut hasher) { hash(x.0, state) }
            fn clone(x: Cell<T>) -> Cell<T> { Cell(x.0) }
            fn drop(x: &mut Cell<T>) { x.0 = None; }
        }
    "#
        .replace(
            "CELL_CONTENT",
            if array_backed { "value[0]" } else { "value" },
        );
        let field = if array_backed {
            "Option<[T]>"
        } else {
            "Option<T>"
        };
        let construction = if array_backed {
            "List::Cons(x, Cell(Some([List::Cons(x, Cell(Some([List::Nil])))])))"
        } else {
            "List::Cons(x, Cell(Some(List::Cons(x, Cell(Some(List::Nil))))))"
        };
        for public in [false, true] {
            for reverse in [false, true] {
                let visibility = if public { "#[private_repr] pub" } else { "" };
                let ty = format!("{visibility} enum List<T> {{ Nil, Cons(T, Cell<List<T>>) }}");
                let items = if reverse {
                    format!("{ty}\n{custom}")
                } else {
                    format!("{custom}\n{ty}")
                };
                let mut session = TestSession::new();
                session.allow_unsafe();
                compile_module(
                    &mut session,
                    "a",
                    &format!(
                        r#"
                struct Cell<T>({field})
                {items}
                pub fn make<T>(x: T) -> List<T> where T: Value {{
                    {construction}
                }}
                pub fn f<T>(x: T) -> string where T: Value {{
                    let values = make(x);
                    let other = values;
                    assert(eq(values, other));
                    to_string((values, other))
                }}
            "#
                    ),
                );
                let rendered = "List::Cons (7, Cell(List::Cons (7, Cell(List::Nil))))";

                assert_val_eq!(
                    session.run("a::f(7)"),
                    string(&format!("({rendered}, {rendered})")),
                );
                if public {
                    assert_val_eq!(session.run("to_string(a::make(7))"), string(rendered));
                }
            }
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_value_evidence_crosses_multiple_custom_members() {
    let mut session = TestSession::new();
    session.allow_unsafe();
    compile_module(
        &mut session,
        "a",
        r#"
        struct Cell<T>(Option<T>)
        impl<T> Value for Cell<T> where T: Value {
            fn eq(x: Cell<T>, y: Cell<T>) -> bool { eq(x.0, y.0) }
            fn to_string(x: Cell<T>) -> string {
                match x.0 { Some(inner) => f"Cell({inner})", None => "Cell(empty)" }
            }
            fn hash(x: Cell<T>, state: &mut hasher) { hash(x.0, state) }
            fn clone(x: Cell<T>) -> Cell<T> { Cell(x.0) }
            fn drop(x: &mut Cell<T>) { x.0 = None; }
        }
        enum List<T> { Nil, Cons(T, Cell<Cell<Tree<T>>>) }
        enum Tree<T> { End, Next(List<T>) }
        pub fn f<T>(x: T) -> string where T: Value {
            let value = List::Cons(x, Cell(Some(Cell(Some(Tree::Next(List::Nil))))));
            let other = value;
            assert(eq(value, other));
            to_string(other)
        }
    "#,
    );
    assert_val_eq!(
        session.run("a::f(7)"),
        string("List::Cons (7, Cell(Cell(Tree::Next (List::Nil))))")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn private_value_prerequisite_cycles_still_need_a_generated_anchor() {
    for reverse in [false, true] {
        let mut session = TestSession::new();
        session.allow_unsafe();
        let implementations = [("A", "B"), ("B", "A")].map(|(name, other)| {
            format!(
                r#"
            impl<T> Value for {name}<T> where T: Value, {other}<T>: Value {{
                fn eq(x: {name}<T>, y: {name}<T>) -> bool {{ eq(x.0, y.0) }}
                fn to_string(x: {name}<T>) -> string {{ to_string(x.0) }}
                fn hash(x: {name}<T>, state: &mut hasher) {{ hash(x.0, state) }}
                fn clone(x: {name}<T>) -> {name}<T> {{ {name}(x.0) }}
                fn drop(x: &mut {name}<T>) {{}}
            }}
        "#
            )
        });
        let (first, second) = if reverse {
            (&implementations[1], &implementations[0])
        } else {
            (&implementations[0], &implementations[1])
        };
        let source = format!(
            r#"
            struct A<T>(T)
            struct B<T>(T)
            {first}
            {second}
            pub fn f<T>(x: T) -> string where T: Value {{ to_string(A(x)) }}
        "#
        );
        assert!(
            module_fails_with(&mut session, "a", &source, |error| matches!(
                error,
                CompilationErrorImpl::PrivateRequirementInPublicContract { .. }
            )),
            "{source}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_declared_field_of_a_generic_receiver_takes_the_evidence_of_the_caller() {
    // What the subscript of a declared field requires of a generic of the function that
    // reads the field is a requirement of that function, however the field is read: the
    // implementation that the module of the function sees for another type is not taken.
    let provider = |body: &str| {
        formatdoc! { r#"
            pub trait Read<Self, Other> {{
                fn read(x: Self, y: Other) -> int;
            }}
            impl Read for <Self = int, Other = int> {{
                fn read(x, y) {{ 7 }}
            }}

            pub struct Box<T>(T)
            pub subscript Box<T>.value(self) -> int {{
                ref {{
                    let zero: int = 0;
                    let local = read(self.0, zero);
                    yield local
                }}
            }}

            fn get(x) {{ x.value }}
            pub struct Wrapper<T>(T)
            pub trait Show<Self> {{ fn show(x: Self) -> int; }}
            impl<T> Show for Wrapper<T> {{
                fn show(x) {{ x.0.value }}
            }}

            pub fn generic<T>(b: Box<T>) -> int {{
                {body}
            }}
        "# }
    };
    for body in [
        "b.value",
        "let field = |x| x.value; field(b)",
        "get(b)",
        "show(Wrapper(b))",
        "let field = |x| x.value; field(b) + get(b) - b.value",
    ] {
        let mut session = TestSession::new();
        session.allow_experimental();
        compile_module(&mut session, "a", &provider(body));
        compile_module(
            &mut session,
            "b",
            indoc! { r#"
                use a::Read;
                struct Q(int)
                impl Read for <Self = Q, Other = int> {
                    fn read(x, y) { 9 }
                }
                pub fn of_q() -> int { a::generic(a::Box(Q(4))) }
                pub fn of_int() -> int { a::generic(a::Box(4)) }
            "# },
        );
        assert_val_eq!(
            session.run("(b::of_q(), b::of_int())"),
            expected_tuple([int(9), int(7)]),
            "{body}"
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_exported_function_uses_a_private_implementation_that_reads_a_field() {
    // The private implementation is chosen where the function is defined, and its dictionary
    // is given the field of the type that it was chosen for. Reading that field needs
    // nothing more, also when the type has another member of a generic type.
    let mut session = TestSession::new();
    compile_module(
        &mut session,
        "a",
        indoc! { r#"
            pub struct Wrapper<T>(T)
            pub struct Flat<A> { value: int, other: A }

            trait Peek<Self> { fn peek(x: Self) -> int; }
            impl<T> Peek for <Self = Wrapper<T>> {
                fn peek(x) { x.0.value + 1 }
            }
            trait Bump<Self> { fn bump(x: &mut Self); }
            impl<T> Bump for <Self = Wrapper<T>> {
                fn bump(x) { x.0.value = x.0.value + 1 }
            }

            pub fn read<A>(a: A) -> int {
                peek(Wrapper(Flat { value: 1, other: a }))
            }
            pub fn written<A>(a: A) -> int {
                let mut wrapper = Wrapper(Flat { value: 1, other: a });
                bump(wrapper);
                bump(wrapper);
                wrapper.0.value
            }

            // Two requirements of an implementation can be one at the types that it is
            // chosen for, and one can need no evidence there, as `Value` of a function.
            fn inc(x: int) -> int { x + 1 }
            trait CopyField<Self> { fn copy_field(x: &mut Self) -> int; }
            impl<T, U> CopyField for Wrapper<(T, U)> {
                fn copy_field(x) {
                    x.0.1.value = x.0.0.value + 1;
                    x.0.1.value
                }
            }
            trait Keep<Self> { fn keep(x: Self) -> int; }
            impl<T, U> Keep for Wrapper<(T, U)> {
                fn keep(x) {
                    let first = x.0.0;
                    let second = x.0.1;
                    1
                }
            }
            pub fn copied<A>(a: A, b: A) -> int {
                let mut wrapper = Wrapper((
                    Flat { value: 3, other: a },
                    Flat { value: 9, other: b },
                ));
                copy_field(wrapper)
            }
            pub fn copied_of_two<A, B>(a: A, b: B) -> int {
                let mut wrapper = Wrapper((
                    Flat { value: 5, other: a },
                    Flat { value: 9, other: b },
                ));
                copy_field(wrapper)
            }
            pub fn kept<A>(a: A) -> int { keep(Wrapper((a, a))) + keep(Wrapper((inc, a))) }
        "# },
    );
    compile_module(
        &mut session,
        "b",
        indoc! { r#"
            struct Mine(string)
            pub fn all() -> (int, int, int, int, int, int, int) {
                (
                    a::read(5),
                    a::read(Mine("s")),
                    a::written(2.5),
                    a::written(Mine("t")),
                    a::copied("a", "b"),
                    a::copied_of_two(1, Mine("u")),
                    a::kept(Mine("v")),
                )
            }
        "# },
    );
    assert_val_eq!(
        session.run("b::all()"),
        expected_tuple([int(2), int(2), int(3), int(3), int(4), int(6), int(2)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_exported_function_reads_a_field_of_a_private_type_through_a_private_implementation() {
    // The requirement of the function names private types and a private trait, so it is
    // reduced where the function is defined. What the implementation requires of a field of
    // a private type is answered there too, by the type, and the function publishes only
    // what an access to that field takes.
    let mut session = TestSession::new();
    session.allow_experimental();
    compile_module(
        &mut session,
        "a",
        indoc! { r#"
            struct Wrapper<T>(T)
            struct Single<A> { value: A }
            struct Pair<A> { value: (A, int) }
            struct Flat<A> { value: int, other: A }
            struct Nested<A> { outer: Single<A> }
            #[private_repr]
            struct Box<T>(T)
            subscript Box<T>.value(self) -> _ {
                ref {
                    let local = self.0;
                    yield local
                }
            }

            // A subscript that requires a trait without methods, which has no evidence, and
            // one with a method, which has.
            pub trait Mark<Self> {}
            impl Mark for int {}
            pub trait Scale<Self> { fn scale(x: Self) -> Self; }
            impl Scale for int {
                fn scale(x) { x * 10 }
            }
            #[private_repr]
            struct Marked<T>(T)
            subscript Marked<T>.value(self) -> T where T: Mark, T: Scale {
                ref {
                    let local = scale(self.0);
                    yield local
                }
            }

            trait Get<Self |-> R> { fn get(x: Self) -> R; }
            impl<T, R> Get for <Self = Wrapper<T> |-> R = R> {
                fn get(x) { x.0.value }
            }
            trait Deep<Self |-> R> { fn deep(x: Self) -> R; }
            impl<T, R> Deep for <Self = Wrapper<T> |-> R = R> {
                fn deep(x) { x.0.outer.value }
            }
            trait Bump<Self> { fn bump(x: &mut Self); }
            impl<T> Bump for <Self = Wrapper<T>> {
                fn bump(x) { x.0.value = x.0.value + 1 }
            }

            pub fn single<A>(a: A) -> A { get(Wrapper(Single { value: a })) }
            pub fn element<A>(a: A) -> A { get(Wrapper(Pair { value: (a, 1) })).0 }
            pub fn deep_one<A>(a: A) -> A {
                deep(Wrapper(Nested { outer: Single { value: a } }))
            }
            pub fn inner<A>(a: A) -> A {
                get(Wrapper(Single { value: Single { value: a } })).value
            }
            pub fn declared<A>(a: A) -> A { get(Wrapper(Box(a))) }
            pub fn marked<A>(a: A) -> A { get(Wrapper(Marked(a))) }
            pub fn written<A>(a: A) -> int {
                let mut wrapper = Wrapper(Flat { value: 1, other: a });
                bump(wrapper);
                get(wrapper)
            }
        "# },
    );
    compile_module(
        &mut session,
        "b",
        indoc! { r#"
            use a::{Mark, Scale};
            struct Mine(int)
            impl Mark for Mine {}
            impl Scale for Mine {
                fn scale(x) { Mine(x.0 + 1) }
            }
            pub fn all() -> (int, string, float, int, int, int, int, int, int) {
                (
                    a::single(5),
                    a::element("a"),
                    a::deep_one(2.5),
                    a::inner(Mine(3)).0,
                    a::declared(8),
                    a::declared(Mine(4)).0,
                    a::written(Mine(0)),
                    a::marked(7),
                    a::marked(Mine(7)).0,
                )
            }
        "# },
    );
    assert_val_eq!(
        session.run("to_string(b::all())"),
        string("(5, a, 2.5, 3, 8, 4, 2, 70, 8)")
    );
    // What the subscript requires is a requirement of the exported function.
    session
        .fail_compilation("a::marked(1.5)")
        .expect_trait_impl_not_found("Mark", &["Self = float"]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_exported_function_uses_a_private_implementation_that_reads_through_a_representation() {
    // An implementation that reads an element of a tuple, or goes through a named type, requires
    // the representation of that type. The head of the type tells it, so the implementation
    // is selected for a type with a generic inside, and the exported function publishes
    // neither the representation nor the element.
    let mut session = TestSession::new();
    session.allow_experimental();
    compile_module(
        &mut session,
        "a",
        indoc! { r#"
            struct Wrapper<T>(T)
            struct Pair<A> { value: (A, int) }
            struct Tagged<A>(A, string)
            struct Deep<A> { inner: Pair<(A, string)> }
            pub struct Open<A> { value: (A, int) }
            enum Shape<A> { Dot(A), Box { w: A, h: int } }

            trait Second<Self |-> R> { fn second(x: Self) -> R; }
            impl<T, R> Second for <Self = Wrapper<T> |-> R = R> {
                fn second(x) { x.0.1 }
            }
            trait First<Self |-> R> { fn first(x: Self) -> R; }
            impl<T, R> First for <Self = Wrapper<T> |-> R = R> {
                fn first(x) { x.0.0 }
            }
            trait Element<Self |-> R> { fn element(x: Self) -> R; }
            impl<T, R> Element for <Self = Wrapper<T> |-> R = R> {
                fn element(x) { x.0.value.0 }
            }
            trait Far<Self |-> R> { fn far(x: Self) -> R; }
            impl<T, R> Far for <Self = Wrapper<T> |-> R = R> {
                fn far(x) { x.0.inner.value.0.0 }
            }
            trait Bump<Self> { fn bump(x: &mut Self); }
            impl<T> Bump for <Self = Wrapper<T>> {
                fn bump(x) { x.0.value.1 = x.0.value.1 + 1 }
            }
            trait Width<Self |-> R> { fn width(x: Self) -> R; }
            impl<T, R> Width for <Self = Wrapper<T> |-> R = R> {
                fn width(x) {
                    match x.0 {
                        Dot(a) => a,
                        Box { w, h } => w,
                    }
                }
            }

            pub fn second_of<A>(a: A) -> A { second(Wrapper((1, a))) }
            pub fn second_twice<A>(a: A) -> A {
                second(Wrapper((1, second(Wrapper((2, a))))))
            }
            pub fn of_tagged<A>(a: A) -> A { first(Wrapper(Tagged(a, "t"))) }
            pub fn of_pair<A>(a: A) -> A { element(Wrapper(Pair { value: (a, 1) })) }
            pub fn of_open<A>(a: A) -> A { element(Wrapper(Open { value: (a, 1) })) }
            pub fn far_of<A>(a: A) -> A {
                far(Wrapper(Deep { inner: Pair { value: ((a, "s"), 3) } }))
            }
            pub fn written<A>(a: A) -> (A, int) {
                let mut wrapper = Wrapper(Pair { value: (a, 1) });
                bump(wrapper);
                wrapper.0.value
            }
            pub fn width_of<A>(a: A, n: int) -> A {
                if n == 0 {
                    width(Wrapper(Shape::Box { w: a, h: 2 }))
                } else {
                    width_of(width(Wrapper(Shape::Dot(a))), n - 1)
                }
            }
        "# },
    );
    compile_module(
        &mut session,
        "b",
        indoc! { r#"
            struct Mine(int)
            pub fn all() -> (string, int, int, float, int, int, (int, int), string) {
                (
                    a::second_of("x"),
                    a::second_twice(Mine(4)).0,
                    a::of_tagged(Mine(1)).0,
                    a::of_pair(2.5),
                    a::of_open(3),
                    a::far_of(Mine(6)).0,
                    (a::written(Mine(9)).0.0, a::written(9).1),
                    a::width_of("w", 2),
                )
            }
        "# },
    );
    assert_val_eq!(
        session.run("to_string(b::all())"),
        string("(x, 4, 1, 2.5, 3, 6, (9, 2), w)")
    );
}
