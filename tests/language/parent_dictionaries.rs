// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Parents inside dictionaries: a dictionary gives those of the requirements that its trait
//! implies, so a body that uses an implied requirement reads it from the dictionary of the written
//! one, which is all that its callers supply.

use test_log::test;

use ferlium::{
    format::FormatWith,
    hir::{function::Function, native_functions::NativeFnR, value::NativeDisplay},
    module::{Module, Path},
    types::r#type::Type,
};
use indoc::indoc;

use crate::harness::{TestSession, expected_tuple, float, int, signature, some};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_complete_clause_publishes_only_its_written_requirements() {
    // `+` needs `Num` and `/` needs `Div`, two and one levels below `Real`.
    let src = "fn f<T>(x: T) -> T where T: Real { x / x + x }";
    assert_eq!(
        signature(&mut TestSession::new(), src, "f"),
        "fn f<T>(x: T) -> T ! fallible where T: Real + Value"
    );
    assert_val_eq!(
        TestSession::new().run(&format!("{src}\nf(2.0)")),
        float(3.0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn the_where_constraints_of_a_trait_are_in_its_dictionaries() {
    // `next` needs the iterator that the `where` clause of `Seq` implies.
    let src = indoc! { r#"
        fn first<S, A, I>(s: S) -> Option<A> where S: Seq<Item = A, Iter = I> {
            let mut it = iter(s);
            next(it)
        }
    "# };
    assert!(
        !signature(&mut TestSession::new(), src, "first").contains("Iterator"),
        "the iterator is read from the dictionary of `Seq`"
    );
    assert_val_eq!(
        TestSession::new().run(&format!("{src}\nfirst([4, 5])")),
        some(int(4))
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_trait_with_only_parents_has_a_dictionary() {
    // `Sum` has no method: its dictionary holds only that of `Num`.
    let src = indoc! { r#"
        trait Sum<Self>: Num<Self> {}
        impl Sum for int {}
        impl Sum for float {}
        fn twice<T>(x: T) -> T where T: Sum { x + x }
    "# };
    assert_eq!(
        signature(&mut TestSession::new(), src, "twice"),
        "fn twice<T>(x: T) -> T where T: Sum"
    );
    assert_val_eq!(
        TestSession::new().run(&format!("{src}\n(twice(2), twice(1.5))")),
        expected_tuple([int(4), float(3.0)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn an_impl_reads_implied_requirements_from_its_prerequisites() {
    // The methods use `T: Num`, which `T: Real` implies: the impl requires `T: Real` alone, and
    // its dictionary, built from the caller's, holds those of its own parents too.
    let src = indoc! { r#"
        struct W<T>(T)
        trait Twice<Self> { fn twice(x: Self) -> Self; }
        impl<T> Twice for W<T> where T: Real { fn twice(x: W<T>) -> W<T> { W(x.0 + x.0) } }
        fn generic<T>(x: T) -> T where T: Real { twice(W(x)).0 }
    "# };
    let mut session = TestSession::new();
    let module_id = session.compile(src).module_id;
    let compiler_session = session.session();
    let rendered = compiler_session
        .expect_fresh_module(module_id)
        .format_with(&compiler_session.modules())
        .to_string();
    assert!(
        rendered.contains("impl<A> Twice for W<A> where A: Real"),
        "the impl requires what it writes:\n{rendered}"
    );
    assert_val_eq!(
        TestSession::new().run(&format!("{src}\n(generic(1.5), twice(W(2.5)).0)")),
        expected_tuple([float(3.0), float(5.0)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_dictionary_built_at_run_time_holds_its_parents() {
    // `Real` for `W<T>` is built from the caller's `T: Real`; its parent `Num` for `W<T>` is
    // built there too, and `scale` reads it.
    let src = indoc! { r#"
        struct W<T>(T)
        impl<T> Num for W<T> where T: Num {
            fn add(a: W<T>, b: W<T>) -> W<T> { W(a.0 + b.0) }
            fn sub(a: W<T>, b: W<T>) -> W<T> { W(a.0 - b.0) }
            fn mul(a: W<T>, b: W<T>) -> W<T> { W(a.0 * b.0) }
            fn neg(a: W<T>) -> W<T> { W(-a.0) }
            fn abs(a: W<T>) -> W<T> { W(abs(a.0)) }
            fn signum(a: W<T>) -> W<T> { W(signum(a.0)) }
            fn from_int(n: int) -> W<T> { W(from_int(n)) }
        }
        impl<T> Div for W<T> where T: Div {
            fn div(a: W<T>, b: W<T>) -> W<T> { W(a.0 / b.0) }
        }
        fn scale<T>(x: T) -> T where T: Div { x + x / x }
        fn wrapped<T>(x: T) -> T where T: Div { scale(W(x)).0 }
    "# };
    assert_val_eq!(
        TestSession::new().run(&format!("{src}\nwrapped(4.0)")),
        float(5.0)
    );
    // Parent slots hold the evidence of their requirements at the types of the dictionary.
    assert_val_eq!(
        TestSession::new().run(&format!("{src}\nscale(W(2.0)).0")),
        float(3.0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parent_slots_cross_modules() {
    // The trait, its implementation and the generic code that reads its parent are in three
    // modules; the dictionary built in the second holds the parent read in the third.
    let mut session = TestSession::new();
    session
        .try_compile_module(
            "shape",
            indoc! {r#"
        pub trait Size<Self> { fn size(x: Self) -> int; }
        pub trait Scaled<Self>: Size<Self> { fn scale(x: Self) -> int; }
        impl Size for int { fn size(x: int) -> int { x } }
        impl Scaled for int { fn scale(x: int) -> int { x * 10 } }
    "#},
        )
        .unwrap();
    session
        .try_compile_module(
            "boxes",
            indoc! {r#"
        use shape::*;
        pub struct Box<T>(T)
        impl<T> Size for Box<T> where T: Size { fn size(x: Box<T>) -> int { size(x.0) + 1 } }
        impl<T> Scaled for Box<T> where T: Scaled { fn scale(x: Box<T>) -> int { scale(x.0) * 2 } }
    "#},
        )
        .unwrap();
    session
        .try_compile_module(
            "user",
            indoc! {r#"
        use shape::*;
        use boxes::*;
        pub fn both<T>(x: T) -> int where T: Scaled { size(x) + scale(x) }
        pub fn boxed<T>(x: T) -> int where T: Scaled { both(Box(x)) }
    "#},
        )
        .unwrap();
    assert!(
        !signature(
            &mut session,
            "use shape::*; fn both<T>(x: T) -> int where T: Scaled { size(x) + scale(x) }",
            "both"
        )
        .contains("Size"),
        "`Size` is read from the dictionary of `Scaled`"
    );
    // both(3) = 3 + 30; boxed(3) = both(Box(3)) = (3 + 1) + (30 * 2).
    assert_val_eq!(
        session.run("(user::both(3), user::boxed(3))"),
        expected_tuple([int(33), int(64)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn value_can_be_a_parent_slot() {
    // `Keep` implies `Self: Value`: copying, laying out and showing `T` use the `Value` that the
    // dictionary of `Keep` holds.
    let src = indoc! { r#"
        trait Keep<Self> where Self: Value { fn tag(x: Self) -> int; }
        struct P { a: int, b: string }
        impl Keep for P { fn tag(x: P) -> int { x.a } }
        fn copy<T>(x: T) -> T where T: Keep { let y = x; let z = x; y }
        fn show<T>(x: T) -> string where T: Keep { to_string([x, x]) }
    "# };
    assert_eq!(
        signature(&mut TestSession::new(), src, "show"),
        "fn show<T>(x: T) -> string where T: Keep"
    );
    assert_val_eq!(
        TestSession::new().run(&format!(
            "{src}let p = P {{ a: 1, b: \"s\" }};\n(copy(p).a, show(p))"
        )),
        expected_tuple([
            int(1),
            crate::harness::string("[P { a: 1, b: s }, P { a: 1, b: s }]")
        ])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_parent_whose_implementation_needs_its_child_is_built_from_it() {
    // `Parent<int>` comes from the blanket implementation, which needs `Child<int>`. The
    // dictionary of `Child<int>` gives its parent as a static dictionary, which holds
    // `Child<int>`: neither holds the other's value, so both can be built. `both` reads that
    // parent from the dictionary that it is given.
    let src = indoc! { r#"
        trait Parent<Self> { fn p(x: Self) -> int; }
        trait Child<Self>: Parent<Self> { fn c(x: Self) -> int; }
        impl<T> Parent for T where T: Child {
            fn p(x: T) -> int { c(x) + 10 }
        }
        impl Child for int {
            fn c(x: int) -> int { x }
        }
        fn both<T>(x: T) -> int where T: Child { c(x) + p(x) }
    "# };
    assert_eq!(
        signature(&mut TestSession::new(), src, "both"),
        "fn both<T>(x: T) -> int where T: Child"
    );
    // both(1) = 1 + 11.
    assert_val_eq!(
        TestSession::new().run(&format!("{src}\n(c(1), p(1), both(1))")),
        expected_tuple([int(1), int(11), int(12)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parent_lookup_visits_each_requirement_once() {
    // Each level has two traits whose parents are both traits of the level below: the paths to
    // `Base` double at each level, the requirements do not.
    let levels = 12;
    let mut src = String::from("trait Base<Self> { fn base(x: Self) -> int; }\n");
    let mut below = vec!["Base".to_string()];
    for level in 1..=levels {
        let names = [format!("A{level}"), format!("B{level}")];
        for name in &names {
            let parents = below
                .iter()
                .map(|parent| format!("{parent}<Self>"))
                .collect::<Vec<_>>()
                .join(", ");
            src += &format!("trait {name}<Self>: {parents} {{ fn m{name}(x: Self) -> int; }}\n");
            src += &format!("impl {name} for int {{ fn m{name}(x: int) -> int {{ x }} }}\n");
        }
        below = names.to_vec();
    }
    src += &format!("trait Top<Self>: A{levels}<Self>, B{levels}<Self> {{}}\n");
    src += "impl Base for int { fn base(x: int) -> int { x } }\n";
    src += "impl Top for int {}\n";
    src += "fn f<T>(x: T) -> int where T: Top { base(x) }\n";
    assert_val_eq!(TestSession::new().run(&format!("{src}f(42)")), int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_where_requirement_of_a_trait_on_its_self_makes_a_variable_numeric() {
    // `T: Num` is not published beside `T: Numeric`, which implies it through its `where`
    // clause: the unused result of `make` still defaults to `int`.
    let src = indoc! { r#"
        trait Numeric<Self> where Self: Num {}
        impl Numeric for int {}
        impl Numeric for float {}
        fn make<T>() -> T where T: Numeric { from_int(1) }
        fn k() -> int { let x = make(); 0 }
    "# };
    assert_val_eq!(TestSession::new().run(&format!("{src}\nk()")), int(0));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_native_implementation_of_traits_of_another_module_gets_their_slots() {
    // The host registers implementations of traits that a source module defines, the second a
    // parent of the first, without access to that module: the slots come with the trait.
    #[derive(Debug)]
    struct Opaque;
    impl NativeDisplay for Opaque {
        fn fmt_repr(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "Opaque")
        }
    }
    extern "C" fn opaque_size(_: &Opaque) -> isize {
        1
    }
    extern "C" fn opaque_scale(_: &Opaque) -> isize {
        10
    }
    let mut session = TestSession::new();
    session
        .try_compile_module(
            "shape",
            indoc! {r#"
        pub trait Size<Self> { fn size(x: Self) -> int; }
        pub trait Scaled<Self>: Size<Self> { fn scale(x: Self) -> int; }
    "#},
        )
        .unwrap();
    let (size_id, size_def, scaled_id, scaled_def) = {
        let modules = session.session().modules();
        let (_, shape) = modules.get_by_path(&Path::single_str("shape")).unwrap();
        let size_id = shape.get_trait_id_str("Size").unwrap();
        let scaled_id = shape.get_trait_id_str("Scaled").unwrap();
        (
            size_id,
            shape.trait_def(size_id).clone(),
            scaled_id,
            shape.trait_def(scaled_id).clone(),
        )
    };
    assert_eq!(
        scaled_def.parent_slots, scaled_def.parent_constraints,
        "`Size` is the slot of `Scaled`"
    );
    let path = Path::single_str("host");
    let mut host = Module::new(session.session().modules().next_id(), path.clone());
    host.add_native_type::<Opaque>("Opaque", "A host type.");
    let opaque = Type::primitive::<Opaque>();
    host.add_concrete_impl_for_trait_def_no_locals(
        size_id,
        &size_def,
        [opaque],
        [],
        [],
        [Box::new(NativeFnR::new(opaque_size)) as Function],
    );
    host.add_concrete_impl_for_trait_def_no_locals(
        scaled_id,
        &scaled_def,
        [opaque],
        [],
        [],
        [Box::new(NativeFnR::new(opaque_scale)) as Function],
    );
    session.session_mut().register_module(path, host);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_native_child_whose_parent_needs_it_is_built_from_it() {
    // As for source implementations, the host's `Child<Opaque>` gives its parent `Parent<Opaque>`,
    // which the blanket implementation builds from `Child<Opaque>`, as a static dictionary.
    #[derive(Debug)]
    struct Opaque;
    impl NativeDisplay for Opaque {
        fn fmt_repr(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "Opaque")
        }
    }
    extern "C" fn opaque_child(_: &Opaque) -> isize {
        1
    }
    let mut session = TestSession::new();
    session
        .try_compile_module(
            "family",
            indoc! {r#"
        pub trait Parent<Self> { fn p(x: Self) -> int; }
        pub trait Child<Self>: Parent<Self> { fn c(x: Self) -> int; }
        impl<T> Parent for T where T: Child {
            fn p(x: T) -> int { c(x) + 10 }
        }
    "#},
        )
        .unwrap();
    let (child_id, child_def) = {
        let modules = session.session().modules();
        let (_, family) = modules.get_by_path(&Path::single_str("family")).unwrap();
        let child_id = family.get_trait_id_str("Child").unwrap();
        (child_id, family.trait_def(child_id).clone())
    };
    let path = Path::single_str("host");
    let mut host = Module::new(session.session().modules().next_id(), path.clone());
    host.add_native_type::<Opaque>("Opaque", "A host type.");
    host.add_concrete_impl_for_trait_def_no_locals(
        child_id,
        &child_def,
        [Type::primitive::<Opaque>()],
        [],
        [],
        [Box::new(NativeFnR::new(opaque_child)) as Function],
    );
    session.session_mut().register_module(path, host);
    session.compile(indoc! {r#"
        use family::*;
        use host::*;
        fn both<T>(x: T) -> int where T: Child { c(x) + p(x) }
        fn f(x: Opaque) -> int { both(x) + p(x) }
    "#});
}
