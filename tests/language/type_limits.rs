// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The limits on the height and size of types, and of their representations, which bound the stack
//! and the work that types cost the compiler, whatever their source.

use test_log::test;

use crate::harness::{TestSession, int};
use ferlium::{
    compiler::error::{CompilationErrorImpl, CompilerLimitKind},
    types::r#type::{
        REPRESENTATION_HEIGHT_LIMIT, REPRESENTATION_SIZE_LIMIT, TYPE_HEIGHT_LIMIT, TYPE_SIZE_LIMIT,
    },
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

/// Assert that compiling `src` exceeds the type limit `kind`, and return the value that exceeded
/// it and the source text that the error points at.
fn type_limit_error(src: &str, kind: CompilerLimitKind) -> (usize, String) {
    let error = TestSession::new().fail_compilation(src);
    let CompilationErrorImpl::CompilerLimitExceeded(error) = error.into_inner() else {
        panic!("expected a type limit error for:\n{src}");
    };
    let limit = match kind {
        CompilerLimitKind::TypeHeight => TYPE_HEIGHT_LIMIT as usize,
        CompilerLimitKind::TypeSize => TYPE_SIZE_LIMIT as usize,
        CompilerLimitKind::RepresentationHeight => REPRESENTATION_HEIGHT_LIMIT as usize,
        CompilerLimitKind::RepresentationSize => REPRESENTATION_SIZE_LIMIT as usize,
        _ => unreachable!("not a type limit"),
    };
    assert_eq!((error.kind, error.limit), (kind, limit));
    assert!(error.actual > error.limit);
    assert!(!error.span.is_synthesized(), "the error has a location");
    let at = src[error.span.start_usize()..error.span.end_usize()].to_string();
    (error.actual, at)
}

/// Assert that compiling `src` exceeds the type limit `kind` with the value `actual`, and return
/// the source text that the error points at.
fn assert_type_limit(src: &str, kind: CompilerLimitKind, actual: usize) -> String {
    let (error_actual, at) = type_limit_error(src, kind);
    assert_eq!(error_actual, actual);
    at
}

/// `n` aliases, each wrapping the previous one in `W`, and a function taking the last.
fn alias_chain(n: usize) -> String {
    let aliases = (1..=n)
        .map(|i| format!("type D{i} = W<D{}>;", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    format!("struct W<T>(T)\ntype D0 = int;\n{aliases}\nfn f(x: D{n}) -> int {{ 1 }}\n0")
}

/// A chain of aliases is as high as its length: the deepest that a function can take compiles,
/// and the alias that crosses the limit is an error, at its definition. The function type is one
/// level more than its argument.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn alias_chains_are_limited_in_height() {
    let deepest = TYPE_HEIGHT_LIMIT as usize - 2;
    assert_val_eq!(TestSession::new().run(&alias_chain(deepest)), int(0));
    let src = alias_chain(TYPE_HEIGHT_LIMIT as usize);
    let at = assert_type_limit(&src, CompilerLimitKind::TypeHeight, 129);
    assert_eq!(at, format!("W<D{}>", TYPE_HEIGHT_LIMIT - 1));
}

/// `n` aliases from `D1` to `Dn`, each a pair of the previous one, from `D0 = int`: the size
/// doubles at each, `Di` having 2^(i+1) - 1 nodes.
fn pair_aliases(n: usize) -> String {
    let aliases = (1..=n)
        .map(|i| format!("type D{i} = (D{0}, D{0});", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    format!("type D0 = int;\n{aliases}")
}

/// The pair aliases up to `Dn`, and nothing else.
fn pair_chain(n: usize) -> String {
    format!("{}\n0", pair_aliases(n))
}

/// The size counts a repeated part at each of its occurrences, so a chain of pairs reaches it
/// at a small height.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn shared_parts_count_at_each_occurrence() {
    // `D11` has 2^12 - 1 nodes.
    assert_val_eq!(TestSession::new().run(&pair_chain(11)), int(0));
    let at = assert_type_limit(&pair_chain(12), CompilerLimitKind::TypeSize, (1 << 13) - 1);
    assert_eq!(at, "(D11, D11)");
}

/// `n` lets, each wrapping the previous value in `W`, from `base`.
fn let_chain(n: usize, base: &str) -> String {
    let lets = (1..=n)
        .map(|i| format!("    let a{i} = W(a{});", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    format!("struct W<T>(T)\nfn g() -> int {{\n    let a0 = {base};\n{lets}\n    1\n}}\ng()")
}

/// Inferred types are limited as written ones are, at the expression that crosses the limit,
/// whether the innermost type is known or still a variable.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn inferred_types_are_limited_in_height() {
    let deepest = TYPE_HEIGHT_LIMIT as usize - 1;
    for base in ["true", "1"] {
        assert_val_eq!(TestSession::new().run(&let_chain(deepest, base)), int(1));
        let src = let_chain(deepest + 1, base);
        let at = assert_type_limit(&src, CompilerLimitKind::TypeHeight, 129);
        assert_eq!(at, format!("let a{0} = W(a{1});", deepest + 1, deepest));
    }
}

/// `n` functions, each applying the previous one twice to its argument: let-polymorphism makes
/// the type of the last one doubly exponential in `n`.
fn doubling_functions(n: usize) -> String {
    let functions = (1..=n)
        .map(|i| format!("fn f{i}(x) {{ f{0}(f{0}(x)) }}", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    format!("fn f0(x) {{ (x, x) }}\n{functions}\n0")
}

/// A type that grows by instantiation is refused when it is built, before any work on it. Its
/// size is measured once the substitution that builds it is complete.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn types_grown_by_instantiation_are_limited_in_size() {
    assert_val_eq!(TestSession::new().run(&doubling_functions(3)), int(0));
    let src = doubling_functions(4);
    let (_, at) = type_limit_error(&src, CompilerLimitKind::TypeSize);
    assert_eq!(at, "fn f4(x) { f3(f3(x)) }");
}

/// A function or trait method, as `kind`, taking `args` arguments, each a pair chain of `D9`,
/// of 1023 nodes.
fn wide_signature(kind: &str, args: usize) -> String {
    let aliases = pair_aliases(9);
    let params = (0..args)
        .map(|i| format!("a{i}: D9"))
        .collect::<Vec<_>>()
        .join(", ");
    let item = match kind {
        "fn" => format!("fn f({params}) -> int {{ 1 }}"),
        _ => format!("trait W<T> {{ fn f({params}) -> T; }}"),
    };
    format!("{aliases}\n{item}\n0")
}

/// The type of a function is limited as a whole: arguments each within the limits may exceed
/// them together.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn signatures_are_limited_as_a_whole() {
    for kind in ["fn", "trait"] {
        // 1 + 4 · 1023 + 1 nodes.
        assert_val_eq!(TestSession::new().run(&wide_signature(kind, 4)), int(0));
        let src = wide_signature(kind, 5);
        let at = assert_type_limit(&src, CompilerLimitKind::TypeSize, 5 * 1023 + 2);
        assert!(at.starts_with("fn f(a0: D9"), "{at}");
    }
}

/// A recursive type of `variants` variants, sharing one payload of `width` occurrences of the
/// type, and a generic function receiving it.
fn shared_recursive_payload(variants: usize, width: usize) -> String {
    let payload = vec!["R<T>"; width].join(", ");
    let variants = (0..variants)
        .map(|i| format!("V{i}(P<T>)"))
        .collect::<Vec<_>>()
        .join(" | ");
    format!(
        "type P<T> = ({payload});\ntype R<T> = {variants} | N(T);\n\
         fn gen<T>(r: R<T>) -> int {{ 1 }}\nfn main(r: R<int>) -> int {{ gen(r) }}\n0"
    )
}

/// The size of a recursive type counts each of its members once, however many share it, so a
/// type within the limits stays within them when substitution rebuilds it. Counted at each
/// occurrence, the payload would be over the limit: 1 + 40 · (1 + 110) + 1 nodes.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn shared_recursive_members_count_once() {
    let src = shared_recursive_payload(40, 110);
    assert_val_eq!(TestSession::new().run(&src), int(0));
}

/// A recursive alias is measured once its group is built, and checked at its definition, used or
/// not.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_aliases_are_limited_at_their_definition() {
    let alias = "Link(R) | One(D11) | Two(D11) | End";
    let src = format!("{}\ntype R = {alias};\n0", pair_aliases(11));
    let (_, at) = type_limit_error(&src, CompilerLimitKind::TypeSize);
    assert_eq!(at, alias);
}

/// A function type can be a member of a recursive type, as `(R<T>) -> R<T>` is of `R<T>`. It
/// then counts that type once, whether written as an alias, or as the signature of a function or
/// of a trait method, although its parameter and its result, each the whole type, would together
/// exceed the size limit.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_signatures_count_their_type_once() {
    let src = format!(
        "{}\ntype R<T> = Step((R<T>) -> R<T>) | Data(D10) | Item(T) | End;\n\
         type Sig = (R<int>) -> R<int>;\n\
         fn f(x: R<int>) -> R<int> {{ x }}\n\
         trait M<Self> {{ fn g(x: R<Self>) -> R<Self>; }}\n\
         impl M for int {{ fn g(x: R<int>) -> R<int> {{ x }} }}\n0",
        pair_aliases(10)
    );
    assert_val_eq!(TestSession::new().run(&src), int(0));
}

/// Defaulting a type variable tries candidates, and a limit reached while checking one is
/// reported, rather than taken as the candidate not applying.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn defaulting_reports_type_limits() {
    let growing = "trait R<Self> {}\nimpl<T> R for T where (T, T): R {}";
    for (function, use_site) in [
        ("fn mk<T>() -> [T] where T: R { [] }", "mk()"),
        ("fn s<T>(x: Option<T>) -> int where T: R { 0 }", "s(None)"),
    ] {
        let src = format!("{growing}\n{function}\n{use_site}");
        let (_, at) = type_limit_error(&src, CompilerLimitKind::TypeSize);
        assert_eq!(at, "(T, T): R");
    }
}

/// `n` structural aliases in a ring, each holding the next one twice, and a function taking the
/// first: the paths through the ring double at each member.
fn ring_of_joins(n: usize) -> String {
    let aliases = (0..n)
        .map(|i| format!("type R{i} = T{i}(R{0}, R{0}) | N{i};", (i + 1) % n))
        .collect::<Vec<_>>()
        .join("\n");
    format!("{aliases}\nfn f(x: R0) -> R0 {{ x }}")
}

/// A recursive type costs the compiler its members, not its paths, of which there can be
/// exponentially many: the largest ring that the height limit allows compiles, also as the input
/// of a written impl, whose effects are checked along every path.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_types_cost_their_members_not_their_paths() {
    // The ring has a member for each alias and each payload, so its height is twice its length,
    // plus one for `()`.
    let longest = (TYPE_HEIGHT_LIMIT as usize - 1) / 2;
    let ring = ring_of_joins(longest);
    assert_val_eq!(TestSession::new().run(&format!("{ring}\n0")), int(0));
    let src = format!(
        "{ring}\nstruct Wrap<T>(T)\ntrait Marker<Self> {{}}\nimpl Marker for Wrap<R0> {{}}\n0"
    );
    assert_val_eq!(TestSession::new().run(&src), int(0));
    let src = format!("{}\n0", ring_of_joins(longest + 1));
    let (_, at) = type_limit_error(&src, CompilerLimitKind::TypeHeight);
    assert!(at.starts_with('T'), "{at}");
}

/// `n` structs from `S1` to `Sn`, each holding the previous one inside `nesting` one-element
/// tuples, from `S0 { x: int }`.
fn struct_chain(n: usize, nesting: usize) -> String {
    let structs = (1..=n)
        .map(|i| {
            let (open, close) = ("(".repeat(nesting), ",)".repeat(nesting));
            format!("struct S{i} {{ x: {open}S{}{close} }}", i - 1)
        })
        .collect::<Vec<_>>()
        .join("\n");
    format!("struct S0 {{ x: int }}\n{structs}\n0")
}

/// The representation of a type definition expands the named types it uses, so a chain of
/// structs is as high as all of its records, named types and tuples. The longest chain within the
/// limit compiles, and the struct that crosses it is an error, at its definition.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn struct_chains_are_limited_in_representation_height() {
    let limit = REPRESENTATION_HEIGHT_LIMIT as usize;
    for nesting in [0, 100] {
        // `S0` is 3 high, its named type, its record and `int`, and each struct adds its named
        // type, its record and its tuples.
        let step = 2 + nesting;
        let longest = (limit - 3) / step;
        TestSession::new().compile(&struct_chain(longest, nesting));
        let src = struct_chain(longest + 1, nesting);
        let actual = 3 + (longest + 1) * step;
        let at = assert_type_limit(&src, CompilerLimitKind::RepresentationHeight, actual);
        assert!(at.starts_with(&format!("struct S{} ", longest + 1)), "{at}");
    }
}

/// `n` enums in a ring, each holding the next one.
fn enum_ring(n: usize) -> String {
    let enums = (0..n)
        .map(|i| format!("enum E{i} {{ A(E{}), N }}", (i + 1) % n))
        .collect::<Vec<_>>()
        .join("\n");
    format!("{enums}\n0")
}

/// A walk over a representation can go through each definition of a recursive group once, so the
/// group is as high as all of its definitions: here three levels per enum, its variants, the
/// payload of `A` and the named type in it. A named type is one level above its group, and the
/// payload of `A` one above that of the next enum. The first definition of the group in the source
/// is reported.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_groups_are_limited_in_representation_height() {
    let longest = (REPRESENTATION_HEIGHT_LIMIT as usize - 2) / 3;
    TestSession::new().compile(&enum_ring(longest));
    let (_, at) = type_limit_error(
        &enum_ring(longest + 1),
        CompilerLimitKind::RepresentationHeight,
    );
    assert_eq!(at, "enum E0 { A(E1), N }");
}

/// `n` structs from `S1` to `Sn`, each holding the previous one twice, from `S0 { x: int }`.
fn struct_pairs(n: usize) -> String {
    let structs = (1..=n)
        .map(|i| format!("struct S{i} {{ a: S{0}, b: S{0} }}", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    format!("struct S0 {{ x: int }}\n{structs}\n0")
}

/// A representation has at most `REPRESENTATION_SIZE_LIMIT` parts, a repeated part counting at
/// each occurrence, so a chain of structs each holding the previous one twice is limited in
/// length, at the definition that crosses the limit.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn representations_are_limited_in_size() {
    // `S0` has 3 parts, its named type, its record and `int`, and `Si` its named type, its
    // record and twice `Si-1`: 5 * 2^i - 2.
    let size = |i: usize| 5 * (1 << i) - 2;
    let longest = (0..)
        .take_while(|&i| size(i) <= REPRESENTATION_SIZE_LIMIT as usize)
        .last()
        .unwrap();
    TestSession::new().compile(&struct_pairs(longest));
    let src = struct_pairs(longest + 1);
    let at = assert_type_limit(
        &src,
        CompilerLimitKind::RepresentationSize,
        size(longest + 1),
    );
    assert!(at.starts_with(&format!("struct S{} ", longest + 1)), "{at}");
}

/// The representation of a generic definition's type depends on its arguments, so it is checked
/// where the type is used: at each node and each local, a parameter that no node uses included.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn representations_of_instantiations_are_limited_where_used() {
    // `P<X>` has its named type, its record and twice `X`, so `Di` has 6 * 2^i - 2 parts.
    let size = |i: usize| 6 * (1 << i) - 2;
    let over = (0..)
        .find(|&i| size(i) > REPRESENTATION_SIZE_LIMIT as usize)
        .unwrap();
    let within = over - 1;
    let aliases = (1..=over)
        .map(|i| format!("type D{i} = P<D{}>;", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    let defs = format!("struct P<T> {{ a: T, b: T }}\ntype D0 = P<int>;\n{aliases}");
    let src = format!("{defs}\nfn f(x: D{within}) -> D{within} {{ x }}\n0");
    assert_val_eq!(TestSession::new().run(&src), int(0));
    for (function, expected) in [
        (
            format!("fn f(x: D{over}) -> D{over} {{ x }}"),
            "x".to_string(),
        ),
        (format!("fn f(x: D{over}) -> int {{ 0 }}"), "x".to_string()),
        (
            format!("fn f() -> int {{ let g = |x| 0; let h: (D{over}) -> int = g; 0 }}"),
            "x".to_string(),
        ),
        (
            format!("fn mk() -> D{over} {{ mk() }}"),
            "{ mk() }".to_string(),
        ),
    ] {
        let src = format!("{defs}\n{function}\n0");
        let at = assert_type_limit(&src, CompilerLimitKind::RepresentationSize, size(over));
        assert_eq!(at, expected);
    }
}

/// A recursive group passes its parameters unchanged to its recursive references, so each
/// parameter's argument counts as many times as the parameter occurs, not as often as all of them.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_groups_count_each_argument_at_its_own_occurrences() {
    // As in `representations_of_instantiations_are_limited_where_used`, `Di` has 6 * 2^i - 2
    // parts, and `D9`, 3070, fits once but not twice.
    let size = |i: usize| 6 * (1 << i) - 2;
    let aliases = (1..=10)
        .map(|i| format!("type D{i} = P<D{}>;", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    let defs = format!(
        "struct P<T> {{ a: T, b: T }}\ntype D0 = P<int>;\n{aliases}\n\
         enum E<T, U> {{ Left(T), Right(U), Again(E<T, U>), End }}"
    );
    let function = |d: usize| format!("{defs}\nfn f(x: E<D{d}, int>) -> E<D{d}, int> {{ x }}\n0");
    assert_val_eq!(TestSession::new().run(&function(9)), int(0));
    // `E` adds 8 parts to `D10`: its named type, its variant, the tuples of its three payloads,
    // `E<T, U>` in `Again`, which is one part, the unit of `End`, and `int`.
    let at = assert_type_limit(
        &function(10),
        CompilerLimitKind::RepresentationSize,
        size(10) + 8,
    );
    assert_eq!(at, "x");
}

/// A callback is a leaf of representations, also as the argument of a named type: a definition that
/// reaches another only through a callback is not in a recursive group with it, and holds none of
/// its parts.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn callbacks_in_named_types_do_not_join_recursive_groups() {
    // As in `representations_of_instantiations_are_limited_where_used`, `D10` alone exceeds the
    // limit.
    let aliases = (1..=10)
        .map(|i| format!("type D{i} = P<D{}>;", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    let src = format!(
        "struct P<T> {{ a: T, b: T }}\ntype D0 = P<int>;\n{aliases}\n\
         struct Callback<T> {{ f: () -> T }}\n\
         enum A<T> {{ EndA, Later(Callback<B<T>>) }}\n\
         enum B<T> {{ EndB, Back(A<T>), Data(T, T) }}\n\
         fn f(x: A<D10>) -> int {{ 0 }}\n0"
    );
    assert_val_eq!(TestSession::new().run(&src), int(0));
}

/// A match holds its condition's value under the view of its cases, which counts as the value's own
/// type: a recursive enum within the limits can be matched, although its cases, each charged with
/// the enum, exceed them.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn matched_recursive_enums_count_as_themselves() {
    let cases = |tag: &str, payload: &str| {
        (0..60)
            .map(|i| format!("{tag}{i}({payload})"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let src = format!(
        "enum Ast {{ End, {} }}\n\
         enum Stmt {{ Done, {} }}\n\
         enum Expr {{ Lit, {} }}\n\
         fn ast(x: Ast) -> int {{ match x {{ Ast::F0(a) => 1 + ast(a), _ => 0 }} }}\n\
         fn stmt(x: Stmt) -> int {{ match x {{ Stmt::S0(e, s) => expr(e) + stmt(s), _ => 1 }} }}\n\
         fn expr(x: Expr) -> int {{ match x {{ Expr::X0(s, e) => stmt(s) + expr(e), _ => 1 }} }}\n\
         ast(Ast::F0(Ast::End)) + stmt(Stmt::S0(Expr::Lit, Stmt::Done))",
        cases("F", "Ast"),
        cases("S", "Expr, Stmt"),
        cases("X", "Stmt, Expr"),
    );
    assert_val_eq!(TestSession::new().run(&src), int(3));
}

/// A structural type counts its cases, also when they are those of a recursive enum, however the
/// type is obtained: written, or substituted for a parameter. So a field fits or not whether it is
/// written with the enum or with a parameter, and a matched value of such a type is checked.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn cases_of_recursive_enums_count_as_written() {
    // `Ast` has 93 parts: its named type, its variant, the unit of `End`, and in each of its 45
    // other cases a tuple and a reference to its group. `Shape<Ast>` has its cases, each holding
    // all of `Ast`.
    let ast = 3 + 2 * 45;
    let shape = 2 + 45 * (1 + ast);
    let cases = |payload: &str, separator: &str| {
        (0..45)
            .map(|i| format!("F{i}({payload})"))
            .collect::<Vec<_>>()
            .join(separator)
    };
    let defs = format!(
        "enum Ast {{ End, {} }}\n\
         type Shape<T> = End | {};\n\
         struct Generic<T> {{ value: Shape<T> }}",
        cases("Ast", ", "),
        cases("T", " | "),
    );
    let concrete = format!("{defs}\nstruct Concrete {{ value: Shape<Ast> }}\n0");
    let at = assert_type_limit(&concrete, CompilerLimitKind::RepresentationSize, shape + 2);
    assert_eq!(at, "struct Concrete { value: Shape<Ast> }");
    let generic = format!("{defs}\nfn f(x: Generic<Ast>) -> int {{ 0 }}\n0");
    let at = assert_type_limit(&generic, CompilerLimitKind::RepresentationSize, shape + 2);
    assert_eq!(at, "x");
    let matched =
        format!("{defs}\nfn f(x: Shape<Ast>) -> int {{ match x {{ End => 0, _ => 1 }} }}\n0");
    let at = assert_type_limit(&matched, CompilerLimitKind::RepresentationSize, shape);
    assert_eq!(at, "x");
}

/// A program taking `ty` wrapped in `levels` pairs of `P`.
fn pairs_of(defs: &str, ty: &str, levels: usize) -> String {
    let wrapped = (0..levels).fold(ty.to_string(), |ty, _| format!("P<{ty}>"));
    format!("{defs}\nstruct P<T> {{ a: T, b: T }}\nfn f(x: {wrapped}) -> int {{ 0 }}\n0")
}

/// Asserts that each of `tys`, of `parts` parts, fits in 8 levels of pairs but not in 9.
fn assert_fit_in_eight_pairs(defs: &str, tys: &[&str], parts: usize) {
    for ty in tys {
        assert_val_eq!(TestSession::new().run(&pairs_of(defs, ty, 8)), int(0));
        let parts = (1 << 9) * parts + 2 * ((1 << 9) - 1);
        let src = pairs_of(defs, ty, 9);
        let at = assert_type_limit(&src, CompilerLimitKind::RepresentationSize, parts);
        assert_eq!(at, "x", "{ty}");
    }
}

/// The named types of a recursive group given the same arguments have the same representation, also
/// when an argument refers back to one of them.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn named_types_of_a_group_count_alike() {
    let defs = "enum A<T> { EndA, Data(T), Go(B<T>) }\n\
                enum B<T> { EndB, Back(A<T>) }\n\
                type X = Done | Wrap(A<X>);";
    assert_fit_in_eight_pairs(defs, &["A<X>", "B<X>"], 11);
}

/// An argument counts the same whether a definition holds it or a parameter substituted with it,
/// also when it is on a cycle that the definition's shape reaches again: the cycle counts once.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn types_count_alike_through_parameters_on_cycles() {
    let defs = "enum A<T> { End, Data(T), Next(A<T>) }\n\
                type X = Done | Wrap(A<X>);\n\
                struct Wrapper<T> { value: A<T> }\n\
                struct Direct { value: A<X> }\n\
                struct Holder<T> { value: Done | Wrap(A<T>) }\n\
                struct Plain { value: X }";
    assert_fit_in_eight_pairs(defs, &["Wrapper<X>", "Direct", "Holder<X>", "Plain"], 9);
}

/// `n` aliases, each giving `W{width}` the previous one and `tag`, where each `Wi` holds the
/// previous one, and a function taking the last.
fn alias_compositions(width: usize, n: usize, tag: &str) -> String {
    let structs = (1..=width)
        .map(|i| format!("struct W{i}<T, U> {{ x: W{}<T, U> }}", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    let aliases = (1..=n)
        .map(|i| format!("type D{i} = W{width}<D{}, {tag}>;", i - 1))
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        "type Flag = End | Back(Flag);\nstruct W0<T, U> {{ x: T, tag: U }}\n{structs}\n\
         type D0 = int;\n{aliases}\nfn f(x: D{n}) -> int {{ 0 }}\n0"
    )
}

/// Aliases compose definitions within the limits into a representation far beyond them. The
/// summaries of the definitions give its height. An argument on a cycle, here `Flag`, makes the
/// walk measure their shapes instead: it stops once deeper than a representation within the limit
/// can be high, rather than going as deep as this one is, and reports that depth.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn walks_of_composed_representations_stop_beyond_the_limit() {
    let (width, n) = (16, 20);
    // Each alias adds the named type and the record of each `Wi`.
    let height = 2 * n * (width + 1) + 1;
    let limit = REPRESENTATION_HEIGHT_LIMIT as usize;
    for (tag, actual) in [("int", height), ("Flag", limit + 1)] {
        let src = alias_compositions(width, n, tag);
        let at = assert_type_limit(&src, CompilerLimitKind::RepresentationHeight, actual);
        assert_eq!(at, "x", "{tag}");
    }
}

/// Generic code can double a type argument at each call, through its dictionaries, which the type
/// limits do not see. Optimization specializes and inlines only within those limits, and
/// compile-time evaluation spends fuel at each call, so such a chain compiles promptly.
#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_code_doubling_its_arguments_compiles() {
    let chain = |k: usize| {
        (1..=k)
            .map(|i| format!("fn f{i}(x) {{ f{}((x, x)) }}\n", i - 1))
            .collect::<String>()
    };
    // `g` would build 2^30 integers, and is never called.
    let src = format!(
        "fn f0(x) {{ 0 }}\n{}fn g() -> int {{ f30(1) }}\n0",
        chain(30)
    );
    assert_val_eq!(TestSession::new().run(&src), int(0));
    let src = format!("fn f0(x) {{ 0 }}\n{}f4(1)", chain(4));
    assert_val_eq!(TestSession::new().run(&src), int(0));
}
