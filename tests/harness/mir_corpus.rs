// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

// Snippets chosen to cover the operation and control-flow forms a rewrite must carry through:
// calls, generics and dictionary passing, closures, aggregates, variants and matching, loops,
// mutation, strings, and fallible operations. An expression included by the MIR optimization tests
// and by the crate's own cost-budget test.
&[
    ("literal", "fn main() -> int { 42 }"),
    ("arithmetic", "fn main() -> int { let x = 2 + 3; x * 7 }"),
    (
        "generic",
        "fn twice(f, x) { f(f(x)) }\nfn main() -> int { twice(|v| v + 1, 0) }",
    ),
    (
        "conditional",
        "fn main() -> int { let mut n = 0; if n == 0 { n = 1 } else { n = 2 }; n }",
    ),
    (
        "loop",
        "fn main() -> int { let mut sum = 0; for i in 0..5 { sum = sum + i }; sum }",
    ),
    (
        "tuple_and_record",
        "fn main() -> int { let t = (1, 2); let r = { a: t.0, b: t.1 }; r.a + r.b }",
    ),
    (
        "variant_match",
        "fn classify(v) { match v { Some(x) => x, None => 0 } }\n\
         fn main() -> int { classify(Some(3)) + classify(None) }",
    ),
    (
        "string",
        "fn main() -> string { let s = \"ab\"; string_concat(s, \"cd\") }",
    ),
    (
        "closure_capture",
        "fn main() -> int { let n = 5; let add = |x| x + n; add(1) + add(2) }",
    ),
    (
        "array",
        "fn main() -> int { let mut a = [1, 2, 3]; a[0] = 10; a[0] + a[2] }",
    ),
    // Indexing is source-fallible, so this lowers through `invoke` terminators and error edges.
    ("invoke", "fn main() -> int { let a = [1, 2]; a[0] + a[1] }"),
    // A fallible call whose arguments *are* known: it is a fold candidate in every respect except
    // that folding it would have to rewrite the `invoke` terminator's control flow.
    ("invoke_constant", "fn main() -> int { idiv(6, 3) }"),
    (
        "recursion",
        "fn fact(n) { if n <= 1 { 1 } else { n * fact(n - 1) } }\nfn main() -> int { fact(5) }",
    ),
]
