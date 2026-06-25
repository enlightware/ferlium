// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use test_log::test;

use ferlium::ide::{AnnotationData, Compiler as IdeCompiler};
use indoc::indoc;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

fn compile_source(src: &str) -> IdeCompiler {
    let mut compiler = IdeCompiler::new();
    assert!(
        compiler.compile(src).is_none(),
        "source should compile successfully"
    );
    compiler
}

fn annotated_source(src: &str, annotations: impl IntoIterator<Item = AnnotationData>) -> String {
    let char_to_byte = |char_pos: usize| {
        src.char_indices()
            .map(|(index, _)| index)
            .nth(char_pos)
            .unwrap_or(src.len())
    };

    let mut grouped = Vec::<(usize, String)>::new();
    for annotation in annotations {
        if let Some((_, hint)) = grouped.last_mut().filter(|(pos, _)| *pos == annotation.pos) {
            hint.push_str(&annotation.hint);
        } else {
            grouped.push((annotation.pos, annotation.hint));
        }
    }

    let mut annotated = src.to_string();
    for (pos, hint) in grouped.into_iter().rev() {
        annotated.insert_str(char_to_byte(pos), &hint);
    }
    annotated
}

fn annotated_ide_source(compiler: &mut IdeCompiler, src: &str) -> String {
    annotated_source(src, compiler.get_annotations())
}

fn light_annotated_ide_source(compiler: &mut IdeCompiler, src: &str) -> String {
    annotated_source(src, compiler.get_light_annotations())
}

fn annotation_hints(compiler: &mut IdeCompiler) -> String {
    compiler
        .get_annotations()
        .into_iter()
        .map(|annotation| annotation.hint)
        .collect()
}

fn light_annotation_hints(compiler: &mut IdeCompiler) -> String {
    compiler
        .get_light_annotations()
        .into_iter()
        .map(|annotation| annotation.hint)
        .collect()
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn light_annotations_hide_value_and_parent_constraints() {
    let src = indoc! { r#"
        fn needs_real<T>(value: T) -> T
        where
            T: Value,
            T: Num,
            T: Div,
            T: Real
        {
            value
        }
    "# };
    let mut compiler = compile_source(src);
    let full_annotations = annotation_hints(&mut compiler);
    let light_annotations = light_annotation_hints(&mut compiler);

    assert!(
        full_annotations.contains("T: Div + Num + Real + Value"),
        "expected full annotations to keep all constraints, got: {full_annotations}"
    );
    assert!(
        light_annotations.contains("T: Real")
            && !light_annotations.contains("T: Value")
            && !light_annotations.contains("T: Num")
            && !light_annotations.contains("T: Div"),
        "expected light annotations to keep only Real, got: {light_annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn light_annotations_group_simple_unary_trait_constraints() {
    let src = indoc! { r#"
        trait Alpha<Self> {}
        trait Beta<Self> {}

        fn constrained<T>(value: T) -> T
        where
            T: Beta,
            T: Alpha
        {
            value
        }
    "# };
    let mut compiler = compile_source(src);
    let annotations = light_annotation_hints(&mut compiler);

    assert!(
        annotations.contains("T: Alpha + Beta"),
        "expected grouped unary trait constraints in light annotations, got: {annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn light_annotations_keep_structural_constraints() {
    let src = indoc! { r#"
        fn get_name<T>(value: T) {
            value.name
        }
    "# };
    let mut compiler = compile_source(src);
    let annotations = light_annotation_hints(&mut compiler);
    let repr_pos = annotations.find("⇝");
    let field_pos = annotations.find("name");

    assert!(
        repr_pos.is_some()
            && field_pos.is_some()
            && repr_pos < field_pos
            && !annotations.contains("Repr"),
        "expected compact Repr and structural field constraints in light annotations, got: {annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn light_annotations_hide_fallible_effect() {
    let src = indoc! { r#"
        fn get(xs: [int]) {
            xs[0]
        }
    "# };
    let mut compiler = compile_source(src);
    let full_annotations = annotation_hints(&mut compiler);
    let light_annotations = light_annotation_hints(&mut compiler);

    assert!(
        full_annotations.contains("! fallible"),
        "expected full annotations to show fallible effect, got: {full_annotations}"
    );
    assert!(
        !light_annotations.contains("fallible"),
        "expected light annotations to hide fallible effect, got: {light_annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn light_annotations_keep_non_fallible_effects() {
    let src = indoc! { r#"
        fn call(f: (() -> int ! (read, fallible))) {
            f()
        }
    "# };
    let mut compiler = compile_source(src);
    let full_annotations = annotation_hints(&mut compiler);
    let light_annotations = light_annotation_hints(&mut compiler);

    assert!(
        full_annotations.contains("! (read, fallible)"),
        "expected full annotations to show all effects, got: {full_annotations}"
    );
    assert!(
        light_annotations.contains("! read") && !light_annotations.contains("fallible"),
        "expected light annotations to keep read and hide fallible, got: {light_annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn light_annotations_hide_fallible_inside_returned_function_types() {
    let src = indoc! { r#"
        fn keep(f: (() -> int ! fallible)) {
            f
        }
    "# };
    let mut compiler = compile_source(src);
    let full_annotations = annotation_hints(&mut compiler);
    let light_annotations = light_annotation_hints(&mut compiler);

    assert!(
        full_annotations.contains("fallible"),
        "expected full annotations to show nested fallible effect, got: {full_annotations}"
    );
    assert!(
        light_annotations.contains("() -> int ! e₀") && !light_annotations.contains("fallible"),
        "expected light annotations to hide nested fallible effect, got: {light_annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn light_annotations_keep_non_fallible_effects_inside_returned_function_types() {
    let src = indoc! { r#"
        fn keep(f: (() -> int ! read)) {
            f
        }
    "# };
    let mut compiler = compile_source(src);
    let light_annotations = light_annotation_hints(&mut compiler);

    assert!(
        light_annotations.contains("() -> int ! (read, e₀)"),
        "expected light annotations to keep nested read effect, got: {light_annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn light_annotations_keep_generic_effect_binders_used_by_callable_effects() {
    let src = indoc! { r#"
        fn call(f) {
            f()
        }
    "# };
    let mut compiler = compile_source(src);
    let light = light_annotated_ide_source(&mut compiler, src);

    assert!(
        light.contains("<A ! e₀>")
            && light.contains("f: () -> A ! e₀")
            && light.contains("-> A ! e₀"),
        "expected light annotations to keep callable effect binder and uses, got:\n{light}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn annotations_preserve_source_effect_generic_names() {
    let src = indoc! { r#"
        fn run<! E>(f: () -> int ! E) {
            f()
        }
    "# };
    let mut compiler = compile_source(src);
    let annotated = annotated_ide_source(&mut compiler, src);

    assert!(
        annotated.contains("fn run<! E>(f: () -> int ! E) -> int ! E"),
        "expected annotations to preserve source effect generic name, got:\n{annotated}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn annotations_insert_inferred_type_params_before_existing_effect_params() {
    let src = indoc! { r#"
        fn keep<! E>(f: () -> int ! E, value) {
            value
        }
    "# };
    let mut compiler = compile_source(src);
    let annotated = annotated_ide_source(&mut compiler, src);

    assert!(
        annotated.contains("fn keep<A ! E>(f: () -> int ! E, value: A) -> A"),
        "expected annotations to insert type params before existing effect params, got:\n{annotated}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn light_annotations_hide_generic_effects_used_only_as_associated_outputs() {
    let src = indoc! { r#"
        fn get_iterator(seq) {
            iter(seq)
        }
    "# };
    let mut compiler = compile_source(src);
    let full_annotations = annotation_hints(&mut compiler);
    let light_annotations = light_annotation_hints(&mut compiler);

    assert!(
        full_annotations.contains("IterEffect = e₀"),
        "expected full annotations to show associated sequence effect, got: {full_annotations}"
    );
    assert!(
        !light_annotations.contains("IterEffect") && !light_annotations.contains("e₀"),
        "expected light annotations to hide associated-only generic effect, got: {light_annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ide_annotations_add_function_effect_annotation_once() {
    let src = indoc! { r#"
        fn get(xs: [int]) -> int {
            xs[0]
        }
    "# };
    let mut compiler = compile_source(src);
    let annotated = annotated_ide_source(&mut compiler, src);

    let occurrences = annotated.matches("! fallible").count();
    assert!(
        occurrences == 1,
        "effect annotation should be rendered once, got {occurrences} occurrences:\n{annotated}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ide_annotations_skip_synthesized_function_signature_spans() {
    let src = indoc! { r#"
        fn f(x, y) {
            (x.1, x.1.0, y == x.1)
        }

        fn l2(v) {
            let sq = |x| x * x;
            sq(v.x) + sq(v.y)
        }

        fn id(x) {
            x
        }

        (id(1), id(true), id(|x, y| (y, x))(1, 1.3), l2({x:1, y:2}))
    "# };
    let mut compiler = compile_source(src);
    let full = annotated_ide_source(&mut compiler, src);
    let light = light_annotated_ide_source(&mut compiler, src);

    assert!(
        full.starts_with("fn f"),
        "full annotations should not insert synthesized function generics at the start, got:\n{full}"
    );
    assert!(
        light.starts_with("fn f"),
        "light annotations should not insert synthesized function generics at the start, got:\n{light}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn lambda_ide_annotations_do_not_show_internal_function_names() {
    let src = "let f = |x| x + 1; f(1)";
    let mut compiler = compile_source(src);
    let annotated = annotated_ide_source(&mut compiler, src);
    assert!(
        annotated.contains("|x: int| -> int x + 1"),
        "expected lambda signature annotations, got: {annotated}"
    );
    assert!(
        !annotated.contains("<lambda>") && !annotated.contains("$lambda"),
        "lambda annotations should not expose internal names, got: {annotated}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ide_annotations_preserve_and_extend_source_generic_names() {
    let src = indoc! { r#"
        fn f<X>(x: X, y) {
            (x, y)
        }
    "# };
    let mut compiler = compile_source(src);
    let annotations = annotation_hints(&mut compiler);
    assert!(
        annotations.contains(", B")
            && annotations.contains(": B")
            && annotations.contains("-> (X, B)")
            && !annotations.contains("<X, B>"),
        "expected IDE annotations to extend `<X>` with generated `B`, got: {annotations}"
    );

    let src = indoc! { r#"
        fn f<B>(x: B, y) {
            (x, y)
        }
    "# };
    let mut compiler = compile_source(src);
    let annotations = annotation_hints(&mut compiler);
    assert!(
        annotations.contains(", C")
            && annotations.contains(": C")
            && annotations.contains("-> (B, C)")
            && !annotations.contains(", B, B"),
        "expected IDE annotations to skip source generic name collision, got: {annotations}"
    );

    let src = indoc! { r#"
        fn f<X>(y, x: X) {
            (y, x)
        }
    "# };
    let mut compiler = compile_source(src);
    let annotations = annotation_hints(&mut compiler);
    assert!(
        annotations.contains(", B")
            && annotations.contains(": B")
            && annotations.contains("-> (B, X)")
            && !annotations.contains("<B, X>"),
        "expected IDE annotations to keep explicit generic first even when inferred arguments appear first, got: {annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_generic_alias_ide_annotations_preserve_recursive_only_arguments() {
    let src = indoc! { r#"
        type Tree<A, B> = Leaf(A) | Node2(Tree<A, B>, Tree<A, B>);
        let a: Tree<_, _> = Leaf(1);
    "# };
    let mut compiler = compile_source(src);
    let annotated = annotated_ide_source(&mut compiler, src);

    assert!(
        annotated.contains("let a: Tree<_, _> ⇨ Tree<int, _> = Leaf(1);"),
        "IDE annotation should preserve the recursive alias and show a placeholder for the erased recursive-only argument, got:\n{annotated}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_alias_recovery_ide_annotations_prefer_concrete_arguments_earlier() {
    let src = indoc! { r#"
        type Tree<A, B> = Leaf(A) | Node2(Tree<A, B>, Tree<A, B>);
        type Tra<C, D> = Node2(Tra<C, D>, Tra<C, D>) | Leaf(D);
        let a: Tree<_, _> = Leaf(1);
        let b: Tra<_, _> = a;
        a
    "# };
    let mut compiler = compile_source(src);
    let annotated = annotated_ide_source(&mut compiler, src);

    assert!(
        annotated.contains("let a: Tree<_, _> ⇨ Tree<int, _> = Leaf(1);"),
        "alias recovery should prefer the alias with concrete arguments earlier, got:\n{annotated}"
    );
    assert!(
        annotated.contains("a: Tree<int, _>"),
        "final expression should use the same preferred alias spelling, got:\n{annotated}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_generic_alias_ide_annotations_preserve_arguments_on_cycle_edges() {
    let src = indoc! { r#"
        type Tree<T> = Leaf(T) | Node(Tree<T>, Tree<T>);

        fn sum<T>(tree: Tree<T>) {
            match tree {
                Leaf(v) => v,
                Node(l, r) => sum(l) + sum(r),
            }
        }
    "# };
    let mut compiler = compile_source(src);
    let signature = compiler.fn_signature("sum").unwrap();
    let annotations = annotation_hints(&mut compiler);

    assert!(
        signature.contains("Tree<T>"),
        "signature should render the recursive alias with a single argument, got: {signature}"
    );
    assert!(
        annotations.contains("Tree<T>"),
        "IDE annotations should render the recursive alias with a single argument, got: {annotations}"
    );
    assert!(
        annotations.contains(": T"),
        "IDE local annotations should preserve the source type parameter name, got: {annotations}"
    );
    assert!(
        !signature.contains("Tree<G>") && !annotations.contains("Tree<G>"),
        "recursive edge kept an uninstantiated type variable; signature: {signature}; annotations: {annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn recursive_generic_alias_ide_annotations_do_not_leak_borrowed_argument_temps() {
    let src = indoc! { r#"
        type Tree<T> = Leaf(T) | Node(Tree<T>, Tree<T>);

        fn sum<T>(tree: Tree<T>) {
            match tree {
                Leaf(v) => v,
                Node(l, r) => sum(l) + sum(r)
            }
        }

        sum(Node(Node(Leaf(2), Leaf(3)), Leaf(4)))
    "# };
    let expected = indoc! { r#"
        type Tree<T> = Leaf(T) | Node(Tree<T>, Tree<T>);

        fn sum<T>(tree: Tree<T>) -> T ! fallible where T: Num + Value {
            match tree {
                Leaf(v: T) => v,
                Node(l: Tree<T>, r: Tree<T>) => sum(tree: l) + sum(tree: r)
            }
        }

        sum(tree: Node(Node(Leaf(2), Leaf(3)), Leaf(4))): int
    "# };
    let mut compiler = compile_source(src);
    let annotated = annotated_ide_source(&mut compiler, src);

    assert_eq!(annotated, expected);
    assert!(
        !annotated.contains("+:"),
        "operator spans should not receive type annotations:\n{annotated}"
    );
    assert!(
        !annotated.contains("tree: sum:"),
        "borrowed argument temporaries should not move hints before the call:\n{annotated}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn ide_annotations_hide_generated_operator_argument_names() {
    let src = indoc! { r#"
        fn ops(a: float, b: float) {
            (a + b, a * b, a / b, -a, a == b)
        }
    "# };
    let mut compiler = compile_source(src);
    let annotated = annotated_ide_source(&mut compiler, src);

    assert!(
        !annotated.contains("left:")
            && !annotated.contains("right:")
            && !annotated.contains("value:"),
        "operator annotations should not expose generated trait-method argument names:\n{annotated}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn array_index_ide_annotations_do_not_expose_generated_place_call() {
    let src = indoc! { r#"
        fn first() {
            let xs = [10, 20];
            xs[{ let i = 0; i }]
        }
    "# };
    let mut compiler = compile_source(src);
    let annotated = annotated_ide_source(&mut compiler, src);

    assert!(
        annotated.contains("let i: int = 0;"),
        "array index annotations should still walk source operands, got:\n{annotated}"
    );
    assert!(
        !annotated.contains("array_index")
            && !annotated.contains("place")
            && !annotated.contains("array: ")
            && !annotated.contains("index: "),
        "array index annotations should not expose generated addressor-place call details, got:\n{annotated}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn match_on_temporary_scrutinee_acquires_value_obligation() {
    // A non-place temporary scrutinee (here the call result `f(x)`) is materialized into an owned,
    // dropped local, so its type acquires a `Value` obligation.
    let src = "fn ho(f, x) { match f(x) { 0 => 1, _ => 2 } }";
    let mut compiler = compile_source(src);
    let annotations = annotation_hints(&mut compiler);
    assert!(
        annotations.contains("Value"),
        "expected the matched temporary's type to acquire a `Value` obligation, got: {annotations}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn match_on_place_scrutinee_adds_no_value_obligation() {
    // Dual of the test above: a place scrutinee (the parameter `x`) already owns its storage, is
    // matched in place, and must NOT acquire a spurious `Value` obligation.
    let src = "fn g(x) { match x { 0 => 1, _ => 2 } }";
    let mut compiler = compile_source(src);
    let annotations = annotation_hints(&mut compiler);
    assert!(
        !annotations.contains("Value"),
        "a place scrutinee must not acquire a `Value` obligation, got: {annotations}"
    );
}
