// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use test_log::test;

use ferlium::ide::Compiler as IdeCompiler;
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

fn annotated_ide_source(compiler: &mut IdeCompiler, src: &str) -> String {
    let char_to_byte = |char_pos: usize| {
        src.char_indices()
            .map(|(index, _)| index)
            .nth(char_pos)
            .unwrap_or(src.len())
    };

    let mut grouped = Vec::<(usize, String)>::new();
    for annotation in compiler.get_annotations() {
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

fn annotation_hints(compiler: &mut IdeCompiler) -> String {
    compiler
        .get_annotations()
        .into_iter()
        .map(|annotation| annotation.hint)
        .collect()
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

        fn sum<T>(tree: Tree<T>) -> T where T: Num, T: Value {
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
