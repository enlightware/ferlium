// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ferlium::error::{
    CompilationErrorImpl, DuplicatedFieldContext, DuplicatedVariantContext,
    InvalidTraitConstraintKind,
};
use ferlium::eval::eval_node;
use ferlium::format::FormatWith;
use ferlium::module::id::Id;
use ferlium::std::logic::bool_type;
use ferlium::std::math::{float_type, int_type};
use ferlium::std::string::string_type;
use ferlium::r#type::{Type, TypeVar};
use ferlium::value::Value;
use ferlium::{CompilerSession, SourceId, ast, parse_module_and_expr};
use test_log::test;

use indoc::indoc;
use ustr::ustr;

use crate::harness::{TestSession, bool, float, int, string};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

fn parse_module_ast(src: &str) -> ast::PModule {
    parse_module_and_expr(src, SourceId::from_index(1), true)
        .unwrap_or_else(|errors| panic!("module should parse cleanly, got {errors:?}"))
        .0
}

fn parse_type_ast(src: &str) -> ast::PType {
    CompilerSession::default()
        .parse_defined_type("test", src)
        .unwrap_or_else(|error| panic!("type should parse cleanly, got {error:?}"))
        .0
}

fn run_and_pretty_format(session: &mut TestSession, src: &str) -> String {
    let module_and_expr = session.compile(src);
    let expr = module_and_expr
        .expr
        .expect("expected an expression to evaluate in pretty-print regression");
    let module = session
        .session()
        .expect_fresh_module(module_and_expr.module_id);
    let value = eval_node(
        &module.ir_arena,
        expr.expr,
        module_and_expr.module_id,
        &expr.locals,
        session.session(),
    )
    .unwrap()
    .into_value();
    value.display_pretty(&expr.ty.ty).to_string()
}

fn format_compiled_module(session: &mut TestSession, src: &str) -> String {
    let module_id = session.compile(src).module_id;
    let module = session.session().expect_fresh_module(module_id);
    module.format_with(session.session().modules()).to_string()
}

fn join_src(parts: &[&str]) -> String {
    parts.join("\n\n")
}

fn assert_compiled_fn_type(session: &mut TestSession, src: &str, fn_name: &str, expected_ty: &str) {
    let function = session.compile_and_get_fn_def(src, fn_name);
    assert!(
        function.ty_scheme.ty_quantifiers.is_empty(),
        "expected a concrete function type, got {}",
        function
            .ty_scheme
            .display_rust_style(&session.std_module_env()),
    );
    assert_eq!(
        function
            .ty_scheme
            .ty()
            .format_with(&session.std_module_env())
            .to_string(),
        expected_ty,
    );
}

fn option_type_def_src() -> &'static str {
    indoc! { r#"
        enum Option<A> {
            None,
            Some(A),
        }
    "# }
}

fn witnessed_type_def_src() -> &'static str {
    indoc! { r#"
        struct Witnessed<Input, Output>
        where
            Input: testing::TestAssoc<Output = Output>
        (Input)
    "# }
}

fn map_iterator_type_def_src() -> &'static str {
    indoc! { r#"
        struct MapIterator<I, T, O>
        where
            I: Iterator<Item = T>
        {
            iterator: I,
            mapper: (T) -> O,
        }
    "# }
}

fn zip_iterator_type_def_src() -> &'static str {
    indoc! { r#"
        struct ZipIterator<L, R, A, B>
        where
            L: Iterator<Item = A>,
            R: Iterator<Item = B>
        {
            left: L,
            right: R,
        }
    "# }
}

fn map_iterator_impl_src() -> &'static str {
    indoc! { r#"
        impl Iterator for MapIterator<I, T, O> {
            fn next(it: &mut MapIterator<I, T, O>) -> None | Some(O) {
                match next(it.iterator) {
                    Some(data) => Some(it.mapper(data)),
                    None => None,
                }
            }
        }
    "# }
}

fn map_iterator_impl_with_explicit_binders_src() -> &'static str {
    indoc! { r#"
        impl<I, T, O> Iterator for MapIterator<I, T, O> {
            fn next(it: &mut MapIterator<I, T, O>) -> None | Some(O) {
                match next(it.iterator) {
                    Some(data) => Some(it.mapper(data)),
                    None => None,
                }
            }
        }
    "# }
}

fn map_iterator_impl_with_explicit_outputs_src() -> &'static str {
    indoc! { r#"
        impl<I, T, O> Iterator for <Self = MapIterator<I, T, O> |-> Item = O> {
            fn next(it: &mut MapIterator<I, T, O>) -> None | Some(O) {
                match next(it.iterator) {
                    Some(data) => Some(it.mapper(data)),
                    None => None,
                }
            }
        }
    "# }
}

fn zip_iterator_impl_src() -> &'static str {
    indoc! { r#"
        impl Iterator for ZipIterator<L, R, A, B> {
            fn next(it: &mut ZipIterator<L, R, A, B>) -> None | Some((A, B)) {
                match next(it.left) {
                    Some(left) => match next(it.right) {
                        Some(right) => Some((left, right)),
                        None => None,
                    },
                    None => None,
                }
            }
        }
    "# }
}

fn collect_expected_path_segments<S, I>(expected: I) -> Vec<ustr::Ustr>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    expected
        .into_iter()
        .map(|segment| ustr(segment.as_ref()))
        .collect()
}

trait PathAssert: std::fmt::Debug {
    fn kind_name(&self) -> &'static str;
    fn path_segments(&self) -> Option<Vec<ustr::Ustr>>;
}

impl<T> PathAssert for &T
where
    T: PathAssert + ?Sized,
{
    fn kind_name(&self) -> &'static str {
        (*self).kind_name()
    }

    fn path_segments(&self) -> Option<Vec<ustr::Ustr>> {
        (*self).path_segments()
    }
}

impl PathAssert for ast::Path {
    fn kind_name(&self) -> &'static str {
        "path"
    }

    fn path_segments(&self) -> Option<Vec<ustr::Ustr>> {
        Some(self.segments.iter().map(|(name, _)| *name).collect())
    }
}

impl PathAssert for ast::PType {
    fn kind_name(&self) -> &'static str {
        "path type"
    }

    fn path_segments(&self) -> Option<Vec<ustr::Ustr>> {
        match self {
            ast::PType::Path(path) => Some(path.segments.iter().map(|(name, _)| *name).collect()),
            _ => None,
        }
    }
}

fn assert_path_matches<T>(value: &T, expected: &[ustr::Ustr])
where
    T: PathAssert + ?Sized,
{
    match value.path_segments() {
        Some(actual) => assert_eq!(actual, expected),
        None => panic!(
            "expected a {} for {expected:?}, got {value:?}",
            value.kind_name()
        ),
    }
}

fn assert_path_is_impl<T, S, I>(value: &T, expected: I)
where
    T: PathAssert + ?Sized,
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let expected = collect_expected_path_segments(expected);
    assert_path_matches(value, &expected);
}

macro_rules! assert_path_is {
    ($value:expr, $expected:expr) => {{
        assert_path_is_impl(&$value, $expected);
    }};
}

fn expect_applied_path<'a, S, I>(ty: &'a ast::PType, expected: I) -> &'a [ast::PTypeSpan]
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let expected = collect_expected_path_segments(expected);
    match ty {
        ast::PType::AppliedPath { path, args } => {
            assert_path_matches(path, &expected);
            args
        }
        other => panic!("expected an applied path type for {expected:?}, got {other:?}"),
    }
}

fn assert_applied_path_matches<S1, I1, S2, I2, J>(
    ty: &ast::PType,
    expected_path: I1,
    expected_args: J,
) where
    I1: IntoIterator<Item = S1>,
    S1: AsRef<str>,
    J: IntoIterator<Item = I2>,
    I2: IntoIterator<Item = S2>,
    S2: AsRef<str>,
{
    let args = expect_applied_path(ty, expected_path);
    let expected_args = expected_args
        .into_iter()
        .map(collect_expected_path_segments)
        .collect::<Vec<_>>();
    assert_eq!(args.len(), expected_args.len());
    for (arg, expected_arg) in args.iter().zip(&expected_args) {
        assert_path_matches(&arg.0, expected_arg);
    }
}

macro_rules! assert_applied_path_is {
    ($ty:expr, $expected_path:expr, $expected_args:expr) => {{
        assert_applied_path_matches(&$ty, $expected_path, $expected_args);
    }};
}

#[derive(Debug)]
enum ExpectedConstraintInput {
    Unnamed(Vec<ustr::Ustr>),
    Named {
        name: ustr::Ustr,
        ty: Vec<ustr::Ustr>,
    },
}

#[derive(Debug)]
struct ExpectedConstraint {
    trait_name: Vec<ustr::Ustr>,
    input_types: Vec<ExpectedConstraintInput>,
    output_types: Vec<(ustr::Ustr, Vec<ustr::Ustr>)>,
}

fn unnamed_constraint_input<S, I>(ty: I) -> ExpectedConstraintInput
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    ExpectedConstraintInput::Unnamed(collect_expected_path_segments(ty))
}

fn named_constraint_input<S, I>(name: &str, ty: I) -> ExpectedConstraintInput
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    ExpectedConstraintInput::Named {
        name: ustr(name),
        ty: collect_expected_path_segments(ty),
    }
}

fn output_binding<S, I>(name: &str, ty: I) -> (ustr::Ustr, Vec<ustr::Ustr>)
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    (ustr(name), collect_expected_path_segments(ty))
}

fn constraint<S1, I1, I2, I3>(
    trait_name: I1,
    input_types: I2,
    output_types: I3,
) -> ExpectedConstraint
where
    I1: IntoIterator<Item = S1>,
    S1: AsRef<str>,
    I2: IntoIterator<Item = ExpectedConstraintInput>,
    I3: IntoIterator<Item = (ustr::Ustr, Vec<ustr::Ustr>)>,
{
    ExpectedConstraint {
        trait_name: collect_expected_path_segments(trait_name),
        input_types: input_types.into_iter().collect(),
        output_types: output_types.into_iter().collect(),
    }
}

fn assert_type_def_constraints<S, I, C>(
    type_def: &ast::PTypeDef,
    expected_params: I,
    constraints: C,
) where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
    C: IntoIterator<Item = ExpectedConstraint>,
{
    assert_eq!(
        type_def
            .generic_params
            .iter()
            .map(|(name, _)| *name)
            .collect::<Vec<_>>(),
        collect_expected_path_segments(expected_params)
    );

    let constraints = constraints.into_iter().collect::<Vec<_>>();
    assert_eq!(type_def.where_clause.len(), constraints.len());
    for (actual, expected) in type_def.where_clause.iter().zip(constraints) {
        assert_path_matches(&actual.trait_name, &expected.trait_name);
        assert_eq!(actual.input_types.len(), expected.input_types.len());
        for (actual_input, expected_input) in actual.input_types.iter().zip(expected.input_types) {
            match expected_input {
                ExpectedConstraintInput::Unnamed(tys) => {
                    assert!(actual_input.name.is_none());
                    assert_path_matches(&actual_input.ty.0, &tys);
                }
                ExpectedConstraintInput::Named { name, ty: tys } => {
                    assert_eq!(actual_input.name.unwrap().0, name);
                    assert_path_matches(&actual_input.ty.0, &tys);
                }
            }
        }

        assert_eq!(actual.output_types.len(), expected.output_types.len());
        for (actual_output, (expected_name, expected_tys)) in
            actual.output_types.iter().zip(expected.output_types)
        {
            assert_eq!(actual_output.name.0, expected_name);
            assert_path_matches(&actual_output.ty.0, &expected_tys);
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn define_enum_types() {
    let mut session = TestSession::new();
    let mod_src = indoc! { r#"
        // Basic unit variants
        enum SimpleColor {
            Red,
            Green,
            Blue
        }

        // Single-type variants
        enum Option {
            Some(int),
            None
        }
        enum Option2 {
            Some(int),
            None,
        }

        // Multi-type tuple variants
        enum Player {
            Basic(string),
            Positioned(string, int, int),
            FullData(string, int, int, float)
        }

        // Record-style variants
        enum Event {
            Click { x: int, y: int },
            KeyPress { key: string, shift: bool },
            Resize { width: int, height: int }
        }

        // Mixed variants in same enum
        enum Message {
            Quit,
            Move { x: int, y: int },
            Write(string),
            ChangeColor(int, int, int),
            Callback((int) -> int)
        }

        // Empty enum
        enum Empty {}
    "# };
    let module_id = session.compile(mod_src).module_id;
    let module = session.session().expect_fresh_module(module_id);

    let simple_color = module.get_type_def(ustr("SimpleColor")).unwrap();
    assert_eq!(simple_color.name, ustr("SimpleColor"));
    let simple_color = simple_color.shape_ty().data().as_variant().unwrap().clone();
    assert_eq!(
        simple_color,
        [
            (ustr("Blue"), Type::unit()),
            (ustr("Green"), Type::unit()),
            (ustr("Red"), Type::unit()),
        ]
    );

    let option_type = module.get_type_def(ustr("Option")).unwrap();
    assert_eq!(option_type.name, ustr("Option"));
    let option_type = option_type.shape_ty().data().as_variant().unwrap().clone();
    assert_eq!(
        option_type,
        [
            (ustr("None"), Type::unit()),
            (ustr("Some"), Type::tuple([int_type()])),
        ]
    );

    let option2_type = module.get_type_def(ustr("Option2")).unwrap();
    assert_eq!(option2_type.name, ustr("Option2"));
    let option2_type = option2_type.shape_ty().data().as_variant().unwrap().clone();
    assert_eq!(option2_type, option_type);

    let player_type = module.get_type_def(ustr("Player")).unwrap();
    assert_eq!(player_type.name, ustr("Player"));
    let player_type = player_type.shape_ty().data().as_variant().unwrap().clone();
    assert_eq!(
        player_type,
        [
            (ustr("Basic"), Type::tuple([string_type()])),
            (
                ustr("FullData"),
                Type::tuple([string_type(), int_type(), int_type(), float_type()])
            ),
            (
                ustr("Positioned"),
                Type::tuple([string_type(), int_type(), int_type()])
            ),
        ]
    );

    let event_type = module.get_type_def(ustr("Event")).unwrap();
    assert_eq!(event_type.name, ustr("Event"));
    let event_type = event_type.shape_ty().data().as_variant().unwrap().clone();
    assert_eq!(
        event_type,
        [
            (
                ustr("Click"),
                Type::record([(ustr("x"), int_type()), (ustr("y"), int_type())])
            ),
            (
                ustr("KeyPress"),
                Type::record([(ustr("key"), string_type()), (ustr("shift"), bool_type())])
            ),
            (
                ustr("Resize"),
                Type::record([(ustr("height"), int_type()), (ustr("width"), int_type())])
            ),
        ]
    );

    let message_type = module.get_type_def(ustr("Message")).unwrap();
    assert_eq!(message_type.name, ustr("Message"));
    let message_type = message_type.shape_ty().data().as_variant().unwrap().clone();
    assert_eq!(
        message_type,
        [
            (
                ustr("Callback"),
                Type::tuple([Type::function_by_val([int_type()], int_type())]),
            ),
            (
                ustr("ChangeColor"),
                Type::tuple([int_type(), int_type(), int_type()])
            ),
            (
                ustr("Move"),
                Type::record([(ustr("x"), int_type()), (ustr("y"), int_type())])
            ),
            (ustr("Quit"), Type::unit()),
            (ustr("Write"), Type::tuple([string_type()])),
        ]
    );

    let empty_type = module.get_type_def(ustr("Empty")).unwrap();
    assert_eq!(empty_type.name, ustr("Empty"));
    assert!(empty_type.shape_ty().data().is_never());

    assert_eq!(
        session
            .fail_compilation("enum Invalid { A, B, A }")
            .into_inner()
            .into_duplicated_variant()
            .unwrap()
            .3,
        DuplicatedVariantContext::Enum
    );
    assert_eq!(
        session
            .fail_compilation("enum Invalid { A, B, A(int) }")
            .into_inner()
            .into_duplicated_variant()
            .unwrap()
            .3,
        DuplicatedVariantContext::Enum
    );
    assert_eq!(
        session
            .fail_compilation("enum Invalid { A, B, A { a: int } }")
            .into_inner()
            .into_duplicated_variant()
            .unwrap()
            .3,
        DuplicatedVariantContext::Enum
    );
    assert_eq!(
        session
            .fail_compilation("enum Invalid { A, B { a: T | T(int) } }")
            .into_inner()
            .into_duplicated_variant()
            .unwrap()
            .3,
        DuplicatedVariantContext::Variant
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parse_generic_type_definitions() {
    let module = parse_module_ast(indoc! { r#"
        struct Box<T>(T)
        struct Pair<A, B>(A, B)
        struct Entry<K, V> { key: K, value: V }

        enum Option<T> {
            Some(T),
            None,
        }

        enum Result<T, E> {
            Ok(T),
            Err(E),
        }
    "# });

    assert_eq!(module.type_defs.len(), 5);

    let box_def = &module.type_defs[0];
    assert_eq!(
        box_def
            .generic_params
            .iter()
            .map(|(name, _)| *name)
            .collect::<Vec<_>>(),
        vec![ustr("T")]
    );
    assert!(box_def.where_clause.is_empty());
    match &box_def.shape {
        ast::PType::Tuple(fields) => {
            assert_eq!(fields.len(), 1);
            assert_path_is!(&fields[0].0, ["T"]);
        }
        other => panic!("expected tuple struct shape, got {other:?}"),
    }

    let entry_def = &module.type_defs[2];
    assert_eq!(
        entry_def
            .generic_params
            .iter()
            .map(|(name, _)| *name)
            .collect::<Vec<_>>(),
        vec![ustr("K"), ustr("V")]
    );
    match &entry_def.shape {
        ast::PType::Record(fields) => {
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0.0, ustr("key"));
            assert_path_is!(&fields[0].1.0, ["K"]);
            assert_eq!(fields[1].0.0, ustr("value"));
            assert_path_is!(&fields[1].1.0, ["V"]);
        }
        other => panic!("expected record struct shape, got {other:?}"),
    }

    let option_def = &module.type_defs[3];
    assert_eq!(
        option_def
            .generic_params
            .iter()
            .map(|(name, _)| *name)
            .collect::<Vec<_>>(),
        vec![ustr("T")]
    );
    match &option_def.shape {
        ast::PType::Variant(variants) => {
            assert_eq!(variants.len(), 2);
            assert_eq!(variants[0].0.0, ustr("Some"));
            match &variants[0].1.0 {
                ast::PType::Tuple(fields) => {
                    assert_eq!(fields.len(), 1);
                    assert_path_is!(&fields[0].0, ["T"]);
                }
                other => panic!("expected tuple payload, got {other:?}"),
            }
            assert_eq!(variants[1].0.0, ustr("None"));
            assert_eq!(variants[1].1.0, ast::PType::Unit);
        }
        other => panic!("expected enum shape, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parse_generic_type_use_sites() {
    let box_ty = parse_type_ast("Box<int>");
    assert_applied_path_is!(&box_ty, ["Box"], [["int"]]);

    let pair_ty = parse_type_ast("Pair<int, string>");
    assert_applied_path_is!(&pair_ty, ["Pair"], [["int"], ["string"]]);

    let nested_ty = parse_type_ast("testing::Option<Pair<int, string>>");
    let nested_args = expect_applied_path(&nested_ty, ["testing", "Option"]);
    assert_eq!(nested_args.len(), 1);
    assert_applied_path_is!(&nested_args[0].0, ["Pair"], [["int"], ["string"]]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parse_doc_commented_type_definitions() {
    let module = parse_module_ast(indoc! { r#"
        /// An optional value.
        enum Option<T> {
            Some(T),
            None,
        }

        /// Stores one value.
        struct Box<T>(T)
    "# });

    assert_eq!(module.type_defs.len(), 2);
    assert_eq!(
        module.type_defs[0].doc_comments,
        vec!["An optional value.".to_string()]
    );
    assert_eq!(
        module.type_defs[1].doc_comments,
        vec!["Stores one value.".to_string()]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parse_generic_types_in_function_signatures() {
    let module = parse_module_ast(indoc! { r#"
        fn demo(value: Option<string>) -> Pair<int, string> {
            value
        }
    "# });

    let function = &module.functions[0];
    let (_, arg_ty, _) = function.args[0].ty.as_ref().unwrap();
    assert_applied_path_is!(arg_ty, ["Option"], [["string"]]);

    let (ret_ty, _) = function.ret_ty.as_ref().unwrap();
    assert_applied_path_is!(ret_ty, ["Pair"], [["int"], ["string"]]);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parse_generic_trait_impl_headers() {
    let module = parse_module_ast(indoc! { r#"
        struct InferredIterator<I, T, O> {
            iterator: I,
            mapper: (T) -> O,
        }

        struct ExplicitIterator<I, T, O> {
            iterator: I,
            mapper: (T) -> O,
        }

        struct S(string)

        impl<I, T, O> Iterator for InferredIterator<I, T, O> {
            fn next(it: &mut InferredIterator<I, T, O>) -> None | Some(O) {
                None
            }
        }

        impl<I, T, O> Iterator for <Self = ExplicitIterator<I, T, O> |-> Item = O> {
            fn next(it: &mut ExplicitIterator<I, T, O>) -> None | Some(O) {
                None
            }
        }

        impl Cast for <int, S> {
            fn cast(self) -> S {
                self
            }
        }
    "# });

    let inferred_header = &module.impls[0];
    assert_eq!(
        inferred_header
            .generic_params
            .iter()
            .map(|(name, _)| *name)
            .collect::<Vec<_>>(),
        vec![ustr("I"), ustr("T"), ustr("O")]
    );
    let inferred_for_trait = inferred_header.for_trait.as_ref().unwrap();
    assert_eq!(inferred_for_trait.input_types.len(), 1);
    assert!(inferred_for_trait.output_types.is_empty());
    assert!(inferred_for_trait.input_types[0].name.is_none());
    assert_applied_path_is!(
        &inferred_for_trait.input_types[0].ty.0,
        ["InferredIterator"],
        [["I"], ["T"], ["O"]]
    );

    let explicit_header = &module.impls[1];
    assert_eq!(
        explicit_header
            .generic_params
            .iter()
            .map(|(name, _)| *name)
            .collect::<Vec<_>>(),
        vec![ustr("I"), ustr("T"), ustr("O")]
    );
    let explicit_for_trait = explicit_header.for_trait.as_ref().unwrap();
    assert_eq!(explicit_for_trait.input_types.len(), 1);
    assert_eq!(
        explicit_for_trait.input_types[0].name.unwrap().0,
        ustr("Self")
    );
    assert_applied_path_is!(
        &explicit_for_trait.input_types[0].ty.0,
        ["ExplicitIterator"],
        [["I"], ["T"], ["O"]]
    );
    assert_eq!(explicit_for_trait.output_types.len(), 1);
    assert_eq!(explicit_for_trait.output_types[0].name.0, ustr("Item"));
    assert_path_is!(&explicit_for_trait.output_types[0].ty.0, ["O"]);

    let specified_multi_input = &module.impls[2];
    assert!(specified_multi_input.generic_params.is_empty());
    let specified_for_trait = specified_multi_input.for_trait.as_ref().unwrap();
    assert_eq!(specified_for_trait.input_types.len(), 2);
    assert!(
        specified_for_trait
            .input_types
            .iter()
            .all(|input| input.name.is_none())
    );
    assert_path_is!(&specified_for_trait.input_types[0].ty.0, ["int"]);
    assert_path_is!(&specified_for_trait.input_types[1].ty.0, ["S"]);
    assert!(specified_for_trait.output_types.is_empty());
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parse_type_def_where_clauses() {
    let src = indoc! { r#"
        struct ZipIterator<L, R, A, B>
        where
            L: Iterator<Item = A>,
            R: Iterator<Item = B>
        {
            left: L,
            right: R,
        }

        enum StreamState<I, T>
        where
            I: Iterator<Item = T>
        {
            Ready(I),
            Done,
        }
    "# };
    let src = join_src(&[map_iterator_type_def_src(), witnessed_type_def_src(), src]);
    let module = parse_module_ast(&src);

    assert_type_def_constraints(
        &module.type_defs[0],
        ["I", "T", "O"],
        [constraint(
            ["Iterator"],
            [unnamed_constraint_input(["I"])],
            [output_binding("Item", ["T"])],
        )],
    );

    assert_type_def_constraints(
        &module.type_defs[1],
        ["Input", "Output"],
        [constraint(
            ["testing", "TestAssoc"],
            [unnamed_constraint_input(["Input"])],
            [output_binding("Output", ["Output"])],
        )],
    );

    assert_type_def_constraints(
        &module.type_defs[2],
        ["L", "R", "A", "B"],
        [
            constraint(
                ["Iterator"],
                [unnamed_constraint_input(["L"])],
                [output_binding("Item", ["A"])],
            ),
            constraint(
                ["Iterator"],
                [unnamed_constraint_input(["R"])],
                [output_binding("Item", ["B"])],
            ),
        ],
    );

    assert_type_def_constraints(
        &module.type_defs[3],
        ["I", "T"],
        [constraint(
            ["Iterator"],
            [unnamed_constraint_input(["I"])],
            [output_binding("Item", ["T"])],
        )],
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parse_multi_parameter_type_def_where_clauses() {
    let module = parse_module_ast(indoc! { r#"
        struct NamedCast<From, To>
        where
            Cast<From = From, To = To>
        {
            value: From,
        }

        struct Convertible<From, To, Via>
        where
            Convert<From = From, To = To |-> Via = Via>
        {
            value: From,
        }

        struct MultiOutput<Left, Right, Combined, Error>
        where
            Combine<Left = Left, Right = Right |-> Output = Combined, Error = Error>
        {
            left: Left,
            right: Right,
        }
    "# });

    assert_type_def_constraints(
        &module.type_defs[0],
        ["From", "To"],
        [constraint(
            ["Cast"],
            [
                named_constraint_input("From", ["From"]),
                named_constraint_input("To", ["To"]),
            ],
            [],
        )],
    );

    assert_type_def_constraints(
        &module.type_defs[1],
        ["From", "To", "Via"],
        [constraint(
            ["Convert"],
            [
                named_constraint_input("From", ["From"]),
                named_constraint_input("To", ["To"]),
            ],
            [output_binding("Via", ["Via"])],
        )],
    );

    assert_type_def_constraints(
        &module.type_defs[2],
        ["Left", "Right", "Combined", "Error"],
        [constraint(
            ["Combine"],
            [
                named_constraint_input("Left", ["Left"]),
                named_constraint_input("Right", ["Right"]),
            ],
            [
                output_binding("Output", ["Combined"]),
                output_binding("Error", ["Error"]),
            ],
        )],
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn invalid_trait_constraint_bindings_report_structured_errors() {
    let mut session = TestSession::new();

    match session
        .fail_compilation("struct Bad<From, To> where Cast<Src = From, To = To> (From)")
        .into_inner()
    {
        CompilationErrorImpl::InvalidTraitConstraint {
            trait_name, kind, ..
        } => {
            assert_eq!(trait_name, "Cast");
            assert_eq!(
                kind,
                InvalidTraitConstraintKind::UnknownInputBinding { name: ustr("Src") }
            );
        }
        other => panic!("expected InvalidTraitConstraint, got {other:?}"),
    }

    match session
        .fail_compilation("struct Bad<From, To> where Cast<From = From, From = To> (From)")
        .into_inner()
    {
        CompilationErrorImpl::InvalidTraitConstraint {
            trait_name, kind, ..
        } => {
            assert_eq!(trait_name, "Cast");
            assert_eq!(
                kind,
                InvalidTraitConstraintKind::DuplicateInputBinding { name: ustr("From") }
            );
        }
        other => panic!("expected InvalidTraitConstraint, got {other:?}"),
    }

    match session
        .fail_compilation("struct Bad<From, To> where Cast<From = From> (From)")
        .into_inner()
    {
        CompilationErrorImpl::InvalidTraitConstraint {
            trait_name, kind, ..
        } => {
            assert_eq!(trait_name, "Cast");
            assert_eq!(
                kind,
                InvalidTraitConstraintKind::MissingInputBindings {
                    names: vec![ustr("To")]
                }
            );
        }
        other => panic!("expected InvalidTraitConstraint, got {other:?}"),
    }

    match session
        .fail_compilation("struct Bad<From, To> where From: Cast<To = To> (From)")
        .into_inner()
    {
        CompilationErrorImpl::InvalidTraitConstraint {
            trait_name, kind, ..
        } => {
            assert_eq!(trait_name, "Cast");
            assert_eq!(
                kind,
                InvalidTraitConstraintKind::ExpectedNamedInputs { expected_count: 2 }
            );
        }
        other => panic!("expected InvalidTraitConstraint, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn user_defined_generic_type_defs_lower_to_type_schemes() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(indoc! { r#"
        enum Option<A> {
            None,
            Some(A),
        }
    "# });

    let option_def = module.get_type_def(ustr("Option")).unwrap();
    assert_eq!(option_def.param_names, vec![ustr("A")]);
    assert_eq!(option_def.shape.ty_quantifiers, vec![TypeVar::new(0)]);
    assert!(option_def.shape.constraints.is_empty());
    let option_shape = option_def.shape_ty().data().clone().into_variant().unwrap();
    assert_eq!(
        option_shape,
        [
            (ustr("None"), Type::unit()),
            (ustr("Some"), Type::tuple([Type::variable_id(0)])),
        ]
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_named_type_from_user_definition() {
    let mut session = TestSession::new();

    let make_some_src = join_src(&[
        option_type_def_src(),
        indoc! { r#"
            fn make_some() {
                Option::Some("hello")
            }
        "# },
    ]);
    assert_compiled_fn_type(
        &mut session,
        &make_some_src,
        "make_some",
        "() -> Option<string>",
    );

    let unwrap_or_zero_src = join_src(&[
        option_type_def_src(),
        indoc! { r#"
            fn unwrap_or_zero(value) {
                match value {
                    Some(inner) => inner,
                    None => 0,
                }
            }

            unwrap_or_zero(Option::Some(41))
        "# },
    ]);
    assert_eq!(session.run(&unwrap_or_zero_src), int(41));

    let annotated_value_src = join_src(&[
        option_type_def_src(),
        indoc! { r#"
            let value: Option<int> = Option::Some(41);
            match value {
                Some(inner) => inner,
                None => 0,
            }
        "# },
    ]);
    assert_eq!(session.run(&annotated_value_src), int(41));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn constrained_named_type_from_user_definition() {
    let mut session = TestSession::new();

    let make_bool_src = join_src(&[
        witnessed_type_def_src(),
        indoc! { r#"
            fn make_bool() {
                Witnessed(true)
            }
        "# },
    ]);
    assert_compiled_fn_type(
        &mut session,
        &make_bool_src,
        "make_bool",
        "() -> Witnessed<bool, string>",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn multi_parameter_trait_constraints_from_user_definition() {
    let mut session = TestSession::new();

    let make_cast_box = session.compile_and_get_fn_def(
        indoc! { r#"
            struct CastBox<From, To>
            where
                Cast<From = From, To = To>
            (From)

            fn make_cast_box() {
                let value: CastBox<int, float> = CastBox(1);
                value
            }
        "# },
        "make_cast_box",
    );
    assert!(make_cast_box.ty_scheme.ty_quantifiers.is_empty());
    assert_eq!(
        make_cast_box
            .ty_scheme
            .ty()
            .format_with(&session.std_module_env())
            .to_string(),
        "() -> CastBox<int, float>"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_struct_patterns_from_user_definition() {
    let mut session = TestSession::new();

    assert_eq!(
        session.run(indoc! { r#"
            struct Box<T>(T)

            let Box(value) = Box(41);
            value
        "# }),
        int(41)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn map_iterator_named_type_from_user_definition() {
    let mut session = TestSession::new();

    let build_map_iterator_src = join_src(&[
        map_iterator_type_def_src(),
        map_iterator_impl_src(),
        indoc! { r#"
            fn build_map_iterator() {
                MapIterator {
                    iterator: iter(["a", "bc"]),
                    mapper: |x| len(x),
                }
            }
        "# },
    ]);
    assert_compiled_fn_type(
        &mut session,
        &build_map_iterator_src,
        "build_map_iterator",
        "() -> MapIterator<array_iterator<string>, string, int>",
    );

    let run_map_iterator_src = join_src(&[
        &build_map_iterator_src,
        indoc! { r#"
            let mut total = 0;
            for score in build_map_iterator() {
                total += score;
            };
            total
        "# },
    ]);
    assert_eq!(session.run(&run_map_iterator_src), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_trait_impl_with_explicit_binders_for_user_defined_map_iterator() {
    let mut session = TestSession::new();

    let build_map_iterator_src = join_src(&[
        map_iterator_type_def_src(),
        map_iterator_impl_with_explicit_binders_src(),
        indoc! { r#"
            fn build_map_iterator() {
                MapIterator {
                    iterator: iter(["a", "bc"]),
                    mapper: |x| len(x),
                }
            }
        "# },
    ]);
    assert_compiled_fn_type(
        &mut session,
        &build_map_iterator_src,
        "build_map_iterator",
        "() -> MapIterator<array_iterator<string>, string, int>",
    );

    let run_map_iterator_src = join_src(&[
        &build_map_iterator_src,
        indoc! { r#"
            let mut total = 0;
            for score in build_map_iterator() {
                total += score;
            };
            total
        "# },
    ]);
    assert_eq!(session.run(&run_map_iterator_src), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_trait_impl_with_explicit_outputs_for_user_defined_map_iterator() {
    let mut session = TestSession::new();

    let build_map_iterator_src = join_src(&[
        map_iterator_type_def_src(),
        map_iterator_impl_with_explicit_outputs_src(),
        indoc! { r#"
            fn build_map_iterator() {
                MapIterator {
                    iterator: iter(["a", "bc"]),
                    mapper: |x| len(x),
                }
            }
        "# },
    ]);
    assert_compiled_fn_type(
        &mut session,
        &build_map_iterator_src,
        "build_map_iterator",
        "() -> MapIterator<array_iterator<string>, string, int>",
    );

    let run_map_iterator_src = join_src(&[
        &build_map_iterator_src,
        indoc! { r#"
            let mut total = 0;
            for score in build_map_iterator() {
                total += score;
            };
            total
        "# },
    ]);
    assert_eq!(session.run(&run_map_iterator_src), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn grammar_extractor_covers_advanced_generic_type_syntax() {
    let mut session = TestSession::new();

    assert_eq!(
        session.run(indoc! { r#"
            enum Option<T> {
                None,
                Some(T),
            }

            struct Wrapper<T>(T)

            struct MapIterator<I, T, O>
            where
                I: Iterator<Item = T>
            {
                iterator: I,
                mapper: (T) -> O,
            }

            enum StreamState<I, T>
            where
                I: Iterator<Item = T>
            {
                Ready(I),
                Done,
            }

            impl<T> Cast for <From = T, To = Wrapper<T>> {
                fn cast(self) -> Wrapper<T> {
                    Wrapper(self)
                }
            }

            impl<I, T, O> Iterator for <Self = MapIterator<I, T, O> |-> Item = O> {
                fn next(it: &mut MapIterator<I, T, O>) -> None | Some(O) {
                    match next(it.iterator) {
                        Some(data) => Some(it.mapper(data)),
                        None => None,
                    }
                }
            }

            let wrapped: Wrapper<int> = cast(2);
            let state = StreamState::Ready(iter([wrapped.0, 40]));
            let result: Option<int> = match state {
                Ready(iterator) => {
                    let mut total = 0;
                    let values = MapIterator {
                        iterator,
                        mapper: |x| x + 1,
                    };
                    for value in values {
                        total += value;
                    };
                    Option::Some(total)
                },
                Done => Option::None,
            };

            match result {
                Some(value) => value,
                None => 0,
            }
        "# }),
        int(44)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_trait_impl_for_user_defined_zip_iterator() {
    let mut session = TestSession::new();

    let build_zip_iterator_src = join_src(&[
        zip_iterator_type_def_src(),
        zip_iterator_impl_src(),
        indoc! { r#"
            fn build_zip_iterator() {
                ZipIterator {
                    left: iter([1 as int, 20 as int]),
                    right: iter(["a", "bbb"]),
                }
            }
        "# },
    ]);
    assert_compiled_fn_type(
        &mut session,
        &build_zip_iterator_src,
        "build_zip_iterator",
        "() -> ZipIterator<array_iterator<int>, array_iterator<string>, int, string>",
    );

    let run_zip_iterator_src = join_src(&[
        &build_zip_iterator_src,
        indoc! { r#"
            fn pair_score(pair) {
                pair.0 + len(pair.1)
            }

            let mut total = 0;
            for score in build_zip_iterator() {
                total += pair_score(score)
            };
            total
        "# },
    ]);
    assert_eq!(session.run(&run_zip_iterator_src), int(25));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compiled_impl_headers_use_source_syntax() {
    let mut session = TestSession::new();

    let rendered = format_compiled_module(
        &mut session,
        &join_src(&[
            indoc! { r#"
                struct S(string)

                impl Ord for S {
                    fn cmp(self, other: S) {
                        cmp(len(self.0), len(other.0))
                    }
                }
            "# },
            map_iterator_type_def_src(),
            map_iterator_impl_with_explicit_outputs_src(),
        ]),
    );

    assert!(
        rendered.contains("impl Ord for S ("),
        "expected unary-input impl sugar, got:\n{rendered}"
    );
    assert!(
        rendered.contains("impl<A, B, C> Iterator for <Self = MapIterator<A, B, C> |-> Item = C>"),
        "expected explicit output impl header, got:\n{rendered}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn compiled_type_defs_include_doc_comments() {
    let mut session = TestSession::new();

    let rendered = format_compiled_module(
        &mut session,
        indoc! { r#"
            /// An optional value.
            enum Option<T> {
                Some(T),
                None,
            }

            /// Stores one value.
            struct Box<T>(T)
        "# },
    );

    assert!(
        rendered.contains("/// An optional value.\nenum Option<T>"),
        "expected enum doc comments in module formatting, got:\n{rendered}"
    );
    assert!(
        rendered.contains("/// Stores one value.\nstruct Box<T>"),
        "expected struct doc comments in module formatting, got:\n{rendered}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn pretty_print_user_defined_generic_enum_values() {
    let mut session = TestSession::new();
    let src = join_src(&[
        option_type_def_src(),
        indoc! { r#"
            Option::Some(32)
        "# },
    ]);

    assert_eq!(
        run_and_pretty_format(&mut session, &src),
        "Option::Some (32)"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_named_type_from_rust_definition() {
    let mut session = TestSession::new();

    let make_some = session.compile_and_get_fn_def(
        indoc! { r#"
            fn make_some() {
                testing::Option::Some("hello")
            }
        "# },
        "make_some",
    );
    assert!(
        make_some.ty_scheme.ty_quantifiers.is_empty(),
        "constructor should infer a concrete named type, got {}",
        make_some
            .ty_scheme
            .display_rust_style(&session.std_module_env()),
    );
    assert_eq!(
        make_some
            .ty_scheme
            .ty()
            .format_with(&session.std_module_env())
            .to_string(),
        "() -> Option<string>"
    );

    assert_eq!(
        session.run(indoc! { r#"
            fn unwrap_or_zero(value) {
                match value {
                    Some(inner) => inner,
                    None => 0,
                }
            }

            unwrap_or_zero(testing::Option::Some(41))
        "# }),
        int(41)
    );
    assert_eq!(
        session.run(indoc! { r#"
            fn unwrap_or_zero(value) {
                match value {
                    Some(inner) => inner,
                    None => 0,
                }
            }

            unwrap_or_zero(testing::Option::None)
        "# }),
        int(0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn constrained_named_type_from_rust_definition() {
    let mut session = TestSession::new();

    let make_string = session.compile_and_get_fn_def(
        indoc! { r#"
            fn make_string() {
                testing::Witnessed("hello")
            }
        "# },
        "make_string",
    );
    assert!(
        make_string.ty_scheme.ty_quantifiers.is_empty(),
        "constraint-instantiated constructor should not stay polymorphic, got {}",
        make_string
            .ty_scheme
            .display_rust_style(&session.std_module_env()),
    );
    assert_eq!(
        make_string
            .ty_scheme
            .ty()
            .format_with(&session.std_module_env())
            .to_string(),
        "() -> Witnessed<string, int>"
    );

    let make_bool = session.compile_and_get_fn_def(
        indoc! { r#"
            fn make_bool() {
                testing::Witnessed(true)
            }
        "# },
        "make_bool",
    );
    assert!(
        make_bool.ty_scheme.ty_quantifiers.is_empty(),
        "constraint-instantiated constructor should not stay polymorphic, got {}",
        make_bool
            .ty_scheme
            .display_rust_style(&session.std_module_env()),
    );
    assert_eq!(
        make_bool
            .ty_scheme
            .ty()
            .format_with(&session.std_module_env())
            .to_string(),
        "() -> Witnessed<bool, string>"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn map_iterator_named_type_from_rust_definition() {
    let mut session = TestSession::new();

    let build_map_iterator = session.compile_and_get_fn_def(
        indoc! { r#"
            fn build_map_iterator() {
                testing::MapIterator {
                    iterator: array_iter(["a", "bc"]),
                    mapper: |x| len(x),
                }
            }
        "# },
        "build_map_iterator",
    );
    assert!(
        build_map_iterator.ty_scheme.ty_quantifiers.is_empty(),
        "constructor should infer a concrete named type, got {}",
        build_map_iterator
            .ty_scheme
            .display_rust_style(&session.std_module_env()),
    );
    assert_eq!(
        build_map_iterator
            .ty_scheme
            .ty()
            .format_with(&session.std_module_env())
            .to_string(),
        "() -> MapIterator<array_iterator<string>, string, int>"
    );

    assert_eq!(
        session.run(indoc! { r#"
            let it = testing::MapIterator {
                iterator: array_iter(["a", "bc"]),
                mapper: |x| len(x),
            };
            it.mapper("abc")
        "# }),
        int(3)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_record_enum_values() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            enum Message {
                Quit,
                Move { x: int, y: int },
            }

            Message::Move { y: 30 + 10, x: 30 }
        "# }),
        Value::raw_variant(ustr("Move"), Value::tuple([int(30), int(40)]))
    );

    let mod_src = indoc! { "
        enum Message {
            Quit,
            Flag { v0: bool, v1: bool }
        }
    " };
    assert_eq!(
        session.run(&format!(
            "{mod_src} Message::Flag {{ v1: false, v0: true }}"
        )),
        Value::raw_variant(ustr("Flag"), Value::tuple([bool(true), bool(false)]))
    );

    assert_eq!(
        *session
            .fail_compilation(&format!(r#"{mod_src} Message::Flag {{ v0: true }}"#))
            .as_missing_struct_field()
            .unwrap()
            .1,
        "v1"
    );
    assert_eq!(
        *session
            .fail_compilation(&format!(
                r#"{mod_src} Message::Flag {{ v1: false, v0: true, v2: false }}"#
            ))
            .as_invalid_struct_field()
            .unwrap()
            .1,
        "v2"
    );
    session
        .fail_compilation(&format!(
            r#"{mod_src} Message::Flag {{ v1: false, v0: 1.0 }}"#
        ))
        .expect_type_mismatch("float", "bool");

    // shorthand syntax when variable name matches field name
    session.run(&format!(
        r#"{mod_src} let v0 = true; let v1 = false; Message::Flag {{ v0, v1 }}"#
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_tuple_enum_values() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            enum Player {
                Basic(string),
                Positioned(int, int),
            }

            Player::Positioned(30 + 10, 0)
        "# }),
        Value::raw_variant(ustr("Positioned"), Value::tuple([int(40), int(0)]))
    );

    let mod_src = indoc! { "
        enum Player {
            Basic(string),
            State(bool)
        }
    " };
    assert_eq!(
        session.run(&format!(r#"{mod_src} Player::Basic("ok")"#)),
        Value::raw_variant(ustr("Basic"), Value::tuple([string("ok")]))
    );
    assert_eq!(
        session.run(&format!("{mod_src} Player::State(false)")),
        Value::raw_variant(ustr("State"), Value::tuple([bool(false)]))
    );
    session
        .fail_compilation(&format!("{mod_src} Player::State(1.0)"))
        .expect_type_mismatch("float", "bool");
    session
        .fail_compilation(&format!("{mod_src} Player::State()"))
        .expect_wrong_number_of_arguments(1, 0);
    session
        .fail_compilation(&format!("{mod_src} Player::State(true, 1.0)"))
        .expect_wrong_number_of_arguments(1, 2);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_mix_enum_values() {
    let mut session = TestSession::new();
    let mod_src = indoc! { r#"
        enum Message {
            Quit,
            Move { x: int, y: int },
            Write(string),
            ChangeColor(int, int, int),
            Callback((int) -> int)
        }
    "# };

    assert_eq!(
        session.run(&format!("{mod_src} Message::Quit")),
        Value::raw_variant(ustr("Quit"), Value::unit())
    );

    assert_eq!(
        session.run(&format!("{mod_src} Message::Move {{ x: 30, y: 40 }}")),
        Value::raw_variant(ustr("Move"), Value::tuple(vec![int(30), int(40)]))
    );

    assert_eq!(
        session.run(&format!(r#"{mod_src} Message::Write("Hello, world!")"#)),
        Value::raw_variant(ustr("Write"), Value::tuple(vec![string("Hello, world!")])),
    );

    assert_eq!(
        session.run(&format!("{mod_src} Message::ChangeColor(255, 0, 0)")),
        Value::raw_variant(
            ustr("ChangeColor"),
            Value::tuple(vec![int(255), int(0), int(0)])
        )
    );

    let value = session.run(&format!("{mod_src} Message::Callback(|x| x + 1)"));
    assert_eq!(value.as_variant().unwrap().tag, ustr("Callback"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn enum_projections() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            enum Action {
                Quit,
                Jump(float),
                Move { x: float, y: float },
            }

            let f = |a| match a {
                Quit => 0.0,
                Jump(h) => h,
                Move { y, x } => x - y,
            };

            f(Action::Move { x: 30.0, y: 40.0 }) + f(Action::Jump(5.0)) + f(Action::Quit)
        "# }),
        float(-5.0)
    );
    assert_eq!(
        session.run(indoc! { r#"
            enum Action {
                Move1 { x: float, y: float },
                Move2 { x: float, y: float },
            }

            let f = |a| match a {
                Move1 { x, .. } => x,
                Move2 { y, .. } => -y,
            };

            f(Action::Move1 { x: 30.0, y: 40.0 }) + f(Action::Move2 { x: 30.0, y: 40.0 })
        "# }),
        float(-10.0)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn define_struct_types() {
    let mut session = TestSession::new();
    let mod_src = indoc! { r#"
        // Empty struct
        struct Empty {}

        // Struct with fields
        struct Person {
            name: string,
            age: int,
            is_active: bool
        }

        // Struct with fields
        struct Person2 {
            name: string,
            age: int,
            is_active: bool,
        }

        // Newtype struct
        struct Email(string)

        // Tuple struct
        struct Point(int, int)

        // Tuple struct
        struct Point2(int, int,)

        // Struct with function pointer
        struct Callable {
            callback: (string) -> ()
        }
    "# };
    let module_id = session.compile(mod_src).module_id;
    let module = session.session().expect_fresh_module(module_id);

    let empty_type = module.get_type_def(ustr("Empty")).unwrap();
    assert_eq!(empty_type.name, ustr("Empty"));
    let empty_type_shape = empty_type.shape_ty().data().as_record().unwrap().clone();
    assert_eq!(empty_type_shape, vec![]);

    let person_type = module.get_type_def(ustr("Person")).unwrap();
    assert_eq!(person_type.name, ustr("Person"));
    let person_type_shape = person_type.shape_ty().data().as_record().unwrap().clone();
    assert_eq!(
        person_type_shape,
        vec![
            (ustr("age"), int_type()),
            (ustr("is_active"), bool_type()),
            (ustr("name"), string_type()),
        ]
    );

    let person2_type = module.get_type_def(ustr("Person2")).unwrap();
    assert_eq!(person2_type.name, ustr("Person2"));
    let person2_type_shape = person2_type.shape_ty().data().as_record().unwrap().clone();
    assert_eq!(person2_type_shape, person_type_shape);

    let email_type = module.get_type_def(ustr("Email")).unwrap();
    assert_eq!(email_type.name, ustr("Email"));
    let email_type_shape = email_type.shape_ty().data().as_tuple().unwrap().clone();
    assert_eq!(email_type_shape, vec![string_type()]);

    let point_type = module.get_type_def(ustr("Point")).unwrap();
    assert_eq!(point_type.name, ustr("Point"));
    let point_type_shape = point_type.shape_ty().data().as_tuple().unwrap().clone();
    assert_eq!(point_type_shape, vec![int_type(), int_type()]);

    let point2_type = module.get_type_def(ustr("Point2")).unwrap();
    assert_eq!(point2_type.name, ustr("Point2"));
    let point2_type_shape = point2_type.shape_ty().data().as_tuple().unwrap().clone();
    assert_eq!(point2_type_shape, vec![int_type(), int_type()]);

    let callable_type = module.get_type_def(ustr("Callable")).unwrap();
    assert_eq!(callable_type.name, ustr("Callable"));
    let callable_type_shape = callable_type.shape_ty().data().as_record().unwrap().clone();
    assert_eq!(
        callable_type_shape,
        vec![(
            ustr("callback"),
            Type::function_by_val([string_type()], Type::unit())
        ),]
    );

    assert_eq!(
        session
            .fail_compilation("struct Invalid { a: int, a: int }")
            .into_inner()
            .into_duplicated_field()
            .unwrap()
            .3,
        DuplicatedFieldContext::Struct
    );
    assert_eq!(
        session
            .fail_compilation("struct Invalid { a: int, b: string, a: float }")
            .into_inner()
            .into_duplicated_field()
            .unwrap()
            .3,
        DuplicatedFieldContext::Struct
    );
    assert_eq!(
        session
            .fail_compilation("struct Invalid { a: int, b: { a: int, a: float } }")
            .into_inner()
            .into_duplicated_field()
            .unwrap()
            .3,
        DuplicatedFieldContext::Record
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_record_struct_values() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            struct Person {
                name: string,
                age: int,
                is_active: bool
            }

            Person {
                name: "Alice",
                age: 20 + 10,
                is_active: true
            }
        "# }),
        Value::tuple(vec![int(30), bool(true), string("Alice")])
    );

    let mod_src = "struct Person { name: string, is_active: bool }";
    assert_eq!(
        session.run(&format!(
            r#"{mod_src} Person {{ name: "Alice", is_active: true }}"#
        )),
        Value::tuple(vec![bool(true), string("Alice")])
    );

    assert_eq!(
        *session
            .fail_compilation(&format!(r#"{mod_src} Person {{ name: "Alice" }}"#))
            .as_missing_struct_field()
            .unwrap()
            .1,
        "is_active"
    );
    assert_eq!(
        *session
            .fail_compilation(&format!(
                r#"{mod_src} Person {{ name: "Alice", is_active: true, age: 20.2 }}"#
            ))
            .as_invalid_struct_field()
            .unwrap()
            .1,
        "age"
    );
    session
        .fail_compilation(&format!(
            r#"{mod_src} Person {{ name: "Alice", is_active: 1.2 }}"#
        ))
        .expect_type_mismatch("float", "bool");

    // shorthand syntax when variable name matches field name
    session.run(&format!(
        r#"{mod_src} let name = "Alice"; let is_active = true; Person {{ name, is_active }}"#
    ));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_empty_struct_values() {
    let mut session = TestSession::new();
    assert_eq!(session.run(r#"struct Empty; Empty"#), Value::unit());
    assert_eq!(
        session.run(r#"struct Empty2 {} Empty2 {}"#),
        Value::empty_tuple()
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn create_tuple_struct_values() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(r#"struct Email(string) Email(string_concat("h", "i"))"#),
        Value::tuple(vec![string("hi")])
    );
    assert_eq!(
        session.run(r#"struct Email(string) Email("hi")"#),
        Value::tuple(vec![string("hi")])
    );

    assert_eq!(
        session.run(r#"struct Email((string, )) Email((string_concat("h", "i"), ))"#),
        Value::tuple(vec![Value::tuple(vec![string("hi")])])
    );
    assert_eq!(
        session.run(r#"struct Email((string, )) Email(("hi", ))"#),
        Value::tuple(vec![Value::tuple(vec![string("hi")])])
    );

    assert_eq!(
        session.run(r#"struct Point(int, int) Point(1 + 0, 2)"#),
        Value::tuple(vec![int(1), int(2)])
    );
    assert_eq!(
        session.run(r#"struct Point(float, float) Point(1.0, 2.0)"#),
        Value::tuple(vec![float(1.0), float(2.0)])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn struct_projections() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(r#"struct Email(string) Email("hi").0"#),
        string("hi")
    );

    assert_eq!(
        session.run(r#"struct Person(string, int) Person("John", 30).0"#),
        string("John")
    );

    assert_eq!(
        session.run(
            r#"struct Person { name: string, age: int } Person { name: "John", age: 30 }.name"#
        ),
        string("John")
    );

    assert_eq!(
        session.run(r#"struct Age(int) struct Person(string, Age) Person("John", Age(30)).0"#),
        string("John")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn struct_destructuring() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            struct Pair(int, int)
            let Pair(x, y) = Pair(1, 2);
            (x, y)
        "# }),
        Value::tuple([int(1), int(2)])
    );
    assert_eq!(
        session.run(indoc! { r#"
            struct Vec3(int, int, int)
            let Vec3(x, ..) = Vec3(1, 2, 3);
            x
        "# }),
        int(1)
    );
    assert_eq!(
        session.run(indoc! { r#"
            struct Point { x: int, y: int, z: int }
            let Point { x: mut horizontal, mut y, .. } = Point { x: 1, y: 2, z: 3 };
            horizontal = horizontal + y;
            y = y + 10;
            horizontal + y
        "# }),
        int(15)
    );
    assert_eq!(
        session.run(indoc! { r#"
            struct Point { x: int, y: int }
            let ((feet, inches), Point { x, y }) = ((3, 10), Point { x: 3, y: -10 });
            (feet, inches, x, y)
        "# }),
        Value::tuple([int(3), int(10), int(3), int(-10)])
    );

    assert_eq!(
        *session
            .fail_compilation(indoc! { r#"
                struct Point { x: int, y: int, z: int }
                let Point { x, y } = Point { x: 1, y: 2, z: 3 };
                x
            "# })
            .as_missing_struct_field()
            .unwrap()
            .1,
        "z"
    );
    assert_eq!(
        *session
            .fail_compilation(indoc! { r#"
                struct Point { x: int, y: int, z: int }
                let Point { x, w, .. } = Point { x: 1, y: 2, z: 3 };
                x
            "# })
            .as_invalid_struct_field()
            .unwrap()
            .1,
        "w"
    );
    session
        .fail_compilation(indoc! { r#"
            struct Vec3(int, int, int)
            let Vec3(x, y) = Vec3(1, 2, 3);
            x
        "# })
        .expect_wrong_number_of_arguments(3, 2);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn projections_through_repr_in_match() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            struct S(bool)
            let s = S(true);
            match s {
                (true,) => 1,
                (false,) => 2
            }
        "# }),
        int(1)
    );
    assert_eq!(
        session.run(indoc! { r#"
            struct S { x: bool }
            let s = S { x: true };
            match s {
                { x: true } => 1,
                { x: false } => 2
            }
        "# }),
        int(1)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn same_module_references() {
    let mut session = TestSession::new();
    assert_eq!(
        session.run(indoc! { r#"
            struct Age(int)
            struct Name(string)
            struct Person { name: Name, age: Age }

            fn get_name(person: Person) { person.name }
            fn get_age(person: Person) { person.age }
            fn get_data(person: Person) { (get_name(person).0, get_age(person).0) }

            get_data(Person { name: Name("John"), age: Age(30) })
        "# }),
        tuple!(string("John"), int(30))
    );

    assert_eq!(
        session
            .fail_compilation("struct A { a: A }")
            .into_inner()
            .into_unsupported()
            .unwrap()
            .1,
        "Self-referential type paths are not supported, but `A` refers to itself"
    );
    assert_eq!(
        session
            .fail_compilation("enum A { X(A) }")
            .into_inner()
            .into_unsupported()
            .unwrap()
            .1,
        "Self-referential type paths are not supported, but `A` refers to itself"
    );
    assert_eq!(
        session
            .fail_compilation("enum A { X(B) } struct B { a: A }")
            .into_inner()
            .into_unsupported()
            .unwrap()
            .1,
        "Cyclic types are not supported, but `B` indirectly refers to itself"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_annotations() {
    let mut session = TestSession::new();
    let mod_src = indoc! { r#"
        struct Age(int)
        struct Person1 { age: Age }
        struct Person2 { age: Age }

        fn age(d) { d.age.0 }
        fn age1(d: Person1) { d.age.0 }
    "# };
    assert_eq!(
        session.run(&format!(r"{mod_src} age(Person1 {{ age: Age(30) }})")),
        int(30)
    );
    assert_eq!(
        session.run(&format!(r"{mod_src} age1(Person1 {{ age: Age(30) }})")),
        int(30)
    );
    assert_eq!(
        session.run(&format!(r"{mod_src} age(Person2 {{ age: Age(30) }})")),
        int(30)
    );
    assert_eq!(
        session.run(&format!(r"{mod_src} age({{ age: Age(30) }})")),
        int(30)
    );
    let error = session
        .fail_compilation(&format!(r"{mod_src} age1(Person2 {{ age: Age(30) }})"))
        .into_inner()
        .into_named_type_mismatch()
        .unwrap();
    assert_eq!(
        (error.0.0.as_str(), error.2.0.as_str()),
        ("Person2", "Person1")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn double_newtype() {
    let mut session = TestSession::new();
    let mod_src = indoc! { r#"
        struct Person(string)
        struct Creature(Person)
    "# };
    assert_eq!(
        session.run(&format!(r#"{mod_src} Creature(Person("Alice")).0.0"#)),
        string("Alice")
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn attributes() {
    let mut session = TestSession::new();
    // Helper to get attributes of a type definition
    let mut attrs = |code, name| {
        session
            .compile_and_get_module(code)
            .get_type_def(ustr(name))
            .unwrap()
            .attributes
            .clone()
    };

    // No attributes by default
    let attributes = attrs(
        indoc! { r#"
            enum SimpleColor { Red, Green, Blue }
        "# },
        "SimpleColor",
    );
    assert!(attributes.is_empty());

    // Flag attribute
    let attributes = attrs(
        indoc! { r#"
            #[flag]
            enum SimpleColor { Red, Green, Blue }
        "# },
        "SimpleColor",
    );
    assert_eq!(attributes.len(), 1);
    assert_eq!(attributes[0].path.0, ustr("flag"));

    // Multiple attributes
    let attributes = attrs(
        indoc! { r#"
            #[flag]
            #[path(name = "value")]
            #[multi(name1 = "value1", name2 = "value2")]
            enum SimpleColor { Red, Green, Blue }
        "# },
        "SimpleColor",
    );
    assert_eq!(attributes.len(), 3);
    assert_eq!(attributes[0].path.0, ustr("flag"));
    assert_eq!(attributes[1].path.0, ustr("path"));
    assert_eq!(attributes[1].items.len(), 1);
    assert_eq!(
        attributes[1].items[0].as_name_value().unwrap().0.0,
        ustr("name")
    );
    assert_eq!(
        attributes[1].items[0].as_name_value().unwrap().1.0,
        ustr("value")
    );
    assert_eq!(attributes[2].path.0, ustr("multi"));
    assert_eq!(attributes[2].items.len(), 2);
    let item1 = attributes[2].items[0].as_name_value().unwrap();
    assert_eq!(item1.0.0, ustr("name1"));
    assert_eq!(item1.1.0, ustr("value1"));
    let item2 = attributes[2].items[1].as_name_value().unwrap();
    assert_eq!(item2.0.0, ustr("name2"));
    assert_eq!(item2.1.0, ustr("value2"));

    // Also works on structs
    let attributes = attrs(
        indoc! { r#"
            #[flag]
            #[path(name = "value")]
            #[multi(name1 = "value1", name2 = "value2")]
            struct Person {
                name: string,
                age: int,
                is_active: bool
            }
        "# },
        "Person",
    );
    assert_eq!(attributes.len(), 3);
    assert_eq!(attributes[0].path.0, ustr("flag"));
    assert_eq!(attributes[1].path.0, ustr("path"));
    assert_eq!(attributes[1].items.len(), 1);
    assert_eq!(
        attributes[1].items[0].as_name_value().unwrap().0.0,
        ustr("name")
    );
    assert_eq!(
        attributes[1].items[0].as_name_value().unwrap().1.0,
        ustr("value")
    );
    assert_eq!(attributes[2].path.0, ustr("multi"));
    assert_eq!(attributes[2].items.len(), 2);
    let item1 = attributes[2].items[0].as_name_value().unwrap();
    assert_eq!(item1.0.0, ustr("name1"));
    assert_eq!(item1.1.0, ustr("value1"));
    let item2 = attributes[2].items[1].as_name_value().unwrap();
    assert_eq!(item2.0.0, ustr("name2"));
    assert_eq!(item2.1.0, ustr("value2"));
}
