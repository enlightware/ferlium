// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use test_log::test;

use ferlium::{
    compiler::error::{
        CompilationErrorImpl, InvalidDefaultMethodKind, InvalidTraitAssociatedConstImplKind,
        InvalidTraitDefinitionKind,
    },
    format::FormatWith,
    hir::{
        ENodeArena, ENodeId, NodeKind,
        function::{ArgConvention, CallableDefinition, Function},
        native_functions::NativeFnR,
        value::LiteralValue,
    },
    module::{Module, ModuleId, Path, TraitDictionaryEntry, TraitId},
    types::{
        effects::{PrimitiveEffect, effect, no_effects},
        r#trait::{
            Trait, TraitAssociatedConst, TraitAssociatedConstIndex, TraitDictionaryEntryIndex,
            TraitMethodIndex,
        },
        r#type::{FnType, Type, TypeVar},
    },
};
use indoc::indoc;
use ustr::ustr;

use crate::harness::{TestSession, int, string};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn user_defined_trait_impls_are_callable() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            trait Double<Self> {
                fn double(value: Self) -> Self;
            }

            impl Double for int {
                fn double(value: int) -> int {
                    value * 2
                }
            }

            double(21)
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn user_defined_trait_methods_are_callable_through_trait_path() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            trait Double<Self> {
                fn double(value: Self) -> Self;
            }

            impl Double for int {
                fn double(value: int) -> int {
                    value * 2
                }
            }

            Double::double(21)
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn functions_shadow_unqualified_trait_methods() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            trait Pick<Self> {
                fn pick(value: Self) -> int;
            }

            impl Pick for int {
                fn pick(value: int) -> int {
                    1
                }
            }

            fn pick(value: int) -> int {
                value + 41
            }

            pick(1) * 10 + Pick::pick(1)
        "#}),
        int(421)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn unqualified_trait_method_ambiguity_is_an_error() {
    let mut session = TestSession::new();
    let err = session
        .fail_compilation(indoc! {r#"
            trait Left<Self> {
                fn pick(value: Self) -> int;
            }

            trait Right<Self> {
                fn pick(value: Self) -> int;
            }

            impl Left for int {
                fn pick(value: int) -> int {
                    1
                }
            }

            impl Right for int {
                fn pick(value: int) -> int {
                    2
                }
            }

            pick(0)
        "#})
        .into_inner();

    match err {
        CompilationErrorImpl::AmbiguousTraitMethod {
            method_name,
            trait_refs,
            ..
        } => {
            assert_eq!(method_name, ustr("pick"));
            assert_eq!(trait_refs.len(), 2);
            assert!(trait_refs.iter().any(|name| name == "Left"));
            assert!(trait_refs.iter().any(|name| name == "Right"));
        }
        other => panic!("expected AmbiguousTraitMethod, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn std_trait_methods_are_first_class_values() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            fn f1(a) {
                let my_f = add;
                my_f(a, a)
            }

            f1(21)
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn first_class_trait_methods_can_be_passed_as_arguments() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            fn apply2(f, left, right) {
                f(left, right)
            }

            apply2(add, 20, 22)
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn a_call_site_records_how_it_instantiated_its_callee() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(indoc! {r#"
        fn twice_it<T>(x: T) -> T
        where
            T: Num,
            T: Value
        {
            x + x
        }

        fn concrete(n: int) -> int { twice_it(n) }

        fn forwarding<U>(y: U) -> U
        where
            U: Num,
            U: Value
        {
            twice_it(y)
        }

        concrete(21)
    "#});

    // The instantiation is recorded per call site, in the type environment of the function
    // containing it — so a concrete caller records a concrete type, while a generic caller records
    // its *own* quantifier. That second case is what lets specialization cascade: instantiating the
    // outer function rewrites the inner call's recorded argument along with everything else.
    // Collected before rendering: the module borrow has to end before the session can hand out a
    // `ModuleEnv`, and a `Type` is a cheap interned handle.
    let instantiations: Vec<Vec<Type>> = module
        .hir_arena
        .iter()
        .filter_map(|(_, node)| match &node.kind {
            NodeKind::StaticApply(app) if !app.inst_data.ty_args.is_empty() => {
                Some(app.inst_data.ty_args.clone())
            }
            _ => None,
        })
        .collect();

    let env = session.session().module_env();
    let recorded: Vec<String> = instantiations
        .iter()
        .map(|ty_args| {
            ty_args
                .iter()
                .map(|ty| ty.format_with(&env).to_string())
                .collect::<Vec<_>>()
                .join(", ")
        })
        .collect();

    assert!(
        recorded.iter().any(|args| args == "int"),
        "`concrete` calls `twice_it` at int, so that call must record `int`; recorded: {recorded:?}"
    );
    // Rendered `A` rather than the source's `U`: generalization normalizes a function's quantifiers,
    // so the recorded argument is `forwarding`'s first quantifier under its canonical name.
    assert!(
        recorded.iter().any(|args| args == "A"),
        "`forwarding` calls `twice_it` at its own quantifier, so that call must record a type \
         variable; recorded: {recorded:?}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_trait_method_function_argument_keeps_source_place_passing() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(indoc! {r#"
        trait Describe<Self> {
            fn describe(value: Self) -> int;
        }

        struct Probe(int)

        impl Describe for Probe {
            fn describe(value: Probe) -> int {
                value.0
            }
        }

        fn apply<T>(f: (T) -> int, value: T) -> int
        where
            T: Value
        {
            f(value)
        }

        fn run<T>(value: T) -> int
        where
            T: Describe,
            T: Value
        {
            apply(describe, value)
        }

        run(Probe(42))
    "#});

    let method_locals = module
        .hir_arena
        .iter()
        .filter_map(|(_, node)| {
            if let NodeKind::StoreLocal(store) = &node.kind
                && store_value_materializes_dictionary_method(&module.hir_arena, store.value)
            {
                Some(store.id)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    let apply = module.get_local_function_id(ustr("apply")).unwrap();
    let mut saw_let_local_arg = false;
    for (_, node) in module.hir_arena.iter() {
        let NodeKind::StaticApply(app) = &node.kind else {
            continue;
        };
        if app.function.module != module.module_id() || app.function.function != apply {
            continue;
        }
        let argument = app.arguments.first().unwrap();
        // Materialization is scoped in an argument block. Check its final place read and the
        // exact local holding the method, not an unrelated generated string/hash call.
        let value = match &module.hir_arena[argument.value].kind {
            NodeKind::Block(block) => *block.body.last().unwrap(),
            _ => argument.value,
        };
        saw_let_local_arg |= argument.passing == ArgConvention::Let
            && matches!(&module.hir_arena[value].kind, NodeKind::LoadLocal(load) if method_locals.contains(&load.id));
    }

    assert!(
        !method_locals.is_empty(),
        "generic trait method values passed as arguments should be materialized explicitly",
    );
    assert!(
        saw_let_local_arg,
        "materialized generic trait method values should use Let access from a local",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn blanket_impl_dictionary_closes_over_prerequisite_evidence() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            trait Describe<Self> {
                fn describe(value: Self) -> int;
            }

            impl Describe for int {
                fn describe(value: int) -> int { value }
            }

            struct Wrapper<T>(T)

            impl<T> Describe for Wrapper<T>
            where
                T: Describe,
                T: Value
            {
                fn describe(value: Wrapper<T>) -> int {
                    describe(value.0) + 1
                }
            }

            fn forward<T>(value: T) -> int
            where
                T: Describe,
                T: Value
            {
                describe(value)
            }

            fn invoke<T>(function: (T) -> int, value: T) -> int
            where
                T: Value
            {
                function(value)
            }

            describe(Wrapper(40))
                + forward(Wrapper(1))
                + invoke(describe, Wrapper(1))
        "#}),
        int(45)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn closed_dictionary_clones_and_drops_a_closure_environment() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            trait Describe<Self> {
                fn describe(value: Self) -> int;
            }

            impl Describe for int {
                fn describe(value: int) -> int { value }
            }

            struct Wrapper<T>(T)

            impl<T> Describe for Wrapper<T>
            where
                T: Describe,
                T: Value
            {
                fn describe(value: Wrapper<T>) -> int {
                    describe(value.0) + 1
                }
            }

            fn duplicate<T>(value: T) -> (T, T)
            where
                T: Value
            {
                (value, value)
            }

            let wrapped = Wrapper(40);
            let functions = duplicate(|offset| describe(wrapped) + offset);
            functions.0(1) + functions.1(2)
        "#}),
        int(85)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn capturing_blanket_dictionary_is_selected_across_modules() {
    let mut session = TestSession::new();
    session
        .try_compile_module(
            "base",
            indoc! {r#"
                pub trait Describe<Self> {
                    fn describe(value: Self) -> int;
                }

                impl Describe for int {
                    fn describe(value: int) -> int { value }
                }

                pub struct Wrapper<T>(T)

                impl<T> Describe for Wrapper<T>
                where
                    T: Describe,
                    T: Value
                {
                    fn describe(value: Wrapper<T>) -> int {
                        describe(value.0) + 1
                    }
                }

                pub fn forward<T>(value: T) -> int
                where
                    T: Describe,
                    T: Value
                {
                    describe(Wrapper(value))
                }
            "#},
        )
        .unwrap();
    session
        .try_compile_module(
            "user",
            "pub fn result() -> int { base::Describe::describe(base::Wrapper(40))\
                 + base::forward(1) }",
        )
        .unwrap();

    assert_val_eq!(session.run("user::result()"), int(43));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_callers_with_different_evidence_prefixes_clone_closed_functions() {
    let mut session = TestSession::new();
    let source = indoc! {r#"
        trait Mark<Self> {
            fn mark(value: Self) -> int;
        }

        impl Mark for int {
            fn mark(value: int) -> int { value }
        }

        fn first<T>(value: T) -> ((int) -> T, (int) -> T)
        where
            T: Value
        {
            let function = |ignored| value;
            (function, function)
        }

        fn second<T>(value: T) -> ((int) -> T, (int) -> T)
        where
            T: Mark,
            T: Value
        {
            mark(value);
            let function = |ignored| value;
            (function, function)
        }

        let a = first(20);
        let b = second(21);
        a.0(0) + a.1(0) + b.0(0) + b.1(0)
    "#};
    assert_val_eq!(session.run(source), int(82));
}

fn store_value_materializes_dictionary_method(arena: &ENodeArena, value: ENodeId) -> bool {
    match &arena[value].kind {
        NodeKind::GetDictionaryFunction(_) => true,
        NodeKind::CloneValue(clone) => {
            matches!(arena[clone.source].kind, NodeKind::GetDictionaryFunction(_))
        }
        _ => false,
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn generic_trait_method_call_uses_concrete_dictionary_method_signature() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            fn cmp_wrapper<A>(left: A, right: A)
            where
                A: Ord
            {
                match cmp(left, right) {
                    Greater => 42,
                    _ => 0,
                }
            }

            cmp_wrapper(1, 0)
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn user_defined_trait_methods_are_first_class_values() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            trait Double<Self> {
                fn double(value: Self) -> Self;
            }

            impl Double for int {
                fn double(value: int) -> int {
                    value * 2
                }
            }

            let my_double = double;
            my_double(21)
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn user_defined_traits_store_outputs_constraints_and_effects() {
    let mut session = TestSession::new();
    let mod_src = indoc! {r#"
        trait Project<Self |-> Output>
        where
            Self: testing::TestAssoc<Output = Output>
        {
            fn project_via_trait(value: Self) -> Output ! fallible;
        }

        impl Project for <Self = string |-> Output = int> {
            fn project_via_trait(value: string) -> int {
                testing::TestAssoc::project(value)
            }
        }
    "#};
    let module_id = session.compile(mod_src).module_id;
    let module = session.session().expect_fresh_module(module_id);
    let project_trait = module
        .trait_iter()
        .find(|(_, trait_def)| trait_def.name == ustr("Project"))
        .expect("expected user-defined trait to be stored in the module");
    let project_trait = project_trait.1;

    assert_eq!(project_trait.input_type_names, vec![ustr("Self")]);
    assert_eq!(project_trait.output_type_names, vec![ustr("Output")]);
    assert_eq!(project_trait.constraints.len(), 1);
    assert_eq!(
        project_trait.methods[0].1.ty_scheme.ty.effects,
        effect(PrimitiveEffect::Fallible)
    );
    let spans = project_trait
        .spans
        .as_ref()
        .expect("expected user-defined trait spans to be stored in the module");
    assert!(!spans.name.is_synthesized());
    assert!(!spans.span.is_synthesized());
    assert_eq!(spans.input_type_names.len(), 1);
    assert_eq!(spans.output_type_names.len(), 1);
    assert_eq!(spans.constraints.len(), 1);
    assert_eq!(spans.methods.len(), 1);
    assert!(!spans.methods[0].name.is_synthesized());
    assert_eq!(spans.methods[0].args.len(), 1);
    assert!(spans.methods[0].ret_ty.is_some());

    let rendered = module.format_with(&session.session().modules()).to_string();
    assert!(
        rendered.contains("trait Project <Self = A ↦ Output = B>"),
        "expected rendered trait header in module output, got:\n{rendered}"
    );
    assert!(
        rendered.contains("fn project_via_trait<A, B>(value: A) -> B ! fallible"),
        "expected rendered trait method signature in module output, got:\n{rendered}"
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parent_trait_constraints_are_impl_obligations() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            trait Parent<Self> {
                fn parent_value(value: Self) -> int;
            }

            trait Child<Self>: Parent<Self> {
                fn child_value(value: Self) -> int;
            }

            impl Parent for int {
                fn parent_value(value: int) -> int {
                    value
                }
            }

            impl Child for int {
                fn child_value(value: int) -> int {
                    parent_value(value) + 1
                }
            }

            child_value(41)
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parent_trait_constraints_must_hold_for_concrete_impls() {
    let mut session = TestSession::new();
    let err = session.fail_compilation(indoc! {r#"
        trait Parent<Self> {
            fn parent_value(value: Self) -> int;
        }

        trait Child<Self>: Parent<Self> {
            fn child_value(value: Self) -> int;
        }

        impl Child for int {
            fn child_value(value: int) -> int {
                42
            }
        }
    "#});

    match err.into_inner() {
        CompilationErrorImpl::TraitImplNotFound { trait_ref, .. } => {
            assert_eq!(trait_ref, "Parent");
        }
        other => panic!("expected TraitImplNotFound for Parent, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parent_trait_constraints_gate_blanket_impl_selection() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            struct Box<T>(T)

            trait Parent<Self> {
                fn parent_value(value: Self) -> int;
            }

            trait Child<Self>: Parent<Self> {
                fn child_value(value: Self) -> int;
            }

            impl<T> Parent for Box<T> {
                fn parent_value(value: Box<T>) -> int {
                    41
                }
            }

            impl<T> Child for Box<T> {
                fn child_value(value: Box<T>) -> int {
                    parent_value(value) + 1
                }
            }

            child_value(Box(0))
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn blanket_impl_structural_field_constraint_matches_named_struct() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            trait ReadX<Self> {
                fn read_x(value: Self) -> int;
            }

            impl<T> ReadX for T {
                fn read_x(value: T) -> int {
                    value.x
                }
            }

            struct Point {
                x: int,
                y: string,
            }

            read_x(Point { x: 42, y: "ignored" })
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parent_trait_constraints_support_multi_input_traits() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            trait Left<A> {
                fn left(value: A) -> int;
            }

            trait Right<B> {
                fn right(value: B) -> int;
            }

            trait Pair<A, B>: Left<A>, Right<B> {
                fn pair(left_value: A, right_value: B) -> int;
            }

            impl Left for int {
                fn left(value: int) -> int {
                    value
                }
            }

            impl Right for string {
                fn right(value: string) -> int {
                    2
                }
            }

            impl Pair for <int, string> {
                fn pair(left_value: int, right_value: string) -> int {
                    left(left_value) + right(right_value)
                }
            }

            pair(40, "ignored")
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn where_clauses_accept_positional_trait_inputs() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            trait Combine<Left, Right> {
                fn combine(left: Left, right: Right) -> int;
            }

            impl Combine for <int, string> {
                fn combine(left: int, right: string) -> int {
                    left + 2
                }
            }

            fn use_combine<Left, Right>(left: Left, right: Right) -> int
            where
                Combine<Left, Right>
            {
                combine(left, right)
            }

            use_combine(40, "ignored")
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn where_clauses_accept_positional_trait_inputs_with_named_outputs() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
            struct IntSource(int)

            trait Produce<Self |-> Item> {
                fn produce(value: Self) -> Item;
            }

            impl Produce for <Self = IntSource |-> Item = int> {
                fn produce(value: IntSource) -> int {
                    value.0
                }
            }

            fn use_produce<Source>(source: Source) -> int
            where
                Produce<Source |-> Item = int>
            {
                produce(source)
            }

            use_produce(IntSource(42))
        "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn parent_trait_constraints_are_not_trait_use_entailment() {
    let mut session = TestSession::new();
    let module = session.compile_and_get_module(indoc! {r#"
        trait Parent<Self> {
            fn parent_value(value: Self) -> int;
        }

        trait Child<Self>: Parent<Self> {
            fn child_value(value: Self) -> int;
        }

        fn needs_both<T>(value: T) -> int
        where
            T: Child
        {
            parent_value(value)
        }
    "#});
    let def = &module
        .get_function(ustr("needs_both"))
        .expect("expected needs_both function")
        .definition;
    let trait_names = def
        .ty_scheme
        .constraints
        .iter()
        .filter_map(|constraint| {
            constraint.as_have_trait().map(|(_, trait_id, _, _, _, _)| {
                module
                    .try_trait_name(*trait_id)
                    .expect("constraint trait should be defined")
            })
        })
        .collect::<Vec<_>>();

    assert!(trait_names.contains(&ustr("Child")));
    assert!(trait_names.contains(&ustr("Parent")));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concrete_impl_stores_associated_const_values() {
    extern "C" fn unit_identity(_: &()) {}

    let method = CallableDefinition::new_infer_quantifiers(
        FnType::new_by_val([Type::variable_id(0)], Type::variable_id(0), no_effects()),
        ["value"],
        "Returns the value.",
    );
    let trait_def = Trait::new_with_self_input_type(
        "Layout",
        "Compiler-only layout metadata.",
        Vec::<&str>::new(),
        [("identity", method)],
    )
    .with_associated_consts([
        TraitAssociatedConst::new("SIZE", Type::primitive::<isize>(), "Size in bytes."),
        TraitAssociatedConst::new("ALIGN", Type::primitive::<isize>(), "Alignment in bytes."),
    ]);
    let mut module = Module::new(ModuleId::new(0), Path::single_str("$trait_impl_test"));
    let trait_id = TraitId::new(ModuleId::new(0), module.add_trait(trait_def.clone()));
    let impl_id = module.add_concrete_impl_for_trait_def(
        trait_id,
        &trait_def,
        [Type::unit()],
        [],
        [
            LiteralValue::new_native(0isize),
            LiteralValue::new_native(1isize),
        ],
        [(
            Box::new(NativeFnR::new(unit_identity)) as Function,
            Vec::new(),
        )],
    );
    let imp = module
        .get_impl_data(impl_id)
        .expect("concrete impl should be registered");

    assert_eq!(
        trait_def.dictionary_method_index(TraitMethodIndex::new(0)),
        TraitDictionaryEntryIndex::new(0)
    );
    assert_eq!(
        trait_def.associated_const_index(ustr("SIZE")),
        Some(TraitAssociatedConstIndex::new(0))
    );
    assert_eq!(
        trait_def.associated_const_index(ustr("ALIGN")),
        Some(TraitAssociatedConstIndex::new(1))
    );
    assert_eq!(
        trait_def.dictionary_associated_const_index(TraitAssociatedConstIndex::new(0)),
        TraitDictionaryEntryIndex::new(1)
    );
    assert_eq!(
        trait_def.dictionary_associated_const_index(TraitAssociatedConstIndex::new(1)),
        TraitDictionaryEntryIndex::new(2)
    );
    assert_eq!(
        imp.associated_const_value(TraitAssociatedConstIndex::new(0)),
        Some(LiteralValue::new_native(0isize))
    );
    assert_eq!(
        imp.associated_const_value(TraitAssociatedConstIndex::new(1)),
        Some(LiteralValue::new_native(1isize))
    );
    assert_eq!(module.function_count(), 3);

    for (index, expected_name) in [
        (TraitAssociatedConstIndex::new(0), ">::SIZE#impl:"),
        (TraitAssociatedConstIndex::new(1), ">::ALIGN#impl:"),
    ] {
        let getter = imp.associated_const_getter(index).unwrap();
        let actual_name = module.get_function_name_by_id(getter).unwrap();
        assert!(
            actual_name.starts_with("Layout<") && actual_name.contains(expected_name),
            "expected `{actual_name}` to identify `Layout{expected_name}`"
        );
        let function = module.get_function_by_id(getter).unwrap();
        let entry = function
            .get_code_entry()
            .expect("associated constant getter should be an ordinary HIR function");
        assert!(matches!(
            module.hir_arena[entry].kind,
            NodeKind::Immediate(_)
        ));
    }

    assert!(matches!(
        imp.dictionary_value
            .entry(TraitDictionaryEntryIndex::new(0)),
        TraitDictionaryEntry::Function(_)
    ));
    assert_eq!(
        imp.dictionary_value
            .entry(TraitDictionaryEntryIndex::new(1)),
        TraitDictionaryEntry::Function(
            imp.associated_const_getter(TraitAssociatedConstIndex::new(0))
                .unwrap()
        )
    );
    assert_eq!(
        imp.dictionary_value
            .entry(TraitDictionaryEntryIndex::new(2)),
        TraitDictionaryEntry::Function(
            imp.associated_const_getter(TraitAssociatedConstIndex::new(1))
                .unwrap()
        )
    );

    let int_ty = Type::primitive::<isize>();
    assert_eq!(
        trait_def.get_dictionary_type_for_tys(&[Type::unit()], &[], &[]),
        imp.dictionary_ty,
        "trait-side and implementation-side dictionary types must agree"
    );
    let dictionary_ty_data = imp.dictionary_ty.data();
    let dictionary_tys = dictionary_ty_data.as_tuple().unwrap();
    assert!(dictionary_tys[0].data().as_function().is_some());
    assert_eq!(dictionary_tys[1].data().as_function().unwrap().ret, int_ty);
    assert_eq!(dictionary_tys[2].data().as_function().unwrap().ret, int_ty);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_items_share_one_namespace() {
    let sources = [
        indoc! {r#"
            trait Duplicate<Self> {
                fn item(value: Self) -> int;
                fn item(value: Self) -> int;
            }
        "#},
        indoc! {r#"
            trait Duplicate<Self> {
                const item: int;
                const item: int;
            }
        "#},
        indoc! {r#"
            trait Duplicate<Self> {
                fn item(value: Self) -> int;
                const item: int;
            }
        "#},
    ];

    for source in sources {
        let mut session = TestSession::new();
        match session.fail_compilation(source).into_inner() {
            CompilationErrorImpl::InvalidTraitDefinition {
                trait_name,
                kind,
                span,
            } => {
                assert_eq!(trait_name, ustr("Duplicate"));
                assert_eq!(
                    kind,
                    InvalidTraitDefinitionKind::DuplicateItem { name: ustr("item") }
                );
                assert_eq!(span.start_usize(), source.rfind("item").unwrap());
            }
            other => panic!("expected InvalidTraitDefinition, got {other:?}"),
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn source_traits_can_define_literal_associated_consts() {
    let mut session = TestSession::new();

    assert_val_eq!(
        session.run(indoc! {r#"
            trait HasConst<Self> {
                const C: Self;
                fn id(value: Self) -> Self;
            }

            impl HasConst for int {
                const C = 7;

                fn id(value: int) -> int {
                    value
                }
            }

            HasConst::<int>::C
        "#}),
        int(7)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn managed_associated_consts_are_materialized_by_concrete_and_dictionary_getters() {
    let mut session = TestSession::new();
    let source = indoc! {r#"
        trait Greeting<Self> {
            const TEXT: string;
        }

        impl Greeting for int {
            const TEXT = "hello";
        }

        fn generic<T>(value: T) -> string
        where
            T: Greeting
        {
            Greeting::<T>::TEXT
        }

        let concrete = Greeting::<int>::TEXT;
        let through_dictionary = generic(0);
        string_concat(concrete, through_dictionary)
    "#};

    assert_val_eq!(session.run(source), string("hellohello"));

    let module = session.compile_and_get_module(source);
    assert!(module.iter_named_functions().any(|(name, _)| {
        name.starts_with("Greeting<std::int>::TEXT#impl:") && !name.contains("getter")
    }));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn source_trait_impl_rejects_unknown_associated_const() {
    let mut session = TestSession::new();

    match session
        .fail_compilation(indoc! {r#"
            trait HasConst<Self> {
                const C: Self;
                fn id(value: Self) -> Self;
            }

            impl HasConst for int {
                const D = 7;
                fn id(value: int) -> int { value }
            }
        "#})
        .into_inner()
    {
        CompilationErrorImpl::InvalidTraitAssociatedConstImpl {
            trait_ref, kind, ..
        } => {
            assert_eq!(trait_ref, "HasConst");
            assert_eq!(
                kind,
                InvalidTraitAssociatedConstImplKind::Unknown { name: ustr("D") }
            );
        }
        other => panic!("expected InvalidTraitAssociatedConstImpl, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn source_trait_impl_rejects_duplicate_associated_const() {
    let mut session = TestSession::new();

    match session
        .fail_compilation(indoc! {r#"
            trait HasConst<Self> {
                const C: Self;
                fn id(value: Self) -> Self;
            }

            impl HasConst for int {
                const C = 7;
                const C = 8;
                fn id(value: int) -> int { value }
            }
        "#})
        .into_inner()
    {
        CompilationErrorImpl::InvalidTraitAssociatedConstImpl {
            trait_ref, kind, ..
        } => {
            assert_eq!(trait_ref, "HasConst");
            assert_eq!(
                kind,
                InvalidTraitAssociatedConstImplKind::Duplicate { name: ustr("C") }
            );
        }
        other => panic!("expected InvalidTraitAssociatedConstImpl, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn source_trait_impl_rejects_missing_associated_const() {
    let mut session = TestSession::new();

    match session
        .fail_compilation(indoc! {r#"
            trait HasConsts<Self> {
                const C: Self;
                const D: Self;
                fn id(value: Self) -> Self;
            }

            impl HasConsts for int {
                const C = 7;
                fn id(value: int) -> int { value }
            }
        "#})
        .into_inner()
    {
        CompilationErrorImpl::InvalidTraitAssociatedConstImpl {
            trait_ref, kind, ..
        } => {
            assert_eq!(trait_ref, "HasConsts");
            assert_eq!(
                kind,
                InvalidTraitAssociatedConstImplKind::Missing {
                    names: vec![ustr("D")]
                }
            );
        }
        other => panic!("expected InvalidTraitAssociatedConstImpl, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn invalid_trait_methods_report_structured_errors() {
    let mut session = TestSession::new();

    match session
        .fail_compilation(indoc! {r#"
            trait Factory<Self> {
                fn make() -> int;
            }
        "#})
        .into_inner()
    {
        CompilationErrorImpl::InvalidTraitDefinition {
            trait_name, kind, ..
        } => {
            assert_eq!(trait_name, ustr("Factory"));
            assert_eq!(
                kind,
                InvalidTraitDefinitionKind::MissingInputTypeVarInMethod {
                    method_name: ustr("make"),
                    ty_var: TypeVar::new(0),
                }
            );
        }
        other => panic!("expected InvalidTraitDefinition, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn invalid_trait_constraint_order_reports_structured_errors() {
    let mut session = TestSession::new();

    match session
        .fail_compilation(indoc! {r#"
            trait Sequence<Self |-> Item, Iter>
            where
                Iter: Iterator<Item = Item>,
                Self: testing::TestAssoc<Output = Iter>
            {
                fn first(value: Self) -> Item;
            }
        "#})
        .into_inner()
    {
        CompilationErrorImpl::InvalidTraitDefinition {
            trait_name, kind, ..
        } => {
            assert_eq!(trait_name, ustr("Sequence"));
            assert_eq!(
                kind,
                InvalidTraitDefinitionKind::UnreachableConstraintInputTypeVar {
                    method_name: ustr("first"),
                    constraint_index: 0,
                }
            );
        }
        other => panic!("expected InvalidTraitDefinition, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_concrete_and_headerless() {
    for header in ["impl Size for int", "impl Size"] {
        let mut session = TestSession::new();
        let code = format!(
            r#"
            trait Size<Self> {{
                fn size(x: Self) -> int;
                fn double(x: Self) -> int {{ size(x) * 2 }}
            }}
            {header} {{ fn size(x: int) -> int {{ x }} }}
            double(21)
        "#
        );
        assert_val_eq!(session.run(&code), int(42));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_generic_and_sibling_calls() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
        trait Size<Self> {
            fn size(x: Self) -> int;
            fn double(x: Self) -> int { size(x) * 2 }
            fn quadruple(x: Self) -> int;
        }
        impl<T> Size for [T] where T: Value {
            fn size(x: [T]) -> int { len(x) }
            fn quadruple(x: [T]) -> int { double(x) * 2 }
        }
        quadruple([1, 2, 3])
    "#}),
        int(12)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_override_through_generic_caller() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
        trait Size<Self> {
            fn size(x: Self) -> int;
            fn double(x: Self) -> int { size(x) * 2 }
        }
        impl Size for int {
            fn size(x: int) -> int { x }
            fn double(x: int) -> int { x * 3 }
        }
        fn use_size<T>(x: T) -> int where T: Size { double(x) }
        use_size(14)
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_resolves_private_helpers_in_defining_module() {
    let mut session = TestSession::new();
    session
        .try_compile_module(
            "base",
            indoc! {r#"
        fn twice(x: int) -> int { x * 2 }
        pub trait Size<Self> {
            fn size(x: Self) -> int;
            fn double(x: Self) -> int { twice(size(x)) }
        }
    "#},
        )
        .unwrap();
    assert_val_eq!(
        session.run(indoc! {r#"
        use base::Size;
        struct Counter(int)
        fn twice(x: int) -> int { 999 }
        impl Size for Counter { fn size(x: Counter) -> int { x.0 } }
        Size::double(Counter(21))
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_cross_module_blanket_dictionary() {
    let mut session = TestSession::new();
    session
        .try_compile_module(
            "base",
            indoc! {r#"
        pub trait Size<Self> {
            fn size(x: Self) -> int;
            fn double(x: Self) -> int { size(x) * 2 }
        }
        impl<T> Size for [T] where T: Value {
            fn size(x: [T]) -> int { len(x) }
        }
    "#},
        )
        .unwrap();
    assert_val_eq!(
        session.run(indoc! {r#"
        use base::Size;
        fn via_dictionary<T>(x: T) -> int where T: Size { Size::double(x) }
        via_dictionary([1, 2, 3])
    "#}),
        int(6)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_checked_without_an_impl() {
    let mut session = TestSession::new();
    for (source, expected_reason) in [
        (
            "trait Bad<Self> { fn bad(x: Self) -> int { x + 1 } }",
            InvalidDefaultMethodKind::SpecializedTypeParameter,
        ),
        (
            "trait Bad<Self> { fn bad(x: Self) -> Self { -x } }",
            InvalidDefaultMethodKind::UndeclaredConstraint,
        ),
        (
            "trait Bad<Self |-> ! E> { fn bad(x: Self) ! E { effects::write() } }",
            InvalidDefaultMethodKind::RestrictedEffectParameter,
        ),
    ] {
        let error = session.fail_compilation(source).into_inner();
        let CompilationErrorImpl::InvalidTraitDefinition {
            trait_name,
            kind:
                InvalidTraitDefinitionKind::InvalidDefaultMethod {
                    method_name,
                    reason,
                },
            span,
        } = error
        else {
            panic!("unexpected diagnostic: {error:?}")
        };
        assert_eq!(trait_name, ustr("Bad"));
        assert_eq!(method_name, ustr("bad"));
        assert_eq!(reason, expected_reason);
        assert_eq!(
            span.as_range(),
            source.find("fn bad").unwrap()..source.len() - 2
        );
    }
    let source = "trait Bad<Self> { fn bad(x: Self) { effects::write() } }";
    let error = session.fail_compilation(source).into_inner();
    let CompilationErrorImpl::TraitMethodEffectMismatch {
        method_name, span, ..
    } = error
    else {
        panic!("unexpected diagnostic: {error:?}")
    };
    assert_eq!(method_name, ustr("bad"));
    assert_eq!(
        span.as_range(),
        source.find("fn bad").unwrap()..source.len() - 2
    );

    let source = "trait Bad<Self> { fn bad(x: Self) -> bool { 1 } }";
    let error = session.fail_compilation(source).into_inner();
    let CompilationErrorImpl::TraitImplNotFound {
        trait_ref, fn_span, ..
    } = error
    else {
        panic!("unexpected diagnostic: {error:?}")
    };
    assert_eq!(trait_ref, "Num");
    assert_eq!(&source[fn_span.as_range()], "1");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_parent_constraint_and_mutable_argument() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
        trait Step<Self>: Num<Self>, Value<Self> {
            fn step(x: &mut Self) { x = -x; }
        }
        impl Step for int {}
        let mut x = -42;
        step(x);
        x
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_output_type_and_effect() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
        trait Get<Self |-> Item ! E> {
            fn get(x: Self) -> Item ! E;
            fn again(x: Self) -> Item ! E { get(x) }
        }
        impl Get for <Self = int |-> Item = int ! E = fallible> {
            fn get(x: int) -> int { assert(x > 0); x }
        }
        again(42)
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_missing_required_method() {
    let mut session = TestSession::new();
    let error = session.fail_compilation(indoc! {r#"
        trait Size<Self> {
            fn size(x: Self) -> int;
            fn double(x: Self) -> int { size(x) * 2 }
        }
        impl Size for int {}
    "#});
    assert!(
        matches!(error.into_inner(), CompilationErrorImpl::TraitMethodImplsMissing { missings, .. } if missings == [ustr("size")])
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_l2_module_functions_still_cannot_use_local_blanket_impls() {
    let mut session = TestSession::new();
    let source = indoc! {r#"
        trait Size<Self> {
            fn size(x: Self) -> int;
            fn double(x: Self) -> int { size(x) * 2 }
        }
        impl<T> Size for [T] where T: Value {
            fn size(x: [T]) -> int { len(x) }
        }
        fn local_use(x: [int]) -> int { double(x) }
    "#};
    let error = session.fail_compilation(source).into_inner();
    let CompilationErrorImpl::TraitImplNotFound {
        trait_ref, fn_span, ..
    } = error
    else {
        panic!("unexpected diagnostic: {error:?}")
    };
    assert_eq!(trait_ref, "Size");
    assert_eq!(&source[fn_span.as_range()], "double");
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_recursive_dispatch_obeys_call_depth_limit() {
    use ferlium::{
        ExecutionTarget,
        compiler::error::{RuntimeErrorKind, SandboxViolationKind},
        execution::ReferenceInterpreterLimits,
    };
    let mut session = TestSession::new();
    for source in [
        "trait Loop<Self> { fn cycle(x: Self) -> int { cycle(x) } } impl Loop for int {} cycle(1)",
        "trait Loop<Self> { fn cycle(x: Self) -> int { callback() } } fn callback() -> int { cycle(1) } impl Loop for int {} cycle(1)",
        "trait Parent<Self> { fn parent(x: Self) -> int; } trait Child<Self>: Parent<Self> { fn child(x: Self) -> int { parent(x) } } impl Parent for int { fn parent(x: int) -> int { child(x) } } impl Child for int {} child(1)",
        "trait Other<Self> { fn other(x: Self) -> int; } trait Loop<Self> where Self: Other { fn cycle(x: Self) -> int { other_helper(x) } } fn other_helper<T>(x: T) -> int where T: Other { other(x) } impl Other for int { fn other(x: int) -> int { cycle(x) } } impl Loop for int {} cycle(1)",
        "trait Loop<Self> { fn a(x: Self) -> int { b(x) } fn b(x: Self) -> int; } impl Loop for int { fn b(x: int) -> int { a(x) } } a(1)",
        "trait Loop<Self> { fn a(x: Self) -> int; fn b(x: Self) -> int; } impl<T> Loop for [T] where T: Value { fn a(x: [T]) -> int { b(x) } fn b(x: [T]) -> int { a(x) } } a([1])",
    ] {
        let output = session.compile(source);
        let entry = output.expr.unwrap();
        for target in ExecutionTarget::REFERENCE {
            let error = session
                .session_mut()
                .run_entry_with_limits(
                    target,
                    output.module_id,
                    entry,
                    vec![],
                    ReferenceInterpreterLimits::default()
                        .with_call_depth_limit(8)
                        .with_fuel_limit(Some(200)),
                )
                .expect_err("recursive trait calls must be bounded");
            assert_eq!(
                error.kind(),
                RuntimeErrorKind::SandboxViolation(SandboxViolationKind::CallDepthLimitExceeded {
                    limit: 8
                })
            );
        }
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_effect_polymorphic_blanket_impl() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
        trait Execute<Self |-> ! E> {
            fn execute(x: Self) -> int ! E;
            fn again(x: Self) -> int ! E { execute(x) }
        }
        struct Action<! F> { f: () -> int ! F }
        impl<! F> Execute for <Self = Action<! F> |-> ! E = F> {
            fn execute(x: Action<! F>) -> int { x.f() }
        }
        again(Action { f: || 21 }) + again(Action { f: || { assert(true); 21 } })
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_effect_parameter_only_in_evidence() {
    let mut session = TestSession::new();
    session
        .try_compile_module(
            "base",
            indoc! {r#"
        pub trait Source<Self |-> ! E> {
            fn get(x: Self) -> int ! E;
            fn plain(x: Self) -> int;
        }
        pub trait Adapter<Self |-> ! E> where Self: Source<! E = E> {
            fn adapted(x: Self) -> int ! E;
            fn tag(x: Self) -> int { plain(x) }
        }
        impl<T ! F> Adapter for <Self = T |-> ! E = F>
        where T: Source<! E = F> {
            fn adapted(x: T) -> int { get(x) }
        }
        impl Source for <Self = int |-> ! E = fallible> {
            fn get(x: int) -> int { assert(x > 0); x }
            fn plain(x: int) -> int { x }
        }
    "#},
        )
        .unwrap();
    assert_val_eq!(
        session.run(indoc! {r#"
        use base::*;
        fn call(x: int) -> int { adapted(x) + tag(x) }
        call(21)
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_first_class_method_uses_override_and_associated_const() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
        trait Measure<Self> {
            const FACTOR: int;
            fn measure(x: Self) -> int { 1 }
            fn scaled(x: Self) -> int { measure(x) * Measure::<Self>::FACTOR }
        }
        impl Measure for int {
            const FACTOR = 2;
            fn measure(x: int) -> int { x }
        }
        let f = Measure::scaled;
        f(21)
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_unbound_parent_effect() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
        trait Source<Self |-> ! E> {
            fn get(x: Self) -> int ! E;
            fn plain(x: Self) -> int;
        }
        trait Tagged<Self>: Source<Self> {
            fn tag(x: Self) -> int { plain(x) }
        }
        impl Source for <Self = int |-> ! E = fallible> {
            fn get(x: int) -> int { assert(x > 0); x }
            fn plain(x: int) -> int { x }
        }
        impl Tagged for int {}
        tag(42)
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_requires_declared_value_constraint() {
    let mut session = TestSession::new();
    let source = "trait Replace<Self> { fn replace(x: &mut Self, y: Self) { x = y; } }";
    let error = session.fail_compilation(source).into_inner();
    let CompilationErrorImpl::InvalidTraitDefinition {
        kind:
            InvalidTraitDefinitionKind::InvalidDefaultMethod {
                reason: InvalidDefaultMethodKind::UndeclaredConstraint,
                ..
            },
        span,
        ..
    } = error
    else {
        panic!("unexpected diagnostic: {error:?}")
    };
    assert_eq!(
        span.as_range(),
        source.find("fn replace").unwrap()..source.len() - 2
    );
    assert_val_eq!(
        session.run(indoc! {r#"
        trait Replace<Self>: Value<Self> { fn replace(x: &mut Self, y: Self) { x = y; } }
        impl Replace for int {}
        let mut x = 0;
        replace(x, 42);
        x
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_ancestor_effects_are_independent() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
        trait Source<Self |-> ! E> {
            fn get(x: Self) -> int ! E;
            fn plain(x: Self) -> int;
        }
        trait Other<Self |-> ! E> {
            fn set(x: Self) ! E;
            fn other_plain(x: Self) -> int;
        }
        trait Parent<Self>: Source<Self> { fn parent(x: Self); }
        trait Tagged<Self>: Parent<Self> where Self: Other {
            fn tag(x: Self) -> int { plain(x) + other_plain(x) }
        }
        impl Source for <Self = int |-> ! E = fallible> {
            fn get(x: int) -> int { assert(x > 0); x }
            fn plain(x: int) -> int { x }
        }
        impl Other for <Self = int |-> ! E = write> {
            fn set(x: int) { effects::write() }
            fn other_plain(x: int) -> int { x }
        }
        impl Parent for int { fn parent(x: int) {} }
        impl Tagged for int {}
        tag(21)
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_leaf_methods_keep_their_dictionary_abi() {
    use ferlium::{
        module::{ConcreteTraitImplKey, id::Id},
        types::type_scheme::PubTypeConstraint,
    };
    let mut session = TestSession::new();
    for (header, ty_name, argument_ty, body, argument) in [
        ("impl Measure for int", "int", "int", "x", "21"),
        (
            "impl<T> Measure for [T] where T: Value",
            "[int]",
            "[T]",
            "len(x)",
            "[1, 2, 3]",
        ),
    ] {
        let code = format!(
            r#"
            trait Measure<Self> {{
                fn leaf(x: Self) -> int;
                fn doubled(x: Self) -> int {{ leaf(x) * 2 }}
            }}
            {header} {{ fn leaf(x: {argument_ty}) -> int {{ {body} }} }}
            doubled({argument})
        "#
        );
        let ty = session.resolve_defined_type(ty_name).unwrap();
        let output = session.compile(&code);
        let module = session.session().expect_fresh_module(output.module_id);
        let trait_id = module.get_trait_id_str("Measure").unwrap();
        let impl_id = module
            .get_concrete_impl_by_key(&ConcreteTraitImplKey::new(trait_id, vec![ty]))
            .unwrap();
        let implementation = module.get_impl_data(*impl_id).unwrap();
        let leaf = TraitDictionaryEntryIndex::from_index(0);
        let doubled = TraitDictionaryEntryIndex::from_index(1);
        assert!(
            !implementation
                .dictionary_value
                .entry_uses_self_dictionary(leaf)
        );
        assert!(
            implementation
                .dictionary_value
                .entry_uses_self_dictionary(doubled)
        );
        let leaf_function = module
            .get_function_by_id(implementation.methods[0])
            .unwrap();
        assert!(!leaf_function.definition.ty_scheme.constraints.iter().any(|constraint| {
            matches!(constraint, PubTypeConstraint::HaveTrait { trait_id: id, .. } if *id == trait_id)
        }));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_given_owners_survive_constraint_deduplication() {
    use ferlium::module::{ConcreteTraitImplKey, id::Id};
    let mut session = TestSession::new();
    let source = indoc! {r#"
        trait Size<Self> {
            fn size(x: Self) -> int;
            fn first(x: Self) -> int;
            fn second(x: Self) -> int;
        }
        impl<T> Size for [T] where T: Value {
            fn size(x: [T]) -> int { len(x) }
            fn first(x: [T]) -> int { size(x) }
            fn second(x: [T]) -> int { let f = || size(x); f() }
        }
        first([1]) + second([1, 2])
    "#};
    let output = session.compile(source);
    let ty = session.resolve_defined_type("[int]").unwrap();
    let module = session.session().expect_fresh_module(output.module_id);
    let trait_id = module.get_trait_id_str("Size").unwrap();
    let impl_id = module
        .get_concrete_impl_by_key(&ConcreteTraitImplKey::new(trait_id, vec![ty]))
        .unwrap();
    let dictionary = &module.get_impl_data(*impl_id).unwrap().dictionary_value;
    assert!(!dictionary.entry_uses_self_dictionary(TraitDictionaryEntryIndex::from_index(0)));
    assert!(dictionary.entry_uses_self_dictionary(TraitDictionaryEntryIndex::from_index(1)));
    assert!(dictionary.entry_uses_self_dictionary(TraitDictionaryEntryIndex::from_index(2)));
    assert_val_eq!(session.run(source), int(3));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_given_used_by_generic_operator() {
    let mut session = TestSession::new();
    assert_val_eq!(session.run(indoc! {r#"
        struct Wrapped<T> { value: T }
        impl<T> Num for Wrapped<T> where T: Num, T: Value {
            fn add(left: Wrapped<T>, right: Wrapped<T>) -> Wrapped<T> { left - (-right) }
            fn sub(left: Wrapped<T>, right: Wrapped<T>) -> Wrapped<T> { Wrapped { value: left.value - right.value } }
            fn mul(left: Wrapped<T>, right: Wrapped<T>) -> Wrapped<T> { Wrapped { value: left.value * right.value } }
            fn neg(x: Wrapped<T>) -> Wrapped<T> { Wrapped { value: -x.value } }
            fn abs(x: Wrapped<T>) -> Wrapped<T> { Wrapped { value: abs(x.value) } }
            fn signum(x: Wrapped<T>) -> Wrapped<T> { Wrapped { value: signum(x.value) } }
            fn from_int(x: int) -> Wrapped<T> { Wrapped { value: from_int(x) } }
        }
        (Wrapped { value: 21 } + Wrapped { value: 21 }).value
    "#}), int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_given_used_by_generic_for_loop() {
    let mut session = TestSession::new();
    assert_val_eq!(
        session.run(indoc! {r#"
        struct Bag<T> { data: [T], nested: bool }
        impl<T> Seq for <Self = Bag<T> |-> Item = T, Iter = ArrayIterator<T>> where T: Value {
            fn iter(bag: Bag<T>) -> ArrayIterator<T> {
                if bag.nested {
                    let inner = Bag { data: bag.data, nested: false };
                    for item in inner { };
                };
                iter(bag.data)
            }
        }
        let mut sum = 0;
        let bag = Bag { data: [21, 21], nested: true };
        for item in bag { sum += item; };
        sum
    "#}),
        int(42)
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_diamond_shares_ancestor_evidence() {
    use ferlium::types::type_scheme::PubTypeConstraint;
    let mut session = TestSession::new();
    let source = indoc! {r#"
        trait D<Self |-> ! E> { fn get(x: Self) -> int; fn act(x: Self) ! E; }
        trait B<Self>: D<Self> { fn b(x: Self); }
        trait C<Self>: D<Self> { fn c(x: Self); }
        trait A<Self>: B<Self>, C<Self> { fn answer(x: Self) -> int { get(x) } }
        impl D for <Self = int |-> ! E = write> {
            fn get(x: int) -> int { x }
            fn act(x: int) { effects::write() }
        }
        impl B for int { fn b(x: int) {} }
        impl C for int { fn c(x: int) {} }
        impl A for int {}
        answer(42)
    "#};
    let output = session.compile(source);
    let module = session.session().expect_fresh_module(output.module_id);
    let ancestor = module.get_trait_id_str("D").unwrap();
    let default = module.get_trait_str("A").unwrap().default_methods[0]
        .as_ref()
        .unwrap();
    let function = module
        .get_function_by_id(default.function.function)
        .unwrap();
    assert_eq!(function.definition.ty_scheme.constraints.iter().filter(|constraint| {
        matches!(constraint, PubTypeConstraint::HaveTrait { trait_id, .. } if *trait_id == ancestor)
    }).count(), 1);
    assert_val_eq!(session.run(source), int(42));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_multi_input_givens() {
    for implementation in [
        "impl Pair for <int, string> { fn pair(a: int, b: string) -> int { a } }",
        "impl Pair { fn pair(a: int, b: string) -> int { a } }",
        "impl<T> Pair for <int, [T]> where T: Value { fn pair(a: int, b: [T]) -> int { a } }",
    ] {
        let argument = if implementation.contains("impl<T>") {
            "[1]"
        } else {
            "\"b\""
        };
        let mut session = TestSession::new();
        assert_val_eq!(session.run(&format!(
            "trait Pair<A, B> {{ fn pair(a: A, b: B) -> int; fn twice(a: A, b: B) -> int {{ pair(a, b) * 2 }} }} {implementation} twice(21, {argument})"
        )), int(42));
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_reversed_same_trait_given() {
    for methods in [
        "Convert<A, B>, Convert<B, A>",
        "Convert<B, A>, Convert<A, B>",
    ] {
        let mut session = TestSession::new();
        assert_val_eq!(
            session.run(&format!(
                r#"
            trait Convert<A, B> {{ fn to(a: A) -> B; }}
            trait Round<A, B> where {methods}, A: Value, B: Value {{ fn round_trip(a: A, b: B) -> A {{ let intermediate: B = to(a); to(intermediate) }} }}
            impl Convert for <int, string> {{ fn to(a: int) -> string {{ "answer" }} }}
            impl Convert for <string, int> {{ fn to(a: string) -> int {{ 42 }} }}
            impl Round for <int, string> {{}}
            let result: int = round_trip(1, "");
            result
        "#
            )),
            int(42)
        );
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn trait_default_headerless_body_determines_self() {
    for methods in [
        "fn base(x) { x + 1 } fn sibling(x) { base(x) }",
        "fn sibling(x) { base(x) } fn base(x) { x + 1 }",
    ] {
        let mut session = TestSession::new();
        assert_val_eq!(session.run(&format!(
            "trait Size<Self> {{ fn base(x: Self) -> int; fn sibling(x: Self) -> int; fn defaulted(x: Self) -> int {{ sibling(x) }} }} impl Size {{ {methods} }} defaulted(41)"
        )), int(42));
    }
}
