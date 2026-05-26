// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use test_log::test;

use ferlium::{
    compiler::error::{CompilationErrorImpl, InvalidTraitDefinitionKind},
    format::FormatWith,
    hir::function::{Function, FunctionDefinition, VoidFunction},
    module::{FunctionCollector, LocalDecl, ModuleId, TraitDictionaryEntry, TraitImpls},
    types::{
        effects::{PrimitiveEffect, effect, no_effects},
        r#trait::{
            TraitAssociatedConst, TraitAssociatedConstIndex, TraitDictionaryEntryIndex,
            TraitMethodIndex, TraitRef,
        },
        r#type::{FnType, Type, TypeVar},
    },
};
use indoc::indoc;
use ustr::ustr;

use crate::harness::{TestSession, int};

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
                testing::project(value)
            }
        }
    "#};
    let module_id = session.compile(mod_src).module_id;
    let module = session.session().expect_fresh_module(module_id);
    let project_trait = module
        .trait_iter()
        .find(|trait_ref| trait_ref.name == ustr("Project"))
        .expect("expected user-defined trait to be stored in the module");

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

    let rendered = module.format_with(session.session().modules()).to_string();
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
            constraint
                .as_have_trait()
                .map(|(trait_ref, _, _, _)| trait_ref.name)
        })
        .collect::<Vec<_>>();

    assert!(trait_names.contains(&ustr("Child")));
    assert!(trait_names.contains(&ustr("Parent")));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn concrete_impl_stores_associated_const_values() {
    let method = FunctionDefinition::new_infer_quantifiers(
        FnType::new_by_val([Type::variable_id(0)], Type::variable_id(0), no_effects()),
        ["value"],
        "Returns the value.",
    );
    let trait_ref = TraitRef::new_with_self_input_type(
        "Layout",
        "Compiler-only layout metadata.",
        Vec::<&str>::new(),
        [("identity", method)],
    )
    .with_associated_consts([
        TraitAssociatedConst::new("SIZE", "Size in bytes."),
        TraitAssociatedConst::new("ALIGN", "Alignment in bytes."),
    ]);
    let mut impls = TraitImpls::new(ModuleId(0));
    let mut fn_collector = FunctionCollector::new(0);

    let impl_id = impls.add_concrete_raw(
        trait_ref.clone(),
        [Type::unit()],
        [],
        [0, 1],
        [(Box::new(VoidFunction) as Function, Vec::<LocalDecl>::new())],
        &mut fn_collector,
    );
    let imp = impls.get_impl_by_local_id(impl_id);

    assert_eq!(
        trait_ref.dictionary_method_index(TraitMethodIndex(0)),
        TraitDictionaryEntryIndex(0)
    );
    assert_eq!(
        trait_ref.associated_const_index(ustr("SIZE")),
        Some(TraitAssociatedConstIndex(0))
    );
    assert_eq!(
        trait_ref.associated_const_index(ustr("ALIGN")),
        Some(TraitAssociatedConstIndex(1))
    );
    assert_eq!(
        trait_ref.dictionary_associated_const_index(TraitAssociatedConstIndex(0)),
        TraitDictionaryEntryIndex(1)
    );
    assert_eq!(
        trait_ref.dictionary_associated_const_index(TraitAssociatedConstIndex(1)),
        TraitDictionaryEntryIndex(2)
    );
    assert_eq!(
        imp.associated_const_value(TraitAssociatedConstIndex(0)),
        Some(0)
    );
    assert_eq!(
        imp.associated_const_value(TraitAssociatedConstIndex(1)),
        Some(1)
    );
    assert_eq!(fn_collector.new_elements.len(), 1);

    assert!(matches!(
        imp.dictionary_value.entry(TraitDictionaryEntryIndex(0)),
        TraitDictionaryEntry::Method(_)
    ));
    assert_eq!(
        imp.dictionary_value.entry(TraitDictionaryEntryIndex(1)),
        TraitDictionaryEntry::AssociatedConst(0)
    );
    assert_eq!(
        imp.dictionary_value.entry(TraitDictionaryEntryIndex(2)),
        TraitDictionaryEntry::AssociatedConst(1)
    );

    let int_ty = Type::primitive::<isize>();
    let dictionary_ty_data = imp.dictionary_ty.data();
    let dictionary_tys = dictionary_ty_data.as_tuple().unwrap();
    assert!(dictionary_tys[0].data().as_function().is_some());
    assert_eq!(dictionary_tys[1], int_ty);
    assert_eq!(dictionary_tys[2], int_ty);
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
