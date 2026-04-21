// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use test_log::test;

use ferlium::error::{CompilationErrorImpl, InvalidTraitDefinitionKind};
use ferlium::r#type::TypeVar;
use ferlium::{
    effects::{PrimitiveEffect, effect},
    format::FormatWith,
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
    assert_eq!(
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
        project_trait.functions[0].1.ty_scheme.ty.effects,
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
    assert_eq!(spans.functions.len(), 1);
    assert!(!spans.functions[0].name.is_synthesized());
    assert_eq!(spans.functions[0].args.len(), 1);
    assert!(spans.functions[0].ret_ty.is_some());

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
