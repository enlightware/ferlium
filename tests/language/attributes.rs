// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ferlium::{
    SourceId, ast,
    compiler::{
        error::{AttributeTarget, CompilationErrorImpl, InvalidAttributeKind, UnsafeFeature},
        test_support::raw_modules,
    },
    hir::test_support::{EmitModuleFrom, emit_module},
    module::{ModuleId, Uses, id::Id},
    parse_module_and_expr,
};
use indoc::indoc;
use test_log::test;
use ustr::ustr;

use crate::harness::TestSession;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

fn parse_module_ast(src: &str) -> ast::PModule {
    parse_module_and_expr(src, SourceId::from_index(1), true)
        .unwrap_or_else(|errors| panic!("module should parse cleanly, got {errors:?}"))
        .0
}

fn compile_std_module(src: &str) -> ferlium::module::Module {
    let session = TestSession::new();
    let source_id = session.source_table().next_id();
    let (module_ast, _, arena) =
        parse_module_and_expr(src, source_id, true).expect("std-context module should parse");
    let module_id = ModuleId(0);
    emit_module(
        module_ast,
        &arena,
        module_id,
        raw_modules(session.session()),
        EmitModuleFrom::Uses(Uses::default()),
    )
    .expect("std-context module should compile")
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn type_def_attributes_are_preserved_in_hir_metadata() {
    let mut session = TestSession::new();
    let mut attrs = |code, name| {
        session
            .compile_and_get_module(code)
            .get_type_def(ustr(name))
            .unwrap()
            .attributes
            .clone()
    };

    let attributes = attrs(
        indoc! { r#"
            enum SimpleColor { Red, Green, Blue }
        "# },
        "SimpleColor",
    );
    assert!(attributes.is_empty());

    let attributes = attrs(
        indoc! { r#"
            #[flag]
            enum SimpleColor { Red, Green, Blue }
        "# },
        "SimpleColor",
    );
    assert_eq!(attributes.len(), 1);
    assert_eq!(attributes[0].path.0, ustr("flag"));

    let attributes = attrs(
        indoc! { r#"
            #[flag]
            #[path(name = "value")]
            #[multi(name1 = "value1", name2 = "value2")]
            enum SimpleColor { Red, Green, Blue }
        "# },
        "SimpleColor",
    );
    assert_multi_attributes(&attributes);

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
    assert_multi_attributes(&attributes);
}

fn assert_multi_attributes(attributes: &[ast::Attribute]) {
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

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn enum_variant_attributes_are_parsed() {
    let module = parse_module_ast(indoc! { r#"
        enum TrafficLight {
            #[default]
            Red,
            #[doc(name = "ignored")]
            Yellow,
            Green,
        }
    "# });

    let type_def = &module.type_defs[0];
    assert_eq!(type_def.variant_attributes.len(), 3);
    assert_eq!(type_def.variant_attributes[0].len(), 1);
    assert_eq!(type_def.variant_attributes[0][0].path.0, ustr("default"));
    assert!(type_def.variant_attributes[0][0].items.is_empty());
    assert_eq!(type_def.variant_attributes[1].len(), 1);
    assert_eq!(type_def.variant_attributes[1][0].path.0, ustr("doc"));
    assert_eq!(type_def.variant_attributes[2].len(), 0);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn function_attributes_are_parsed() {
    let module = parse_module_ast(indoc! { r#"
        #[flag]
        #[path(name = "value")]
        fn with_attributes() {}
    "# });

    let attributes = &module.functions[0].attributes;
    assert_eq!(attributes.len(), 2);
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
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn function_attributes_are_preserved_in_hir_metadata() {
    let mut session = TestSession::new();
    let attributes = session
        .compile_and_get_module(indoc! { r#"
            #[flag]
            fn with_attributes() {}
        "# })
        .get_function(ustr("with_attributes"))
        .unwrap()
        .definition
        .attributes
        .clone();

    assert_eq!(attributes.len(), 1);
    assert_eq!(attributes[0].path.0, ustr("flag"));
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn place_result_attribute_is_rejected_in_user_code() {
    let mut session = TestSession::new();
    match session
        .fail_compilation(indoc! { r#"
            #[place_result]
            fn f() {}
        "# })
        .into_inner()
    {
        CompilationErrorImpl::UnsafeFeatureUseNotAllowed { feature, .. } => {
            assert_eq!(
                feature,
                UnsafeFeature::FunctionAttribute(ustr("place_result"))
            );
        }
        other => panic!("expected unsafe feature error, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn no_fuel_check_attribute_is_rejected_in_user_code() {
    let mut session = TestSession::new();
    match session
        .fail_compilation(indoc! { r#"
            #[no_fuel_check]
            fn f() {}
        "# })
        .into_inner()
    {
        CompilationErrorImpl::UnsafeFeatureUseNotAllowed { feature, .. } => {
            assert_eq!(
                feature,
                UnsafeFeature::FunctionAttribute(ustr("no_fuel_check"))
            );
        }
        other => panic!("expected unsafe feature error, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn place_result_attribute_is_preserved_as_function_flag_in_std_context() {
    let module = compile_std_module(indoc! { r#"
        #[place_result]
        fn f() {}
    "# });
    let definition = &module.get_function(ustr("f")).unwrap().definition;
    assert!(definition.returns_place);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn place_result_attribute_rejects_arguments_in_std_context() {
    let session = TestSession::new();
    let source_id = session.source_table().next_id();
    let (module_ast, _, arena) = parse_module_and_expr(
        indoc! { r#"
            #[place_result(note = "nope")]
            fn f() {}
        "# },
        source_id,
        true,
    )
    .expect("std-context module should parse");
    let module_id = ModuleId(0);
    match emit_module(
        module_ast,
        &arena,
        module_id,
        raw_modules(session.session()),
        EmitModuleFrom::Uses(Uses::default()),
    )
    .unwrap_err()
    .into_inner()
    {
        CompilationErrorImpl::InvalidAttribute {
            attribute_name,
            target,
            kind,
            ..
        } => {
            assert_eq!(attribute_name, ustr("place_result"));
            assert_eq!(target, AttributeTarget::Function { name: ustr("f") });
            assert_eq!(kind, InvalidAttributeKind::HasArguments);
        }
        other => panic!("expected invalid attribute error, got {other:?}"),
    }
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn place_result_attribute_rejects_duplicates_in_std_context() {
    let session = TestSession::new();
    let source_id = session.source_table().next_id();
    let (module_ast, _, arena) = parse_module_and_expr(
        indoc! { r#"
            #[place_result]
            #[place_result]
            fn f() {}
        "# },
        source_id,
        true,
    )
    .expect("std-context module should parse");
    let module_id = ModuleId(0);
    match emit_module(
        module_ast,
        &arena,
        module_id,
        raw_modules(session.session()),
        EmitModuleFrom::Uses(Uses::default()),
    )
    .unwrap_err()
    .into_inner()
    {
        CompilationErrorImpl::InvalidAttribute {
            attribute_name,
            target,
            kind,
            ..
        } => {
            assert_eq!(attribute_name, ustr("place_result"));
            assert_eq!(target, AttributeTarget::Function { name: ustr("f") });
            assert_eq!(kind, InvalidAttributeKind::Duplicate);
        }
        other => panic!("expected invalid attribute error, got {other:?}"),
    }
}
