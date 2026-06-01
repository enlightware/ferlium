// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use ferlium::{
    CompilerSession, FxHashSet, Location, ModuleAndExpr, SourceTable,
    compiler::{
        error::{CompilationError, RuntimeErrorKind},
        test_support::raw_modules,
    },
    containers::IntoSVec2,
    eval::{ControlFlow, EvalResult, RuntimeError, eval_node},
    hir::function::{
        BinaryNativeFnNNV, BinaryNativeFnRMN, BinaryNativeFnRRN, BinaryNativeFnRWN, Function,
        FunctionDefinition, NullaryNativeFnN, NullaryNativeFnV, UnaryNativeFnMN, UnaryNativeFnNN,
        UnaryNativeFnNV, UnaryNativeFnRN, UnaryNativeFnVN, UnaryNativeFnVV,
    },
    hir::value::{LiteralValue, NativeDisplay, Value},
    hir::{CompiledExpr, test_support::emit_expr_unsafe},
    module::{BlanketTraitImplSubKey, Module, ModuleEnv, ModuleId, Path, TraitId},
    parse_module_and_expr,
    std::core_traits_names::{ITERATOR_TRAIT_NAME, VALUE_TRAIT_NAME},
    std::{
        array::{array_type, array_value_from_vec},
        buffer::Buffer,
        logic::bool_type,
        math::int_type,
        new_module_using_std,
        string::string_type,
    },
    types::effects::{PrimitiveEffect, effect, effects, no_effects},
    types::r#trait::Trait,
    types::r#type::{
        FnType, Type, TypeDef, TypeDefProductDocs, TypeDefShapeDocs, TypeVar, variant_type,
    },
    types::type_scheme::{PubTypeConstraint, TypeScheme},
};
use std::{cell::RefCell, sync::atomic::AtomicIsize};
use ustr::ustr;

#[derive(Debug)]
pub enum Error {
    Compilation(CompilationError),
    Runtime(RuntimeError),
}

pub type CompileRunResult = Result<Value, Error>;

fn compare_native_values(actual: &Value, expected: &Value, path: &str) -> Result<(), String> {
    if actual.as_primitive_ty::<()>().is_some() && expected.as_primitive_ty::<()>().is_some() {
        return Ok(());
    }

    if let (Some(actual), Some(expected)) = (
        actual.as_primitive_ty::<bool>(),
        expected.as_primitive_ty::<bool>(),
    ) {
        return if actual == expected {
            Ok(())
        } else {
            Err(format!("{path}: expected {expected}, got {actual}"))
        };
    }

    if let (Some(actual), Some(expected)) = (
        actual.as_primitive_ty::<isize>(),
        expected.as_primitive_ty::<isize>(),
    ) {
        return if actual == expected {
            Ok(())
        } else {
            Err(format!("{path}: expected {expected}, got {actual}"))
        };
    }

    if let (Some(actual), Some(expected)) = (
        actual.as_primitive_ty::<ferlium::std::math::Float>(),
        expected.as_primitive_ty::<ferlium::std::math::Float>(),
    ) {
        return if actual == expected {
            Ok(())
        } else {
            Err(format!("{path}: expected {expected}, got {actual}"))
        };
    }

    if let (Some(actual), Some(expected)) = (
        actual.as_primitive_ty::<ferlium::std::string::String>(),
        expected.as_primitive_ty::<ferlium::std::string::String>(),
    ) {
        return if actual == expected {
            Ok(())
        } else {
            Err(format!("{path}: expected {expected}, got {actual}"))
        };
    }

    if let (Some(actual), Some(expected)) = (
        actual.as_primitive_ty::<Buffer>(),
        expected.as_primitive_ty::<Buffer>(),
    ) {
        if actual.capacity() != expected.capacity() {
            return Err(format!(
                "{path}: expected buffer capacity {}, got {}",
                expected.capacity(),
                actual.capacity()
            ));
        }
        for index in 0..actual.capacity() {
            compare_values(
                actual.get(index).unwrap(),
                expected.get(index).unwrap(),
                &format!("{path}[{index}]"),
            )?;
        }
        return Ok(());
    }

    Err(format!(
        "{path}: unsupported native comparison between {} and {}",
        actual.to_string_repr(),
        expected.to_string_repr()
    ))
}

fn ferlium_array_parts(value: &Value) -> Option<(&Buffer, usize, usize)> {
    let Value::Tuple(fields) = value else {
        return None;
    };
    if fields.len() != 4 {
        return None;
    }
    let buffer = fields[1].as_primitive_ty::<Buffer>()?;
    let len = usize::try_from(*fields[2].as_primitive_ty::<isize>()?).ok()?;
    let start = usize::try_from(*fields[3].as_primitive_ty::<isize>()?).ok()?;
    Some((buffer, len, start))
}

fn compare_ferlium_arrays(
    actual: &Value,
    expected: &Value,
    path: &str,
) -> Option<Result<(), String>> {
    let (actual_buffer, actual_len, actual_start) = ferlium_array_parts(actual)?;
    let (expected_buffer, expected_len, expected_start) = ferlium_array_parts(expected)?;
    Some((|| {
        if actual_len != expected_len {
            return Err(format!(
                "{path}: expected array length {expected_len}, got {actual_len}"
            ));
        }
        for index in 0..actual_len {
            let actual_capacity = actual_buffer.capacity();
            let expected_capacity = expected_buffer.capacity();
            let actual_physical = if actual_capacity == 0 {
                0
            } else {
                (actual_start + index) % actual_capacity
            };
            let expected_physical = if expected_capacity == 0 {
                0
            } else {
                (expected_start + index) % expected_capacity
            };
            compare_values(
                actual_buffer.get(actual_physical).unwrap(),
                expected_buffer.get(expected_physical).unwrap(),
                &format!("{path}[{index}]"),
            )?;
        }
        Ok(())
    })())
}

fn compare_tuple_values(actual: &Value, expected: &Value, path: &str) -> Result<(), String> {
    let (Value::Tuple(actual), Value::Tuple(expected)) = (actual, expected) else {
        panic!("compare_tuple_values called for non-tuple values");
    };
    if actual.len() != expected.len() {
        return Err(format!(
            "{path}: expected tuple length {}, got {}",
            expected.len(),
            actual.len()
        ));
    }
    for (index, (actual, expected)) in actual.iter().zip(expected.iter()).enumerate() {
        compare_values(actual, expected, &format!("{path}.{index}"))?;
    }
    Ok(())
}

pub(crate) fn compare_values(actual: &Value, expected: &Value, path: &str) -> Result<(), String> {
    match (actual, expected) {
        (Value::Tuple(_), Value::Tuple(_)) => {
            if let Some(result) = compare_ferlium_arrays(actual, expected, path) {
                return result;
            }
            compare_tuple_values(actual, expected, path)
        }
        (Value::Tuple(_), Value::Native(_)) => Err(format!(
            "{path}: expected {}, got {}",
            expected.to_string_repr(),
            actual.to_string_repr()
        )),
        (Value::Native(_), Value::Tuple(_)) => Err(format!(
            "{path}: expected {}, got {}",
            expected.to_string_repr(),
            actual.to_string_repr()
        )),
        (Value::Native(_), Value::Native(_)) => compare_native_values(actual, expected, path),
        (Value::Variant(actual), Value::Variant(expected)) => {
            if actual.tag != expected.tag {
                return Err(format!(
                    "{path}: expected variant tag {}, got {}",
                    expected.tag, actual.tag
                ));
            }
            compare_values(
                &actual.value,
                &expected.value,
                &format!("{path}.{}", actual.tag),
            )
        }
        (Value::Function(actual), Value::Function(expected)) => {
            if actual.function_id != expected.function_id {
                return Err(format!(
                    "{path}: expected function id {}, got {}",
                    expected.function_id, actual.function_id
                ));
            }
            if actual.module_id != expected.module_id {
                return Err(format!(
                    "{path}: expected module {}, got {}",
                    expected.module_id, actual.module_id
                ));
            }
            if actual.hidden_args.len() != expected.hidden_args.len() {
                return Err(format!(
                    "{path}: expected {} hidden metadata values, got {}",
                    expected.hidden_args.len(),
                    actual.hidden_args.len()
                ));
            }
            let actual_captures = actual.closure_env_values();
            let expected_captures = expected.closure_env_values();
            if actual_captures.len() != expected_captures.len() {
                return Err(format!(
                    "{path}: expected {} captured values, got {}",
                    expected_captures.len(),
                    actual_captures.len()
                ));
            }
            for (index, (actual, expected)) in actual_captures
                .iter()
                .zip(expected_captures.iter())
                .enumerate()
            {
                compare_values(actual, expected, &format!("{path}.captured[{index}]"))?;
            }
            Ok(())
        }
        _ => Err(format!(
            "{path}: expected {}, got {}",
            expected.to_string_repr(),
            actual.to_string_repr()
        )),
    }
}

pub fn assert_value_eq(actual: &Value, expected: &Value) {
    if let Err(message) = compare_values(actual, expected, "value") {
        panic!(
            "Value assertion failed: {message}\nactual: {}\nexpected: {}",
            actual.to_string_repr(),
            expected.to_string_repr()
        );
    }
}

pub fn assert_some_value_eq(actual: Option<Value>, expected: Value) {
    let actual = actual.expect("expected Some(value)");
    assert_value_eq(&actual, &expected)
}

#[macro_export]
macro_rules! assert_val_eq {
    ($actual:expr, $expected:expr, $($arg:tt)+) => {{
        let actual = $actual;
        let expected = $expected;
        if let Err(message) = $crate::harness::compare_values(&actual, &expected, "value") {
            panic!(
                "Value assertion failed: {message}\nactual: {}\nexpected: {}\n{}",
                actual.to_string_repr(),
                expected.to_string_repr(),
                format_args!($($arg)+),
            );
        }
    }};
    ($actual:expr, $expected:expr $(,)?) => {{
        let actual = $actual;
        let expected = $expected;
        $crate::harness::assert_value_eq(&actual, &expected);
    }};
}

fn test_assoc_trait() -> Trait {
    Trait::new_with_self_input_type(
        "TestAssoc",
        "Test-only trait with one associated output type.",
        ["Output"],
        [(
            "project",
            FunctionDefinition::new_infer_quantifiers(
                FnType::new_by_val([Type::variable_id(0)], Type::variable_id(1), no_effects()),
                ["value"],
                "Projects a test-only associated output type.",
            ),
        )],
    )
}

fn test_witnessed_project_trait() -> Trait {
    Trait::new_with_self_input_type(
        "TestWitnessedProject",
        "Test-only trait used to exercise structured trait improvement on a non-std trait name.",
        ["Output"],
        [(
            "witness_project",
            FunctionDefinition::new_infer_quantifiers(
                FnType::new_by_val([Type::variable_id(0)], Type::variable_id(1), no_effects()),
                ["value"],
                "Projects the output witnessed by a constrained named type.",
            ),
        )],
    )
}

fn option_type_def() -> TypeDef {
    TypeDef {
        name: ustr("Option"),
        doc: None,
        generic_params: vec![(ustr("T"), Location::new_synthesized())],
        shape: TypeScheme {
            ty_quantifiers: vec![TypeVar::new(0)],
            eff_quantifiers: FxHashSet::default(),
            ty: variant_type([
                ("None", Type::unit()),
                ("Some", Type::tuple([Type::variable_id(0)])),
            ]),
            constraints: vec![],
        },
        shape_docs: TypeDefShapeDocs::Enum(vec![]),
        span: Location::new_synthesized(),
        attributes: vec![],
        default_variant: None,
    }
}

fn map_iterator_type_def(iterator_trait: TraitId) -> TypeDef {
    TypeDef {
        name: ustr("MapIterator"),
        doc: None,
        generic_params: vec![
            (ustr("I"), Location::new_synthesized()),
            (ustr("T"), Location::new_synthesized()),
            (ustr("O"), Location::new_synthesized()),
        ],
        shape: TypeScheme {
            ty_quantifiers: vec![TypeVar::new(0), TypeVar::new(1), TypeVar::new(2)],
            eff_quantifiers: FxHashSet::default(),
            ty: Type::record([
                (ustr("iterator"), Type::variable_id(0)),
                (
                    ustr("mapper"),
                    Type::function_by_val([Type::variable_id(1)], Type::variable_id(2)),
                ),
            ]),
            constraints: vec![PubTypeConstraint::new_have_trait(
                iterator_trait,
                vec![Type::variable_id(0)],
                vec![Type::variable_id(1)],
                Location::new_synthesized(),
            )],
        },
        shape_docs: TypeDefShapeDocs::Struct(TypeDefProductDocs::Record(vec![])),
        span: Location::new_synthesized(),
        attributes: vec![],
        default_variant: None,
    }
}

fn witnessed_type_def(test_assoc_trait: TraitId) -> TypeDef {
    TypeDef {
        name: ustr("Witnessed"),
        doc: None,
        generic_params: vec![
            (ustr("Input"), Location::new_synthesized()),
            (ustr("Output"), Location::new_synthesized()),
        ],
        shape: TypeScheme {
            ty_quantifiers: vec![TypeVar::new(0), TypeVar::new(1)],
            eff_quantifiers: FxHashSet::default(),
            ty: Type::tuple([Type::variable_id(0)]),
            constraints: vec![PubTypeConstraint::new_have_trait(
                test_assoc_trait,
                vec![Type::variable_id(0)],
                vec![Type::variable_id(1)],
                Location::new_synthesized(),
            )],
        },
        shape_docs: TypeDefShapeDocs::Struct(TypeDefProductDocs::Tuple(vec![])),
        span: Location::new_synthesized(),
        attributes: vec![],
        default_variant: None,
    }
}

static TRACKED_CLONES: AtomicIsize = AtomicIsize::new(0);
static TRACKED_DROPS: AtomicIsize = AtomicIsize::new(0);

#[derive(Debug)]
pub struct CloneTrackedNative(isize);

impl Clone for CloneTrackedNative {
    fn clone(&self) -> Self {
        TRACKED_CLONES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Self(self.0)
    }
}

impl NativeDisplay for CloneTrackedNative {
    fn fmt_repr(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "clone_tracked({})", self.0)
    }
}

fn make_clone_tracked() -> CloneTrackedNative {
    CloneTrackedNative(7)
}

fn clone_tracked_payload(value: &CloneTrackedNative) -> isize {
    value.0
}

fn reset_clone_tracked_clones() {
    TRACKED_CLONES.store(0, std::sync::atomic::Ordering::Relaxed);
}

fn clone_tracked_clone_count() -> isize {
    TRACKED_CLONES.load(std::sync::atomic::Ordering::Relaxed)
}

fn equal_clone_tracked(left: &CloneTrackedNative, right: &CloneTrackedNative) -> bool {
    left.0 == right.0
}

fn clone_tracked_to_string(value: &CloneTrackedNative) -> ferlium::std::string::String {
    ferlium::std::string::String::new(&format!("clone_tracked({})", value.0))
}

fn hash_clone_tracked(value: &CloneTrackedNative, state: &mut ferlium::std::hash::Hasher) {
    state.write_isize(value.0);
}

fn clone_clone_tracked(source: &CloneTrackedNative, target: &mut Value) {
    *target = Value::native(source.clone());
}

fn drop_clone_tracked(_target: &mut CloneTrackedNative) {}

fn clone_tracked_value_clone_function() -> Function {
    Box::new(BinaryNativeFnRWN::new(clone_clone_tracked)) as Function
}

fn clone_tracked_value_drop_function() -> Function {
    Box::new(UnaryNativeFnMN::new(drop_clone_tracked)) as Function
}

fn record_tracked_drop(value: isize) {
    TRACKED_DROPS
        .fetch_update(
            std::sync::atomic::Ordering::Relaxed,
            std::sync::atomic::Ordering::Relaxed,
            |old| Some(old * 10 + value),
        )
        .unwrap();
}

fn reset_tracked_drops() {
    TRACKED_DROPS.store(0, std::sync::atomic::Ordering::Relaxed);
}

fn tracked_drop_log() -> isize {
    TRACKED_DROPS.load(std::sync::atomic::Ordering::Relaxed)
}

fn testing_module(
    module_id: ModuleId,
    iterator_trait: TraitId,
    value_trait_id: TraitId,
    value_trait_def: &Trait,
) -> Module {
    let mut module = Module::new(module_id);
    let test_assoc_trait = test_assoc_trait();
    let test_witnessed_project_trait = test_witnessed_project_trait();
    let test_assoc_trait_id = TraitId::new(module_id, module.add_trait(test_assoc_trait));
    let test_witnessed_project_trait_id =
        TraitId::new(module_id, module.add_trait(test_witnessed_project_trait));
    let option_type_def = option_type_def();
    let map_iterator_type_def = map_iterator_type_def(iterator_trait);
    let witnessed_type_def = witnessed_type_def(test_assoc_trait_id);
    module.add_concrete_impl_no_locals(
        test_assoc_trait_id,
        [string_type()],
        [int_type()],
        [],
        [
            Box::new(UnaryNativeFnRN::new(|_: &ferlium::std::string::String| {
                0isize
            })) as Function,
        ],
    );
    module.add_concrete_impl_no_locals(
        test_assoc_trait_id,
        [bool_type()],
        [string_type()],
        [],
        [Box::new(UnaryNativeFnNN::new(|value: bool| {
            ferlium::std::string::String::new(if value { "true" } else { "false" })
        })) as Function],
    );
    let option_type_def_id = module.add_type_def(option_type_def.name, option_type_def);
    module.add_type_def(map_iterator_type_def.name, map_iterator_type_def);
    let witnessed_type_def_id = module.add_type_def(witnessed_type_def.name, witnessed_type_def);
    module.add_blanket_impl_no_locals(
        test_witnessed_project_trait_id,
        BlanketTraitImplSubKey {
            input_tys: vec![Type::named(
                witnessed_type_def_id,
                [Type::variable_id(0), Type::variable_id(1)],
            )],
            ty_var_count: 2,
            constraints: vec![PubTypeConstraint::new_have_trait(
                test_assoc_trait_id,
                vec![Type::variable_id(0)],
                vec![Type::variable_id(1)],
                Location::new_synthesized(),
            )],
        },
        vec![Type::variable_id(1)],
        [],
        [Box::new(UnaryNativeFnVV::new(|_value: &Value| Value::unit())) as Function],
    );
    module.add_concrete_impl_for_trait_def_no_locals(
        value_trait_id,
        value_trait_def,
        [Type::primitive::<CloneTrackedNative>()],
        [],
        [
            LiteralValue::new_native(std::mem::size_of::<CloneTrackedNative>() as isize),
            LiteralValue::new_native(std::mem::align_of::<CloneTrackedNative>() as isize),
        ],
        [
            Box::new(BinaryNativeFnRRN::new(equal_clone_tracked)) as Function,
            Box::new(UnaryNativeFnRN::new(clone_tracked_to_string)) as Function,
            Box::new(BinaryNativeFnRMN::new(hash_clone_tracked)) as Function,
            clone_tracked_value_clone_function(),
            clone_tracked_value_drop_function(),
        ],
    );
    module.add_function(
        "some_int".into(),
        UnaryNativeFnNV::description_with_ty(
            |v: isize| Value::tuple_variant(ustr("Some"), [Value::native(v)]),
            ["option"],
            "Wraps an integer into an Option variant.",
            int_type(),
            Type::named(option_type_def_id, [int_type()]),
            no_effects(),
        ),
    );
    let pair_variant_type = variant_type([("Pair", Type::tuple([int_type(), int_type()]))]);
    module.add_function(
        "pair".into(),
        BinaryNativeFnNNV::description_with_ty(
            |a: isize, b: isize| {
                Value::tuple_variant(ustr("Pair"), [Value::native(a), Value::native(b)])
            },
            ["first", "second"],
            "Creates a Pair variant from two integers.",
            int_type(),
            int_type(),
            pair_variant_type,
            no_effects(),
        ),
    );
    module.add_function(
        "make_clone_tracked".into(),
        NullaryNativeFnN::description_with_default_ty(
            make_clone_tracked,
            [],
            "Creates a clone-counting native test value.",
            no_effects(),
        ),
    );
    module.add_function(
        "clone_tracked_payload".into(),
        UnaryNativeFnRN::description_with_default_ty(
            clone_tracked_payload,
            ["value"],
            "Returns the payload of a clone-counting native test value.",
            no_effects(),
        ),
    );
    module.add_function(
        "reset_clone_tracked_clones".into(),
        NullaryNativeFnN::description_with_default_ty(
            reset_clone_tracked_clones,
            [],
            "Resets the clone counter for clone-counting native test values.",
            no_effects(),
        ),
    );
    module.add_function(
        "clone_tracked_clone_count".into(),
        NullaryNativeFnN::description_with_default_ty(
            clone_tracked_clone_count,
            [],
            "Returns the clone counter for clone-counting native test values.",
            no_effects(),
        ),
    );
    module.add_function(
        "record_tracked_drop".into(),
        UnaryNativeFnNN::description_with_default_ty(
            record_tracked_drop,
            ["value"],
            "Records a dropped test value in the drop log.",
            no_effects(),
        ),
    );
    module.add_function(
        "reset_tracked_drops".into(),
        NullaryNativeFnN::description_with_default_ty(
            reset_tracked_drops,
            [],
            "Resets the tracked drop log.",
            no_effects(),
        ),
    );
    module.add_function(
        "tracked_drop_log".into(),
        NullaryNativeFnN::description_with_default_ty(
            tracked_drop_log,
            [],
            "Returns the tracked drop log.",
            no_effects(),
        ),
    );
    module
}

fn test_effect_module(module_id: ModuleId) -> Module {
    let mut module = Module::new(module_id);
    module.add_function(
        "read".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            "Performs a read effect.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "write".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            "Performs a write effect.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_function(
        "read_write".into(),
        NullaryNativeFnN::description_with_default_ty(
            || (),
            [],
            "Performs both read and write effects.",
            effects(&[PrimitiveEffect::Read, PrimitiveEffect::Write]),
        ),
    );
    module.add_function(
        "take_read".into(),
        UnaryNativeFnVN::description_with_in_ty(
            |_value: &Value| (),
            ["value"],
            "Takes a first-class function that performs a read effect, and fake call it.",
            Type::function_type(FnType::new(
                vec![],
                Type::unit(),
                effect(PrimitiveEffect::Read),
            )),
            effect(PrimitiveEffect::Read),
        ),
    );
    module
}

static INT_PROPERTY_VALUE: AtomicIsize = AtomicIsize::new(0);

pub fn set_property_value(value: isize) {
    INT_PROPERTY_VALUE.store(value, std::sync::atomic::Ordering::Relaxed);
}

pub fn get_property_value() -> isize {
    INT_PROPERTY_VALUE.load(std::sync::atomic::Ordering::Relaxed)
}

thread_local! {
    static INT_ARRAY_PROPERTY_VALUE: RefCell<Vec<isize>> = const { RefCell::new(Vec::new()) };
}

pub fn set_array_property_value(value: Value) {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| *cell.borrow_mut() = int_vec_from_array_value(&value));
}

pub fn get_array_property_value() -> Value {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| int_vec_to_array_value(&cell.borrow()))
}

fn get_array_property_value_value() -> Value {
    get_array_property_value()
}

fn set_array_property_value_value_ref(value: &Value) {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| *cell.borrow_mut() = int_vec_from_array_value(value));
}

fn int_vec_to_array_value(value: &[isize]) -> Value {
    let values = value.iter().copied().map(Value::native).collect::<Vec<_>>();
    array_value_from_vec(values)
}

fn int_vec_from_array_value(value: &Value) -> Vec<isize> {
    let (buffer, len, start) =
        ferlium_array_parts(value).expect("test property my_array only stores arrays");
    let mut result = Vec::with_capacity(len);
    for index in 0..len {
        let physical = if buffer.capacity() == 0 {
            0
        } else {
            (start + index) % buffer.capacity()
        };
        let item = *buffer
            .get(physical)
            .unwrap()
            .as_primitive_ty::<isize>()
            .expect("test property my_array only stores ints");
        result.push(item);
    }
    result
}

fn test_property_module(module_id: ModuleId) -> Module {
    let mut module = Module::new(module_id);
    module.add_function(
        "@get my_scope.my_var".into(),
        NullaryNativeFnN::description_with_default_ty(
            get_property_value,
            [],
            "Gets the value of my_scope.my_var.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "@set my_scope.my_var".into(),
        UnaryNativeFnNN::description_with_default_ty(
            set_property_value,
            ["value"],
            "Sets the value of my_scope.my_var.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_function(
        "@get my_scope.my_array".into(),
        NullaryNativeFnV::description_with_ty(
            get_array_property_value_value,
            [],
            "Gets the value of my_scope.my_array.",
            array_type(int_type()),
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "@set my_scope.my_array".into(),
        UnaryNativeFnVN::description_with_in_ty(
            set_array_property_value_value_ref,
            ["value"],
            "Sets the value of my_scope.my_array.",
            array_type(int_type()),
            effect(PrimitiveEffect::Write),
        ),
    );
    module
}

macro_rules! ferlium {
    ($name:expr, $file:literal) => {
        ($name, $file, include_str!($file))
    };
}

fn add_deep_modules(session: &mut CompilerSession) {
    for (name, file, code) in [
        ferlium!("deep::level1", "deep_module1.fer"),
        ferlium!("deep::deeper::level2", "deep_module2.fer"),
    ] {
        let path = Path::new(name.split("::").map(ustr).collect());
        session.compile(code, file, path).unwrap();
    }
}

/// A test session with std, testing, effects and props modules
#[derive(Debug)]
pub struct TestSession {
    session: CompilerSession,
}
impl TestSession {
    /// Create a new test session with std, testing, effects and props modules registered.
    pub fn new() -> Self {
        let mut compiler_session = CompilerSession::new();
        let std_iterator_trait = compiler_session
            .std_module()
            .get_trait_id_str(ITERATOR_TRAIT_NAME)
            .expect("std Iterator trait should be registered");
        let std_value_trait = compiler_session
            .std_module()
            .get_trait_id_str(VALUE_TRAIT_NAME)
            .expect("std Value trait should be registered");
        let testing_module = testing_module(
            compiler_session.modules().next_id(),
            std_iterator_trait,
            std_value_trait,
            compiler_session.std_module().trait_def(std_value_trait),
        );
        compiler_session.register_module(Path::single_str("testing"), testing_module);
        compiler_session.register_module(
            Path::single_str("effects"),
            test_effect_module(compiler_session.modules().next_id()),
        );
        compiler_session.register_module(
            Path::single_str("props"),
            test_property_module(compiler_session.modules().next_id()),
        );
        add_deep_modules(&mut compiler_session);
        Self {
            session: compiler_session,
        }
    }

    /// Get the compiler session of this test session.
    pub fn session(&self) -> &CompilerSession {
        &self.session
    }

    /// Get a module environment, with an empty module including the standard library
    /// for debugging purposes.
    pub fn std_module_env(&self) -> ModuleEnv<'_> {
        self.session.module_env()
    }

    pub fn std_trait(&self, name: &str) -> TraitId {
        self.session
            .module_env()
            .get_trait_id((ustr(name), Location::new_synthesized()))
            .expect("standard trait lookup should succeed")
            .unwrap_or_else(|| panic!("Standard trait `{name}` not found"))
    }

    /// Get the source table for this compilation session.
    pub fn source_table(&self) -> &SourceTable {
        &self.session.source_table()
    }

    /// Parse a type from a source code and return the corresponding fully-defined Type.
    pub fn resolve_defined_type(&mut self, src: &str) -> Result<Type, CompilationError> {
        self.session.resolve_defined_type_with_std("<test>", src)
    }

    /// Resolve a generic type from a source code and return the corresponding Type,
    /// with placeholder filled with first generic variable.
    pub fn resolve_holed_type(&mut self, src: &str) -> Result<Type, CompilationError> {
        self.session.resolve_holed_type_with_std("<test>", src)
    }

    /// Compile and run the src and return its module and expression
    pub fn try_compile(&mut self, src: &str) -> Result<ModuleAndExpr, CompilationError> {
        self.session
            .compile(src, "<test>", Path::single_str("test"))
    }

    /// Compile and run the src with a custom module name and return its module and expression
    pub fn try_compile_module(
        &mut self,
        name: &str,
        src: &str,
    ) -> Result<ModuleAndExpr, CompilationError> {
        self.session.compile(src, name, Path::single_str(name))
    }

    /// Compile the src and return its module and expression
    pub fn compile(&mut self, src: &str) -> ModuleAndExpr {
        self.try_compile(src)
            .unwrap_or_else(|error| panic!("Compilation error: {error:?}"))
    }

    /// Compile an expression with unstable features enabled.
    pub fn compile_unstable_expr(&mut self, src: &str) -> CompiledExpr {
        let source_id = self.session.source_table().next_id();
        let (_module, expr, arena) = parse_module_and_expr(src, source_id, true)
            .unwrap_or_else(|errors| panic!("Parsing error: {errors:?}"));
        let mut module = new_module_using_std(self.session.modules().next_id());
        emit_expr_unsafe(
            expr.expect("Expected an expression"),
            &arena,
            &mut module,
            raw_modules(&self.session),
            vec![],
        )
        .unwrap_or_else(|error| panic!("Compilation error: {error:?}"))
    }

    /// Compile and get the module of the src
    pub fn compile_and_get_module(&mut self, src: &str) -> &Module {
        let module_id = self.compile(src).module_id;
        self.session.expect_fresh_module(module_id)
    }

    /// Compile and get a specific function definition
    pub fn compile_and_get_fn_def(&mut self, src: &str, fn_name: &str) -> FunctionDefinition {
        let module = self.compile_and_get_module(src);
        module
            .get_function(ustr(fn_name))
            .expect("Function not found")
            .definition
            .clone()
    }

    /// Compile and run the src and return its execution result (either a value or an error)
    pub fn try_compile_and_run(&mut self, src: &str) -> CompileRunResult {
        // Compile the source.
        let ModuleAndExpr { module_id, expr } =
            self.try_compile(src).map_err(Error::Compilation)?;

        // Run the expression if any.
        if let Some(expr) = expr {
            let arena = &self.session.expect_fresh_module(module_id).ir_arena;
            eval_node(arena, expr.expr, module_id, &expr.locals, &self.session)
                .map(ControlFlow::into_value)
                .map_err(Error::Runtime)
        } else {
            Ok(Value::unit())
        }
    }

    /// Compile and run the src and return its execution result (either a value or an error)
    pub fn try_run(&mut self, src: &str) -> EvalResult {
        self.try_compile_and_run(src).map_err(|error| match error {
            Error::Compilation(error) => panic!("Compilation error: {error:?}"),
            Error::Runtime(error) => error,
        })
    }

    /// Compile and run the src and return its value
    pub fn run(&mut self, src: &str) -> Value {
        self.try_run(src)
            .unwrap_or_else(|error| panic!("Runtime error: {error:?}"))
    }

    /// Compile and run the src and expect a runtime error
    pub fn fail_run(&mut self, src: &str) -> RuntimeErrorKind {
        match self.try_run(src) {
            Ok(value) => panic!(
                "Expected runtime error, got value: {}",
                value.to_string_repr()
            ),
            Err(error) => error.kind(),
        }
    }

    /// Compile and expect a check error
    pub fn fail_compilation(&mut self, src: &str) -> CompilationError {
        match self.try_compile_and_run(src) {
            Ok(value) => panic!(
                "Expected compilation error, got value: {}",
                value.to_string_repr()
            ),
            Err(error) => match error {
                Error::Compilation(error) => error,
                _ => panic!("Expected compilation error, got {error:?}"),
            },
        }
    }

    pub fn default_value_for_type(&mut self, ty: Type) -> Option<Value> {
        self.session.default_value_for_type(ty)
    }
}

// helper functions to construct values easily to make tests more readable

/// The value of type unit
pub fn unit() -> Value {
    Value::unit()
}

/// A primitive boolean value
pub fn bool(b: bool) -> Value {
    Value::native(b)
}

/// A primitive integer value
pub fn int(n: isize) -> Value {
    Value::native(n)
}

/// A primitive float value
pub fn float(f: f64) -> Value {
    Value::native(ferlium::std::math::Float::new(f).unwrap())
}

/// A primitive string value
pub fn string(s: &str) -> Value {
    use std::str::FromStr;
    Value::native(ferlium::std::string::String::from_str(s).unwrap())
}
/// A variant value of given tag and no values
pub fn variant_0(tag: &str) -> Value {
    Value::unit_variant(ustr(tag))
}

/// A variant value of given tag and exactly 1 value
pub fn variant_t1(tag: &str, value: Value) -> Value {
    Value::tuple_variant(ustr(tag), [value])
}

/// A variant value of given tag and N values
pub fn variant_tn(tag: &str, values: impl IntoSVec2<Value>) -> Value {
    Value::tuple_variant(ustr(tag), values)
}

// macros to construct values easily to make tests more readable

/// An array of boolean values
#[macro_export]
macro_rules! bool_a {
    [] => {
        ferlium::std::array::array_value_from_vec(vec![])
    };
    [$($elem:expr),+ $(,)?] => {
        {
            let values = vec![
            $(Value::native::<bool>($elem)),+
            ];
            ferlium::std::array::array_value_from_vec(values)
        }
    };
}

/// An array of integer values
#[macro_export]
macro_rules! int_a {
    [] => {
        ferlium::std::array::array_value_from_vec(vec![])
    };
    [$($elem:expr),+ $(,)?] => {
        {
            let values = vec![
            $(Value::native::<ferlium::std::math::Int>($elem)),+
            ];
            ferlium::std::array::array_value_from_vec(values)
        }
    };
}

/// An array of float values
#[macro_export]
macro_rules! float_a {
    [] => {
        ferlium::std::array::array_value_from_vec(vec![])
    };
    [$($elem:expr),+ $(,)?] => {
        {
            let values = vec![
            $(Value::native::<ferlium::std::math::Float>(ferlium::std::math::Float::new($elem).unwrap())),+
            ];
            ferlium::std::array::array_value_from_vec(values)
        }
    };
}

/// A tuple of integer values
#[macro_export]
macro_rules! int_tuple {
    () => {
        Value::tuple(vec![])
    };
    ($($elem:expr),+ $(,)?) => {
        Value::tuple(vec![
            $(Value::native::<ferlium::std::math::Int>($elem)),+
        ])
    };
}

/// An tuple of values
#[macro_export]
macro_rules! tuple {
    () => {
        Value::tuple([])
    };
    ($($elem:expr),+ $(,)?) => {
        Value::tuple(vec![
            $($elem),+
        ])
    };
}

/// An array of values
#[macro_export]
macro_rules! array {
    [] => {
        ferlium::std::array::array_value_from_vec(vec![])
    };
    [$($elem:expr),+ $(,)?] => {
        {
            let values = vec![
            $($elem),+
            ];
            ferlium::std::array::array_value_from_vec(values)
        }
    };
}
