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
    compiler::error::{CompilationError, RuntimeErrorKind},
    eval::{ControlFlow, EvalResult, RuntimeError, eval_node},
    hir::function::{
        BinaryNativeFnNNV, BinaryNativeFnRMN, BinaryNativeFnRRN, CallableDefinition, Function,
        NullaryNativeFnN, NullaryNativeFnV, UnaryNativeFnMN, UnaryNativeFnNN, UnaryNativeFnNV,
        UnaryNativeFnRN, UnaryNativeFnVN, UnaryNativeFnVV,
    },
    hir::value::{LiteralValue, NativeValueType, Value},
    module::{BlanketTraitImplSubKey, Module, ModuleEnv, ModuleId, Path, TraitId},
    std::core_traits_names::{ITERATOR_TRAIT_NAME, VALUE_TRAIT_NAME},
    std::{
        array::{array_type, array_value_from_vec},
        buffer::Buffer,
        logic::bool_type,
        math::int_type,
        string::string_type,
    },
    types::effects::{EffType, EffectVar, PrimitiveEffect, effect, effects, no_effects},
    types::r#trait::Trait,
    types::r#type::{
        FnType, Type, TypeDef, TypeDefProductDocs, TypeDefShapeDocs, TypeVar, variant_type,
    },
    types::type_scheme::{PubTypeConstraint, TypeScheme},
};
use std::{cell::RefCell, fmt, sync::atomic::AtomicIsize};
use ustr::ustr;

#[derive(Debug)]
pub enum Error {
    Compilation(CompilationError),
    Runtime(RuntimeError),
}

pub type CompileRunResult = Result<Value, Error>;
pub type CompileRunValueResult = Result<RunValue, Error>;

#[derive(Debug)]
pub struct RunValue {
    pub module_id: ModuleId,
    pub value: Value,
    pub ty: Type,
}

#[derive(Debug)]
pub struct ExpectedValue {
    pub value: Value,
    pub ty: Option<Type>,
}

impl ExpectedValue {
    pub fn raw(value: Value) -> Self {
        Self { value, ty: None }
    }

    pub fn typed(value: Value, ty: Type) -> Self {
        Self {
            value,
            ty: Some(ty),
        }
    }

    pub fn as_value(&self) -> &Value {
        &self.value
    }

    pub fn into_value(self) -> Value {
        self.value
    }
}

impl From<Value> for ExpectedValue {
    fn from(value: Value) -> Self {
        Self::raw(value)
    }
}

pub fn raw_value(value: impl Into<ExpectedValue>) -> Value {
    value.into().into_value()
}

fn value_shape(value: &Value) -> &'static str {
    match value {
        Value::Uninit => "uninitialized value",
        Value::Native(_) => "native value",
        Value::Variant(_) => "variant value",
        Value::Tuple(_) => "tuple value",
        Value::Function(_) => "function value",
    }
}

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

    Err(format!("{path}: unsupported native comparison"))
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
            value_shape(expected),
            value_shape(actual)
        )),
        (Value::Native(_), Value::Tuple(_)) => Err(format!(
            "{path}: expected {}, got {}",
            value_shape(expected),
            value_shape(actual)
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
            if actual.function != expected.function {
                return Err(format!(
                    "{path}: expected function {:?}, got {:?}",
                    expected.function, actual.function
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
            value_shape(expected),
            value_shape(actual)
        )),
    }
}

pub fn assert_value_eq(actual: &Value, expected: &Value) {
    if let Err(message) = compare_values(actual, expected, "value") {
        panic!("Value assertion failed: {message}");
    }
}

pub fn assert_some_value_eq(actual: Option<Value>, expected: impl Into<ExpectedValue>) {
    let actual = actual.expect("expected Some(value)");
    let expected = expected.into();
    assert_value_eq(&actual, expected.as_value())
}

#[macro_export]
macro_rules! assert_val_eq {
    ($session:ident . run($src:expr), $expected:expr, $($arg:tt)+) => {{
        let expected = $expected;
        $session.assert_run_value_eq_with_message($src, expected, format_args!($($arg)+));
    }};
    ($session:ident . run($src:expr), $expected:expr $(,)?) => {{
        let expected = $expected;
        $session.assert_run_value_eq($src, expected);
    }};
    ($actual:expr, $expected:expr, $($arg:tt)+) => {{
        let actual = $actual;
        let expected: $crate::harness::ExpectedValue = $expected.into();
        if let Err(message) = $crate::harness::compare_values(&actual, expected.as_value(), "value") {
            panic!(
                "Value assertion failed: {message}\n{}",
                format_args!($($arg)+),
            );
        }
    }};
    ($actual:expr, $expected:expr $(,)?) => {{
        let actual = $actual;
        let expected: $crate::harness::ExpectedValue = $expected.into();
        $crate::harness::assert_value_eq(&actual, expected.as_value());
    }};
}

/// Replaces every interned-id marker of the form `<number-number>` (e.g. `<0-6>`, `<0-4043>`) with
/// `...`, so that textual assertions don't flake on the non-deterministic ids embedded in dumps.
pub(crate) fn replace_flaky_ids(s: impl AsRef<str>) -> String {
    let s = s.as_ref();
    let bytes = s.as_bytes();
    let mut result = String::with_capacity(s.len());
    let mut i = 0;
    let mut segment_start = 0;
    while i < bytes.len() {
        // Try to match `<digits-digits>` starting at `i`.
        if bytes[i] == b'<' {
            let mut j = i + 1;
            let first_digits = j;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > first_digits && j < bytes.len() && bytes[j] == b'-' {
                j += 1;
                let second_digits = j;
                while j < bytes.len() && bytes[j].is_ascii_digit() {
                    j += 1;
                }
                if j > second_digits && j < bytes.len() && bytes[j] == b'>' {
                    result.push_str(&s[segment_start..i]);
                    result.push_str("<...>");
                    i = j + 1;
                    segment_start = i;
                    continue;
                }
            }
        }
        i += 1;
    }
    result.push_str(&s[segment_start..]);
    result
}

/// Like `assert_eq!`, but first replaces every interned-id marker (`<number-number>`) in both sides
/// with `...`, so the comparison ignores non-deterministic ids that would otherwise cause flakes.
#[macro_export]
macro_rules! assert_eq_sans_flake {
    ($lhs:expr, $rhs:expr $(,)?) => {{
        let lhs = $crate::harness::replace_flaky_ids($lhs);
        let rhs = $crate::harness::replace_flaky_ids($rhs);
        assert_eq!(lhs, rhs);
    }};
    ($lhs:expr, $rhs:expr, $($arg:tt)+) => {{
        let lhs = $crate::harness::replace_flaky_ids($lhs);
        let rhs = $crate::harness::replace_flaky_ids($rhs);
        assert_eq!(lhs, rhs, $($arg)+);
    }};
}

fn test_assoc_trait() -> Trait {
    Trait::new_with_self_input_type(
        "TestAssoc",
        "Test-only trait with one associated output type.",
        ["Output"],
        [(
            "project",
            CallableDefinition::new_infer_quantifiers(
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
            CallableDefinition::new_infer_quantifiers(
                FnType::new_by_val([Type::variable_id(0)], Type::variable_id(1), no_effects()),
                ["value"],
                "Projects the output witnessed by a constrained named type.",
            ),
        )],
    )
}

fn test_eff_trait() -> Trait {
    Trait::new_with_self_input_type(
        "TestEff",
        "Test-only trait with one associated output type and one output effect.",
        ["Output"],
        [(
            "eff_project",
            CallableDefinition::new_infer_quantifiers(
                FnType::new_by_val(
                    [Type::variable_id(0)],
                    Type::variable_id(1),
                    EffType::single_variable_id(0),
                ),
                ["value"],
                "Projects a test-only associated output type with a trait-determined effect.",
            ),
        )],
    )
    .with_output_effects(["E"])
}

fn test_eff_pair_trait() -> Trait {
    Trait::new_with_self_input_type(
        "TestEffPair",
        "Test-only trait with two output effect slots, each used by one method.",
        Vec::<&str>::new(),
        [
            (
                "eff_pair_first",
                CallableDefinition::new_infer_quantifiers(
                    FnType::new_by_val(
                        [Type::variable_id(0)],
                        int_type(),
                        EffType::single_variable_id(0),
                    ),
                    ["value"],
                    "Projects an int with the effect of the first slot.",
                ),
            ),
            (
                "eff_pair_second",
                CallableDefinition::new_infer_quantifiers(
                    FnType::new_by_val(
                        [Type::variable_id(0)],
                        int_type(),
                        EffType::single_variable_id(1),
                    ),
                    ["value"],
                    "Projects an int with the effect of the second slot.",
                ),
            ),
        ],
    )
    .with_output_effects(["E1", "E2"])
}

fn test_eff_join_trait() -> Trait {
    Trait::new_with_self_input_type(
        "TestEffJoin",
        "Test-only trait whose output effect is derived from multiple trait obligations.",
        Vec::<&str>::new(),
        [(
            "eff_join",
            CallableDefinition::new_infer_quantifiers(
                FnType::new_by_val(
                    [Type::variable_id(0)],
                    int_type(),
                    EffType::single_variable_id(0),
                ),
                ["value"],
                "Projects an int with the joined effect of the input.",
            ),
        )],
    )
    .with_output_effects(["E"])
}

fn option_type_def() -> TypeDef {
    TypeDef {
        name: ustr("Option"),
        doc: None,
        generic_params: vec![(ustr("T"), Location::new_synthesized())],
        generic_effect_params: vec![],
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
        generic_effect_params: vec![],
        shape: TypeScheme {
            ty_quantifiers: vec![TypeVar::new(0), TypeVar::new(1), TypeVar::new(2)],
            eff_quantifiers: [EffectVar::new(0)].into_iter().collect(),
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
                vec![EffType::single_variable_id(0)],
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
        generic_effect_params: vec![],
        shape: TypeScheme {
            ty_quantifiers: vec![TypeVar::new(0), TypeVar::new(1)],
            eff_quantifiers: FxHashSet::default(),
            ty: Type::tuple([Type::variable_id(0)]),
            constraints: vec![PubTypeConstraint::new_have_trait(
                test_assoc_trait,
                vec![Type::variable_id(0)],
                vec![Type::variable_id(1)],
                vec![],
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

impl NativeValueType for CloneTrackedNative {}

impl Clone for CloneTrackedNative {
    fn clone(&self) -> Self {
        TRACKED_CLONES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Self(self.0)
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

fn clone_clone_tracked(source: &CloneTrackedNative) -> CloneTrackedNative {
    source.clone()
}

fn drop_clone_tracked(_target: &mut CloneTrackedNative) {}

fn clone_tracked_value_clone_function() -> Function {
    Box::new(UnaryNativeFnRN::new(clone_clone_tracked)) as Function
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
    let mut module = Module::new(module_id, Path::single_str("testing"));
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
            eff_var_count: 0,
            constraints: vec![PubTypeConstraint::new_have_trait(
                test_assoc_trait_id,
                vec![Type::variable_id(0)],
                vec![Type::variable_id(1)],
                vec![],
                Location::new_synthesized(),
            )],
        },
        vec![Type::variable_id(1)],
        [],
        [Box::new(UnaryNativeFnVV::new(|_value: &Value| Value::unit())) as Function],
    );
    // Test trait with an output effect slot: a pure impl for int, an impl with
    // the read effect for bool, and a blanket impl over Option<T> forwarding
    // the effect of the inner type.
    let test_eff_trait_id = TraitId::new(module_id, module.add_trait(test_eff_trait()));
    module.add_concrete_impl_with_effects_no_locals(
        test_eff_trait_id,
        [int_type()],
        [int_type()],
        [no_effects()],
        [],
        [Box::new(UnaryNativeFnNN::new(|v: isize| v * 2)) as Function],
    );
    module.add_concrete_impl_with_effects_no_locals(
        test_eff_trait_id,
        [bool_type()],
        [int_type()],
        [effect(PrimitiveEffect::Read)],
        [],
        [Box::new(UnaryNativeFnNN::new(
            |v: bool| {
                if v { 1isize } else { 0isize }
            },
        )) as Function],
    );
    module.add_concrete_impl_with_effects_no_locals(
        test_eff_trait_id,
        [string_type()],
        [int_type()],
        [effect(PrimitiveEffect::Write)],
        [],
        [
            Box::new(UnaryNativeFnRN::new(|_: &ferlium::std::string::String| {
                0isize
            })) as Function,
        ],
    );
    module.add_blanket_impl_with_effects_no_locals(
        test_eff_trait_id,
        BlanketTraitImplSubKey {
            input_tys: vec![Type::named(option_type_def_id, [Type::variable_id(0)])],
            ty_var_count: 2,
            eff_var_count: 0,
            constraints: vec![PubTypeConstraint::new_have_trait(
                test_eff_trait_id,
                vec![Type::variable_id(0)],
                vec![Type::variable_id(1)],
                vec![EffType::single_variable_id(0)],
                Location::new_synthesized(),
            )],
        },
        vec![Type::variable_id(1)],
        vec![EffType::single_variable_id(0)],
        [],
        [Box::new(UnaryNativeFnVV::new(|_value: &Value| Value::unit())) as Function],
    );
    // Test trait with two output effect slots: the bool impl has different
    // effects in each slot, so any slot transposition swaps the methods'
    // effects and is caught by the tests.
    let test_eff_pair_trait_id = TraitId::new(module_id, module.add_trait(test_eff_pair_trait()));
    module.add_concrete_impl_with_effects_no_locals(
        test_eff_pair_trait_id,
        [bool_type()],
        [],
        [
            effect(PrimitiveEffect::Read),
            effect(PrimitiveEffect::Write),
        ],
        [],
        [
            Box::new(UnaryNativeFnNN::new(
                |v: bool| {
                    if v { 1isize } else { 0isize }
                },
            )) as Function,
            Box::new(UnaryNativeFnNN::new(
                |v: bool| {
                    if v { 2isize } else { 0isize }
                },
            )) as Function,
        ],
    );
    let test_eff_join_trait_id = TraitId::new(module_id, module.add_trait(test_eff_join_trait()));
    module.add_blanket_impl_with_effects_no_locals(
        test_eff_join_trait_id,
        BlanketTraitImplSubKey {
            input_tys: vec![Type::tuple([Type::variable_id(0), Type::variable_id(1)])],
            ty_var_count: 4,
            eff_var_count: 0,
            constraints: vec![
                PubTypeConstraint::new_have_trait(
                    test_eff_trait_id,
                    vec![Type::variable_id(0)],
                    vec![Type::variable_id(2)],
                    vec![EffType::single_variable_id(1)],
                    Location::new_synthesized(),
                ),
                PubTypeConstraint::new_have_trait(
                    test_eff_trait_id,
                    vec![Type::variable_id(1)],
                    vec![Type::variable_id(3)],
                    vec![EffType::single_variable_id(2)],
                    Location::new_synthesized(),
                ),
            ],
        },
        [],
        [EffType::single_variable_id(1).union(&EffType::single_variable_id(2))],
        [],
        [Box::new(UnaryNativeFnVN::new(|_value: &Value| 0isize)) as Function],
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
    module.add_function(
        "some_bool".into(),
        UnaryNativeFnNV::description_with_ty(
            |v: bool| Value::tuple_variant(ustr("Some"), [Value::native(v)]),
            ["option"],
            "Wraps a boolean into an Option variant.",
            bool_type(),
            Type::named(option_type_def_id, [bool_type()]),
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
    let mut module = Module::new(module_id, Path::single_str("effects"));
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

pub fn set_array_property_value(value: impl Into<ExpectedValue>) {
    let value = raw_value(value);
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
    let mut module = Module::new(module_id, Path::single_str("props"));
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

    pub fn allow_experimental(&mut self) {
        self.session.set_allow_experimental(true);
    }

    /// Get a module environment, with an empty module including the standard library
    /// for debugging purposes.
    pub fn std_module_env(&self) -> ModuleEnv<'_> {
        self.session.module_env()
    }

    pub fn value_to_string(&mut self, module_id: ModuleId, value: Value, ty: Type) -> String {
        self.session
            .value_to_string(module_id, value, ty)
            .expect("value formatting should succeed")
    }

    pub fn value_to_inspect_text(&mut self, module_id: ModuleId, value: Value, ty: Type) -> String {
        self.session
            .value_to_inspect_text(module_id, value, ty)
            .expect("value inspection should succeed")
    }

    fn value_to_assertion_text(&mut self, module_id: ModuleId, value: Value, ty: Type) -> String {
        self.session
            .value_to_inspect_text(module_id, value, ty)
            .unwrap_or_else(|error| format!("<inspect failed: {error}>"))
    }

    fn assert_run_value_eq_inner(
        &mut self,
        actual: RunValue,
        expected: ExpectedValue,
        extra_message: Option<fmt::Arguments<'_>>,
    ) {
        if let Err(message) = compare_values(&actual.value, expected.as_value(), "value") {
            let RunValue {
                module_id,
                value,
                ty,
            } = actual;
            let expected_ty = expected.ty.unwrap_or_else(|| ty.clone());
            let actual = self.value_to_assertion_text(module_id, value, ty);
            let expected = self.value_to_assertion_text(module_id, expected.value, expected_ty);
            if let Some(extra_message) = extra_message {
                panic!(
                    "Value assertion failed: {message}\nactual: {actual}\nexpected: {expected}\n{extra_message}"
                );
            } else {
                panic!("Value assertion failed: {message}\nactual: {actual}\nexpected: {expected}");
            }
        }
    }

    pub fn assert_run_value_eq(&mut self, src: &str, expected: impl Into<ExpectedValue>) {
        let actual = self.run_value(src);
        self.assert_run_value_eq_inner(actual, expected.into(), None);
    }

    pub fn assert_run_value_eq_with_message(
        &mut self,
        src: &str,
        expected: impl Into<ExpectedValue>,
        message: fmt::Arguments<'_>,
    ) {
        let actual = self.run_value(src);
        self.assert_run_value_eq_inner(actual, expected.into(), Some(message));
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

    pub fn emit_ssa(&mut self, src: &str) -> String {
        self.session.emit_ssa("<test>", src)
    }

    /// Compile the src and return its module and expression
    pub fn compile(&mut self, src: &str) -> ModuleAndExpr {
        self.try_compile(src)
            .unwrap_or_else(|error| panic!("Compilation error: {error:?}"))
    }

    /// Compile and get the module of the src
    pub fn compile_and_get_module(&mut self, src: &str) -> &Module {
        let module_id = self.compile(src).module_id;
        self.session.expect_fresh_module(module_id)
    }

    /// Compile and get a specific function definition
    pub fn compile_and_get_fn_def(&mut self, src: &str, fn_name: &str) -> CallableDefinition {
        let module = self.compile_and_get_module(src);
        module
            .get_function(ustr(fn_name))
            .expect("Function not found")
            .definition
            .clone()
    }

    /// Compile and run the src and return its typed execution result (either a value or an error)
    pub fn try_compile_and_run_value(&mut self, src: &str) -> CompileRunValueResult {
        // Compile the source.
        let ModuleAndExpr { module_id, expr } =
            self.try_compile(src).map_err(Error::Compilation)?;

        // Run the expression if any.
        if let Some(expr) = expr {
            let ty = expr.ty.ty;
            let arena = &self.session.expect_fresh_module(module_id).hir_arena;
            eval_node(arena, expr.expr, module_id, &expr.locals, &self.session)
                .map(ControlFlow::into_value)
                .map(|value| RunValue {
                    module_id,
                    value,
                    ty,
                })
                .map_err(Error::Runtime)
        } else {
            Ok(RunValue {
                module_id,
                value: Value::unit(),
                ty: Type::unit(),
            })
        }
    }

    /// Compile and run the src and return its execution result (either a value or an error)
    pub fn try_compile_and_run(&mut self, src: &str) -> CompileRunResult {
        self.try_compile_and_run_value(src)
            .map(|run_value| run_value.value)
    }

    /// Compile and run the src and return its execution result (either a value or an error)
    pub fn try_run(&mut self, src: &str) -> EvalResult {
        self.try_compile_and_run(src).map_err(|error| match error {
            Error::Compilation(error) => panic!("Compilation error: {error:?}"),
            Error::Runtime(error) => error,
        })
    }

    /// Compile and run the src and return its typed value
    pub fn try_run_value(&mut self, src: &str) -> Result<RunValue, RuntimeError> {
        self.try_compile_and_run_value(src)
            .map_err(|error| match error {
                Error::Compilation(error) => panic!("Compilation error: {error:?}"),
                Error::Runtime(error) => error,
            })
    }

    /// Compile and run the src and return its value
    pub fn run(&mut self, src: &str) -> Value {
        self.try_run(src)
            .unwrap_or_else(|error| panic!("Runtime error: {error:?}"))
    }

    /// Compile and run the src and return its typed value
    pub fn run_value(&mut self, src: &str) -> RunValue {
        self.try_run_value(src)
            .unwrap_or_else(|error| panic!("Runtime error: {error:?}"))
    }

    /// Compile and run the src and expect a runtime error
    pub fn fail_run(&mut self, src: &str) -> RuntimeErrorKind {
        match self.try_run_value(src) {
            Ok(value) => {
                let rendered = self.value_to_assertion_text(value.module_id, value.value, value.ty);
                panic!("Expected runtime error, got value: {rendered}");
            }
            Err(error) => error.kind(),
        }
    }

    /// Compile and expect a check error
    pub fn fail_compilation(&mut self, src: &str) -> CompilationError {
        match self.try_compile_and_run_value(src) {
            Ok(value) => {
                let rendered = self.value_to_assertion_text(value.module_id, value.value, value.ty);
                panic!("Expected compilation error, got value: {rendered}");
            }
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
pub fn unit() -> ExpectedValue {
    ExpectedValue::typed(unit_value(), Type::unit())
}

pub fn unit_value() -> Value {
    Value::unit()
}

/// A primitive boolean value
pub fn bool(b: bool) -> ExpectedValue {
    ExpectedValue::typed(bool_value(b), bool_type())
}

pub fn bool_value(b: bool) -> Value {
    Value::native(b)
}

/// A primitive integer value
pub fn int(n: isize) -> ExpectedValue {
    ExpectedValue::typed(int_value(n), int_type())
}

pub fn int_value(n: isize) -> Value {
    Value::native(n)
}

/// A primitive float value
pub fn float(f: f64) -> ExpectedValue {
    ExpectedValue::typed(float_value(f), ferlium::std::math::float_type())
}

pub fn float_value(f: f64) -> Value {
    Value::native(ferlium::std::math::Float::new(f).unwrap())
}

/// A primitive string value
pub fn string(s: &str) -> ExpectedValue {
    ExpectedValue::typed(string_value(s), string_type())
}

pub fn string_value(s: &str) -> Value {
    use std::str::FromStr;
    Value::native(ferlium::std::string::String::from_str(s).unwrap())
}

/// An expected tuple value. If any field lacks a type, the tuple type is left unknown.
pub fn expected_tuple<I, V>(values: I) -> ExpectedValue
where
    I: IntoIterator<Item = V>,
    V: Into<ExpectedValue>,
{
    let mut raw_values = Vec::new();
    let mut types = Vec::new();
    let mut fully_typed = true;
    for value in values {
        let value = value.into();
        if let Some(ty) = value.ty {
            types.push(ty);
        } else {
            fully_typed = false;
        }
        raw_values.push(value.value);
    }
    let value = Value::tuple(raw_values);
    if fully_typed {
        ExpectedValue::typed(value, Type::tuple(types))
    } else {
        ExpectedValue::raw(value)
    }
}

/// An expected array value with a caller-supplied element type.
pub fn expected_array<I, V>(element_ty: Type, values: I) -> ExpectedValue
where
    I: IntoIterator<Item = V>,
    V: Into<ExpectedValue>,
{
    let values = values.into_iter().map(raw_value).collect();
    ExpectedValue::typed(array_value_from_vec(values), array_type(element_ty))
}

/// An expected array value. If element types are known and uniform, the array type is preserved.
pub fn expected_array_infer<I, V>(values: I) -> ExpectedValue
where
    I: IntoIterator<Item = V>,
    V: Into<ExpectedValue>,
{
    let mut raw_values = Vec::new();
    let mut element_ty: Option<Type> = None;
    let mut fully_typed = true;
    for value in values {
        let value = value.into();
        match (element_ty.as_ref(), value.ty) {
            (None, Some(ty)) => element_ty = Some(ty),
            (Some(element_ty), Some(ty)) if *element_ty == ty => {}
            _ => fully_typed = false,
        }
        raw_values.push(value.value);
    }
    let value = array_value_from_vec(raw_values);
    if fully_typed {
        if let Some(element_ty) = element_ty {
            ExpectedValue::typed(value, array_type(element_ty))
        } else {
            ExpectedValue::raw(value)
        }
    } else {
        ExpectedValue::raw(value)
    }
}

/// A variant value of given tag and no values
pub fn variant_0(tag: &str) -> ExpectedValue {
    ExpectedValue::raw(Value::unit_variant(ustr(tag)))
}

/// A variant value with an exact runtime payload.
pub fn variant_raw(tag: &str, payload: impl Into<ExpectedValue>) -> ExpectedValue {
    ExpectedValue::raw(Value::raw_variant(ustr(tag), raw_value(payload)))
}

/// A variant value with an exact unit runtime payload.
pub fn variant_unit(tag: &str) -> ExpectedValue {
    ExpectedValue::raw(Value::raw_variant(ustr(tag), Value::unit()))
}

/// A variant value of given tag and exactly 1 value
pub fn variant_t1(tag: &str, value: impl Into<ExpectedValue>) -> ExpectedValue {
    ExpectedValue::raw(Value::tuple_variant(ustr(tag), [raw_value(value)]))
}

/// A variant value of given tag and N values
pub fn variant_tn<I, V>(tag: &str, values: I) -> ExpectedValue
where
    I: IntoIterator<Item = V>,
    V: Into<ExpectedValue>,
{
    ExpectedValue::raw(Value::tuple_variant(
        ustr(tag),
        values.into_iter().map(raw_value).collect::<Vec<_>>(),
    ))
}

pub fn none() -> ExpectedValue {
    ExpectedValue::raw(ferlium::std::option::none())
}

pub fn some(value: impl Into<ExpectedValue>) -> ExpectedValue {
    let value = value.into();
    let ty = value.ty.clone().map(ferlium::std::option::option_type);
    ExpectedValue {
        value: ferlium::std::option::some(value.value),
        ty,
    }
}

// macros to construct values easily to make tests more readable

/// An array of boolean values
#[macro_export]
macro_rules! bool_a {
    [] => {
        $crate::harness::expected_array(ferlium::std::logic::bool_type(), Vec::<$crate::harness::ExpectedValue>::new())
    };
    [$($elem:expr),+ $(,)?] => {
        {
            let values = vec![
            $($crate::harness::bool($elem)),+
            ];
            $crate::harness::expected_array(ferlium::std::logic::bool_type(), values)
        }
    };
}

/// An array of integer values
#[macro_export]
macro_rules! int_a {
    [] => {
        $crate::harness::expected_array(ferlium::std::math::int_type(), Vec::<$crate::harness::ExpectedValue>::new())
    };
    [$($elem:expr),+ $(,)?] => {
        {
            let values = vec![
            $($crate::harness::int($elem)),+
            ];
            $crate::harness::expected_array(ferlium::std::math::int_type(), values)
        }
    };
}

/// An array of float values
#[macro_export]
macro_rules! float_a {
    [] => {
        $crate::harness::expected_array(ferlium::std::math::float_type(), Vec::<$crate::harness::ExpectedValue>::new())
    };
    [$($elem:expr),+ $(,)?] => {
        {
            let values = vec![
            $($crate::harness::float($elem)),+
            ];
            $crate::harness::expected_array(ferlium::std::math::float_type(), values)
        }
    };
}

/// A tuple of integer values
#[macro_export]
macro_rules! int_tuple {
    () => {
        $crate::harness::expected_tuple(Vec::<$crate::harness::ExpectedValue>::new())
    };
    ($($elem:expr),+ $(,)?) => {
        $crate::harness::expected_tuple(vec![
            $($crate::harness::int($elem)),+
        ])
    };
}

/// An tuple of values
#[macro_export]
macro_rules! tuple {
    () => {
        $crate::harness::expected_tuple(Vec::<$crate::harness::ExpectedValue>::new())
    };
    ($($elem:expr),+ $(,)?) => {
        $crate::harness::expected_tuple(Vec::<$crate::harness::ExpectedValue>::from([
            $(($elem).into()),+
        ]))
    };
}

/// An array of values
#[macro_export]
macro_rules! array {
    [] => {
        $crate::harness::ExpectedValue::raw(ferlium::std::array::array_value_from_vec(vec![]))
    };
    [$($elem:expr),+ $(,)?] => {
        {
            let values = Vec::<$crate::harness::ExpectedValue>::from([
            $(($elem).into()),+
            ]);
            $crate::harness::expected_array_infer(values)
        }
    };
}
