// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use ferlium::{
    CompilationOutput, CompilerSession, ExecutionTarget, FxHashSet, Location, MirOptimization,
    SourceTable,
    compiler::error::{CompilationError, SourceFailureKind},
    compiler::test_support::add_module_source,
    eval::{EvalResult, RuntimeError},
    hir::function::{CallableDefinition, Function},
    hir::native_functions::{
        NativeDropFn, NativeFn0, NativeFnN, NativeFnR, NativeFnRM, NativeFnRR, NativeOptionalFnN,
        NativeOutFn0, NativeOutFnN, NativeOutFnR,
    },
    hir::value::{LiteralValue, NativeValueType, Value},
    hir::{ENodeArena, ENodeId, NodeKind},
    module::{Module, ModuleEnv, ModuleId, Path, TraitId},
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
use regex::Regex;
use std::{
    cell::{Cell, RefCell},
    fmt,
    sync::LazyLock,
    sync::atomic::AtomicIsize,
};
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

pub fn hir_child_nodes(arena: &ENodeArena, node: ENodeId) -> Vec<ENodeId> {
    // Lightweight white-box test traversal. Extend this when a test body needs
    // to search through additional HIR node shapes.
    match &arena[node].kind {
        NodeKind::Block(block) => block.body.iter().copied().collect(),
        NodeKind::Return(value) => vec![*value],
        NodeKind::Project(project) => vec![project.value],
        NodeKind::FieldAccess(_) => Vec::new(),
        NodeKind::BuildSubscriptValue(build) => std::iter::once(build.subscript)
            .chain(build.evidence_captures.iter().copied())
            .collect(),
        NodeKind::SubscriptApply(app) => std::iter::once(app.subscript)
            .chain(app.arguments.iter().map(|arg| arg.value))
            .collect(),
        NodeKind::FunctionApply(app) => std::iter::once(app.function)
            .chain(app.arguments.iter().map(|arg| arg.value))
            .collect(),
        NodeKind::StaticApply(app) => app
            .extra_arguments
            .iter()
            .copied()
            .chain(app.arguments.iter().map(|arg| arg.value))
            .collect(),
        NodeKind::CallDictionaryFunction(app) => std::iter::once(app.dictionary)
            .chain(app.arguments.iter().map(|arg| arg.value))
            .collect(),
        NodeKind::GetDictionary(dictionary) => dictionary.captures.clone(),
        NodeKind::WithPlace(with_place) => vec![with_place.place, with_place.body],
        NodeKind::WithYielded(with_yielded) => vec![with_yielded.accessor, with_yielded.body],
        NodeKind::CloneValue(clone) => vec![clone.source],
        NodeKind::StoreLocal(store) => vec![store.value],
        NodeKind::Assign(assign) => vec![assign.place, assign.value],
        _ => Vec::new(),
    }
}

fn value_shape(value: &Value) -> &'static str {
    match value {
        Value::Uninit => "uninitialized value",
        Value::Native(_) => "native value",
        Value::Variant { .. } => "variant value",
        Value::Tuple(_) => "tuple value",
        Value::Function(_) => "function value",
        Value::Subscript(_) => "subscript value",
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
        actual.as_primitive_ty::<ferlium::std::hash::HashValue>(),
        expected.as_primitive_ty::<ferlium::std::hash::HashValue>(),
    ) {
        return if actual == expected {
            Ok(())
        } else {
            Err(format!("{path}: expected {expected:?}, got {actual:?}"))
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
        (
            Value::Variant {
                tag: actual_tag, ..
            },
            Value::Variant {
                tag: expected_tag, ..
            },
        ) => {
            if actual_tag != expected_tag {
                return Err(format!(
                    "{path}: expected variant tag {expected_tag}, got {actual_tag}"
                ));
            }
            let path = format!("{path}.{actual_tag}");
            // A case that carries nothing has two encodings: no payload at all, which is what a
            // natively built variant uses, and a stored unit, which is what the MIR emitter leaves
            // after filling a variant shell. They are the same value.
            match (actual.variant_payload(), expected.variant_payload()) {
                (None, None) => Ok(()),
                (Some(actual), Some(expected)) => compare_values(actual, expected, &path),
                (None, Some(present)) | (Some(present), None) => {
                    if present.is_unit() {
                        Ok(())
                    } else {
                        Err(format!(
                            "{path}: one side carries a payload and the other does not"
                        ))
                    }
                }
            }
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

/// How a snippet is executed by the test harness.
///
/// By default every snippet runs under all of these, and each is checked against the first — the
/// HIR interpreter. That is what gives the MIR backend and the optimization passes their coverage:
/// a divergence surfaces in whichever test happens to exercise the construct, rather than only in a
/// hand-picked corpus. A test that must not run under some mode selects its own set; see
/// [`TestSession::without_optimized_mode`] and [`TestSession::only_optimized_mode`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RunMode {
    /// The HIR interpreter: the reference.
    Hir,
    /// The MIR interpreter on the bodies the emitter produced.
    Mir,
    /// The MIR interpreter on optimized bodies (partial evaluation).
    OptimizedMir,
    /// The physical MIR interpreter on ABI-lowered optimized bodies.
    PhysicalMir,
}

impl RunMode {
    pub const ALL: [Self; 4] = [Self::Hir, Self::Mir, Self::OptimizedMir, Self::PhysicalMir];

    fn target(self) -> ExecutionTarget {
        match self {
            Self::Hir => ExecutionTarget::Hir,
            Self::Mir | Self::OptimizedMir => ExecutionTarget::Mir,
            Self::PhysicalMir => ExecutionTarget::PhysicalMir,
        }
    }

    fn optimization(self) -> MirOptimization {
        match self {
            Self::Hir | Self::Mir => MirOptimization::Disabled,
            Self::OptimizedMir | Self::PhysicalMir => MirOptimization::Enabled,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Hir => "the HIR interpreter",
            Self::Mir => "the MIR backend",
            Self::OptimizedMir => "the optimized MIR backend",
            Self::PhysicalMir => "the physical MIR backend",
        }
    }
}

/// Asserts that one execution mode agreed with the reference run, in value or in failure.
///
/// Optimization may change how much fuel or call depth a program consumes (sandbox policy, not
/// source-visible semantics), but never what it computes or whether it raises.
fn assert_outcomes_agree(
    reference: &Result<Value, Error>,
    actual: &Result<Value, Error>,
    label: &str,
) {
    // Optimization may change fuel and call-depth consumption, which is sandbox policy rather than
    // source-visible semantics; it may never change the value or whether the program raises.
    match (reference, actual) {
        (Ok(expected), Ok(actual)) => {
            if let Err(message) = compare_values(actual, expected, "value") {
                panic!("{label} diverged from the HIR interpreter: {message}");
            }
        }
        (Err(Error::Runtime(expected)), Err(Error::Runtime(actual))) => {
            assert_eq!(
                actual.kind(),
                expected.kind(),
                "{label} raised a different runtime error than the HIR interpreter: {actual:?}"
            );
            match (
                expected.failure_during_cleanup(),
                actual.failure_during_cleanup(),
            ) {
                (Some(expected), Some(actual)) => {
                    assert_eq!(
                        actual.initial().kind(),
                        expected.initial().kind(),
                        "{label} retained a different initial failure than HIR"
                    );
                    assert_eq!(
                        actual.during_cleanup().kind(),
                        expected.during_cleanup().kind(),
                        "{label} retained a different cleanup failure than HIR"
                    );
                }
                (None, None) => {}
                _ => panic!(
                    "{label} disagreed with HIR about whether the runtime error was a structured \
                     failure during cleanup"
                ),
            }
        }
        (expected, actual) => panic!(
            "{label} diverged from the HIR interpreter: one produced a value and the other a \
             runtime error (HIR: {expected:?}, {label}: {actual:?})"
        ),
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

/// Normalizes the *module id* of a MIR dictionary operand `dict(m<number>:i<number>)` — and of the
/// raw `subscript(m<number>:s<number>)` fallback used when a malformed/unavailable subscript cannot
/// be named — to `dict(m<...>:i<number>)`: the module id is assigned by module load order (so it
/// shifts as the std prelude grows), whereas the trailing impl/subscript id is an index within a
/// fixed module and stays deterministic, so it is preserved.
///
/// Trait-impl method names used to embed non-deterministic interned ids (e.g. `Num<0-6>`); these
/// are now fully-qualified type names plus a deterministic `#impl:<hash>` head hash (see
/// commit 2231b61), so they need no normalization.
pub(crate) fn replace_flaky_ids(s: impl AsRef<str>) -> String {
    static MODULE_ID: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"(dict|subscript)\(m\d+:").unwrap());
    MODULE_ID.replace_all(s.as_ref(), "$1(m<...>:").into_owned()
}

/// Like `assert_eq!`, but normalizes both sides with [`replace_flaky_ids`] first, so the comparison
/// ignores the non-deterministic module id that would otherwise cause flakes.
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
        has_custom_value_impl: false,
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
        has_custom_value_impl: false,
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
        has_custom_value_impl: false,
    }
}

thread_local! {
    static TRACKED_CLONES: Cell<isize> = const { Cell::new(0) };
    static TRACKED_DROPS: Cell<isize> = const { Cell::new(0) };
    static TRACKED_NATIVE_DROPS: Cell<isize> = const { Cell::new(0) };
}

#[derive(Debug)]
pub struct CloneTrackedNative(isize);

impl NativeValueType for CloneTrackedNative {}

impl Drop for CloneTrackedNative {
    fn drop(&mut self) {
        TRACKED_NATIVE_DROPS.set(TRACKED_NATIVE_DROPS.get() + 1);
    }
}

impl Clone for CloneTrackedNative {
    fn clone(&self) -> Self {
        TRACKED_CLONES.set(TRACKED_CLONES.get() + 1);
        Self(self.0)
    }
}

fn make_clone_tracked() -> CloneTrackedNative {
    CloneTrackedNative(7)
}

unsafe extern "C" fn tracked_member_ref(value: *const CloneTrackedNative) -> *const isize {
    unsafe { &raw const (*value).0 }
}
unsafe extern "C" fn tracked_member_mut(value: *mut CloneTrackedNative) -> *mut isize {
    unsafe { &raw mut (*value).0 }
}
unsafe extern "C" fn tracked_self_ref(
    value: *const CloneTrackedNative,
) -> *const CloneTrackedNative {
    value
}
unsafe extern "C" fn tracked_self_mut(value: *mut CloneTrackedNative) -> *mut CloneTrackedNative {
    value
}

unsafe extern "C" fn tracked_failing_member(
    failure: &mut ferlium::hir::native_functions::NativeFailureState,
    value: *mut CloneTrackedNative,
    output: &mut std::mem::MaybeUninit<*mut isize>,
) -> u32 {
    if unsafe { (*value).0 } < 0 {
        failure.fail(SourceFailureKind::InvalidArgument(
            "negative native member".into(),
        ))
    } else {
        output.write(unsafe { &raw mut (*value).0 });
        0
    }
}

extern "C" fn clone_tracked_payload(value: &CloneTrackedNative) -> isize {
    value.0
}

extern "C" fn reset_clone_tracked_clones() {
    TRACKED_CLONES.set(0);
}

extern "C" fn clone_tracked_clone_count() -> isize {
    TRACKED_CLONES.get()
}

extern "C" fn equal_clone_tracked(left: &CloneTrackedNative, right: &CloneTrackedNative) -> bool {
    left.0 == right.0
}

fn clone_tracked_to_string(value: &CloneTrackedNative) -> ferlium::std::string::String {
    ferlium::std::string::String::new(&format!("clone_tracked({})", value.0))
}

extern "C" fn hash_clone_tracked(
    value: &CloneTrackedNative,
    state: &mut ferlium::std::hash::Hasher,
) {
    state.write_isize(value.0);
}

unsafe extern "C" fn drop_clone_tracked(target: *mut CloneTrackedNative) {
    // SAFETY: the destructor adapter supplies one exclusively owned, initialized native value.
    unsafe { target.drop_in_place() };
}

pub(crate) extern "C" fn reset_native_drops() {
    TRACKED_NATIVE_DROPS.set(0);
}

pub(crate) extern "C" fn native_drop_count() -> isize {
    TRACKED_NATIVE_DROPS.get()
}

fn clone_tracked_value_clone_function() -> Function {
    Box::new(NativeOutFnR::from_rust(CloneTrackedNative::clone)) as Function
}

fn clone_tracked_value_drop_function() -> Function {
    // SAFETY: this Value::drop entry destroys its native pointee exactly once without freeing it.
    Box::new(unsafe { NativeDropFn::new(drop_clone_tracked) }) as Function
}

extern "C" fn record_tracked_drop(value: isize) {
    // Unread logs can overflow, particularly on wasm32. Tests reset before asserting short logs.
    TRACKED_DROPS.set(TRACKED_DROPS.get().wrapping_mul(10).wrapping_add(value));
}

extern "C" fn reset_tracked_drops() {
    TRACKED_DROPS.set(0);
}

extern "C" fn tracked_drop_log() -> isize {
    TRACKED_DROPS.get()
}

fn add_tracked_members(module: &mut Module) {
    use ferlium::hir::native_functions::{
        NativeAddressorMut, NativeAddressorRef, NativeFallibleAddressorMut,
    };
    // SAFETY: these entries expose initialized fields (or the receiver itself), with no guard
    // or extra Rust invariants; the failure entry writes output only on success.
    unsafe {
        module.add_native_member(
            ustr("payload"),
            Some(NativeAddressorRef::new(tracked_member_ref).description(
                ["self"],
                "Native payload",
                no_effects(),
            )),
            Some(NativeAddressorMut::new(tracked_member_mut).description(
                ["self"],
                "Native payload",
                no_effects(),
            )),
        );
        module.add_native_member(
            ustr("readonly"),
            Some(NativeAddressorRef::new(tracked_member_ref).description(
                ["self"],
                "Read-only payload",
                no_effects(),
            )),
            None,
        );
        module.add_native_member(
            ustr("self_member"),
            Some(NativeAddressorRef::new(tracked_self_ref).description(
                ["self"],
                "Rooted native value",
                no_effects(),
            )),
            Some(NativeAddressorMut::new(tracked_self_mut).description(
                ["self"],
                "Rooted native value",
                no_effects(),
            )),
        );
        module.add_native_member(
            ustr("checked_payload"),
            Some(NativeAddressorRef::new(tracked_member_ref).description(
                ["self"],
                "Read payload",
                no_effects(),
            )),
            Some(
                NativeFallibleAddressorMut::new(tracked_failing_member).description(
                    ["self"],
                    "Checked payload",
                    effect(PrimitiveEffect::Fallible),
                ),
            ),
        );
    }
}

fn add_tracked_value(module: &mut Module, value_trait_id: TraitId, value_trait_def: &Trait) {
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
            Box::new(NativeFnRR::new(equal_clone_tracked)) as Function,
            Box::new(NativeOutFnR::from_rust(clone_tracked_to_string)) as Function,
            Box::new(NativeFnRM::new(hash_clone_tracked)) as Function,
            clone_tracked_value_clone_function(),
            clone_tracked_value_drop_function(),
        ],
    );
}

fn add_tracked_functions(module: &mut Module) {
    module.add_function(
        "make_clone_tracked".into(),
        NativeOutFn0::from_rust(make_clone_tracked).description(
            [],
            "Creates a clone-counting native test value.",
            no_effects(),
        ),
    );
    module.add_function(
        "clone_tracked_payload".into(),
        NativeFnR::new(clone_tracked_payload).description(
            ["value"],
            "Returns the payload of a clone-counting native test value.",
            no_effects(),
        ),
    );
    module.add_function(
        "reset_clone_tracked_clones".into(),
        NativeFn0::new(reset_clone_tracked_clones).description(
            [],
            "Resets the clone counter for clone-counting native test values.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_function(
        "clone_tracked_clone_count".into(),
        NativeFn0::new(clone_tracked_clone_count).description(
            [],
            "Returns the clone counter for clone-counting native test values.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "reset_native_drops".into(),
        NativeFn0::new(reset_native_drops).description(
            [],
            "Resets the Rust destructor counter for native test values.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_function(
        "native_drop_count".into(),
        NativeFn0::new(native_drop_count).description(
            [],
            "Returns the Rust destructor counter for native test values.",
            effect(PrimitiveEffect::Read),
        ),
    );
}

fn testing_module(
    module_id: ModuleId,
    iterator_trait: TraitId,
    value_trait_id: TraitId,
    value_trait_def: &Trait,
) -> Module {
    let mut module = Module::new(module_id, Path::single_str("testing"));
    add_tracked_members(&mut module);
    let test_assoc_trait = test_assoc_trait();
    let test_witnessed_project_trait = test_witnessed_project_trait();
    let test_assoc_trait_id = TraitId::new(module_id, module.add_trait(test_assoc_trait));
    module.add_trait(test_witnessed_project_trait);
    let option_type_def = option_type_def();
    let map_iterator_type_def = map_iterator_type_def(iterator_trait);
    let witnessed_type_def = witnessed_type_def(test_assoc_trait_id);
    module.add_concrete_impl_no_locals(
        test_assoc_trait_id,
        [string_type()],
        [int_type()],
        [],
        [
            Box::new(NativeFnR::from_rust(|_: &ferlium::std::string::String| {
                0isize
            })) as Function,
        ],
    );
    module.add_concrete_impl_no_locals(
        test_assoc_trait_id,
        [bool_type()],
        [string_type()],
        [],
        [Box::new(NativeOutFnN::from_rust(|value: bool| {
            ferlium::std::string::String::new(if value { "true" } else { "false" })
        })) as Function],
    );
    let option_type_def_id = module.add_type_def(option_type_def.name, option_type_def);
    module.add_type_def(map_iterator_type_def.name, map_iterator_type_def);
    module.add_type_def(witnessed_type_def.name, witnessed_type_def);
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
        [Box::new(NativeFnN::from_rust(|v: isize| v * 2)) as Function],
    );
    module.add_concrete_impl_with_effects_no_locals(
        test_eff_trait_id,
        [bool_type()],
        [int_type()],
        [effect(PrimitiveEffect::Read)],
        [],
        [Box::new(NativeFnN::from_rust(
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
            Box::new(NativeFnR::from_rust(|_: &ferlium::std::string::String| {
                0isize
            })) as Function,
        ],
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
            Box::new(NativeFnN::from_rust(
                |v: bool| {
                    if v { 1isize } else { 0isize }
                },
            )) as Function,
            Box::new(NativeFnN::from_rust(
                |v: bool| {
                    if v { 2isize } else { 0isize }
                },
            )) as Function,
        ],
    );
    module.add_trait(test_eff_join_trait());
    add_tracked_value(&mut module, value_trait_id, value_trait_def);
    module.add_function(
        "some_int".into(),
        NativeOptionalFnN::from_rust(Some::<isize>, Type::named(option_type_def_id, [int_type()]))
            .description(
                ["option"],
                "Wraps an integer into an Option variant.",
                no_effects(),
            ),
    );
    module.add_function(
        "some_bool".into(),
        NativeOptionalFnN::from_rust(Some::<bool>, Type::named(option_type_def_id, [bool_type()]))
            .description(
                ["option"],
                "Wraps a boolean into an Option variant.",
                no_effects(),
            ),
    );
    add_tracked_functions(&mut module);
    module.add_function(
        "record_tracked_drop".into(),
        // Declared pure because Value::drop has no effects. Unit calls are not folded away.
        NativeFnN::new(record_tracked_drop).description(
            ["value"],
            "Records a dropped test value in the drop log.",
            no_effects(),
        ),
    );
    module.add_function(
        "reset_tracked_drops".into(),
        NativeFn0::new(reset_tracked_drops).description(
            [],
            "Resets the tracked drop log.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_function(
        "tracked_drop_log".into(),
        NativeFn0::new(tracked_drop_log).description(
            [],
            "Returns the tracked drop log.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module
}

/// The natives above that touch the process-global counters declare `Read` or `Write`
/// accordingly, and must keep doing so. A native declaring neither is *asserted* by its host to be
/// pure and deterministic, and the compiler may then execute it at compile time — zero times, once,
/// or many (see `doc/runtime-sandboxing.md`). A drop counter declared pure gets folded to whatever
/// it happened to read during compilation.
fn test_effect_module(module_id: ModuleId) -> Module {
    let mut module = Module::new(module_id, Path::single_str("effects_native"));
    module.add_function(
        "read".into(),
        NativeFn0::from_rust(|| ()).description(
            [],
            "Performs a read effect.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "write".into(),
        NativeFn0::from_rust(|| ()).description(
            [],
            "Performs a write effect.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_function(
        "read_write".into(),
        NativeFn0::from_rust(|| ()).description(
            [],
            "Performs both read and write effects.",
            effects(&[PrimitiveEffect::Read, PrimitiveEffect::Write]),
        ),
    );
    module
}

static INT_PROPERTY_VALUE: AtomicIsize = AtomicIsize::new(0);

pub extern "C" fn set_property_value(value: isize) {
    INT_PROPERTY_VALUE.store(value, std::sync::atomic::Ordering::Relaxed);
}

pub extern "C" fn get_property_value() -> isize {
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

extern "C" fn array_property_len() -> isize {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| cell.borrow().len() as isize)
}

extern "C" fn array_property_get(index: isize) -> isize {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| cell.borrow()[index as usize])
}

extern "C" fn array_property_clear() {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| cell.borrow_mut().clear());
}

extern "C" fn array_property_push(value: isize) {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| cell.borrow_mut().push(value));
}

/// External property state, restored before each backend and compared after execution.
/// The reference outcome is restored last so a snippet applies its effects only once.
#[derive(Debug, PartialEq, Eq)]
struct PropertyFixtures {
    int_property: isize,
    int_array_property: Vec<isize>,
}

impl PropertyFixtures {
    fn capture() -> Self {
        Self {
            int_property: get_property_value(),
            int_array_property: INT_ARRAY_PROPERTY_VALUE.with(|cell| cell.borrow().clone()),
        }
    }

    fn restore(&self) {
        set_property_value(self.int_property);
        INT_ARRAY_PROPERTY_VALUE.with(|cell| *cell.borrow_mut() = self.int_array_property.clone());
    }
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
        NativeFn0::new(get_property_value).description(
            [],
            "Gets the value of my_scope.my_var.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "@set my_scope.my_var".into(),
        NativeFnN::new(set_property_value).description(
            ["value"],
            "Sets the value of my_scope.my_var.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_function(
        "array_len".into(),
        NativeFn0::new(array_property_len).description(
            [],
            "Array fixture length.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "array_get".into(),
        NativeFnN::new(array_property_get).description(
            ["index"],
            "Array fixture element.",
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "array_clear".into(),
        NativeFn0::new(array_property_clear).description(
            [],
            "Clear the array fixture.",
            effect(PrimitiveEffect::Write),
        ),
    );
    module.add_function(
        "array_push".into(),
        NativeFnN::new(array_property_push).description(
            ["value"],
            "Append to the array fixture.",
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
    /// The execution modes snippets run under. The first is the reference the others are checked
    /// against, and whose result is returned.
    modes: Vec<RunMode>,
}
impl TestSession {
    /// Opt trusted fixtures into unsafe language features, including custom ownership methods.
    pub fn allow_unsafe(&mut self) {
        self.session.set_allow_unsafe(true);
    }

    /// Create a new test session with std, testing, effects and props modules registered.
    ///
    /// Every snippet run through the session is executed under every [`RunMode`] — the HIR
    /// interpreter, raw MIR, optimized MIR, and physical MIR — which are
    /// asserted to agree (see [`TestSession::try_compile_and_run_value`]).
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
        let testing_module = add_module_source(
            &mut compiler_session,
            testing_module,
            r#"
            use std::*;
            impl<A, B> TestWitnessedProject for <Self = Witnessed<A, B> |-> Output = B>
                where A: TestAssoc<Output = B> {
                fn witness_project(value: Witnessed<A, B>) -> B { project(value.0) }
            }
            impl<A, B ! F> TestEff for <Self = Option<A> |-> Output = B ! E = F>
                where A: TestEff<Output = B ! E = F> {
                // Typing-only fixture: there is no B to return for an absent A.
                fn eff_project(value: Option<A>) -> B { loop {} }
            }
            pub struct EffPair<A, B>(A, B)
            impl<A, B, X, Y ! F, G> TestEffJoin for <Self = EffPair<A, B> |-> ! E = (F, G)>
                where A: TestEff<Output = X ! E = F>, B: TestEff<Output = Y ! E = G> {
                fn eff_join(value: EffPair<A, B>) -> int { 0 }
            }
            pub fn constrained_probe<T>(value: T) -> int where T: Value { 42 }
            pub fn pair(first: int, second: int) -> Pair(int, int) { Pair(first, second) }
            "#,
        )
        .unwrap();
        compiler_session.register_module(Path::single_str("testing"), testing_module);
        compiler_session.register_module(
            Path::single_str("effects_native"),
            test_effect_module(compiler_session.modules().next_id()),
        );
        // Constrain callback effects without passing a callable across the native boundary.
        compiler_session
            .compile(
                "pub fn read() { effects_native::read() }
                 pub fn write() { effects_native::write() }
                 pub fn read_write() { effects_native::read_write() }
                 pub fn take_read(f: (() -> () ! read)) { read() }",
                "effects.fer",
                Path::single_str("effects"),
            )
            .unwrap();
        let properties = test_property_module(compiler_session.modules().next_id());
        let mut properties = add_module_source(
            &mut compiler_session,
            properties,
            r#"
            use std::*;
            fn get_array() -> [int] {
                let mut value = [];
                for i in 0..array_len() { array_append(value, array_get(i)); };
                value
            }
            fn set_array(value: [int]) { array_clear(); for item in value { array_push(item); } }
        "#,
        )
        .unwrap();
        for (name, function) in [
            ("@get my_scope.my_array", "get_array"),
            ("@set my_scope.my_array", "set_array"),
        ] {
            properties.add_function(
                ustr(name),
                properties.get_function(ustr(function)).unwrap().clone(),
            );
        }
        compiler_session.register_module(Path::single_str("props"), properties);
        add_deep_modules(&mut compiler_session);
        Self {
            session: compiler_session,
            modes: RunMode::ALL.to_vec(),
        }
    }

    /// Selects the execution modes snippets run under. The first is the reference the others are
    /// checked against, and the one whose result is returned.
    pub fn run_modes(&mut self, modes: impl IntoIterator<Item = RunMode>) -> &mut Self {
        self.modes = modes.into_iter().collect();
        assert!(!self.modes.is_empty(), "a snippet must run somewhere");
        self
    }

    /// Excludes the optimized-MIR mode, for a test whose expectation only holds without
    /// optimization.
    ///
    /// The case this exists for: the language declares `Value::drop` effect-free, so a host that
    /// instruments drops must declare that instrumentation pure — and a pure function is then
    /// eligible for compile-time evaluation, which runs those drops while compiling instead of at
    /// run time. A test counting the drops of a pure function's locals therefore cannot also assert
    /// on the optimized run. That is the compile-time execution contract working as documented (see
    /// `doc/runtime-sandboxing.md`), not a divergence.
    pub fn without_optimized_mode(&mut self) -> &mut Self {
        self.run_modes([RunMode::Hir, RunMode::Mir])
    }

    /// Runs snippets *only* under optimized MIR, for a test aimed at the effect of optimization
    /// itself.
    ///
    /// Nothing cross-checks the result then — the test's own assertions are the check — so prefer
    /// the default modes unless running the other backends would itself perturb what is measured.
    pub fn only_optimized_mode(&mut self) -> &mut Self {
        self.run_modes([RunMode::OptimizedMir])
    }

    /// Get the compiler session of this test session.
    pub fn session(&self) -> &CompilerSession {
        &self.session
    }

    /// Get mutable access to the compiler session for artifact preparation and compiler tests.
    pub fn session_mut(&mut self) -> &mut CompilerSession {
        &mut self.session
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
            let expected_ty = expected.ty.unwrap_or(ty);
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
        self.session.source_table()
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
    pub fn try_compile(&mut self, src: &str) -> Result<CompilationOutput, CompilationError> {
        self.session
            .compile(src, "<test>", Path::single_str("test"))
    }

    /// Compile and run the src with a custom module name and return its module and expression
    pub fn try_compile_module(
        &mut self,
        name: &str,
        src: &str,
    ) -> Result<CompilationOutput, CompilationError> {
        self.session.compile(src, name, Path::single_str(name))
    }

    pub fn emit_mir(&mut self, src: &str) -> String {
        self.session.emit_mir("<test>", src)
    }

    /// Lower `src` to MIR, interpret its `fn main`, and return the rendered result.
    pub fn _eval_mir(&mut self, src: &str) -> String {
        self.session.eval_mir("<test>", src)
    }

    /// Compile the src and return its module and expression
    pub fn compile(&mut self, src: &str) -> CompilationOutput {
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
        let CompilationOutput { module_id, expr } =
            self.try_compile(src).map_err(Error::Compilation)?;

        // Run the expression through every execution mode, asserting they all agree with the HIR
        // interpreter: equal values, matching structural runtime-error kinds, or matching
        // cleanup-failure causes and retained cause kinds. Return the HIR result. Running every
        // mode on every snippet is what gives the MIR backend, and the optimization passes, full
        // coverage — including the error path, since a failing snippet exercises all of them rather
        // than short-circuiting on the HIR error.
        if let Some(expr) = expr {
            let ty = self
                .session
                .expect_fresh_module(module_id)
                .get_function_by_id(expr)
                .unwrap()
                .definition
                .ty_scheme
                .ty
                .ret;
            let value = {
                // Snapshot the externally-mutable `@props` fixtures so every mode observes the
                // same preconditions. Without this, a snippet that mutates a fixture would apply
                // its effect once per mode and they would diverge spuriously. See
                // `PropertyFixtures`.
                let fixtures = PropertyFixtures::capture();
                let selected = self.session.mir_optimization();
                let modes = self.modes.clone();
                let mut expected_effects = None;
                let results: Vec<_> = modes
                    .iter()
                    .map(|mode| {
                        fixtures.restore();
                        self.session.set_mir_optimization(mode.optimization());
                        let result = self
                            .session
                            .run_entry(mode.target(), module_id, expr, vec![])
                            .map_err(Error::Runtime);
                        let effects = PropertyFixtures::capture();
                        if let Some(expected) = &expected_effects {
                            assert_eq!(
                                expected,
                                &effects,
                                "{} changed the property fixtures differently",
                                mode.label()
                            );
                        } else {
                            expected_effects = Some(effects);
                        }
                        result
                    })
                    .collect();
                self.session.set_mir_optimization(selected);
                expected_effects.unwrap().restore();

                // The first mode — the HIR interpreter unless a test says otherwise — is the
                // reference every other one is checked against.
                for (mode, result) in modes.iter().zip(&results).skip(1) {
                    assert_outcomes_agree(&results[0], result, mode.label());
                }
                // Only the reference value is returned; the rest own storage that a plain Rust
                // drop would not reclaim, `Value` being `ManuallyDrop`-based.
                let mut results = results.into_iter();
                let reference = results.next().expect("at least one mode runs");
                for value in results.flatten() {
                    value.discard_storage();
                }
                reference?
            };
            Ok(RunValue {
                module_id,
                value,
                ty,
            })
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
    pub fn fail_run(&mut self, src: &str) -> SourceFailureKind {
        match self.try_run_value(src) {
            Ok(value) => {
                let rendered = self.value_to_assertion_text(value.module_id, value.value, value.ty);
                panic!("Expected runtime error, got value: {rendered}");
            }
            Err(error) => error
                .source_failure()
                .unwrap_or_else(|| panic!("Expected source failure, got {error:?}"))
                .kind(),
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
    let ty = value.ty.map(ferlium::std::option::option_type);
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
