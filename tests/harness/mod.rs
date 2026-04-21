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
    containers::IntoSVec2,
    effects::{PrimitiveEffect, effect, effects, no_effects},
    emit_ir::{CompiledExpr, emit_expr_unsafe},
    error::{CompilationError, RuntimeErrorKind},
    eval::{ControlFlow, EvalResult, RuntimeError, eval_node},
    function::{
        BinaryNativeFnNNV, Function, FunctionDefinition, NullaryNativeFnN, UnaryNativeFnMV,
        UnaryNativeFnNN, UnaryNativeFnNV, UnaryNativeFnVN, UnaryNativeFnVV,
    },
    module::{BlanketTraitImplSubKey, Module, ModuleEnv, ModuleId, Path},
    parse_module_and_expr,
    std::{
        array::{Array, ArrayIterator, array_iter_type_generic, array_type},
        logic::bool_type,
        math::int_type,
        new_module_using_std,
        option::option_type,
        string::string_type,
    },
    r#trait::TraitRef,
    r#type::{FnType, Type, TypeDef, TypeDefRef, TypeVar, variant_type},
    type_scheme::{PubTypeConstraint, TypeScheme},
    value::Value,
};
use std::{cell::RefCell, sync::atomic::AtomicIsize};
use ustr::ustr;

#[derive(Debug)]
pub enum Error {
    Compilation(CompilationError),
    Runtime(RuntimeError),
}

pub type CompileRunResult = Result<Value, Error>;

fn test_assoc_trait() -> TraitRef {
    TraitRef::new_with_self_input_type(
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

fn test_iterator_trait() -> TraitRef {
    TraitRef::new_with_self_input_type(
        "TestIterator",
        "Test-only iterator trait with one associated item type.",
        ["Item"],
        [(
            "test_next",
            FunctionDefinition::new_infer_quantifiers(
                FnType::new_mut_resolved(
                    [(Type::variable_id(0), true)],
                    option_type(Type::variable_id(1)),
                    no_effects(),
                ),
                ["iterator"],
                "Gets the next item from a test-only iterator.",
            ),
        )],
    )
}

fn test_witnessed_project_trait() -> TraitRef {
    TraitRef::new_with_self_input_type(
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

fn option_type_def() -> TypeDefRef {
    TypeDefRef::new(TypeDef {
        name: ustr("Option"),
        doc: None,
        param_names: vec![ustr("T")],
        shape: TypeScheme {
            ty_quantifiers: vec![TypeVar::new(0)],
            eff_quantifiers: FxHashSet::default(),
            ty: variant_type([
                ("None", Type::unit()),
                ("Some", Type::tuple([Type::variable_id(0)])),
            ]),
            constraints: vec![],
        },
        span: Location::new_synthesized(),
        attributes: vec![],
        default_variant: None,
    })
}

fn map_iterator_type_def(test_iterator_trait: TraitRef) -> TypeDefRef {
    TypeDefRef::new(TypeDef {
        name: ustr("MapIterator"),
        doc: None,
        param_names: vec![ustr("I"), ustr("T"), ustr("O")],
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
                test_iterator_trait,
                vec![Type::variable_id(0)],
                vec![Type::variable_id(1)],
                Location::new_synthesized(),
            )],
        },
        span: Location::new_synthesized(),
        attributes: vec![],
        default_variant: None,
    })
}

fn witnessed_type_def(test_assoc_trait: TraitRef) -> TypeDefRef {
    TypeDefRef::new(TypeDef {
        name: ustr("Witnessed"),
        doc: None,
        param_names: vec![ustr("Input"), ustr("Output")],
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
        span: Location::new_synthesized(),
        attributes: vec![],
        default_variant: None,
    })
}

fn testing_module(module_id: ModuleId) -> Module {
    let mut module = Module::new(module_id);
    let test_assoc_trait = test_assoc_trait();
    let test_iterator_trait = test_iterator_trait();
    let test_witnessed_project_trait = test_witnessed_project_trait();
    let option_type_def = option_type_def();
    let map_iterator_type_def = map_iterator_type_def(test_iterator_trait.clone());
    let witnessed_type_def = witnessed_type_def(test_assoc_trait.clone());
    module.add_trait(test_assoc_trait.clone());
    module.add_trait(test_iterator_trait.clone());
    module.add_trait(test_witnessed_project_trait.clone());
    module.add_concrete_impl_no_locals(
        test_assoc_trait.clone(),
        [string_type()],
        [int_type()],
        [
            Box::new(UnaryNativeFnNN::new(|_: ferlium::std::string::String| {
                0isize
            })) as Function,
        ],
    );
    module.add_concrete_impl_no_locals(
        test_assoc_trait.clone(),
        [bool_type()],
        [string_type()],
        [Box::new(UnaryNativeFnNN::new(|value: bool| {
            ferlium::std::string::String::new(if value { "true" } else { "false" })
        })) as Function],
    );
    module.add_type_def(option_type_def.name, option_type_def.clone());
    module.add_type_def(map_iterator_type_def.name, map_iterator_type_def.clone());
    module.add_type_def(witnessed_type_def.name, witnessed_type_def.clone());
    module.add_blanket_impl_no_locals(
        test_iterator_trait,
        BlanketTraitImplSubKey {
            input_tys: vec![array_iter_type_generic()],
            ty_var_count: 1,
            constraints: vec![],
        },
        vec![Type::variable_id(0)],
        [Box::new(UnaryNativeFnMV::new(ArrayIterator::next_value)) as Function],
    );
    module.add_blanket_impl_no_locals(
        test_witnessed_project_trait,
        BlanketTraitImplSubKey {
            input_tys: vec![Type::named(
                witnessed_type_def.clone(),
                [Type::variable_id(0), Type::variable_id(1)],
            )],
            ty_var_count: 2,
            constraints: vec![PubTypeConstraint::new_have_trait(
                test_assoc_trait.clone(),
                vec![Type::variable_id(0)],
                vec![Type::variable_id(1)],
                Location::new_synthesized(),
            )],
        },
        vec![Type::variable_id(1)],
        [Box::new(UnaryNativeFnVV::new(|_value: Value| Value::unit())) as Function],
    );
    module.add_function(
        "some_int".into(),
        UnaryNativeFnNV::description_with_ty(
            |v: isize| Value::tuple_variant(ustr("Some"), [Value::native(v)]),
            ["option"],
            "Wraps an integer into an Option variant.",
            int_type(),
            Type::named(option_type_def, [int_type()]),
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
            |_value: Value| (),
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
    static INT_ARRAY_PROPERTY_VALUE: RefCell<Array> = RefCell::new(Array::new());
}

pub fn set_array_property_value(value: Array) {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| *cell.borrow_mut() = value);
}

pub fn get_array_property_value() -> Array {
    INT_ARRAY_PROPERTY_VALUE.with(|cell| cell.borrow().clone())
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
        NullaryNativeFnN::description_with_ty(
            get_array_property_value,
            [],
            "Gets the value of my_scope.my_array.",
            array_type(int_type()),
            effect(PrimitiveEffect::Read),
        ),
    );
    module.add_function(
        "@set my_scope.my_array".into(),
        UnaryNativeFnNN::description_with_in_ty(
            set_array_property_value,
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
        compiler_session.register_module(
            Path::single_str("testing"),
            testing_module(compiler_session.modules().next_id()),
        );
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
            self.session.modules(),
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
        Value::native(Array::new())
    };
    [$($elem:expr),+ $(,)?] => {
        Value::native(ferlium::std::array::Array::from_vec(vec![
            $(Value::native::<bool>($elem)),+
        ]))
    };
}

/// An array of integer values
#[macro_export]
macro_rules! int_a {
    [] => {
        Value::native(ferlium::std::array::Array::new())
    };
    [$($elem:expr),+ $(,)?] => {
        Value::native(ferlium::std::array::Array::from_vec(vec![
            $(Value::native::<ferlium::std::math::Int>($elem)),+
        ]))
    };
}

/// An array of float values
#[macro_export]
macro_rules! float_a {
    [] => {
        Value::native(ferlium::std::array::Array::new())
    };
    [$($elem:expr),+ $(,)?] => {
        Value::native(ferlium::std::array::Array::from_vec(vec![
            $(Value::native::<ferlium::std::math::Float>(ferlium::std::math::Float::new($elem).unwrap())),+
        ]))
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
        Value::native(ferlium::std::array::Array::new())
    };
    [$($elem:expr),+ $(,)?] => {
        Value::native(ferlium::std::array::Array::from_vec(vec![
            $($elem),+
        ]))
    };
}
