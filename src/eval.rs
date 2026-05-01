// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{collections::VecDeque, mem};

use derive_new::new;
use enum_as_inner::EnumAsInner;
use ustr::Ustr;
#[cfg(debug_assertions)]
use ustr::ustr;

#[cfg(debug_assertions)]
use crate::module::id::Id;
use crate::{
    CompilerSession, Location, SourceId, SourceTable,
    compiler::error::RuntimeErrorKind,
    containers::b,
    format::{FormatWith, write_with_separator},
    hir::function::NativeArgPassing,
    hir::value::{FunctionValue, NativeValue, Value},
    module::{FunctionId, LocalDecl, LocalFunctionId, ModuleFunction, ModuleId, TraitImplId},
    std::array,
    types::r#type::FnArgType,
};
use crate::{
    Modules,
    hir::{self, NodeArena, NodeId, NodeKind},
};

use crate::module::ImportFunctionTarget;

/// Either a value or a unique mutable reference to a value.
/// This allows to implement the mutable value semantics.
#[derive(Debug, Clone, EnumAsInner)]
pub enum ValOrMut {
    /// A value, itself
    Val(Value),
    /// A mutable reference, index in the environment plus path within the value
    Mut(Place),
}

impl ValOrMut {
    pub fn from_primitive(value: impl NativeValue) -> Self {
        ValOrMut::Val(Value::native(value))
    }

    pub fn into_primitive<T: 'static>(self) -> Option<T> {
        match self {
            ValOrMut::Val(val) => val.into_primitive_ty::<T>(),
            ValOrMut::Mut(_) => None,
        }
    }

    pub fn as_mut_primitive<'a, 'b, T: 'static>(
        &self,
        ctx: &'a mut EvalCtx<'b>,
    ) -> Result<Option<&'a mut T>, RuntimeErrorKind> {
        Ok(match self {
            ValOrMut::Val(_) => None,
            ValOrMut::Mut(place) => place.target_mut(ctx)?.as_primitive_ty_mut::<T>(),
        })
    }

    pub fn as_primitive<'a, T: 'static>(
        &'a self,
        ctx: &'a EvalCtx<'_>,
    ) -> Result<Option<&'a T>, RuntimeErrorKind> {
        Ok(match self {
            ValOrMut::Val(val) => val.as_primitive_ty::<T>(),
            ValOrMut::Mut(place) => place.target_ref(ctx)?.as_primitive_ty::<T>(),
        })
    }

    pub fn as_value_ref<'a>(&'a self, ctx: &'a EvalCtx<'_>) -> Result<&'a Value, RuntimeErrorKind> {
        Ok(match self {
            ValOrMut::Val(value) => value,
            ValOrMut::Mut(place) => place.target_ref(ctx)?,
        })
    }

    pub fn as_value(&self, ctx: &EvalCtx<'_>) -> Result<Value, RuntimeErrorKind> {
        Ok(match self {
            ValOrMut::Val(value) => value.clone(),
            ValOrMut::Mut(place) => place.target_ref(ctx)?.clone(),
        })
    }

    pub fn as_place(&self) -> &Place {
        match self {
            ValOrMut::Val(_) => panic!("Cannot get a place from a value"),
            ValOrMut::Mut(place) => place,
        }
    }
}

impl FormatWith<EvalCtx<'_>> for ValOrMut {
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &EvalCtx<'_>) -> std::fmt::Result {
        match self {
            ValOrMut::Val(value) => {
                write!(f, "value ")?;
                value.format_as_string_repr(f)
            }
            ValOrMut::Mut(place) => {
                write!(f, "mut. ref. {}", place.format_with(data))
            }
        }
    }
}

#[cfg(debug_assertions)]
#[derive(Debug, Clone, new)]
struct StackEntry {
    local_id: LocalFunctionId,
    module_id: ModuleId,
    frame_base: usize,
}

/// Along with the Rust native stack, corresponds to the Zinc Abstract Machine of Caml language family
/// with the addition of Mutable Value Semantics through references to earlier stack frames
pub struct EvalCtx<'a> {
    /// all values or mutable references of all stack frames
    pub environment: Vec<ValOrMut>,
    /// base of current stack frame in `environment`
    pub frame_base: usize,
    /// current function call depth
    pub call_depth: usize,
    /// maximum function call depth
    pub call_depth_limit: usize,
    /// maximum number of values in the evaluation environment
    pub stack_limit: usize,
    /// a flag to break the evaluation
    pub break_loop: bool,
    /// id of the current module for import slot resolution
    pub module_id: ModuleId,
    /// session holding sources and other modules for error reporting and import resolution
    compiler_session: &'a CompilerSession,
    #[cfg(debug_assertions)]
    stack_trace: Vec<StackEntry>,
    #[cfg(debug_assertions)]
    pub environment_names: Vec<Ustr>,
}

impl<'a> EvalCtx<'a> {
    const DEFAULT_CALL_DEPTH_LIMIT: usize = 192;
    const DEFAULT_STACK_LIMIT: usize = 65_536;

    pub fn new(module_id: ModuleId, compiler_session: &'a CompilerSession) -> EvalCtx<'a> {
        EvalCtx {
            environment: Vec::new(),
            frame_base: 0,
            call_depth: 0,
            call_depth_limit: Self::DEFAULT_CALL_DEPTH_LIMIT,
            stack_limit: Self::DEFAULT_STACK_LIMIT,
            break_loop: false,
            module_id,
            compiler_session,
            #[cfg(debug_assertions)]
            stack_trace: Vec::new(),
            #[cfg(debug_assertions)]
            environment_names: Vec::new(),
        }
    }

    /// Get the compiler session.
    pub fn compiler_session(&self) -> &'a CompilerSession {
        self.compiler_session
    }

    pub fn with_environment(
        module: ModuleId,
        environment: Vec<ValOrMut>,
        compiler_session: &'a CompilerSession,
    ) -> EvalCtx<'a> {
        #[cfg(debug_assertions)]
        let environment_names = vec![ustr("<unknown>"); environment.len()];
        EvalCtx {
            environment,
            frame_base: 0,
            call_depth: 0,
            call_depth_limit: Self::DEFAULT_CALL_DEPTH_LIMIT,
            stack_limit: Self::DEFAULT_STACK_LIMIT,
            break_loop: false,
            module_id: module,
            compiler_session,
            #[cfg(debug_assertions)]
            stack_trace: Vec::new(),
            #[cfg(debug_assertions)]
            environment_names,
        }
    }

    #[cfg(debug_assertions)]
    pub fn print_environment(&self) {
        assert_eq!(self.environment.len(), self.environment_names.len());
        eprintln!(
            "frame base: {}, fn stack depth: {}",
            self.frame_base, self.call_depth
        );
        eprintln!("Environment:");
        let mut i = self.environment_names.len();
        for entry in self.stack_trace.iter().rev() {
            while i > entry.frame_base {
                i -= 1;
                eprintln!("  {}", self.environment_names[i]);
            }
            let module = self.compiler_session.expect_fresh_module(entry.module_id);
            let fn_name = module.get_function_name_by_id(entry.local_id).unwrap();
            eprintln!("- {}::{}", entry.module_id, fn_name);
        }
        while i > 0 {
            i -= 1;
            eprintln!("  {}", self.environment_names[i]);
        }
    }

    /// Get a function's local id and module for a FunctionId at runtime.
    pub fn get_function_local_id(&self, function: FunctionId) -> (LocalFunctionId, ModuleId) {
        use FunctionId::*;
        match function {
            Local(id) => (id, self.module_id),
            Import(id) => {
                let module = self.compiler_session.expect_fresh_module(self.module_id);
                let slot = module
                    .get_import_fn_slot(id)
                    .unwrap_or_else(|| panic!("imported function slot not found: {}", id));
                let module_id = slot.module;
                let module = self.compiler_session.expect_fresh_module(module_id);
                let target_module_id = module_id;
                use ImportFunctionTarget::*;
                let local_id = match &slot.target {
                    TraitImplMethod { key, index } => {
                        let imp = module.get_impl_data_by_trait_key(key).unwrap_or_else(|| {
                            panic!(
                                "imported trait impl not found: {:?} in module #{}",
                                key, module_id
                            )
                        });
                        imp.methods[*index as usize]
                    }
                    &NamedFunction(fn_name) => {
                        module.get_local_function_id(fn_name).unwrap_or_else(|| {
                            panic!(
                                "imported function not found: {} in module #{}",
                                fn_name, module_id
                            )
                        })
                    }
                };
                (local_id, target_module_id)
            }
        }
    }

    /// Get a function's code and module for a FunctionId at runtime.
    pub fn get_module_function(
        &self,
        local_id: LocalFunctionId,
        module_id: ModuleId,
    ) -> &ModuleFunction {
        let module = self.compiler_session.expect_fresh_module(module_id);
        module.get_function_by_id(local_id).unwrap()
    }

    fn function_argument_passing(
        &self,
        local_id: LocalFunctionId,
        module_id: ModuleId,
    ) -> Option<&'static [NativeArgPassing]> {
        self.get_module_function(local_id, module_id)
            .code
            .argument_passing()
    }

    pub fn function_id_argument_passing(
        &self,
        function_id: FunctionId,
    ) -> Option<&'static [NativeArgPassing]> {
        let (local_id, module_id) = self.get_function_local_id(function_id);
        self.function_argument_passing(local_id, module_id)
    }

    pub fn function_value_argument_passing(
        &self,
        function_value: &FunctionValue,
    ) -> Option<&'static [NativeArgPassing]> {
        let passing =
            self.function_argument_passing(function_value.function, function_value.module)?;
        Some(&passing[function_value.captured.len()..])
    }

    /// Get the dictionary value for a ImplId at runtime using module.
    pub fn get_dictionary(&self, dictionary: TraitImplId) -> Value {
        let module = self.compiler_session.expect_fresh_module(self.module_id);
        use TraitImplId::*;
        match dictionary {
            Local(id) => module.get_impl_data(id).unwrap().dictionary_value.clone(),
            Import(id) => {
                let slot = module.get_import_impl_slot(id).unwrap();
                let module = self.compiler_session.expect_fresh_module(slot.module);
                module
                    .get_impl_data_by_trait_key(&slot.key)
                    .unwrap()
                    .dictionary_value
                    .clone()
            }
        }
    }

    /// Call a function value along containing its module context.
    pub fn call_function_value(
        &mut self,
        function_value: &FunctionValue,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> EvalControlFlowResult {
        let local_id = function_value.function;
        let module_id = function_value.module;

        #[cfg(debug_assertions)]
        self.stack_trace
            .push(StackEntry::new(local_id, module_id, self.environment.len()));

        let arguments = if function_value.captured.is_empty() {
            arguments
        } else {
            function_value
                .captured
                .clone()
                .into_iter()
                .map(ValOrMut::Val)
                .chain(arguments)
                .collect()
        };

        let result = self
            .call_function(local_id, module_id, arguments)
            .map_err(|err| {
                err.with_frame(
                    module_id,
                    FunctionId::Local(local_id),
                    self.environment.len(),
                    location,
                )
            });

        #[cfg(debug_assertions)]
        self.stack_trace.pop();

        result
    }

    /// Call a function by its id, this will look up the function and its module.
    pub fn call_function_id(
        &mut self,
        function_id: FunctionId,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> EvalControlFlowResult {
        let (local_id, module_id) = self.get_function_local_id(function_id);

        #[cfg(debug_assertions)]
        self.stack_trace
            .push(StackEntry::new(local_id, module_id, self.environment.len()));

        let result = self
            .call_function(local_id, module_id, arguments)
            .map_err(|err| {
                err.with_frame(
                    self.module_id,
                    function_id,
                    self.environment.len(),
                    location,
                )
            });

        #[cfg(debug_assertions)]
        self.stack_trace.pop();

        result
    }

    /// Call a function along with its correct module context.
    fn call_function(
        &mut self,
        local_id: LocalFunctionId,
        mut module_id: ModuleId,
        arguments: Vec<ValOrMut>,
    ) -> EvalControlFlowResult {
        // Use the new module for the duration of the function call.
        mem::swap(&mut self.module_id, &mut module_id);

        // Call the function.
        let module = self.compiler_session.expect_fresh_module(self.module_id);
        let function_data = module.get_function_by_id(local_id).unwrap();
        let locals = &function_data.locals;
        let result = function_data.code.call(arguments, self, locals);

        // Restore the previous module.
        mem::swap(&mut self.module_id, &mut module_id);

        // Return the call result.
        result
    }
}

/// A place in the environment (absolute position), with a path to a compound value
/// This behaves like a global address to a Value given our Mutable Value Semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Place {
    // index of target variable, absolute in the environment, to allow to access parent frames
    pub target: usize,
    // path within the compound value located at `target`
    pub path: Vec<isize>,
}

impl Place {
    /// Return a path and an index of a variable in the environment that is for sure a Value
    fn resolved_path_and_index(&self, ctx: &EvalCtx) -> (VecDeque<isize>, usize) {
        let mut path = self.path.iter().copied().collect::<VecDeque<_>>();
        let mut index = self.target;
        loop {
            match &ctx.environment[index] {
                ValOrMut::Val(_target) => {
                    break;
                }
                ValOrMut::Mut(place) => {
                    index = place.target;
                    for &index in place.path.iter().rev() {
                        path.push_front(index);
                    }
                }
            };
        }
        (path, index)
    }

    /// Get a mutable reference to the target value
    pub fn target_mut<'c>(&self, ctx: &'c mut EvalCtx) -> Result<&'c mut Value, RuntimeErrorKind> {
        let (path, index) = self.resolved_path_and_index(ctx);
        let mut target = ctx.environment[index].as_val_mut().unwrap();
        for &index in path.iter() {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get_mut(index as usize).unwrap(),
                Native(primitive) => {
                    // iif the primitive is our standard Array, we can access its elements
                    let array = primitive
                        .as_mut_any()
                        .downcast_mut::<array::Array>()
                        .unwrap();
                    let len = array.len();
                    match array.get_mut_signed(index) {
                        Some(target) => target,
                        None => {
                            return Err(RuntimeErrorKind::ArrayAccessOutOfBounds { index, len });
                        }
                    }
                }
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }

    /// Get a shared reference to the target value
    pub fn target_ref<'c>(&self, ctx: &'c EvalCtx) -> Result<&'c Value, RuntimeErrorKind> {
        let (path, index) = self.resolved_path_and_index(ctx);
        let mut target = ctx.environment[index].as_val().unwrap();
        for &index in path.iter() {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get(index as usize).unwrap(),
                Native(primitive) => {
                    // iif the primitive is our standard Array, we can access its elements
                    let array = NativeValue::as_any(&**primitive)
                        .downcast_ref::<array::Array>()
                        .unwrap();
                    let len = array.len();
                    match array.get_signed(index) {
                        Some(target) => target,
                        None => {
                            return Err(RuntimeErrorKind::ArrayAccessOutOfBounds { index, len });
                        }
                    }
                }
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }
}

impl FormatWith<EvalCtx<'_>> for Place {
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &EvalCtx<'_>) -> std::fmt::Result {
        let Place { target, path } = self;
        let ctx = data;
        let relative_index = *target as isize - ctx.frame_base as isize;
        write!(f, "@{relative_index}")?;
        if !path.is_empty() {
            write!(f, ".")?;
        }
        write_with_separator(path, ".", f)?;
        if relative_index < 0 {
            write!(f, " (in a previous frame)")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum ControlFlow<V> {
    Continue(V),
    Return(Value),
}
impl ControlFlow<Value> {
    pub fn into_value(self) -> Value {
        match self {
            ControlFlow::Continue(value) => value,
            ControlFlow::Return(value) => value,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BacktraceFrame {
    module_id: ModuleId,
    function_id: FunctionId,
    #[allow(dead_code)]
    frame_base: usize,
    location: Location,
}
impl FormatWith<(&SourceTable, &Modules)> for BacktraceFrame {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, &Modules),
    ) -> std::fmt::Result {
        let (source_table, modules) = data;
        let mut module_path = modules
            .get_name(self.module_id)
            .map(|name| format!("{name}"))
            .unwrap_or("<unknown>".to_string());
        let module = &modules
            .get(self.module_id)
            .unwrap()
            .module
            .as_ref()
            .unwrap();
        match self.function_id {
            FunctionId::Local(id) => {
                let local_name = module.get_function_name_by_id(id).unwrap();
                write!(f, "{module_path}::{local_name}")?
            }
            FunctionId::Import(id) => {
                let slot = module.get_import_fn_slot(id).unwrap();
                module_path = format!("{}", slot.module);
                use ImportFunctionTarget::*;
                match &slot.target {
                    TraitImplMethod { key, index } => {
                        let trait_ref = key.trait_ref();
                        write!(
                            f,
                            "{}",
                            trait_ref.qualified_method_name(*index as usize, key.input_tys())
                        )?
                    }
                    NamedFunction(fn_name) => write!(f, "{module_path}::{fn_name}")?,
                }
            }
        };
        write!(f, " at {}", self.location.format_with(source_table))
    }
}

/// A runtime error that occurred during evaluation and is propagated upwards.
#[derive(Debug, Clone, new)]
pub struct RuntimeError {
    /// The kind of the error.
    pub(crate) kind: RuntimeErrorKind,
    /// The location where the error occurred, None if in native code.
    pub(crate) location: Option<Location>,
    /// The call stack at the time of the error.
    #[new(default)]
    pub(crate) backtrace: Vec<BacktraceFrame>,
}
impl RuntimeError {
    pub fn new_native(kind: RuntimeErrorKind) -> Self {
        Self {
            kind,
            location: None,
            backtrace: Vec::new(),
        }
    }

    pub fn with_frame(
        self,
        module_id: ModuleId,
        function_id: FunctionId,
        frame_base: usize,
        location: Location,
    ) -> Self {
        let mut backtrace = self.backtrace;
        backtrace.push(BacktraceFrame {
            module_id,
            function_id,
            frame_base,
            location,
        });
        Self {
            kind: self.kind,
            location: self.location,
            backtrace,
        }
    }

    pub fn kind(&self) -> RuntimeErrorKind {
        self.kind.clone()
    }

    pub fn location(&self) -> Option<Location> {
        self.location
    }

    pub fn backtrace(&self) -> &Vec<BacktraceFrame> {
        &self.backtrace
    }

    pub fn top_most_location_in(&self, source_id: SourceId) -> Option<Location> {
        if let Some(location) = self.location
            && location.source_id == source_id
        {
            return Some(location);
        }
        for frame in &self.backtrace {
            if frame.location.source_id == source_id {
                return Some(frame.location);
            }
        }
        None
    }
}

impl FormatWith<(&SourceTable, &Modules)> for RuntimeError {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, &Modules),
    ) -> std::fmt::Result {
        write!(f, "Execution error: {}", self.kind)?;
        if let Some(location) = &self.location {
            write!(f, " at {}", location.format_with(data.0))?;
        }
        writeln!(f)?;
        if !self.backtrace.is_empty() {
            writeln!(f, "stack backtrace:")?;
            for (i, frame) in self.backtrace.iter().enumerate() {
                writeln!(f, "  {i}: {}", frame.format_with(data))?;
            }
        }
        Ok(())
    }
}

/// The result of evaluating an HIR node, either a control flow action or a runtime error.
pub type EvalControlFlowResult = Result<ControlFlow<Value>, RuntimeError>;

/// The result of evaluating an HIR node, either a value or a runtime error.
pub type EvalResult = Result<Value, RuntimeError>;

pub fn cont(value: Value) -> EvalControlFlowResult {
    Ok(ControlFlow::Continue(value))
}

pub fn ret(value: Value) -> EvalControlFlowResult {
    Ok(ControlFlow::Return(value))
}

/// Helper macro to evaluate a node and propagate Return, or extract Continue value.
/// Usage: eval_or_return!(node.eval_with_ctx(ctx))
/// Returns early with Return, or provides the unwrapped Value.
macro_rules! eval_or_return {
    ($expr:expr) => {
        match $expr? {
            ControlFlow::Return(val) => return Ok(ControlFlow::Return(val)),
            ControlFlow::Continue(val) => val,
        }
    };
}

/// Evaluate this node and return the result.
pub fn eval_node(
    arena: &NodeArena,
    id: NodeId,
    module_id: ModuleId,
    locals: &[LocalDecl],
    compiler_session: &CompilerSession,
) -> EvalControlFlowResult {
    let mut ctx = EvalCtx::new(module_id, compiler_session);
    eval_node_with_ctx(arena, id, &mut ctx, locals)
}

/// Evaluate this node given the environment and return the result.
pub fn eval_node_with_ctx(
    arena: &NodeArena,
    id: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    use NodeKind::*;
    let node = &arena[id];
    match &node.kind {
        Immediate(immediate) => cont(immediate.value.clone()),
        BuildClosure(build_closure) => eval_build_closure(arena, build_closure, ctx, locals),
        Apply(app) => eval_apply(arena, app, node.span, ctx, locals),
        StaticApply(app) => eval_static_apply(arena, app, node.span, ctx, locals),
        TraitFnApply(_) => {
            panic!(
                "Trait function application should not be executed, but transformed to StaticApply"
            );
        }
        GetTraitFunction(_) => {
            panic!(
                "Trait function value should not be executed, but transformed to a function value"
            );
        }
        GetFunction(get_fn) => {
            let (function, module_id) = ctx.get_function_local_id(get_fn.function);
            cont(Value::function(function, module_id))
        }
        GetDictionary(get_dict) => {
            let value = ctx.get_dictionary(get_dict.dictionary);
            cont(value)
        }
        EnvStore(node) => eval_env_store(arena, node, arena[id].span, ctx, locals),
        EnvLoad(node) => eval_env_load(arena, id, node, ctx),
        Return(node) => eval_return(arena, *node, ctx, locals),
        Block(nodes) => eval_block(arena, nodes, ctx, locals),
        Assign(assignment) => eval_assign(arena, id, assignment, ctx, locals),
        Tuple(nodes) | Record(nodes) => eval_tuple(arena, nodes, ctx, locals),
        Project(data, index) => eval_project(arena, *data, *index, ctx, locals),
        FieldAccess(_, _) => {
            panic!("String projection should not be executed, but transformed to ProjectLocal");
        }
        ProjectAt(data, index) => eval_project_at(arena, id, *data, *index, ctx, locals),
        Variant(tag, payload) => eval_variant(arena, *tag, *payload, ctx, locals),
        ExtractTag(node) => eval_extract_tag(arena, *node, ctx, locals),
        Array(nodes) => eval_array(arena, nodes, ctx, locals),
        Index(array, index) => eval_index(arena, id, *array, *index, ctx, locals),
        Case(case) => eval_case(arena, case, ctx, locals),
        Loop(body) => eval_loop(arena, *body, ctx, locals),
        SoftBreak => {
            ctx.break_loop = true;
            cont(Value::unit())
        }
        Unimplemented => {
            panic!("Unimplemented HIR node executed!")
        }
    }
}

#[inline(never)]
fn eval_build_closure(
    arena: &NodeArena,
    build_closure: &hir::BuildClosure,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let captured = eval_or_return!(eval_nodes(arena, &build_closure.captures, ctx, locals));
    // Note: function should be GetFunction or similar immediate - returns not allowed here.
    let function_value =
        eval_node_with_ctx(arena, build_closure.function, ctx, locals)?.into_value();
    let function_value = function_value.into_function().unwrap();
    let function_value =
        FunctionValue::new(function_value.function, function_value.module, captured);
    cont(Value::Function(b(function_value)))
}

#[inline(never)]
fn eval_apply(
    arena: &NodeArena,
    app: &hir::Application,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Evaluate left-to-right: function first, then arguments (matches Rust semantics).
    let function_value = eval_or_return!(eval_node_with_ctx(arena, app.function, ctx, locals));
    let function_value = function_value.as_function().unwrap();
    let arg_passing = ctx.function_value_argument_passing(function_value);
    let args_ty = {
        arena[app.function]
            .ty
            .data()
            .as_function()
            .expect("Apply needs a function type")
            .args
            .clone()
    };
    let arguments = eval_or_return!(eval_args(
        arena,
        &app.arguments,
        &args_ty,
        arg_passing,
        ctx,
        locals
    ));
    ctx.call_function_value(function_value, arguments, span)
}

#[inline(never)]
fn eval_static_apply(
    arena: &NodeArena,
    app: &hir::StaticApplication,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let arg_passing = ctx.function_id_argument_passing(app.function);
    let arguments = eval_or_return!(eval_args(
        arena,
        &app.arguments,
        &app.ty.args,
        arg_passing,
        ctx,
        locals
    ));
    ctx.call_function_id(app.function, arguments, span)
}

#[inline(never)]
fn eval_env_store(
    arena: &NodeArena,
    node: &hir::EnvStore,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
    if ctx.environment.len() >= ctx.stack_limit {
        return Err(RuntimeError::new(
            RuntimeErrorKind::StackLimitExceeded {
                limit: ctx.stack_limit,
            },
            Some(span),
        ));
    }
    ctx.environment.push(ValOrMut::Val(value));
    #[cfg(debug_assertions)]
    ctx.environment_names
        .push(locals[node.id.as_index()].name.0);
    cont(Value::unit())
}

#[inline(never)]
fn eval_env_load(
    arena: &NodeArena,
    id: NodeId,
    node: &hir::EnvLoad,
    ctx: &mut EvalCtx,
) -> EvalControlFlowResult {
    let index = ctx.frame_base + node.index as usize;
    cont(
        ctx.environment[index]
            .as_value(ctx)
            .map_err(|err| RuntimeError::new(err, Some(arena[id].span)))?,
    )
}

#[inline(never)]
fn eval_return(
    arena: &NodeArena,
    node: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    ret(eval_node_with_ctx(arena, node, ctx, locals)?.into_value())
}

#[inline(never)]
fn eval_block(
    arena: &NodeArena,
    nodes: &[NodeId],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let env_size = ctx.environment.len();
    let mut last_value = Value::unit();
    for node in nodes.iter() {
        match eval_node_with_ctx(arena, *node, ctx, locals)? {
            ControlFlow::Return(val) => {
                // Early return: clean up environment and propagate.
                ctx.environment.truncate(env_size);
                #[cfg(debug_assertions)]
                ctx.environment_names.truncate(env_size);
                return Ok(ControlFlow::Return(val));
            }
            ControlFlow::Continue(val) => {
                last_value = val;
            }
        }
    }
    // Normal block completion.
    ctx.environment.truncate(env_size);
    #[cfg(debug_assertions)]
    ctx.environment_names.truncate(env_size);
    cont(last_value)
}

#[inline(never)]
fn eval_assign(
    arena: &NodeArena,
    id: NodeId,
    assignment: &hir::Assignment,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Evaluate left-to-right: place first, then value (matches Rust semantics).
    let place = eval_or_return!(resolve_node_place(arena, assignment.place, ctx, locals));
    let value = eval_or_return!(eval_node_with_ctx(arena, assignment.value, ctx, locals));
    let target_ref = place
        .target_mut(ctx)
        .map_err(|err| RuntimeError::new(err, Some(arena[id].span)))?;
    *target_ref = value;
    cont(Value::unit())
}

#[inline(never)]
fn eval_tuple(
    arena: &NodeArena,
    nodes: &[NodeId],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Note: record values are stored as tuples.
    let values = eval_or_return!(eval_nodes(arena, nodes, ctx, locals));
    cont(Value::Tuple(b(values.into())))
}

#[inline(never)]
fn eval_project(
    arena: &NodeArena,
    data: NodeId,
    index: usize,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let value = eval_or_return!(eval_node_with_ctx(arena, data, ctx, locals));
    cont(match value {
        Value::Tuple(tuple) => tuple.into_iter().nth(index).unwrap(),
        Value::Variant(variant) => variant.value,
        _ => panic!("Cannot project from a non-compound value"),
    })
}

#[inline(never)]
fn eval_project_at(
    arena: &NodeArena,
    id: NodeId,
    data: NodeId,
    index: usize,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let value = eval_or_return!(eval_node_with_ctx(arena, data, ctx, locals));
    let index = ctx.frame_base + index;
    let index = ctx.environment[index]
        .as_value(ctx)
        .map_err(|err| RuntimeError::new(err, Some(arena[id].span)))?
        .into_primitive_ty::<isize>()
        .unwrap();
    cont(match value {
        Value::Tuple(tuple) => tuple.into_iter().nth(index as usize).unwrap(),
        _ => panic!("Cannot access field from a non-compound value"),
    })
}

#[inline(never)]
fn eval_variant(
    arena: &NodeArena,
    tag: Ustr,
    payload: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let value = eval_or_return!(eval_node_with_ctx(arena, payload, ctx, locals));
    cont(Value::raw_variant(tag, value))
}

#[inline(never)]
fn eval_extract_tag(
    arena: &NodeArena,
    node: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let value = eval_or_return!(eval_node_with_ctx(arena, node, ctx, locals));
    let variant = value.into_variant().unwrap();
    cont(Value::native(variant.tag_as_isize()))
}

#[inline(never)]
fn eval_array(
    arena: &NodeArena,
    nodes: &[NodeId],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let values = eval_or_return!(eval_nodes(arena, nodes, ctx, locals));
    cont(Value::native(array::Array::from_vec(values)))
}

#[inline(never)]
fn eval_index(
    arena: &NodeArena,
    id: NodeId,
    array: NodeId,
    index: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Evaluate left-to-right: array first, then index (matches Rust semantics).
    let mut array = eval_or_return!(eval_node_with_ctx(arena, array, ctx, locals))
        .into_primitive_ty::<array::Array>()
        .unwrap();
    let index = eval_or_return!(eval_node_with_ctx(arena, index, ctx, locals))
        .into_primitive_ty::<isize>()
        .unwrap();
    match array.get_mut_signed(index) {
        Some(value) => cont(value.clone()),
        None => {
            let len = array.len();
            Err(RuntimeError::new(
                RuntimeErrorKind::ArrayAccessOutOfBounds { index, len },
                Some(arena[id].span),
            ))
        }
    }
}

#[inline(never)]
fn eval_case(
    arena: &NodeArena,
    case: &hir::Case,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let value = eval_or_return!(eval_node_with_ctx(arena, case.value, ctx, locals));
    let value = value.to_literal_value().unwrap_or_else(|| {
        panic!(
            "Case evaluated a non-literal scrutinee: {}. This HIR should have been rejected before evaluation.",
            value.to_string_repr()
        )
    });
    for (alternative, node) in &case.alternatives {
        if value == *alternative {
            return eval_node_with_ctx(arena, *node, ctx, locals);
        }
    }
    eval_node_with_ctx(arena, case.default, ctx, locals)
}

#[inline(never)]
fn eval_loop(
    arena: &NodeArena,
    body: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let break_loop = ctx.break_loop;
    ctx.break_loop = false;
    while !ctx.break_loop {
        eval_or_return!(eval_node_with_ctx(arena, body, ctx, locals));
    }
    ctx.break_loop = break_loop;
    cont(Value::unit())
}

/// Return this node as a place in the environment.
pub fn resolve_node_place(
    arena: &NodeArena,
    id: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Place>, RuntimeError> {
    match eval_or_return!(try_resolve_node_place(arena, id, ctx, locals)) {
        Some(place) => Ok(ControlFlow::Continue(place)),
        None => panic!("Cannot resolve a non-place node"),
    }
}

fn eval_nodes(
    arena: &NodeArena,
    nodes: &[NodeId],
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Vec<Value>>, RuntimeError> {
    let mut results = Vec::with_capacity(nodes.len());
    for &node in nodes {
        results.push(eval_or_return!(eval_node_with_ctx(
            arena, node, ctx, locals
        )));
    }
    Ok(ControlFlow::Continue(results))
}

fn eval_args(
    arena: &NodeArena,
    args: &[NodeId],
    args_ty: &[FnArgType],
    arg_passing: Option<&[NativeArgPassing]>,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Vec<ValOrMut>>, RuntimeError> {
    // Automatically cast mutable references to values if the function expects values.
    let mut results = Vec::with_capacity(args.len());
    assert_eq!(args.len(), args_ty.len());
    for (index, (arg, ty)) in args.iter().zip(args_ty).enumerate() {
        let is_mutable = ty
            .mut_ty
            .as_resolved()
            .expect("Unresolved mutability variable found during execution")
            .is_mutable();
        let borrow_as_shared_ref = arg_passing
            .and_then(|passing| passing.get(index))
            .is_some_and(|passing| *passing == NativeArgPassing::SharedRef);
        results.push(if is_mutable {
            ValOrMut::Mut(eval_or_return!(resolve_node_place(
                arena, *arg, ctx, locals
            )))
        } else if borrow_as_shared_ref {
            match eval_or_return!(try_resolve_node_place(arena, *arg, ctx, locals)) {
                Some(place) => ValOrMut::Mut(place),
                None => ValOrMut::Val(eval_or_return!(eval_node_with_ctx(
                    arena, *arg, ctx, locals
                ))),
            }
        } else {
            ValOrMut::Val(eval_or_return!(eval_node_with_ctx(
                arena, *arg, ctx, locals
            )))
        });
    }
    Ok(ControlFlow::Continue(results))
}

fn try_resolve_node_place(
    arena: &NodeArena,
    id: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Option<Place>>, RuntimeError> {
    let node = &arena[id];
    use NodeKind::*;
    Ok(ControlFlow::Continue(Some(match &node.kind {
        Project(node, index) => {
            let Some(mut place) =
                eval_or_return!(try_resolve_node_place(arena, *node, ctx, locals))
            else {
                return Ok(ControlFlow::Continue(None));
            };
            place.path.push(*index as isize);
            place
        }
        ProjectAt(node, index) => {
            let Some(mut place) =
                eval_or_return!(try_resolve_node_place(arena, *node, ctx, locals))
            else {
                return Ok(ControlFlow::Continue(None));
            };
            let index = ctx.frame_base + *index;
            let index_value = ctx.environment[index]
                .as_value(ctx)
                .map_err(|err| RuntimeError::new(err, Some(arena[id].span)))?;
            let index = index_value.into_primitive_ty::<isize>().unwrap();
            place.path.push(index);
            place
        }
        Index(array, index) => {
            let Some(mut place) =
                eval_or_return!(try_resolve_node_place(arena, *array, ctx, locals))
            else {
                return Ok(ControlFlow::Continue(None));
            };
            let index_value = eval_or_return!(eval_node_with_ctx(arena, *index, ctx, locals));
            let index = index_value.into_primitive_ty::<isize>().unwrap();
            place.path.push(index);
            place
        }
        EnvLoad(node) => Place {
            // By using frame_base here, we allow to access parent frames
            // when the ResolvedPlace is used in a child function.
            target: ctx.frame_base + node.index as usize,
            path: Vec::new(),
        },
        _ => return Ok(ControlFlow::Continue(None)),
    })))
}
