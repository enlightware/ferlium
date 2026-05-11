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

use crate::module::id::Id;
use crate::std::value::{VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX, VALUE_TRAIT};
use crate::{
    CompilerSession, Location, SourceId, SourceTable,
    compiler::error::RuntimeErrorKind,
    format::{FormatWith, write_with_separator},
    hir::function::ArgPassing,
    hir::value::{FunctionHiddenArgValue, FunctionValue, NativeValue, Value},
    module::{
        FunctionId, LocalClone, LocalDecl, LocalDrop, LocalFunctionId, ModuleFunction, ModuleId,
        TraitDictionary, TraitDictionaryEntry, TraitDictionaryId, TraitImplId,
    },
    std::{array, logic::bool_type, math::int_type},
    types::{
        r#trait::TraitDictionaryEntryIndex,
        r#type::{FnArgType, Type},
        type_like::TypeLike,
    },
};
use crate::{
    Modules,
    hir::{self, NodeArena, NodeId, NodeKind},
};

use crate::module::ImportFunctionTarget;

/// Either a value or a unique mutable reference to a value.
/// This allows to implement the mutable value semantics.
#[derive(Debug, EnumAsInner)]
pub enum ValOrMut {
    /// A value, itself
    Val(Value),
    /// Runtime trait dictionary metadata.
    Dictionary(TraitDictionaryId),
    /// A shared reference to value storage outside the environment.
    ///
    /// This is used for interpreter-only call setup, for example when cloning a
    /// closure environment without first duplicating it with Rust `Clone`.
    Ref(*const Value),
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
            ValOrMut::Dictionary(_) | ValOrMut::Ref(_) | ValOrMut::Mut(_) => None,
        }
    }

    pub fn as_mut_primitive<'a, 'b, T: 'static>(
        &self,
        ctx: &'a mut EvalCtx<'b>,
    ) -> Result<Option<&'a mut T>, RuntimeErrorKind> {
        Ok(match self {
            ValOrMut::Val(_) => None,
            ValOrMut::Dictionary(_) => None,
            ValOrMut::Ref(_) => None,
            ValOrMut::Mut(place) => place.target_mut(ctx)?.as_primitive_ty_mut::<T>(),
        })
    }

    pub fn as_primitive<'a, T: 'static>(
        &'a self,
        ctx: &'a EvalCtx<'_>,
    ) -> Result<Option<&'a T>, RuntimeErrorKind> {
        Ok(match self {
            ValOrMut::Val(val) => val.as_primitive_ty::<T>(),
            ValOrMut::Dictionary(_) => None,
            ValOrMut::Ref(value) => {
                // SAFETY: `Ref` entries are only installed for the duration of a
                // synchronous interpreter call, and the environment frame is
                // truncated before the borrowed storage can go away.
                unsafe { &**value }.as_primitive_ty::<T>()
            }
            ValOrMut::Mut(place) => place.target_ref(ctx)?.as_primitive_ty::<T>(),
        })
    }

    pub fn as_value_ref<'a>(&'a self, ctx: &'a EvalCtx<'_>) -> Result<&'a Value, RuntimeErrorKind> {
        Ok(match self {
            ValOrMut::Val(value) => {
                if matches!(value, Value::Uninit) {
                    panic!("attempted to read an uninitialized value");
                }
                value
            }
            ValOrMut::Dictionary(_) => panic!("attempted to read a trait dictionary as a Value"),
            ValOrMut::Ref(value) => {
                // SAFETY: see `ValOrMut::as_primitive`.
                unsafe { &**value }
            }
            ValOrMut::Mut(place) => place.target_ref(ctx)?,
        })
    }

    pub fn as_place(&self) -> &Place {
        match self {
            ValOrMut::Val(_) | ValOrMut::Dictionary(_) | ValOrMut::Ref(_) => {
                panic!("Cannot get a place from a value")
            }
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
            ValOrMut::Dictionary(_) => write!(f, "dictionary metadata"),
            ValOrMut::Ref(value) => {
                write!(f, "ref. ")?;
                // SAFETY: see `ValOrMut::as_primitive`.
                unsafe { &**value }.format_as_string_repr(f)
            }
            ValOrMut::Mut(place) => {
                write!(f, "mut. ref. {}", place.format_with(data))
            }
        }
    }
}

fn hidden_arg_to_val_or_mut(arg: FunctionHiddenArgValue) -> ValOrMut {
    match arg {
        FunctionHiddenArgValue::TraitDictionary(dictionary) => ValOrMut::Dictionary(dictionary),
        FunctionHiddenArgValue::FieldIndex(index) => ValOrMut::Val(Value::native(index)),
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
                        imp.methods[index.as_index()]
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
    ) -> Option<&'static [ArgPassing]> {
        self.get_module_function(local_id, module_id)
            .code
            .argument_passing()
    }

    pub fn function_id_argument_passing(
        &self,
        function_id: FunctionId,
    ) -> Option<&'static [ArgPassing]> {
        let (local_id, module_id) = self.get_function_local_id(function_id);
        self.function_argument_passing(local_id, module_id)
    }

    pub fn function_value_argument_passing(
        &self,
        function_value: &FunctionValue,
    ) -> Option<&'static [ArgPassing]> {
        let passing =
            self.function_argument_passing(function_value.function_id, function_value.module_id)?;
        Some(&passing[function_value.hidden_args.len() + function_value.closure_env_len..])
    }

    /// Resolve a module-relative impl reference to a canonical runtime dictionary ID.
    pub fn get_dictionary_id(&self, dictionary: TraitImplId) -> TraitDictionaryId {
        let module = self.compiler_session.expect_fresh_module(self.module_id);
        use TraitImplId::*;
        match dictionary {
            Local(id) => TraitDictionaryId {
                module_id: self.module_id,
                impl_id: id,
            },
            Import(id) => {
                let slot = module.get_import_impl_slot(id).unwrap();
                let imported_module = self.compiler_session.expect_fresh_module(slot.module);
                let impl_id = imported_module
                    .get_impl_id_by_trait_key(&slot.key)
                    .unwrap_or_else(|| panic!("imported trait impl not found: {:?}", slot.key));
                TraitDictionaryId {
                    module_id: slot.module,
                    impl_id,
                }
            }
        }
    }

    pub fn dictionary_value(&self, dictionary: TraitDictionaryId) -> &TraitDictionary {
        let module = self
            .compiler_session
            .expect_fresh_module(dictionary.module_id);
        &module
            .get_impl_data(dictionary.impl_id)
            .unwrap_or_else(|| panic!("trait dictionary impl not found: {:?}", dictionary))
            .dictionary_value
    }

    /// Call a function value along containing its module context.
    pub fn call_function_value(
        &mut self,
        function_value: &FunctionValue,
        arguments: Vec<ValOrMut>,
        location: Location,
    ) -> EvalControlFlowResult {
        let local_id = function_value.function_id;
        let module_id = function_value.module_id;

        #[cfg(debug_assertions)]
        self.stack_trace
            .push(StackEntry::new(local_id, module_id, self.environment.len()));

        let closure_env_dictionary = function_value
            .closure_env_value_dictionary
            .as_ref()
            .cloned();
        let closure_env_temp = if function_value.closure_env_len == 0 {
            None
        } else {
            let dictionary = closure_env_dictionary
                .expect("closures with captured values must carry a Value dictionary");
            let closure_env = call_value_clone_for_temp(
                self,
                dictionary,
                ValOrMut::Ref(&function_value.closure_env as *const Value),
                location,
            )?;
            let index = self.environment.len();
            self.environment.push(ValOrMut::Val(closure_env));
            #[cfg(debug_assertions)]
            self.environment_names.push(ustr("$closure_env_call"));
            Some(index)
        };

        let arguments = if function_value.hidden_args.is_empty()
            && function_value.closure_env_len == 0
        {
            arguments
        } else {
            let mut prepared = Vec::with_capacity(
                function_value.hidden_args.len() + function_value.closure_env_len + arguments.len(),
            );
            prepared.extend(
                function_value
                    .hidden_args
                    .iter()
                    .copied()
                    .map(hidden_arg_to_val_or_mut),
            );
            if let Some(target) = closure_env_temp {
                prepared.extend((0..function_value.closure_env_len).map(|index| {
                    ValOrMut::Mut(Place {
                        target,
                        path: vec![index as isize],
                    })
                }));
            }
            prepared.extend(arguments);
            prepared
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

        if let Some(target) = closure_env_temp {
            let drop_result = call_value_drop_for_temp(
                self,
                closure_env_dictionary.expect("closure environment dictionary disappeared"),
                ValOrMut::Mut(Place {
                    target,
                    path: Vec::new(),
                }),
                location,
            );
            #[cfg(debug_assertions)]
            self.environment_names.pop();
            self.environment.pop();
            let result = result.and_then(|result| {
                drop_result?;
                Ok(result)
            });
            #[cfg(debug_assertions)]
            self.stack_trace.pop();
            return result;
        }

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
                ValOrMut::Dictionary(_) => {
                    panic!("cannot mutably access trait dictionary metadata");
                }
                ValOrMut::Ref(_) => {
                    panic!("cannot mutably access shared reference storage");
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
                Variant(variant) if index == 0 => &mut variant.value,
                Native(primitive) => {
                    // iif the primitive is our standard Array, we can access its elements
                    let array = primitive
                        .as_mut()
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
                Uninit => panic!("cannot access a field of an uninitialized value"),
                Variant(_) => panic!("Cannot access a variant payload with a non-zero index"),
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }

    /// Get a shared reference to the target value
    pub fn target_ref<'c>(&self, ctx: &'c EvalCtx) -> Result<&'c Value, RuntimeErrorKind> {
        let mut path = self.path.iter().copied().collect::<VecDeque<_>>();
        let mut index = self.target;
        let mut target = loop {
            match &ctx.environment[index] {
                ValOrMut::Val(target) => break target,
                ValOrMut::Dictionary(_) => {
                    panic!("cannot read trait dictionary metadata as a Value")
                }
                ValOrMut::Ref(target) => {
                    // SAFETY: see `ValOrMut::as_primitive`.
                    break unsafe { &**target };
                }
                ValOrMut::Mut(place) => {
                    index = place.target;
                    for &index in place.path.iter().rev() {
                        path.push_front(index);
                    }
                }
            };
        };
        for &index in path.iter() {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get(index as usize).unwrap(),
                Variant(variant) if index == 0 => &variant.value,
                Native(primitive) => {
                    // iif the primitive is our standard Array, we can access its elements
                    let array = NativeValue::as_any(primitive.as_ref())
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
                Uninit => panic!("cannot read a field of an uninitialized value"),
                Variant(_) => panic!("Cannot access a variant payload with a non-zero index"),
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        if matches!(target, Value::Uninit) {
            panic!("attempted to read an uninitialized value");
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

#[derive(Debug)]
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
                            trait_ref.qualified_method_name(*index, key.input_tys())
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
        Immediate(immediate) => cont(immediate.value.clone().into_value()),
        Uninit => cont(Value::uninit()),
        BuildClosure(build_closure) => eval_build_closure(arena, build_closure, ctx, locals),
        Apply(app) => eval_apply(arena, app, node.span, ctx, locals),
        FunctionClone(node) => eval_function_clone(arena, node, arena[id].span, ctx, locals),
        FunctionDrop(node) => eval_function_drop(arena, node, arena[id].span, ctx, locals),
        ValueClone(node) => eval_value_clone(arena, node, arena[id].span, ctx, locals),
        TrivialCopy(node) => eval_trivial_copy(arena, node, arena[id].span, ctx, locals),
        StaticApply(app) => eval_static_apply(arena, app, node.span, ctx, locals),
        TraitMethodApply(_) => {
            panic!(
                "Trait function application should not be executed, but transformed to StaticApply"
            );
        }
        GetTraitMethod(_) => {
            panic!(
                "Trait function value should not be executed, but transformed to a function value"
            );
        }
        GetTraitAssociatedConst(_) => {
            panic!(
                "Trait associated const should not be executed, but transformed to an immediate or dictionary projection"
            );
        }
        GetTraitDictionary(_) => {
            panic!(
                "Trait dictionary should not be executed, but transformed to a concrete dictionary or dictionary load"
            );
        }
        GetFunction(get_fn) => {
            let (function, module_id) = ctx.get_function_local_id(get_fn.function);
            cont(Value::function(function, module_id))
        }
        GetDictionary(get_dict) => {
            let _ = get_dict;
            panic!("GetDictionary is runtime metadata and should not be evaluated as a Value")
        }
        EnvStore(node) => eval_env_store(arena, node, arena[id].span, ctx, locals),
        EnvDrop(node) => eval_env_drop(node, arena[id].span, ctx, locals),
        EnvMove(node) => eval_env_move(node, arena[id].span, ctx),
        EnvLoad(node) => eval_env_load(arena, id, node, ctx, locals),
        Return(node) => eval_return(arena, *node, ctx, locals),
        Block(nodes) => eval_block(arena, nodes, ctx, locals),
        Assign(assignment) => eval_assign(arena, id, assignment, ctx, locals),
        Tuple(nodes) | Record(nodes) => eval_tuple(arena, nodes, ctx, locals),
        Project(data, index) => eval_project(arena, id, *data, *index, ctx, locals),
        FieldAccess(_, _) => {
            panic!("String projection should not be executed, but transformed to ProjectLocal");
        }
        ProjectAt(data, index) => eval_project_at(arena, id, *data, *index, ctx, locals),
        Variant(tag, payload) => eval_variant(arena, *tag, *payload, ctx, locals),
        ExtractTag(node) => eval_extract_tag(arena, *node, ctx, locals),
        Array(nodes) => eval_array(arena, nodes, ctx, locals),
        Index(index) => eval_index(arena, id, index, ctx, locals),
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
    let mut hidden_args = Vec::with_capacity(build_closure.dictionary_captures.len());
    for &capture in &build_closure.dictionary_captures {
        hidden_args.push(eval_or_return!(eval_function_hidden_arg_node(
            arena, capture, ctx, locals
        )));
    }
    let captures = eval_or_return!(eval_nodes(arena, &build_closure.captures, ctx, locals));
    let captures_value_dictionary = if let Some(dict) = build_closure.captures_value_dictionary {
        Some(eval_or_return!(eval_dictionary_metadata_node(
            arena, dict, ctx, locals
        )))
    } else {
        None
    };
    // Note: function should be GetFunction or similar immediate - returns not allowed here.
    let function_value =
        eval_node_with_ctx(arena, build_closure.function, ctx, locals)?.into_value();
    let function_value = function_value.into_function().unwrap();
    let function_value = FunctionValue::closure(
        function_value.function_id,
        function_value.module_id,
        hidden_args,
        captures,
        captures_value_dictionary,
    );
    cont(Value::function_value(function_value))
}

fn eval_function_hidden_arg_node(
    arena: &NodeArena,
    node: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<FunctionHiddenArgValue>, RuntimeError> {
    if let Some(dictionary) =
        eval_or_return!(try_dictionary_metadata_node(arena, node, ctx, locals))
    {
        return Ok(ControlFlow::Continue(
            FunctionHiddenArgValue::TraitDictionary(dictionary),
        ));
    }
    let value = eval_or_return!(eval_node_with_ctx(arena, node, ctx, locals));
    let Some(index) = value.into_primitive_ty::<isize>() else {
        panic!("expected hidden function metadata to be a trait dictionary or field index");
    };
    Ok(ControlFlow::Continue(FunctionHiddenArgValue::FieldIndex(
        index,
    )))
}

fn eval_dictionary_metadata_node(
    arena: &NodeArena,
    node: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<TraitDictionaryId>, RuntimeError> {
    if let Some(dictionary) =
        eval_or_return!(try_dictionary_metadata_node(arena, node, ctx, locals))
    {
        return Ok(ControlFlow::Continue(dictionary));
    }
    panic!(
        "expected dictionary metadata node, got {:?}",
        arena[node].kind
    )
}

fn try_dictionary_metadata_node(
    arena: &NodeArena,
    node: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Option<TraitDictionaryId>>, RuntimeError> {
    if let Some(place) = eval_or_return!(try_resolve_node_place(arena, node, ctx, locals)) {
        if let Some(dictionary) = try_dictionary_from_place(&place, ctx) {
            return Ok(ControlFlow::Continue(Some(dictionary)));
        }
    }
    match &arena[node].kind {
        NodeKind::GetDictionary(get_dict) => Ok(ControlFlow::Continue(Some(
            ctx.get_dictionary_id(get_dict.dictionary),
        ))),
        _ => Ok(ControlFlow::Continue(None)),
    }
}

pub(crate) fn try_dictionary_from_place(place: &Place, ctx: &EvalCtx) -> Option<TraitDictionaryId> {
    let mut path = place.path.iter().copied().collect::<VecDeque<_>>();
    let mut index = place.target;
    loop {
        match &ctx.environment[index] {
            ValOrMut::Dictionary(dictionary) => {
                return path.is_empty().then_some(*dictionary);
            }
            ValOrMut::Mut(place) => {
                index = place.target;
                for &index in place.path.iter().rev() {
                    path.push_front(index);
                }
            }
            ValOrMut::Val(_) | ValOrMut::Ref(_) => return None,
        }
    }
}

fn dictionary_from_local_index(
    ctx: &EvalCtx,
    local_index: usize,
    _span: Location,
) -> TraitDictionaryId {
    let place = Place {
        target: ctx.frame_base + local_index,
        path: Vec::new(),
    };
    try_dictionary_from_place(&place, ctx).unwrap_or_else(|| {
        panic!("expected local {local_index} to contain trait dictionary metadata")
    })
}

fn dictionary_entry_value(
    ctx: &EvalCtx,
    dictionary: TraitDictionaryId,
    entry_index: TraitDictionaryEntryIndex,
) -> Value {
    match ctx.dictionary_value(dictionary).entry(entry_index) {
        TraitDictionaryEntry::Method(function) => Value::function(function, dictionary.module_id),
        TraitDictionaryEntry::AssociatedConst(value) => Value::native(value),
    }
}

fn call_dictionary_method(
    ctx: &mut EvalCtx,
    dictionary: TraitDictionaryId,
    entry_index: TraitDictionaryEntryIndex,
    arguments: Vec<ValOrMut>,
    span: Location,
) -> EvalControlFlowResult {
    let TraitDictionaryEntry::Method(function) =
        ctx.dictionary_value(dictionary).entry(entry_index)
    else {
        panic!("attempted to call a non-method dictionary entry");
    };
    let function_value = FunctionValue::bare(function, dictionary.module_id);
    ctx.call_function_value(&function_value, arguments, span)
}

fn call_value_clone_with(
    ctx: &mut EvalCtx,
    source: ValOrMut,
    _span: Location,
    call: impl FnOnce(&mut EvalCtx, Vec<ValOrMut>) -> EvalControlFlowResult,
) -> Result<Value, RuntimeError> {
    let target_index = ctx.environment.len();
    ctx.environment.push(ValOrMut::Val(Value::uninit()));
    #[cfg(debug_assertions)]
    ctx.environment_names.push(ustr("$function_clone_target"));
    let target = Place {
        target: target_index,
        path: Vec::new(),
    };
    let result = call(ctx, vec![source, ValOrMut::Mut(target)]);
    #[cfg(debug_assertions)]
    ctx.environment_names.pop();
    let target = ctx.environment.pop().unwrap().into_val().unwrap();
    result?;
    if matches!(target, Value::Uninit) {
        panic!("Value::clone returned without initializing its target");
    }
    Ok(target)
}

pub(crate) fn call_value_clone_for_temp(
    ctx: &mut EvalCtx,
    dictionary: TraitDictionaryId,
    source: ValOrMut,
    span: Location,
) -> Result<Value, RuntimeError> {
    call_value_clone_with(ctx, source, span, |ctx, arguments| {
        call_dictionary_method(
            ctx,
            dictionary,
            VALUE_TRAIT.dictionary_method_index(VALUE_CLONE_METHOD_INDEX),
            arguments,
            span,
        )
    })
}

pub(crate) fn call_value_clone_to_target(
    ctx: &mut EvalCtx,
    dictionary: TraitDictionaryId,
    source: ValOrMut,
    target: Place,
    span: Location,
) -> EvalControlFlowResult {
    call_dictionary_method(
        ctx,
        dictionary,
        VALUE_TRAIT.dictionary_method_index(VALUE_CLONE_METHOD_INDEX),
        vec![source, ValOrMut::Mut(target.clone())],
        span,
    )?;
    let target_value = target
        .target_mut(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    if matches!(target_value, Value::Uninit) {
        panic!("Value::clone returned without initializing its target");
    }
    cont(Value::unit())
}

fn call_value_clone_dispatch_for_temp(
    ctx: &mut EvalCtx,
    clone: &LocalClone,
    source: ValOrMut,
    span: Location,
) -> Result<Value, RuntimeError> {
    call_value_clone_with(ctx, source, span, |ctx, arguments| match clone {
        LocalClone::Required => {
            panic!("LocalClone::Required should have been resolved before evaluation")
        }
        LocalClone::Static(function) => ctx.call_function_id(*function, arguments, span),
        LocalClone::Dictionary(dict_index) => {
            let dictionary = dictionary_from_local_index(ctx, *dict_index, span);
            call_dictionary_method(
                ctx,
                dictionary,
                VALUE_TRAIT.dictionary_method_index(VALUE_CLONE_METHOD_INDEX),
                arguments,
                span,
            )
        }
    })
}

pub(crate) fn call_value_drop_for_temp(
    ctx: &mut EvalCtx,
    dictionary: TraitDictionaryId,
    target: ValOrMut,
    span: Location,
) -> EvalControlFlowResult {
    let mut temp_target = None;
    let mut target_place = None;
    let target = match target {
        ValOrMut::Mut(place) => {
            target_place = Some(place.clone());
            ValOrMut::Mut(place)
        }
        ValOrMut::Ref(_) => panic!("cannot drop shared reference storage"),
        ValOrMut::Dictionary(_) => panic!("cannot drop trait dictionary metadata as a Value"),
        ValOrMut::Val(value) => {
            let target_index = ctx.environment.len();
            ctx.environment.push(ValOrMut::Val(value));
            #[cfg(debug_assertions)]
            ctx.environment_names.push(ustr("$function_drop_target"));
            temp_target = Some(target_index);
            target_place = Some(Place {
                target: target_index,
                path: Vec::new(),
            });
            ValOrMut::Mut(Place {
                target: target_index,
                path: Vec::new(),
            })
        }
    };
    let result = call_dictionary_method(
        ctx,
        dictionary,
        VALUE_TRAIT.dictionary_method_index(VALUE_DROP_METHOD_INDEX),
        vec![target],
        span,
    );
    if result.is_ok() {
        if let Some(place) = &target_place {
            discard_value_storage_at_place(ctx, place, span)?;
        }
    }
    if let Some(target_index) = temp_target {
        #[cfg(debug_assertions)]
        ctx.environment_names.pop();
        let value = ctx.environment.pop().unwrap();
        debug_assert_eq!(target_index, ctx.environment.len());
        debug_assert!(matches!(value, ValOrMut::Val(Value::Uninit)));
    }
    result?;
    cont(Value::unit())
}

fn discard_value_storage_at_place(
    ctx: &mut EvalCtx,
    place: &Place,
    span: Location,
) -> Result<(), RuntimeError> {
    let target = place
        .target_mut(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    let value = mem::replace(target, Value::uninit());
    value.discard_storage();
    Ok(())
}

#[inline(never)]
fn eval_function_clone(
    arena: &NodeArena,
    node: &hir::FunctionClone,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let owned_source;
    let (
        function_id,
        module_id,
        hidden_args,
        closure_env_ptr,
        closure_env_len,
        closure_env_value_dictionary,
    ) = {
        let source = if let Some(place) =
            eval_or_return!(try_resolve_node_place(arena, node.source, ctx, locals))
        {
            place
                .target_ref(ctx)
                .map_err(|err| RuntimeError::new(err, Some(span)))?
                .as_function()
                .unwrap()
        } else {
            owned_source = eval_or_return!(eval_node_with_ctx(arena, node.source, ctx, locals));
            owned_source.as_function().unwrap()
        };
        (
            source.function_id,
            source.module_id,
            source.hidden_args.clone(),
            &source.closure_env as *const Value,
            source.closure_env_len,
            source.closure_env_value_dictionary,
        )
    };
    let closure_env = if let Some(dictionary) = closure_env_value_dictionary {
        call_value_clone_for_temp(ctx, dictionary, ValOrMut::Ref(closure_env_ptr), span)?
    } else {
        Value::unit()
    };
    let target_function = FunctionValue {
        function_id,
        module_id,
        hidden_args,
        closure_env,
        closure_env_len,
        closure_env_value_dictionary,
    };
    let target = eval_or_return!(resolve_node_place(arena, node.target, ctx, locals));
    *target
        .target_mut(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))? =
        Value::function_value(target_function);
    cont(Value::unit())
}

#[inline(never)]
fn eval_function_drop(
    arena: &NodeArena,
    node: &hir::FunctionDrop,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let target = eval_or_return!(resolve_node_place(arena, node.target, ctx, locals));
    let Some((dictionary, captures)) = ({
        let target = target
            .target_mut(ctx)
            .map_err(|err| RuntimeError::new(err, Some(span)))?;
        let function = target.as_function_mut().unwrap();
        let dictionary = function.closure_env_value_dictionary;
        dictionary.map(|dictionary| {
            function.closure_env_len = 0;
            function.closure_env_value_dictionary = None;
            (
                dictionary,
                mem::replace(&mut function.closure_env, Value::uninit()),
            )
        })
    }) else {
        return cont(Value::unit());
    };
    call_value_drop_for_temp(ctx, dictionary, ValOrMut::Val(captures), span)
}

#[inline(never)]
fn eval_value_clone(
    arena: &NodeArena,
    node: &hir::ValueClone,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let source = match eval_or_return!(try_resolve_node_place(arena, node.source, ctx, locals)) {
        Some(place) => ValOrMut::Mut(place),
        None => ValOrMut::Val(eval_or_return!(eval_node_with_ctx(
            arena,
            node.source,
            ctx,
            locals
        ))),
    };
    let clone = node
        .clone
        .as_ref()
        .expect("ValueClone dispatch should have been resolved before evaluation");
    call_value_clone_dispatch_for_temp(ctx, clone, source, span).map(ControlFlow::Continue)
}

#[inline(never)]
fn eval_trivial_copy(
    arena: &NodeArena,
    node: &hir::TrivialCopy,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let place = eval_or_return!(resolve_node_place(arena, node.source, ctx, locals));
    cont(copy_trivial_value_from_place(
        &place,
        arena[node.source].ty,
        ctx,
        span,
    )?)
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
    let owned_function_value;
    let function_value = if let Some(place) =
        eval_or_return!(try_resolve_node_place(arena, app.function, ctx, locals))
    {
        let function_value = place
            .target_ref(ctx)
            .map_err(|err| RuntimeError::new(err, Some(span)))?
            .as_function()
            .unwrap();
        function_value.as_ref() as *const FunctionValue
    } else {
        owned_function_value =
            eval_or_return!(eval_node_with_ctx(arena, app.function, ctx, locals));
        owned_function_value.as_function().unwrap().as_ref() as *const FunctionValue
    };
    // SAFETY: the pointer either targets `owned_function_value`, kept alive in
    // this stack frame, or environment storage that the borrow checker prevents
    // from being mutably aliased by the call arguments.
    let function_value = unsafe { &*function_value };
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
    if ctx.environment.len() >= ctx.stack_limit {
        return Err(RuntimeError::new(
            RuntimeErrorKind::StackLimitExceeded {
                limit: ctx.stack_limit,
            },
            Some(span),
        ));
    }
    if let Some(clone) = &locals[node.id.as_index()].clone {
        let target_index = ctx.environment.len();
        ctx.environment.push(ValOrMut::Val(Value::uninit()));
        #[cfg(debug_assertions)]
        ctx.environment_names
            .push(locals[node.id.as_index()].name.0);
        let target = Place {
            target: target_index,
            path: Vec::new(),
        };
        let source = match eval_or_return!(try_resolve_node_place(arena, node.value, ctx, locals)) {
            Some(place) => ValOrMut::Mut(place),
            None => ValOrMut::Val(eval_or_return!(eval_node_with_ctx(
                arena, node.value, ctx, locals
            ))),
        };
        let arguments = vec![source, ValOrMut::Mut(target)];
        match clone {
            LocalClone::Required => {
                panic!("LocalClone::Required should have been resolved before evaluation")
            }
            LocalClone::Static(function) => {
                ctx.call_function_id(*function, arguments, span)?;
            }
            LocalClone::Dictionary(dict_index) => {
                let dictionary = dictionary_from_local_index(ctx, *dict_index, span);
                call_dictionary_method(
                    ctx,
                    dictionary,
                    VALUE_TRAIT.dictionary_method_index(VALUE_CLONE_METHOD_INDEX),
                    arguments,
                    span,
                )?;
            }
        }
        if matches!(&ctx.environment[target_index], ValOrMut::Val(Value::Uninit)) {
            panic!("Value::clone returned without initializing local storage");
        }
    } else if !locals[node.id.as_index()].owns_storage {
        match eval_or_return!(try_resolve_node_place(arena, node.value, ctx, locals)) {
            Some(place) => {
                if let Some(dictionary) = try_dictionary_from_place(&place, ctx) {
                    ctx.environment.push(ValOrMut::Dictionary(dictionary));
                } else if let Some(value) = try_copy_trivial_value_from_place(
                    &place,
                    locals[node.id.as_index()].ty,
                    ctx,
                    span,
                )? {
                    ctx.environment.push(ValOrMut::Val(value));
                } else {
                    ctx.environment.push(ValOrMut::Mut(place));
                }
            }
            None if locals[node.id.as_index()].ty == Type::never() => {
                eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
                panic!("never-typed local initializer returned normally");
            }
            None if matches!(arena[node.value].kind, NodeKind::GetDictionary(_)) => {
                let dictionary = eval_or_return!(eval_dictionary_metadata_node(
                    arena, node.value, ctx, locals
                ));
                ctx.environment.push(ValOrMut::Dictionary(dictionary));
            }
            None if matches!(arena[node.value].kind, NodeKind::GetFunction(_)) => {
                let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
                ctx.environment.push(ValOrMut::Val(value));
            }
            None => {
                if eval_or_return!(is_dictionary_entry_projection(
                    arena, node.value, ctx, locals
                )) {
                    let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
                    ctx.environment.push(ValOrMut::Val(value));
                } else {
                    panic!(
                        "Cannot bind non-owning local '{}' of type {:?} to non-place node: {:?}",
                        locals[node.id.as_index()].name.0,
                        locals[node.id.as_index()].ty,
                        arena[node.value].kind
                    );
                }
            }
        }
        #[cfg(debug_assertions)]
        ctx.environment_names
            .push(locals[node.id.as_index()].name.0);
    } else {
        if matches!(arena[node.value].kind, NodeKind::GetDictionary(_)) {
            let dictionary = eval_or_return!(eval_dictionary_metadata_node(
                arena, node.value, ctx, locals
            ));
            ctx.environment.push(ValOrMut::Dictionary(dictionary));
        } else {
            let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
            ctx.environment.push(ValOrMut::Val(value));
        }
        #[cfg(debug_assertions)]
        ctx.environment_names
            .push(locals[node.id.as_index()].name.0);
    }
    cont(Value::unit())
}

#[inline(never)]
fn eval_env_drop(
    node: &hir::EnvDrop,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let Some(drop) = &locals[node.id.as_index()].drop else {
        return cont(Value::unit());
    };
    let target = Place {
        target: ctx.frame_base + node.index as usize,
        path: Vec::new(),
    };
    let arguments = vec![ValOrMut::Mut(target.clone())];
    match drop {
        LocalDrop::Required => {
            panic!("LocalDrop::Required should have been resolved before evaluation")
        }
        LocalDrop::Static(function) => {
            ctx.call_function_id(*function, arguments, span)?;
        }
        LocalDrop::Dictionary(dict_index) => {
            let dictionary = dictionary_from_local_index(ctx, *dict_index, span);
            call_dictionary_method(
                ctx,
                dictionary,
                VALUE_TRAIT.dictionary_method_index(VALUE_DROP_METHOD_INDEX),
                arguments,
                span,
            )?;
        }
    }
    discard_value_storage_at_place(ctx, &target, span)?;
    cont(Value::unit())
}

#[inline(never)]
fn eval_env_move(node: &hir::EnvMove, _span: Location, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let index = ctx.frame_base + node.index as usize;
    match mem::replace(&mut ctx.environment[index], ValOrMut::Val(Value::uninit())) {
        ValOrMut::Val(value) => cont(value),
        ValOrMut::Dictionary(_) => panic!("cannot move out of a trait dictionary metadata local"),
        ValOrMut::Ref(_) => panic!("cannot move out of shared reference storage"),
        ValOrMut::Mut(_) => panic!("cannot move out of a mutable reference local"),
    }
}

// Temporary boxed-`Value` interpreter bridge for HIR `TrivialCopy`.
//
// This is not the language contract for `TrivialCopy`. Once interpreter storage
// moves to typed/linear value slots, this operation should become a storage-level
// copy driven by the layout of the concrete value, and this hand-written list
// should disappear.
fn trivial_copy_value(value: &Value, ty: Type) -> Option<Value> {
    if ty == Type::unit() {
        value.as_primitive_ty::<()>().map(|_| Value::unit())
    } else if ty == bool_type() {
        value
            .as_primitive_ty::<bool>()
            .map(|value| Value::native(*value))
    } else if ty == int_type() {
        value
            .as_primitive_ty::<isize>()
            .map(|value| Value::native(*value))
    } else if !ty.is_constant() {
        value
            .as_primitive_ty::<()>()
            .map(|_| Value::unit())
            .or_else(|| {
                value
                    .as_primitive_ty::<bool>()
                    .map(|value| Value::native(*value))
            })
            .or_else(|| {
                value
                    .as_primitive_ty::<isize>()
                    .map(|value| Value::native(*value))
            })
    } else {
        None
    }
}

fn copy_trivial_value_from_place(
    place: &Place,
    ty: Type,
    ctx: &EvalCtx,
    span: Location,
) -> Result<Value, RuntimeError> {
    // Temporary companion to `trivial_copy_value` for the boxed-value
    // interpreter. This should collapse into the backend implementation of HIR
    // `TrivialCopy` once values are stored in copyable slots.
    try_copy_trivial_value_from_place(place, ty, ctx, span)?.ok_or_else(|| {
        #[cfg(debug_assertions)]
        panic!(
            "attempted to materialize non-TrivialCopy local value without Value::clone: type {:?}, place {:?}, name {:?}",
            ty,
            place,
            ctx.environment_names.get(place.target)
        );
        #[cfg(not(debug_assertions))]
        panic!(
            "attempted to materialize non-TrivialCopy local value without Value::clone: type {:?}, place {:?}",
            ty, place
        );
    })
}

fn try_copy_trivial_value_from_place(
    place: &Place,
    ty: Type,
    ctx: &EvalCtx,
    span: Location,
) -> Result<Option<Value>, RuntimeError> {
    // Temporary boxed-value interpreter bridge; see `trivial_copy_value`.
    let value = place
        .target_ref(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    Ok(trivial_copy_value(value, ty))
}

#[inline(never)]
fn eval_env_load(
    arena: &NodeArena,
    id: NodeId,
    node: &hir::EnvLoad,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let index = ctx.frame_base + node.index as usize;
    let place = Place {
        target: index,
        path: Vec::new(),
    };
    cont(copy_trivial_value_from_place(
        &place,
        locals[node.id.as_index()].ty,
        ctx,
        arena[id].span,
    )?)
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
                if !matches!(arena[*node].kind, NodeKind::EnvDrop(_)) {
                    last_value = val;
                }
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
    cont(Value::tuple(values))
}

#[inline(never)]
fn eval_project(
    arena: &NodeArena,
    id: NodeId,
    data: NodeId,
    index: usize,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    if let Some(mut place) = eval_or_return!(try_resolve_node_place(arena, data, ctx, locals)) {
        if let Some(dictionary) = try_dictionary_from_place(&place, ctx) {
            return cont(dictionary_entry_value(
                ctx,
                dictionary,
                TraitDictionaryEntryIndex::from_index(index),
            ));
        }
        if !should_evaluate_projection_data_as_value(arena, data, arena[id].ty) {
            place.path.push(index as isize);
            return cont(copy_trivial_value_from_place(
                &place,
                arena[id].ty,
                ctx,
                arena[id].span,
            )?);
        }
    }
    if is_dictionary_metadata_node(arena, data) {
        let dictionary = eval_or_return!(eval_dictionary_metadata_node(arena, data, ctx, locals));
        return cont(dictionary_entry_value(
            ctx,
            dictionary,
            TraitDictionaryEntryIndex::from_index(index),
        ));
    }
    let value = eval_or_return!(eval_node_with_ctx(arena, data, ctx, locals));
    cont(
        value
            .into_projected_value(index)
            .unwrap_or_else(|| panic!("Cannot project from a non-compound value")),
    )
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
    if let Some(mut place) = eval_or_return!(try_resolve_node_place(arena, data, ctx, locals)) {
        let index = ctx.frame_base + index;
        let index = *ctx.environment[index]
            .as_primitive::<isize>(ctx)
            .map_err(|err| RuntimeError::new(err, Some(arena[id].span)))?
            .unwrap();
        if let Some(dictionary) = try_dictionary_from_place(&place, ctx) {
            return cont(dictionary_entry_value(
                ctx,
                dictionary,
                TraitDictionaryEntryIndex::from_index(index as usize),
            ));
        }
        if !should_evaluate_projection_data_as_value(arena, data, arena[id].ty) {
            place.path.push(index);
            return cont(copy_trivial_value_from_place(
                &place,
                arena[id].ty,
                ctx,
                arena[id].span,
            )?);
        }
    }
    if is_dictionary_metadata_node(arena, data) {
        let dictionary = eval_or_return!(eval_dictionary_metadata_node(arena, data, ctx, locals));
        let index = ctx.frame_base + index;
        let index = *ctx.environment[index]
            .as_primitive::<isize>(ctx)
            .map_err(|err| RuntimeError::new(err, Some(arena[id].span)))?
            .unwrap();
        return cont(dictionary_entry_value(
            ctx,
            dictionary,
            TraitDictionaryEntryIndex::from_index(index as usize),
        ));
    }
    let value = eval_or_return!(eval_node_with_ctx(arena, data, ctx, locals));
    let index = ctx.frame_base + index;
    let index = *ctx.environment[index]
        .as_primitive::<isize>(ctx)
        .map_err(|err| RuntimeError::new(err, Some(arena[id].span)))?
        .unwrap();
    cont(
        value
            .into_tuple_element(index as usize)
            .unwrap_or_else(|| panic!("Cannot access field from a non-compound value")),
    )
}

fn should_evaluate_projection_data_as_value(
    arena: &NodeArena,
    data: NodeId,
    result_ty: Type,
) -> bool {
    !is_direct_interpreter_argument(result_ty)
        && place_resolution_depends_on_array_index(arena, data)
}

fn place_resolution_depends_on_array_index(arena: &NodeArena, node_id: NodeId) -> bool {
    match &arena[node_id].kind {
        NodeKind::Index(_) => true,
        NodeKind::Project(base, _)
        | NodeKind::FieldAccess(base, _)
        | NodeKind::ProjectAt(base, _) => place_resolution_depends_on_array_index(arena, *base),
        _ => false,
    }
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
    if let Some(place) = eval_or_return!(try_resolve_node_place(arena, node, ctx, locals)) {
        let value = place
            .target_ref(ctx)
            .map_err(|err| RuntimeError::new(err, Some(arena[node].span)))?;
        let variant = value.as_variant().unwrap();
        return cont(Value::native(variant.tag_as_isize()));
    }
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
    index: &hir::ArrayIndex,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    // Evaluate left-to-right: array first, then index (matches Rust semantics).
    let mut array_place = eval_or_return!(try_resolve_node_place(arena, index.array, ctx, locals));
    let mut temp_array_index = None;
    if array_place.is_none() {
        let array = eval_or_return!(eval_node_with_ctx(arena, index.array, ctx, locals));
        let target = ctx.environment.len();
        ctx.environment.push(ValOrMut::Val(array));
        #[cfg(debug_assertions)]
        ctx.environment_names.push(ustr("$array_index_source"));
        temp_array_index = Some(target);
        array_place = Some(Place {
            target,
            path: Vec::new(),
        });
    }
    let mut element_place = array_place.unwrap();
    let index_value = eval_or_return!(eval_node_with_ctx(arena, index.index, ctx, locals))
        .into_primitive_ty::<isize>()
        .unwrap();
    element_place.path.push(index_value);

    let clone = index
        .clone
        .as_ref()
        .expect("ArrayIndex clone dispatch should have been resolved before evaluation");
    let result = call_value_clone_dispatch_for_temp(
        ctx,
        clone,
        ValOrMut::Mut(element_place.clone()),
        arena[id].span,
    );

    if temp_array_index.is_some() {
        #[cfg(debug_assertions)]
        ctx.environment_names.pop();
        ctx.environment.pop();
    }

    result.map(ControlFlow::Continue)
}

#[inline(never)]
fn eval_case(
    arena: &NodeArena,
    case: &hir::Case,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let value = if let Some(place) =
        eval_or_return!(try_resolve_node_place(arena, case.value, ctx, locals))
    {
        place
            .target_ref(ctx)
            .map_err(|err| RuntimeError::new(err, Some(arena[case.value].span)))?
            .to_literal_value()
    } else {
        eval_or_return!(eval_node_with_ctx(arena, case.value, ctx, locals)).to_literal_value()
    };
    let value = value.unwrap_or_else(|| {
        panic!(
            "Case evaluated a non-literal scrutinee. This HIR should have been rejected before evaluation."
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
        None => panic!("Cannot resolve a non-place node: {:?}", arena[id].kind),
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
    arg_passing: Option<&[ArgPassing]>,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Vec<ValOrMut>>, RuntimeError> {
    // Automatically cast mutable references to values if the function expects values.
    let mut results = Vec::with_capacity(args.len());
    assert_eq!(args.len(), args_ty.len());
    for (index, (arg, ty)) in args.iter().zip(args_ty).enumerate() {
        let passing = arg_passing
            .and_then(|passing| passing.get(index).copied())
            .unwrap_or_else(|| default_argument_passing(ty));
        results.push(match passing {
            ArgPassing::MutableRef => ValOrMut::Mut(eval_or_return!(resolve_node_place(
                arena, *arg, ctx, locals
            ))),
            ArgPassing::SharedRef => {
                match eval_or_return!(try_resolve_node_place(arena, *arg, ctx, locals)) {
                    Some(place) => ValOrMut::Mut(place),
                    None if is_dictionary_metadata_node(arena, *arg) => ValOrMut::Dictionary(
                        eval_or_return!(eval_dictionary_metadata_node(arena, *arg, ctx, locals)),
                    ),
                    None => ValOrMut::Val(eval_or_return!(eval_node_with_ctx(
                        arena, *arg, ctx, locals
                    ))),
                }
            }
            ArgPassing::OwnedValue if is_dictionary_metadata_node(arena, *arg) => {
                ValOrMut::Dictionary(eval_or_return!(eval_dictionary_metadata_node(
                    arena, *arg, ctx, locals
                )))
            }
            ArgPassing::OwnedValue => ValOrMut::Val(eval_or_return!(eval_node_with_ctx(
                arena, *arg, ctx, locals
            ))),
        });
    }
    Ok(ControlFlow::Continue(results))
}

fn is_dictionary_metadata_node(arena: &NodeArena, node: NodeId) -> bool {
    matches!(arena[node].kind, NodeKind::GetDictionary(_))
}

fn is_dictionary_entry_projection(
    arena: &NodeArena,
    node: NodeId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<bool>, RuntimeError> {
    let data = match &arena[node].kind {
        NodeKind::Project(data, _) | NodeKind::ProjectAt(data, _) => *data,
        _ => return Ok(ControlFlow::Continue(false)),
    };
    if is_dictionary_metadata_node(arena, data) {
        return Ok(ControlFlow::Continue(true));
    }
    let Some(place) = eval_or_return!(try_resolve_node_place(arena, data, ctx, locals)) else {
        return Ok(ControlFlow::Continue(false));
    };
    Ok(ControlFlow::Continue(
        try_dictionary_from_place(&place, ctx).is_some(),
    ))
}

fn default_argument_passing(arg: &FnArgType) -> ArgPassing {
    if arg
        .mut_ty
        .as_resolved()
        .expect("Unresolved mutability variable found during execution")
        .is_mutable()
    {
        ArgPassing::MutableRef
    } else if is_direct_interpreter_argument(arg.ty) {
        ArgPassing::OwnedValue
    } else {
        ArgPassing::SharedRef
    }
}

fn is_direct_interpreter_argument(ty: Type) -> bool {
    ty == Type::unit() || ty == bool_type() || ty == int_type()
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
            if try_dictionary_from_place(&place, ctx).is_some() {
                return Ok(ControlFlow::Continue(None));
            }
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
            let index = *ctx.environment[index]
                .as_primitive::<isize>(ctx)
                .map_err(|err| RuntimeError::new(err, Some(arena[id].span)))?
                .unwrap();
            if try_dictionary_from_place(&place, ctx).is_some() {
                return Ok(ControlFlow::Continue(None));
            }
            place.path.push(index);
            place
        }
        Index(index) => {
            let Some(mut place) =
                eval_or_return!(try_resolve_node_place(arena, index.array, ctx, locals))
            else {
                return Ok(ControlFlow::Continue(None));
            };
            let index_value = eval_or_return!(eval_node_with_ctx(arena, index.index, ctx, locals));
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
