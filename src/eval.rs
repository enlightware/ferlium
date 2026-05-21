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
use ustr::{Ustr, ustr};

use crate::module::id::Id;
use crate::std::array::array_value_from_vec;
use crate::std::value::{VALUE_CLONE_METHOD_INDEX, VALUE_DROP_METHOD_INDEX, VALUE_TRAIT};
use crate::{
    CompilerSession, Location, SourceId, SourceTable,
    compiler::error::RuntimeErrorKind,
    format::{FormatWith, write_with_separator},
    hir::function::{ArgPassing, TrivialCopy},
    hir::value::{FunctionHiddenArgValue, FunctionValue, NativeValue, Value},
    module::{
        ExtraParameterId, FunctionId, LocalClone, LocalDebugVisibility, LocalDecl, LocalDeclId,
        LocalDrop, LocalFunctionId, LocalValueMethodDispatch, ModuleFunction, ModuleId,
        ProjectionIndex, TraitDictionary, TraitDictionaryEntry, TraitDictionaryId, TraitImplId,
    },
    std::buffer,
    types::{
        r#trait::{TraitDictionaryEntryIndex, TraitMethodIndex},
        r#type::{FnArgType, Type, TypeKind, bare_native_type},
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

    pub(crate) fn discard_storage(self) {
        if let ValOrMut::Val(value) = self {
            value.discard_storage();
        }
    }
}

/// Draining iterator that discards unconsumed owned argument storage on drop.
pub(crate) struct ValOrMutArgs {
    args: std::vec::IntoIter<ValOrMut>,
}

impl ValOrMutArgs {
    pub(crate) fn new(args: Vec<ValOrMut>) -> Self {
        Self {
            args: args.into_iter(),
        }
    }

    pub(crate) fn next(&mut self) -> Option<ValOrMut> {
        self.args.next()
    }
}

impl Drop for ValOrMutArgs {
    fn drop(&mut self) {
        for arg in self.args.by_ref() {
            arg.discard_storage();
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
    /// whether the current function returns a place result
    returns_place: bool,
    /// session holding sources and other modules for error reporting and import resolution
    compiler_session: &'a CompilerSession,
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
            returns_place: false,
            compiler_session,
        }
    }

    /// Get the compiler session.
    pub fn compiler_session(&self) -> &'a CompilerSession {
        self.compiler_session
    }

    pub fn pop_environment_entry(&mut self) -> Option<ValOrMut> {
        self.environment.pop()
    }

    pub fn pop_environment_entry_discard(&mut self) {
        if let Some(entry) = self.pop_environment_entry() {
            entry.discard_storage();
        }
    }

    pub fn truncate_environment_storage(&mut self, len: usize) {
        while self.environment.len() > len {
            self.pop_environment_entry_discard();
        }
    }

    fn ensure_environment_slot(&mut self, index: usize) {
        while self.environment.len() <= index {
            self.environment.push(ValOrMut::Val(Value::uninit()));
        }
    }

    fn set_environment_entry(&mut self, index: usize, value: ValOrMut) {
        self.ensure_environment_slot(index);
        let old = mem::replace(&mut self.environment[index], value);
        old.discard_storage();
    }

    pub fn with_environment(
        module: ModuleId,
        environment: Vec<ValOrMut>,
        compiler_session: &'a CompilerSession,
    ) -> EvalCtx<'a> {
        EvalCtx {
            environment,
            frame_base: 0,
            call_depth: 0,
            call_depth_limit: Self::DEFAULT_CALL_DEPTH_LIMIT,
            stack_limit: Self::DEFAULT_STACK_LIMIT,
            break_loop: false,
            module_id: module,
            returns_place: false,
            compiler_session,
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

    fn function_value_visible_argument_types(
        &self,
        function_value: &FunctionValue,
    ) -> Vec<FnArgType> {
        // Dynamic calls must use the actual callee signature. A generic
        // dictionary projection can have surface type `(A, A) -> R` while its
        // runtime `FunctionValue` points at a concrete method such as
        // `Ord<int>::cmp`.
        self.get_module_function(function_value.function_id, function_value.module_id)
            .definition
            .ty_scheme
            .ty
            .args
            .clone()
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
            self.pop_environment_entry_discard();
            let result = match (result, drop_result) {
                (Ok(result), Ok(_)) => Ok(result),
                (Ok(result), Err(err)) => {
                    result.into_value().discard_storage();
                    Err(err)
                }
                (Err(err), _) => Err(err),
            };
            return result;
        }

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

        self.call_function(local_id, module_id, arguments)
            .map_err(|err| {
                err.with_frame(
                    module_id,
                    FunctionId::Local(local_id),
                    self.environment.len(),
                    location,
                )
            })
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
        let previous_returns_place = mem::replace(
            &mut self.returns_place,
            function_data.definition.returns_place,
        );
        let result = function_data.code.call(arguments, self, locals);
        self.returns_place = previous_returns_place;

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

/// Internal runtime marker returned by functions marked `#[place_result]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlaceResult(Place);

impl PlaceResult {
    pub(crate) fn new(place: Place) -> Self {
        Self(place)
    }

    fn into_place(self) -> Place {
        self.0
    }
}

impl crate::hir::value::NativeDisplay for PlaceResult {
    fn fmt_repr(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<place>")
    }
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

    fn resolved(&self, ctx: &EvalCtx) -> Self {
        let (path, target) = self.resolved_path_and_index(ctx);
        Self {
            target,
            path: path.into_iter().collect(),
        }
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
                    let buffer = primitive
                        .as_mut()
                        .as_mut_any()
                        .downcast_mut::<buffer::Buffer>()
                        .unwrap();
                    match buffer.get_mut_signed(index) {
                        Some(target) => target,
                        None => {
                            return Err(RuntimeErrorKind::InvalidArgument(ustr("buffer index")));
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

    fn target_ref_allow_uninit<'c>(&self, ctx: &'c EvalCtx) -> Result<&'c Value, RuntimeErrorKind> {
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
                    let buffer = NativeValue::as_any(primitive.as_ref())
                        .downcast_ref::<buffer::Buffer>()
                        .unwrap();
                    match buffer.get_signed(index) {
                        Some(target) => target,
                        None => {
                            return Err(RuntimeErrorKind::InvalidArgument(ustr("buffer index")));
                        }
                    }
                }
                Uninit => panic!("cannot read a field of an uninitialized value"),
                Variant(_) => panic!("Cannot access a variant payload with a non-zero index"),
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }

    /// Get a shared reference to the target value
    pub fn target_ref<'c>(&self, ctx: &'c EvalCtx) -> Result<&'c Value, RuntimeErrorKind> {
        let target = self.target_ref_allow_uninit(ctx)?;
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
impl<V> ControlFlow<V> {
    fn map_continue<U>(self, f: impl FnOnce(V) -> U) -> ControlFlow<U> {
        match self {
            ControlFlow::Continue(value) => ControlFlow::Continue(f(value)),
            ControlFlow::Return(value) => ControlFlow::Return(value),
        }
    }
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
    call_site: Location,
}
impl BacktraceFrame {
    fn fmt_with_suspended_at(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, &Modules),
        suspended_at: Option<Location>,
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
        write!(f, " at {}", self.call_site.format_with(source_table))?;
        if let (FunctionId::Local(id), Some(suspended_at)) = (self.function_id, suspended_at)
            && let Some(function) = module.get_function_by_id(id)
        {
            let locals = function
                .debug_info
                .locals_at_source(suspended_at, LocalDebugVisibility::User);
            if !locals.is_empty() {
                write!(f, "\n     locals: ")?;
                write_with_separator(locals.iter().map(|local| local.name), ", ", f)?;
            }
        }
        Ok(())
    }
}
impl FormatWith<(&SourceTable, &Modules)> for BacktraceFrame {
    fn fmt_with(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        data: &(&SourceTable, &Modules),
    ) -> std::fmt::Result {
        self.fmt_with_suspended_at(f, data, None)
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
            call_site: location,
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
            if frame.call_site.source_id == source_id {
                return Some(frame.call_site);
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
            let mut suspended_at = self.location;
            for (i, frame) in self.backtrace.iter().enumerate() {
                write!(f, "  {i}: ")?;
                frame.fmt_with_suspended_at(f, data, suspended_at)?;
                writeln!(f)?;
                suspended_at = Some(frame.call_site);
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
        EnvMove(node) => eval_env_move(node, arena[id].span, ctx, locals),
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

fn dictionary_from_extra_parameter(
    ctx: &EvalCtx,
    extra_parameter: ExtraParameterId,
    _span: Location,
) -> TraitDictionaryId {
    let local_index = extra_parameter.as_index();
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

fn discard_call_result(result: EvalControlFlowResult) -> Result<(), RuntimeError> {
    result?.into_value().discard_storage();
    Ok(())
}

/// Invoke a resolved `Value` method (clone or drop) for a local-dispatch site.
fn call_local_value_method(
    ctx: &mut EvalCtx,
    dispatch: &LocalValueMethodDispatch,
    method_index: TraitMethodIndex,
    arguments: Vec<ValOrMut>,
    span: Location,
) -> EvalControlFlowResult {
    match dispatch {
        LocalValueMethodDispatch::Required => {
            panic!("LocalValueMethodDispatch::Required should have been resolved before evaluation")
        }
        LocalValueMethodDispatch::Static(function) => {
            ctx.call_function_id(*function, arguments, span)
        }
        LocalValueMethodDispatch::Dictionary(dict_index) => {
            let dictionary = dictionary_from_extra_parameter(ctx, *dict_index, span);
            call_dictionary_method(
                ctx,
                dictionary,
                VALUE_TRAIT.dictionary_method_index(method_index),
                arguments,
                span,
            )
        }
    }
}

fn call_local_drop_dispatch(
    ctx: &mut EvalCtx,
    drop: &LocalDrop,
    target: Place,
    span: Location,
) -> Result<(), RuntimeError> {
    discard_call_result(call_local_value_method(
        ctx,
        drop,
        VALUE_DROP_METHOD_INDEX,
        vec![ValOrMut::Mut(target)],
        span,
    ))
}

pub(crate) fn drop_frame_owned_locals_on_error(
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
    span: Location,
) -> Result<(), RuntimeError> {
    drop_owned_locals_on_error_from(ctx, locals, ctx.frame_base, span)
}

fn drop_owned_locals_on_error_from(
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
    start_environment_index: usize,
    span: Location,
) -> Result<(), RuntimeError> {
    for (index, local) in locals.iter().enumerate().rev() {
        if !local.owns_storage {
            continue;
        }
        let Some(drop) = &local.drop else {
            continue;
        };
        let id = LocalDeclId::from_index(index);
        let target_index = local_environment_index(ctx, locals, id);
        if target_index < start_environment_index {
            continue;
        }
        if target_index >= ctx.environment.len() {
            continue;
        }
        let target = Place {
            target: target_index,
            path: Vec::new(),
        };
        if place_contains_uninit(ctx, &target, span)? {
            continue;
        }
        call_local_drop_dispatch(ctx, drop, target.clone(), span)?;
        discard_value_storage_at_place(ctx, &target, span)?;
    }
    Ok(())
}

fn call_value_clone_with(
    ctx: &mut EvalCtx,
    source: ValOrMut,
    _span: Location,
    call: impl FnOnce(&mut EvalCtx, Vec<ValOrMut>) -> EvalControlFlowResult,
) -> Result<Value, RuntimeError> {
    let target_index = ctx.environment.len();
    ctx.environment.push(ValOrMut::Val(Value::uninit()));
    let target = Place {
        target: target_index,
        path: Vec::new(),
    };
    let result = call(ctx, vec![source, ValOrMut::Mut(target)]);
    let target = ctx.pop_environment_entry().unwrap().into_val().unwrap();
    if let Err(err) = discard_call_result(result) {
        target.discard_storage();
        return Err(err);
    }
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
    discard_call_result(call_dictionary_method(
        ctx,
        dictionary,
        VALUE_TRAIT.dictionary_method_index(VALUE_CLONE_METHOD_INDEX),
        vec![source, ValOrMut::Mut(target.clone())],
        span,
    ))?;
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
    call_value_clone_with(ctx, source, span, |ctx, arguments| {
        call_local_value_method(ctx, clone, VALUE_CLONE_METHOD_INDEX, arguments, span)
    })
}

pub(crate) fn call_value_drop_for_temp(
    ctx: &mut EvalCtx,
    dictionary: TraitDictionaryId,
    target: ValOrMut,
    span: Location,
) -> EvalControlFlowResult {
    let (target_place, temp_index) = match target {
        ValOrMut::Mut(place) => (place, None),
        ValOrMut::Ref(_) => panic!("cannot drop shared reference storage"),
        ValOrMut::Dictionary(_) => panic!("cannot drop trait dictionary metadata as a Value"),
        ValOrMut::Val(value) => {
            let target_index = ctx.environment.len();
            ctx.environment.push(ValOrMut::Val(value));
            let place = Place {
                target: target_index,
                path: Vec::new(),
            };
            (place, Some(target_index))
        }
    };
    let result = discard_call_result(call_dictionary_method(
        ctx,
        dictionary,
        VALUE_TRAIT.dictionary_method_index(VALUE_DROP_METHOD_INDEX),
        vec![ValOrMut::Mut(target_place.clone())],
        span,
    ));
    if result.is_ok() {
        discard_value_storage_at_place(ctx, &target_place, span)?;
    }
    if let Some(target_index) = temp_index {
        let value = ctx.pop_environment_entry().unwrap();
        debug_assert_eq!(target_index, ctx.environment.len());
        if result.is_ok() {
            debug_assert!(matches!(value, ValOrMut::Val(Value::Uninit)));
        } else {
            value.discard_storage();
        }
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

fn replace_value_storage_at_place(
    ctx: &mut EvalCtx,
    place: &Place,
    value: Value,
    span: Location,
) -> Result<(), RuntimeError> {
    let target = match place.target_mut(ctx) {
        Ok(target) => target,
        Err(err) => {
            value.discard_storage();
            return Err(RuntimeError::new(err, Some(span)));
        }
    };
    let old_value = mem::replace(target, value);
    old_value.discard_storage();
    Ok(())
}

fn place_contains_uninit(
    ctx: &EvalCtx,
    place: &Place,
    span: Location,
) -> Result<bool, RuntimeError> {
    let target = place
        .target_ref_allow_uninit(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    Ok(matches!(target, Value::Uninit))
}

fn local_environment_index(ctx: &EvalCtx, locals: &[LocalDecl], id: LocalDeclId) -> usize {
    ctx.frame_base + locals[id.as_index()].slot.as_index()
}

fn extra_parameter_environment_index(ctx: &EvalCtx, id: ExtraParameterId) -> usize {
    ctx.frame_base + id.as_index()
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
    let captured_env = {
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
    };
    let Some((dictionary, captures)) = captured_env else {
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
    let temp_start = ctx.environment.len();
    let source = match eval_or_return!(try_resolve_node_place(arena, node.source, ctx, locals)) {
        Some(place) => {
            place
                .target_ref(ctx)
                .map_err(|err| RuntimeError::new(err, Some(arena[node.source].span)))?;
            ValOrMut::Mut(place)
        }
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
    match call_value_clone_dispatch_for_temp(ctx, clone, source, span) {
        Ok(value) => cont(value),
        Err(err) => {
            ctx.truncate_environment_storage(temp_start);
            Err(err)
        }
    }
}

#[inline(never)]
fn eval_trivial_copy(
    arena: &NodeArena,
    node: &hir::TrivialCopy,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let temp_start = ctx.environment.len();
    let place = eval_or_return!(resolve_node_place(arena, node.source, ctx, locals));
    let result = copy_trivial_value_from_place(&place, arena[node.source].ty, ctx, span);
    ctx.truncate_environment_storage(temp_start);
    cont(result?)
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
    let args_ty = ctx.function_value_visible_argument_types(function_value);
    let temp_start = ctx.environment.len();
    let arguments = eval_or_return!(eval_args(
        arena,
        &app.arguments,
        &args_ty,
        arg_passing,
        ctx,
        locals
    ));
    let result = ctx.call_function_value(function_value, arguments, span);
    ctx.truncate_environment_storage(temp_start);
    result
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
    let temp_start = ctx.environment.len();
    let arguments = eval_or_return!(eval_args(
        arena,
        &app.arguments,
        &app.ty.args,
        arg_passing,
        ctx,
        locals
    ));
    let result = ctx.call_function_id(app.function, arguments, span);
    ctx.truncate_environment_storage(temp_start);
    result
}

fn eval_place_result_static_apply(
    arena: &NodeArena,
    app: &hir::StaticApplication,
    span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let arg_passing = ctx.function_id_argument_passing(app.function);
    let temp_start = ctx.environment.len();
    let arguments = eval_or_return!(eval_place_result_args(
        arena,
        &app.arguments,
        &app.ty.args,
        arg_passing,
        ctx,
        locals,
    ));
    match ctx.call_function_id(app.function, arguments, span) {
        Ok(result) => Ok(result),
        Err(err) => {
            ctx.truncate_environment_storage(temp_start);
            Err(err)
        }
    }
}

enum PendingPlaceResultArg {
    Ready(ValOrMut),
    SharedTemp(Value),
}

impl PendingPlaceResultArg {
    fn discard_storage(self) {
        match self {
            Self::Ready(arg) => arg.discard_storage(),
            Self::SharedTemp(value) => value.discard_storage(),
        }
    }
}

fn eval_place_result_args(
    arena: &NodeArena,
    args: &[NodeId],
    args_ty: &[FnArgType],
    arg_passing: Option<&[ArgPassing]>,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<Vec<ValOrMut>>, RuntimeError> {
    let mut results = Vec::with_capacity(args.len());
    assert_eq!(args.len(), args_ty.len());
    for (arg, ty) in args.iter().zip(args_ty) {
        let passing = arg_passing
            .and_then(|passing| passing.get(results.len()).copied())
            .unwrap_or_else(|| default_argument_passing(ty));
        let result = match passing {
            ArgPassing::MutableRef => resolve_node_place(arena, *arg, ctx, locals).map(|result| {
                result.map_continue(|place| PendingPlaceResultArg::Ready(ValOrMut::Mut(place)))
            }),
            ArgPassing::SharedRef => match try_resolve_node_place(arena, *arg, ctx, locals) {
                Ok(ControlFlow::Continue(Some(place))) => Ok(ControlFlow::Continue(
                    PendingPlaceResultArg::Ready(ValOrMut::Mut(place)),
                )),
                Ok(ControlFlow::Continue(None)) if is_dictionary_metadata_node(arena, *arg) => {
                    eval_dictionary_metadata_node(arena, *arg, ctx, locals).map(|result| {
                        result.map_continue(|dictionary| {
                            PendingPlaceResultArg::Ready(ValOrMut::Dictionary(dictionary))
                        })
                    })
                }
                Ok(ControlFlow::Continue(None)) => {
                    let value = eval_node_with_ctx(arena, *arg, ctx, locals)?;
                    Ok(value.map_continue(PendingPlaceResultArg::SharedTemp))
                }
                Ok(ControlFlow::Return(value)) => Ok(ControlFlow::Return(value)),
                Err(err) => Err(err),
            },
            ArgPassing::OwnedValue if is_dictionary_metadata_node(arena, *arg) => {
                eval_dictionary_metadata_node(arena, *arg, ctx, locals).map(|result| {
                    result.map_continue(|dictionary| {
                        PendingPlaceResultArg::Ready(ValOrMut::Dictionary(dictionary))
                    })
                })
            }
            ArgPassing::OwnedValue => eval_owned_arg(arena, *arg, ty.ty, ctx, locals)
                .map(|result| result.map_continue(PendingPlaceResultArg::Ready)),
        };
        match result {
            Ok(ControlFlow::Continue(arg)) => results.push(arg),
            Ok(ControlFlow::Return(value)) => {
                for result in results {
                    result.discard_storage();
                }
                return Ok(ControlFlow::Return(value));
            }
            Err(err) => {
                for result in results {
                    result.discard_storage();
                }
                return Err(err);
            }
        }
    }
    let mut arguments = Vec::with_capacity(results.len());
    for result in results {
        match result {
            PendingPlaceResultArg::Ready(arg) => arguments.push(arg),
            PendingPlaceResultArg::SharedTemp(value) => {
                let target = ctx.environment.len();
                ctx.environment.push(ValOrMut::Val(value));
                arguments.push(ValOrMut::Mut(Place {
                    target,
                    path: Vec::new(),
                }));
            }
        }
    }
    Ok(ControlFlow::Continue(arguments))
}

fn value_into_place_result(value: Value) -> Place {
    value
        .into_primitive_ty::<PlaceResult>()
        .expect("place_result function should return internal PlaceResult")
        .into_place()
}

fn control_flow_into_place_result(result: ControlFlow<Value>) -> ControlFlow<Place> {
    match result {
        ControlFlow::Continue(value) => ControlFlow::Continue(value_into_place_result(value)),
        ControlFlow::Return(value) => ControlFlow::Return(value),
    }
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
    let target_index = local_environment_index(ctx, locals, node.id);
    if target_index >= ctx.stack_limit {
        return Err(RuntimeError::new(
            RuntimeErrorKind::StackLimitExceeded {
                limit: ctx.stack_limit,
            },
            Some(span),
        ));
    }
    if let Some(clone) = &locals[node.id.as_index()].clone {
        ctx.ensure_environment_slot(target_index);
        let target = Place {
            target: target_index,
            path: Vec::new(),
        };
        let source = match eval_or_return!(try_resolve_node_place(arena, node.value, ctx, locals)) {
            Some(place) => {
                place
                    .target_ref(ctx)
                    .map_err(|err| RuntimeError::new(err, Some(arena[node.value].span)))?;
                ValOrMut::Mut(place)
            }
            None => ValOrMut::Val(eval_or_return!(eval_node_with_ctx(
                arena, node.value, ctx, locals
            ))),
        };
        let arguments = vec![source, ValOrMut::Mut(target)];
        let result = call_local_value_method(ctx, clone, VALUE_CLONE_METHOD_INDEX, arguments, span);
        discard_call_result(result)?;
        if matches!(&ctx.environment[target_index], ValOrMut::Val(Value::Uninit)) {
            panic!("Value::clone returned without initializing local storage");
        }
    } else if !locals[node.id.as_index()].owns_storage {
        let entry = match eval_or_return!(try_resolve_node_place(arena, node.value, ctx, locals)) {
            Some(place) => {
                if let Some(dictionary) = try_dictionary_from_place(&place, ctx) {
                    ValOrMut::Dictionary(dictionary)
                } else if let Some(value) = try_copy_trivial_value_from_place(
                    &place,
                    locals[node.id.as_index()].ty,
                    ctx,
                    span,
                )? {
                    ValOrMut::Val(value)
                } else {
                    ValOrMut::Mut(place)
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
                ValOrMut::Dictionary(dictionary)
            }
            None if matches!(arena[node.value].kind, NodeKind::GetFunction(_)) => {
                let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
                ValOrMut::Val(value)
            }
            None => {
                if eval_or_return!(is_dictionary_entry_projection(
                    arena, node.value, ctx, locals
                )) {
                    let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
                    ValOrMut::Val(value)
                } else {
                    panic!(
                        "Cannot bind non-owning local '{}' of type {:?} to non-place node: {:?}",
                        locals[node.id.as_index()].name.0,
                        locals[node.id.as_index()].ty,
                        arena[node.value].kind
                    );
                }
            }
        };
        ctx.set_environment_entry(target_index, entry);
    } else {
        let entry = if matches!(arena[node.value].kind, NodeKind::GetDictionary(_)) {
            let dictionary = eval_or_return!(eval_dictionary_metadata_node(
                arena, node.value, ctx, locals
            ));
            ValOrMut::Dictionary(dictionary)
        } else {
            let value = eval_or_return!(eval_node_with_ctx(arena, node.value, ctx, locals));
            ValOrMut::Val(value)
        };
        ctx.set_environment_entry(target_index, entry);
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
        target: local_environment_index(ctx, locals, node.id),
        path: Vec::new(),
    };
    call_local_drop_dispatch(ctx, drop, target.clone(), span)?;
    discard_value_storage_at_place(ctx, &target, span)?;
    cont(Value::unit())
}

#[inline(never)]
fn eval_env_move(
    node: &hir::EnvMove,
    _span: Location,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let index = local_environment_index(ctx, locals, node.id);
    match mem::replace(&mut ctx.environment[index], ValOrMut::Val(Value::uninit())) {
        ValOrMut::Val(value) => cont(value),
        ValOrMut::Dictionary(_) => panic!("cannot move out of a trait dictionary metadata local"),
        ValOrMut::Ref(_) => panic!("cannot move out of shared reference storage"),
        ValOrMut::Mut(_) => panic!("cannot move out of a mutable reference local"),
    }
}

fn copy_trivial_native_value_typed<T: TrivialCopy + NativeValue>(value: &Value) -> Option<Value> {
    value
        .as_primitive_ty::<T>()
        .map(|value| Value::native(*value))
}

/// Temporary boxed-interpreter copy for native values known to implement `TrivialCopy`.
///
/// This is not the language contract for `TrivialCopy`: future typed/linear
/// storage should lower HIR `TrivialCopy` to a layout-driven memcpy instead.
fn copy_trivial_native_value(value: &Value, ty: Type) -> Option<Value> {
    let ty_data = ty.data();
    if let TypeKind::Native(native) = &*ty_data
        && native.arguments.is_empty()
    {
        if native.bare_ty == bare_native_type::<()>() {
            return copy_trivial_native_value_typed::<()>(value);
        }
        if native.bare_ty == bare_native_type::<bool>() {
            return copy_trivial_native_value_typed::<bool>(value);
        }
        if native.bare_ty == bare_native_type::<isize>() {
            return copy_trivial_native_value_typed::<isize>(value);
        }
    }
    None
}

fn copy_trivial_value_from_place(
    place: &Place,
    ty: Type,
    ctx: &EvalCtx,
    span: Location,
) -> Result<Value, RuntimeError> {
    // Temporary companion to `copy_trivial_native_value` for the boxed-value
    // interpreter. This should collapse into the backend implementation of HIR
    // `TrivialCopy` once values are stored in copyable slots.
    try_copy_trivial_value_from_place(place, ty, ctx, span)?.ok_or_else(|| {
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
    // Temporary boxed-value interpreter bridge; see `copy_trivial_native_value`.
    let value = place
        .target_ref(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    Ok(copy_trivial_native_value(value, ty))
}

#[inline(never)]
fn eval_env_load(
    arena: &NodeArena,
    id: NodeId,
    node: &hir::EnvLoad,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let index = local_environment_index(ctx, locals, node.id);
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
    if ctx.returns_place {
        let place = match resolve_node_place(arena, node, ctx, locals)? {
            ControlFlow::Continue(place) => place,
            ControlFlow::Return(value) => return Ok(ControlFlow::Return(value)),
        };
        let place = place.resolved(ctx);
        return ret(Value::native(PlaceResult::new(place)));
    }
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
    let mut last_value: Option<Value> = None;
    for node in nodes.iter() {
        match eval_node_with_ctx(arena, *node, ctx, locals) {
            Err(err) => {
                if let Some(value) = last_value.take() {
                    value.discard_storage();
                }
                let cleanup =
                    drop_owned_locals_on_error_from(ctx, locals, env_size, arena[*node].span);
                ctx.truncate_environment_storage(env_size);
                cleanup?;
                return Err(err);
            }
            Ok(ControlFlow::Return(val)) => {
                // Early return: clean up environment and propagate.
                if let Some(value) = last_value.take() {
                    value.discard_storage();
                }
                ctx.truncate_environment_storage(env_size);
                return Ok(ControlFlow::Return(val));
            }
            Ok(ControlFlow::Continue(val)) => {
                if !matches!(arena[*node].kind, NodeKind::EnvDrop(_)) {
                    if let Some(old_value) = last_value.replace(val) {
                        old_value.discard_storage();
                    }
                } else {
                    val.discard_storage();
                }
            }
        }
    }
    // Normal block completion.
    ctx.truncate_environment_storage(env_size);
    cont(last_value.unwrap_or_else(Value::unit))
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
    let span = arena[id].span;
    if let Some(drop) = &assignment.drop
        && !place_contains_uninit(ctx, &place, span)?
        && let Err(err) = call_local_drop_dispatch(ctx, drop, place.clone(), span)
    {
        value.discard_storage();
        return Err(err);
    }
    replace_value_storage_at_place(ctx, &place, value, span)?;
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
    index: ProjectionIndex,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    let index = index.as_index();
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
    index: ExtraParameterId,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> EvalControlFlowResult {
    if let Some(mut place) = eval_or_return!(try_resolve_node_place(arena, data, ctx, locals)) {
        let index = extra_parameter_environment_index(ctx, index);
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
        let index = extra_parameter_environment_index(ctx, index);
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
    let index = extra_parameter_environment_index(ctx, index);
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
        && place_resolution_depends_on_place_result(arena, data)
}

fn place_resolution_depends_on_place_result(arena: &NodeArena, node_id: NodeId) -> bool {
    match &arena[node_id].kind {
        NodeKind::Apply(app) => app.returns_place,
        NodeKind::StaticApply(app) => app.returns_place,
        NodeKind::Project(base, _)
        | NodeKind::FieldAccess(base, _)
        | NodeKind::ProjectAt(base, _) => place_resolution_depends_on_place_result(arena, *base),
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
        let tag = variant.tag_as_isize();
        return cont(Value::native(tag));
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
    cont(array_value_from_vec(values))
}

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
        match eval_node_with_ctx(arena, node, ctx, locals) {
            Ok(ControlFlow::Continue(value)) => results.push(value),
            Ok(ControlFlow::Return(value)) => {
                for result in results {
                    result.discard_storage();
                }
                return Ok(ControlFlow::Return(value));
            }
            Err(err) => {
                for result in results {
                    result.discard_storage();
                }
                return Err(err);
            }
        }
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
    let temp_start = ctx.environment.len();
    let mut results = Vec::with_capacity(args.len());
    assert_eq!(args.len(), args_ty.len());
    for (index, (arg, ty)) in args.iter().zip(args_ty).enumerate() {
        let passing = arg_passing
            .and_then(|passing| passing.get(index).copied())
            .unwrap_or_else(|| default_argument_passing(ty));
        let result = match passing {
            ArgPassing::MutableRef => resolve_node_place(arena, *arg, ctx, locals)
                .map(|result| result.map_continue(ValOrMut::Mut)),
            ArgPassing::SharedRef => match try_resolve_node_place(arena, *arg, ctx, locals) {
                Ok(ControlFlow::Continue(Some(place))) => {
                    Ok(ControlFlow::Continue(ValOrMut::Mut(place)))
                }
                Ok(ControlFlow::Continue(None)) if is_dictionary_metadata_node(arena, *arg) => {
                    eval_dictionary_metadata_node(arena, *arg, ctx, locals)
                        .map(|result| result.map_continue(ValOrMut::Dictionary))
                }
                Ok(ControlFlow::Continue(None)) => eval_node_with_ctx(arena, *arg, ctx, locals)
                    .map(|result| result.map_continue(ValOrMut::Val)),
                Ok(ControlFlow::Return(value)) => Ok(ControlFlow::Return(value)),
                Err(err) => Err(err),
            },
            ArgPassing::OwnedValue if is_dictionary_metadata_node(arena, *arg) => {
                eval_dictionary_metadata_node(arena, *arg, ctx, locals)
                    .map(|result| result.map_continue(ValOrMut::Dictionary))
            }
            ArgPassing::OwnedValue => eval_owned_arg(arena, *arg, ty.ty, ctx, locals),
        };
        match result {
            Ok(ControlFlow::Continue(arg)) => results.push(arg),
            Ok(ControlFlow::Return(value)) => {
                for result in results {
                    result.discard_storage();
                }
                ctx.truncate_environment_storage(temp_start);
                return Ok(ControlFlow::Return(value));
            }
            Err(err) => {
                for result in results {
                    result.discard_storage();
                }
                ctx.truncate_environment_storage(temp_start);
                return Err(err);
            }
        }
    }
    Ok(ControlFlow::Continue(results))
}

fn eval_owned_arg(
    arena: &NodeArena,
    arg: NodeId,
    ty: Type,
    ctx: &mut EvalCtx,
    locals: &[LocalDecl],
) -> Result<ControlFlow<ValOrMut>, RuntimeError> {
    let temp_start = ctx.environment.len();
    match try_resolve_node_place(arena, arg, ctx, locals) {
        // If the expression is a place, materialize the by-value argument using
        // the expected callee type. For dictionary-projected concrete methods,
        // the place node can still carry the caller's generic surface type.
        Ok(ControlFlow::Continue(Some(place))) => {
            let value = copy_trivial_value_from_place(&place, ty, ctx, arena[arg].span);
            ctx.truncate_environment_storage(temp_start);
            Ok(ControlFlow::Continue(ValOrMut::Val(value?)))
        }
        Ok(ControlFlow::Continue(None)) => eval_node_with_ctx(arena, arg, ctx, locals)
            .map(|result| result.map_continue(ValOrMut::Val)),
        Ok(ControlFlow::Return(value)) => Ok(ControlFlow::Return(value)),
        Err(err) => Err(err),
    }
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
    let result = try_dictionary_from_place(&place, ctx).is_some();
    Ok(ControlFlow::Continue(result))
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
    let ty_data = ty.data();
    let TypeKind::Native(native) = &*ty_data else {
        return false;
    };
    native.arguments.is_empty()
        && (native.bare_ty == bare_native_type::<()>()
            || native.bare_ty == bare_native_type::<bool>()
            || native.bare_ty == bare_native_type::<isize>())
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
            place.path.push(index.as_index() as isize);
            place
        }
        ProjectAt(node, index) => {
            let Some(mut place) =
                eval_or_return!(try_resolve_node_place(arena, *node, ctx, locals))
            else {
                return Ok(ControlFlow::Continue(None));
            };
            let index = extra_parameter_environment_index(ctx, *index);
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
        Apply(app) if app.returns_place => {
            let result = eval_apply(arena, app, node.span, ctx, locals)?;
            return Ok(control_flow_into_place_result(result).map_continue(Some));
        }
        StaticApply(app) if app.returns_place => {
            let result = eval_place_result_static_apply(arena, app, node.span, ctx, locals)?;
            return Ok(control_flow_into_place_result(result).map_continue(Some));
        }
        ValueClone(node) => return try_resolve_node_place(arena, node.source, ctx, locals),
        Block(nodes) => {
            let Some(place_index) = nodes.iter().rposition(|node| {
                !matches!(
                    arena[*node].kind,
                    NodeKind::EnvDrop(_) | NodeKind::EnvStore(_)
                )
            }) else {
                return Ok(ControlFlow::Continue(None));
            };
            for &node in &nodes[..place_index] {
                eval_or_return!(eval_node_with_ctx(arena, node, ctx, locals));
            }
            return try_resolve_node_place(arena, nodes[place_index], ctx, locals);
        }
        EnvLoad(node) => Place {
            // By using frame_base here, we allow to access parent frames
            // when the Place is used in a child function.
            target: local_environment_index(ctx, locals, node.id),
            path: Vec::new(),
        },
        _ => return Ok(ControlFlow::Continue(None)),
    })))
}

#[cfg(test)]
mod tests {
    use std::{
        fmt,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use crate::{
        CompilerSession, Location,
        eval::{ControlFlow, EvalCtx, eval_args, eval_nodes},
        hir::{
            Immediate, Node, NodeArena, NodeKind,
            function::ArgPassing,
            value::{LiteralValue, NativeDisplay},
        },
        module::{ModuleId, id::Id},
        types::{
            effects::EffType,
            r#type::{FnArgType, Type},
        },
    };

    static EVAL_DROP_TRACKED_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    struct EvalDropTracked;

    impl Drop for EvalDropTracked {
        fn drop(&mut self) {
            EVAL_DROP_TRACKED_COUNT.fetch_add(1, Ordering::Relaxed);
        }
    }

    impl NativeDisplay for EvalDropTracked {
        fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "<eval-drop-tracked>")
        }
    }

    fn reset_eval_drop_tracked_count() {
        EVAL_DROP_TRACKED_COUNT.store(0, Ordering::Relaxed);
    }

    fn eval_drop_tracked_count() -> usize {
        EVAL_DROP_TRACKED_COUNT.load(Ordering::Relaxed)
    }

    #[test]
    fn eval_nodes_discards_partial_values_on_return() {
        reset_eval_drop_tracked_count();
        let span = Location::new_synthesized();
        let mut arena = NodeArena::default();
        let tracked = arena.alloc(Node::new(
            NodeKind::Immediate(Immediate::new(LiteralValue::new_native(EvalDropTracked))),
            Type::primitive::<EvalDropTracked>(),
            EffType::empty(),
            span,
        ));
        let unit = arena.alloc(Node::new(
            NodeKind::Immediate(Immediate::new(LiteralValue::new_native(()))),
            Type::unit(),
            EffType::empty(),
            span,
        ));
        let return_unit = arena.alloc(Node::new(
            NodeKind::Return(unit),
            Type::never(),
            EffType::empty(),
            span,
        ));
        let session = CompilerSession::new();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);

        let result = eval_nodes(&arena, &[tracked, return_unit], &mut ctx, &[]).unwrap();
        let ControlFlow::Return(value) = result else {
            panic!("expected eval_nodes to propagate return");
        };

        assert_eq!(eval_drop_tracked_count(), 1);
        value.discard_storage();
    }

    #[test]
    fn eval_args_discards_partial_values_on_return() {
        reset_eval_drop_tracked_count();
        let span = Location::new_synthesized();
        let mut arena = NodeArena::default();
        let tracked = arena.alloc(Node::new(
            NodeKind::Immediate(Immediate::new(LiteralValue::new_native(EvalDropTracked))),
            Type::primitive::<EvalDropTracked>(),
            EffType::empty(),
            span,
        ));
        let unit = arena.alloc(Node::new(
            NodeKind::Immediate(Immediate::new(LiteralValue::new_native(()))),
            Type::unit(),
            EffType::empty(),
            span,
        ));
        let return_unit = arena.alloc(Node::new(
            NodeKind::Return(unit),
            Type::never(),
            EffType::empty(),
            span,
        ));
        let session = CompilerSession::new();
        let mut ctx = EvalCtx::new(ModuleId::from_index(0), &session);
        let arg_tys = [
            FnArgType::new_by_val(Type::primitive::<EvalDropTracked>()),
            FnArgType::new_by_val(Type::unit()),
        ];
        let arg_passing = [ArgPassing::OwnedValue, ArgPassing::OwnedValue];

        let result = eval_args(
            &arena,
            &[tracked, return_unit],
            &arg_tys,
            Some(&arg_passing),
            &mut ctx,
            &[],
        )
        .unwrap();
        let ControlFlow::Return(value) = result else {
            panic!("expected eval_args to propagate return");
        };

        assert_eq!(eval_drop_tracked_count(), 1);
        value.discard_storage();
    }
}
