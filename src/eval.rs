// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{collections::VecDeque, mem, rc::Rc};

#[cfg(debug_assertions)]
use derive_new::new;
use enum_as_inner::EnumAsInner;
#[cfg(debug_assertions)]
use ustr::{Ustr, ustr};

use crate::{
    containers::b,
    error::RuntimeError,
    format::{FormatWith, write_with_separator},
    function::{Closure, FunctionRc},
    ir::{Node, NodeKind},
    module::{FunctionId, ModuleRc, TraitImplId},
    std::array,
    r#type::FnArgType,
    value::{FunctionValue, NativeValue, Value},
};

#[cfg(debug_assertions)]
use crate::module::ImportFunctionTarget;

/// Either a value or a unique mutable reference to a value.
/// This allows to implement the mutable value semantics.
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
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

    pub fn as_mut_primitive<T: 'static>(
        self,
        ctx: &mut EvalCtx,
    ) -> Result<Option<&mut T>, RuntimeError> {
        Ok(match self {
            ValOrMut::Val(_) => None,
            ValOrMut::Mut(place) => place.target_mut(ctx)?.as_primitive_ty_mut::<T>(),
        })
    }

    pub fn as_value(&self, ctx: &EvalCtx) -> Result<Value, RuntimeError> {
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

impl FormatWith<EvalCtx> for ValOrMut {
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &EvalCtx) -> std::fmt::Result {
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
    fn_name: String,
    mod_name: Ustr,
    frame_base: usize,
}

/// Along with the Rust native stack, corresponds to the Zinc Abstract Machine of Caml language family
/// with the addition of Mutable Value Semantics through references to earlier stack frames
pub struct EvalCtx {
    /// all values or mutable references of all stack frames
    pub environment: Vec<ValOrMut>,
    /// base of current stack frame in `environment`
    pub frame_base: usize,
    /// recursion counter
    pub recursion: usize,
    /// maximum number of recursion
    pub recursion_limit: usize,
    /// a flag to break the evaluation
    pub break_loop: bool,
    /// reference to the current module for import slot resolution
    pub module: ModuleRc,
    #[cfg(debug_assertions)]
    stack_trace: Vec<StackEntry>,
    #[cfg(debug_assertions)]
    pub environment_names: Vec<Ustr>,
}

impl EvalCtx {
    const DEFAULT_RECURSION_LIMIT: usize = 100;

    pub fn new(module: ModuleRc) -> EvalCtx {
        EvalCtx {
            environment: Vec::new(),
            frame_base: 0,
            recursion: 0,
            recursion_limit: Self::DEFAULT_RECURSION_LIMIT,
            break_loop: false,
            module,
            #[cfg(debug_assertions)]
            stack_trace: Vec::new(),
            #[cfg(debug_assertions)]
            environment_names: Vec::new(),
        }
    }

    pub fn with_environment(module: ModuleRc, environment: Vec<ValOrMut>) -> EvalCtx {
        #[cfg(debug_assertions)]
        let environment_names = vec![ustr("<unknown>"); environment.len()];
        EvalCtx {
            environment,
            frame_base: 0,
            recursion: 0,
            recursion_limit: Self::DEFAULT_RECURSION_LIMIT,
            break_loop: false,
            module,
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
            self.frame_base, self.recursion
        );
        eprintln!("Environment:");
        let mut i = self.environment_names.len();
        for entry in self.stack_trace.iter().rev() {
            while i > entry.frame_base {
                i -= 1;
                eprintln!("  {}", self.environment_names[i]);
            }
            eprintln!("- {}", entry.fn_name);
        }
        while i > 0 {
            i -= 1;
            eprintln!("  {}", self.environment_names[i]);
        }
    }

    /// Get the function code for a FunctionId at runtime using module.
    pub fn get_function(&self, function: FunctionId) -> (FunctionRc, ModuleRc) {
        use FunctionId::*;
        match &function {
            Local(id) => (
                self.module.functions[id.as_index()].function.code.clone(),
                self.module.clone(),
            ),
            Import(id) => {
                let slot = &self.module.import_fn_slots[id.as_index()];
                let resolved = slot.resolved.borrow();
                let resolved = resolved.as_ref().unwrap_or_else(|| {
                    panic!("Function import slot #{id} not resolved.\nSlot data: {slot:?}")
                });
                (resolved.0.clone(), resolved.1.clone())
            }
        }
    }

    #[cfg(debug_assertions)]
    fn get_last_module_name(&self) -> Ustr {
        self.stack_trace
            .last()
            .map(|entry| entry.mod_name)
            .unwrap_or(ustr("<current>"))
    }

    #[cfg(debug_assertions)]
    fn get_stack_entry_from_fn_and_mod(
        &self,
        function: &FunctionRc,
        module: &ModuleRc,
    ) -> StackEntry {
        let fn_name = format!("value function {:p}::{:p}", module, function);
        StackEntry::new(fn_name, ustr("<unknown>"), self.environment.len())
    }

    #[cfg(debug_assertions)]
    fn get_stack_entry_from_function_id(&self, function: FunctionId) -> StackEntry {
        use FunctionId::*;
        let module_name;
        let fn_name = match &function {
            Local(id) => {
                let function = &self.module.functions[id.as_index()];
                module_name = self.get_last_module_name();
                format!(
                    "{module_name}::{} (#{})",
                    function.name.map_or("<anonymous>", |s| s.as_str()),
                    id
                )
            }
            Import(id) => {
                let slot = &self.module.import_fn_slots[id.as_index()];
                module_name = slot.module_name;
                use ImportFunctionTarget::*;
                match &slot.target {
                    TraitImplMethod { key, index } => {
                        let trait_ref = key.trait_ref();
                        let fn_name = trait_ref.functions[*index as usize].0;
                        format!(
                            "{module_name}::impl {} for <…>::{}",
                            trait_ref.name, fn_name
                        )
                    }
                    NamedFunction(fn_name) => {
                        format!("{module_name}::{fn_name}")
                    }
                }
            }
        };
        StackEntry::new(fn_name, module_name, self.environment.len())
    }

    /// Get the dictionary value for a ImplId at runtime using module.
    pub fn get_dictionary(&self, dictionary: TraitImplId) -> Value {
        use TraitImplId::*;
        match &dictionary {
            Local(id) => self.module.impls.data[id.as_index()]
                .dictionary_value
                .borrow()
                .clone(),
            Import(id) => {
                let slot = &self.module.import_impl_slots[id.as_index()];
                slot.resolved
                    .borrow()
                    .as_ref()
                    .unwrap_or_else(|| {
                        panic!("Impl import slot #{id} not resolved.\nSlot data: {slot:?}")
                    })
                    .0
                    .clone()
            }
        }
    }

    /// Call a function value along containing its module context.
    pub fn call_function_value(
        &mut self,
        function_value: &FunctionValue,
        arguments: Vec<ValOrMut>,
    ) -> EvalControlFlowResult {
        let function = &function_value.function;
        let module = function_value.upgrade_module();
        #[cfg(debug_assertions)]
        self.stack_trace
            .push(self.get_stack_entry_from_fn_and_mod(function, &module));
        let result = self.call_function(function, module, arguments)?;
        #[cfg(debug_assertions)]
        self.stack_trace.pop();
        Ok(result)
    }

    /// Call a function by its id, this will look up the function and its module.
    pub fn call_function_id(
        &mut self,
        function_id: FunctionId,
        arguments: Vec<ValOrMut>,
    ) -> EvalControlFlowResult {
        let (function, module) = self.get_function(function_id);
        #[cfg(debug_assertions)]
        self.stack_trace
            .push(self.get_stack_entry_from_function_id(function_id));
        let result = self.call_function(&function, module, arguments)?;
        #[cfg(debug_assertions)]
        self.stack_trace.pop();
        Ok(result)
    }

    /// Call a function along with its correct module context.
    fn call_function(
        &mut self,
        function: &FunctionRc,
        mut module: ModuleRc,
        arguments: Vec<ValOrMut>,
    ) -> EvalControlFlowResult {
        // Use the new module for the duration of the function call.
        mem::swap(&mut self.module, &mut module);
        // Call the function.
        let result = function.borrow().call(arguments, self);
        // Restore the previous module.
        mem::swap(&mut self.module, &mut module);
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
    pub fn target_mut<'c>(&self, ctx: &'c mut EvalCtx) -> Result<&'c mut Value, RuntimeError> {
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
                        None => return Err(RuntimeError::ArrayAccessOutOfBounds { index, len }),
                    }
                }
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }

    /// Get a shared reference to the target value
    pub fn target_ref<'c>(&self, ctx: &'c EvalCtx) -> Result<&'c Value, RuntimeError> {
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
                        None => return Err(RuntimeError::ArrayAccessOutOfBounds { index, len }),
                    }
                }
                _ => panic!("Cannot access a non-compound value"),
            };
        }
        Ok(target)
    }
}

impl FormatWith<EvalCtx> for Place {
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &EvalCtx) -> std::fmt::Result {
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

#[derive(Debug, Clone, PartialEq, Eq)]
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

/// The result of evaluating an IR node, either a control flow action or a runtime error.
pub type EvalControlFlowResult = Result<ControlFlow<Value>, RuntimeError>;

/// The result of evaluating an IR node, either a value or a runtime error.
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

impl Node {
    /// Evaluate this node and return the result.
    pub fn eval(&self, module: ModuleRc) -> EvalControlFlowResult {
        let mut ctx = EvalCtx::new(module);
        self.eval_with_ctx(&mut ctx)
    }

    /// Evaluate this node given the environment and return the result.
    pub fn eval_with_ctx(&self, ctx: &mut EvalCtx) -> EvalControlFlowResult {
        use NodeKind::*;
        match &self.kind {
            Immediate(immediate) => cont(immediate.value.clone()),
            BuildClosure(build_closure) => {
                let captured = eval_or_return!(eval_nodes(&build_closure.captures, ctx));
                // Note: function should be GetFunction or similar immediate - returns not allowed here
                let function_value = build_closure.function.eval_with_ctx(ctx)?.into_value();
                let function_value = function_value.into_function().unwrap().function;
                let function_value = FunctionValue::new(function_value, Rc::downgrade(&ctx.module));
                cont(Value::function(
                    b(Closure::new(function_value, captured)),
                    Rc::downgrade(&ctx.module),
                ))
            }
            Apply(app) => {
                // Evaluate left-to-right: function first, then arguments (matches Rust semantics)
                let function_value = eval_or_return!(app.function.eval_with_ctx(ctx));
                let function_value = function_value.as_function().unwrap();
                let args_ty = {
                    app.function
                        .ty
                        .data()
                        .as_function()
                        .expect("Apply needs a function type")
                        .args
                        .clone()
                };
                let arguments = eval_or_return!(eval_args(&app.arguments, &args_ty, ctx));
                ctx.call_function_value(function_value, arguments)
            }
            StaticApply(app) => {
                let arguments = eval_or_return!(eval_args(&app.arguments, &app.ty.args, ctx));
                ctx.call_function_id(app.function, arguments)
            }
            TraitFnApply(_) => {
                panic!(
                    "Trait function application should not be executed, but transformed to StaticApply"
                );
            }
            GetFunction(get_fn) => {
                let (function, module) = ctx.get_function(get_fn.function);
                cont(Value::function_rc(function, Rc::downgrade(&module)))
            }
            GetDictionary(get_dict) => {
                let value = ctx.get_dictionary(get_dict.dictionary);
                cont(value)
            }
            EnvStore(node) => {
                let value = eval_or_return!(node.value.eval_with_ctx(ctx));
                ctx.environment.push(ValOrMut::Val(value));
                #[cfg(debug_assertions)]
                ctx.environment_names.push(node.name);
                cont(Value::unit())
            }
            EnvLoad(node) => {
                let index = ctx.frame_base + node.index;
                cont(ctx.environment[index].as_value(ctx)?)
            }
            Return(node) => ret(node.eval_with_ctx(ctx)?.into_value()),
            Block(nodes) => {
                let env_size = ctx.environment.len();
                let mut last_value = Value::unit();
                for node in nodes.iter() {
                    match node.eval_with_ctx(ctx)? {
                        ControlFlow::Return(val) => {
                            // Early return: clean up environment and propagate
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
                // Normal block completion
                ctx.environment.truncate(env_size);
                #[cfg(debug_assertions)]
                ctx.environment_names.truncate(env_size);
                cont(last_value)
            }
            Assign(assignment) => {
                // Evaluate left-to-right: place first, then value (matches Rust semantics)
                let place = eval_or_return!(assignment.place.as_place(ctx));
                let value = eval_or_return!(assignment.value.eval_with_ctx(ctx));
                let target_ref = place.target_mut(ctx)?;
                *target_ref = value;
                cont(Value::unit())
            }
            Tuple(nodes) | Record(nodes) => {
                // Note: record values are stored as tuples
                let values = eval_or_return!(eval_nodes(nodes, ctx));
                cont(Value::Tuple(b(values.into())))
            }
            Project(projection) => {
                let value = eval_or_return!(projection.0.eval_with_ctx(ctx));
                cont(match value {
                    Value::Tuple(tuple) => tuple.into_iter().nth(projection.1).unwrap(),
                    Value::Variant(variant) => variant.value,
                    _ => panic!("Cannot project from a non-compound value"),
                })
            }
            FieldAccess(_) => {
                panic!("String projection should not be executed, but transformed to ProjectLocal");
            }
            ProjectAt(access) => {
                let value = eval_or_return!(access.0.eval_with_ctx(ctx));
                let index = ctx.frame_base + access.1;
                let index = ctx.environment[index]
                    .as_value(ctx)?
                    .into_primitive_ty::<isize>()
                    .unwrap();
                cont(match value {
                    Value::Tuple(tuple) => tuple.into_iter().nth(index as usize).unwrap(),
                    _ => panic!("Cannot access field from a non-compound value"),
                })
            }
            Variant(variant) => {
                let value = eval_or_return!(variant.1.eval_with_ctx(ctx));
                cont(Value::raw_variant(variant.0, value))
            }
            ExtractTag(node) => {
                let value = eval_or_return!(node.eval_with_ctx(ctx));
                let variant = value.into_variant().unwrap();
                cont(Value::native(variant.tag_as_isize()))
            }
            Array(nodes) => {
                let values = eval_or_return!(eval_nodes(nodes, ctx));
                cont(Value::native(array::Array::from_vec(values)))
            }
            Index(array, index) => {
                // Evaluate left-to-right: array first, then index (matches Rust semantics)
                let mut array = eval_or_return!(array.eval_with_ctx(ctx))
                    .into_primitive_ty::<array::Array>()
                    .unwrap();
                let index = eval_or_return!(index.eval_with_ctx(ctx))
                    .into_primitive_ty::<isize>()
                    .unwrap();
                match array.get_mut_signed(index) {
                    Some(value) => cont(value.clone()),
                    None => {
                        let len = array.len();
                        Err(RuntimeError::ArrayAccessOutOfBounds { index, len })
                    }
                }
            }
            Case(case) => {
                let value = eval_or_return!(case.value.eval_with_ctx(ctx));
                for (alternative, node) in &case.alternatives {
                    if value == *alternative {
                        return node.eval_with_ctx(ctx);
                    }
                }
                case.default.eval_with_ctx(ctx)
            }
            Loop(body) => {
                let break_loop = ctx.break_loop;
                ctx.break_loop = false;
                while !ctx.break_loop {
                    eval_or_return!(body.eval_with_ctx(ctx));
                }
                ctx.break_loop = break_loop;
                cont(Value::unit())
            }
            SoftBreak => {
                ctx.break_loop = true;
                cont(Value::unit())
            }
        }
    }

    /// Return this node as a place in the environment.
    pub fn as_place(&self, ctx: &mut EvalCtx) -> Result<ControlFlow<Place>, RuntimeError> {
        fn resolve_node(
            node: &Node,
            ctx: &mut EvalCtx,
        ) -> Result<ControlFlow<Place>, RuntimeError> {
            use NodeKind::*;
            Ok(ControlFlow::Continue(match &node.kind {
                Project(projection) => {
                    let (ref node, index) = **projection;
                    let mut place = eval_or_return!(resolve_node(node, ctx));
                    place.path.push(index as isize);
                    place
                }
                ProjectAt(projection) => {
                    let (ref node, index) = **projection;
                    let mut place = eval_or_return!(resolve_node(node, ctx));
                    let index = ctx.frame_base + index;
                    let index_value = ctx.environment[index].as_value(ctx)?;
                    let index = index_value.into_primitive_ty::<isize>().unwrap();
                    place.path.push(index);
                    place
                }
                Index(array, index) => {
                    let mut place = eval_or_return!(resolve_node(array, ctx));
                    let index_value = eval_or_return!(index.eval_with_ctx(ctx));
                    let index = index_value.into_primitive_ty::<isize>().unwrap();
                    place.path.push(index);
                    place
                }
                EnvLoad(node) => Place {
                    // By using frame_base here, we allow to access parent frames
                    // when the ResolvedPlace is used in a child function.
                    target: ctx.frame_base + node.index,
                    path: Vec::new(),
                },
                _ => panic!("Cannot resolve a non-place node"),
            }))
        }
        resolve_node(self, ctx)
    }
}

fn eval_nodes(nodes: &[Node], ctx: &mut EvalCtx) -> Result<ControlFlow<Vec<Value>>, RuntimeError> {
    let mut results = Vec::with_capacity(nodes.len());
    for node in nodes {
        results.push(eval_or_return!(node.eval_with_ctx(ctx)));
    }
    Ok(ControlFlow::Continue(results))
}

fn eval_args(
    args: &[Node],
    args_ty: &[FnArgType],
    ctx: &mut EvalCtx,
) -> Result<ControlFlow<Vec<ValOrMut>>, RuntimeError> {
    // Automatically cast mutable references to values if the function expects values.
    let mut results = Vec::with_capacity(args.len());
    assert_eq!(args.len(), args_ty.len());
    for (arg, ty) in args.iter().zip(args_ty) {
        let is_mutable = ty
            .mut_ty
            .as_resolved()
            .expect("Unresolved mutability variable found during execution")
            .is_mutable();
        results.push(if is_mutable {
            ValOrMut::Mut(eval_or_return!(arg.as_place(ctx)))
        } else {
            ValOrMut::Val(eval_or_return!(arg.eval_with_ctx(ctx)))
        });
    }
    Ok(ControlFlow::Continue(results))
}
