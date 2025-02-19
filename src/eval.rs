// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{collections::VecDeque, fmt::Display};

use enum_as_inner::EnumAsInner;

use crate::{
    containers::{b, SVec2},
    error::RuntimeError,
    format::{write_with_separator, FormatWith},
    function::Closure,
    ir::{Node, NodeKind},
    module::{FmtWithModuleEnv, ModuleEnv},
    r#type::FnArgType,
    std::{array, range},
    value::{NativeValue, Value},
};

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

impl Display for FormatWithEvalCtx<'_, ValOrMut> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            ValOrMut::Val(value) => write!(f, "value {value}"),
            ValOrMut::Mut(place) => write!(f, "mut. ref. {}", FormatWith::new(place, self.data)),
        }
    }
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
}

impl EvalCtx {
    const DEFAULT_RECURSION_LIMIT: usize = 100;

    #[allow(clippy::new_without_default)]
    pub fn new() -> EvalCtx {
        EvalCtx {
            environment: Vec::new(),
            frame_base: 0,
            recursion: 0,
            recursion_limit: Self::DEFAULT_RECURSION_LIMIT,
        }
    }
}

type FormatWithEvalCtx<'a, T> = FormatWith<'a, T, EvalCtx>;

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

impl Display for FormatWithEvalCtx<'_, Place> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Place { target, path } = self.value;
        let ctx = self.data;
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

/// The result of evaluating an IR node, either a Value or a runtime error.
pub type EvalResult = Result<Value, RuntimeError>;

impl Node {
    /// Evaluate this node and return the result.
    pub fn eval(&self) -> EvalResult {
        let mut ctx = EvalCtx::new();
        self.eval_with_ctx(&mut ctx)
    }

    /// Evaluate this node given the environment and return the result.
    pub fn eval_with_ctx(&self, ctx: &mut EvalCtx) -> EvalResult {
        use NodeKind::*;
        match &self.kind {
            Immediate(immediate) => Ok(immediate.value.clone()),
            BuildClosure(build_closure) => {
                let captured = eval_nodes(&build_closure.captures, ctx)?;
                let function_value = build_closure.function.eval_with_ctx(ctx)?;
                let function = function_value.into_function().unwrap().0;
                Ok(Value::function(b(Closure::new(function, captured))))
            }
            Apply(app) => {
                let args_ty = {
                    app.function
                        .ty
                        .data()
                        .as_function()
                        .expect("Apply needs a function type")
                        .args
                        .clone()
                };
                let function_value = app.function.eval_with_ctx(ctx)?;
                let function = function_value.as_function().unwrap().0.get();
                let function = function.borrow();
                let arguments = eval_args(&app.arguments, &args_ty, ctx)?;
                function.call(arguments, ctx)
            }
            StaticApply(app) => {
                let args_ty = &app.ty.args;
                let function = app.function.get();
                let function = function.borrow();
                let arguments = eval_args(&app.arguments, args_ty, ctx)?;
                function.call(arguments, ctx)
            }
            TraitFnApply(_) => {
                panic!("Trait function application should not be executed, but transformed to StaticApply");
            }
            EnvStore(node) => {
                let value = node.node.eval_with_ctx(ctx)?;
                ctx.environment.push(ValOrMut::Val(value));
                Ok(Value::unit())
            }
            EnvLoad(node) => {
                let index = ctx.frame_base + node.index;
                Ok(ctx.environment[index].as_value(ctx)?)
            }
            Block(nodes) => {
                let env_size = ctx.environment.len();
                let return_value = nodes
                    .iter()
                    .try_fold(None, |_, node| Ok(Some(node.eval_with_ctx(ctx)?)))?
                    .unwrap_or(Value::unit());
                ctx.environment.truncate(env_size);
                Ok(return_value)
            }
            Assign(assignment) => {
                let value = assignment.value.eval_with_ctx(ctx)?;
                let target_ref = assignment.place.as_place(ctx)?.target_mut(ctx)?;
                *target_ref = value;
                Ok(Value::unit())
            }
            Tuple(nodes) => {
                let values = nodes.iter().try_fold(SVec2::new(), |mut nodes, node| {
                    nodes.push(node.eval_with_ctx(ctx)?);
                    Ok(nodes)
                })?;
                Ok(Value::Tuple(b(values)))
            }
            Project(projection) => {
                let value = projection.0.eval_with_ctx(ctx)?;
                Ok(match value {
                    Value::Tuple(tuple) => tuple.into_iter().nth(projection.1).unwrap(),
                    Value::Variant(variant) => variant.value,
                    _ => panic!("Cannot project from a non-compound value"),
                })
            }
            Record(nodes) => {
                let values = nodes.iter().try_fold(SVec2::new(), |mut nodes, node| {
                    nodes.push(node.eval_with_ctx(ctx)?);
                    Ok(nodes)
                })?;
                // Note: record values are stored as tuples
                Ok(Value::Tuple(b(values)))
            }
            FieldAccess(_) => {
                panic!("String projection should not be executed, but transformed to ProjectLocal");
            }
            ProjectAt(access) => {
                let value = access.0.eval_with_ctx(ctx)?;
                let index = ctx.frame_base + access.1;
                let index = ctx.environment[index]
                    .as_value(ctx)?
                    .into_primitive_ty::<isize>()
                    .unwrap();
                Ok(match value {
                    Value::Tuple(tuple) => tuple.into_iter().nth(index as usize).unwrap(),
                    _ => panic!("Cannot access field from a non-compound value"),
                })
            }
            Variant(variant) => {
                let value = variant.1.eval_with_ctx(ctx)?;
                Ok(Value::variant(variant.0, value))
            }
            ExtractTag(node) => {
                let value = node.eval_with_ctx(ctx)?;
                let variant = value.into_variant().unwrap();
                Ok(Value::native(variant.tag_as_isize()))
            }
            Array(nodes) => {
                let values = eval_nodes(nodes, ctx)?;
                Ok(Value::native(array::Array::from_vec(values)))
            }
            Index(array, index) => {
                let index = index
                    .eval_with_ctx(ctx)?
                    .into_primitive_ty::<isize>()
                    .unwrap();
                let mut array = array
                    .eval_with_ctx(ctx)?
                    .into_primitive_ty::<array::Array>()
                    .unwrap();
                match array.get_mut_signed(index) {
                    Some(value) => Ok(value.clone()),
                    None => {
                        let len = array.len();
                        Err(RuntimeError::ArrayAccessOutOfBounds { index, len })
                    }
                }
            }
            Case(case) => {
                let value = case.value.eval_with_ctx(ctx)?;
                for (alternative, node) in &case.alternatives {
                    if value == *alternative {
                        return node.eval_with_ctx(ctx);
                    }
                }
                case.default.eval_with_ctx(ctx)
            }
            Iterate(iteration) => {
                // TODO: use a more generic type for iterator!
                let iterator = iteration
                    .iterator
                    .eval_with_ctx(ctx)?
                    .into_primitive_ty::<range::RangeIterator>()
                    .unwrap();
                for value in iterator {
                    ctx.environment.push(ValOrMut::Val(Value::native(value)));
                    _ = iteration.body.eval_with_ctx(ctx)?;
                    ctx.environment.pop();
                }
                Ok(Value::unit())
            }
        }
    }

    /// Evaluate this node given the environment and print the result.
    pub fn eval_and_print(&self, ctx: &mut EvalCtx, env: &ModuleEnv) {
        match self.eval_with_ctx(ctx) {
            Ok(value) => println!("{value}: {}", self.ty.format_with(env)),
            Err(error) => println!("Runtime error: {error:?}"),
        }
    }

    /// Return this node as a place in the environment.
    pub fn as_place(&self, ctx: &mut EvalCtx) -> Result<Place, RuntimeError> {
        fn resolve_node(node: &Node, ctx: &mut EvalCtx) -> Result<Place, RuntimeError> {
            use NodeKind::*;
            Ok(match &node.kind {
                Project(projection) => {
                    let (ref node, index) = **projection;
                    let mut place = resolve_node(node, ctx)?;
                    place.path.push(index as isize);
                    place
                }
                ProjectAt(projection) => {
                    let (ref node, index) = **projection;
                    let mut place = resolve_node(node, ctx)?;
                    let index = ctx.frame_base + index;
                    let index_value = ctx.environment[index].as_value(ctx)?;
                    let index = index_value.into_primitive_ty::<isize>().unwrap();
                    place.path.push(index);
                    place
                }
                Index(array, index) => {
                    let mut place = resolve_node(array, ctx)?;
                    let index_value = index.eval_with_ctx(ctx)?;
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
            })
        }
        resolve_node(self, ctx)
    }
}

fn eval_nodes(nodes: &[Node], ctx: &mut EvalCtx) -> Result<Vec<Value>, RuntimeError> {
    eval_nodes_with(nodes.iter(), |node, ctx| node.eval_with_ctx(ctx), ctx)
}

fn eval_args(
    args: &[Node],
    args_ty: &[FnArgType],
    ctx: &mut EvalCtx,
) -> Result<Vec<ValOrMut>, RuntimeError> {
    // Automatically cast mutable references to values if the function expects values.
    let f = |(arg, ty): &(&Node, &FnArgType), ctx: &mut EvalCtx| {
        let is_mutable = ty
            .mut_ty
            .as_resolved()
            .expect("Unresolved mutability variable found during execution")
            .is_mutable();
        Ok(if is_mutable {
            ValOrMut::Mut(arg.as_place(ctx)?)
        } else {
            ValOrMut::Val(arg.eval_with_ctx(ctx)?)
        })
    };
    eval_nodes_with(args.iter().zip(args_ty), f, ctx)
}

fn eval_nodes_with<F, I, O, It>(
    mut inputs: It,
    f: F,
    ctx: &mut EvalCtx,
) -> Result<Vec<O>, RuntimeError>
where
    It: Iterator<Item = I>,
    F: Fn(&I, &mut EvalCtx) -> Result<O, RuntimeError>,
{
    inputs.try_fold(vec![], |mut output, input| {
        output.push(f(&input, ctx)?);
        Ok(output)
    })
}
