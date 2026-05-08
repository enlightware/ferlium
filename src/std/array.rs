// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{collections::VecDeque, fmt};

use ustr::ustr;

use crate::{
    Location, cached_ty,
    compiler::error::RuntimeErrorKind,
    eval::{
        EvalControlFlowResult, EvalCtx, Place, RuntimeError, ValOrMut, call_value_clone_for_temp,
        call_value_drop_for_temp, cont,
    },
    format::{write_with_separator, write_with_separator_and_format_fn},
    hir::function::{
        ArgPassing, Callable, Function, FunctionDefinition, NullaryNativeFnN, UnaryNativeFnMV,
        UnaryNativeFnNN, UnaryNativeFnRN,
    },
    hir::value::{NativeDisplay, NativeValue, Value},
    module::{BlanketTraitImplSubKey, LocalDecl, Module, ModuleEnv, ModuleFunction},
    types::effects::no_effects,
    types::r#type::{FnType, NativeType, Type, bare_native_type},
    types::type_scheme::{PubTypeConstraint, TypeScheme},
};

use super::{
    default::DEFAULT_TRAIT,
    empty::EMPTY_TRAIT,
    math::int_type,
    option::{none, option_type_generic, some},
    value::VALUE_TRAIT,
};

#[derive(Debug, Clone)]
pub struct Array(VecDeque<Value>);

impl Array {
    pub fn new() -> Self {
        Self(VecDeque::new())
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self(VecDeque::with_capacity(capacity))
    }

    pub fn with_capacity_signed(capacity: isize) -> Self {
        Self::with_capacity(capacity.max(0) as usize)
    }

    pub fn from_vec(values: Vec<Value>) -> Self {
        Self::from_deque(VecDeque::from(values))
    }

    pub fn from_deque(values: VecDeque<Value>) -> Self {
        Self(values)
    }

    pub fn get(&self, index: usize) -> Option<&Value> {
        self.0.get(index)
    }

    pub fn get_signed(&self, index: isize) -> Option<&Value> {
        self.get(self.to_unsigned_index(index))
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut Value> {
        self.0.get_mut(index)
    }

    pub fn get_mut_signed(&mut self, index: isize) -> Option<&mut Value> {
        self.get_mut(self.to_unsigned_index(index))
    }

    pub fn push_back(&mut self, value: Value) {
        self.0.push_back(value);
    }

    pub fn push_front(&mut self, value: Value) {
        self.0.push_front(value);
    }

    pub fn pop_back_raw(&mut self) -> Option<Value> {
        self.0.pop_back()
    }

    pub fn pop_front_raw(&mut self) -> Option<Value> {
        self.0.pop_front()
    }

    fn to_unsigned_index(&self, index: isize) -> usize {
        if index < 0 {
            (self.len() as isize + index) as usize
        } else {
            index as usize
        }
    }

    fn append_descr() -> ModuleFunction {
        let unit = Type::unit();
        let gen0 = Type::variable_id(0);
        array_native_function(
            FnType::new_mut_resolved(
                [(array_type(gen0), true), (gen0, false)],
                unit,
                no_effects(),
            ),
            value_constraint(gen0),
            ["array", "value"],
            "Appends an element to the back of the array.",
            ArrayAppendFunction { front: false },
        )
    }

    fn prepend_descr() -> ModuleFunction {
        let unit = Type::unit();
        let gen0 = Type::variable_id(0);
        array_native_function(
            FnType::new_mut_resolved(
                [(array_type(gen0), true), (gen0, false)],
                unit,
                no_effects(),
            ),
            value_constraint(gen0),
            ["array", "value"],
            "Prepends an element to the front of the array.",
            ArrayAppendFunction { front: true },
        )
    }

    pub fn pop_back(&mut self) -> Value {
        let value = self.pop_back_raw();
        match value {
            Some(v) => some(v),
            None => none(),
        }
    }

    fn pop_back_desc() -> ModuleFunction {
        let array = array_type_generic();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            [(array, true)],
            option_type_generic(),
            no_effects(),
        ));
        UnaryNativeFnMV::description_with_ty_scheme(
            Self::pop_back,
            ["array"],
            "Removes the last element of the array and returns it, or `None` if it is empty.",
            ty_scheme,
        )
    }

    pub fn pop_front(&mut self) -> Value {
        let value = self.pop_front_raw();
        match value {
            Some(v) => some(v),
            None => none(),
        }
    }

    fn pop_front_desc() -> ModuleFunction {
        let array = array_type_generic();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            [(array, true)],
            option_type_generic(),
            no_effects(),
        ));
        UnaryNativeFnMV::description_with_ty_scheme(
            Self::pop_front,
            ["array"],
            "Removes the first element of the array and returns it, or `None` if it is empty.",
            ty_scheme,
        )
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    fn len_descr() -> ModuleFunction {
        let array = array_type_generic();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
            [array],
            int_type(),
            no_effects(),
        ));
        UnaryNativeFnRN::description_with_ty_scheme(
            |a: &Self| a.len() as isize,
            ["array"],
            "Returns the length of the array.",
            ty_scheme,
        )
    }

    fn with_capacity_descr() -> ModuleFunction {
        let array = array_type_generic();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
            [int_type()],
            array,
            no_effects(),
        ));
        UnaryNativeFnNN::description_with_ty_scheme(
            |capacity: isize| Self::with_capacity_signed(capacity),
            ["capacity"],
            "Creates an empty array with at least the specified capacity.",
            ty_scheme,
        )
    }

    fn concat_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let array_ty = array_type(gen0);
        array_native_function(
            FnType::new_mut_resolved(
                [(array_ty, false), (array_ty, false)],
                array_ty,
                no_effects(),
            ),
            value_constraint(gen0),
            ["left", "right"],
            "Concatenates two arrays and returns the result.",
            ArrayConcatFunction,
        )
    }

    fn slice_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let array = array_type(gen0);
        array_native_function(
            FnType::new_by_val([array, int_type(), int_type()], array, no_effects()),
            value_constraint(gen0),
            ["array", "start", "end"],
            "Returns the slice of `array` from index `start` to index `end`. Negative indices count from the end.",
            ArraySliceFunction,
        )
    }

    fn value_clone_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let array = array_type(gen0);
        array_native_function(
            FnType::new_mut_resolved([(array, false), (array, true)], Type::unit(), no_effects()),
            value_constraint(gen0),
            ["source", "target"],
            "Clones an array through its element Value dictionary.",
            ArrayCloneFunction,
        )
    }

    fn value_drop_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let array = array_type(gen0);
        array_native_function(
            FnType::new_mut_resolved([(array, true)], Type::unit(), no_effects()),
            value_constraint(gen0),
            ["target"],
            "Drops an array through its element Value dictionary.",
            ArrayDropFunction,
        )
    }
}

fn value_constraint(ty: Type) -> Vec<PubTypeConstraint> {
    vec![PubTypeConstraint::new_have_trait(
        VALUE_TRAIT.clone(),
        vec![ty],
        vec![],
        Location::new_synthesized(),
    )]
}

fn array_native_function(
    ty: FnType,
    constraints: Vec<PubTypeConstraint>,
    arg_names: impl IntoIterator<Item = &'static str>,
    doc: &'static str,
    code: impl Callable + Clone + 'static,
) -> ModuleFunction {
    ModuleFunction {
        definition: FunctionDefinition::new(
            TypeScheme::new_infer_quantifiers_with_constraints(ty, constraints),
            arg_names.into_iter().map(ustr::Ustr::from).collect(),
            Some(String::from(doc)),
        ),
        code: Box::new(code),
        spans: None,
        locals: Vec::new(),
    }
}

fn dictionary_from_arg(arg: ValOrMut, ctx: &mut EvalCtx<'_>) -> Result<Value, RuntimeError> {
    match arg {
        ValOrMut::Val(value) => Ok(value),
        ValOrMut::Mut(place) => place
            .target_ref(ctx)
            .cloned()
            .map_err(RuntimeError::new_native),
    }
}

fn signed_index_for_len(len: usize, index: isize) -> usize {
    if index < 0 {
        (len as isize + index) as usize
    } else {
        index as usize
    }
}

struct ArraySource {
    place: Place,
    temp: bool,
}

impl ArraySource {
    fn new(arg: ValOrMut, ctx: &mut EvalCtx<'_>) -> Result<Self, RuntimeError> {
        match arg {
            ValOrMut::Mut(place) => Ok(Self { place, temp: false }),
            ValOrMut::Val(value) => {
                let target = ctx.environment.len();
                ctx.environment.push(ValOrMut::Val(value));
                #[cfg(debug_assertions)]
                ctx.environment_names.push(ustr("$array_source"));
                Ok(Self {
                    place: Place {
                        target,
                        path: Vec::new(),
                    },
                    temp: true,
                })
            }
        }
    }

    fn len(&self, ctx: &EvalCtx<'_>) -> Result<usize, RuntimeError> {
        let value = self
            .place
            .target_ref(ctx)
            .map_err(RuntimeError::new_native)?;
        Ok(value.as_primitive_ty::<Array>().unwrap().len())
    }

    fn element(&self, index: usize) -> ValOrMut {
        let mut place = self.place.clone();
        place.path.push(index as isize);
        ValOrMut::Mut(place)
    }

    fn finish(self, ctx: &mut EvalCtx<'_>) {
        if self.temp {
            #[cfg(debug_assertions)]
            ctx.environment_names.pop();
            ctx.environment.pop();
        }
    }
}

fn clone_array_range_into(
    ctx: &mut EvalCtx<'_>,
    dictionary: &Value,
    source: ValOrMut,
    start: usize,
    end: usize,
    output: &mut VecDeque<Value>,
) -> Result<(), RuntimeError> {
    let source = ArraySource::new(source, ctx)?;
    let outcome = (|| {
        let len = source.len(ctx)?;
        let end = end.min(len);
        if end <= start {
            return Ok(());
        }
        for index in start..end {
            let value = call_value_clone_for_temp(
                ctx,
                dictionary,
                source.element(index),
                Location::new_synthesized(),
            )?;
            output.push_back(value);
        }
        Ok(())
    })();
    source.finish(ctx);
    outcome
}

fn array_arg_as_mut<'a>(
    arg: &'a ValOrMut,
    ctx: &'a mut EvalCtx<'_>,
) -> Result<&'a mut Array, RuntimeError> {
    arg.as_mut_primitive::<Array>(ctx)
        .map_err(RuntimeError::new_native)?
        .ok_or_else(|| RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(ustr("array"))))
}

// These custom callables are an interpreter bridge: they let native array storage call
// Ferlium `Value` clone/drop today. Long term, array storage should expose smaller
// slot-oriented primitives so these loops can move back into Ferlium std source.
#[derive(Debug, Clone, Copy)]
struct ArrayAppendFunction {
    front: bool,
}

impl Callable for ArrayAppendFunction {
    fn call(
        &self,
        args: Vec<ValOrMut>,
        ctx: &mut EvalCtx,
        _locals: &[LocalDecl],
    ) -> EvalControlFlowResult {
        let mut args = args.into_iter();
        let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
        let array_arg = args.next().unwrap();
        let value_arg = args.next().unwrap();
        let value =
            call_value_clone_for_temp(ctx, &dictionary, value_arg, Location::new_synthesized())?;
        let array = array_arg_as_mut(&array_arg, ctx)?;
        if self.front {
            array.push_front(value);
        } else {
            array.push_back(value);
        }
        cont(Value::unit())
    }

    fn argument_passing(&self) -> Option<&'static [ArgPassing]> {
        Some(&[
            ArgPassing::SharedRef,
            ArgPassing::MutableRef,
            ArgPassing::SharedRef,
        ])
    }

    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        _locals: &[LocalDecl],
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        write!(f, "{indent_str}ArrayAppendFunction")
    }
}

#[derive(Debug, Clone, Copy)]
struct ArrayConcatFunction;

impl Callable for ArrayConcatFunction {
    fn call(
        &self,
        args: Vec<ValOrMut>,
        ctx: &mut EvalCtx,
        _locals: &[LocalDecl],
    ) -> EvalControlFlowResult {
        let mut args = args.into_iter();
        let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
        let left = args.next().unwrap();
        let right = args.next().unwrap();
        let mut output = VecDeque::new();
        clone_array_range_into(ctx, &dictionary, left, 0, usize::MAX, &mut output)?;
        clone_array_range_into(ctx, &dictionary, right, 0, usize::MAX, &mut output)?;
        cont(Value::native(Array::from_deque(output)))
    }

    fn argument_passing(&self) -> Option<&'static [ArgPassing]> {
        Some(&[
            ArgPassing::SharedRef,
            ArgPassing::SharedRef,
            ArgPassing::SharedRef,
        ])
    }

    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        _locals: &[LocalDecl],
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        write!(f, "{indent_str}ArrayConcatFunction")
    }
}

#[derive(Debug, Clone, Copy)]
struct ArraySliceFunction;

impl Callable for ArraySliceFunction {
    fn call(
        &self,
        args: Vec<ValOrMut>,
        ctx: &mut EvalCtx,
        _locals: &[LocalDecl],
    ) -> EvalControlFlowResult {
        let mut args = args.into_iter();
        let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
        let array = args.next().unwrap();
        let start = args
            .next()
            .unwrap()
            .into_primitive::<isize>()
            .expect("array slice start index should be an int");
        let end = args
            .next()
            .unwrap()
            .into_primitive::<isize>()
            .expect("array slice end index should be an int");
        let source = ArraySource::new(array, ctx)?;
        let outcome = (|| {
            let len = source.len(ctx)?;
            let start = signed_index_for_len(len, start).min(len);
            let end = signed_index_for_len(len, end).min(len);
            let mut output = VecDeque::new();
            if end > start {
                for index in start..end {
                    let value = call_value_clone_for_temp(
                        ctx,
                        &dictionary,
                        source.element(index),
                        Location::new_synthesized(),
                    )?;
                    output.push_back(value);
                }
            }
            Ok(Value::native(Array::from_deque(output)))
        })();
        source.finish(ctx);
        cont(outcome?)
    }

    fn argument_passing(&self) -> Option<&'static [ArgPassing]> {
        Some(&[
            ArgPassing::SharedRef,
            ArgPassing::SharedRef,
            ArgPassing::OwnedValue,
            ArgPassing::OwnedValue,
        ])
    }

    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        _locals: &[LocalDecl],
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        write!(f, "{indent_str}ArraySliceFunction")
    }
}

#[derive(Debug, Clone, Copy)]
struct ArrayCloneFunction;

impl Callable for ArrayCloneFunction {
    fn call(
        &self,
        args: Vec<ValOrMut>,
        ctx: &mut EvalCtx,
        _locals: &[LocalDecl],
    ) -> EvalControlFlowResult {
        let mut args = args.into_iter();
        let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
        let source = args.next().unwrap();
        let target = args.next().unwrap().as_place().clone();
        let mut output = VecDeque::new();
        clone_array_range_into(ctx, &dictionary, source, 0, usize::MAX, &mut output)?;
        *target.target_mut(ctx).map_err(RuntimeError::new_native)? =
            Value::native(Array::from_deque(output));
        cont(Value::unit())
    }

    fn argument_passing(&self) -> Option<&'static [ArgPassing]> {
        Some(&[
            ArgPassing::SharedRef,
            ArgPassing::SharedRef,
            ArgPassing::MutableRef,
        ])
    }

    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        _locals: &[LocalDecl],
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        write!(f, "{indent_str}ArrayCloneFunction")
    }
}

#[derive(Debug, Clone, Copy)]
struct ArrayDropFunction;

impl Callable for ArrayDropFunction {
    fn call(
        &self,
        args: Vec<ValOrMut>,
        ctx: &mut EvalCtx,
        _locals: &[LocalDecl],
    ) -> EvalControlFlowResult {
        let mut args = args.into_iter();
        let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
        let target = args.next().unwrap().as_place().clone();
        loop {
            let value = {
                let target_value = target.target_mut(ctx).map_err(RuntimeError::new_native)?;
                let array = target_value.as_primitive_ty_mut::<Array>().unwrap();
                array.pop_back_raw()
            };
            let Some(value) = value else {
                break;
            };
            call_value_drop_for_temp(
                ctx,
                &dictionary,
                ValOrMut::Val(value),
                Location::new_synthesized(),
            )?;
        }
        cont(Value::unit())
    }

    fn argument_passing(&self) -> Option<&'static [ArgPassing]> {
        Some(&[ArgPassing::SharedRef, ArgPassing::MutableRef])
    }

    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        _locals: &[LocalDecl],
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        write!(f, "{indent_str}ArrayDropFunction")
    }
}

impl Default for Array {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeDisplay for Array {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        write_with_separator_and_format_fn(self.0.iter(), ", ", Value::format_as_string_repr, f)?;
        write!(f, "]")
    }
    fn fmt_pretty(&self, f: &mut fmt::Formatter, ty: &NativeType) -> fmt::Result {
        write!(f, "[")?;
        let inner_ty = ty.arguments[0];
        write_with_separator(
            self.0.iter().map(|item| item.display_pretty(&inner_ty)),
            ", ",
            f,
        )?;
        write!(f, "]")
    }
}

impl<V: NativeValue + 'static> FromIterator<V> for Array {
    fn from_iter<T: IntoIterator<Item = V>>(iter: T) -> Self {
        Self::from_vec(iter.into_iter().map(Value::native).collect())
    }
}

pub fn array_type(element_ty: Type) -> Type {
    Type::native::<Array>([element_ty])
}

pub fn int_array_type() -> Type {
    cached_ty!(|| array_type(int_type()))
}

pub fn array_type_generic() -> Type {
    cached_ty!(|| array_type(Type::variable_id(0)))
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.add_bare_native_type_alias_str("array", bare_native_type::<Array>());

    // TODO: use type classes to get rid of the array prefix
    // to.add_local_function(ustr("array_from_iterator"), Array::from_iterator_descr());
    to.add_function(ustr("array_append"), Array::append_descr());
    to.add_function(ustr("array_prepend"), Array::prepend_descr());
    to.add_function(ustr("array_pop_back"), Array::pop_back_desc());
    to.add_function(ustr("array_pop_front"), Array::pop_front_desc());
    to.add_function(ustr("array_len"), Array::len_descr());
    to.add_function(ustr("array_with_capacity"), Array::with_capacity_descr());
    to.add_function(ustr("array_slice"), Array::slice_descr());
    to.add_function(ustr("array_concat"), Array::concat_descr());
    to.add_function(ustr("array_value_clone"), Array::value_clone_descr());
    to.add_function(ustr("array_value_drop"), Array::value_drop_descr());
    to.add_native_blanket_impl(
        DEFAULT_TRAIT.clone(),
        BlanketTraitImplSubKey {
            input_tys: vec![array_type_generic()],
            ty_var_count: 1,
            constraints: vec![],
        },
        [],
        [Box::new(NullaryNativeFnN::new(Array::new)) as Function],
    );
    to.add_native_blanket_impl(
        EMPTY_TRAIT.clone(),
        BlanketTraitImplSubKey {
            input_tys: vec![array_type_generic()],
            ty_var_count: 1,
            constraints: vec![],
        },
        [],
        [Box::new(NullaryNativeFnN::new(Array::new)) as Function],
    );
}
