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
    eval::{EvalControlFlowResult, EvalCtx, Place, RuntimeError, ValOrMutArgs, cont},
    format::{write_with_separator, write_with_separator_and_format_fn},
    hir::function::{
        ArgPassing, Callable, ContextNativeFn, Function, FunctionDefinition, NullaryNativeFnN,
        UnaryNativeFnMN, UnaryNativeFnMV, UnaryNativeFnNN, UnaryNativeFnRN,
    },
    hir::value::{NativeDisplay, NativeValue, Value},
    module::{BlanketTraitImplSubKey, Module, ModuleEnv, ModuleFunction},
    types::effects::no_effects,
    types::r#type::{FnType, NativeType, Type, bare_native_type},
    types::type_scheme::{PubTypeConstraint, TypeScheme},
};

use super::{
    default::DEFAULT_TRAIT,
    empty::EMPTY_TRAIT,
    math::int_type,
    option::{none, option_type_generic, some},
    ptr::{self, MutPtr, Ptr, mut_ptr_type, ptr_type},
};

#[derive(Debug)]
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

    fn element_ptr_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        native_function(
            FnType::new_by_val([array_type(gen0), int_type()], ptr_type(gen0), no_effects()),
            [],
            ["array", "index"],
            "Returns a std-only pointer to an array element.",
            ContextNativeFn::new(
                "array_element_ptr",
                &[ArgPassing::SharedRef, ArgPassing::OwnedValue],
                array_element_ptr,
            ),
        )
    }

    fn element_mut_ptr_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        native_function(
            FnType::new_mut_resolved(
                [(array_type(gen0), true), (int_type(), false)],
                mut_ptr_type(gen0),
                no_effects(),
            ),
            [],
            ["array", "index"],
            "Returns a std-only mutable pointer to an array element.",
            ContextNativeFn::new(
                "array_element_mut_ptr",
                &[ArgPassing::MutableRef, ArgPassing::OwnedValue],
                array_element_mut_ptr,
            ),
        )
    }

    fn push_uninit_back_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        native_function(
            FnType::new_mut_resolved([(array_type(gen0), true)], mut_ptr_type(gen0), no_effects()),
            [],
            ["array"],
            "Appends uninitialized storage and returns a std-only mutable pointer to it.",
            ContextNativeFn::new(
                "array_push_uninit_back",
                &[ArgPassing::MutableRef],
                array_push_uninit_back,
            ),
        )
    }

    fn push_uninit_front_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        native_function(
            FnType::new_mut_resolved([(array_type(gen0), true)], mut_ptr_type(gen0), no_effects()),
            [],
            ["array"],
            "Prepends uninitialized storage and returns a std-only mutable pointer to it.",
            ContextNativeFn::new(
                "array_push_uninit_front",
                &[ArgPassing::MutableRef],
                array_push_uninit_front,
            ),
        )
    }

    fn pop_back_uninit_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            [(array_type(gen0), true)],
            Type::unit(),
            no_effects(),
        ));
        UnaryNativeFnMN::description_with_ty_scheme(
            array_pop_back_uninit,
            ["array"],
            "Removes the last array slot without running element drop.",
            ty_scheme,
        )
    }
}

fn native_function(
    ty: FnType,
    constraints: impl Into<Vec<PubTypeConstraint>>,
    arg_names: impl IntoIterator<Item = &'static str>,
    doc: &'static str,
    code: impl Callable + Clone + 'static,
) -> ModuleFunction {
    ModuleFunction {
        definition: FunctionDefinition::new(
            TypeScheme::new_infer_quantifiers_with_constraints(ty, constraints.into()),
            arg_names.into_iter().map(ustr::Ustr::from).collect(),
            Some(String::from(doc)),
        ),
        code: Box::new(code),
        spans: None,
        locals: Vec::new(),
    }
}

fn array_len_from_place(
    place: &Place,
    ctx: &EvalCtx<'_>,
    span: Location,
) -> Result<usize, RuntimeError> {
    let value = place
        .target_ref(ctx)
        .map_err(|err| RuntimeError::new(err, Some(span)))?;
    Ok(value.as_primitive_ty::<Array>().unwrap().len())
}

fn array_element_ptr(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let mut place = ptr::place_from_arg(args.next().unwrap())?;
    let index = args
        .next()
        .unwrap()
        .into_primitive::<isize>()
        .expect("array pointer index should be an int");
    let len = array_len_from_place(&place, ctx, Location::new_synthesized())?;
    if place
        .target_ref(ctx)
        .map_err(RuntimeError::new_native)?
        .as_primitive_ty::<Array>()
        .unwrap()
        .get_signed(index)
        .is_none()
    {
        return Err(RuntimeError::new_native(
            RuntimeErrorKind::ArrayAccessOutOfBounds { index, len },
        ));
    }
    place.path.push(index);
    cont(Value::native(Ptr::new(place)))
}

fn array_element_mut_ptr(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let mut place = ptr::place_from_arg(args.next().unwrap())?;
    let index = args
        .next()
        .unwrap()
        .into_primitive::<isize>()
        .expect("array mutable pointer index should be an int");
    let len = array_len_from_place(&place, ctx, Location::new_synthesized())?;
    if place
        .target_ref(ctx)
        .map_err(RuntimeError::new_native)?
        .as_primitive_ty::<Array>()
        .unwrap()
        .get_signed(index)
        .is_none()
    {
        return Err(RuntimeError::new_native(
            RuntimeErrorKind::ArrayAccessOutOfBounds { index, len },
        ));
    }
    place.path.push(index);
    cont(Value::native(MutPtr::new(place)))
}

fn array_push_uninit_back(args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    array_push_uninit(args, ctx, false)
}

fn array_push_uninit_front(args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    array_push_uninit(args, ctx, true)
}

fn array_push_uninit(
    mut args: ValOrMutArgs,
    ctx: &mut EvalCtx,
    front: bool,
) -> EvalControlFlowResult {
    let mut place = ptr::place_from_arg(args.next().unwrap())?;
    let index = {
        let array = place
            .target_mut(ctx)
            .map_err(RuntimeError::new_native)?
            .as_primitive_ty_mut::<Array>()
            .ok_or_else(|| {
                RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(ustr("array")))
            })?;
        let index = if front { 0 } else { array.len() };
        if front {
            array.push_front(Value::uninit());
        } else {
            array.push_back(Value::uninit());
        }
        index
    };
    place.path.push(index as isize);
    cont(Value::native(MutPtr::new(place)))
}

fn array_pop_back_uninit(array: &mut Array) {
    array.pop_back_raw();
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
    fn fmt_pretty(
        &self,
        f: &mut fmt::Formatter,
        ty: &NativeType,
        env: Option<&ModuleEnv<'_>>,
    ) -> fmt::Result {
        write!(f, "[")?;
        let inner_ty = ty.arguments[0];
        write_with_separator(
            self.0
                .iter()
                .map(|item| item.display_pretty_env(&inner_ty, env)),
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
    to.add_function(ustr("array_pop_back"), Array::pop_back_desc());
    to.add_function(ustr("array_pop_front"), Array::pop_front_desc());
    to.add_function(ustr("array_len"), Array::len_descr());
    to.add_function(ustr("array_with_capacity"), Array::with_capacity_descr());
    to.add_unsafe_function(ustr("array_element_ptr"), Array::element_ptr_descr());
    to.add_unsafe_function(
        ustr("array_element_mut_ptr"),
        Array::element_mut_ptr_descr(),
    );
    to.add_unsafe_function(
        ustr("array_push_uninit_back"),
        Array::push_uninit_back_descr(),
    );
    to.add_unsafe_function(
        ustr("array_push_uninit_front"),
        Array::push_uninit_front_descr(),
    );
    to.add_unsafe_function(
        ustr("array_pop_back_uninit"),
        Array::pop_back_uninit_descr(),
    );
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
