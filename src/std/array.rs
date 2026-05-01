// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{collections::VecDeque, fmt, rc::Rc};

use ustr::ustr;

use crate::{
    cached_ty,
    format::{write_with_separator, write_with_separator_and_format_fn},
    hir::function::{
        BinaryNativeFnMVN, BinaryNativeFnRRN, Function, NullaryNativeFnN, TernaryNativeFnRNNN,
        UnaryNativeFnMV, UnaryNativeFnNN, UnaryNativeFnRN,
    },
    hir::value::{NativeDisplay, NativeValue, Value},
    module::{BlanketTraitImplSubKey, Module, ModuleFunction},
    types::effects::no_effects,
    types::r#type::{FnType, NativeType, Type, bare_native_type},
    types::type_scheme::TypeScheme,
};

use super::{
    default::DEFAULT_TRAIT,
    empty::EMPTY_TRAIT,
    math::int_type,
    option::{none, option_type_generic, some},
};

#[derive(Debug, Clone)]
pub struct Array(Rc<VecDeque<Value>>);

impl Array {
    pub fn new() -> Self {
        Self(Rc::new(VecDeque::new()))
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self(Rc::new(VecDeque::with_capacity(capacity)))
    }

    pub fn with_capacity_signed(capacity: isize) -> Self {
        Self::with_capacity(capacity.max(0) as usize)
    }

    pub fn from_vec(values: Vec<Value>) -> Self {
        Self::from_deque(VecDeque::from(values))
    }

    pub fn from_deque(values: VecDeque<Value>) -> Self {
        Self(Rc::new(values))
    }

    // // Manual implementation of a conversion from an iterator function to a new list
    // fn from_value_iterator(mut iter: Value) -> Result<Self, RuntimeError> {
    //     let mut vec = VecDeque::new();
    //     loop {
    //         let iter_fn_key = iter.as_function().unwrap();
    //         let iter_fn = iter_fn_key.0.get();
    //         let mut ctx = EvalCtx::new();
    //         let ret = iter_fn.borrow().call(vec![], &mut ctx)?;
    //         let ret_tuple = *ret.into_tuple().unwrap();
    //         let (in_value, next_iter) = ret_tuple.into_iter().collect_tuple().unwrap();
    //         let option = *in_value.into_variant().unwrap();
    //         if option.tag == "None" {
    //             break;
    //         }
    //         vec.push_back(option.value);
    //         iter = next_iter;
    //     }
    //     Ok(Array(Rc::new(vec)))
    // }

    // fn from_iterator_descr() -> ModuleFunction {
    //     let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
    //         &[iterator_type()],
    //         array_type_generic(),
    //         no_effects(),
    //     ));
    //     UnaryNativeFnVFN::description_with_ty_scheme(
    //         Array::from_value_iterator,
    //         ["iterator"],
    //         None,
    //         ty_scheme,
    //     )
    // }

    pub fn get(&self, index: usize) -> Option<&Value> {
        self.0.get(index)
    }

    pub fn get_signed(&self, index: isize) -> Option<&Value> {
        self.get(self.to_unsigned_index(index))
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut Value> {
        Rc::make_mut(&mut self.0).get_mut(index)
    }

    pub fn get_mut_signed(&mut self, index: isize) -> Option<&mut Value> {
        self.get_mut(self.to_unsigned_index(index))
    }

    pub fn append(&mut self, value: &Value) {
        Rc::make_mut(&mut self.0).push_back(value.clone());
    }

    fn to_unsigned_index(&self, index: isize) -> usize {
        if index < 0 {
            (self.len() as isize + index) as usize
        } else {
            index as usize
        }
    }

    fn append_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let unit = Type::unit();
        let array = array_type_generic();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            [(array, true), (gen0, false)],
            unit,
            no_effects(),
        ));
        BinaryNativeFnMVN::description_with_ty_scheme(
            Self::append,
            ["array", "value"],
            "Appends an element to the back of the array.",
            ty_scheme,
        )
    }

    pub fn prepend(&mut self, value: &Value) {
        Rc::make_mut(&mut self.0).push_front(value.clone());
    }

    fn prepend_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let unit = Type::unit();
        let array = array_type_generic();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            [(array, true), (gen0, false)],
            unit,
            no_effects(),
        ));
        BinaryNativeFnMVN::description_with_ty_scheme(
            Self::prepend,
            ["array", "value"],
            "Prepends an element to the front of the array.",
            ty_scheme,
        )
    }

    pub fn pop_back(&mut self) -> Value {
        let value = Rc::make_mut(&mut self.0).pop_back();
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
        let value = Rc::make_mut(&mut self.0).pop_front();
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

    fn concat(a: &Self, b: &Self) -> Self {
        let mut new = (*a.0).clone();
        new.extend(b.0.iter().cloned());
        Self::from_deque(new)
    }

    fn concat_descr() -> ModuleFunction {
        let array_ty = array_type_generic();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            [(array_ty, false), (array_ty, false)],
            array_ty,
            no_effects(),
        ));
        BinaryNativeFnRRN::description_with_ty_scheme(
            Self::concat,
            ["left", "right"],
            "Concatenates two arrays and returns the result.",
            ty_scheme,
        )
    }

    pub fn iter(&self) -> ArrayIterator {
        ArrayIterator {
            array: self.0.clone(),
            index: 0,
        }
    }

    fn iter_descr() -> ModuleFunction {
        let array = array_type_generic();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
            [array],
            array_iter_type_generic(),
            no_effects(),
        ));
        UnaryNativeFnRN::description_with_ty_scheme(
            Self::iter,
            ["array"],
            "Creates an iterator over the array.",
            ty_scheme,
        )
    }

    pub fn slice(&self, start: isize, end: isize) -> Self {
        let len = self.len();
        let start = self.to_unsigned_index(start).min(len);
        let end = self.to_unsigned_index(end).min(len);

        self.slice_range(start, end)
    }

    fn slice_range(&self, start: usize, end: usize) -> Self {
        if end <= start {
            Self::default()
        } else {
            Self::from_deque(self.0.range(start..end).cloned().collect())
        }
    }

    fn slice_descr() -> ModuleFunction {
        let array = array_type_generic();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
            [array, int_type(), int_type()],
            array,
            no_effects(),
        ));
        TernaryNativeFnRNNN::description_with_ty_scheme(
            Self::slice,
            ["array", "start", "end"],
            "Returns the slice of `array` from index `start` to index `end`. Negative indices count from the end.",
            ty_scheme,
        )
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

#[derive(Debug, Clone)]
pub struct ArrayIterator {
    array: Rc<VecDeque<Value>>,
    index: usize,
}

impl ArrayIterator {
    pub fn next_value(&mut self) -> Value {
        match self.next() {
            Some(value) => some(value),
            None => none(),
        }
    }

    fn next_value_descr() -> ModuleFunction {
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            [(array_iter_type_generic(), true)],
            option_type_generic(),
            no_effects(),
        ));
        UnaryNativeFnMV::description_with_ty_scheme(
            Self::next_value,
            ["iterator"],
            "Gets the next value of the array.",
            ty_scheme,
        )
    }
}

impl Iterator for ArrayIterator {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.array.len() {
            let item = &self.array[self.index];
            self.index += 1;
            Some(item.clone())
        } else {
            None
        }
    }
}

impl NativeDisplay for ArrayIterator {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ArrayIterator on [")?;
        write_with_separator_and_format_fn(
            self.array.iter(),
            ", ",
            Value::format_as_string_repr,
            f,
        )?;
        write!(f, "] @ {}", self.index)
    }
    fn fmt_pretty(&self, f: &mut fmt::Formatter, ty: &NativeType) -> fmt::Result {
        write!(f, "ArrayIterator on [")?;
        let inner_ty = ty.arguments[0];
        write_with_separator(
            self.array.iter().map(|item| item.display_pretty(&inner_ty)),
            ", ",
            f,
        )?;
        write!(f, "] @ {}", self.index)
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

pub fn array_iter_type(element_ty: Type) -> Type {
    Type::native::<ArrayIterator>([element_ty])
}

pub fn array_iter_type_generic() -> Type {
    cached_ty!(|| array_iter_type(Type::variable_id(0)))
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.add_bare_native_type_alias_str("array", bare_native_type::<Array>());
    to.add_bare_native_type_alias_str("array_iterator", bare_native_type::<ArrayIterator>());

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
    to.add_function(ustr("array_iter"), Array::iter_descr());
    to.add_blanket_impl_no_locals(
        DEFAULT_TRAIT.clone(),
        BlanketTraitImplSubKey {
            input_tys: vec![array_type_generic()],
            ty_var_count: 1,
            constraints: vec![],
        },
        [],
        [Box::new(NullaryNativeFnN::new(Array::new)) as Function],
    );
    to.add_blanket_impl_no_locals(
        EMPTY_TRAIT.clone(),
        BlanketTraitImplSubKey {
            input_tys: vec![array_type_generic()],
            ty_var_count: 1,
            constraints: vec![],
        },
        [],
        [Box::new(NullaryNativeFnN::new(Array::new)) as Function],
    );

    to.add_function(
        ustr("array_iterator_next"),
        ArrayIterator::next_value_descr(),
    );
}
