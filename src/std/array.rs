// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{collections::VecDeque, fmt, rc::Rc};

use itertools::process_results;
use ustr::ustr;

use crate::{
    cached_ty,
    effects::{no_effects, EffType},
    error::RuntimeError,
    eval::{EvalCtx, ValOrMut},
    format::write_with_separator,
    function::{
        BinaryNativeFnMVN, BinaryNativeFnNNN, BinaryNativeFnNVFN, UnaryNativeFnMV, UnaryNativeFnNN,
    },
    module::{Module, ModuleFunction},
    r#type::{bare_native_type, FnType, Type},
    type_scheme::TypeScheme,
    value::{NativeDisplay, NativeValue, Value},
};

use super::{
    logic::bool_type,
    math::int_type,
    option::{none, option_type_generic, some},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Array(Rc<VecDeque<Value>>);

impl Array {
    pub fn new() -> Self {
        Self(Rc::new(VecDeque::new()))
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

    pub fn append(&mut self, value: Value) {
        Rc::make_mut(&mut self.0).push_back(value);
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
            &[(array, true), (gen0, false)],
            unit,
            no_effects(),
        ));
        BinaryNativeFnMVN::description_with_ty_scheme(
            Self::append,
            ["array", "value"],
            None,
            ty_scheme,
        )
    }

    pub fn prepend(&mut self, value: Value) {
        Rc::make_mut(&mut self.0).push_front(value);
    }

    fn prepend_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let unit = Type::unit();
        let array = array_type_generic();
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            &[(array, true), (gen0, false)],
            unit,
            no_effects(),
        ));
        BinaryNativeFnMVN::description_with_ty_scheme(
            Self::prepend,
            ["array", "value"],
            None,
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
            &[array],
            int_type(),
            no_effects(),
        ));
        UnaryNativeFnNN::description_with_ty_scheme(
            |a: Self| a.len() as isize,
            ["array"],
            None,
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
            &[(array_ty, false), (array_ty, false)],
            array_ty,
            no_effects(),
        ));
        BinaryNativeFnNNN::description_with_ty_scheme(
            |a: Self, b: Self| Self::concat(&a, &b),
            ["left", "right"],
            None,
            ty_scheme,
        )
    }

    pub fn map(self, f: Value) -> Result<Self, RuntimeError> {
        let function = f.as_function().unwrap().0.get();
        let mut ctx = EvalCtx::new();
        Ok(Self(Rc::new(
            self.0
                .iter()
                .map(|v| {
                    function
                        .borrow()
                        .call(vec![ValOrMut::Val(v.clone())], &mut ctx)
                })
                .collect::<Result<_, _>>()?,
        )))
    }

    fn map_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let gen1 = Type::variable_id(1);
        let effects = EffType::single_variable_id(0);
        let map_fn = Type::function_by_val_with_effects(&[gen0], gen1, effects.clone());
        let array0 = Type::native::<Self>(vec![gen0]);
        let array1 = Type::native::<Self>(vec![gen1]);
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
            &[array0, map_fn],
            array1,
            effects,
        ));
        BinaryNativeFnNVFN::description_with_ty_scheme(
            Self::map,
            ["array", "function"],
            None,
            ty_scheme,
        )
    }

    pub fn any(self, f: Value) -> Result<bool, RuntimeError> {
        let function = f.as_function().unwrap().0.get();
        let mut ctx = EvalCtx::new();
        process_results(
            self.0.iter().map(|v| {
                Ok(function
                    .borrow()
                    .call(vec![ValOrMut::Val(v.clone())], &mut ctx)?
                    .into_primitive_ty::<bool>()
                    .unwrap())
            }),
            |mut iter| iter.any(|matches| matches),
        )
    }

    fn any_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let effects = EffType::single_variable_id(0);
        let any_fn = Type::function_by_val_with_effects(&[gen0], bool_type(), effects.clone());
        let array = Type::native::<Self>(vec![gen0]);
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
            &[array, any_fn],
            bool_type(),
            effects,
        ));
        BinaryNativeFnNVFN::description_with_ty_scheme(
            Self::any,
            ["array", "predicate"],
            None,
            ty_scheme,
        )
    }

    pub fn all(self, f: Value) -> Result<bool, RuntimeError> {
        let function = f.as_function().unwrap().0.get();
        let mut ctx = EvalCtx::new();
        process_results(
            self.0.iter().map(|v| {
                Ok(function
                    .borrow()
                    .call(vec![ValOrMut::Val(v.clone())], &mut ctx)?
                    .into_primitive_ty::<bool>()
                    .unwrap())
            }),
            |mut iter| iter.all(|matches| matches),
        )
    }

    fn all_descr() -> ModuleFunction {
        let gen0 = Type::variable_id(0);
        let effects = EffType::single_variable_id(0);
        let all_fn = Type::function_by_val_with_effects(&[gen0], bool_type(), effects.clone());
        let array = Type::native::<Self>(vec![gen0]);
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_by_val(
            &[array, all_fn],
            bool_type(),
            effects,
        ));
        BinaryNativeFnNVFN::description_with_ty_scheme(
            Self::all,
            ["array", "predicate"],
            None,
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
            &[array],
            array_iter_type_generic(),
            no_effects(),
        ));
        UnaryNativeFnNN::description_with_ty_scheme(|a: Self| a.iter(), ["array"], None, ty_scheme)
    }
}

impl Default for Array {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeDisplay for Array {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        write_with_separator(self.0.iter(), ", ", f)?;
        write!(f, "]")
    }
}

impl<V: NativeValue + 'static> FromIterator<V> for Array {
    fn from_iter<T: IntoIterator<Item = V>>(iter: T) -> Self {
        Self::from_vec(iter.into_iter().map(Value::native).collect())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
            &[(array_iter_type_generic(), true)],
            option_type_generic(),
            no_effects(),
        ));
        UnaryNativeFnMV::description_with_ty_scheme(Self::next_value, ["iterator"], None, ty_scheme)
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
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ArrayIterator on [")?;
        write_with_separator(self.array.iter(), ", ", f)?;
        write!(f, "] @ {}", self.index)
    }
}

pub fn array_type(element_ty: Type) -> Type {
    Type::native::<Array>(vec![element_ty])
}

pub fn int_array_type() -> Type {
    cached_ty!(|| array_type(int_type()))
}

pub fn array_type_generic() -> Type {
    cached_ty!(|| array_type(Type::variable_id(0)))
}

pub fn array_iter_type(element_ty: Type) -> Type {
    Type::native::<ArrayIterator>(vec![element_ty])
}

pub fn array_iter_type_generic() -> Type {
    cached_ty!(|| array_iter_type(Type::variable_id(0)))
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.types
        .set_bare_native("array", bare_native_type::<Array>());
    to.types
        .set_bare_native("array_iterator", bare_native_type::<ArrayIterator>());

    // TODO: use type classes to get rid of the array prefix
    // to.functions
    //     .insert(ustr("array_from_iterator"), Array::from_iterator_descr());
    to.functions
        .insert(ustr("array_append"), Array::append_descr());
    to.functions
        .insert(ustr("array_prepend"), Array::prepend_descr());
    to.functions.insert(ustr("array_len"), Array::len_descr());
    to.functions
        .insert(ustr("array_concat"), Array::concat_descr());
    to.functions.insert(ustr("array_map"), Array::map_descr());
    to.functions.insert(ustr("array_any"), Array::any_descr());
    to.functions.insert(ustr("array_all"), Array::all_descr());
    to.functions.insert(ustr("array_iter"), Array::iter_descr());

    to.functions.insert(
        ustr("array_iterator_next"),
        ArrayIterator::next_value_descr(),
    );
}
