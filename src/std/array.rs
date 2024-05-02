use std::{cell::RefCell, collections::VecDeque, fmt, rc::Rc};

use itertools::Itertools;
use ustr::ustr;

use crate::{
    function::{
        BinaryPartialMutNativeFn, BinaryPartialNativeFn, FunctionDescription, UnaryNativeFn,
    },
    ir::EvalCtx,
    module::Module,
    r#type::{bare_native_type, write_with_separator, FnType, NativeType, Type, TypeOfNativeValue},
    value::{ValOrMut, Value},
};

use super::{iterator::iterator_type, math::int_type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Array(Rc<VecDeque<Value>>);

impl Array {
    pub fn new() -> Self {
        Array(Rc::new(VecDeque::new()))
    }

    pub fn from_vec(values: Vec<Value>) -> Self {
        Array(Rc::new(VecDeque::from(values)))
    }

    // Manual implementation of a conversion from an iterator function to a new list
    fn from_iterator(mut iter: Value) -> Self {
        let mut vec = VecDeque::new();
        loop {
            let iter_fn_key = iter.as_function().unwrap();
            let iter_fn = iter_fn_key.get();
            let mut ctx = EvalCtx::new();
            // FIXME: address runtime error by returning a Result
            let ret = iter_fn.borrow().code.call(vec![], &mut ctx).unwrap();
            let ret_tuple = *ret.into_tuple().unwrap();
            let (in_value, next_iter) = ret_tuple.into_iter().collect_tuple().unwrap();
            let option = *in_value.into_variant().unwrap();
            if option.tag == "None" {
                break;
            }
            vec.push_back(option.value);
            iter = next_iter;
        }
        Array(Rc::new(vec))
    }

    fn from_iterator_descr() -> FunctionDescription {
        FunctionDescription {
            ty: FnType::new_by_val(&[iterator_type()], array_type()),
            code: Box::new(UnaryNativeFn::new(Array::from_iterator)),
        }
    }

    pub fn get(&self, index: usize) -> Option<&Value> {
        self.0.get(index)
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut Value> {
        Rc::make_mut(&mut self.0).get_mut(index)
    }

    pub fn get_mut_signed(&mut self, index: isize) -> Option<&mut Value> {
        let index = if index < 0 {
            (self.len() as isize + index) as usize
        } else {
            index as usize
        };
        self.get_mut(index)
    }

    pub fn append(&mut self, value: Value) {
        Rc::make_mut(&mut self.0).push_back(value);
    }

    fn append_descr() -> FunctionDescription {
        let gen0 = Type::variable_id(0);
        let unit = Type::unit();
        let array = array_type();
        FunctionDescription {
            ty: FnType::new(&[(array, true), (gen0, false)], unit),
            code: Box::new(BinaryPartialMutNativeFn::new(Array::append)),
        }
    }

    pub fn prepend(&mut self, value: Value) {
        Rc::make_mut(&mut self.0).push_front(value);
    }

    fn prepend_descr() -> FunctionDescription {
        let gen0 = Type::variable_id(0);
        let unit = Type::unit();
        let array = array_type();
        FunctionDescription {
            ty: FnType::new(&[(array, true), (gen0, false)], unit),
            code: Box::new(BinaryPartialMutNativeFn::new(Array::prepend)),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    fn len_descr() -> FunctionDescription {
        let array = array_type();
        FunctionDescription {
            ty: FnType::new(&[(array, false)], int_type()),
            code: Box::new(UnaryNativeFn::new(|a: Self| a.len() as isize)),
        }
    }

    // TODO: how to make this into an iterator

    pub fn map(self, f: Value) -> Self {
        let function = f.as_function().unwrap().get();
        let mut ctx = EvalCtx::new();
        Self(Rc::new(
            self.0
                .iter()
                // FIXME: address runtime error by returning a Result<...>
                .map(|v| {
                    function
                        .borrow()
                        .code
                        .call(vec![ValOrMut::Val(v.clone())], &mut ctx)
                        .unwrap()
                })
                .collect(),
        ))
    }

    fn map_descr() -> FunctionDescription {
        let gen0 = Type::variable_id(0);
        let gen1 = Type::variable_id(1);
        let map_fn = Type::function(&[gen0], gen1);
        let array0 = Type::native::<Array>(vec![gen0]);
        let array1 = Type::native::<Array>(vec![gen1]);
        FunctionDescription {
            ty: FnType::new_by_val(&[array0, map_fn], array1),
            code: Box::new(BinaryPartialNativeFn::new(Array::map)),
        }
    }
}

impl Default for Array {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for Array {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let (lhs, rhs) = self.0.as_slices();
        if !lhs.is_empty() {
            write_with_separator(lhs, ", ", f)?;
        }
        if !lhs.is_empty() && !rhs.is_empty() {
            write!(f, ", ")?;
        }
        if !rhs.is_empty() {
            write_with_separator(rhs, ", ", f)?;
        }
        write!(f, "]")
    }
}

impl TypeOfNativeValue for Array {
    fn type_of_value(&self) -> NativeType {
        NativeType::new(
            bare_native_type::<Self>(),
            match self.get(0) {
                Some(value) => vec![value.ty()],
                None => vec![Type::variable_id(0)],
            }
        )
    }
}

pub fn array_type() -> Type {
    Type::native::<Array>(vec![Type::variable_id(0)])
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.types.set(ustr("array"), array_type());

    // TODO: use type classes to get rid of the array prefix
    to.functions.insert(
        ustr("array_from_iterator"),
        Rc::new(RefCell::new(Array::from_iterator_descr())),
    );
    to.functions.insert(
        ustr("array_append"),
        Rc::new(RefCell::new(Array::append_descr())),
    );
    to.functions.insert(
        ustr("array_prepend"),
        Rc::new(RefCell::new(Array::prepend_descr())),
    );
    to.functions
        .insert(ustr("array_len"), Rc::new(RefCell::new(Array::len_descr())));
    to.functions
        .insert(ustr("array_map"), Rc::new(RefCell::new(Array::map_descr())));
}
