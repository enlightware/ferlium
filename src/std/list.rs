use itertools::Itertools;
use smallvec::smallvec;
use std::{collections::VecDeque, rc::Rc};
use ustr::ustr;

use crate::{
    function::{BinaryPartialNativeFn, FunctionDescription, NullaryNativeFn, UnaryNativeFn},
    r#type::{FunctionType, Type},
    value::Value,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct List(Rc<VecDeque<Value>>);

impl List {
    fn new() -> Self {
        List(Rc::new(VecDeque::new()))
    }

    // Manual implementation of a conversion from an iterator function to a new list
    fn from_iterator(mut iter: Value) -> Self {
        let mut vec = VecDeque::new();
        loop {
            let iter_fn_key = iter.as_function().unwrap();
            let iter_fn = iter_fn_key.get();
            let ret = iter_fn.code.call(vec![], &());
            let ret_tuple = *ret.into_tuple().unwrap();
            let (in_value, next_iter) = ret_tuple.into_iter().collect_tuple().unwrap();
            let option = *in_value.into_variant().unwrap();
            if option.tag == "None" {
                break;
            }
            vec.push_back(option.value);
            iter = next_iter;
        }
        List(Rc::new(vec))
    }

    // FIXME: this is very inefficient because we clone the whole list
    // although we might not modify the other one. A smarter copy-on-write
    // would be helpful.
    // see: https://github.com/orium/rpds
    pub fn append(mut self, value: Value) -> Self {
        Rc::make_mut(&mut self.0).push_back(value);
        self
    }

    pub fn prepend(mut self, value: Value) -> Self {
        Rc::make_mut(&mut self.0).push_front(value);
        self
    }

    fn len(self) -> isize {
        self.0.len() as isize
    }

    // TODO: how to make this into an iterator

    fn map(self, f: Value) -> Self {
        let function = f.as_function().unwrap().get();
        Self(Rc::new(
            self.0
                .iter()
                .map(|v| function.code.call(vec![v.clone()], &()))
                .collect(),
        ))
    }
}

impl Default for List {
    fn default() -> Self {
        Self::new()
    }
}

pub struct ListModule {
    pub new: Rc<FunctionDescription>,
    pub from_iterator: Rc<FunctionDescription>,
    pub append: Rc<FunctionDescription>,
    pub prepend: Rc<FunctionDescription>,
    pub len: Rc<FunctionDescription>,
    pub map: Rc<FunctionDescription>,
}

impl ListModule {
    // TODO: insert these functions to some name table
    pub fn new_mod() -> Self {
        let gen0 = Type::generic_variable(0);
        let gen1 = Type::generic_variable(1);
        let unit = Type::unit();
        let list = Type::generic_native::<List>(smallvec![gen0]);
        let int = Type::primitive::<isize>();
        let new = Rc::new(FunctionDescription {
            ty: FunctionType::new(&[], list),
            code: Box::new(NullaryNativeFn::new(List::new)),
        });
        // TODO: move this in a common place
        let empty_tuple = Type::tuple(vec![]);
        let option = Type::variant(vec![(ustr("None"), empty_tuple), (ustr("Some"), gen0)]);
        let iterator_gen0 = Type::function(&[], Type::tuple(vec![option, Type::new_local(0)]));
        let from_iterator = Rc::new(FunctionDescription {
            ty: FunctionType::new(&[iterator_gen0], list),
            code: Box::new(UnaryNativeFn::new(List::from_iterator)),
        });
        let append = Rc::new(FunctionDescription {
            ty: FunctionType::new(&[list, gen0], unit),
            code: Box::new(BinaryPartialNativeFn::new(List::append)),
        });
        let prepend = Rc::new(FunctionDescription {
            ty: FunctionType::new(&[list, gen0], unit),
            code: Box::new(BinaryPartialNativeFn::new(List::prepend)),
        });
        let len = Rc::new(FunctionDescription {
            ty: FunctionType::new(&[list], int),
            code: Box::new(UnaryNativeFn::new(List::len)),
        });
        let map_fn = Type::function(&[gen0], gen1);
        let list1 = Type::generic_native::<List>(smallvec![gen1]);
        let map = Rc::new(FunctionDescription {
            ty: FunctionType::new(&[list, map_fn], list1),
            code: Box::new(BinaryPartialNativeFn::new(List::map)),
        });
        ListModule {
            new,
            from_iterator,
            append,
            prepend,
            len,
            map,
        }
    }
}
