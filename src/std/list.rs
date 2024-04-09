use smallvec::smallvec;
use std::{collections::VecDeque, rc::Rc};

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

    fn map(self, f: Value) -> Self {
        let function = f.as_function().unwrap().get();
        Self(Rc::new(self.0.iter().map(|v| {
            function.code.call(vec![v.clone()], &())
        }).collect()))
    }
}

impl Default for List {
    fn default() -> Self {
        Self::new()
    }
}

pub struct ListModule {
    pub new: Rc<FunctionDescription>,
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
        ListModule { new, append, prepend, len, map }
    }
}
