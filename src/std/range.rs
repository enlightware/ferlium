// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::fmt;

use derive_new::new;
use ustr::ustr;

use crate::{
    effects::no_effects,
    function::{BinaryNativeFnNNN, UnaryNativeFnMV, UnaryNativeFnNN},
    module::{Module, ModuleFunction},
    r#type::{FnType, Type},
    type_scheme::TypeScheme,
    value::{NativeDisplay, Value},
};

use super::{
    math::int_type,
    option::{none, option_type, some},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, new)]
pub struct Range {
    start: isize,
    end: isize,
}

impl Range {
    pub fn iter(self) -> RangeIterator {
        RangeIterator {
            range: self,
            next: self.start,
        }
    }

    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    pub fn len(self) -> isize {
        (self.end - self.start).abs()
    }
}

impl NativeDisplay for Range {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}‥{}", self.start, self.end)
    }
}

pub fn range_type() -> Type {
    Type::primitive::<Range>()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RangeIterator {
    range: Range,
    next: isize,
}

impl RangeIterator {
    pub fn new(start: isize, end: isize) -> Self {
        Self {
            range: Range::new(start, end),
            next: start,
        }
    }

    pub fn next_value(&mut self) -> Value {
        match self.next() {
            Some(value) => some(Value::native(value)),
            None => none(),
        }
    }

    fn next_value_descr() -> ModuleFunction {
        let ty_scheme = TypeScheme::new_infer_quantifiers(FnType::new_mut_resolved(
            [(range_iterator_type(), true)],
            option_type(int_type()),
            no_effects(),
        ));
        UnaryNativeFnMV::description_with_ty_scheme(
            Self::next_value,
            ["iterator"],
            Some("Gets the next value within a range."),
            ty_scheme,
        )
    }
}

impl Iterator for RangeIterator {
    type Item = isize;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.next;
        if self.range.end >= self.range.start {
            if self.next < self.range.end {
                self.next += 1;
                Some(next)
            } else {
                None
            }
        } else if self.next > self.range.end {
            self.next -= 1;
            Some(next)
        } else {
            None
        }
    }
}

impl NativeDisplay for RangeIterator {
    fn fmt_repr(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} in {}‥{}",
            self.next, self.range.start, self.range.end
        )
    }
}

pub fn range_iterator_type() -> Type {
    Type::primitive::<RangeIterator>()
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.type_aliases.set("range", range_type());
    to.type_aliases.set("range_iterator", range_iterator_type());

    // Functions
    to.add_named_function(
        ustr("range"),
        BinaryNativeFnNNN::description_with_default_ty(
            Range::new,
            ["start", "end"],
            Some("Creates a range from `start` to `end`."),
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("range_iter"),
        UnaryNativeFnNN::description_with_default_ty(
            Range::iter,
            ["range"],
            Some("Creates an iterator over the range."),
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("range_len"),
        UnaryNativeFnNN::description_with_default_ty(
            Range::len,
            ["range"],
            Some("Returns the length of the range."),
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("range_iterator_new"),
        BinaryNativeFnNNN::description_with_default_ty(
            RangeIterator::new,
            ["start", "end"],
            Some("Creates a new range iterator from `start` to `end`."),
            no_effects(),
        ),
    );
    to.add_named_function(
        ustr("range_iterator_next"),
        RangeIterator::next_value_descr(),
    );
}
