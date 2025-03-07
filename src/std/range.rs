// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::fmt;

use ustr::ustr;

use crate::{
    effects::no_effects, function::BinaryNativeFnNNN, module::Module, r#type::Type,
    value::NativeDisplay,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    start: isize,
    end: isize,
}

impl Range {
    pub fn new(start: isize, end: isize) -> Self {
        Self { start, end }
    }

    // pub fn iter(self) -> RangeIterator {
    //     RangeIterator {
    //         range: self,
    //         next: self.start,
    //     }
    // }
}

// impl NativeDisplay for Range {
//     fn native_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(f, "{}‥{}", self.start, self.end)
//     }
// }

// pub fn range_type() -> Type {
//     Type::native::<Range>(vec![])
// }

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
    fn fmt_as_literal(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} in {}‥{}",
            self.next, self.range.start, self.range.end
        )
    }
}

pub fn range_iterator_type() -> Type {
    Type::native::<RangeIterator>(vec![])
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.types.set("range_iterator", range_iterator_type());

    // Functions
    to.functions.insert(
        ustr("range_iterator_new"),
        BinaryNativeFnNNN::description_with_default_ty(
            RangeIterator::new,
            ["start", "end"],
            None,
            no_effects(),
        ),
    );
}
