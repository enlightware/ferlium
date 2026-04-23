// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::fmt;

use crate::{
    cached_primitive_ty,
    containers::b,
    effects::no_effects,
    function::{
        BinaryNativeFnMNN, BinaryNativeFnNMN, BinaryNativeFnNNN, Function, NullaryNativeFnN,
        UnaryNativeFnNN,
    },
    module::Module,
    std::{
        cast::CAST_TRAIT,
        math::int_type,
        string::String,
        value::{VALUE_TRAIT, equal},
    },
    r#type::Type,
    value::NativeDisplay,
};
use ustr::ustr;

/// A hash value
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HashValue(u64);

impl NativeDisplay for HashValue {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "hash({})", self.0)
    }
}

pub fn hash_type() -> Type {
    cached_primitive_ty!(HashValue)
}

/// A non-cryptographic hasher
#[derive(Debug, Clone, Copy)]
pub struct Hasher {
    state: u64,
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

impl Hasher {
    /// Fixed non-zero seed.
    const INIT: u64 = 0x6e62_4eb7_a3c9_b5c1;

    pub fn new() -> Self {
        Self { state: Self::INIT }
    }

    pub fn finish(self) -> HashValue {
        HashValue(final_mix(self.state))
    }

    pub fn write_isize(&mut self, x: isize) {
        self.write_u64(x as u64);
    }

    pub fn write_u64(&mut self, x: u64) {
        self.state = mix_word(self.state, x);
    }

    pub fn write_bool(&mut self, b: bool) {
        self.write_u64(if b { 1 } else { 0 });
    }

    pub fn write_u8(&mut self, x: u8) {
        self.write_u64(x as u64);
    }

    pub fn write_bytes(&mut self, bytes: &[u8]) {
        self.write_u64(bytes.len() as u64);
        for &b in bytes {
            self.write_u8(b);
        }
    }

    pub fn write_string(&mut self, s: String) {
        self.write_bytes(s.as_ref().as_bytes());
    }

    pub fn write_hash(&mut self, h: HashValue) {
        self.write_u64(h.0);
    }
}

impl NativeDisplay for Hasher {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "hasher {{ state = {} }}", self.state)
    }
}

/// Mix one 64-bit word into the running state.
fn mix_word(state: u64, word: u64) -> u64 {
    // Based on a splitmix64-style avalanche, but used incrementally.
    let x = word.wrapping_add(0x9e37_79b9_7f4a_7c15).rotate_left(17);

    let mut s = state ^ x;
    s = s.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    s ^= s >> 32;
    s = s.wrapping_mul(0x94d0_49bb_1331_11eb);
    s ^= s >> 29;
    s
}

fn final_mix(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^= x >> 31;
    x
}

pub fn hasher_type() -> Type {
    cached_primitive_ty!(Hasher)
}

/// Accumulator for unordered collections.
#[derive(Debug, Clone, Copy)]
struct UnorderedHasher {
    sum: u64,
    xor: u64,
    count: u64,
}

impl UnorderedHasher {
    pub fn new() -> Self {
        Self {
            sum: 0,
            xor: 0,
            count: 0,
        }
    }

    pub fn add(&mut self, h: HashValue) {
        self.sum = self.sum.wrapping_add(h.0);
        self.xor ^= h.0;
        self.count = self.count.wrapping_add(1);
    }

    pub fn finish(self) -> HashValue {
        let mut h = Hasher::new();
        h.write_u64(self.sum);
        h.write_u64(self.xor);
        h.write_u64(self.count);
        h.finish()
    }
}

impl NativeDisplay for UnorderedHasher {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "UnorderedHasher {{ sum: {}, xor: {}, count: {} }}",
            self.sum, self.xor, self.count
        )
    }
}

pub fn unordered_hasher_type() -> Type {
    cached_primitive_ty!(UnorderedHasher)
}

fn hash_value_to_string(value: HashValue) -> String {
    String::new(&format!("hash({})", value.0))
}

fn hash_hash_value(value: HashValue, state: &mut Hasher) {
    state.write_hash(value);
}

fn hash_to_int(value: HashValue) -> isize {
    value.0 as isize
}

pub fn add_to_module(to: &mut Module) {
    // Types
    to.add_type_alias_str("hash", hash_type());
    to.add_type_alias_str("hasher", hasher_type());
    to.add_type_alias_str("unordered_hasher", unordered_hasher_type());

    to.add_concrete_impl_no_locals(
        VALUE_TRAIT.clone(),
        [hash_type()],
        [],
        [
            b(BinaryNativeFnNNN::new(equal::<HashValue>)) as Function,
            b(UnaryNativeFnNN::new(hash_value_to_string)) as Function,
            b(BinaryNativeFnNMN::new(hash_hash_value)) as Function,
        ],
    );
    to.add_concrete_impl_no_locals(
        CAST_TRAIT.clone(),
        [hash_type(), int_type()],
        [],
        [b(UnaryNativeFnNN::new(hash_to_int)) as Function],
    );

    // Functions
    to.add_function(
        ustr("hasher_new"),
        NullaryNativeFnN::description_with_default_ty(
            Hasher::new,
            [],
            "Create a new hasher with a fixed non-zero seed.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("hasher_write_int"),
        BinaryNativeFnMNN::description_with_default_ty(
            Hasher::write_isize,
            ["hasher", "value"],
            "Write an integer value into a hasher.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("hasher_write_hash"),
        BinaryNativeFnMNN::description_with_default_ty(
            Hasher::write_hash,
            ["hasher", "hash"],
            "Write a hash value into a hasher.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("hasher_write_string"),
        BinaryNativeFnMNN::description_with_default_ty(
            Hasher::write_string,
            ["hasher", "value"],
            "Write a string value into a hasher.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("hasher_finish"),
        UnaryNativeFnNN::description_with_default_ty(
            Hasher::finish,
            ["hasher"],
            "Finish a hasher and produce the final hash value.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("unordered_hasher_new"),
        NullaryNativeFnN::description_with_default_ty(
            UnorderedHasher::new,
            [],
            "Create an empty unordered hash accumulator with no elements added yet.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("unordered_hasher_add"),
        BinaryNativeFnMNN::description_with_default_ty(
            UnorderedHasher::add,
            ["acc", "hash"],
            "Add a hash value to an unordered hash accumulator.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("unordered_hasher_finish"),
        UnaryNativeFnNN::description_with_default_ty(
            UnorderedHasher::finish,
            ["acc"],
            "Finish an unordered hash accumulator and produce the final hash value.",
            no_effects(),
        ),
    );
}
