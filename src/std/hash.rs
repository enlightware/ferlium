// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use crate::{
    cached_primitive_ty,
    containers::b,
    hir::function::Function,
    hir::native_functions::{
        NativeFallibleOutFnR, NativeFnMN, NativeFnMR, NativeFnRM, NativeFnRR, NativeOutFn0,
        NativeOutFnR,
    },
    hir::value::NativeValueType,
    module::Module,
    std::{
        core_traits_names::{CAST_TRAIT_NAME, INSPECT_TRAIT_NAME, VALUE_TRAIT_NAME},
        math::int_type,
        string::{StaticStr, String},
        value::{
            native_layout_associated_consts, native_value_clone_function,
            native_value_drop_function,
        },
    },
    types::effects::no_effects,
    types::r#type::Type,
};
use ustr::ustr;

/// A hash value
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HashValue(u64);

impl NativeValueType for HashValue {}

pub fn hash_type() -> Type {
    cached_primitive_ty!(HashValue)
}

/// A non-cryptographic hasher
#[derive(Debug, Clone, Copy)]
pub struct Hasher {
    state: u64,
}

impl NativeValueType for Hasher {}

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

    pub fn finish(&self) -> HashValue {
        HashValue(final_mix(self.state))
    }

    pub extern "C" fn write_isize(&mut self, x: isize) {
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

    pub extern "C" fn write_string(&mut self, s: &String) {
        self.write_bytes(s.as_ref().as_bytes());
    }

    pub(crate) extern "C" fn write_static_str(&mut self, s: &StaticStr) {
        self.write_bytes(s.as_str().as_bytes());
    }

    pub extern "C" fn write_hash(&mut self, h: &HashValue) {
        self.write_u64(h.0);
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
pub(crate) struct UnorderedHasher {
    sum: u64,
    xor: u64,
    count: u64,
}

impl NativeValueType for UnorderedHasher {}

impl UnorderedHasher {
    pub fn new() -> Self {
        Self {
            sum: 0,
            xor: 0,
            count: 0,
        }
    }

    pub extern "C" fn add(&mut self, h: &HashValue) {
        self.sum = self.sum.wrapping_add(h.0);
        self.xor ^= h.0;
        self.count = self.count.wrapping_add(1);
    }

    pub fn finish(&self) -> HashValue {
        let mut h = Hasher::new();
        h.write_u64(self.sum);
        h.write_u64(self.xor);
        h.write_u64(self.count);
        h.finish()
    }
}

pub fn unordered_hasher_type() -> Type {
    cached_primitive_ty!(UnorderedHasher)
}

fn hash_value_to_string(value: &HashValue) -> String {
    String::new(&format!("hash({})", value.0))
}

extern "C" fn hash_hash_value(value: &HashValue, state: &mut Hasher) {
    state.write_hash(value);
}

extern "C" fn equal_hasher(lhs: &Hasher, rhs: &Hasher) -> bool {
    lhs.state == rhs.state
}

fn hasher_to_string(value: &Hasher) -> String {
    String::new(&format!("hasher {{ state = {} }}", value.state))
}

extern "C" fn hash_hasher(value: &Hasher, state: &mut Hasher) {
    state.write_u64(value.state);
}

extern "C" fn equal_unordered_hasher(lhs: &UnorderedHasher, rhs: &UnorderedHasher) -> bool {
    lhs.sum == rhs.sum && lhs.xor == rhs.xor && lhs.count == rhs.count
}

fn unordered_hasher_to_string(value: &UnorderedHasher) -> String {
    String::new(&format!(
        "UnorderedHasher {{ sum: {}, xor: {}, count: {} }}",
        value.sum, value.xor, value.count
    ))
}

extern "C" fn hash_unordered_hasher(value: &UnorderedHasher, state: &mut Hasher) {
    state.write_u64(value.sum);
    state.write_u64(value.xor);
    state.write_u64(value.count);
}

fn hash_to_int(value: &HashValue) -> isize {
    value.0 as isize
}

extern "C" fn equal_hash_value(lhs: &HashValue, rhs: &HashValue) -> bool {
    lhs == rhs
}

pub fn add_to_module(to: &mut Module) {
    let value_trait_id = to.expect_std_trait_id_in_current_module(VALUE_TRAIT_NAME);
    let inspect_trait_id = to.expect_std_trait_id_in_current_module(INSPECT_TRAIT_NAME);
    let cast_trait_id = to.expect_std_trait_id_in_current_module(CAST_TRAIT_NAME);
    // Types
    to.add_type_alias_str_with_doc(
        "hash",
        hash_type(),
        "A hash value produced by the Hash trait.",
    );
    to.add_type_alias_str_with_doc(
        "hasher",
        hasher_type(),
        "A stateful hasher used to combine values into a hash.",
    );
    to.add_type_alias_str_with_doc(
        "unordered_hasher",
        unordered_hasher_type(),
        "A hasher for order-independent hashing.",
    );

    to.add_concrete_impl_no_locals(
        value_trait_id,
        [hash_type()],
        [],
        native_layout_associated_consts::<HashValue>(),
        [
            b(NativeFnRR::new(equal_hash_value)) as Function,
            b(NativeOutFnR::from_rust(hash_value_to_string)) as Function,
            b(NativeFnRM::new(hash_hash_value)) as Function,
            native_value_clone_function::<HashValue>(),
            native_value_drop_function::<HashValue>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [hash_type()],
        [],
        [],
        [b(NativeFallibleOutFnR::from_rust_infallible(
            hash_value_to_string,
        )) as Function],
    );
    to.add_concrete_impl_no_locals(
        value_trait_id,
        [hasher_type()],
        [],
        native_layout_associated_consts::<Hasher>(),
        [
            b(NativeFnRR::new(equal_hasher)) as Function,
            b(NativeOutFnR::from_rust(hasher_to_string)) as Function,
            b(NativeFnRM::new(hash_hasher)) as Function,
            native_value_clone_function::<Hasher>(),
            native_value_drop_function::<Hasher>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [hasher_type()],
        [],
        [],
        [b(NativeFallibleOutFnR::from_rust_infallible(hasher_to_string)) as Function],
    );
    to.add_concrete_impl_no_locals(
        value_trait_id,
        [unordered_hasher_type()],
        [],
        native_layout_associated_consts::<UnorderedHasher>(),
        [
            b(NativeFnRR::new(equal_unordered_hasher)) as Function,
            b(NativeOutFnR::from_rust(unordered_hasher_to_string)) as Function,
            b(NativeFnRM::new(hash_unordered_hasher)) as Function,
            native_value_clone_function::<UnorderedHasher>(),
            native_value_drop_function::<UnorderedHasher>(),
        ],
    );
    to.add_concrete_impl_no_locals(
        inspect_trait_id,
        [unordered_hasher_type()],
        [],
        [],
        [b(NativeFallibleOutFnR::from_rust_infallible(
            unordered_hasher_to_string,
        )) as Function],
    );
    to.add_native_concrete_impl(
        cast_trait_id,
        [hash_type(), int_type()],
        [],
        [b(NativeFallibleOutFnR::from_rust_infallible(hash_to_int)) as Function],
    );

    // Functions
    to.add_function(
        ustr("hasher_new"),
        NativeOutFn0::from_rust(Hasher::new).description(
            [],
            "Create a new hasher with a fixed non-zero seed.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("hasher_write_int"),
        NativeFnMN::new(Hasher::write_isize).description(
            ["hasher", "value"],
            "Write an integer value into a hasher.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("hasher_write_hash"),
        NativeFnMR::new(Hasher::write_hash).description(
            ["hasher", "hash"],
            "Write a hash value into a hasher.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("hasher_write_string"),
        NativeFnMR::new(Hasher::write_string).description(
            ["hasher", "value"],
            "Write a string value into a hasher.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("hasher_write_static_str"),
        NativeFnMR::new(Hasher::write_static_str).description(
            ["hasher", "value"],
            "Write a compiler constant string into a hasher.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("hasher_finish"),
        NativeOutFnR::from_rust(Hasher::finish).description(
            ["hasher"],
            "Finish a hasher and produce the final hash value.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("unordered_hasher_new"),
        NativeOutFn0::from_rust(UnorderedHasher::new).description(
            [],
            "Create an empty unordered hash accumulator with no elements added yet.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("unordered_hasher_add"),
        NativeFnMR::new(UnorderedHasher::add).description(
            ["acc", "hash"],
            "Add a hash value to an unordered hash accumulator.",
            no_effects(),
        ),
    );
    to.add_function(
        ustr("unordered_hasher_finish"),
        NativeOutFnR::from_rust(UnorderedHasher::finish).description(
            ["acc"],
            "Finish an unordered hash accumulator and produce the final hash value.",
            no_effects(),
        ),
    );
}
