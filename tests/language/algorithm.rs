// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use test_log::test;

use indoc::indoc;

use crate::harness::{TestSession, int, string};

use ferlium::{
    call_fn,
    module::ModuleId,
    run_fn_native,
    std::{array::array_type, math::int_type, string::String as Str},
    value::Value,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::*;

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn factorial() {
    let mut session = TestSession::new();
    let module_id = session
        .compile(include_str!("../modules/factorial.fer"))
        .module_id;
    assert_eq!(
        run_native_int_int(&session, module_id, "factorial_rec_int", 5),
        120,
    );
    assert_eq!(
        run_native_int_int(&session, module_id, "factorial_iter_int", 5),
        120,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn fibonacci() {
    let mut session = TestSession::new();
    let module_id = session
        .compile(include_str!("../modules/fibonacci.fer"))
        .module_id;
    assert_eq!(
        run_native_int_int(&session, module_id, "fibonacci_iter", 16),
        987,
    );
    assert_eq!(
        run_native_int_int(&session, module_id, "fibonacci_rec", 16),
        987,
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn quicksort() {
    let mut session = TestSession::new();
    let module_id = session
        .compile(include_str!("../modules/quicksort.fer"))
        .module_id;
    let array_ty = array_type(int_type());
    let input = int_a![5, 3, 8, 1, 2, 7, 4, 11, 0];
    assert_val_eq!(
        call_fn!(session.session(), module_id, "quicksort_int_a", [input => array_ty] -> array_ty)
            .unwrap(),
        int_a![0, 1, 2, 3, 4, 5, 7, 8, 11],
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn sieve() {
    let mut session = TestSession::new();
    let module_id = session
        .compile(include_str!("../modules/sieve.fer"))
        .module_id;

    let array_ty = array_type(int_type());
    let primes_up_to = |n| {
        call_fn!(session.session(), module_id, "primes_up_to", [n => int_type()] -> array_ty)
            .unwrap()
    };
    assert_val_eq!(primes_up_to(int(10)), int_a![2, 3, 5, 7]);
    assert_val_eq!(
        primes_up_to(int(30)),
        int_a![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    );

    let is_prime = |n| run_native_int_bool(&session, module_id, "is_prime", n);
    assert_eq!(is_prime(1), false);
    assert_eq!(is_prime(4), false);
    assert_eq!(is_prime(100), false);
    assert_eq!(is_prime(2), true);
    assert_eq!(is_prime(97), true);

    let prime_count = |n| run_native_int_int(&session, module_id, "prime_count", n);
    assert_eq!(prime_count(10), 4);
    assert_eq!(prime_count(100), 25);
    // assert_eq!(prime_count(1_000), 168);
    // assert_eq!(prime_count(10_000), 1229);
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn rle_encode() {
    let mut session = TestSession::new();
    let module_id = session
        .compile(include_str!("../modules/rle_encode.fer"))
        .module_id;

    assert_eq!(
        run_native_string_string(&session, module_id, "rle_encode_string", "aabccccdde").as_ref(),
        "a2b1c4d2e1",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn csv() {
    let mut session = TestSession::new();
    let module_id = session
        .compile(include_str!("../modules/csv.fer"))
        .module_id;

    assert_eq!(
        run_native_int_string(&session, module_id, "csv_table", 3).as_ref(),
        "id,name,value\n1,item_1,1\n2,item_2,4\n3,item_3,9\n",
    );
}

#[test]
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
fn bank_account() {
    let mut session = TestSession::new();
    session
        .try_compile_module("quicksort", include_str!("../modules/quicksort.fer"))
        .unwrap();
    session
        .try_compile_module("account", include_str!("../modules/bank_account.fer"))
        .unwrap();

    session.run("account::assert_consistency()");
    assert_val_eq!(session.run("account::richest_person()"), string("Bob"));
    assert_val_eq!(session.run("account::most_active_person()"), string("Eve"));
    // FIXME: this cannot be in bank_account.fer due to issue #111
    assert_val_eq!(
        session.run(indoc! { r#"
            let data = account::test_data();
            let json = json_encode(data);
            let decoded: [account::Account] = json_decode(json);
            let sorted = quicksort::quicksort_array(decoded);
            sorted[len(sorted) - 1].name
		"# }),
        string("Eve")
    );
}

// helpers for calling Ferlium functions from Rust

fn run_native_int_int(
    session: &TestSession,
    module_id: ModuleId,
    name: &str,
    input: isize,
) -> isize {
    run_fn_native!(session.session(), module_id, name, [input => isize] -> isize).unwrap()
}

fn run_native_int_bool(
    session: &TestSession,
    module_id: ModuleId,
    name: &str,
    input: isize,
) -> bool {
    run_fn_native!(session.session(), module_id, name, [input => isize] -> bool).unwrap()
}

fn run_native_int_string(
    session: &TestSession,
    module_id: ModuleId,
    name: &str,
    input: isize,
) -> Str {
    run_fn_native!(session.session(), module_id, name, [input => isize] -> Str).unwrap()
}

fn run_native_string_string(
    session: &TestSession,
    module_id: ModuleId,
    name: &str,
    input: &str,
) -> Str {
    let input = Str::new(input);
    run_fn_native!(session.session(), module_id, name, [input => Str] -> Str).unwrap()
}
