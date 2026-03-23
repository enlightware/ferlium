// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use gungraun::{library_benchmark, library_benchmark_group, main};
use indoc::indoc;
use std::hint::black_box;

use ferlium::{
    CompilerSession, Path, call_fn,
    module::ModuleId,
    run_fn_native,
    std::{array::array_type, math::int_type, string::String as Str},
    value::Value,
};

// --- Benchmark Functions ---

#[library_benchmark]
fn bench_new_session() {
    CompilerSession::new();
}

fn compile_quicksort() -> (CompilerSession, ModuleId) {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/quicksort.fer"),
            "quicksort.fer",
            Path::single_str("quicksort"),
        )
        .unwrap()
        .module_id;
    (session, module_id)
}

#[library_benchmark]
fn bench_quicksort_compile() {
    compile_quicksort();
}

fn setup_quicksort() -> (CompilerSession, ModuleId, Vec<isize>) {
    let (session, module_id) = compile_quicksort();
    let random_data = lcg_seq(300, 42);
    (session, module_id, random_data)
}

#[library_benchmark(setup = setup_quicksort)]
fn bench_quicksort_run((session, module_id, random_data): (CompilerSession, ModuleId, Vec<isize>)) {
    let array_ty = array_type(int_type());
    let input = int_a(random_data);

    call_fn!(&session, module_id, "quicksort_int_a", [input => array_ty] -> array_ty).unwrap();
}

fn setup_fibonacci() -> (CompilerSession, ModuleId) {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/fibonacci.fer"),
            "fibonacci.fer",
            Path::single_str("fibonacci"),
        )
        .unwrap()
        .module_id;
    (session, module_id)
}

#[library_benchmark(setup = setup_fibonacci)]
fn bench_fibonacci((session, module_id): (CompilerSession, ModuleId)) {
    run_fn_native!(&session, module_id, "fibonacci_rec", [black_box(20) => isize] -> isize)
        .unwrap();
}

fn setup_sieve() -> (CompilerSession, ModuleId) {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/sieve.fer"),
            "sieve.fer",
            Path::single_str("sieve"),
        )
        .unwrap()
        .module_id;
    (session, module_id)
}

#[library_benchmark(setup = setup_sieve)]
fn bench_sieve((session, module_id): (CompilerSession, ModuleId)) {
    run_fn_native!(&session, module_id, "prime_count", [black_box(500) => isize] -> isize).unwrap();
}

fn setup_rle_encode() -> (CompilerSession, ModuleId, Str) {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/rle_encode.fer"),
            "rle_encode.fer",
            Path::single_str("rle_encode"),
        )
        .unwrap()
        .module_id;
    let input = Str::new(&"aabccccccc".repeat(50));
    (session, module_id, input)
}

#[library_benchmark(setup = setup_rle_encode)]
fn bench_rle_encode((session, module_id, input): (CompilerSession, ModuleId, Str)) {
    run_fn_native!(&session, module_id, "rle_encode_string", [input => Str] -> Str).unwrap();
}

fn setup_csv() -> (CompilerSession, ModuleId) {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/csv.fer"),
            "csv.fer",
            Path::single_str("csv"),
        )
        .unwrap()
        .module_id;
    (session, module_id)
}

#[library_benchmark(setup = setup_csv)]
fn bench_csv((session, module_id): (CompilerSession, ModuleId)) {
    run_fn_native!(&session, module_id, "csv_table", [black_box(500) => isize] -> Str).unwrap();
}

fn compile_bank_account() -> (CompilerSession, ModuleId) {
    let mut session = CompilerSession::new();
    let _ = session.compile(
        include_str!("../tests/modules/quicksort.fer"),
        "quicksort.fer",
        Path::single_str("quicksort"),
    );
    let _ = session.compile(
        include_str!("../tests/modules/bank_account.fer"),
        "bank_account.fer",
        Path::single_str("account"),
    );
    let module_id = session
        .compile(
            indoc! { r#"
            fn test() {
                let data = account::test_data();
                let json = json_encode(data);
                let decoded: [account::Account] = json_decode(json);
                let sorted = quicksort::quicksort_array(decoded);
                sorted[len(sorted) - 1].name
            }
        "# },
            "test.fer",
            Path::single_str("test"),
        )
        .unwrap()
        .module_id;
    (session, module_id)
}

#[library_benchmark]
fn bench_bank_account_compile() {
    compile_bank_account();
}

#[library_benchmark(setup = compile_bank_account)]
fn bench_bank_account_run((session, module_id): (CompilerSession, ModuleId)) {
    run_fn_native!(&session, module_id, "test", [] -> Str).unwrap();
}

// --- Support functions ---

fn int_a(values: impl Into<Vec<isize>>) -> Value {
    Value::native(ferlium::std::array::Array::from_vec(
        values.into().into_iter().map(Value::native).collect(),
    ))
}

fn lcg_seq(n: usize, seed: usize) -> Vec<isize> {
    let mut state = seed;
    (0..n)
        .map(|_| {
            state = state.wrapping_mul(1664525).wrapping_add(1013904223);
            state as isize
        })
        .collect()
}

// --- Gungraun Setup ---

library_benchmark_group!(
    name = compilation,
    benchmarks = [
        bench_new_session,
        bench_quicksort_compile,
        bench_bank_account_compile
    ]
);

library_benchmark_group!(
    name = runtime,
    benchmarks = [
        bench_quicksort_run,
        bench_fibonacci,
        bench_sieve,
        bench_rle_encode,
        bench_csv,
        bench_bank_account_run
    ]
);

main!(library_benchmark_groups = [compilation, runtime]);
