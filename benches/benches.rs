// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use gungraun::{
    Callgrind, EntryPoint, LibraryBenchmarkConfig, library_benchmark, library_benchmark_group, main,
};
use std::hint::black_box;

use ferlium::{
    CompilerSession, Path, call_fn,
    hir::value::Value,
    module::ModuleId,
    run_fn_native,
    std::{
        array::{array_type, array_value_from_vec},
        math::int_type,
        string::String as Str,
    },
};

// --- User-code corpus ---
//
// Bundle of mid-size, non-trivial modules used by the user-code compilation
// benchmarks. Each tuple is (module-name, source). Order matters when modules
// reference each other (here they don't).
const USER_CODE_CORPUS: &[(&str, &str)] = &[
    ("sudoku", include_str!("../tests/modules/sudoku.fer")),
    (
        "calculator",
        include_str!("../tests/modules/calculator.fer"),
    ),
    ("quicksort", include_str!("../tests/modules/quicksort.fer")),
    ("account", include_str!("../tests/modules/bank_account.fer")),
    ("sieve", include_str!("../tests/modules/sieve.fer")),
    ("csv", include_str!("../tests/modules/csv.fer")),
    (
        "rle_encode",
        include_str!("../tests/modules/rle_encode.fer"),
    ),
];

fn compile_user_code_corpus(session: &mut CompilerSession) {
    for (name, src) in USER_CODE_CORPUS {
        let file = format!("{name}.fer");
        let module_id = session
            .compile(src, &file, Path::single_str(name))
            .unwrap()
            .module_id;
        black_box(module_id);
    }
}

struct BenchOutput<T> {
    session: CompilerSession,
    result: T,
}

fn bench_session() -> CompilerSession {
    CompilerSession::new()
}

/// Drop benchmark-owned values after Gungraun has left the measured function.
fn teardown_benchmark<T>(output: BenchOutput<T>) {
    let BenchOutput {
        session: _session,
        result: _result,
    } = output;
}

// This function's symbol is the custom Callgrind entry point. Keeping it out of line gives every
// benchmark the same precise boundary without matching nested Rust closure/monomorph symbols.
#[inline(never)]
fn measure<T>(run: impl FnOnce() -> T) -> T {
    let result = run();
    black_box(&result);
    result
}

fn benchmark_config() -> LibraryBenchmarkConfig {
    let mut config = LibraryBenchmarkConfig::default();
    config.tool(Callgrind::default().entry_point(EntryPoint::Custom("*::measure::<*>".to_owned())));
    config
}

// --- Compilation benchmarks ---

#[library_benchmark(teardown = teardown_benchmark)]
fn bench_std_load() -> BenchOutput<()> {
    BenchOutput {
        session: measure(bench_session),
        result: (),
    }
}

#[library_benchmark(setup = bench_session, teardown = teardown_benchmark)]
fn bench_user_code_compile_without_std_startup(mut session: CompilerSession) -> BenchOutput<()> {
    measure(|| compile_user_code_corpus(&mut session));
    BenchOutput {
        session,
        result: (),
    }
}

// --- Runtime benchmarks ---

fn setup_quicksort() -> (CompilerSession, ModuleId, Vec<isize>) {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/quicksort.fer"),
            "quicksort.fer",
            Path::single_str("quicksort"),
        )
        .unwrap()
        .module_id;
    let random_data = lcg_seq(300, 42);
    (session, module_id, random_data)
}

#[library_benchmark(setup = setup_quicksort, teardown = teardown_benchmark)]
fn bench_quicksort_run(
    (session, module_id, random_data): (CompilerSession, ModuleId, Vec<isize>),
) -> BenchOutput<Value> {
    let result = measure(|| {
        let array_ty = array_type(int_type());
        let input = int_a(random_data);
        call_fn!(&session, module_id, "quicksort_int_a", [input => array_ty] -> array_ty).unwrap()
    });
    BenchOutput { session, result }
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

#[library_benchmark(setup = setup_fibonacci, teardown = teardown_benchmark)]
fn bench_fibonacci((session, module_id): (CompilerSession, ModuleId)) -> BenchOutput<isize> {
    let result = measure(|| {
        run_fn_native!(&session, module_id, "fibonacci_rec", [black_box(20) => isize] -> isize)
            .unwrap()
    });
    BenchOutput { session, result }
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

#[library_benchmark(setup = setup_sieve, teardown = teardown_benchmark)]
fn bench_sieve((session, module_id): (CompilerSession, ModuleId)) -> BenchOutput<isize> {
    let result = measure(|| {
        run_fn_native!(&session, module_id, "prime_count", [black_box(500) => isize] -> isize)
            .unwrap()
    });
    BenchOutput { session, result }
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

#[library_benchmark(setup = setup_rle_encode, teardown = teardown_benchmark)]
fn bench_rle_encode(
    (session, module_id, input): (CompilerSession, ModuleId, Str),
) -> BenchOutput<Str> {
    let result = measure(|| {
        run_fn_native!(&session, module_id, "rle_encode_string", [input => Str] -> Str).unwrap()
    });
    BenchOutput { session, result }
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

#[library_benchmark(setup = setup_csv, teardown = teardown_benchmark)]
fn bench_csv((session, module_id): (CompilerSession, ModuleId)) -> BenchOutput<Str> {
    let result = measure(|| {
        run_fn_native!(&session, module_id, "csv_table", [black_box(500) => isize] -> Str).unwrap()
    });
    BenchOutput { session, result }
}

fn setup_bank_account() -> (CompilerSession, ModuleId) {
    use indoc::indoc;
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

#[library_benchmark(setup = setup_bank_account, teardown = teardown_benchmark)]
fn bench_bank_account_run((session, module_id): (CompilerSession, ModuleId)) -> BenchOutput<Str> {
    let result = measure(|| run_fn_native!(&session, module_id, "test", [] -> Str).unwrap());
    BenchOutput { session, result }
}

fn setup_sudoku() -> (CompilerSession, ModuleId) {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/sudoku.fer"),
            "sudoku.fer",
            Path::single_str("sudoku"),
        )
        .unwrap()
        .module_id;
    (session, module_id)
}

#[library_benchmark(setup = setup_sudoku, teardown = teardown_benchmark)]
fn bench_sudoku_run((session, module_id): (CompilerSession, ModuleId)) -> BenchOutput<isize> {
    let result = measure(|| {
        run_fn_native!(
            &session,
            module_id,
            "solved_cell",
            [black_box(0) => isize, black_box(2) => isize] -> isize
        )
        .unwrap()
    });
    BenchOutput { session, result }
}

fn setup_calculator() -> (CompilerSession, ModuleId, Str) {
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/calculator.fer"),
            "calculator.fer",
            Path::single_str("calculator"),
        )
        .unwrap()
        .module_id;
    let expr = Str::new("((1 + 2) * (3 + 4) - 5) * 6 / 2 + 100");
    (session, module_id, expr)
}

#[library_benchmark(setup = setup_calculator, teardown = teardown_benchmark)]
fn bench_calculator_run(
    (session, module_id, expr): (CompilerSession, ModuleId, Str),
) -> BenchOutput<isize> {
    let result = measure(|| {
        run_fn_native!(&session, module_id, "calculate", [expr => Str] -> isize).unwrap()
    });
    BenchOutput { session, result }
}

// --- Support functions ---

fn int_a(values: impl Into<Vec<isize>>) -> Value {
    array_value_from_vec(values.into().into_iter().map(Value::native).collect())
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
    benchmarks = [bench_std_load, bench_user_code_compile_without_std_startup]
);

library_benchmark_group!(
    name = runtime,
    benchmarks = [
        bench_quicksort_run,
        bench_fibonacci,
        bench_sieve,
        bench_rle_encode,
        bench_csv,
        bench_bank_account_run,
        bench_sudoku_run,
        bench_calculator_run
    ]
);

main!(
    config = benchmark_config(),
    library_benchmark_groups = [compilation, runtime]
);
