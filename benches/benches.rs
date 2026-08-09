// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

mod runtime_workloads;

use gungraun::{
    Callgrind, EntryPoint, LibraryBenchmarkConfig, library_benchmark, library_benchmark_group, main,
};
use std::hint::black_box;

use ferlium::{
    CompilerSession, ExecutionTarget, MirOptimization, Path,
    hir::value::Value,
    std::{math::Float, string::String as Str},
};

use runtime_workloads::{BenchTarget, PreparedRuntimeWorkload, RuntimeWorkload};

// --- User-code corpus ---

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

fn compile_user_code_corpus(session: &mut CompilerSession, target: ExecutionTarget) {
    for (name, src) in USER_CODE_CORPUS {
        let file = format!("{name}.fer");
        let module_id = session
            .compile_for(target, src, &file, Path::single_str(name))
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

fn bench_session_for_target(target: BenchTarget) -> (CompilerSession, ExecutionTarget) {
    let mut session = target.session();
    if target.target() == ExecutionTarget::Mir {
        let std_id = session.std_module().module_id();
        session.prepare_execution_target(target.target(), std_id);
    }
    (session, target.target())
}

fn warm_initial_session_state() {
    drop(CompilerSession::new());
}

fn prepared_std_mir_session() -> CompilerSession {
    let mut session = CompilerSession::new();
    let std_id = session.std_module().module_id();
    session.prepare_execution_target(ExecutionTarget::Mir, std_id);
    session
}

fn warm_std_mir_state() {
    drop(prepared_std_mir_session());
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

#[library_benchmark(setup = warm_initial_session_state, teardown = teardown_benchmark)]
fn bench_warm_session_load(_: ()) -> BenchOutput<()> {
    BenchOutput {
        session: measure(CompilerSession::new),
        result: (),
    }
}

#[library_benchmark(setup = bench_session, teardown = teardown_benchmark)]
fn bench_std_mir_build(mut session: CompilerSession) -> BenchOutput<()> {
    let std_id = session.std_module().module_id();
    measure(|| session.prepare_execution_target(ExecutionTarget::Mir, std_id));
    BenchOutput {
        session,
        result: (),
    }
}

// The cost of the optimization passes, over every body of the standard library. Optimization is
// driven by `prepare_execution_target`, not by compiling, so this is where its compile-time cost
// shows up — the user-code compile benchmarks never enter it. Read against `bench_std_mir_build`,
// which does the same work with the passes off. (Gungraun's macro rejects doc comments here.)
#[library_benchmark(setup = bench_session, teardown = teardown_benchmark)]
fn bench_std_mir_optimize(mut session: CompilerSession) -> BenchOutput<()> {
    session.set_mir_optimization(MirOptimization::Enabled);
    let std_id = session.std_module().module_id();
    measure(|| session.prepare_execution_target(ExecutionTarget::Mir, std_id));
    BenchOutput {
        session,
        result: (),
    }
}

#[library_benchmark(setup = warm_std_mir_state, teardown = teardown_benchmark)]
fn bench_cached_std_mir_session_load(_: ()) -> BenchOutput<()> {
    BenchOutput {
        session: measure(CompilerSession::new),
        result: (),
    }
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = bench_session_for_target)]
fn bench_user_code_compile_without_std_startup(
    (mut session, target): (CompilerSession, ExecutionTarget),
) -> BenchOutput<()> {
    measure(|| compile_user_code_corpus(&mut session, target));
    BenchOutput {
        session,
        result: (),
    }
}

// --- Runtime benchmarks ---
//
// Workload compilation, entry selection and input construction live in `runtime_workloads.rs`,
// shared with `examples/mir_profile.rs`. These one-line setup functions remain because Gungraun's
// macro requires a concrete function path for each named benchmark.

fn setup_quicksort(target: BenchTarget) -> PreparedRuntimeWorkload {
    RuntimeWorkload::Quicksort.prepare(target)
}

fn setup_fibonacci(target: BenchTarget) -> PreparedRuntimeWorkload {
    RuntimeWorkload::Fibonacci.prepare(target)
}

fn setup_sieve(target: BenchTarget) -> PreparedRuntimeWorkload {
    RuntimeWorkload::Sieve.prepare(target)
}

fn setup_rle_encode(target: BenchTarget) -> PreparedRuntimeWorkload {
    RuntimeWorkload::RleEncode.prepare(target)
}

fn setup_csv(target: BenchTarget) -> PreparedRuntimeWorkload {
    RuntimeWorkload::Csv.prepare(target)
}

fn setup_bank_account(target: BenchTarget) -> PreparedRuntimeWorkload {
    RuntimeWorkload::BankAccount.prepare(target)
}

fn setup_sudoku(target: BenchTarget) -> PreparedRuntimeWorkload {
    RuntimeWorkload::Sudoku.prepare(target)
}

fn setup_calculator(target: BenchTarget) -> PreparedRuntimeWorkload {
    RuntimeWorkload::Calculator.prepare(target)
}

fn setup_linalg_transform(target: BenchTarget) -> PreparedRuntimeWorkload {
    RuntimeWorkload::LinalgTransform.prepare(target)
}

fn setup_linalg_grid(target: BenchTarget) -> PreparedRuntimeWorkload {
    RuntimeWorkload::LinalgGrid.prepare(target)
}

macro_rules! runtime_benchmark {
    ($benchmark:ident, $setup:ident, $output:ty, $run:ident) => {
        #[library_benchmark(teardown = teardown_benchmark)]
        #[benches::target(iter = BenchTarget::ALL, setup = $setup)]
        fn $benchmark(mut bench: PreparedRuntimeWorkload) -> BenchOutput<$output> {
            let result = measure(|| bench.$run());
            BenchOutput {
                session: bench.session,
                result,
            }
        }
    };
}

runtime_benchmark!(bench_quicksort_run, setup_quicksort, Value, run_value);
runtime_benchmark!(bench_fibonacci, setup_fibonacci, isize, run_int);
runtime_benchmark!(bench_sieve, setup_sieve, isize, run_int);
runtime_benchmark!(bench_rle_encode, setup_rle_encode, Str, run_string);
runtime_benchmark!(bench_csv, setup_csv, Str, run_string);
runtime_benchmark!(bench_bank_account_run, setup_bank_account, Str, run_string);
runtime_benchmark!(bench_sudoku_run, setup_sudoku, isize, run_int);
runtime_benchmark!(bench_calculator_run, setup_calculator, isize, run_int);
runtime_benchmark!(
    bench_linalg_transform,
    setup_linalg_transform,
    isize,
    run_int
);
runtime_benchmark!(bench_linalg_grid, setup_linalg_grid, Float, run_float);

// --- Gungraun setup ---

library_benchmark_group!(
    name = compilation,
    benchmarks = [
        bench_std_load,
        bench_warm_session_load,
        bench_std_mir_build,
        bench_std_mir_optimize,
        bench_cached_std_mir_session_load,
        bench_user_code_compile_without_std_startup
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
        bench_bank_account_run,
        bench_sudoku_run,
        bench_calculator_run,
        bench_linalg_transform,
        bench_linalg_grid
    ]
);

main!(
    config = benchmark_config(),
    library_benchmark_groups = [compilation, runtime]
);
