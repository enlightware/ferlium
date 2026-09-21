// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

mod runtime_workloads;

use gungraun::{
    Callgrind, EntryPoint, LibraryBenchmarkConfig, library_benchmark, library_benchmark_group, main,
};
use std::hint::black_box;

use ferlium::{CompilerSession, ExecutionTarget, MirOptimization, Path, std::math::Float};

use runtime_workloads::{BenchTarget, PreparedRuntimeWorkload, RuntimeWorkload};

trait RuntimeChecksum {
    fn checksum(self) -> f64;
}

impl RuntimeChecksum for isize {
    fn checksum(self) -> f64 {
        self as f64
    }
}

impl RuntimeChecksum for Float {
    fn checksum(self) -> f64 {
        self.into_inner()
    }
}

// --- User-code corpus ---

/// The modules the user-code compile benchmark builds.
///
/// `linalg` and `iter_pipeline` are here for the optimizer rather than for the front end: the other
/// seven are concrete script code that specializes barely at all, while these two carry the generic
/// bodies, the specialization table and the closure-carrying adapter structs the passes actually
/// spend themselves on.
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
    ("linalg", include_str!("../tests/modules/linalg.fer")),
    (
        "iter_pipeline",
        include_str!("../tests/modules/iter_pipeline.fer"),
    ),
];

/// Compiles every corpus module and builds its execution target.
///
/// The `prepare_execution_target` call is what runs the optimizer; without it the `Mir` and
/// `OptimizedMir` variants differ by a session flag with nothing to act on. No-op for `Hir`.
fn compile_user_code_corpus(session: &mut CompilerSession, target: ExecutionTarget) {
    for (name, src) in USER_CODE_CORPUS {
        let file = format!("{name}.fer");
        let module_id = session
            .compile_for(target, src, &file, Path::single_str(name))
            .unwrap()
            .module_id;
        session.prepare_execution_target(target, module_id);
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
    // Allow subscript access, used by `linalg`.
    session.set_allow_experimental(true);
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

// The cost of the optimization passes, over every body of the standard library. Read against
// `bench_std_mir_build`, which does the same work with the passes off. (Gungraun's macro rejects
// doc comments here.)
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

// Read `Mir` against `OptimizedMir` for the optimizer's cost over user code, which the std-only
// pair above cannot give. (Gungraun's macro rejects doc comments here.)
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
// shared with the MIR and Wasm profile runners. The macro emits the named setup functions that
// Gungraun requires.

macro_rules! runtime_benchmark {
    ($benchmark:ident, $setup:ident, $workload:expr, $output:ty, $run:ident) => {
        fn $setup(target: BenchTarget) -> PreparedRuntimeWorkload {
            $workload.prepare(target)
        }

        #[library_benchmark(teardown = teardown_benchmark)]
        #[benches::target(iter = BenchTarget::ALL, setup = $setup)]
        fn $benchmark(mut bench: PreparedRuntimeWorkload) -> BenchOutput<$output> {
            let result = measure(|| bench.$run());
            assert_eq!(
                result.checksum(),
                $workload.expected(),
                "benchmark `{}` produced the wrong checksum",
                $workload.name()
            );
            BenchOutput {
                session: bench.session,
                result,
            }
        }
    };
}

runtime_benchmark!(
    bench_quicksort_run,
    setup_quicksort,
    RuntimeWorkload::QUICKSORT,
    isize,
    run_int
);
runtime_benchmark!(
    bench_fibonacci,
    setup_fibonacci,
    RuntimeWorkload::FIBONACCI,
    isize,
    run_int
);
runtime_benchmark!(
    bench_sieve,
    setup_sieve,
    RuntimeWorkload::SIEVE,
    isize,
    run_int
);
runtime_benchmark!(
    bench_rle_encode,
    setup_rle_encode,
    RuntimeWorkload::RLE_ENCODE,
    isize,
    run_int
);
runtime_benchmark!(bench_csv, setup_csv, RuntimeWorkload::CSV, isize, run_int);
runtime_benchmark!(
    bench_bank_account_run,
    setup_bank_account,
    RuntimeWorkload::BANK_ACCOUNT,
    isize,
    run_int
);
runtime_benchmark!(
    bench_sudoku_run,
    setup_sudoku,
    RuntimeWorkload::SUDOKU,
    isize,
    run_int
);
runtime_benchmark!(
    bench_calculator_run,
    setup_calculator,
    RuntimeWorkload::CALCULATOR,
    isize,
    run_int
);
runtime_benchmark!(
    bench_linalg_transform,
    setup_linalg_transform,
    RuntimeWorkload::LINALG_TRANSFORM,
    isize,
    run_int
);
runtime_benchmark!(
    bench_linalg_grid,
    setup_linalg_grid,
    RuntimeWorkload::LINALG_GRID,
    Float,
    run_float
);
runtime_benchmark!(
    bench_iter_pipeline,
    setup_iter_pipeline,
    RuntimeWorkload::ITER_PIPELINE,
    isize,
    run_int
);
runtime_benchmark!(
    bench_data_text_roundtrip,
    setup_data_text_roundtrip,
    RuntimeWorkload::DATA_TEXT_ROUNDTRIP,
    isize,
    run_int
);

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
        bench_linalg_grid,
        bench_iter_pipeline,
        bench_data_text_roundtrip
    ]
);

main!(
    config = benchmark_config(),
    library_benchmark_groups = [compilation, runtime]
);
