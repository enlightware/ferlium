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
    CompilerSession, ExecutionTarget, MirOptimization, Path,
    hir::value::Value,
    module::{LocalFunctionId, ModuleId},
    std::{array::array_value_from_vec, math::Float, string::String as Str},
};

/// What a benchmark runs against.
///
/// Optimization is a per-compilation session setting rather than an execution target — the target
/// says *which interpreter*, the setting says *which artifact stage* — so the two axes are combined
/// here rather than by adding a variant to [`ExecutionTarget`]. Every benchmark that iterates
/// targets runs all three, which is what makes the cost of partial evaluation, at compile time and
/// at run time, directly comparable to the two baselines.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum BenchTarget {
    Hir,
    Mir,
    OptimizedMir,
}

impl BenchTarget {
    const ALL: [Self; 3] = [Self::Hir, Self::Mir, Self::OptimizedMir];

    fn target(self) -> ExecutionTarget {
        match self {
            Self::Hir => ExecutionTarget::Hir,
            Self::Mir | Self::OptimizedMir => ExecutionTarget::Mir,
        }
    }

    fn optimization(self) -> MirOptimization {
        match self {
            Self::Hir | Self::Mir => MirOptimization::Disabled,
            Self::OptimizedMir => MirOptimization::Enabled,
        }
    }

    /// A fresh session configured for this target.
    fn session(self) -> CompilerSession {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(self.optimization());
        session
    }
}

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

struct RuntimeBench<I> {
    target: ExecutionTarget,
    session: CompilerSession,
    module_id: ModuleId,
    entry: LocalFunctionId,
    input: I,
}

fn runtime_bench<I>(
    target: ExecutionTarget,
    mut session: CompilerSession,
    module_id: ModuleId,
    function_name: &str,
    input: I,
) -> RuntimeBench<I> {
    let entry = session
        .expect_fresh_module(module_id)
        .get_local_function_id(ferlium::ustr(function_name))
        .unwrap_or_else(|| panic!("function {function_name} not found"));
    session.prepare_execution_target(target, module_id);
    RuntimeBench {
        target,
        session,
        module_id,
        entry,
        input,
    }
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

fn setup_quicksort(target: BenchTarget) -> RuntimeBench<Vec<isize>> {
    let mut session = target.session();
    let module_id = session
        .compile_for(
            target.target(),
            include_str!("../tests/modules/quicksort.fer"),
            "quicksort.fer",
            Path::single_str("quicksort"),
        )
        .unwrap()
        .module_id;
    let random_data = lcg_seq(300, 42);
    runtime_bench(
        target.target(),
        session,
        module_id,
        "quicksort_int_a",
        random_data,
    )
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = setup_quicksort)]
fn bench_quicksort_run(bench: RuntimeBench<Vec<isize>>) -> BenchOutput<Value> {
    let RuntimeBench {
        target,
        mut session,
        module_id,
        entry,
        input,
    } = bench;
    let result = measure(|| {
        session
            .run_entry(target, module_id, entry, vec![int_a(input)])
            .unwrap()
    });
    BenchOutput { session, result }
}

fn setup_fibonacci(target: BenchTarget) -> RuntimeBench<()> {
    let mut session = target.session();
    let module_id = session
        .compile_for(
            target.target(),
            include_str!("../tests/modules/fibonacci.fer"),
            "fibonacci.fer",
            Path::single_str("fibonacci"),
        )
        .unwrap()
        .module_id;
    runtime_bench(target.target(), session, module_id, "fibonacci_rec", ())
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = setup_fibonacci)]
fn bench_fibonacci(bench: RuntimeBench<()>) -> BenchOutput<isize> {
    let RuntimeBench {
        target,
        mut session,
        module_id,
        entry,
        input: (),
    } = bench;
    let result = measure(|| {
        session
            .run_entry(
                target,
                module_id,
                entry,
                vec![Value::native(black_box(20isize))],
            )
            .unwrap()
            .into_primitive_ty::<isize>()
            .unwrap()
    });
    BenchOutput { session, result }
}

fn setup_sieve(target: BenchTarget) -> RuntimeBench<()> {
    let mut session = target.session();
    let module_id = session
        .compile_for(
            target.target(),
            include_str!("../tests/modules/sieve.fer"),
            "sieve.fer",
            Path::single_str("sieve"),
        )
        .unwrap()
        .module_id;
    runtime_bench(target.target(), session, module_id, "prime_count", ())
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = setup_sieve)]
fn bench_sieve(bench: RuntimeBench<()>) -> BenchOutput<isize> {
    let RuntimeBench {
        target,
        mut session,
        module_id,
        entry,
        input: (),
    } = bench;
    let result = measure(|| {
        session
            .run_entry(
                target,
                module_id,
                entry,
                vec![Value::native(black_box(500isize))],
            )
            .unwrap()
            .into_primitive_ty::<isize>()
            .unwrap()
    });
    BenchOutput { session, result }
}

fn setup_rle_encode(target: BenchTarget) -> RuntimeBench<Str> {
    let mut session = target.session();
    let module_id = session
        .compile_for(
            target.target(),
            include_str!("../tests/modules/rle_encode.fer"),
            "rle_encode.fer",
            Path::single_str("rle_encode"),
        )
        .unwrap()
        .module_id;
    let input = Str::new(&"aabccccccc".repeat(50));
    runtime_bench(
        target.target(),
        session,
        module_id,
        "rle_encode_string",
        input,
    )
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = setup_rle_encode)]
fn bench_rle_encode(bench: RuntimeBench<Str>) -> BenchOutput<Str> {
    let RuntimeBench {
        target,
        mut session,
        module_id,
        entry,
        input,
    } = bench;
    let result = measure(|| {
        session
            .run_entry(target, module_id, entry, vec![Value::native(input)])
            .unwrap()
            .into_primitive_ty::<Str>()
            .unwrap()
    });
    BenchOutput { session, result }
}

fn setup_csv(target: BenchTarget) -> RuntimeBench<()> {
    let mut session = target.session();
    let module_id = session
        .compile_for(
            target.target(),
            include_str!("../tests/modules/csv.fer"),
            "csv.fer",
            Path::single_str("csv"),
        )
        .unwrap()
        .module_id;
    runtime_bench(target.target(), session, module_id, "csv_table", ())
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = setup_csv)]
fn bench_csv(bench: RuntimeBench<()>) -> BenchOutput<Str> {
    let RuntimeBench {
        target,
        mut session,
        module_id,
        entry,
        input: (),
    } = bench;
    let result = measure(|| {
        session
            .run_entry(
                target,
                module_id,
                entry,
                vec![Value::native(black_box(500isize))],
            )
            .unwrap()
            .into_primitive_ty::<Str>()
            .unwrap()
    });
    BenchOutput { session, result }
}

fn setup_bank_account(target: BenchTarget) -> RuntimeBench<()> {
    use indoc::indoc;
    let mut session = target.session();
    let _ = session.compile_for(
        target.target(),
        include_str!("../tests/modules/quicksort.fer"),
        "quicksort.fer",
        Path::single_str("quicksort"),
    );
    let _ = session.compile_for(
        target.target(),
        include_str!("../tests/modules/bank_account.fer"),
        "bank_account.fer",
        Path::single_str("account"),
    );
    let module_id = session
        .compile_for(
            target.target(),
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
    runtime_bench(target.target(), session, module_id, "test", ())
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = setup_bank_account)]
fn bench_bank_account_run(bench: RuntimeBench<()>) -> BenchOutput<Str> {
    let RuntimeBench {
        target,
        mut session,
        module_id,
        entry,
        input: (),
    } = bench;
    let result = measure(|| {
        session
            .run_entry(target, module_id, entry, vec![])
            .unwrap()
            .into_primitive_ty::<Str>()
            .unwrap()
    });
    BenchOutput { session, result }
}

fn setup_sudoku(target: BenchTarget) -> RuntimeBench<()> {
    let mut session = target.session();
    let module_id = session
        .compile_for(
            target.target(),
            include_str!("../tests/modules/sudoku.fer"),
            "sudoku.fer",
            Path::single_str("sudoku"),
        )
        .unwrap()
        .module_id;
    runtime_bench(target.target(), session, module_id, "solved_cell", ())
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = setup_sudoku)]
fn bench_sudoku_run(bench: RuntimeBench<()>) -> BenchOutput<isize> {
    let RuntimeBench {
        target,
        mut session,
        module_id,
        entry,
        input: (),
    } = bench;
    let result = measure(|| {
        session
            .run_entry(
                target,
                module_id,
                entry,
                vec![
                    Value::native(black_box(0isize)),
                    Value::native(black_box(2isize)),
                ],
            )
            .unwrap()
            .into_primitive_ty::<isize>()
            .unwrap()
    });
    BenchOutput { session, result }
}

// --- Linear algebra ---
//
// Two profiles of the same library, deliberately kept as separate targets: the transform is
// dominated by calls, dictionary passing and per-call copies on bodies where inlining and
// specialization decide everything, while the grid is dominated by the quality of an innermost loop
// run n^3 times. The first measured baseline separates them cleanly — the optimizer recovers ~19% of
// the transform and ~7% of the grid — so a single number mixing the two would hide which half moved.
//
// The transform runs its `int` and `float` instantiations together, which is the one place a single
// number is right: they measure the same thing, and the first baseline had them within 1.6 points of
// each other. Running both still reaches both specializations of every generic body.
//
// Both are runtime-only — adding either to the compile corpus would move `bench_std_mir_optimize`
// and break comparison against every figure recorded for it.

fn linalg_session(target: BenchTarget, function_name: &str) -> RuntimeBench<()> {
    let mut session = target.session();
    // The module's element access goes through subscripts, which are gated as experimental.
    session.set_allow_experimental(true);
    let module_id = session
        .compile_for(
            target.target(),
            include_str!("../tests/modules/linalg.fer"),
            "linalg.fer",
            Path::single_str("linalg"),
        )
        .unwrap()
        .module_id;
    runtime_bench(target.target(), session, module_id, function_name, ())
}

fn setup_linalg_transform(target: BenchTarget) -> RuntimeBench<()> {
    linalg_session(target, "transform_pipeline_mixed")
}

fn setup_linalg_grid(target: BenchTarget) -> RuntimeBench<()> {
    linalg_session(target, "grid_simulation")
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = setup_linalg_transform)]
fn bench_linalg_transform(bench: RuntimeBench<()>) -> BenchOutput<isize> {
    let RuntimeBench {
        target,
        mut session,
        module_id,
        entry,
        input: (),
    } = bench;
    let result = measure(|| {
        session
            .run_entry(
                target,
                module_id,
                entry,
                vec![Value::native(black_box(6isize))],
            )
            .unwrap()
            .into_primitive_ty::<isize>()
            .unwrap()
    });
    BenchOutput { session, result }
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = setup_linalg_grid)]
fn bench_linalg_grid(bench: RuntimeBench<()>) -> BenchOutput<Float> {
    let RuntimeBench {
        target,
        mut session,
        module_id,
        entry,
        input: (),
    } = bench;
    let result = measure(|| {
        session
            .run_entry(
                target,
                module_id,
                entry,
                vec![
                    Value::native(black_box(8isize)),
                    Value::native(black_box(2isize)),
                ],
            )
            .unwrap()
            .into_primitive_ty::<Float>()
            .unwrap()
    });
    BenchOutput { session, result }
}

fn setup_calculator(target: BenchTarget) -> RuntimeBench<Str> {
    let mut session = target.session();
    let module_id = session
        .compile_for(
            target.target(),
            include_str!("../tests/modules/calculator.fer"),
            "calculator.fer",
            Path::single_str("calculator"),
        )
        .unwrap()
        .module_id;
    let expr = Str::new("((1 + 2) * (3 + 4) - 5) * 6 / 2 + 100");
    runtime_bench(target.target(), session, module_id, "calculate", expr)
}

#[library_benchmark(teardown = teardown_benchmark)]
#[benches::target(iter = BenchTarget::ALL, setup = setup_calculator)]
fn bench_calculator_run(bench: RuntimeBench<Str>) -> BenchOutput<isize> {
    let RuntimeBench {
        target,
        mut session,
        module_id,
        entry,
        input,
    } = bench;
    let result = measure(|| {
        session
            .run_entry(target, module_id, entry, vec![Value::native(input)])
            .unwrap()
            .into_primitive_ty::<isize>()
            .unwrap()
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
