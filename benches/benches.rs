// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use criterion::{Criterion, criterion_group, criterion_main};
use ferlium::{
    CompilerSession, Path, call_fn, run_fn_native,
    std::{array::array_type, math::int_type, string::String as Str},
    value::Value,
};

fn bench_new_session(c: &mut Criterion) {
    let mut group = c.benchmark_group("compilation");
    group.bench_function("CompilerSession::new", |b| {
        b.iter(|| {
            CompilerSession::new();
        })
    });
    group.finish();
}

fn bench_quicksort(c: &mut Criterion) {
    // Prepare
    let mut session = CompilerSession::new();
    let compile = |session: &mut CompilerSession| {
        session
            .compile(
                include_str!("../tests/modules/quicksort.fer"),
                "quicksort.fer",
                Path::single_str("quicksort"),
            )
            .unwrap()
            .module_id
    };
    let array_ty = array_type(int_type());
    let random_data = lcg_seq(500, 42);

    // Bench compilation
    let mut group = c.benchmark_group("compilation");
    group.bench_function("quicksort", |b| b.iter(|| compile(&mut session)));
    group.finish();

    // Bench evaluation
    let mut group = c.benchmark_group("runtime");
    group.sample_size(20);
    let module_id = compile(&mut session);
    group.bench_function("quicksort(500)", |b| {
        b.iter(|| {
            let input = int_a(random_data.clone());
            call_fn!(&session, module_id, "quicksort_int_a", [input => array_ty] -> array_ty)
                .unwrap();
        })
    });
    group.finish();
}

fn bench_fibonacci(c: &mut Criterion) {
    // Prepare
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/fibonacci.fer"),
            "fibonacci.fer",
            Path::single_str("fibonacci"),
        )
        .unwrap()
        .module_id;

    // Bench evaluation
    let mut group = c.benchmark_group("runtime");
    group.sample_size(20);
    group.bench_function("fibonacci_rec(22)", |b| {
        b.iter(|| {
            run_fn_native!(&session, module_id, "fibonacci_rec", [22 => isize] -> isize).unwrap()
        })
    });
    group.finish();
}

fn bench_sieve(c: &mut Criterion) {
    // Prepare
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/sieve.fer"),
            "sieve.fer",
            Path::single_str("sieve"),
        )
        .unwrap()
        .module_id;

    // Bench evaluation
    let mut group = c.benchmark_group("runtime");
    group.bench_function("prime_count(1000)", |b| {
        b.iter(|| {
            run_fn_native!(&session, module_id, "prime_count", [1000 => isize] -> isize).unwrap()
        })
    });
    group.finish();
}

fn bench_csv(c: &mut Criterion) {
    // Prepare
    let mut session = CompilerSession::new();
    let module_id = session
        .compile(
            include_str!("../tests/modules/csv.fer"),
            "csv.fer",
            Path::single_str("csv"),
        )
        .unwrap()
        .module_id;

    // Bench evaluation
    let mut group = c.benchmark_group("runtime");
    group.bench_function("csv_table(500)", |b| {
        b.iter(|| run_fn_native!(&session, module_id, "csv_table", [500 => isize] -> Str).unwrap())
    });
    group.finish();
}

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

criterion_group!(
    name = runtime;
    config = Criterion::default().sample_size(50);
    targets = bench_new_session, bench_quicksort, bench_fibonacci, bench_sieve, bench_csv
);
criterion_main!(runtime);
