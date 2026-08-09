// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Runtime workload definitions shared by the Gungraun harness and the fast MIR profile runner.
//!
//! Compilation and canonical inputs are prepared by [`RuntimeWorkload::prepare`]. Gungraun then
//! measures one of the typed `PreparedRuntimeWorkload::run_*` methods; the profile runner uses the
//! same prepared work without Valgrind and asks the session for instruction counts.

#![allow(dead_code)] // each of the two importing binaries uses a different half of this module

use std::hint::black_box;

use ferlium::{
    CompilerSession, ExecutionTarget, MirOptimization, Path,
    hir::value::Value,
    mir::profile::MirExecutionProfile,
    module::{LocalFunctionId, ModuleId},
    std::{array::array_value_from_vec, math::Float, string::String as Str},
};

/// Runtime artifact stage selected by the benchmark or profiler.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BenchTarget {
    Hir,
    Mir,
    OptimizedMir,
}

impl BenchTarget {
    pub const ALL: [Self; 3] = [Self::Hir, Self::Mir, Self::OptimizedMir];

    pub fn target(self) -> ExecutionTarget {
        match self {
            Self::Hir => ExecutionTarget::Hir,
            Self::Mir | Self::OptimizedMir => ExecutionTarget::Mir,
        }
    }

    pub fn optimization(self) -> MirOptimization {
        match self {
            Self::Hir | Self::Mir => MirOptimization::Disabled,
            Self::OptimizedMir => MirOptimization::Enabled,
        }
    }

    pub fn session(self) -> CompilerSession {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(self.optimization());
        session
    }
}

/// The runtime suite's canonical workloads and inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeWorkload {
    Quicksort,
    Fibonacci,
    Sieve,
    RleEncode,
    Csv,
    BankAccount,
    Sudoku,
    Calculator,
    LinalgTransform,
    LinalgGrid,
}

impl RuntimeWorkload {
    pub const ALL: [Self; 10] = [
        Self::Quicksort,
        Self::Fibonacci,
        Self::Sieve,
        Self::RleEncode,
        Self::Csv,
        Self::BankAccount,
        Self::Sudoku,
        Self::Calculator,
        Self::LinalgTransform,
        Self::LinalgGrid,
    ];

    pub const fn name(self) -> &'static str {
        match self {
            Self::Quicksort => "quicksort",
            Self::Fibonacci => "fibonacci",
            Self::Sieve => "sieve",
            Self::RleEncode => "rle_encode",
            Self::Csv => "csv",
            Self::BankAccount => "bank_account",
            Self::Sudoku => "sudoku",
            Self::Calculator => "calculator",
            Self::LinalgTransform => "linalg_transform",
            Self::LinalgGrid => "linalg_grid",
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|workload| workload.name() == name)
    }

    pub fn prepare(self, target: BenchTarget) -> PreparedRuntimeWorkload {
        match self {
            Self::Quicksort => prepare_quicksort(target),
            Self::Fibonacci => prepare_single_module(
                target,
                "fibonacci",
                include_str!("../tests/modules/fibonacci.fer"),
                "fibonacci_rec",
                RuntimeArguments::Int(20),
            ),
            Self::Sieve => prepare_single_module(
                target,
                "sieve",
                include_str!("../tests/modules/sieve.fer"),
                "prime_count",
                RuntimeArguments::Int(500),
            ),
            Self::RleEncode => prepare_single_module(
                target,
                "rle_encode",
                include_str!("../tests/modules/rle_encode.fer"),
                "rle_encode_string",
                RuntimeArguments::String(Str::new(&"aabccccccc".repeat(50))),
            ),
            Self::Csv => prepare_single_module(
                target,
                "csv",
                include_str!("../tests/modules/csv.fer"),
                "csv_table",
                RuntimeArguments::Int(500),
            ),
            Self::BankAccount => prepare_bank_account(target),
            Self::Sudoku => prepare_single_module(
                target,
                "sudoku",
                include_str!("../tests/modules/sudoku.fer"),
                "solved_cell",
                RuntimeArguments::IntPair(0, 2),
            ),
            Self::Calculator => prepare_single_module(
                target,
                "calculator",
                include_str!("../tests/modules/calculator.fer"),
                "calculate",
                RuntimeArguments::String(Str::new("((1 + 2) * (3 + 4) - 5) * 6 / 2 + 100")),
            ),
            Self::LinalgTransform => {
                prepare_linalg(target, "transform_pipeline_mixed", RuntimeArguments::Int(6))
            }
            Self::LinalgGrid => {
                prepare_linalg(target, "grid_simulation", RuntimeArguments::IntPair(8, 2))
            }
        }
    }
}

/// One fully compiled workload. Arguments are owned because MIR entry execution consumes them.
pub struct PreparedRuntimeWorkload {
    pub target: ExecutionTarget,
    pub session: CompilerSession,
    pub module_id: ModuleId,
    pub entry: LocalFunctionId,
    arguments: Option<RuntimeArguments>,
}

enum RuntimeArguments {
    None,
    Int(isize),
    IntPair(isize, isize),
    String(Str),
    IntArray(Vec<isize>),
}

impl RuntimeArguments {
    fn into_values(self) -> Vec<Value> {
        match self {
            Self::None => vec![],
            Self::Int(value) => vec![Value::native(black_box(value))],
            Self::IntPair(first, second) => vec![
                Value::native(black_box(first)),
                Value::native(black_box(second)),
            ],
            Self::String(value) => vec![Value::native(value)],
            Self::IntArray(values) => vec![int_a(values)],
        }
    }
}

impl PreparedRuntimeWorkload {
    fn take_arguments(&mut self) -> Vec<Value> {
        self.arguments
            .take()
            .expect("a prepared runtime workload can only be run once")
            .into_values()
    }

    fn run_entry(&mut self) -> Value {
        let arguments = self.take_arguments();
        self.session
            .run_entry(self.target, self.module_id, self.entry, arguments)
            .unwrap()
    }

    pub fn run_value(&mut self) -> Value {
        self.run_entry()
    }

    pub fn run_int(&mut self) -> isize {
        self.run_entry().into_primitive_ty::<isize>().unwrap()
    }

    pub fn run_float(&mut self) -> Float {
        self.run_entry().into_primitive_ty::<Float>().unwrap()
    }

    pub fn run_string(&mut self) -> Str {
        self.run_entry().into_primitive_ty::<Str>().unwrap()
    }

    pub fn run_profiled(&mut self) -> (Value, MirExecutionProfile) {
        let arguments = self.take_arguments();
        self.session
            .run_mir_entry_profiled(self.module_id, self.entry, arguments)
            .unwrap()
    }
}

fn prepare_single_module(
    target: BenchTarget,
    name: &str,
    source: &str,
    function_name: &str,
    arguments: RuntimeArguments,
) -> PreparedRuntimeWorkload {
    let mut session = target.session();
    let module_id = session
        .compile_for(
            target.target(),
            source,
            &format!("{name}.fer"),
            Path::single_str(name),
        )
        .unwrap()
        .module_id;
    prepare_entry(
        target.target(),
        session,
        module_id,
        function_name,
        arguments,
    )
}

fn prepare_entry(
    target: ExecutionTarget,
    mut session: CompilerSession,
    module_id: ModuleId,
    function_name: &str,
    arguments: RuntimeArguments,
) -> PreparedRuntimeWorkload {
    let entry = session
        .expect_fresh_module(module_id)
        .get_local_function_id(ferlium::ustr(function_name))
        .unwrap_or_else(|| panic!("function {function_name} not found"));
    session.prepare_execution_target(target, module_id);
    PreparedRuntimeWorkload {
        target,
        session,
        module_id,
        entry,
        arguments: Some(arguments),
    }
}

fn prepare_quicksort(target: BenchTarget) -> PreparedRuntimeWorkload {
    let data = lcg_seq(300, 42);
    prepare_single_module(
        target,
        "quicksort",
        include_str!("../tests/modules/quicksort.fer"),
        "quicksort_int_a",
        RuntimeArguments::IntArray(data),
    )
}

fn prepare_bank_account(target: BenchTarget) -> PreparedRuntimeWorkload {
    use indoc::indoc;

    let mut session = target.session();
    session
        .compile_for(
            target.target(),
            include_str!("../tests/modules/quicksort.fer"),
            "quicksort.fer",
            Path::single_str("quicksort"),
        )
        .unwrap();
    session
        .compile_for(
            target.target(),
            include_str!("../tests/modules/bank_account.fer"),
            "bank_account.fer",
            Path::single_str("account"),
        )
        .unwrap();
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
    prepare_entry(
        target.target(),
        session,
        module_id,
        "test",
        RuntimeArguments::None,
    )
}

fn prepare_linalg(
    target: BenchTarget,
    function_name: &str,
    arguments: RuntimeArguments,
) -> PreparedRuntimeWorkload {
    let mut session = target.session();
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
    prepare_entry(
        target.target(),
        session,
        module_id,
        function_name,
        arguments,
    )
}

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
