// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Runtime workload definitions shared by the Gungraun harness and the fast MIR profile runner.
//!
//! Compilation and canonical inputs are prepared by [`RuntimeWorkload::prepare`]. Gungraun then
//! measures one of the typed `PreparedRuntimeWorkload::run_*` methods; the profile runner uses the
//! same prepared work without Valgrind and asks the session for instruction counts.

#![allow(dead_code)] // each of the two importing binaries uses a different half of this module

use ferlium::{
    CompilerSession, ExecutionTarget, MirOptimization, Path,
    hir::value::Value,
    mir::profile::MirExecutionProfile,
    module::{LocalFunctionId, ModuleId},
    std::math::Float,
};

#[cfg(target_arch = "wasm32")]
use ferlium::{module::FunctionId, wasm::CompiledProgram};

/// Runtime artifact stage selected by the benchmark or profiler.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BenchTarget {
    Hir,
    Mir,
    OptimizedMir,
    UnoptimizedPhysicalMir,
    PhysicalMir,
}

impl BenchTarget {
    pub const ALL: [Self; 3] = [Self::Hir, Self::Mir, Self::OptimizedMir];

    pub fn target(self) -> ExecutionTarget {
        match self {
            Self::Hir => ExecutionTarget::Hir,
            Self::Mir | Self::OptimizedMir => ExecutionTarget::Mir,
            Self::PhysicalMir | Self::UnoptimizedPhysicalMir => ExecutionTarget::PhysicalMir,
        }
    }

    pub fn optimization(self) -> MirOptimization {
        match self {
            Self::Hir | Self::Mir => MirOptimization::Disabled,
            Self::OptimizedMir | Self::PhysicalMir | Self::UnoptimizedPhysicalMir => {
                MirOptimization::Enabled
            }
        }
    }

    pub fn session(self) -> CompilerSession {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(self.optimization());
        session.set_physical_mir_optimization(if self == Self::UnoptimizedPhysicalMir {
            MirOptimization::Disabled
        } else {
            MirOptimization::Enabled
        });
        session
    }
}

#[derive(Clone, Copy)]
struct ModuleSource {
    name: &'static str,
    source: &'static str,
}

const BANK_ACCOUNT_DEPENDENCIES: &[ModuleSource] = &[
    ModuleSource {
        name: "quicksort",
        source: include_str!("../tests/modules/quicksort.fer"),
    },
    ModuleSource {
        name: "account",
        source: include_str!("../tests/modules/bank_account.fer"),
    },
];

/// One canonical runtime workload and everything needed to compile its scalar benchmark entry.
#[derive(Clone, Copy)]
pub struct RuntimeWorkload {
    name: &'static str,
    module_name: &'static str,
    workload_source: &'static str,
    benchmark_source: &'static str,
    dependencies: &'static [ModuleSource],
    result: RuntimeResult,
    expected: f64,
    experimental: bool,
}

impl RuntimeWorkload {
    pub const QUICKSORT: Self = Self::single(
        "quicksort",
        include_str!("../tests/modules/quicksort.fer"),
        include_str!("runtime/quicksort.fer"),
        RuntimeResult::Int,
        8_259_661.0,
    );
    pub const FIBONACCI: Self = Self::single(
        "fibonacci",
        include_str!("../tests/modules/fibonacci.fer"),
        include_str!("runtime/fibonacci.fer"),
        RuntimeResult::Int,
        6_765.0,
    );
    pub const SIEVE: Self = Self::single(
        "sieve",
        include_str!("../tests/modules/sieve.fer"),
        include_str!("runtime/sieve.fer"),
        RuntimeResult::Int,
        95.0,
    );
    pub const RLE_ENCODE: Self = Self::single(
        "rle_encode",
        include_str!("../tests/modules/rle_encode.fer"),
        include_str!("runtime/rle_encode.fer"),
        RuntimeResult::Int,
        300.0,
    );
    pub const CSV: Self = Self::single(
        "csv",
        include_str!("../tests/modules/csv.fer"),
        include_str!("runtime/csv.fer"),
        RuntimeResult::Int,
        9_340.0,
    );
    pub const BANK_ACCOUNT: Self = Self {
        name: "bank_account",
        module_name: "bank_account_benchmark",
        workload_source: "",
        benchmark_source: include_str!("runtime/bank_account.fer"),
        dependencies: BANK_ACCOUNT_DEPENDENCIES,
        result: RuntimeResult::Int,
        expected: 3.0,
        experimental: false,
    };
    pub const SUDOKU: Self = Self::single(
        "sudoku",
        include_str!("../tests/modules/sudoku.fer"),
        include_str!("runtime/sudoku.fer"),
        RuntimeResult::Int,
        4.0,
    );
    pub const CALCULATOR: Self = Self::single(
        "calculator",
        include_str!("../tests/modules/calculator.fer"),
        include_str!("runtime/calculator.fer"),
        RuntimeResult::Int,
        148.0,
    );
    pub const LINALG_TRANSFORM: Self = Self::single(
        "linalg_transform",
        include_str!("../tests/modules/linalg.fer"),
        include_str!("runtime/linalg_transform.fer"),
        RuntimeResult::Int,
        416.0,
    )
    .experimental();
    pub const LINALG_GRID: Self = Self::single(
        "linalg_grid",
        include_str!("../tests/modules/linalg.fer"),
        include_str!("runtime/linalg_grid.fer"),
        RuntimeResult::Float,
        114_176.720_214_843_75,
    )
    .experimental();
    pub const ITER_PIPELINE: Self = Self::single(
        "iter_pipeline",
        include_str!("../tests/modules/iter_pipeline.fer"),
        include_str!("runtime/iter_pipeline.fer"),
        RuntimeResult::Int,
        4_195.0,
    );
    pub const DATA_TEXT_ROUNDTRIP: Self = Self::single(
        "data_text_roundtrip",
        include_str!("../tests/modules/data_text.fer"),
        include_str!("runtime/data_text_roundtrip.fer"),
        RuntimeResult::Int,
        569.0,
    );

    pub const ALL: [Self; 12] = [
        Self::QUICKSORT,
        Self::FIBONACCI,
        Self::SIEVE,
        Self::RLE_ENCODE,
        Self::CSV,
        Self::BANK_ACCOUNT,
        Self::SUDOKU,
        Self::CALCULATOR,
        Self::LINALG_TRANSFORM,
        Self::LINALG_GRID,
        Self::ITER_PIPELINE,
        Self::DATA_TEXT_ROUNDTRIP,
    ];

    pub const fn name(self) -> &'static str {
        self.name
    }

    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|workload| workload.name() == name)
    }

    /// Canonical scalar checksum produced by the benchmark entry.
    pub const fn expected(self) -> f64 {
        self.expected
    }

    /// Checks a boxed interpreter result outside the measured workload.
    pub fn assert_value(self, value: &Value) {
        let actual = match self.result {
            RuntimeResult::Int => *value
                .as_primitive_ty::<isize>()
                .expect("integer benchmark entry returned another type")
                as f64,
            RuntimeResult::Float => value
                .as_primitive_ty::<Float>()
                .expect("float benchmark entry returned another type")
                .into_inner(),
        };
        assert_eq!(
            actual, self.expected,
            "benchmark `{}` produced the wrong checksum",
            self.name
        );
    }

    pub fn prepare(self, target: BenchTarget) -> PreparedRuntimeWorkload {
        let (session, module_id) = compile_workload(target, self);
        prepare_entry(target.target(), session, module_id, self.result)
    }

    /// Compile the canonical workload behind a parameterless, scalar-result Wasm entry.
    ///
    /// Inputs are constructed inside generated code and passed through `std::black_box`, keeping
    /// their representation opaque without exposing workload-specific types to the host bridge.
    /// Aggregate and string results are reduced to a deterministic scalar after the workload has
    /// produced them.
    #[cfg(target_arch = "wasm32")]
    pub fn prepare_wasm(self, target: BenchTarget) -> PreparedWasmRuntimeWorkload {
        let prepared = self.prepare(target);
        let program = CompiledProgram::compile(
            &prepared.session,
            FunctionId::new(prepared.module_id, prepared.entry),
        )
        .unwrap_or_else(|error| panic!("failed to emit {}: {error:?}", self.name()));
        PreparedWasmRuntimeWorkload {
            program,
            result: prepared.result.wasm_transport(),
            prepared,
            expected: self.expected,
        }
    }

    const fn single(
        name: &'static str,
        workload_source: &'static str,
        benchmark_source: &'static str,
        result: RuntimeResult,
        expected: f64,
    ) -> Self {
        Self {
            name,
            module_name: name,
            workload_source,
            benchmark_source,
            dependencies: &[],
            result,
            expected,
            experimental: false,
        }
    }

    const fn experimental(mut self) -> Self {
        self.experimental = true;
        self
    }
}

/// Scalar transport used by a generated Wasm benchmark entry.
#[cfg(target_arch = "wasm32")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WasmRuntimeResult {
    Int,
    Float,
}

/// One emitted workload, before engine compilation and instantiation.
#[cfg(target_arch = "wasm32")]
pub struct PreparedWasmRuntimeWorkload {
    pub program: CompiledProgram,
    pub prepared: PreparedRuntimeWorkload,
    pub result: WasmRuntimeResult,
    pub expected: f64,
}

const BENCHMARK_ENTRY: &str = "benchmark_entry";

#[derive(Clone, Copy)]
enum RuntimeResult {
    Int,
    Float,
}

impl RuntimeResult {
    #[cfg(target_arch = "wasm32")]
    fn wasm_transport(self) -> WasmRuntimeResult {
        match self {
            Self::Float => WasmRuntimeResult::Float,
            Self::Int => WasmRuntimeResult::Int,
        }
    }
}

fn compile_workload(target: BenchTarget, workload: RuntimeWorkload) -> (CompilerSession, ModuleId) {
    let mut session = target.session();
    session.set_allow_experimental(workload.experimental);
    for dependency in workload.dependencies {
        session
            .compile_for(
                target.target(),
                dependency.source,
                &format!("{}.fer", dependency.name),
                Path::single_str(dependency.name),
            )
            .unwrap_or_else(|error| {
                panic!(
                    "failed to compile {} dependency {}: {error:?}",
                    workload.name, dependency.name
                )
            });
    }
    let source = format!(
        "{}\n{}",
        workload.workload_source, workload.benchmark_source
    );
    let module_id = session
        .compile_for(
            target.target(),
            &source,
            &format!("{}.fer", workload.name),
            Path::single_str(workload.module_name),
        )
        .unwrap_or_else(|error| panic!("failed to compile {}: {error:?}", workload.name))
        .module_id;
    (session, module_id)
}

/// One fully compiled parameterless workload.
pub struct PreparedRuntimeWorkload {
    pub target: ExecutionTarget,
    pub session: CompilerSession,
    pub module_id: ModuleId,
    pub entry: LocalFunctionId,
    result: RuntimeResult,
}

impl PreparedRuntimeWorkload {
    fn run_entry(&mut self) -> Value {
        self.session
            .run_entry(self.target, self.module_id, self.entry, vec![])
            .unwrap()
    }

    pub fn run_int(&mut self) -> isize {
        self.run_entry().into_primitive_ty::<isize>().unwrap()
    }

    pub fn run_float(&mut self) -> Float {
        self.run_entry().into_primitive_ty::<Float>().unwrap()
    }

    pub fn run_profiled(&mut self) -> (Value, MirExecutionProfile) {
        if self.target == ExecutionTarget::PhysicalMir {
            return self
                .session
                .run_physical_mir_entry_profiled(self.module_id, self.entry, vec![])
                .unwrap();
        }
        self.session
            .run_mir_entry_profiled(self.module_id, self.entry, vec![])
            .unwrap()
    }
}

fn prepare_entry(
    target: ExecutionTarget,
    mut session: CompilerSession,
    module_id: ModuleId,
    result: RuntimeResult,
) -> PreparedRuntimeWorkload {
    let entry = session
        .expect_fresh_module(module_id)
        .get_local_function_id(ferlium::ustr(BENCHMARK_ENTRY))
        .expect("benchmark wrapper must define its entry");
    session.prepare_execution_target(target, module_id);
    PreparedRuntimeWorkload {
        target,
        session,
        module_id,
        entry,
        result,
    }
}
