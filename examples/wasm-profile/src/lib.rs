// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Node-facing driver for the shared runtime workload corpus.
#![cfg(target_arch = "wasm32")]

#[path = "../../../benches/runtime_workloads.rs"]
mod runtime_workloads;

use ferlium::{
    compiler::bench_support::reset_initial_session_state_cache,
    std::math::Float,
    wasm::{CompiledProgram, Instance, WasmLimits},
};
use runtime_workloads::{BenchTarget, PreparedRuntimeWorkload, RuntimeWorkload, WasmRuntimeResult};
use wasm_bindgen::prelude::*;

/// Post-expansion optimization is the axis the Callgrind benchmark varies.
fn bench_target(optimized: bool) -> BenchTarget {
    if optimized {
        BenchTarget::PhysicalMir
    } else {
        BenchTarget::UnoptimizedPhysicalMir
    }
}

enum WorkloadInstance {
    Int(Instance<(), isize>),
    Float(Instance<(), Float>),
}

#[wasm_bindgen]
pub struct Workload {
    program: CompiledProgram,
    prepared: PreparedRuntimeWorkload,
    result: WasmRuntimeResult,
    expected: f64,
    instance: Option<WorkloadInstance>,
}

#[wasm_bindgen]
impl Workload {
    /// Compile one shared runtime workload using physical MIR.
    #[wasm_bindgen(constructor)]
    pub fn new(name: &str, optimized: bool) -> Result<Workload, JsValue> {
        let workload = RuntimeWorkload::from_name(name)
            .ok_or_else(|| JsValue::from_str(&format!("unknown runtime workload `{name}`")))?;
        let prepared = workload.prepare_wasm(bench_target(optimized));
        Ok(Self {
            program: prepared.program,
            prepared: prepared.prepared,
            result: prepared.result,
            expected: prepared.expected,
            instance: None,
        })
    }

    /// Keep engine compilation/instantiation separate from Ferlium compilation in the timings.
    pub fn instantiate(&mut self) -> Result<(), JsValue> {
        self.instance = Some(match self.result {
            WasmRuntimeResult::Int => WorkloadInstance::Int(
                self.program
                    .instantiate()
                    .map_err(|error| JsValue::from_str(&format!("{error:?}")))?,
            ),
            WasmRuntimeResult::Float => WorkloadInstance::Float(
                self.program
                    .instantiate()
                    .map_err(|error| JsValue::from_str(&format!("{error:?}")))?,
            ),
        });
        Ok(())
    }

    pub fn run(&mut self) -> Result<f64, JsValue> {
        let instance = self
            .instance
            .as_mut()
            .ok_or_else(|| JsValue::from_str("instantiate first"))?;
        match instance {
            WorkloadInstance::Int(instance) => instance
                .run((), WasmLimits::default())
                .map(|result| result as f64),
            WorkloadInstance::Float(instance) => instance
                .run((), WasmLimits::default())
                .map(Float::into_inner),
        }
        .map_err(|error| JsValue::from_str(&format!("{error:?}")))
    }

    /// Run the same workload through the physical MIR interpreter instead of generated Wasm.
    pub fn run_mir(&mut self) -> f64 {
        match self.result {
            WasmRuntimeResult::Int => self.prepared.run_int() as f64,
            WasmRuntimeResult::Float => self.prepared.run_float().into_inner(),
        }
    }

    pub fn code_bytes(&self) -> usize {
        self.program.bytes().len()
    }

    pub fn expected(&self) -> f64 {
        self.expected
    }
}

/// Lower std alone, so that workload compilations measured afterwards reuse its artifacts.
#[wasm_bindgen]
pub fn prepare_std(optimized: bool) -> Result<(), JsValue> {
    bench_target(optimized)
        .session()
        .prepare_std_artifacts()
        .map_err(|error| JsValue::from_str(&format!("{error:?}")))
}

/// Discard the cached pristine session state left by an unmeasured warmup.
#[wasm_bindgen]
pub fn reset_std_cache() {
    reset_initial_session_state_cache();
}

/// Newline-separated workload names, kept in the shared corpus definition.
#[wasm_bindgen]
pub fn workload_names() -> String {
    RuntimeWorkload::ALL
        .into_iter()
        .map(RuntimeWorkload::name)
        .collect::<Vec<_>>()
        .join("\n")
}
