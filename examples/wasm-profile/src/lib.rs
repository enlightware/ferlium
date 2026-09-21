// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Node-facing driver for the shared runtime workload corpus.
#![cfg(target_arch = "wasm32")]

#[path = "../../../benches/runtime_workloads.rs"]
mod runtime_workloads;

use ferlium::{
    std::math::Float,
    wasm::{CompiledProgram, Instance, WasmLimits},
};
use runtime_workloads::{RuntimeWorkload, WasmRuntimeResult};
use wasm_bindgen::prelude::*;

enum WorkloadInstance {
    Int(Instance<(), isize>),
    Float(Instance<(), Float>),
}

#[wasm_bindgen]
pub struct Workload {
    program: CompiledProgram,
    result: WasmRuntimeResult,
    expected: f64,
    instance: Option<WorkloadInstance>,
}

#[wasm_bindgen]
impl Workload {
    /// Compile one shared runtime workload using optimized physical MIR.
    #[wasm_bindgen(constructor)]
    pub fn new(name: &str) -> Result<Workload, JsValue> {
        let workload = RuntimeWorkload::from_name(name)
            .ok_or_else(|| JsValue::from_str(&format!("unknown runtime workload `{name}`")))?;
        let prepared = workload.prepare_wasm();
        Ok(Self {
            program: prepared.program,
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

    pub fn code_bytes(&self) -> usize {
        self.program.bytes().len()
    }

    pub fn expected(&self) -> f64 {
        self.expected
    }
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
