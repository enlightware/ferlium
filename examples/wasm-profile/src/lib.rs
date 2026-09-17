// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Node-facing benchmark driver. Workload loops execute in generated Wasm, not in JavaScript.
#![cfg(target_arch = "wasm32")]

use ferlium::{
    CompilerSession,
    compiler::MirOptimization,
    module::{FunctionId, Path},
    ustr,
    wasm::{CompiledProgram, Instance, WasmLimits},
};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct Workload {
    program: CompiledProgram,
    instance: Option<Instance<(isize,), isize>>,
}

#[wasm_bindgen]
impl Workload {
    /// Compile `compute(iterations: int) -> int` using optimized physical MIR.
    #[wasm_bindgen(constructor)]
    pub fn new(source: &str) -> Result<Workload, JsValue> {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Enabled);
        let module = session
            .compile(source, "benchmark", Path::single(ustr("benchmark")))
            .map_err(|error| JsValue::from_str(&format!("{error:?}")))?
            .module_id;
        let function = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("compute"))
            .ok_or_else(|| JsValue::from_str("missing compute function"))?;
        let program = CompiledProgram::compile(&session, FunctionId::new(module, function))
            .map_err(|error| JsValue::from_str(&format!("{error:?}")))?;
        Ok(Self {
            program,
            instance: None,
        })
    }

    /// Keep engine compilation/instantiation separate from Ferlium compilation in the timings.
    pub fn instantiate(&mut self) -> Result<(), JsValue> {
        self.instance = Some(
            self.program
                .instantiate()
                .map_err(|error| JsValue::from_str(&format!("{error:?}")))?,
        );
        Ok(())
    }

    pub fn run(&mut self, iterations: i32) -> Result<i32, JsValue> {
        let result = self
            .instance
            .as_mut()
            .ok_or_else(|| JsValue::from_str("instantiate first"))?
            .run((iterations as isize,), WasmLimits::default())
            .map_err(|error| JsValue::from_str(&format!("{error:?}")))?;
        Ok(result as i32)
    }

    pub fn code_bytes(&self) -> usize {
        self.program.bytes().len()
    }
}
