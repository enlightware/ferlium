// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Terminal-independent Wasm REPL services; Node owns input and output.
#![cfg(target_arch = "wasm32")]

use ferlium::{
    Compiler, CompilerSession, Location, Path,
    execution::DEFAULT_INTERACTIVE_FUEL_LIMIT,
    ide::{CompilationReport, ExecutionResult, IrText, PositionEncoding},
    module::{UseData, Uses},
    repl,
    std::string::String as FerliumString,
};
use std::cell::RefCell;
use wasm_bindgen::prelude::*;

thread_local! {
    static OUTPUT: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

extern "C" fn print(message: &FerliumString) {
    OUTPUT.with(|output| output.borrow_mut().push(message.as_ref().to_string()));
}

#[wasm_bindgen]
pub struct Repl {
    compiler: Compiler,
    optimized: bool,
}

#[wasm_bindgen]
impl Repl {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        console_error_panic_hook::set_once();
        let mut session = CompilerSession::new();
        let path = Path::single_str("console");
        session.register_module(
            path.clone(),
            repl::console_module(session.modules().next_id(), print),
        );
        let mut uses = Uses::new_with_std();
        uses.wildcards
            .push(UseData::new(path, Location::new_synthesized()));
        let mut compiler = Compiler::new_with_session_and_uses(session, uses);
        compiler.set_position_encoding(PositionEncoding::Utf16CodeUnit);
        Self {
            compiler,
            optimized: true,
        }
    }

    pub fn compile(&mut self, source: &str) -> CompilationReport {
        self.compiler.compile_repl_report(source)
    }

    pub fn run(&mut self) -> Option<ExecutionResult> {
        self.compiler.run_expr_wasm_optimized(self.optimized)
    }

    pub fn take_output(&self) -> Vec<String> {
        OUTPUT.with(|output| std::mem::take(&mut *output.borrow_mut()))
    }

    pub fn wasm_text(&mut self) -> Result<IrText, String> {
        self.compiler.wasm_text_optimized(self.optimized)
    }

    pub fn mir_text(&mut self, optimized: bool, module: Option<String>) -> Result<String, String> {
        self.compiler
            .repl_mir_text(module.as_deref(), optimized, false)
    }

    pub fn physical_mir_text(
        &mut self,
        raw: bool,
        module: Option<String>,
    ) -> Result<String, String> {
        self.compiler
            .repl_mir_text(module.as_deref(), self.optimized && !raw, true)
    }

    pub fn module_text(&self, name: Option<String>) -> Result<String, String> {
        self.compiler.repl_module_text(
            name.as_deref()
                .or((!self.compiler.repl_has_submission()).then_some("std")),
        )
    }

    pub fn function_text(&self, function: &str, module: Option<String>) -> Result<String, String> {
        self.compiler.repl_function_text(
            function,
            module.as_deref().or((!self.compiler.repl_has_submission()
                && repl::split_qualified_function_name(function).is_none())
            .then_some("std")),
        )
    }

    pub fn history_text(&self) -> String {
        self.compiler.repl_history_text()
    }

    pub fn set_optimized(&mut self, optimized: bool) {
        self.optimized = optimized;
    }

    pub fn set_fuel(&mut self, limit: u32) {
        self.compiler.set_execution_fuel_limit(limit);
    }

    pub fn disable_fuel(&mut self) {
        self.compiler.disable_execution_fuel_limit();
    }

    pub fn set_allow_experimental(&mut self, allow: bool) {
        self.compiler.set_allow_experimental(allow);
    }
}

impl Default for Repl {
    fn default() -> Self {
        Self::new()
    }
}

#[wasm_bindgen]
pub fn default_fuel_limit() -> u32 {
    DEFAULT_INTERACTIVE_FUEL_LIMIT as u32
}
