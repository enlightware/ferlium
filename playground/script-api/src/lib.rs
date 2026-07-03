// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use wasm_bindgen::prelude::*;

use ferlium::{
    hir::function::UnaryNativeFnRN,
    module::{Module, ModuleId, UseData, Uses},
    std::string::String as FerliumString,
    types::effects::effect_write,
    ustr, CompilerSession, Location, Path,
};

pub use ferlium::ide::ExecutionResult;
pub use ferlium::ide::{AnnotationData, ErrorData, ExecutionErrorData};

#[wasm_bindgen]
pub struct PlaygroundCompiler {
    inner: ferlium::Compiler,
}

#[wasm_bindgen]
impl PlaygroundCompiler {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        let mut session = CompilerSession::new();
        session.register_module(
            Path::single_str("console"),
            console_module(session.modules().next_id()),
        );

        let mut uses = Uses::new_with_std();
        uses.wildcards.push(UseData::new(
            Path::single_str("console"),
            Location::new_synthesized(),
        ));

        Self {
            inner: ferlium::Compiler::new_with_session_and_uses(session, uses),
        }
    }

    pub fn compile(&mut self, src: &str) -> Option<Vec<ErrorData>> {
        self.inner.compile(src)
    }

    pub fn run_expr(&mut self) -> Option<ExecutionResult> {
        self.inner.run_expr()
    }

    pub fn get_annotations(&mut self) -> Vec<AnnotationData> {
        self.inner.get_annotations()
    }

    pub fn get_light_annotations(&mut self) -> Vec<AnnotationData> {
        self.inner.get_light_annotations()
    }

    pub fn set_allow_experimental(&mut self, allow: bool) {
        self.inner.set_allow_experimental(allow);
    }
}

impl Default for PlaygroundCompiler {
    fn default() -> Self {
        Self::new()
    }
}

#[wasm_bindgen]
pub fn init_rust_api() {
    set_panic_hook();
    wasm_logger::init(wasm_logger::Config::new(log::Level::Debug));
    log::info!("Rust API logging enabled.");
}

pub fn set_panic_hook() {
    // When the `console_error_panic_hook` feature is enabled, we can call the
    // `set_panic_hook` function at least once during initialization, and then
    // we will get better error messages if our code ever panics.
    console_error_panic_hook::set_once();
}

fn console_print(message: &FerliumString) {
    append_to_playground_console(message.as_ref());
}

fn console_module(module_id: ModuleId) -> Module {
    let mut module = Module::new(module_id, Path::single_str("console"));
    module.add_function(
        ustr("print"),
        UnaryNativeFnRN::description_with_default_ty(
            console_print,
            ["message"],
            "Prints `message` to the playground console.",
            effect_write(),
        ),
    );
    module
}

#[cfg(target_arch = "wasm32")]
fn append_to_playground_console(text: &str) {
    let Some(window) = web_sys::window() else {
        return;
    };
    let Some(document) = window.document() else {
        return;
    };
    let Some(console) = document.get_element_by_id("console-output") else {
        return;
    };
    if console.has_child_nodes() {
        console
            .append_child(&document.create_text_node("\n"))
            .expect("failed to append newline to playground console");
    }
    console
        .append_child(&document.create_text_node(text))
        .expect("failed to append text to playground console");
}

#[cfg(not(target_arch = "wasm32"))]
fn append_to_playground_console(_text: &str) {}
