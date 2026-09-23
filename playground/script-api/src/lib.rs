// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{panic, sync::Once};

use wasm_bindgen::prelude::*;

use ferlium::ide::PositionEncoding;
use ferlium::{
    hir::native_functions::NativeFnR,
    module::{Module, ModuleId, UseData, Uses},
    std::string::String as FerliumString,
    types::effects::effect_write,
    ustr, CompilerSession, Location, Path,
};

pub use ferlium::ide::ExecutionResult;
pub use ferlium::ide::{
    AnnotationData, CompilationReport, ErrorData, ExecutionErrorData, IrText, TextSourceMapEntry,
};

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

        let mut inner = ferlium::Compiler::new_with_session_and_uses(session, uses);
        // CodeMirror addresses JavaScript strings in UTF-16 code units.
        inner.set_position_encoding(PositionEncoding::Utf16CodeUnit);
        Self { inner }
    }

    pub fn compile(&mut self, src: &str) -> CompilationReport {
        self.inner.compile_report(src)
    }

    pub fn run_expr(&mut self) -> Option<ExecutionResult> {
        self.inner.run_expr()
    }

    pub fn run_expr_mir(&mut self, optimized: bool) -> Option<ExecutionResult> {
        self.inner.run_expr_mir(optimized)
    }

    pub fn mir_text(&mut self, optimized: bool) -> IrText {
        self.inner.mir_text(optimized)
    }

    pub fn run_expr_physical_mir(&mut self) -> Option<ExecutionResult> {
        self.inner.run_expr_physical_mir()
    }

    pub fn physical_mir_text(&mut self) -> Result<IrText, String> {
        self.inner.physical_mir_text()
    }

    #[cfg(target_arch = "wasm32")]
    pub fn wasm_text(&mut self) -> Result<IrText, String> {
        self.inner.wasm_text()
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
    wasm_logger::init(wasm_logger::Config::new(log::Level::Debug).module_prefix("ferlium"));
    log::info!("Rust API logging enabled.");
}

pub fn set_panic_hook() {
    // Log panics to the browser console, and tell the playground, which reloads the page to replace
    // this instance, as a panic aborts it.
    static SET_HOOK: Once = Once::new();
    SET_HOOK.call_once(|| {
        panic::set_hook(Box::new(|info| {
            console_error_panic_hook::hook(info);
            notify_panic(&info.to_string());
        }));
    });
}

/// Listened to by `App.vue` in the playground, keep in sync.
#[cfg(target_arch = "wasm32")]
const PANIC_EVENT: &str = "ferlium-panic";

/// Synchronously dispatch the panic event on the window, with the message as detail.
#[cfg(target_arch = "wasm32")]
fn notify_panic(message: &str) {
    let Some(window) = web_sys::window() else {
        return;
    };
    let init = web_sys::CustomEventInit::new();
    init.set_detail(&JsValue::from_str(message));
    if let Ok(event) = web_sys::CustomEvent::new_with_event_init_dict(PANIC_EVENT, &init) {
        // Nothing more can be done if dispatching fails; the message is in the console anyway.
        let _ = window.dispatch_event(&event);
    }
}

#[cfg(not(target_arch = "wasm32"))]
fn notify_panic(_message: &str) {}

extern "C" fn console_print(message: &FerliumString) {
    append_to_playground_console(message.as_ref());
}

fn console_module(module_id: ModuleId) -> Module {
    let mut module = Module::new(module_id, Path::single_str("console"));
    module.add_function(
        ustr("print"),
        NativeFnR::new(console_print).description(
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

#[cfg(all(test, target_arch = "wasm32"))]
mod tests {
    use super::*;
    use wasm_bindgen_test::*;

    wasm_bindgen_test_configure!(run_in_browser);

    #[wasm_bindgen_test]
    fn physical_mir_inspection_and_execution_in_browser() {
        set_panic_hook();
        let mut compiler = PlaygroundCompiler::new();
        let source = "// 😀\nfn second(pair: (int, bool)) -> bool { pair.1 } second((42, true))";
        assert!(compiler.compile(source).succeeded);
        let physical = compiler.physical_mir_text().unwrap();
        assert!(physical.text.contains("address_offset"));
        assert!(!physical.source_map.is_empty());
        assert!(physical.source_map.iter().all(|entry| {
            entry.from < entry.to
                && entry.to as usize <= physical.text.encode_utf16().count()
                && entry.source_from <= entry.source_to
                && entry.source_to as usize <= source.encode_utf16().count()
        }));
        assert_eq!(
            compiler.run_expr_physical_mir().unwrap().html_message(),
            "true: bool"
        );
        assert!(compiler.compile("40 + 2").succeeded);
        assert_eq!(
            compiler.run_expr_mir(true).unwrap().html_message(),
            "42: int"
        );
        assert_eq!(
            compiler.run_expr_physical_mir().unwrap().html_message(),
            "42: int"
        );
    }

    #[wasm_bindgen_test]
    fn wasm_inspection_in_browser() {
        set_panic_hook();
        let mut compiler = PlaygroundCompiler::new();
        let source = "// 😀\nfn triple(x: int) -> int { x * 3 }\ntriple(14)";
        assert!(compiler.compile(source).succeeded);
        let wasm = compiler.wasm_text().unwrap();
        assert!(
            wasm.text.contains("(export \"ide::triple\""),
            "{}",
            wasm.text
        );
        assert!(
            !wasm.text.contains("(export \"ide::<expr>\""),
            "{}",
            wasm.text
        );
        assert!(!wasm.source_map.is_empty());
        assert!(wasm.source_map.iter().all(|entry| {
            entry.from < entry.to
                && entry.to as usize <= wasm.text.encode_utf16().count()
                && entry.source_from <= entry.source_to
                && entry.source_to as usize <= source.encode_utf16().count()
        }));
    }
}
