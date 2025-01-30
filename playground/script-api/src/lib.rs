use wasm_bindgen::prelude::*;

pub use painturscript::Compiler;

#[wasm_bindgen]
pub fn init_rust_api() {
    set_panic_hook();
    wasm_logger::init(wasm_logger::Config::default());
    log::info!("Rust API logging enabled.");
}

pub fn set_panic_hook() {
    // When the `console_error_panic_hook` feature is enabled, we can call the
    // `set_panic_hook` function at least once during initialization, and then
    // we will get better error messages if our code ever panics.
    console_error_panic_hook::set_once();
}