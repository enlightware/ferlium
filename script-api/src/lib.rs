mod utils;

use utils::set_panic_hook;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn replace_text(input: &str, search: &str, replace: &str) -> String {
    input.replace(search, replace)
}

#[wasm_bindgen]
pub fn init_rust_api() {
    set_panic_hook();
    wasm_logger::init(wasm_logger::Config::default());
    log::info!("Rust API logging enabled.");
}
