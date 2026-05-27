#![no_main]

use ferlium::{SourceId, module::id::Id, parse_module_and_expr};
use libfuzzer_sys::fuzz_target;

const MAX_INPUT_LEN: usize = 32 * 1024;

fuzz_target!(|data: &[u8]| {
    if data.len() > MAX_INPUT_LEN {
        return;
    }

    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };

    let _ = parse_module_and_expr(src, SourceId::from_index(0), false);
});
