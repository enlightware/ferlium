#![no_main]

use libfuzzer_sys::fuzz_target;

const MAX_INPUT_LEN: usize = 32 * 1024;

fuzz_target!(|data: &[u8]| {
    if data.len() > MAX_INPUT_LEN {
        return;
    }

    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };

    let mut compiler = ferlium::Compiler::new();
    let _ = compiler.compile(src);
});
