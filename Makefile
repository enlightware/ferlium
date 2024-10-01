install-deps:
	cargo install cargo-nextest --locked

test-local:
	RUST_LOG=painturscript=debug cargo nextest run

test-wasm:
	wasm-pack test --node --test simple --test complex --test algorithm --lib

test: test-local test-wasm

repl:
	RUST_BACKTRACE=1 RUST_LOG=painturscript=debug cargo run --example pscript