install-deps:
	cargo install cargo-nextest --locked

test:
	RUST_LOG=painturscript=debug cargo nextest run
	wasm-pack test --node --test simple --test complex --test algorithm --lib

repl:
	RUST_BACKTRACE=1 RUST_LOG=painturscript=debug cargo run --example pscript