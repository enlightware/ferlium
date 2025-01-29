install-deps:
	cargo install cargo-nextest --locked

test-local:
	RUST_LOG=ferlium=debug cargo nextest run

test-wasm:
	wasm-pack test --node --test language --lib

test: test-local test-wasm

repl:
	RUST_BACKTRACE=1 RUST_LOG=ferlium=debug cargo run --example ferlium

update-license-headers:
	licensure --in-place `find . -name "*.rs"`