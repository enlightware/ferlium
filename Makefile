install-deps:
	cargo install cargo-nextest --locked

test-local:
	RUST_LOG=ferlium=debug cargo nextest run

test-wasm:
	WASM_BINDGEN_USE_BROWSER=1 wasm-pack test --chrome --firefox --headless --test language --lib

test: test-local test-wasm

repl:
	RUST_BACKTRACE=1 RUST_LOG=ferlium=debug cargo run --example ferlium

book-devel:
	cargo install mdbook
	mdbook serve --open docs/book/en

validate-book:
	cargo run --example validate_book docs/book/en/

update-license-headers:
	licensure --in-place `find . -name "*.rs"`
	licensure --in-place `find playground/src -name "*.ts"` playground/*.ts