install-deps:
	cargo install cargo-nextest --locked

test:
	RUST_LOG=painturscript=debug cargo nextest run

repl:
	RUST_BACKTRACE=1 RUST_LOG=painturscript=debug cargo run --example pscript