install-deps:
	cargo install cargo-nextest --locked

test:
	cargo nextest run