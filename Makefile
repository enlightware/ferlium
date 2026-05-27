# Fuzzing duration in seconds
FUZZ_TIME ?= 30
# Number of parallel libFuzzer workers. Defaults to the online CPU count on Linux.
FUZZ_JOBS ?= $(shell nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)

install-deps:
	cargo install cargo-nextest --locked
	cargo install --version 0.18.2 gungraun-runner

test-local:
	RUST_LOG=ferlium=debug cargo nextest run

test-wasm:
	WASM_BINDGEN_USE_BROWSER=1 wasm-pack test --chrome --firefox --headless --test language --lib

test: test-local test-wasm

test-miri:
	cargo +nightly miri test hir::value::tests::discard_storage_recursively_reclaims_runtime_payloads --lib

bench:
	cargo bench

fuzz-parse:
	mkdir -p fuzz/corpus-generated/parse_any
	ASAN_OPTIONS=detect_leaks=0 cargo +nightly fuzz run parse_any fuzz/corpus-generated/parse_any fuzz/corpus/parse_any -- -max_total_time=$(FUZZ_TIME) -jobs=$(FUZZ_JOBS) -workers=$(FUZZ_JOBS)

fuzz-ide:
	mkdir -p fuzz/corpus-generated/ide_compile_any
	ASAN_OPTIONS=detect_leaks=0 cargo +nightly fuzz run ide_compile_any fuzz/corpus-generated/ide_compile_any fuzz/corpus/programs fuzz/corpus/diagnostics -- -max_total_time=$(FUZZ_TIME) -jobs=$(FUZZ_JOBS) -workers=$(FUZZ_JOBS)

fuzz-grammar:
	mkdir -p fuzz/corpus-generated/grammar_ide_compile
	ASAN_OPTIONS=detect_leaks=0 cargo +nightly fuzz run grammar_ide_compile fuzz/corpus-generated/grammar_ide_compile fuzz/corpus/grammar_ide_compile -- -max_total_time=$(FUZZ_TIME) -jobs=$(FUZZ_JOBS) -workers=$(FUZZ_JOBS)

fuzz: fuzz-parse fuzz-ide fuzz-grammar

repl:
	RUST_BACKTRACE=1 RUST_LOG=ferlium=debug cargo run --example ferlium

print-std:
	cargo run --example ferlium -- --print-std

book-devel:
	cargo install mdbook
	mdbook serve --open docs/book/en

validate-book:
	cargo run --example validate_book docs/book/en/

update-license-headers:
	licensure --in-place `find . -name "*.rs"`
	licensure --in-place `find playground/src -name "*.ts"` playground/*.ts
