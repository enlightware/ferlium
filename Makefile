# Fuzzing duration in seconds
FUZZ_TIME ?= 30
# Number of parallel libFuzzer workers. Defaults to the online CPU count on Linux.
FUZZ_JOBS ?= $(shell nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
# Directory where libFuzzer writes fuzz-*.log files in multi-worker mode.
FUZZ_LOG_DIR ?= fuzz/logs
# libFuzzer links the C++ standard library through clang. On systems where clang
# does not know GCC's library directory, expose it through LIBRARY_PATH.
CXX_STDLIB_PATH ?= $(shell c++ -print-file-name=libstdc++.so 2>/dev/null)
CXX_STDLIB_DIR ?= $(if $(filter /%,$(CXX_STDLIB_PATH)),$(dir $(CXX_STDLIB_PATH)))
FUZZ_ENV := ASAN_OPTIONS=detect_leaks=0
ifneq ($(strip $(CXX_STDLIB_DIR)),)
FUZZ_ENV += LIBRARY_PATH=$(CXX_STDLIB_DIR):$${LIBRARY_PATH}
endif

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
	mkdir -p fuzz/corpus-generated/parse_any $(FUZZ_LOG_DIR)/parse_any
	cd $(FUZZ_LOG_DIR)/parse_any && $(FUZZ_ENV) cargo +nightly fuzz run --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target parse_any $(CURDIR)/fuzz/corpus-generated/parse_any $(CURDIR)/fuzz/corpus/parse_any -- -max_total_time=$(FUZZ_TIME) -jobs=$(FUZZ_JOBS) -workers=$(FUZZ_JOBS)

fuzz-ide:
	mkdir -p fuzz/corpus-generated/ide_compile_any $(FUZZ_LOG_DIR)/ide_compile_any
	cd $(FUZZ_LOG_DIR)/ide_compile_any && $(FUZZ_ENV) cargo +nightly fuzz run --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target ide_compile_any $(CURDIR)/fuzz/corpus-generated/ide_compile_any $(CURDIR)/fuzz/corpus/programs $(CURDIR)/fuzz/corpus/diagnostics -- -max_total_time=$(FUZZ_TIME) -jobs=$(FUZZ_JOBS) -workers=$(FUZZ_JOBS)

fuzz-grammar:
	mkdir -p fuzz/corpus-generated/grammar_ide_compile $(FUZZ_LOG_DIR)/grammar_ide_compile
	cd $(FUZZ_LOG_DIR)/grammar_ide_compile && $(FUZZ_ENV) cargo +nightly fuzz run --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target grammar_ide_compile $(CURDIR)/fuzz/corpus-generated/grammar_ide_compile $(CURDIR)/fuzz/corpus/grammar_ide_compile -- -max_total_time=$(FUZZ_TIME) -jobs=$(FUZZ_JOBS) -workers=$(FUZZ_JOBS)

fuzz: fuzz-parse fuzz-ide fuzz-grammar

fuzz-cmin-parse:
	mkdir -p fuzz/corpus-generated/parse_any
	$(FUZZ_ENV) cargo +nightly fuzz cmin --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target parse_any $(CURDIR)/fuzz/corpus-generated/parse_any

fuzz-cmin-ide:
	mkdir -p fuzz/corpus-generated/ide_compile_any
	$(FUZZ_ENV) cargo +nightly fuzz cmin --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target ide_compile_any $(CURDIR)/fuzz/corpus-generated/ide_compile_any

fuzz-cmin-grammar:
	mkdir -p fuzz/corpus-generated/grammar_ide_compile
	$(FUZZ_ENV) cargo +nightly fuzz cmin --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target grammar_ide_compile $(CURDIR)/fuzz/corpus-generated/grammar_ide_compile

fuzz-cmin: fuzz-cmin-parse fuzz-cmin-ide fuzz-cmin-grammar

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
