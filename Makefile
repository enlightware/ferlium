# Fuzzing duration in seconds
FUZZ_TIME ?= 30
# Per-input libFuzzer timeout in seconds.
FUZZ_ITEM_TIMEOUT ?= 60
# Number of parallel libFuzzer workers. Defaults to the online CPU count on Linux.
FUZZ_JOBS ?= $(shell nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
# Directory where libFuzzer writes fuzz-*.log files in multi-worker mode.
FUZZ_LOG_DIR ?= fuzz/logs
# libFuzzer links the C++ standard library through clang. On systems where clang
# does not know GCC's library directory, expose it through LIBRARY_PATH.
CXX_STDLIB_PATH ?= $(shell c++ -print-file-name=libstdc++.so 2>/dev/null)
CXX_STDLIB_DIR ?= $(if $(filter /%,$(CXX_STDLIB_PATH)),$(dir $(CXX_STDLIB_PATH)))
FUZZ_ENV := ASAN_OPTIONS=detect_leaks=0
# Leak detection costs roughly 3x throughput, so it is opt-in rather than on by default.
FUZZ_ENV_LEAKS := ASAN_OPTIONS=detect_leaks=1
ifneq ($(strip $(CXX_STDLIB_DIR)),)
FUZZ_ENV += LIBRARY_PATH=$(CXX_STDLIB_DIR):$${LIBRARY_PATH}
FUZZ_ENV_LEAKS += LIBRARY_PATH=$(CXX_STDLIB_DIR):$${LIBRARY_PATH}
endif

# Number of callgrind benchmarks to run in parallel: physical cores, not logical threads.
#
# Parallelism is sound here in a way it is not for wall-clock benchmarking. Callgrind counts the
# instructions of the *simulated* program and simulates the cache with fixed parameters, so neither
# metric can be perturbed by what else runs on the machine.
#
# Physical cores rather than `nproc` because a callgrind worker is a serial, CPU-bound simulator
# with a large shadow-memory working set: two of them on one physical core contend for the same L1
# and L2 and the same execution ports, so an SMT sibling buys much less than a core does.
BENCH_JOBS ?= $(shell c=$$(lscpu -p=Core,Socket 2>/dev/null | grep -v '^\#' | sort -u | wc -l); \
	if [ "$$c" -gt 0 ] 2>/dev/null; then echo $$c; \
	else nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1; fi)

install-deps:
	cargo install cargo-nextest --locked
	cargo install --version 0.18.2 gungraun-runner

test-local:
	RUST_LOG=ferlium=debug cargo nextest run

test-wasm:
	CARGO_PROFILE_TEST_DEBUG=0 WASM_BINDGEN_USE_BROWSER=1 wasm-pack test --chrome --firefox --headless --test language --lib

test: test-local test-wasm

test-miri:
	cargo +nightly miri test hir::value::tests::discard_storage_recursively_reclaims_runtime_payloads --lib

bench:
	GUNGRAUN_PARALLEL=$(BENCH_JOBS) cargo bench

fuzz-ide:
	mkdir -p fuzz/corpus-generated/ide_compile_any $(FUZZ_LOG_DIR)/ide_compile_any
	cd $(FUZZ_LOG_DIR)/ide_compile_any && $(FUZZ_ENV) cargo +nightly fuzz run --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target ide_compile_any $(CURDIR)/fuzz/corpus-generated/ide_compile_any $(CURDIR)/fuzz/corpus/programs $(CURDIR)/fuzz/corpus/diagnostics $(CURDIR)/fuzz/corpus/parse_any -- -max_total_time=$(FUZZ_TIME) -timeout=$(FUZZ_ITEM_TIMEOUT) -jobs=$(FUZZ_JOBS) -workers=$(FUZZ_JOBS)

fuzz-grammar:
	mkdir -p fuzz/corpus-generated/grammar_ide_compile $(FUZZ_LOG_DIR)/grammar_ide_compile
	cd $(FUZZ_LOG_DIR)/grammar_ide_compile && $(FUZZ_ENV) cargo +nightly fuzz run --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target grammar_ide_compile $(CURDIR)/fuzz/corpus-generated/grammar_ide_compile $(CURDIR)/fuzz/corpus/grammar_ide_compile -- -max_total_time=$(FUZZ_TIME) -timeout=$(FUZZ_ITEM_TIMEOUT) -jobs=$(FUZZ_JOBS) -workers=$(FUZZ_JOBS)

fuzz-optimization:
	mkdir -p fuzz/corpus-generated/grammar_optimization_differential $(FUZZ_LOG_DIR)/grammar_optimization_differential
	cd $(FUZZ_LOG_DIR)/grammar_optimization_differential && $(FUZZ_ENV) cargo +nightly fuzz run --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target grammar_optimization_differential $(CURDIR)/fuzz/corpus-generated/grammar_optimization_differential $(CURDIR)/fuzz/corpus/grammar_ide_compile -- -max_total_time=$(FUZZ_TIME) -timeout=$(FUZZ_ITEM_TIMEOUT) -jobs=$(FUZZ_JOBS) -workers=$(FUZZ_JOBS)

fuzz-optimization-leaks:
	mkdir -p fuzz/corpus-generated/grammar_optimization_differential $(FUZZ_LOG_DIR)/grammar_optimization_differential
	cd $(FUZZ_LOG_DIR)/grammar_optimization_differential && $(FUZZ_ENV_LEAKS) cargo +nightly fuzz run --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target grammar_optimization_differential $(CURDIR)/fuzz/corpus-generated/grammar_optimization_differential $(CURDIR)/fuzz/corpus/grammar_ide_compile -- -max_total_time=$(FUZZ_TIME) -timeout=$(FUZZ_ITEM_TIMEOUT) -jobs=$(FUZZ_JOBS) -workers=$(FUZZ_JOBS)

fuzz: fuzz-ide fuzz-grammar fuzz-optimization

fuzz-cmin-ide:
	mkdir -p fuzz/corpus-generated/ide_compile_any
	$(FUZZ_ENV) cargo +nightly fuzz cmin --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target ide_compile_any $(CURDIR)/fuzz/corpus-generated/ide_compile_any -- -timeout=$(FUZZ_ITEM_TIMEOUT)

fuzz-cmin-grammar:
	mkdir -p fuzz/corpus-generated/grammar_ide_compile
	$(FUZZ_ENV) cargo +nightly fuzz cmin --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target grammar_ide_compile $(CURDIR)/fuzz/corpus-generated/grammar_ide_compile -- -timeout=$(FUZZ_ITEM_TIMEOUT)

fuzz-cmin-optimization:
	mkdir -p fuzz/corpus-generated/grammar_optimization_differential
	$(FUZZ_ENV) cargo +nightly fuzz cmin --fuzz-dir $(CURDIR)/fuzz --target-dir $(CURDIR)/target grammar_optimization_differential $(CURDIR)/fuzz/corpus-generated/grammar_optimization_differential -- -timeout=$(FUZZ_ITEM_TIMEOUT)

fuzz-cmin: fuzz-cmin-ide fuzz-cmin-grammar fuzz-cmin-optimization

repl:
	RUST_BACKTRACE=1 RUST_LOG=ferlium=debug cargo run --example ferlium

repl-mir:
	RUST_BACKTRACE=1 RUST_LOG=ferlium=debug cargo run --example ferlium -- --mir

repl-opt:
	RUST_BACKTRACE=1 RUST_LOG=ferlium=debug cargo run --example ferlium -- --optimize

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
