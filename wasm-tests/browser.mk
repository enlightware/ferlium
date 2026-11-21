WASM_BROWSER_TEST_DIR ?= target/wasm-browser-tests
WASM_BROWSER_ALL_SUITES := ferlium language script_api
WASM_BROWSER_SUITES ?= $(WASM_BROWSER_ALL_SUITES)
WASM_BINDGEN_TEST_RUNNER ?= wasm-bindgen-test-runner
WASM_BINDGEN_TEST_TIMEOUT ?= 600

WASM_BROWSER_TEST_ENV = WASM_BINDGEN_USE_BROWSER=1 \
	WASM_BINDGEN_TEST_TIMEOUT=$(WASM_BINDGEN_TEST_TIMEOUT) \
	WASM_BINDGEN_TEST_WEBDRIVER_JSON="$(CURDIR)/wasm-tests/webdriver.json"

# Keep debug assertions, but omit DWARF and lightly optimize the large browser test binaries.
WASM_BROWSER_TEST_PROFILE = CARGO_PROFILE_TEST_DEBUG=0 CARGO_PROFILE_TEST_OPT_LEVEL=1

.PHONY: build-wasm-browser-tests run-wasm-browser-tests test-wasm-browser

build-wasm-browser-tests: SHELL := bash
build-wasm-browser-tests:
	@set -euo pipefail; \
	mkdir -p "$(WASM_BROWSER_TEST_DIR)"; \
	$(WASM_BROWSER_TEST_PROFILE) cargo test --target wasm32-unknown-unknown --no-run \
		--message-format=json-render-diagnostics -p ferlium -p script-api --lib --test language \
		| jq -r 'select(.reason == "compiler-artifact" and .executable != null) | [.target.name, .executable] | @tsv' \
		| while IFS=$$'\t' read -r name executable; do \
			cp "$$executable" "$(WASM_BROWSER_TEST_DIR)/$$name.wasm"; \
		done; \
	for suite in $(WASM_BROWSER_ALL_SUITES); do \
		binary="$(WASM_BROWSER_TEST_DIR)/$$suite.wasm"; \
		test -f "$$binary" || { echo "Missing Wasm test binary: $$binary" >&2; exit 1; }; \
	done

run-wasm-browser-tests:
	@set -e; for suite in $(WASM_BROWSER_SUITES); do \
		$(WASM_BROWSER_TEST_ENV) "$(WASM_BINDGEN_TEST_RUNNER)" "$(WASM_BROWSER_TEST_DIR)/$$suite.wasm"; \
	done

test-wasm-browser: build-wasm-browser-tests
	$(MAKE) -f wasm-tests/browser.mk run-wasm-browser-tests
