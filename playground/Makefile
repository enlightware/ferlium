RUST_SRC_DIR := ..
RUST_SOURCES := $(shell find $(RUST_SRC_DIR) -type f -name '*.rs')
RUST_CONFIG_FILES := $(shell find $(RUST_SRC_DIR) -type f -name 'Cargo.*')
RUST_WASM := $(RUST_SRC_DIR)/pkg/script_api_bg.wasm

dev: install-dev-deps build-rust-code
	npx vite

build: install-dev-deps build-rust-code
	npx vite build

build-rust-code: $(RUST_WASM)

$(RUST_WASM): $(RUST_SOURCES) $(RUST_CONFIG_FILES)
	wasm-pack build script-api/ --target web

install-dev-deps:
	cargo install wasm-pack
	npm i

lint:
	./node_modules/.bin/eslint

validate-grammar: install-dev-deps
	./node_modules/.bin/lezer-generator src/language/language.grammar -o test/temp-grammar.js
	cd test && node extract-test-grammar.js ./temp-grammar.js
	rm -f test/temp-grammar.js test/temp-grammar.terms.js

list-grammar-errors: install-dev-deps
	./node_modules/.bin/lezer-generator src/language/language.grammar -o test/temp-grammar.js
	cd test && node extract-test-grammar.js ./temp-grammar.js --errors
	rm -f test/temp-grammar.js test/temp-grammar.terms.js

validate-grammar-verbose: install-dev-deps
	./node_modules/.bin/lezer-generator src/language/language.grammar -o test/temp-grammar.js
	cd test && node extract-test-grammar.js ./temp-grammar.js --verbose
	rm -f test/temp-grammar.js test/temp-grammar.terms.js