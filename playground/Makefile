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

install-wasm-deps:
	cargo install wasm-pack

install-npm-deps:
	npm i

install-dev-deps: install-npm-deps install-wasm-deps

lint:
	./node_modules/.bin/eslint --ignore-pattern "script-api/pkg/*"

validate-grammar: install-npm-deps
	./node_modules/.bin/lezer-generator src/language/language.grammar -o src/language/language.grammar.js
	./node_modules/.bin/esbuild src/language/unicode-identifiers.ts --bundle --format=esm --external:@lezer/lr --outfile=src/language/unicode-identifiers.js
	cd test && node extract-test-grammar.js ../src/language/language.grammar.js
	rm -f src/language/language.grammar.js src/language/language.grammar.terms.js src/language/unicode-identifiers.js

list-grammar-errors: install-npm-deps
	./node_modules/.bin/lezer-generator src/language/language.grammar -o src/language/language.grammar.js
	./node_modules/.bin/esbuild src/language/unicode-identifiers.ts --bundle --format=esm --external:@lezer/lr --outfile=src/language/unicode-identifiers.js
	cd test && node extract-test-grammar.js ../src/language/language.grammar.js --errors
	rm -f src/language/language.grammar.js src/language/language.grammar.terms.js src/language/unicode-identifiers.js

validate-grammar-verbose: install-npm-deps
	./node_modules/.bin/lezer-generator src/language/language.grammar -o src/language/language.grammar.js
	./node_modules/.bin/esbuild src/language/unicode-identifiers.ts --bundle --format=esm --external:@lezer/lr --outfile=src/language/unicode-identifiers.js
	cd test && node extract-test-grammar.js ../src/language/language.grammar.js --verbose
	rm -f src/language/language.grammar.js src/language/language.grammar.terms.js src/language/unicode-identifiers.js
