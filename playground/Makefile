RUST_SRC_DIR := script-api
RUST_SOURCES := $(shell find $(RUST_SRC_DIR) -type f -name '*.rs')
RUST_CONFIG_FILES := $(shell find $(RUST_SRC_DIR) -type f -name 'Cargo.*')
RUST_WASM := $(RUST_SRC_DIR)/pkg/script_api_bg.wasm

dev: install-dev-deps build-rust-code
	npx vite

build: install-dev-deps build-rust-code
	npx vite build --base='./'

build-rust-code: $(RUST_WASM)

$(RUST_WASM): $(RUST_SOURCES) $(RUST_CONFIG_FILES)
	wasm-pack build script-api/ --target web

install-dev-deps:
	cargo install wasm-pack
	npm i

lint:
	./node_modules/.bin/eslint
