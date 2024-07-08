dev: install-dev-deps build-rust-code
	npx vite

build-rust-code:
	wasm-pack build script-api/ --target web

install-dev-deps:
	cargo install wasm-pack

lint:
	./node_modules/.bin/eslint
