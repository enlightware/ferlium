dev: install-dev-deps build-rust-code
	npx vite

build: build-rust-code
	npx vite build --base='./'

build-rust-code:
	wasm-pack build script-api/ --target web

install-dev-deps:
	cargo install wasm-pack

update-cargo-dev:
	cd script-api && CARGO_NET_GIT_FETCH_WITH_CLI=true cargo update

lint:
	./node_modules/.bin/eslint
