install-deps:
	cargo install cargo-nextest --locked

test-local:
	RUST_LOG=ferlium=debug cargo nextest run

test-wasm:
	WASM_BINDGEN_USE_BROWSER=1 wasm-pack test --chrome --firefox --headless --test language --lib

test: test-local test-wasm

bench:
	PREV_GOV=$$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor); \
	sudo cpupower frequency-set --governor performance; \
	if [ -f /sys/devices/system/cpu/intel_pstate/no_turbo ]; then \
		echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo > /dev/null; \
	elif [ -f /sys/devices/system/cpu/cpufreq/boost ]; then \
		echo 0 | sudo tee /sys/devices/system/cpu/cpufreq/boost > /dev/null; \
	fi; \
	cargo bench; \
	if [ -f /sys/devices/system/cpu/intel_pstate/no_turbo ]; then \
		echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo > /dev/null; \
	elif [ -f /sys/devices/system/cpu/cpufreq/boost ]; then \
		echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost > /dev/null; \
	fi; \
	sudo cpupower frequency-set --governor "$$PREV_GOV"

repl:
	RUST_BACKTRACE=1 RUST_LOG=ferlium=debug cargo run --example ferlium

book-devel:
	cargo install mdbook
	mdbook serve --open docs/book/en

validate-book:
	cargo run --example validate_book docs/book/en/

update-license-headers:
	licensure --in-place `find . -name "*.rs"`
	licensure --in-place `find playground/src -name "*.ts"` playground/*.ts