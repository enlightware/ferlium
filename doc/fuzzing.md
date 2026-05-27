# Fuzzing

Ferlium has a small `cargo-fuzz` setup for crash-oriented compiler fuzzing.
The fuzz package is a workspace member, but it is not a default workspace member; run fuzzing explicitly with nightly Rust and the `cargo-fuzz` subcommand.

Install the subcommand if needed:

```sh
cargo install cargo-fuzz
```

Run short local smoke sessions:

```sh
make fuzz
```

Override the default 30 second per-target duration with `FUZZ_TIME`:

```sh
make fuzz FUZZ_TIME=120
```

The equivalent direct commands are:

```sh
mkdir -p fuzz/corpus-generated/parse_any
ASAN_OPTIONS=detect_leaks=0 cargo +nightly fuzz run parse_any fuzz/corpus-generated/parse_any fuzz/corpus/parse_any -- -max_total_time=30
mkdir -p fuzz/corpus-generated/ide_compile_any
ASAN_OPTIONS=detect_leaks=0 cargo +nightly fuzz run ide_compile_any fuzz/corpus-generated/ide_compile_any fuzz/corpus/programs fuzz/corpus/diagnostics -- -max_total_time=30
```

The Make targets set `ASAN_OPTIONS=detect_leaks=0` because short fuzz smoke runs are looking for compiler crashes, not process-lifetime leak reports from the sanitizer runtime.
The first corpus directory passed to libFuzzer is writable.
The committed `fuzz/corpus/*` directories are seed inputs; generated discoveries go under the ignored `fuzz/corpus-generated/` directory.

Targets:

- `parse_any` feeds valid UTF-8 directly to `parse_module_and_expr`.
- `ide_compile_any` feeds valid UTF-8 through the IDE compiler path, including the normal compiler and diagnostic position conversion.

All targets ignore invalid UTF-8 and inputs larger than 32 KiB.
Panics are left uncaught on purpose: a compiler panic is a fuzz finding.

When a crash is found, minimize it with cargo-fuzz and keep the reduced input as a regression test if it represents a real compiler bug.
