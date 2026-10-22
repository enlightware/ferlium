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

Each generated input has a default one minute timeout.
Override it with `FUZZ_ITEM_TIMEOUT` when investigating slower inputs:

```sh
make fuzz-grammar FUZZ_ITEM_TIMEOUT=10
```

Fuzzing uses multiple libFuzzer workers by default.
`FUZZ_JOBS` defaults to the online CPU count reported by `nproc`, with a `getconf _NPROCESSORS_ONLN` fallback.
Override it when you want fewer workers:

```sh
make fuzz-grammar FUZZ_TIME=300 FUZZ_JOBS=4
```

The equivalent direct commands are:

```sh
mkdir -p fuzz/corpus-generated/parse_any
ASAN_OPTIONS=detect_leaks=0 cargo +nightly fuzz run parse_any fuzz/corpus-generated/parse_any fuzz/corpus/parse_any -- -max_total_time=30 -timeout=60 -jobs=$(nproc) -workers=$(nproc)
mkdir -p fuzz/corpus-generated/ide_compile_any
ASAN_OPTIONS=detect_leaks=0 cargo +nightly fuzz run ide_compile_any fuzz/corpus-generated/ide_compile_any fuzz/corpus/programs fuzz/corpus/diagnostics -- -max_total_time=30 -timeout=60 -jobs=$(nproc) -workers=$(nproc)
mkdir -p fuzz/corpus-generated/grammar_ide_compile
ASAN_OPTIONS=detect_leaks=0 cargo +nightly fuzz run grammar_ide_compile fuzz/corpus-generated/grammar_ide_compile fuzz/corpus/grammar_ide_compile -- -max_total_time=30 -timeout=60 -jobs=$(nproc) -workers=$(nproc)
```

The Make targets set `ASAN_OPTIONS=detect_leaks=0` because short fuzz smoke runs are looking for compiler crashes, not process-lifetime leak reports from the sanitizer runtime.
The first corpus directory passed to libFuzzer is writable.
The committed `fuzz/corpus/*` directories are seed inputs; generated discoveries go under the ignored `fuzz/corpus-generated/` directory.

Shrink generated corpora with libFuzzer corpus minimization:

```sh
make fuzz-cmin
```

This runs `cargo fuzz cmin` for each generated corpus directory.
Use `make fuzz-cmin-parse`, `make fuzz-cmin-ide`, `make fuzz-cmin-grammar`, or `make fuzz-cmin-effects` to minimize a single target.
These targets also use `FUZZ_ITEM_TIMEOUT`, so pathological inputs do not block minimization indefinitely.
Minimization preserves the coverage observed by the current fuzz target binary and instrumentation; it is still worth keeping a backup or commit boundary before replacing a very large corpus.

Grammar-level fuzzing uses Barkus, pinned as a Git dependency in the fuzz crate.
The EBNF grammar lives in `fuzz/grammar/ferlium.ebnf`.
It is a generation grammar for structured compiler inputs, not the official language specification.

Targets:

- `parse_any` feeds valid UTF-8 directly to `parse_module_and_expr`.
- `ide_compile_any` feeds valid UTF-8 through the IDE compiler path, including the normal compiler and diagnostic position conversion.
- `grammar_ide_compile` decodes Barkus decision tapes into Ferlium-shaped source, then feeds the source through the IDE compiler path.
- `grammar_optimization_differential` runs grammar-generated expressions with MIR optimization off and on, and compares their outcomes.
- `effect_soundness` generates programs combining traits with output effects, concrete and blanket impls, generic callers and fallible callbacks (`make fuzz-effects`).

The raw byte targets ignore invalid UTF-8 and inputs larger than 32 KiB.
The grammar target ignores invalid decision tapes, very large tapes, and generated source larger than 32 KiB.
Panics are left uncaught on purpose: a compiler panic is a fuzz finding.

When a crash is found, minimize it with cargo-fuzz and keep the reduced input as a regression test if it represents a real compiler bug.

Grammar-fuzzer artifacts are Barkus decision tapes, not Ferlium source.
Decode one before triaging it:

```sh
cargo run --manifest-path fuzz/Cargo.toml --bin decode_grammar_tape -- fuzz/artifacts/grammar_ide_compile/crash-...
```

The effect soundness target checks that no source failure escapes code typed as unable to fail, that every reference backend computes the same outcome, and that renaming effect variables and reordering declarations and uses changes nothing.
Its programs are well typed by construction, so a rejection is worth a look, but only a panic is a finding.
Its artifacts are generator inputs; print the program one generates, and rerun the checks on a source file while reducing it:

```sh
cargo run --manifest-path fuzz/Cargo.toml --bin decode_effect_program -- fuzz/artifacts/effect_soundness/crash-... > program.fer
cargo run --release --manifest-path fuzz/Cargo.toml --bin check_effect_source -- program.fer
```

Under the sanitizer, the target checks a few programs per second and worker.
For a faster search without coverage guidance, `effect_program_census` checks programs from pseudo-random inputs, recording crashes and rejections by kind instead of stopping at the first:

```sh
cargo run --release --manifest-path fuzz/Cargo.toml --bin effect_program_census -- 1000 42
```
