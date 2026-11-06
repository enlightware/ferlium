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

Options, all optional:

- `FUZZ_TIME`: seconds per target, default 30.
- `FUZZ_ITEM_TIMEOUT`: seconds per input, default 60.
- `FUZZ_JOBS`: workers, default the number of online CPUs.
- `FUZZ_RSS_LIMIT_MB`: memory per worker, default 4096.

```sh
make fuzz-grammar FUZZ_TIME=300 FUZZ_JOBS=4
```

The Make targets turn leak detection off, in both the sanitizer and libFuzzer, as they look for crashes and checking leaks costs about three times the throughput.
`make fuzz-optimization-leaks` runs the optimization target with leak detection.
The first corpus directory passed to libFuzzer is writable.
The committed `fuzz/corpus/*` directories are seed inputs; generated discoveries go under the ignored `fuzz/corpus-generated/` directory.

Shrink generated corpora with libFuzzer corpus minimization:

```sh
make fuzz-cmin
```

This runs `cargo fuzz cmin` for each generated corpus directory.
Each `make fuzz-<target>` has a `make fuzz-cmin-<target>` that minimizes only its corpus.
These targets also use `FUZZ_ITEM_TIMEOUT`, so pathological inputs do not block minimization indefinitely.
Minimization preserves the coverage observed by the current fuzz target binary and instrumentation; it is still worth keeping a backup or commit boundary before replacing a very large corpus.

A run first replays its whole corpus, and only then tries new inputs.
A slow target can spend all of `FUZZ_TIME` replaying: if a worker log shows `INITED` and `DONE` at the same run count, the run tried nothing new.
Give the run more time than the replay takes, or start from an empty corpus folder to try new inputs right away.

Grammar-level fuzzing uses Barkus, pinned as a Git dependency in the fuzz crate.
The EBNF grammar lives in `fuzz/grammar/ferlium.ebnf`.
It is a generation grammar for structured compiler inputs, not the official language specification.

Targets:

- `ide_compile_any` (`make fuzz-ide`) feeds valid UTF-8 through the IDE compiler path, including diagnostic position conversion.
- `grammar_ide_compile` (`make fuzz-grammar`) decodes Barkus decision tapes into Ferlium-shaped source for the IDE compiler path.
- `grammar_optimization_differential` (`make fuzz-optimization`) runs grammar-generated source with MIR optimization off and on, and compares the outcomes.
- `effect_soundness` (`make fuzz-effect-soundness`) generates programs combining traits with output effects, impls, generic callers and fallible callbacks.
- `effect_selection` (`make fuzz-effect-selection`) generates programs in which effects could reach impl selection.

The raw byte target ignores invalid UTF-8 and inputs larger than 32 KiB.
The grammar targets ignore invalid decision tapes, very large tapes, and generated source larger than 32 KiB.
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
cargo run --manifest-path fuzz/Cargo.toml --bin decode_effect_soundness_program -- fuzz/artifacts/effect_soundness/crash-... > program.fer
cargo run --release --manifest-path fuzz/Cargo.toml --bin check_effect_source -- program.fer
```

Under the sanitizer, the target checks a few programs per second and worker.
For a faster search without coverage guidance, `effect_soundness_census` and `effect_selection_census` check programs from pseudo-random inputs, recording crashes and rejections by kind instead of stopping at the first:

```sh
cargo run --release --manifest-path fuzz/Cargo.toml --bin effect_soundness_census -- 1000 42
```

The effect selection target makes the same backend checks as the effect soundness target, and checks that:

- changing only a callback's annotation, or the declaration order, does not change what runs;
- a declaration that would let effects select an impl is rejected with the matching error;
- a pure callback is accepted unless an impl it reaches requires an effect.

Its programs are compiled as trusted code, so that they can implement `Value`.
