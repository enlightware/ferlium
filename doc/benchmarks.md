# Benchmarks

The Rust-hosted and WebAssembly runners use the workload corpus in
`benches/runtime_workloads.rs`.

## Rust-hosted benchmarks

Install the Gungraun runner with `make install-deps`, then run `make bench` to measure instruction
counts and other Valgrind-based metrics. Valgrind 3.19 or newer is required: version 3.18 silently
collects zero events because its Rust v0 demangler is broken. Select an uninstalled build with
`make bench VALGRIND=/path/to/vg-in-place`.

For faster optimizer iteration, `make profile-mir` compares unweighted instruction counts for raw
and optimized MIR through the MIR interpreter. Use `make profile-mir WORKLOADS="fibonacci sieve"`
to select workloads. This runner does not require Valgrind.

To see where compilation time goes, `make profile-compile WORKLOAD=sudoku REPEATS=3` compiles one
workload under Callgrind, collecting only the repeated user compilation after a warm-up that builds
the standard library. It writes `target/compile-profile/callgrind.<workload>.out`, to be read with
`callgrind_annotate --inclusive=yes`. Compare two compiler versions by profiling each.

## WebAssembly benchmarks

`make bench-wasm` reports wall-clock times under normal Node behaviour. `make bench-wasm-callgrind`
runs the same workloads under Callgrind, in Gungraun's metrics. Only the first sees real cold-start
time and parallel engine compilation; only the second is immune to what else runs on the machine.

Both drive `examples/wasm-profile` over the shared workload corpus.

### Wall-clock runner

`make bench-wasm` builds the Node profile runner and executes every workload. Set
`ARGS="quicksort sieve"` to select workloads or `ARGS="--list"` to list them. Each workload checks
a fixed result and reports Ferlium compilation/emission, engine instantiation, the first call,
median warmed execution, and generated module bytes separately. It uses the same generated
parameterless entry as the interpreter measurements.

### Callgrind runner

| Phase | Covers |
| --- | --- |
| `std_build` | Lowering the standard library to physical MIR, once per process |
| `compile` | Compiling the workload and emitting its Wasm module |
| `execute_cold` | The first call after compilation |
| `execute` | Steady-state calls, per invocation |

Execution is measured through generated Wasm by default. Passing `--mir-batch=1` also measures the
physical MIR interpreter on the same artifacts, so their ratio shows what code generation adds over
the shared input. This is opt-in because one interpreted linalg call can dominate the wall time of
the entire Wasm benchmark. The axis is post-expansion optimization (`optimize:off` is
`BenchTarget::UnoptimizedPhysicalMir`), the comparison `make bench` offers natively through
`BenchTarget::ALL`.

```
make bench-wasm-callgrind                                   # all workloads, both axes
make bench-wasm-callgrind ARGS="--list"                     # workload names
make bench-wasm-callgrind ARGS="sieve --jobs=8 --batch=20"  # subset, parallelism, batch size
make bench-wasm-callgrind ARGS="sieve --mir-batch=1"        # include interpreter comparison
make bench-wasm-callgrind ARGS="--optimized-only"           # skip the optimize:off axis, half the load
make bench-wasm-callgrind ARGS="--no-std"                   # skip the std build, the longest worker
make bench-wasm-callgrind VALGRIND=/path/to/vg-in-place     # an uninstalled Valgrind
```

Each run compares against `target/wasm-callgrind/baseline.json`, written by the previous one. Compare
only runs with the same workload selection and job count: they decide how workloads are sharded, and
the runtime code a workload runs (evidence construction, allocation) varies with what ran earlier in
its process. `--optimized-only` and `--no-std` keep the sharding of a full run.
`VALGRIND_INCLUDE` overrides where `callgrind.h` is found for the marker addon, which exists because
neither the compiler nor the generated code can issue client requests — both are Wasm.

### Why the controls are there

Instrumentation is enabled once and only collection is toggled afterwards; restarting it would flush
Valgrind's translations and distort later ranges.

Before that, each process builds the standard library, then compiles and runs one workload. Without
this warmup the first compilation in a process costs several times a later one, and a workload would
measure differently depending on how the shards were cut. The warmup uses the *opposite*
optimization setting because V8 keys its compiled module cache on the module bytes, which would
otherwise serve back the very module about to be measured. The warmup runs before instrumentation
starts, so it does not fill the simulated caches: the first measured range of a process starts from
cold caches.

One process per axis measures the standard library build: it drops the warmup's state through
`reset_std_cache` and builds it again. A second collected build must then be nearly free; the run
fails otherwise. The other processes measure workloads, reusing the warmup's standard library, built
at a small fraction of the cost of an instrumented build.

Node runs with `--predictable --no-liftoff --no-wasm-lazy-compilation`. Without the first, identical
work varied 20x depending on whether a background compile had landed. The other two make V8 compile
with TurboFan during instantiation, so `execute` measures generated code and not Liftoff output.

Workloads are sharded across processes and both axes run concurrently; each process pays for its own
uninstrumented standard library build. That trade is sound only because Callgrind counts the
simulated program. `BENCH_JOBS` or `--jobs` sets the process count, of which each axis keeps one for
the standard library build. A baseline recorded by a different version of the harness is ignored.

### Comparing results

Ranges are reproducible to within a few instructions and comparable across shard layouts.

Building does not reproduce as well: rebuilding identical sources can move compile counts by up to
about 0.7%, and a build in a git worktree differs from one in the main checkout, since the build
path is embedded in the binary. Build the base and the change in the same directory, and treat
compile differences below that as noise.

The baseline stays in `target/`, where it belongs: the simulated cache follows the host CPU, so
counts are comparable on the machine that produced them, under the Node and Valgrind versions the
report prints.

Gungraun's numbers use the same metrics and weights but measure the native build, so the two are
read the same way and their absolute counts are not interchangeable.
