# Wasm benchmarks

`make bench-wasm` reports wall-clock times under normal Node behaviour. `make bench-wasm-callgrind`
runs the same workloads under Callgrind, in Gungraun's metrics. Only the first sees real cold-start
time and parallel engine compilation; only the second is immune to what else runs on the machine.

Both drive `examples/wasm-profile` over the corpus in `benches/runtime_workloads.rs`, the one
Gungraun and `make profile-mir` use.

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
make bench-wasm-callgrind VALGRIND=/path/to/vg-in-place     # an uninstalled Valgrind
```

Each run compares against `target/wasm-callgrind/baseline.json`, written by the previous one.
`VALGRIND_INCLUDE` overrides where `callgrind.h` is found for the marker addon, which exists because
neither the compiler nor the generated code can issue client requests — both are Wasm.

## Why the controls are there

Instrumentation is enabled once and only collection is toggled afterwards; restarting it would flush
Valgrind's translations and distort later ranges.

Before that, each process builds the standard library, compiles and runs one workload, then drops
that state through `reset_std_cache`. Without this warmup the first compilation in a process costs
several times a later one, and a workload would measure differently depending on how the shards were
cut. The warmup uses the *opposite* optimization setting because V8 keys its compiled module cache
on the module bytes, which would otherwise serve back the very module about to be measured.

The measured standard library build then serves every later compilation, so a second collected build
must be nearly free; the run fails otherwise.

Node runs with `--predictable --no-liftoff --no-wasm-lazy-compilation`. Without the first, identical
work varied 20x depending on whether a background compile had landed. The other two make V8 compile
with TurboFan during instantiation, so `execute` measures generated code and not Liftoff output.

Workloads are sharded across processes and both axes run concurrently; each process pays for its own
standard library build. That trade is sound only because Callgrind counts the simulated program.
`BENCH_JOBS` or `--jobs` sets the process count. The repeated standard library builds double as a
check that a repeated measurement lands on the same counts.

## Comparing results

Ranges are reproducible to within a few instructions and comparable across shard layouts.

The baseline stays in `target/`, where it belongs: the simulated cache follows the host CPU, so
counts are comparable on the machine that produced them, under the Node and Valgrind versions the
report prints.

Gungraun's numbers use the same metrics and weights but measure the native build, so the two are
read the same way and their absolute counts are not interchangeable.
