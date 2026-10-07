# REPL

Ferlium has two terminal REPLs with the same submission model:

```sh
make repl-hir                 # Native: HIR interpreter
make repl-mir                 # Native: optimized MIR interpreter
make repl-wasm                # Node: dynamically generated and linked Wasm
```

The Wasm flavour uses the playground backend and requires Node, `wasm-pack`, and
Rust's `wasm32-unknown-unknown` target. After building, run
`node examples/wasm-repl/run.mjs` directly to skip the build step.

Each input is a `replN` module. Public definitions persist; newer definitions
shadow older ones, while existing functions retain their original bindings.
Expression locals do not persist. Use `pub fn`, `pub struct`, etc. for definitions
that later inputs should access.

Multiline terminal pastes are kept as one submission; press Enter to submit.
This uses bracketed paste, supported by modern terminals.

| Command (both flavours) | Behaviour |
| --- | --- |
| `\help` | List commands. |
| `\fuel [N\|off]` | Show/set execution fuel; default 100,000. `none` and `unlimited` also disable it. |
| `\module [MODULE]` | Inspect the current or named module's HIR, including private definitions. |
| `\function FN [MODULE]` | Inspect a function by name/index, or `MODULE::FN`. |
| `\history` | List compiled submissions and their statistics. |
| `\opt [on\|off]` | Show/set MIR optimization; `yes`/`no` are aliases. Native HIR execution is unaffected. |
| `\mir [MODULE] [raw]` | Inspect the last submission or named module’s semantic MIR with the current optimization setting, or raw MIR. |
| `\physical-mir [MODULE] [raw]` | Inspect the last submission or named module’s physical MIR with the current optimization setting, or raw MIR. |
| `\load FILE` | Compile and run a file as a submission. |
| `\run` | Repeat the last expression, including side effects. |
| `\reset` | Clear the session. |
| `\quit` or Ctrl-D | Exit. |

Both REPLs print values and program output by default; inspection is explicit.
In Wasm, `\wasm` shows the complete last compiled module, including uncalled
private functions and runtime data annotations, as in the playground. Execution
separately emits the expression entry and its reachable code. Both flavours
enable MIR optimization by default; `--opt off` disables it. Native `--hir`
selects HIR execution. `--mir` and `--physical-mir` request inspection after
execution in either flavour. Pass flags through Make with `ARGS`, for example
`make repl-mir ARGS="--opt off"`. MIR inspection follows `\opt` unless `raw` is specified.

Compilation errors preserve earlier definitions; recoverable runtime errors allow
later inputs. Use `\help` for the full command-line options.

Both flavours accept piped source as one complete submission. For agents, the
Wasm frontend also offers file input, `--eval SOURCE`, and scripted sessions:

```sh
node examples/wasm-repl/run.mjs --session --json <<'SESSION'
pub fn twice(x: int) -> int { x * 2 }
twice(21)
\wasm
SESSION
```

`--session` reads one input/command per line; `--json` emits JSON lines without
prompts. Diagnostic offsets use UTF-16 code units. Exit status is 0 on success,
1 for compilation/usage errors, and 2 for execution/inspection errors;
the highest exit status is retained across session inputs. Run Wasm integration tests
with `make test-wasm-repl`.
