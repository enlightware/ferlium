#!/usr/bin/env python3
"""Check rustc's actual core-Wasm signatures; requires the wasm32 target and WABT."""

from pathlib import Path
import os
import re
import subprocess
import tempfile


# These are the agreed core-Wasm signatures, not inferred from Rust's emitted signatures.
EXPECTED = {
    "probe_scalars": ("i32 i64 f32 f64 i32 i32", "f64"),
    "probe_integer": ("i64", "i64"),
    "probe_boolean": ("i32", "i32"),
    "probe_unit": ("", ""),
    "probe_member_ref": ("i32", "i32"),
    "probe_member_mut": ("i32", "i32"),
    "probe_member_fallible": ("i32 i32 i32", "i32"),
    "probe_unit_clone": ("i32", ""),
    "probe_borrow": ("i32", "i32"),
    "probe_mutate": ("i32 i32", ""),
    "probe_clone": ("i32 i32", ""),
    "probe_drop": ("i32", ""),
    "probe_optional": ("i64 i32", "i32"),
    "probe_fallible": ("i32 i32 i32", "i32"),
    "probe_fallible_string": ("i32 i64 i32", "i32"),
    "probe_fallible_unit": ("i32 i32", "i32"),
}


def run(*args):
    return subprocess.run(args, check=True, text=True, capture_output=True).stdout


def signatures(wat):
    # WABT supplies numeric indexes with --no-debug-names. Resolve exports via function/type
    # indexes, so LLVM merging identical types or functions does not affect the check.
    types = {}
    for index, body in re.findall(r"\(type \(;(\d+);\) \(func(.*?)\)\)\s*$", wat, re.MULTILINE):
        def fields(kind):
            return " ".join(re.findall(rf"\({kind} ([^)]+)\)", body))
        types[index] = (fields("param"), fields("result"))
    functions = dict(re.findall(r"\(func \(;(\d+);\) \(type (\d+)\)", wat))
    exports = re.findall(r'\(export "(probe_[^"]+)" \(func (\d+)\)\)', wat)
    return {name: types[functions[index]] for name, index in exports}


def main():
    rustc = os.environ.get("RUSTC", "rustc")
    print(run(rustc, "--version").strip())
    source = Path(__file__).with_name("entries.rs")
    with tempfile.TemporaryDirectory(prefix="ferlium-native-abi-") as scratch:
        for optimization in ("0", "3"):
            output = str(Path(scratch) / "entries.wasm")
            run(rustc, str(source), "--edition=2024", "--crate-type=cdylib",
                "--target=wasm32-unknown-unknown", "-Dwarnings",
                "-C", f"opt-level={optimization}", "-o", output)
            actual = signatures(run("wasm2wat", "--no-debug-names", output))
            if actual != EXPECTED:
                differences = [
                    f"{name}: expected {EXPECTED.get(name)}, got {actual.get(name)}"
                    for name in sorted(EXPECTED.keys() | actual.keys())
                    if EXPECTED.get(name) != actual.get(name)
                ]
                raise SystemExit("ABI signature mismatch:\n" + "\n".join(differences))
            print(f"Wasm32 opt-level={optimization}: {len(actual)} entry signatures match")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.stderr) from error
    except FileNotFoundError as error:
        raise SystemExit(f"{error}. Install rustc, the wasm32-unknown-unknown target, and WABT.") from error
