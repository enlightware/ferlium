// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Executing a program repeatedly must not grow the heap.
//!
//! `Value` is `ManuallyDrop`-based, so Rust never reclaims one implicitly: every path has to
//! discard it explicitly, and a path that forgets leaks silently. Nothing in the ordinary test suite
//! can see that — the leak is invisible to results, to the verifier, and to the interpreter's own
//! bookkeeping. This binary installs a counting allocator so a leak on a hot path shows up as an
//! allocation count that climbs with the number of executions.
//!
//! It is a *steady-state* check, not an absolute one: caches, interners and lazily built artifacts
//! legitimately allocate on the first runs, so the measurement warms up first and then requires the
//! live count to stay flat across further identical runs.
//!
//! This is the regression net for the `subfield`/`condbr` operand leaks the differential fuzz target
//! found under LeakSanitizer; `make fuzz-optimization-leaks` remains the broader one.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicIsize, Ordering};

use ferlium::{CompilerSession, ExecutionTarget, MirOptimization, module::Path, ustr};

static LIVE_ALLOCATIONS: AtomicIsize = AtomicIsize::new(0);

struct CountingAllocator;

// SAFETY: every call delegates to the system allocator with the same arguments; the counter only
// observes.
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        LIVE_ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        LIVE_ALLOCATIONS.fetch_sub(1, Ordering::Relaxed);
        unsafe { System.dealloc(pointer, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

fn live() -> isize {
    LIVE_ALLOCATIONS.load(Ordering::Relaxed)
}

/// Exercises the operations whose operands were leaked: a field access per iteration (`subfield`
/// reads a constant index) and a conditional (`condbr` reads a bool).
const SOURCE: &str = "\
struct Pair { x: int, y: int }
fn main() -> int {
    let pair = { x: 1, y: 2 };
    let mut sum = 0;
    for i in 0..20 {
        if pair.x < pair.y { sum = sum + pair.x } else { sum = sum + pair.y }
    };
    sum
}";

fn run_repeatedly(optimization: MirOptimization, runs: usize) -> isize {
    let mut session = CompilerSession::new();
    session.set_mir_optimization(optimization);
    let module_id = session
        .compile_for(
            ExecutionTarget::Mir,
            SOURCE,
            "leaks",
            Path::single_str("leaks"),
        )
        .expect("the snippet must compile")
        .module_id;
    let main = session
        .expect_fresh_module(module_id)
        .get_local_function_id(ustr("main"))
        .expect("the snippet defines main");

    let mut execute = || {
        session
            .run_entry(ExecutionTarget::Mir, module_id, main, vec![])
            .expect("the snippet must run")
            .discard_storage();
    };

    // Warm up: the first runs build artifacts and fill caches that are meant to persist.
    for _ in 0..3 {
        execute();
    }
    let before = live();
    for _ in 0..runs {
        execute();
    }
    live() - before
}

/// The detector itself must be able to see a leak, or the tests below would pass vacuously.
#[test]
fn the_counting_allocator_observes_a_leak() {
    let before = live();
    for _ in 0..16 {
        std::mem::forget(Box::new(1_u64));
    }
    assert!(
        live() - before >= 16,
        "the allocator must count deliberately leaked boxes"
    );
}

#[test]
fn repeated_mir_execution_does_not_leak() {
    let growth = run_repeatedly(MirOptimization::Disabled, 50);
    assert_eq!(
        growth, 0,
        "50 identical executions grew the live allocation count by {growth}"
    );
}

#[test]
fn repeated_optimized_mir_execution_does_not_leak() {
    let growth = run_repeatedly(MirOptimization::Enabled, 50);
    assert_eq!(
        growth, 0,
        "50 identical optimized executions grew the live allocation count by {growth}"
    );
}
