//! Standalone ABI fixtures, also compiled directly by `check_wasm.py`.
//! These model entry transport, not production native registration or failure-state policy.

use std::{cell::Cell, mem::MaybeUninit, rc::Rc};

#[derive(Default)]
pub struct FailureState {
    pub message: Option<String>,
}

pub struct Tracked {
    pub payload: String,
    pub drops: Rc<Cell<usize>>,
}

impl Drop for Tracked {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

// Explicit exports retain the fixtures; export naming is independent of their C ABI.
#[unsafe(no_mangle)]
pub extern "C" fn probe_scalars(a: i32, b: i64, c: f32, d: f64, e: usize, f: bool) -> f64 {
    f64::from(a) + b as f64 + f64::from(c) + d + e as f64 + u8::from(f) as f64
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_integer(value: i64) -> i64 {
    value.wrapping_add(1)
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_boolean(value: bool) -> bool {
    !value
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_unit() {}

/// # Safety
/// `source` must point to a live, shared String for the duration of the call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_borrow(source: *const String) -> usize {
    let source = unsafe { &*source };
    source.len()
}

/// # Safety
/// Both strings must be live; `target` must be exclusively accessible and disjoint from `source`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_mutate(target: *mut String, source: *const String) {
    let target = unsafe { &mut *target };
    target.push_str(unsafe { &*source });
}

/// # Safety
/// `source` must be live; `output` must be writable, aligned, and disjoint result storage
/// with no live value requiring destruction.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_clone(source: *const String, output: *mut MaybeUninit<String>) {
    let source = unsafe { &*source };
    unsafe { (*output).write(source.clone()) };
}

/// # Safety
/// `target` must contain an exclusively accessible Tracked value, consumed by this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_drop(target: *mut Tracked) {
    unsafe { target.drop_in_place() };
}

/// # Safety
/// `output` must point to writable, aligned result storage.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_optional(value: i64, output: *mut MaybeUninit<i64>) -> bool {
    if value < 0 {
        return false;
    }
    unsafe { (*output).write(value) };
    true
}

fn parse(source: &str) -> Result<i64, String> {
    source
        .parse()
        .map_err(|_| format!("invalid integer: {source}"))
}

/// # Safety
/// `failure` must be live and exclusively accessible, `source` live and shared, and `output`
/// writable and aligned. All three must be disjoint. Failure consumes no result storage.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_fallible(
    failure: *mut FailureState,
    source: *const String,
    output: *mut MaybeUninit<i64>,
) -> u32 {
    match parse(unsafe { &*source }) {
        Ok(value) => {
            unsafe { (*output).write(value) };
            0
        }
        Err(message) => {
            unsafe { (*failure).message = Some(message) };
            1
        }
    }
}

/// # Safety
/// `failure` must be live and exclusively accessible; `output` must be writable, aligned,
/// disjoint result storage with no live value requiring destruction.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_fallible_string(
    failure: *mut FailureState,
    value: i64,
    output: *mut MaybeUninit<String>,
) -> u32 {
    if value < 0 {
        unsafe { (*failure).message = Some(format!("negative value: {value}")) };
        return 1;
    }
    unsafe { (*output).write(value.to_string()) };
    0
}

/// # Safety
/// `failure` must point to a live, exclusively accessible failure state.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_fallible_unit(failure: *mut FailureState, succeed: bool) -> u32 {
    if succeed {
        0
    } else {
        unsafe { (*failure).message = Some("unit failure".to_owned()) };
        1
    }
}
