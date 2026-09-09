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
/// The receiver is initialized and borrowed for the lifetime of the returned member.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_member_ref(receiver: *const Tracked) -> *const String {
    unsafe { &raw const (*receiver).payload }
}

/// # Safety
/// The receiver is initialized and exclusively borrowed for the returned member's lifetime.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_member_mut(receiver: *mut Tracked) -> *mut String {
    unsafe { &raw mut (*receiver).payload }
}

/// # Safety
/// The receiver is initialized and exclusively borrowed. Success initializes the pointer output.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_member_fallible(
    failure: &mut FailureState,
    receiver: *mut Tracked,
    output: &mut MaybeUninit<*mut String>,
) -> u32 {
    let payload = unsafe { &(*receiver).payload };
    if payload.is_empty() {
        failure.message = Some("empty member".into());
        1
    } else {
        output.write(unsafe { &raw mut (*receiver).payload });
        0
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_unit_clone(_: &()) {}

#[unsafe(no_mangle)]
pub extern "C" fn probe_borrow(source: &String) -> usize {
    source.len()
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_mutate(target: &mut String, source: &String) {
    target.push_str(source);
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_clone(source: &String, output: &mut MaybeUninit<String>) {
    output.write(source.clone());
}

/// # Safety
/// `target` must contain an exclusively accessible Tracked value, consumed by this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn probe_drop(target: *mut Tracked) {
    unsafe { target.drop_in_place() };
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_optional(value: i64, output: &mut MaybeUninit<i64>) -> bool {
    if value < 0 {
        return false;
    }
    output.write(value);
    true
}

fn parse(source: &str) -> Result<i64, String> {
    source
        .parse()
        .map_err(|_| format!("invalid integer: {source}"))
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_fallible(
    failure: &mut FailureState,
    source: &String,
    output: &mut MaybeUninit<i64>,
) -> u32 {
    match parse(source) {
        Ok(value) => {
            output.write(value);
            0
        }
        Err(message) => {
            failure.message = Some(message);
            1
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_fallible_string(
    failure: &mut FailureState,
    value: i64,
    output: &mut MaybeUninit<String>,
) -> u32 {
    if value < 0 {
        failure.message = Some(format!("negative value: {value}"));
        return 1;
    }
    output.write(value.to_string());
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_fallible_unit(failure: &mut FailureState, succeed: bool) -> u32 {
    if succeed {
        0
    } else {
        failure.message = Some("unit failure".to_owned());
        1
    }
}
