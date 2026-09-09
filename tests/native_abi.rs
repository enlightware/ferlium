//! Native execution of the same Rust entries whose Wasm signatures are checked separately.

#![cfg(not(target_arch = "wasm32"))]

#[path = "native_abi/entries.rs"]
mod entries;

use entries::*;
use std::{cell::Cell, mem::MaybeUninit, rc::Rc};

#[test]
fn native_abi_rooted_member_pointers() {
    let drops = Rc::new(Cell::new(0));
    let mut owner = Tracked {
        payload: "member".into(),
        drops: drops.clone(),
    };
    let shared: unsafe extern "C" fn(*const Tracked) -> *const String = probe_member_ref;
    let mutable: unsafe extern "C" fn(*mut Tracked) -> *mut String = probe_member_mut;
    let mut failure = FailureState::default();
    let mut output = MaybeUninit::uninit();
    // SAFETY: each pointer is used within its receiver borrow. Replacement keeps the field live.
    unsafe {
        assert_eq!(&*shared(&owner), "member");
        let old = std::ptr::replace(mutable(&mut owner), "replacement".into());
        assert_eq!(old, "member");
        assert_eq!(
            probe_member_fallible(&mut failure, &mut owner, &mut output),
            0
        );
        (*output.assume_init()).clear();
        let sentinel = std::ptr::without_provenance_mut::<String>(1);
        output.write(sentinel);
        assert_ne!(
            probe_member_fallible(&mut failure, &mut owner, &mut output),
            0
        );
        assert_eq!(output.assume_init(), sentinel);
    }
    assert_eq!(failure.message.as_deref(), Some("empty member"));
    assert!(owner.payload.is_empty());
    assert_eq!(drops.get(), 0);
    drop(owner);
    assert_eq!(drops.get(), 1);
}

#[test]
fn native_abi_scalar_and_unit_transport() {
    // Typed function pointers check that the entries really expose the intended Rust C ABI.
    let mixed: extern "C" fn(i32, i64, f32, f64, usize, bool) -> f64 = probe_scalars;
    assert_eq!(mixed(0, 0, 0.0, 0.0, usize::MAX, false), usize::MAX as f64);
    assert_eq!(
        mixed(-3, 1_i64 << 40, 0.5, 0.25, 7, true),
        (1_i64 << 40) as f64 + 5.75
    );
    let integer: extern "C" fn(i64) -> i64 = probe_integer;
    assert_eq!(integer(i64::MAX), i64::MIN);
    assert!(probe_boolean(false));
    assert!(!probe_boolean(true));
    probe_unit();
    let clone_unit: extern "C" fn(&()) = probe_unit_clone;
    clone_unit(&());
}

#[test]
fn native_abi_borrows_mutation_and_managed_output() {
    let source = " world".to_owned();
    let mut target = "hello".to_owned();
    let mut output = MaybeUninit::uninit();
    let clone: extern "C" fn(&String, &mut MaybeUninit<String>) = probe_clone;
    assert_eq!(probe_borrow(&source), 6);
    probe_mutate(&mut target, &source);
    clone(&target, &mut output);
    // SAFETY: clone initialized the output.
    let cloned = unsafe { output.assume_init() };
    assert_eq!(target, "hello world");
    assert_eq!(cloned, target);
    assert_ne!(cloned.as_ptr(), target.as_ptr());
    drop(target);
    assert_eq!(cloned, "hello world");
    assert_eq!(source, " world");
}

#[test]
fn native_abi_consuming_drop() {
    let drops = Rc::new(Cell::new(0));
    let mut storage = MaybeUninit::new(Tracked {
        payload: "owned backing storage".to_owned(),
        drops: drops.clone(),
    });
    let destroy: unsafe extern "C" fn(*mut Tracked) = probe_drop;
    // SAFETY: storage contains a live value and is never accessed as Tracked after consumption.
    unsafe {
        assert_eq!((*storage.as_ptr()).payload, "owned backing storage");
        destroy(storage.as_mut_ptr());
    }
    assert_eq!(drops.get(), 1);
    assert_eq!(Rc::strong_count(&drops), 1); // Fields were destroyed too.
    // MaybeUninit has no drop glue that could repeat destruction at scope exit.
}

#[test]
fn native_abi_optional_initialization() {
    // Known scalar bits let us check that None leaves output completely untouched.
    let mut output = MaybeUninit::new(0x1234_i64);
    let optional: extern "C" fn(i64, &mut MaybeUninit<i64>) -> bool = probe_optional;
    assert!(!optional(-1, &mut output));
    // SAFETY: None preserves the initialized sentinel.
    assert_eq!(unsafe { output.assume_init() }, 0x1234);
    assert!(optional(1_i64 << 40, &mut output));
    // SAFETY: Some initializes the output.
    assert_eq!(unsafe { output.assume_init() }, 1_i64 << 40);
}

#[test]
fn native_abi_failure_state_and_scalar_output() {
    let mut failure = FailureState::default();
    let mut output = MaybeUninit::new(0x1234_i64);
    let call: extern "C" fn(&mut FailureState, &String, &mut MaybeUninit<i64>) -> u32 =
        probe_fallible;
    let source = "bad".to_owned();
    assert_ne!(call(&mut failure, &source, &mut output), 0);
    // SAFETY: failure preserves the initialized sentinel.
    assert_eq!(unsafe { output.assume_init() }, 0x1234);
    drop(source);
    assert_eq!(failure.message.as_deref(), Some("invalid integer: bad"));

    // A nested host invocation owns separate state; success must not disturb either diagnostic.
    let mut nested = FailureState::default();
    let source = "1099511627776".to_owned();
    assert_eq!(call(&mut nested, &source, &mut output), 0);
    // SAFETY: success initializes the output.
    assert_eq!(unsafe { output.assume_init() }, 1_i64 << 40);
    assert_eq!(probe_fallible_unit(&mut failure, true), 0);
    assert!(nested.message.is_none());
    assert_eq!(failure.message.as_deref(), Some("invalid integer: bad"));
    drop(failure.message.take()); // The owning Rust runtime releases the diagnostic.
}

#[test]
fn native_abi_fallible_managed_and_unit_results() {
    let mut failure = FailureState::default();
    let mut output = MaybeUninit::uninit();
    let call: extern "C" fn(&mut FailureState, i64, &mut MaybeUninit<String>) -> u32 =
        probe_fallible_string;
    assert_ne!(call(&mut failure, -7, &mut output), 0);
    assert_eq!(
        failure.message.take().as_deref(),
        Some("negative value: -7")
    );
    assert_eq!(call(&mut failure, 42, &mut output), 0);
    // SAFETY: success initializes the output.
    assert_eq!(unsafe { output.assume_init() }, "42");
    assert!(failure.message.is_none());
    assert_eq!(probe_fallible_unit(&mut failure, true), 0);
    assert_ne!(probe_fallible_unit(&mut failure, false), 0);
    assert_eq!(failure.message.as_deref(), Some("unit failure"));
}
