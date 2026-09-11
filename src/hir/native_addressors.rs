//! Native member entries use raw pointers: the returned borrow survives the C call.
use super::*;
use crate::{
    eval::PlaceResult,
    place::{NativeMember, Place},
};

fn receiver_place(arg: &ValOrMut, ctx: &EvalCtx) -> Result<Place, RuntimeError> {
    match arg {
        ValOrMut::Mut(place) => Ok(place.resolved(ctx)),
        _ => Err(RuntimeError::new_native(
            SourceFailureKind::InvalidArgument("native addressor receiver must be a place".into()),
        )),
    }
}

macro_rules! addressor {
    ($name:ident, $fallible:ident, $pointer:ty, $result:ty, $parameter:ident, $mutable:expr) => {
        /// A rooted native member entry. Registration is unsafe because Rust cannot check
        /// pointer rooting, stability, or the enclosing value's mutation invariants.
        pub struct $name<T: NativeValue, M: NativeValue>(unsafe extern "C" fn($pointer) -> $result);
        impl<T: NativeValue, M: NativeValue> Clone for $name<T, M> {
            fn clone(&self) -> Self {
                Self(self.0)
            }
        }
        impl<T: NativeValue, M: NativeValue> $name<T, M> {
            /// # Safety
            /// The entry returns an aligned initialized member rooted in its receiver, stable
            /// throughout the receiver borrow. It must not retain pointers, require a guard,
            /// mutate a shared receiver, or panic. Mutable access must permit arbitrary valid
            /// member mutation and replacement without breaking the receiver's Rust invariants.
            pub unsafe fn new(
                entry: unsafe extern "C" fn($pointer) -> $result,
            ) -> NativeCallable<Self> {
                NativeCallable::new(Self(entry))
            }
        }
        impl<T: NativeValue, M: NativeValue> sealed::Entry for $name<T, M> {}
        impl<T: NativeValue, M: NativeValue> EntryFunction for $name<T, M> {
            fn entry(&self) -> NativeEntry {
                NativeEntry::new(
                    self.0 as *const (),
                    NativeSignature {
                        failure: NativeFailureConvention::Infallible,
                        parameters: vec![NativeParameter::$parameter(NativeLayout::of::<T>())],
                        result: NativeResult::Addressor {
                            pointee: NativeLayout::of::<M>(),
                            root: 0,
                            mutable: $mutable,
                        },
                    },
                )
            }
            fn invoke(&self, args: &[ValOrMut], ctx: &mut EvalCtx) -> EvalControlFlowResult {
                let root = receiver_place(&args[0], ctx)?;
                let pointer = if $mutable {
                    args[0]
                        .as_mut_primitive::<T>(ctx)
                        .map_err(RuntimeError::new_native)?
                        .expect("native addressor receiver") as *mut T
                } else {
                    // The macro unifies pointer types here; shared entries receive *const T
                    // and the resulting place never permits mutation through this pointer.
                    function::extract_native_ref::<T>(&args[0], ctx)
                        .map_err(RuntimeError::new_native)? as *const T as *mut T
                };
                // SAFETY: typed extraction and exclusive/shared place access establish inputs;
                // unsafe registration guarantees the returned member contract.
                let pointer = unsafe { (self.0)(pointer as $pointer) };
                let place = unsafe { NativeMember::place(root, pointer as *mut M, $mutable) };
                cont(Value::native(PlaceResult::new(place)))
            }
        }

        /// Fallible member selection, using status and success-only trailing pointer storage.
        pub struct $fallible<T: NativeValue, M: NativeValue>(
            unsafe extern "C" fn(
                &mut NativeFailureState,
                $pointer,
                &mut MaybeUninit<$result>,
            ) -> u32,
        );
        impl<T: NativeValue, M: NativeValue> Clone for $fallible<T, M> {
            fn clone(&self) -> Self {
                Self(self.0)
            }
        }
        impl<T: NativeValue, M: NativeValue> $fallible<T, M> {
            /// # Safety
            /// The same rooted member contract as the infallible entry applies. Success writes
            /// one valid pointer; failure records a diagnostic and leaves output uninitialized.
            /// Both exits preserve the receiver's initialization and Rust invariants.
            pub unsafe fn new(
                entry: unsafe extern "C" fn(
                    &mut NativeFailureState,
                    $pointer,
                    &mut MaybeUninit<$result>,
                ) -> u32,
            ) -> NativeCallable<Self> {
                NativeCallable::new(Self(entry))
            }
        }
        impl<T: NativeValue, M: NativeValue> sealed::Entry for $fallible<T, M> {}
        impl<T: NativeValue, M: NativeValue> EntryFunction for $fallible<T, M> {
            fn entry(&self) -> NativeEntry {
                NativeEntry::new(
                    self.0 as *const (),
                    NativeSignature {
                        failure: NativeFailureConvention::StatusWithState,
                        parameters: vec![NativeParameter::$parameter(NativeLayout::of::<T>())],
                        result: NativeResult::Addressor {
                            pointee: NativeLayout::of::<M>(),
                            root: 0,
                            mutable: $mutable,
                        },
                    },
                )
            }
            fn invoke(&self, args: &[ValOrMut], ctx: &mut EvalCtx) -> EvalControlFlowResult {
                let root = receiver_place(&args[0], ctx)?;
                let pointer = if $mutable {
                    args[0]
                        .as_mut_primitive::<T>(ctx)
                        .map_err(RuntimeError::new_native)?
                        .expect("native addressor receiver") as *mut T
                } else {
                    // As above, the shared entry only receives a const receiver pointer.
                    function::extract_native_ref::<T>(&args[0], ctx)
                        .map_err(RuntimeError::new_native)? as *const T as *mut T
                };
                let mut failure = NativeFailureState::default();
                let mut output = MaybeUninit::uninit();
                // SAFETY: registered entry protocol and typed, borrowed receiver.
                let status = unsafe { (self.0)(&mut failure, pointer as $pointer, &mut output) };
                failure.finish(status)?;
                let place =
                    unsafe { NativeMember::place(root, output.assume_init() as *mut M, $mutable) };
                cont(Value::native(PlaceResult::new(place)))
            }
        }
    };
}

addressor!(
    NativeAddressorRef,
    NativeFallibleAddressorRef,
    *const T,
    *const M,
    Shared,
    false
);
addressor!(
    NativeAddressorMut,
    NativeFallibleAddressorMut,
    *mut T,
    *mut M,
    Mutable,
    true
);

#[cfg(test)]
mod tests {
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use super::*;
    use crate::{
        CompilerSession, compiler::error::RuntimeErrorKind, eval::EvalCtx,
        hir::value::NativeValueType, types::effects::no_effects,
    };

    unsafe extern "C" fn shared(value: *const isize) -> *const isize {
        value
    }
    unsafe extern "C" fn mutable(value: *mut isize) -> *mut isize {
        value
    }

    #[test]
    fn native_member_registration_checks_root_and_access() {
        let function =
            unsafe { NativeAddressorRef::new(shared) }.description(["self"], "", no_effects());
        let signature = function.code.native_entry().unwrap().signature();
        signature.validate(&function.definition).unwrap();
        let mut definition = function.definition.clone();
        definition.result_rooted_in = None;
        assert_eq!(
            signature.validate(&definition),
            Err(NativeContractError::AddressorRoot)
        );
        let mut signature = signature.clone();
        signature.result = NativeResult::Addressor {
            pointee: NativeLayout::of::<isize>(),
            root: 0,
            mutable: true,
        };
        assert_eq!(
            signature.validate(&function.definition),
            Err(NativeContractError::AddressorRoot)
        );
        definition = function.definition.clone();
        definition.result_convention = CallResultConvention::Value;
        assert_eq!(
            signature.validate(&definition),
            Err(NativeContractError::ResultConvention)
        );
    }

    #[test]
    fn native_member_transport_exemption_is_only_for_the_root() {
        let function =
            unsafe { NativeAddressorRef::new(shared) }.description(["self"], "", no_effects());
        let mut definition = function.definition.clone();
        definition
            .ty_scheme
            .ty
            .args
            .push(definition.ty_scheme.ty.args[0]);
        let mut signature = function.code.native_entry().unwrap().signature().clone();
        signature
            .parameters
            .push(NativeParameter::Shared(NativeLayout::of::<isize>()));
        for root in [0, 1] {
            definition.result_rooted_in = Some(root);
            signature.result = NativeResult::Addressor {
                pointee: NativeLayout::of::<isize>(),
                root,
                mutable: false,
            };
            assert_eq!(
                signature.validate(&definition),
                Err(NativeContractError::ArgumentTransport {
                    index: 1 - root as usize
                })
            );
            signature.parameters[1 - root as usize] =
                NativeParameter::Scalar(NativeLayout::of::<isize>(), NativeScalar::Int);
            signature.validate(&definition).unwrap();
            signature.parameters[1 - root as usize] =
                NativeParameter::Shared(NativeLayout::of::<isize>());
        }
    }

    #[test]
    fn native_member_non_place_receiver_reports_invalid_argument() {
        let session = CompilerSession::new();
        let mut ctx = EvalCtx::new(session.std_module().module_id(), &session);
        let callable = unsafe { NativeAddressorRef::new(shared) };
        let value = Value::native(7isize);
        for arg in [ValOrMut::Ref(&value), ValOrMut::Val(Value::native(7isize))] {
            let error = callable.function.invoke(&[arg], &mut ctx).unwrap_err();
            assert!(matches!(
                error.kind(),
                RuntimeErrorKind::SourceFailure(SourceFailureKind::InvalidArgument(_))
            ));
        }
    }

    #[test]
    fn native_member_boxed_guards_prevent_consumption_and_shared_writes() {
        let session = CompilerSession::new();
        let mut ctx = EvalCtx::new(session.std_module().module_id(), &session);
        ctx.environment.push(ValOrMut::Val(Value::native(7isize)));
        let root = Place::Boxed {
            root: 0,
            path: Vec::new(),
        };
        let shared = unsafe { NativeAddressorRef::new(shared) };
        let place = shared
            .function
            .invoke(&[ValOrMut::Mut(root.clone())], &mut ctx)
            .unwrap()
            .into_value()
            .into_primitive_ty::<PlaceResult>()
            .unwrap()
            .place()
            .clone();
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                let _ = ValOrMut::Mut(place.clone()).as_mut_primitive::<isize>(&mut ctx);
            }))
            .is_err()
        );
        let mutable = unsafe { NativeAddressorMut::new(mutable) };
        let place = mutable
            .function
            .invoke(&[ValOrMut::Mut(root)], &mut ctx)
            .unwrap()
            .into_value()
            .into_primitive_ty::<PlaceResult>()
            .unwrap()
            .place()
            .clone();
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                let _ = place.boxed_mut(&mut ctx);
            }))
            .is_err()
        );
        assert_eq!(
            place.target_ref(&ctx).unwrap().as_primitive_ty::<isize>(),
            Some(&7)
        );
        ctx.truncate_environment_storage(0);
    }

    #[test]
    fn native_member_borrow_replacement_and_selection_lifetime() {
        use std::{cell::Cell, rc::Rc};

        #[derive(Debug)]
        struct Counter {
            value: isize,
            selections: usize,
            drops: Rc<Cell<usize>>,
        }
        impl NativeValueType for Counter {}
        impl Drop for Counter {
            fn drop(&mut self) {
                self.drops.set(self.drops.get() + 1);
            }
        }
        unsafe extern "C" fn select(counter: *mut Counter) -> *mut isize {
            unsafe {
                (*counter).selections += 1;
                &raw mut (*counter).value
            }
        }

        let session = CompilerSession::new();
        let mut ctx = EvalCtx::new(session.std_module().module_id(), &session);
        let drops = Rc::new(Cell::new(0));
        ctx.environment
            .push(ValOrMut::Val(Value::tuple([Value::native(Counter {
                value: 7,
                selections: 0,
                drops: drops.clone(),
            })])));
        let root = Place::Boxed {
            root: 0,
            path: vec![0],
        };
        // SAFETY: select returns the initialized integer field, with no guard or retained input.
        let addressor = unsafe { NativeAddressorMut::new(select) };
        let member = addressor
            .function
            .invoke(&[ValOrMut::Mut(root.clone())], &mut ctx)
            .unwrap()
            .into_value()
            .into_primitive_ty::<PlaceResult>()
            .unwrap()
            .place()
            .clone();
        ctx.environment.push(ValOrMut::Mut(member.clone()));
        ctx.environment.push(ValOrMut::Mut(Place::boxed(1)));
        let alias = Place::boxed(2);
        for _ in 0..3 {
            assert_eq!(
                alias.target_ref(&ctx).unwrap().as_primitive_ty::<isize>(),
                Some(&7)
            );
        }
        *ValOrMut::Mut(alias.clone())
            .as_mut_primitive::<isize>(&mut ctx)
            .unwrap()
            .unwrap() = 9;
        ctx.environment.push(ValOrMut::Val(Value::native(13isize)));
        alias
            .replace_from_owned_slot(&mut ctx, &Place::boxed(3))
            .unwrap();
        assert_eq!(
            alias.target_ref(&ctx).unwrap().as_primitive_ty::<isize>(),
            Some(&13)
        );
        assert_eq!(
            Place::boxed(3)
                .target_ref(&ctx)
                .unwrap()
                .as_primitive_ty::<isize>(),
            Some(&9)
        );
        assert_eq!(
            root.target_ref(&ctx)
                .unwrap()
                .as_primitive_ty::<Counter>()
                .unwrap()
                .selections,
            1
        );
        // Reclaiming aliases and the detached old value does not consume the receiver.
        ctx.truncate_environment_storage(1);
        drop(member);
        assert_eq!(drops.get(), 0);
        assert_eq!(
            root.target_ref(&ctx)
                .unwrap()
                .as_primitive_ty::<Counter>()
                .unwrap()
                .value,
            13
        );
        ctx.truncate_environment_storage(0);
        assert_eq!(drops.get(), 1);
    }
}
