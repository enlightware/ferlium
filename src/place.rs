// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Boxed and native-member places shared by the HIR and MIR interpreters.

use std::{collections::VecDeque, ptr::NonNull, rc::Rc};

use crate::{
    compiler::error::SourceFailureKind,
    eval::buffer,
    eval::{EvalCtx, ValOrMut},
    format::{FormatWith, write_with_separator},
    hir::value::{NativeValue, Value, ValueRef},
};

/// Borrowed storage in a boxed interpreter. Native members have no boxed `Value` slot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Place {
    Boxed { root: usize, path: Vec<isize> },
    NativeMember(Rc<NativeMember>),
}

/// One evaluated addressor result, retaining its receiver and typed replacement operation.
/// The descriptor owns no pointee storage; the selected member borrows its receiver.
#[derive(Debug)]
pub struct NativeMember {
    root: Place,
    pointer: NonNull<dyn NativeValue>,
    mutable: bool,
    replace: unsafe fn(*mut (), Value) -> Value,
}

impl PartialEq for NativeMember {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::addr_eq(self.pointer.as_ptr(), other.pointer.as_ptr())
            && self.mutable == other.mutable
            && self.root == other.root
    }
}
impl Eq for NativeMember {}

impl NativeMember {
    /// # Safety
    /// `pointer` denotes an initialized T rooted in `root` for the entire place borrow.
    /// Mutable exposure permits arbitrary valid T replacements and mutations without breaking
    /// the enclosing Rust value's invariants. The pointer must not require a suspended guard.
    pub(crate) unsafe fn place<T: NativeValue>(
        root: Place,
        pointer: *mut T,
        mutable: bool,
    ) -> Place {
        assert!(
            !pointer.is_null() && pointer.is_aligned(),
            "invalid native member pointer"
        );
        unsafe fn replace<T: NativeValue>(pointer: *mut (), value: Value) -> Value {
            let value = value
                .into_primitive_ty::<T>()
                .expect("native member replacement type");
            // SAFETY: caller establishes exclusive initialized storage; replace leaves it live.
            Value::native(unsafe { std::ptr::replace(pointer.cast::<T>(), value) })
        }
        Place::NativeMember(Rc::new(Self {
            root,
            pointer: NonNull::new(pointer as *mut dyn NativeValue).unwrap(),
            mutable,
            replace: replace::<T>,
        }))
    }

    fn receiver(&self) -> &Place {
        &self.root
    }

    /// Only called after resolving the receiver's lifetime through `Place::native_member`.
    fn borrow(&self) -> &dyn NativeValue {
        // SAFETY: the receiver borrow keeps the selected initialized member live.
        unsafe { self.pointer.as_ref() }
    }

    pub(crate) fn mutable<T: 'static>(&self) -> Option<*mut T> {
        assert!(self.mutable, "cannot mutate a shared native member");
        self.borrow()
            .as_any()
            .is::<T>()
            .then(|| self.pointer.as_ptr().cast::<T>())
    }

    fn replace(&self, value: Value) -> Value {
        assert!(self.mutable, "cannot replace a shared native member");
        // SAFETY: the interpreter's exclusive place access establishes the registered contract.
        unsafe { (self.replace)(self.pointer.as_ptr().cast(), value) }
    }
}

fn invalid_buffer_index(index: isize, len: usize) -> SourceFailureKind {
    SourceFailureKind::InvalidArgument(format!(
        "Buffer index {index} is out of bounds for buffer of length {len}"
    ))
}

impl Place {
    pub fn boxed(root: usize) -> Self {
        Self::Boxed {
            root,
            path: Vec::new(),
        }
    }

    pub(crate) fn boxed_parts(&self) -> (usize, &[isize]) {
        match self {
            Self::Boxed { root, path } => (*root, path),
            Self::NativeMember(_) => panic!("expected a boxed storage place"),
        }
    }

    /// Structural indexing applies only to boxed aggregates. Native members use Rust addressors.
    pub(crate) fn push_index(&mut self, index: isize) {
        match self {
            Self::Boxed { path, .. } => path.push(index),
            Self::NativeMember(_) => panic!("native members require explicit Rust addressors"),
        }
    }

    /// Return a path and an index of a variable in the environment that is for sure a Value
    fn resolved_path_and_index(&self, ctx: &EvalCtx) -> (VecDeque<isize>, usize) {
        let (mut index, path) = self.boxed_parts();
        let mut path = path.iter().copied().collect::<VecDeque<_>>();
        loop {
            match &ctx.environment[index] {
                ValOrMut::Val(_target) => {
                    break;
                }
                ValOrMut::Dictionary(_) => {
                    panic!("cannot mutably access trait dictionary metadata");
                }
                ValOrMut::Ref(_) => {
                    panic!("cannot mutably access shared reference storage");
                }
                ValOrMut::Mut(place) => {
                    let (root, parent_path) = place.boxed_parts();
                    index = root;
                    for &index in parent_path.iter().rev() {
                        path.push_front(index);
                    }
                }
            };
        }
        (path, index)
    }

    pub(crate) fn resolved(&self, ctx: &EvalCtx) -> Self {
        let Self::Boxed { root, path } = self else {
            return self.clone();
        };
        if let ValOrMut::Mut(parent) = &ctx.environment[*root] {
            let mut resolved = parent.resolved(ctx);
            for &index in path {
                resolved.push_index(index);
            }
            return resolved;
        }
        self.clone()
    }

    /// Mutably access a boxed storage slot, never the contents of a borrowed native member.
    pub fn boxed_mut<'c>(&self, ctx: &'c mut EvalCtx) -> Result<&'c mut Value, SourceFailureKind> {
        debug_assert!(
            self.native_member(ctx).is_none(),
            "native member must remain initialized; use typed mutation or replace"
        );
        let (path, index) = self.resolved_path_and_index(ctx);
        self.project_mut(ctx.environment[index].as_val_mut().unwrap(), &path)
    }

    /// Install a prepared whole-slot replacement, leaving the displaced value in that slot.
    pub(crate) fn replace_from_owned_slot(
        &self,
        ctx: &mut EvalCtx,
        replacement: &Place,
    ) -> Result<(), SourceFailureKind> {
        let (replacement_root, replacement_path) = replacement.boxed_parts();
        assert!(
            replacement_path.is_empty(),
            "replacement must be a whole owned slot"
        );
        if let Some(native) = self.native_member(ctx).cloned() {
            let replacement = replacement.boxed_mut(ctx)?;
            let value = std::mem::replace(replacement, Value::uninit());
            // Selection and slot resolution are complete; typed replacement cannot source-fail.
            // SAFETY: MIR supplies an independently owned replacement temporary, disjoint from
            // the member's receiver. Writing through the member pointer therefore cannot alias
            // this live mutable borrow of the replacement slot or invalidate the receiver.
            *replacement = native.replace(value);
            return Ok(());
        }
        let (path, index) = self.resolved_path_and_index(ctx);
        let [destination, replacement] = ctx
            .environment
            .get_disjoint_mut([index, replacement_root])
            .expect("replacement and destination must be distinct allocated slots");
        let replacement = replacement.as_val_mut().expect("replacement must be owned");
        // Resolve the destination before changing either slot; projection can report failure.
        let destination = self.project_mut(destination.as_val_mut().unwrap(), &path)?;
        std::mem::swap(replacement, destination);
        Ok(())
    }

    fn project_mut<'v>(
        &self,
        mut target: &'v mut Value,
        path: &VecDeque<isize>,
    ) -> Result<&'v mut Value, SourceFailureKind> {
        for &index in path.iter() {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get_mut(index as usize).unwrap(),
                // A payload-free case has no slot until something writes one.
                Variant { .. } if index == 0 => target.variant_payload_mut().unwrap(),
                Native(primitive) => {
                    let buffer = primitive
                        .as_mut()
                        .as_mut_any()
                        .downcast_mut::<buffer::Buffer>()
                        .unwrap();
                    let len = buffer.capacity();
                    match buffer.get_mut_signed(index) {
                        Some(target) => target,
                        None => {
                            return Err(invalid_buffer_index(index, len));
                        }
                    }
                }
                Uninit => panic!("cannot access a field of an uninitialized value"),
                Variant { .. } => panic!("Cannot access a variant payload with a non-zero index"),
                _ => panic!(
                    "Cannot access a non-compound value while following mutable place path: index {}, full place {:?}",
                    index, self
                ),
            };
        }
        Ok(target)
    }

    pub(crate) fn target_ref_allow_uninit<'c>(
        &'c self,
        ctx: &'c EvalCtx,
    ) -> Result<ValueRef<'c>, SourceFailureKind> {
        if let Some(native) = self.native_member(ctx) {
            return Ok(ValueRef::Native(native.borrow()));
        }
        let (mut index, path) = self.boxed_parts();
        let mut path = path.iter().copied().collect::<VecDeque<_>>();
        let mut target = loop {
            match &ctx.environment[index] {
                ValOrMut::Val(target) => break target,
                ValOrMut::Dictionary(_) => {
                    panic!("cannot read trait dictionary metadata as a Value")
                }
                ValOrMut::Ref(target) => {
                    // SAFETY: see `ValOrMut::as_primitive`.
                    break unsafe { &**target };
                }
                ValOrMut::Mut(place) => {
                    let (root, parent_path) = place.boxed_parts();
                    index = root;
                    for &index in parent_path.iter().rev() {
                        path.push_front(index);
                    }
                }
            };
        };
        for &index in path.iter() {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get(index as usize).unwrap(),
                Variant {
                    payload: Some(payload),
                    ..
                } if index == 0 => payload,
                Native(primitive) => {
                    let buffer = NativeValue::as_any(primitive.as_ref())
                        .downcast_ref::<buffer::Buffer>()
                        .unwrap();
                    let len = buffer.capacity();
                    match buffer.get_signed(index) {
                        Some(target) => target,
                        None => {
                            return Err(invalid_buffer_index(index, len));
                        }
                    }
                }
                Uninit => panic!("cannot read a field of an uninitialized value"),
                Variant { .. } => panic!("Cannot access a variant payload with a non-zero index"),
                other => panic!(
                    "Cannot access a non-compound value while following place path: target {:?}, index {}, full place {:?}",
                    other, index, self
                ),
            };
        }
        Ok(ValueRef::Boxed(target))
    }

    /// Returns the target when every intermediate projection has materialized storage.
    /// An uninitialized intermediate or an absent variant payload is an uninitialized place.
    pub(crate) fn target_ref_if_materialized<'c>(
        &'c self,
        ctx: &'c EvalCtx,
    ) -> Result<Option<ValueRef<'c>>, SourceFailureKind> {
        if let Some(native) = self.native_member(ctx) {
            return Ok(Some(ValueRef::Native(native.borrow())));
        }
        let (mut index, path) = self.boxed_parts();
        let mut path = path.iter().copied().collect::<VecDeque<_>>();
        let mut target = loop {
            match &ctx.environment[index] {
                ValOrMut::Val(target) => break target,
                ValOrMut::Dictionary(_) => {
                    panic!("cannot read trait dictionary metadata as a Value")
                }
                ValOrMut::Ref(target) => {
                    // SAFETY: the referent outlives this borrow.
                    break unsafe { &**target };
                }
                ValOrMut::Mut(place) => {
                    let (root, parent_path) = place.boxed_parts();
                    index = root;
                    for &index in parent_path.iter().rev() {
                        path.push_front(index);
                    }
                }
            };
        };
        for &index in &path {
            use Value::*;
            target = match target {
                Tuple(tuple) => tuple.get(index as usize).unwrap(),
                Variant {
                    payload: Some(payload),
                    ..
                } if index == 0 => payload,
                Variant { payload: None, .. } if index == 0 => return Ok(None),
                Native(primitive) => {
                    let buffer = NativeValue::as_any(primitive.as_ref())
                        .downcast_ref::<buffer::Buffer>()
                        .unwrap();
                    let len = buffer.capacity();
                    match buffer.get_signed(index) {
                        Some(target) => target,
                        None => return Err(invalid_buffer_index(index, len)),
                    }
                }
                Uninit => return Ok(None),
                Variant { .. } => {
                    panic!("Cannot access a variant payload with a non-zero index")
                }
                other => panic!(
                    "Cannot access a non-compound value while following place path: target {:?}, index {}, full place {:?}",
                    other, index, self
                ),
            };
        }
        Ok(Some(ValueRef::Boxed(target)))
    }

    /// Borrow the selected boxed value or native member without transferring ownership.
    pub fn target_ref<'c>(&'c self, ctx: &'c EvalCtx) -> Result<ValueRef<'c>, SourceFailureKind> {
        let target = self.target_ref_allow_uninit(ctx)?;
        if target.is_uninit() {
            panic!("attempted to read an uninitialized value");
        }
        Ok(target)
    }

    /// Follow parameter aliases without losing the selected member or replaying its addressor.
    pub(crate) fn native_member<'a>(&'a self, ctx: &'a EvalCtx) -> Option<&'a Rc<NativeMember>> {
        match self {
            Self::NativeMember(native) => {
                assert!(
                    native
                        .root
                        .target_ref_if_materialized(ctx)
                        .expect("native member receiver must remain addressable")
                        .is_some_and(|value| !value.is_uninit()),
                    "native member receiver must remain initialized"
                );
                Some(native)
            }
            Self::Boxed { root, path } => {
                if let ValOrMut::Mut(parent) = &ctx.environment[*root] {
                    let native = parent.native_member(ctx);
                    assert!(
                        native.is_none() || path.is_empty(),
                        "native members require explicit Rust addressors"
                    );
                    native
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn replace_value(
        &self,
        ctx: &mut EvalCtx,
        value: Value,
    ) -> Result<Value, SourceFailureKind> {
        if let Some(native) = self.native_member(ctx) {
            Ok(native.replace(value))
        } else {
            match self.boxed_mut(ctx) {
                Ok(target) => Ok(std::mem::replace(target, value)),
                Err(error) => {
                    value.discard_storage();
                    Err(error)
                }
            }
        }
    }
}

impl FormatWith<EvalCtx<'_>> for Place {
    fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>, data: &EvalCtx<'_>) -> std::fmt::Result {
        match self {
            Place::NativeMember(native) => write!(
                f,
                "native member of {}",
                native.receiver().format_with(data)
            ),
            Place::Boxed { root, path } => {
                let ctx = data;
                let relative_index = *root as isize - ctx.frame_base as isize;
                write!(f, "@{relative_index}")?;
                if !path.is_empty() {
                    write!(f, ".")?;
                }
                write_with_separator(path, ".", f)?;
                if relative_index < 0 {
                    write!(f, " (in a previous frame)")?;
                }
                Ok(())
            }
        }
    }
}
