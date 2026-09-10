// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Scalar storage with real aligned allocations and checked address provenance. The scalar-only
//! slice tracks initialization per allocation; aggregate/subobject initialization is future work.

use super::{invalid, unsupported};
use crate::{
    eval::RuntimeError,
    hir::{
        native_functions::NativeLayout,
        value::{LiteralValue, Value},
    },
    std::math::Float,
    types::r#type::Type,
};
use std::{
    alloc::{Layout, alloc, dealloc},
    ptr::NonNull,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ScalarKind {
    Unit,
    Bool,
    Int,
    Float,
}

impl ScalarKind {
    pub(super) fn for_type(ty: Type) -> Result<Self, RuntimeError> {
        if ty == Type::primitive::<()>() || ty == Type::never() {
            Ok(Self::Unit)
        } else if ty == Type::primitive::<bool>() {
            Ok(Self::Bool)
        } else if ty == Type::primitive::<isize>() {
            Ok(Self::Int)
        } else if ty == Type::primitive::<Float>() {
            Ok(Self::Float)
        } else {
            Err(unsupported("non-scalar storage types"))
        }
    }

    pub(super) fn for_native(layout: NativeLayout) -> Result<Self, RuntimeError> {
        let kind = Self::for_type(layout.ty)?;
        let expected = match kind {
            Self::Unit => NativeLayout::of::<()>(),
            Self::Bool => NativeLayout::of::<bool>(),
            Self::Int => NativeLayout::of::<isize>(),
            Self::Float => NativeLayout::of::<Float>(),
        };
        if expected != layout {
            return Err(invalid("native scalar layout mismatch"));
        }
        Ok(kind)
    }

    fn layout(self) -> Layout {
        match self {
            Self::Unit => Layout::new::<()>(),
            Self::Bool => Layout::new::<bool>(),
            Self::Int => Layout::new::<isize>(),
            Self::Float => Layout::new::<Float>(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) enum Scalar {
    Unit,
    Bool(bool),
    Int(isize),
    Float(Float),
}

impl Scalar {
    /// Address of a by-value transport copy. The caller must keep this scalar stationary until
    /// the native call finishes; no Rust reference to the containing enum may overlap that call.
    pub(super) fn pointer(&mut self) -> *mut u8 {
        match self {
            Self::Unit => NonNull::<u8>::dangling().as_ptr(),
            Self::Bool(value) => std::ptr::from_mut(value).cast(),
            Self::Int(value) => std::ptr::from_mut(value).cast(),
            Self::Float(value) => std::ptr::from_mut(value).cast(),
        }
    }
    pub(super) fn kind(self) -> ScalarKind {
        match self {
            Self::Unit => ScalarKind::Unit,
            Self::Bool(_) => ScalarKind::Bool,
            Self::Int(_) => ScalarKind::Int,
            Self::Float(_) => ScalarKind::Float,
        }
    }
    pub(super) fn from_value(value: &Value) -> Result<Self, RuntimeError> {
        if value.as_primitive_ty::<()>().is_some() {
            Ok(Self::Unit)
        } else if let Some(v) = value.as_primitive_ty::<bool>() {
            Ok(Self::Bool(*v))
        } else if let Some(v) = value.as_primitive_ty::<isize>() {
            Ok(Self::Int(*v))
        } else if let Some(v) = value.as_primitive_ty::<Float>() {
            Ok(Self::Float(*v))
        } else {
            Err(unsupported("non-scalar host arguments"))
        }
    }
    pub(super) fn from_literal(value: &LiteralValue) -> Result<Self, RuntimeError> {
        if value.as_primitive_ty::<()>().is_some() {
            Ok(Self::Unit)
        } else if let Some(v) = value.as_primitive_ty::<bool>() {
            Ok(Self::Bool(*v))
        } else if let Some(v) = value.as_primitive_ty::<isize>() {
            Ok(Self::Int(*v))
        } else if let Some(v) = value.as_primitive_ty::<Float>() {
            Ok(Self::Float(*v))
        } else {
            Err(unsupported("non-scalar constants"))
        }
    }
    pub(super) fn boxed(self) -> Value {
        match self {
            Self::Unit => Value::unit(),
            Self::Bool(v) => Value::native(v),
            Self::Int(v) => Value::native(v),
            Self::Float(v) => Value::native(v),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Address {
    allocation: usize,
    generation: u64,
    offset: usize,
    pub(super) kind: ScalarKind,
}

struct Allocation {
    pointer: NonNull<u8>,
    layout: Layout,
    kind: ScalarKind,
    initialized: bool,
    generation: u64,
}

impl Drop for Allocation {
    fn drop(&mut self) {
        // SAFETY: this owner holds the allocation returned by alloc with exactly this layout.
        // Scalar payloads require no destructor, including on failure/poisoning exits.
        unsafe { dealloc(self.pointer.as_ptr(), self.layout) };
    }
}

#[derive(Default)]
pub(super) struct Memory {
    allocations: Vec<Allocation>,
    generation: u64,
}

impl Memory {
    pub(super) fn len(&self) -> usize {
        self.allocations.len()
    }
    pub(super) fn restore(&mut self, marker: usize) {
        self.allocations.truncate(marker);
    }

    pub(super) fn allocate(&mut self, kind: ScalarKind) -> Result<Address, RuntimeError> {
        self.generation = self
            .generation
            .checked_add(1)
            .ok_or_else(|| invalid("allocation identity exhausted"))?;
        let scalar_layout = kind.layout();
        // Zero-sized values still get a unique live, aligned pointer and an initialization bit.
        let layout =
            Layout::from_size_align(scalar_layout.size().max(1), scalar_layout.align()).unwrap();
        // SAFETY: layout is nonzero and valid. A null allocation becomes a diagnostic, not a dereference.
        let pointer = NonNull::new(unsafe { alloc(layout) })
            .ok_or_else(|| invalid("physical allocation failed"))?;
        let address = Address {
            allocation: self.len(),
            generation: self.generation,
            offset: 0,
            kind,
        };
        self.allocations.push(Allocation {
            pointer,
            layout,
            kind,
            initialized: false,
            generation: self.generation,
        });
        Ok(address)
    }

    fn allocation(&self, address: Address) -> Result<&Allocation, RuntimeError> {
        let allocation = self
            .allocations
            .get(address.allocation)
            .ok_or_else(|| invalid("address outlived its allocation"))?;
        if allocation.generation != address.generation {
            return Err(invalid("stale allocation address"));
        }
        let layout = address.kind.layout();
        if address
            .offset
            .checked_add(layout.size())
            .is_none_or(|end| end > allocation.kind.layout().size())
        {
            return Err(invalid("address outside allocation bounds"));
        }
        if !address.offset.is_multiple_of(layout.align()) {
            return Err(invalid("misaligned address"));
        }
        // No type punning: initialization guarantees a valid Rust scalar, not just initialized bytes.
        if address.kind != allocation.kind || address.offset != 0 {
            return Err(invalid("incompatible scalar storage view"));
        }
        Ok(allocation)
    }

    pub(super) fn pointer(&self, address: Address) -> Result<*mut u8, RuntimeError> {
        Ok(self.allocation(address)?.pointer.as_ptr())
    }
    pub(super) fn initialized(&self, address: Address) -> Result<bool, RuntimeError> {
        Ok(self.allocation(address)?.initialized)
    }
    pub(super) fn mark_initialized(&mut self, address: Address) -> Result<(), RuntimeError> {
        if self.initialized(address)? {
            return Err(invalid("overwriting initialized storage"));
        }
        self.allocations[address.allocation].initialized = true;
        Ok(())
    }
    pub(super) fn clear(&mut self, address: Address) -> Result<(), RuntimeError> {
        self.allocation(address)?;
        self.allocations[address.allocation].initialized = false;
        Ok(())
    }
    pub(super) fn read(&self, address: Address) -> Result<Scalar, RuntimeError> {
        if !self.initialized(address)? {
            return Err(invalid("read of uninitialized storage"));
        }
        let pointer = self.pointer(address)?;
        // SAFETY: the checked allocation has this exact scalar type, alignment and initialization.
        // Only typed scalar writes or the matching trusted native adapter can initialize it.
        Ok(unsafe {
            match address.kind {
                ScalarKind::Unit => Scalar::Unit,
                ScalarKind::Bool => Scalar::Bool(pointer.cast::<bool>().read()),
                ScalarKind::Int => Scalar::Int(pointer.cast::<isize>().read()),
                ScalarKind::Float => Scalar::Float(pointer.cast::<Float>().read()),
            }
        })
    }
    pub(super) fn write(&mut self, address: Address, value: Scalar) -> Result<(), RuntimeError> {
        if value.kind() != address.kind {
            return Err(invalid("scalar store type mismatch"));
        }
        let pointer = self.pointer(address)?;
        // MIR permits overwriting LIVE_NO_DROP storage. Every supported scalar is TrivialCopy.
        // SAFETY: the destination is live, aligned and correctly sized; Scalar has no destructor.
        unsafe {
            match value {
                Scalar::Unit => (),
                Scalar::Bool(v) => pointer.cast::<bool>().write(v),
                Scalar::Int(v) => pointer.cast::<isize>().write(v),
                Scalar::Float(v) => pointer.cast::<Float>().write(v),
            }
        }
        self.allocations[address.allocation].initialized = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn physical_memory_checks_initialization_bounds_and_lifetimes() {
        let mut memory = Memory::default();
        let address = memory.allocate(ScalarKind::Int).unwrap();
        assert_eq!(
            memory.pointer(address).unwrap() as usize % align_of::<isize>(),
            0
        );
        assert!(memory.read(address).is_err());
        memory.write(address, Scalar::Int(42)).unwrap();
        assert_eq!(memory.read(address).unwrap(), Scalar::Int(42));
        memory.write(address, Scalar::Int(7)).unwrap();
        assert_eq!(memory.read(address).unwrap(), Scalar::Int(7));
        assert!(
            memory
                .pointer(Address {
                    offset: usize::MAX,
                    ..address
                })
                .is_err()
        );
        assert!(
            memory
                .pointer(Address {
                    offset: 1,
                    ..address
                })
                .is_err()
        );
        assert!(
            memory
                .read(Address {
                    kind: ScalarKind::Bool,
                    ..address
                })
                .is_err()
        );
        memory.clear(address).unwrap();
        assert!(memory.read(address).is_err());
        memory.restore(0);
        assert!(memory.pointer(address).is_err());
        let replacement = memory.allocate(ScalarKind::Int).unwrap();
        assert_ne!(address, replacement);
        assert!(memory.pointer(address).is_err());
        let unit = memory.allocate(ScalarKind::Unit).unwrap();
        assert!(!memory.initialized(unit).unwrap());
        memory.write(unit, Scalar::Unit).unwrap();
        assert_eq!(memory.read(unit).unwrap(), Scalar::Unit);
        memory.restore(0);
        assert_eq!(memory.len(), 0);
    }
}
