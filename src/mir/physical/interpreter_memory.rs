// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! ABI-layout storage with checked provenance, typed subobjects and leaf initialization.

use super::{invalid, unsupported};
use crate::{
    Location,
    containers::SVec2,
    eval::RuntimeError,
    hir::{
        native_functions::NativeLayout,
        value::{LiteralValue, Value},
    },
    module::{ProjectionIndex, id::Id},
    std::{
        math::Float,
        value::{TypeLayoutEnv, product_layout_spec, product_member_types, value_layout_for_type},
    },
    types::r#type::Type,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    alloc::{Layout, alloc, dealloc},
    ptr::NonNull,
    rc::Rc,
};

// Capability bounds, not an invocation-wide memory quota. Check before layout computation and
// flattening, which otherwise expand a compact type DAG into an arbitrarily large tree.
const MAX_STORAGE_LEAVES: usize = 4096;
const MAX_STORAGE_DEPTH: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum ScalarKind {
    Unit,
    Bool,
    Int,
    Float,
}

impl ScalarKind {
    pub(super) fn ty(self) -> Type {
        match self {
            Self::Unit => Type::primitive::<()>(),
            Self::Bool => Type::primitive::<bool>(),
            Self::Int => Type::primitive::<isize>(),
            Self::Float => Type::primitive::<Float>(),
        }
    }
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

/// A register snapshot contains typed scalar leaves, never boxed guest values or padding bytes.
/// Absent leaves are retained only by replacement of partially initialized storage.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct StoredValue {
    pub(super) ty: Type,
    leaves: SVec2<Option<Scalar>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Address {
    allocation: usize,
    generation: u64,
    offset: usize,
    pub(super) ty: Type,
}

struct StorageLayout {
    ty: Type,
    layout: Layout,
    depth: usize,
    // Logical order, independent of the ABI's compact-record field order.
    members: Option<Vec<(usize, Rc<StorageLayout>)>>,
    leaves: Vec<(usize, ScalarKind)>,
}

impl StorageLayout {
    fn scalar(ty: Type, kind: ScalarKind) -> Self {
        Self {
            ty,
            layout: kind.layout(),
            depth: 0,
            members: None,
            leaves: vec![(0, kind)],
        }
    }

    fn product(
        ty: Type,
        layout: Layout,
        members: Vec<(usize, Rc<StorageLayout>)>,
    ) -> Result<Self, RuntimeError> {
        fn check_extent(parent: Layout, offset: usize, child: Layout) -> Result<(), RuntimeError> {
            if offset
                .checked_add(child.size())
                .is_none_or(|end| end > parent.size())
            {
                return Err(invalid("product subobject outside layout bounds"));
            }
            if parent.align() < child.align() || !offset.is_multiple_of(child.align()) {
                return Err(invalid("misaligned product subobject"));
            }
            Ok(())
        }
        let depth = 1 + members
            .iter()
            .map(|(_, member)| member.depth)
            .max()
            .unwrap_or(0);
        if depth > MAX_STORAGE_DEPTH {
            return Err(unsupported("product storage nesting limit"));
        }
        // Distinct zero-sized products may have observable destructors but share a typed address.
        // They need ownership identities beyond address-based leaf flags. Canonical unit is scalar.
        if layout.size() == 0 {
            return Err(unsupported("zero-sized product ownership"));
        }
        let mut leaves = Vec::new();
        let mut identities = FxHashSet::default();
        let mut extents = Vec::new();
        for (offset, member) in &members {
            check_extent(layout, *offset, member.layout)?;
            if member.layout.size() != 0 {
                extents.push((*offset, offset + member.layout.size()));
            }
            if member.leaves.len() > MAX_STORAGE_LEAVES - leaves.len() {
                return Err(unsupported("product storage leaf limit"));
            }
            for (inner, kind) in &member.leaves {
                check_extent(member.layout, *inner, kind.layout())?;
                let offset = offset
                    .checked_add(*inner)
                    .ok_or_else(|| invalid("product offset overflow"))?;
                check_extent(layout, offset, kind.layout())?;
                if !identities.insert((offset, *kind)) {
                    // Moving one co-located unit must not clear its sibling's presence flag.
                    return Err(unsupported("co-located zero-sized fields"));
                }
                leaves.push((offset, *kind));
            }
        }
        extents.sort_unstable();
        if extents.windows(2).any(|pair| pair[0].1 > pair[1].0) {
            return Err(invalid("overlapping product members"));
        }
        Ok(Self {
            ty,
            layout,
            depth,
            members: Some(members),
            leaves,
        })
    }

    /// Ignore nominal wrappers, but preserve the logical member tree and its physical offsets.
    fn representation_compatible(&self, other: &Self) -> bool {
        if self.layout != other.layout {
            return false;
        }
        match (&self.members, &other.members) {
            (None, None) => self.leaves == other.leaves,
            (Some(left), Some(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|((left_offset, left), (right_offset, right))| {
                            left_offset == right_offset && left.representation_compatible(right)
                        })
            }
            _ => false,
        }
    }

    fn contains(&self, offset: usize, ty: Type) -> bool {
        (offset == 0 && ty == self.ty)
            || self.members.as_ref().is_some_and(|members| {
                members.iter().any(|(base, member)| {
                    offset
                        .checked_sub(*base)
                        .is_some_and(|offset| member.contains(offset, ty))
                })
            })
    }

    fn import(
        &self,
        value: &Value,
        leaves: &mut SVec2<Option<Scalar>>,
    ) -> Result<(), RuntimeError> {
        if let Some(members) = &self.members {
            let fields = value
                .as_tuple()
                .ok_or_else(|| invalid("expected a product host value"))?;
            if fields.len() != members.len() {
                return Err(invalid("host product arity mismatch"));
            }
            for ((_, member), field) in members.iter().zip(fields.iter()) {
                member.import(field, leaves)?;
            }
        } else {
            let scalar = Scalar::from_value(value)?;
            if scalar.kind() != self.leaves[0].1 {
                return Err(invalid("host scalar type mismatch"));
            }
            leaves.push(Some(scalar));
        }
        Ok(())
    }

    fn export(&self, leaves: &mut impl Iterator<Item = Option<Scalar>>) -> Value {
        if let Some(members) = &self.members {
            Value::tuple(
                members
                    .iter()
                    .map(|(_, member)| member.export(leaves))
                    .collect::<Vec<_>>(),
            )
        } else {
            leaves
                .next()
                .flatten()
                .expect("export checked initialization")
                .boxed()
        }
    }
}

struct Allocation {
    pointer: NonNull<u8>,
    layout: Layout,
    shape: Rc<StorageLayout>,
    initialized: SVec2<bool>,
    generation: u64,
}

impl Drop for Allocation {
    fn drop(&mut self) {
        // SAFETY: this owner holds the allocation returned by alloc with exactly this layout.
        // All admitted leaves are trivially destructible, including on poisoning exits.
        unsafe { dealloc(self.pointer.as_ptr(), self.layout) };
    }
}

pub(super) struct Memory {
    allocations: Vec<Allocation>,
    layouts: FxHashMap<Type, Rc<StorageLayout>>,
    generation: u64,
}

impl Default for Memory {
    fn default() -> Self {
        let mut layouts = FxHashMap::default();
        for kind in [
            ScalarKind::Unit,
            ScalarKind::Bool,
            ScalarKind::Int,
            ScalarKind::Float,
        ] {
            layouts.insert(kind.ty(), Rc::new(StorageLayout::scalar(kind.ty(), kind)));
        }
        layouts.insert(
            Type::never(),
            Rc::new(StorageLayout::scalar(Type::never(), ScalarKind::Unit)),
        );
        Self {
            allocations: Vec::new(),
            layouts,
            generation: 0,
        }
    }
}

impl Memory {
    /// Use exactly the layout recipes used by physical lowering, including named products and
    /// compact records. Reject recursive/non-product representations before allocating anything.
    pub(super) fn prepare_type(
        &mut self,
        ty: Type,
        env: &impl TypeLayoutEnv,
    ) -> Result<(), RuntimeError> {
        self.prepare_inner(ty, env, &mut Vec::new())
    }

    fn prepare_inner(
        &mut self,
        ty: Type,
        env: &impl TypeLayoutEnv,
        active: &mut Vec<Type>,
    ) -> Result<(), RuntimeError> {
        if self.layouts.contains_key(&ty) {
            return Ok(());
        }
        if let Ok(kind) = ScalarKind::for_type(ty) {
            self.layouts
                .insert(ty, Rc::new(StorageLayout::scalar(ty, kind)));
            return Ok(());
        }
        if active.contains(&ty) {
            return Err(unsupported("recursive storage"));
        }
        if active.len() >= MAX_STORAGE_DEPTH {
            return Err(unsupported("product storage nesting limit"));
        }
        // The layout recipe recursively visits member representations, so apply the expansion
        // bound first, using direct member types and already prepared child layouts.
        let member_types =
            product_member_types(ty, env).ok_or_else(|| unsupported("this storage type"))?;
        if member_types.len() > MAX_STORAGE_LEAVES {
            return Err(unsupported("product storage leaf limit"));
        }
        active.push(ty);
        let mut leaf_count = 0;
        for member in member_types {
            self.prepare_inner(member, env, active)?;
            let shape = self.shape(member)?;
            // A child may have been prepared by an earlier entry, so recursion-stack depth alone
            // does not bound the resulting representation tree.
            if shape.depth >= MAX_STORAGE_DEPTH {
                return Err(unsupported("product storage nesting limit"));
            }
            let count = shape.leaves.len();
            if count > MAX_STORAGE_LEAVES - leaf_count {
                return Err(unsupported("product storage leaf limit"));
            }
            leaf_count += count;
        }
        active.pop();
        let span = Location::new_synthesized();
        let spec =
            product_layout_spec(ty, span, env).ok_or_else(|| unsupported("this storage type"))?;
        let mut members = Vec::with_capacity(spec.members.len());
        for (index, member) in spec.members.iter().enumerate() {
            let offset = spec
                .static_field_offset(ProjectionIndex::from_index(index))
                .ok_or_else(|| unsupported("dynamic product layouts"))?;
            let shape = self.shape(member.ty)?;
            members.push((offset, shape));
        }
        let layout =
            value_layout_for_type(ty, span, env).map_err(|_| unsupported("this product layout"))?;
        let layout = Layout::from_size_align(layout.size as usize, layout.align as usize)
            .map_err(|_| invalid("invalid product layout"))?;
        self.layouts
            .insert(ty, Rc::new(StorageLayout::product(ty, layout, members)?));
        Ok(())
    }

    fn shape(&self, ty: Type) -> Result<Rc<StorageLayout>, RuntimeError> {
        self.layouts
            .get(&ty)
            .cloned()
            .ok_or_else(|| unsupported("unprepared storage type"))
    }

    pub(super) fn len(&self) -> usize {
        self.allocations.len()
    }
    pub(super) fn restore(&mut self, marker: usize) {
        self.allocations.truncate(marker);
    }

    pub(super) fn allocate(&mut self, ty: Type) -> Result<Address, RuntimeError> {
        let shape = self.shape(ty)?;
        self.generation = self
            .generation
            .checked_add(1)
            .ok_or_else(|| invalid("allocation identity exhausted"))?;
        // Even zero-sized values receive a unique, live, aligned allocation.
        let layout =
            Layout::from_size_align(shape.layout.size().max(1), shape.layout.align()).unwrap();
        // SAFETY: layout is nonzero and valid; null is handled without dereferencing it.
        let pointer = NonNull::new(unsafe { alloc(layout) })
            .ok_or_else(|| invalid("physical allocation failed"))?;
        let address = Address {
            allocation: self.len(),
            generation: self.generation,
            offset: 0,
            ty,
        };
        self.allocations.push(Allocation {
            pointer,
            layout,
            initialized: smallvec::smallvec![false; shape.leaves.len()],
            shape,
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
        let shape = self.shape(address.ty)?;
        if address
            .offset
            .checked_add(shape.layout.size())
            .is_none_or(|end| end > allocation.shape.layout.size())
        {
            return Err(invalid("address outside allocation bounds"));
        }
        if allocation.layout.align() < shape.layout.align()
            || !address.offset.is_multiple_of(shape.layout.align())
        {
            return Err(invalid("misaligned address"));
        }
        if !allocation.shape.contains(address.offset, address.ty) {
            return Err(invalid("incompatible storage view"));
        }
        Ok(allocation)
    }

    pub(super) fn offset(
        &self,
        base: Address,
        offset: usize,
        ty: Type,
    ) -> Result<Address, RuntimeError> {
        self.allocation(base)?;
        if !self.shape(base.ty)?.contains(offset, ty) {
            return Err(invalid("offset does not select a typed subobject"));
        }
        let address = Address {
            offset: base
                .offset
                .checked_add(offset)
                .ok_or_else(|| invalid("address overflow"))?,
            ty,
            ..base
        };
        self.allocation(address)?;
        Ok(address)
    }

    pub(super) fn size(&self, address: Address) -> Result<usize, RuntimeError> {
        self.allocation(address)?;
        Ok(self.shape(address.ty)?.layout.size())
    }

    pub(super) fn overlaps(&self, a: Address, b: Address) -> Result<bool, RuntimeError> {
        self.allocation(a)?;
        self.allocation(b)?;
        if a.allocation != b.allocation {
            return Ok(false);
        }
        let left = self.leaf_indices(a)?.into_iter().collect::<FxHashSet<_>>();
        Ok(self
            .leaf_indices(b)?
            .iter()
            .any(|index| left.contains(index)))
    }

    pub(super) fn pointer(&self, address: Address) -> Result<*mut u8, RuntimeError> {
        let allocation = self.allocation(address)?;
        // SAFETY: allocation() checked bounds, alignment, lifetime and the typed subobject.
        Ok(unsafe { allocation.pointer.as_ptr().add(address.offset) })
    }

    fn leaf_indices(&self, address: Address) -> Result<SVec2<usize>, RuntimeError> {
        let allocation = self.allocation(address)?;
        self.shape(address.ty)?
            .leaves
            .iter()
            .map(|(offset, kind)| {
                allocation
                    .shape
                    .leaves
                    .iter()
                    .position(|leaf| *leaf == (address.offset + offset, *kind))
                    .ok_or_else(|| invalid("missing initialization leaf"))
            })
            .collect()
    }

    pub(super) fn initialized(&self, address: Address) -> Result<bool, RuntimeError> {
        Ok(self
            .leaf_indices(address)?
            .iter()
            .all(|&i| self.allocations[address.allocation].initialized[i]))
    }

    pub(super) fn any_initialized(&self, address: Address) -> Result<bool, RuntimeError> {
        Ok(self
            .leaf_indices(address)?
            .iter()
            .any(|&i| self.allocations[address.allocation].initialized[i]))
    }

    pub(super) fn mark_initialized(&mut self, address: Address) -> Result<(), RuntimeError> {
        if self.any_initialized(address)? {
            return Err(invalid("overwriting initialized storage"));
        }
        for i in self.leaf_indices(address)? {
            self.allocations[address.allocation].initialized[i] = true;
        }
        Ok(())
    }

    pub(super) fn clear(&mut self, address: Address) -> Result<(), RuntimeError> {
        for i in self.leaf_indices(address)? {
            self.allocations[address.allocation].initialized[i] = false;
        }
        Ok(())
    }

    pub(super) fn read(&self, address: Address) -> Result<Scalar, RuntimeError> {
        let kind = ScalarKind::for_type(address.ty)?;
        if !self.initialized(address)? {
            return Err(invalid("read of uninitialized storage"));
        }
        let pointer = self.pointer(address)?;
        // SAFETY: checked live storage, exact scalar type, alignment, and initialized typed writes.
        Ok(unsafe { Self::read_scalar(pointer, kind) })
    }

    unsafe fn read_scalar(pointer: *mut u8, kind: ScalarKind) -> Scalar {
        // SAFETY: caller establishes the scalar type, initialization and alignment.
        unsafe {
            match kind {
                ScalarKind::Unit => Scalar::Unit,
                ScalarKind::Bool => Scalar::Bool(pointer.cast::<bool>().read()),
                ScalarKind::Int => Scalar::Int(pointer.cast::<isize>().read()),
                ScalarKind::Float => Scalar::Float(pointer.cast::<Float>().read()),
            }
        }
    }

    pub(super) fn read_value(
        &self,
        address: Address,
        allow_absent: bool,
    ) -> Result<StoredValue, RuntimeError> {
        let shape = self.shape(address.ty)?;
        let pointer = self.pointer(address)?;
        let indices = self.leaf_indices(address)?;
        let mut leaves = SVec2::with_capacity(indices.len());
        for ((offset, kind), index) in shape.leaves.iter().zip(indices) {
            let initialized = self.allocations[address.allocation].initialized[index];
            if !initialized && !allow_absent {
                return Err(invalid("read of uninitialized storage"));
            }
            // SAFETY: every leaf is within the validated subobject, with canonical alignment and
            // type. Absent leaves and padding are never read.
            leaves.push(if initialized {
                Some(unsafe { Self::read_scalar(pointer.add(*offset), *kind) })
            } else {
                None
            });
        }
        Ok(StoredValue {
            ty: address.ty,
            leaves,
        })
    }

    pub(super) fn write(&mut self, address: Address, value: Scalar) -> Result<(), RuntimeError> {
        self.write_value(
            address,
            &StoredValue {
                ty: value.kind().ty(),
                leaves: smallvec::smallvec![Some(value)],
            },
        )
    }

    pub(super) fn write_value(
        &mut self,
        address: Address,
        value: &StoredValue,
    ) -> Result<(), RuntimeError> {
        let shape = self.shape(address.ty)?;
        let source = self.shape(value.ty)?;
        // Stores bridge named products and their structural shapes, but cannot regroup fields.
        if !shape.representation_compatible(&source) || value.leaves.len() != shape.leaves.len() {
            return Err(invalid("store representation mismatch"));
        }
        let pointer = self.pointer(address)?;
        let indices = self.leaf_indices(address)?;
        for (((offset, kind), value), index) in shape.leaves.iter().zip(&value.leaves).zip(indices)
        {
            if let Some(value) = value {
                if value.kind() != *kind {
                    return Err(invalid("scalar store type mismatch"));
                }
                // SAFETY: canonical leaf layout and destination lifetime/bounds checked above;
                // only a matching typed scalar is written, never invalid bytes or padding.
                unsafe {
                    let pointer = pointer.add(*offset);
                    match value {
                        Scalar::Unit => (),
                        Scalar::Bool(v) => pointer.cast::<bool>().write(*v),
                        Scalar::Int(v) => pointer.cast::<isize>().write(*v),
                        Scalar::Float(v) => pointer.cast::<Float>().write(*v),
                    }
                }
            }
            self.allocations[address.allocation].initialized[index] = value.is_some();
        }
        Ok(())
    }

    pub(super) fn import(&self, ty: Type, value: &Value) -> Result<StoredValue, RuntimeError> {
        let mut leaves = SVec2::new();
        self.shape(ty)?.import(value, &mut leaves)?;
        Ok(StoredValue { ty, leaves })
    }

    pub(super) fn export(&self, address: Address) -> Result<Value, RuntimeError> {
        let value = self.read_value(address, false)?;
        Ok(self
            .shape(address.ty)?
            .export(&mut value.leaves.into_iter()))
    }

    pub(super) fn literal(
        &self,
        ty: Type,
        literal: &LiteralValue,
    ) -> Result<StoredValue, RuntimeError> {
        fn visit(
            shape: &StorageLayout,
            literal: &LiteralValue,
            leaves: &mut SVec2<Option<Scalar>>,
        ) -> Result<(), RuntimeError> {
            if let Some(members) = &shape.members {
                let LiteralValue::Tuple(fields) = literal else {
                    return Err(invalid("expected a product literal"));
                };
                if fields.len() != members.len() {
                    return Err(invalid("literal product arity mismatch"));
                }
                for ((_, member), field) in members.iter().zip(fields.iter()) {
                    visit(member, field, leaves)?;
                }
            } else {
                let scalar = Scalar::from_literal(literal)?;
                if scalar.kind() != shape.leaves[0].1 {
                    return Err(invalid("literal scalar type mismatch"));
                }
                leaves.push(Some(scalar));
            }
            Ok(())
        }
        let mut leaves = SVec2::new();
        visit(self.shape(ty)?.as_ref(), literal, &mut leaves)?;
        Ok(StoredValue { ty, leaves })
    }

    pub(super) fn matches(
        &self,
        address: Address,
        literal: &LiteralValue,
    ) -> Result<bool, RuntimeError> {
        Ok(self.read_value(address, false)?.leaves == self.literal(address.ty, literal)?.leaves)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn physical_product_layout_validation() {
        let int = Rc::new(StorageLayout::scalar(ScalarKind::Int.ty(), ScalarKind::Int));
        let boolean = Rc::new(StorageLayout::scalar(
            ScalarKind::Bool.ty(),
            ScalarKind::Bool,
        ));
        let size = int.layout.size();
        let layout = Layout::from_size_align(2 * size, int.layout.align()).unwrap();
        let ty = Type::tuple(vec![int.ty; 2]);
        assert!(
            StorageLayout::product(ty, layout, vec![(0, int.clone()), (size, int.clone())]).is_ok()
        );
        for members in [
            vec![(2 * size, int.clone())],        // Member outside allocation.
            vec![(1, int.clone())],               // Misaligned member.
            vec![(usize::MAX, int.clone())],      // Extent overflow.
            vec![(0, boolean), (0, int.clone())], // Different typed leaves still overlap in bytes.
        ] {
            assert!(StorageLayout::product(ty, layout, members).is_err());
        }
        assert!(
            StorageLayout::product(
                ty,
                Layout::from_size_align(2 * size, 1).unwrap(),
                vec![(0, int)]
            )
            .is_err()
        );
        // A child extent can be valid while its own flattened leaf metadata is inconsistent.
        for offset in [1, 2 * size] {
            let malformed = Rc::new(StorageLayout {
                ty,
                layout,
                depth: 1,
                members: Some(vec![]),
                leaves: vec![(offset, ScalarKind::Int)],
            });
            assert!(StorageLayout::product(ty, layout, vec![(0, malformed)]).is_err());
        }
    }

    #[test]
    fn physical_product_preparation_bounds_expansion() {
        let module = crate::module::Module::new(
            crate::module::ModuleId::from_index(0),
            crate::module::path::Path::single_str("memory_test"),
        );
        let modules = Default::default();
        let env = crate::module::ModuleEnv::new(&module, &modules);
        let int = ScalarKind::Int.ty();
        // A compact type DAG denotes over a million scalar leaves. Reject it before asking
        // the recursive layout recipe to expand that tree, not after allocating the leaf vector.
        let huge = (0..20).fold(int, |ty, _| Type::tuple(vec![ty, ty]));
        let mut memory = Memory::default();
        let error = memory.prepare_type(huge, &env).unwrap_err();
        assert!(matches!(error, RuntimeError::Backend(message) if message.contains("leaf limit")));
        assert!(!memory.layouts.contains_key(&huge));
        assert!(
            memory
                .layouts
                .values()
                .all(|shape| shape.leaves.len() <= MAX_STORAGE_LEAVES)
        );
        assert!(
            memory
                .layouts
                .values()
                .any(|shape| shape.leaves.len() == MAX_STORAGE_LEAVES)
        );
        assert_eq!(memory.len(), 0);

        // Cached children must not allow successively prepared wrappers to evade the depth bound.
        let mut nested = int;
        for _ in 0..MAX_STORAGE_DEPTH {
            nested = Type::tuple(vec![nested]);
            memory.prepare_type(nested, &env).unwrap();
        }
        nested = Type::tuple(vec![nested]);
        for mut memory in [memory, Memory::default()] {
            let error = memory.prepare_type(nested, &env).unwrap_err();
            assert!(
                matches!(error, RuntimeError::Backend(message) if message.contains("nesting limit"))
            );
        }
    }

    #[test]
    fn physical_product_compatibility_and_zero_sized_overlap() {
        let module = crate::module::Module::new(
            crate::module::ModuleId::from_index(0),
            crate::module::path::Path::single_str("memory_test"),
        );
        let modules = Default::default();
        let env = crate::module::ModuleEnv::new(&module, &modules);
        let int = ScalarKind::Int.ty();
        let pair = Type::tuple(vec![int, int]);
        let left = Type::tuple(vec![pair, int]);
        let right = Type::tuple(vec![int, pair]);
        let mixed = Type::tuple(vec![int, Type::unit(), int]);
        let mut memory = Memory::default();
        for ty in [left, right, mixed] {
            memory.prepare_type(ty, &env).unwrap();
        }
        assert_eq!(
            memory.shape(left).unwrap().leaves,
            memory.shape(right).unwrap().leaves
        );
        let literal = LiteralValue::new_tuple(vec![
            LiteralValue::new_tuple(vec![
                LiteralValue::new_native(1isize),
                LiteralValue::new_native(2isize),
            ]),
            LiteralValue::new_native(3isize),
        ]);
        let value = memory.literal(left, &literal).unwrap();
        let destination = memory.allocate(right).unwrap();
        assert!(memory.write_value(destination, &value).is_err());
        assert!(!memory.any_initialized(destination).unwrap());
        let source = memory.allocate(left).unwrap();
        memory.write_value(source, &value).unwrap();

        let product = memory.allocate(mixed).unwrap();
        let offset = size_of::<isize>();
        let unit = memory.offset(product, offset, Type::unit()).unwrap();
        let sized = memory.offset(product, offset, int).unwrap();
        assert_eq!(
            memory.pointer(unit).unwrap(),
            memory.pointer(sized).unwrap()
        );
        assert!(!memory.overlaps(unit, sized).unwrap());
        assert!(!memory.overlaps(sized, unit).unwrap());
        assert!(memory.overlaps(product, unit).unwrap());
        assert!(memory.overlaps(unit, unit).unwrap());
        memory.write(unit, Scalar::Unit).unwrap();
        memory.write(sized, Scalar::Int(42)).unwrap();
        memory.clear(unit).unwrap();
        assert_eq!(memory.read(sized).unwrap(), Scalar::Int(42));
    }

    #[test]
    fn physical_product_memory_checks_subobjects_and_partial_initialization() {
        let module = crate::module::Module::new(
            crate::module::ModuleId::from_index(0),
            crate::module::path::Path::single("memory_test".into()),
        );
        let modules = Default::default();
        let env = crate::module::ModuleEnv::new(&module, &modules);
        let ty = Type::record(vec![
            ("a".into(), ScalarKind::Bool.ty()),
            ("b".into(), ScalarKind::Int.ty()),
        ]);
        let spec = product_layout_spec(ty, Location::new_synthesized(), &env).unwrap();
        let mut memory = Memory::default();
        memory.prepare_type(ty, &env).unwrap();
        let whole = memory.allocate(ty).unwrap();
        let fields = [ScalarKind::Bool, ScalarKind::Int].map(|kind| {
            let index = usize::from(kind == ScalarKind::Int);
            memory
                .offset(
                    whole,
                    spec.static_field_offset(ProjectionIndex::from_index(index))
                        .unwrap(),
                    kind.ty(),
                )
                .unwrap()
        });
        assert!(
            fields[1].offset < fields[0].offset,
            "records use physical alignment order"
        );
        memory.write(fields[0], Scalar::Bool(true)).unwrap();
        assert!(memory.any_initialized(whole).unwrap());
        assert!(!memory.initialized(whole).unwrap());
        assert!(memory.read_value(whole, false).is_err());
        let partial = memory.read_value(whole, true).unwrap();
        let copy = memory.allocate(ty).unwrap();
        memory.write_value(copy, &partial).unwrap();
        assert_eq!(memory.read_value(copy, true).unwrap(), partial);
        memory.write(fields[1], Scalar::Int(42)).unwrap();
        assert!(memory.initialized(whole).unwrap());
        let exported = memory.export(whole).unwrap();
        let imported = memory.import(ty, &exported).unwrap();
        assert_eq!(memory.read_value(whole, false).unwrap(), imported);
        exported.discard_storage();
        assert!(memory.overlaps(whole, fields[0]).unwrap());
        assert!(!memory.overlaps(fields[0], fields[1]).unwrap());
        assert!(
            memory
                .offset(fields[1], fields[0].offset, ScalarKind::Bool.ty())
                .is_err(),
            "a field cannot project into a sibling"
        );
        assert!(memory.offset(whole, 1, ScalarKind::Int.ty()).is_err());
        memory.clear(whole).unwrap();
        assert!(!memory.any_initialized(whole).unwrap());
        memory.restore(0);
        assert!(memory.read(fields[0]).is_err());
        assert_eq!(memory.len(), 0);
        assert!(
            memory
                .prepare_type(Type::tuple(vec![Type::unit(); 2]), &env)
                .is_err(),
            "co-located zero-sized products need independent ownership identities"
        );
        assert!(
            memory
                .prepare_type(
                    Type::tuple(vec![Type::unit(), Type::unit(), ScalarKind::Int.ty()]),
                    &env
                )
                .is_err(),
            "co-located unit fields also need separate presence flags"
        );
    }

    #[test]
    fn physical_memory_checks_initialization_bounds_and_lifetimes() {
        let mut memory = Memory::default();
        let address = memory.allocate(ScalarKind::Int.ty()).unwrap();
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
                    ty: ScalarKind::Bool.ty(),
                    ..address
                })
                .is_err()
        );
        memory.clear(address).unwrap();
        assert!(memory.read(address).is_err());
        memory.restore(0);
        assert!(memory.pointer(address).is_err());
        let replacement = memory.allocate(ScalarKind::Int.ty()).unwrap();
        assert_ne!(address, replacement);
        assert!(memory.pointer(address).is_err());
        let unit = memory.allocate(ScalarKind::Unit.ty()).unwrap();
        assert!(!memory.initialized(unit).unwrap());
        memory.write(unit, Scalar::Unit).unwrap();
        assert_eq!(memory.read(unit).unwrap(), Scalar::Unit);
        memory.restore(0);
        assert_eq!(memory.len(), 0);
    }
}
