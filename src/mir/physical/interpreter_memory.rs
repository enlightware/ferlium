// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! ABI-layout storage with checked provenance, logical subobjects and initialization.

use super::{Evidence, invalid, unsupported};
use crate::{
    Location,
    compiler::error::SandboxViolationKind,
    eval::RuntimeError,
    hir::{
        native_functions::NativeLayout,
        value::{LiteralValue, Value, VariantPayloadStorage},
    },
    mir::physical::dictionary::{DictionaryReference, EvidenceEnvironmentLayout},
    module::{ProjectionIndex, id::Id},
    std::{
        math::Float,
        value::{
            TypeLayoutEnv, product_layout_spec, product_member_types, structural_variant,
            value_layout_for_type, variant_payload_offset, variant_payload_storage_for_type,
        },
    },
    types::r#type::Type,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    alloc::{Layout, alloc, dealloc},
    mem::{offset_of, size_of, take},
    ptr::{NonNull, from_mut},
    rc::Rc,
};
use ustr::Ustr;

// Capability bounds, not an invocation-wide memory quota. Check before layout computation and
// flattening, which otherwise expand a compact type DAG into an arbitrarily large tree.
const MAX_STORAGE_LEAVES: usize = 4096;
const MAX_STORAGE_DEPTH: usize = 64;
const MAX_STORAGE_NODES: usize = 16384;

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
            Self::Bool(value) => from_mut(value).cast(),
            Self::Int(value) => from_mut(value).cast(),
            Self::Float(value) => from_mut(value).cast(),
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

/// Snapshots contain typed data and pointer provenance, never padding or boxed guest values.
/// An indirect payload is transferred by its pointer, not recursively copied.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct StoredValue {
    pub(super) ty: Type,
    data: StoredData,
}

#[derive(Clone, Debug, PartialEq)]
enum StoredData {
    Scalar(Option<Scalar>),
    Product(Vec<StoredValue>),
    Empty(bool),
    Variant(Option<(Ustr, Box<StoredValue>)>),
    Pointer(Option<Address>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct Address {
    allocation: usize,
    generation: u64,
    node: usize,
    version: u64,
    offset: usize,
    pub(super) ty: Type,
}

struct VariantCase {
    tag: Ustr,
    payload: Type,
    storage: VariantPayloadStorage,
    // Indirect edges retain only a type, so recursive layouts never form Rc cycles.
    inline: Option<Rc<StorageLayout>>,
}

struct StorageLayout {
    ty: Type,
    layout: Layout,
    depth: usize,
    nodes: usize,
    members: Option<Vec<(usize, Rc<StorageLayout>)>>,
    cases: Option<Vec<VariantCase>>,
    pointer: bool,
    // Static scalar extents, used to validate the ABI layout before any unsafe access.
    leaves: Vec<(usize, ScalarKind)>,
}

fn check_extent(parent: Layout, offset: usize, child: Layout) -> Result<(), RuntimeError> {
    if offset
        .checked_add(child.size())
        .is_none_or(|end| end > parent.size())
    {
        return Err(invalid("subobject outside layout bounds"));
    }
    if parent.align() < child.align() || !offset.is_multiple_of(child.align()) {
        return Err(invalid("misaligned subobject"));
    }
    Ok(())
}

impl StorageLayout {
    fn scalar(ty: Type, kind: ScalarKind) -> Self {
        Self {
            ty,
            layout: kind.layout(),
            depth: 0,
            nodes: 1,
            members: None,
            cases: None,
            pointer: false,
            leaves: vec![(0, kind)],
        }
    }

    fn pointer(ty: Type) -> Self {
        Self {
            ty,
            layout: Layout::new::<*mut u8>(),
            depth: 0,
            nodes: 1,
            members: None,
            cases: None,
            pointer: true,
            leaves: vec![],
        }
    }

    fn product(
        ty: Type,
        layout: Layout,
        members: Vec<(usize, Rc<StorageLayout>)>,
    ) -> Result<Self, RuntimeError> {
        let depth = 1 + members.iter().map(|(_, m)| m.depth).max().unwrap_or(0);
        if depth > MAX_STORAGE_DEPTH {
            return Err(unsupported("product storage nesting limit"));
        }
        let nodes = 1 + members.iter().map(|(_, m)| m.nodes).sum::<usize>();
        if nodes > MAX_STORAGE_NODES {
            return Err(unsupported("storage subobject limit"));
        }
        let mut leaves = Vec::new();
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
            nodes,
            members: Some(members),
            cases: None,
            pointer: false,
            leaves,
        })
    }

    fn representation_compatible(&self, other: &Self) -> bool {
        if self.layout != other.layout || self.pointer != other.pointer {
            return false;
        }
        match (&self.members, &other.members, &self.cases, &other.cases) {
            (Some(left), Some(right), _, _) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|((a, l), (b, r))| a == b && l.representation_compatible(r))
            }
            (None, None, Some(left), Some(right)) => {
                left.len() == right.len()
                    && left.iter().zip(right).all(|(l, r)| {
                        l.tag == r.tag && l.payload == r.payload && l.storage == r.storage
                    })
            }
            (None, None, None, None) => self.leaves == other.leaves,
            _ => false,
        }
    }
}

/// Local initialization and the metadata needed to interpret initialized bytes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum StorageState {
    /// Scalars and empty products need an independent presence flag.
    Value(bool),
    /// Nonempty products derive initialization from their children.
    Product,
    /// An initialized variant shell records its active case.
    Variant(Option<Ustr>),
    /// An initialized pointer slot records its checked provenance.
    Pointer(Option<Address>),
}

impl StorageState {
    fn absent(shape: &StorageLayout) -> Self {
        if shape.pointer {
            Self::Pointer(None)
        } else if shape.cases.is_some() {
            Self::Variant(None)
        } else if shape.members.as_ref().is_some_and(|m| !m.is_empty()) {
            Self::Product
        } else {
            Self::Value(false)
        }
    }

    fn locally_present(self) -> bool {
        match self {
            Self::Value(present) => present,
            Self::Product => false,
            Self::Variant(tag) => tag.is_some(),
            Self::Pointer(pointer) => pointer.is_some(),
        }
    }
}

/// Presence and subobject identity are separate from bytes. Each active product field has its own
/// node, even when its extent is empty. Replacing a variant case retires its old payload nodes.
struct StorageNode {
    /// Type and ABI layout of this subobject.
    shape: Rc<StorageLayout>,
    /// Byte offset from the allocation base.
    offset: usize,
    /// Identity stamp preventing reused node slots from reviving old addresses.
    version: u64,
    /// Whether this subobject identity is active rather than retired.
    live: bool,
    /// Kind-specific initialization; nonempty products use their children.
    state: StorageState,
    /// Direct field or active payload/pointer-slot indices in `Allocation::nodes`.
    children: Vec<usize>,
}

/// An owned byte allocation and its logical subobject bookkeeping.
struct Allocation {
    /// Base address of the owned host allocation.
    pointer: NonNull<u8>,
    /// Actual allocation layout, including the minimum byte for zero-sized values.
    layout: Layout,
    /// Logical subobjects, with the allocation root at index zero.
    nodes: Vec<StorageNode>,
    /// Retired node indices available for reuse.
    free_nodes: Vec<usize>,
    /// Monotonic counter assigning fresh identities to subobject nodes.
    version: u64,
    /// Allocation identity stamp preventing stale addresses after allocation-slot reuse.
    generation: u64,
    /// Whether lifetime follows `runtime_dealloc` rather than stack restoration.
    heap: bool,
}

impl Allocation {
    fn add_node(&mut self, shape: Rc<StorageLayout>, offset: usize) -> Result<usize, RuntimeError> {
        check_extent(self.layout, offset, shape.layout)?;
        self.version = self
            .version
            .checked_add(1)
            .ok_or_else(|| invalid("subobject identity exhausted"))?;
        let node = StorageNode {
            shape: shape.clone(),
            offset,
            version: self.version,
            live: true,
            state: StorageState::absent(&shape),
            children: vec![],
        };
        let id = if let Some(id) = self.free_nodes.pop() {
            self.nodes[id] = node;
            id
        } else {
            if self.nodes.len() >= MAX_STORAGE_NODES {
                return Err(unsupported("storage subobject limit"));
            }
            self.nodes.push(node);
            self.nodes.len() - 1
        };
        if let Some(members) = &shape.members {
            for (inner, member) in members {
                let child = self.add_node(member.clone(), offset + inner)?;
                self.nodes[id].children.push(child);
            }
        }
        Ok(id)
    }

    fn retire_children(&mut self, id: usize) {
        for child in take(&mut self.nodes[id].children) {
            self.retire_children(child);
            self.nodes[child].live = false;
            self.free_nodes.push(child);
        }
    }
}

impl Drop for Allocation {
    fn drop(&mut self) {
        // SAFETY: this owner holds exactly the allocation returned by alloc. Guest destruction is
        // explicit MIR; scalar/tag/pointer representations have no Rust destructor.
        unsafe { dealloc(self.pointer.as_ptr(), self.layout) };
    }
}

/// ABI bytes own the count and captures; types and generations only validate their interpretation.
struct EvidenceAllocation {
    /// Pointer-aligned ABI bytes, including the reference-count header and capture fields.
    words: Box<[usize]>,
    /// Field extents and representations selected by shared physical lowering.
    layout: EvidenceEnvironmentLayout,
    /// Resolved descriptor expected by references to this environment.
    descriptor: u32,
    /// Identity stamp rejecting pointers to a previous allocation at the same address.
    generation: u64,
    /// Type and pointer-provenance checks for each stored capture, not executable evidence.
    captures: Box<[(Type, u64)]>,
}

impl EvidenceAllocation {
    fn read<T: Copy>(&self, offset: usize) -> T {
        assert!(
            offset
                .checked_add(size_of::<T>())
                .is_some_and(|end| end <= self.layout.allocation.size())
        );
        // SAFETY: all callers select initialized scalar fields from the checked ABI layout.
        // Unaligned access also supports byte-sized fields between dictionary references.
        unsafe {
            self.words
                .as_ptr()
                .cast::<u8>()
                .add(offset)
                .cast::<T>()
                .read_unaligned()
        }
    }

    fn write<T: Copy>(&mut self, offset: usize, value: T) {
        assert!(
            offset
                .checked_add(size_of::<T>())
                .is_some_and(|end| end <= self.layout.allocation.size())
        );
        // SAFETY: the extent is checked above and the exclusive borrow excludes concurrent access.
        unsafe {
            self.words
                .as_mut_ptr()
                .cast::<u8>()
                .add(offset)
                .cast::<T>()
                .write_unaligned(value)
        };
    }

    fn captures(&self) -> Vec<Evidence> {
        self.layout
            .fields
            .iter()
            .zip(&self.captures)
            .map(|(field, &(ty, generation))| {
                if field.is_storage_flag {
                    Evidence::Storage(self.read::<u8>(field.offset) != 0)
                } else {
                    Evidence::Physical {
                        reference: DictionaryReference {
                            descriptor: self.read(field.offset),
                            environment: self
                                .read(field.offset + offset_of!(DictionaryReference, environment)),
                        },
                        generation,
                        ty,
                    }
                }
            })
            .collect()
    }
}

/// Checked storage and ABI layout metadata for one interpreter invocation.
pub(super) struct Memory {
    /// Evidence environments keyed by their target-sized base address.
    evidence: FxHashMap<usize, EvidenceAllocation>,
    /// Dynamic evidence allocations charged to the shared cell budget.
    live_evidence: usize,
    /// Allocation slots; released entries are empty until reused.
    allocations: Vec<Option<Allocation>>,
    /// Released allocation-slot indices available for reuse.
    free_allocations: Vec<usize>,
    /// Stack allocation indices in creation order, defining stack-restore boundaries.
    stack: Vec<usize>,
    /// Prepared storage layouts indexed by concrete type.
    layouts: FxHashMap<Type, Rc<StorageLayout>>,
    /// Symbolic variant tags mapped to their ABI discriminant identities.
    tags: FxHashMap<Ustr, u32>,
    /// Monotonic counter assigning fresh allocation identities.
    generation: u64,
    /// Maximum live allocation count, not a byte-memory quota.
    pub(super) allocation_limit: usize,
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
            evidence: FxHashMap::default(),
            live_evidence: 0,
            allocations: vec![],
            free_allocations: vec![],
            stack: vec![],
            layouts,
            tags: FxHashMap::default(),
            generation: 0,
            allocation_limit: usize::MAX,
        }
    }
}

impl Memory {
    fn evidence_allocation(
        &self,
        value: &Evidence,
    ) -> Result<Option<&EvidenceAllocation>, RuntimeError> {
        let Evidence::Physical {
            reference,
            generation,
            ..
        } = value
        else {
            return Err(invalid("expected physical dictionary"));
        };
        if reference.environment == 0 {
            return Ok(None);
        }
        let allocation = self
            .evidence
            .get(&reference.environment)
            .filter(|a| a.generation == *generation && a.descriptor == reference.descriptor)
            .ok_or_else(|| invalid("stale evidence environment"))?;
        Ok(Some(allocation))
    }

    pub(super) fn evidence_captures(
        &self,
        value: &Evidence,
    ) -> Result<Vec<Evidence>, RuntimeError> {
        Ok(self
            .evidence_allocation(value)?
            .map_or_else(Vec::new, |a| a.captures()))
    }

    fn evidence_allocation_mut(
        &mut self,
        reference: DictionaryReference,
        generation: u64,
    ) -> Result<&mut EvidenceAllocation, RuntimeError> {
        self.evidence
            .get_mut(&reference.environment)
            .filter(|a| a.generation == generation && a.descriptor == reference.descriptor)
            .ok_or_else(|| invalid("stale evidence environment"))
    }

    pub(super) fn allocate_evidence(
        &mut self,
        descriptor: u32,
        ty: Type,
        layout: &EvidenceEnvironmentLayout,
        captures: &[Evidence],
        is_static: bool,
        span: Option<Location>,
    ) -> Result<Evidence, RuntimeError> {
        if layout.fields.len() != captures.len() {
            return Err(invalid("evidence environment capture count mismatch"));
        }
        for (field, capture) in layout.fields.iter().zip(captures) {
            match (field.is_storage_flag, capture) {
                (true, Evidence::Storage(_)) => (),
                (false, Evidence::Physical { .. }) => {
                    if let Some(allocation) = self.evidence_allocation(capture)?
                        && is_static
                        && allocation.read::<usize>(0) != 0
                    {
                        return Err(invalid("static evidence captures dynamic evidence"));
                    }
                }
                _ => return Err(invalid("evidence capture representation mismatch")),
            }
        }
        if captures.is_empty() {
            return Ok(Evidence::Physical {
                reference: DictionaryReference {
                    descriptor,
                    environment: 0,
                },
                generation: 0,
                ty,
            });
        }
        if !is_static {
            self.check_allocation_limit(span)?;
        }
        self.generation = self
            .generation
            .checked_add(1)
            .ok_or_else(|| invalid("allocation identity exhausted"))?;
        let mut words = Vec::new();
        let count = layout.allocation.size().div_ceil(size_of::<usize>());
        words
            .try_reserve_exact(count)
            .map_err(|_| invalid("physical evidence allocation failed"))?;
        words.resize(count, 0);
        let mut allocation = EvidenceAllocation {
            words: words.into_boxed_slice(),
            layout: layout.clone(),
            descriptor,
            generation: self.generation,
            captures: captures
                .iter()
                .map(|e| {
                    (
                        e.ty(),
                        match e {
                            Evidence::Physical { generation, .. } => *generation,
                            _ => 0,
                        },
                    )
                })
                .collect(),
        };
        allocation.write(0, if is_static { 0usize } else { 1usize });
        for (index, (field, capture)) in layout.fields.iter().zip(captures).enumerate() {
            if !is_static {
                if let Err(error) = self.retain_evidence(capture) {
                    for retained in &captures[..index] {
                        self.release_evidence(retained)?;
                    }
                    return Err(error);
                }
            }
            match capture {
                Evidence::Storage(value) => allocation.write(field.offset, u8::from(*value)),
                Evidence::Physical { reference, .. } => {
                    allocation.write(field.offset, reference.descriptor);
                    allocation.write(
                        field.offset + offset_of!(DictionaryReference, environment),
                        reference.environment,
                    );
                }
                _ => unreachable!("capture representations checked above"),
            }
        }
        let environment = allocation.words.as_ptr() as usize;
        let generation = allocation.generation;
        self.evidence.insert(environment, allocation);
        self.live_evidence += usize::from(!is_static);
        Ok(Evidence::Physical {
            reference: DictionaryReference {
                descriptor,
                environment,
            },
            generation,
            ty,
        })
    }

    pub(super) fn retain_evidence(&mut self, value: &Evidence) -> Result<(), RuntimeError> {
        let Evidence::Physical {
            reference,
            generation,
            ..
        } = value
        else {
            return if matches!(value, Evidence::Storage(_)) {
                Ok(())
            } else {
                Err(invalid("symbolic evidence at execution"))
            };
        };
        if reference.environment == 0 {
            return Ok(());
        }
        let allocation = self.evidence_allocation_mut(*reference, *generation)?;
        if allocation.read::<usize>(0) != 0 {
            let count = allocation
                .read::<usize>(0)
                .checked_add(1)
                .ok_or_else(|| invalid("evidence reference count overflow"))?;
            allocation.write(0, count);
        }
        Ok(())
    }

    pub(super) fn release_evidence(&mut self, value: &Evidence) -> Result<(), RuntimeError> {
        let mut pending = vec![value.clone()];
        while let Some(value) = pending.pop() {
            let Evidence::Physical {
                reference,
                generation,
                ..
            } = value
            else {
                continue;
            };
            if reference.environment == 0 {
                continue;
            }
            let allocation = self.evidence_allocation_mut(reference, generation)?;
            if allocation.read::<usize>(0) == 0 {
                continue;
            }
            let count = allocation
                .read::<usize>(0)
                .checked_sub(1)
                .ok_or_else(|| invalid("evidence reference count underflow"))?;
            allocation.write(0, count);
            if count == 0 {
                pending.extend(allocation.captures());
                self.evidence.remove(&reference.environment);
                self.live_evidence -= 1;
            }
        }
        Ok(())
    }

    pub(super) fn prepare_type(
        &mut self,
        ty: Type,
        env: &impl TypeLayoutEnv,
    ) -> Result<(), RuntimeError> {
        let mut pending = vec![ty];
        let mut visited = FxHashSet::default();
        while let Some(ty) = pending.pop() {
            if visited.insert(ty) {
                self.prepare_inner(ty, env, &mut Vec::new(), &mut pending)?;
            }
        }
        Ok(())
    }

    fn prepare_inner(
        &mut self,
        ty: Type,
        env: &impl TypeLayoutEnv,
        active: &mut Vec<Type>,
        pending: &mut Vec<Type>,
    ) -> Result<(), RuntimeError> {
        if self.layouts.contains_key(&ty) {
            return Ok(());
        }
        if active.contains(&ty) {
            return Err(unsupported("recursive inline storage"));
        }
        if active.len() >= MAX_STORAGE_DEPTH {
            return Err(unsupported("product storage nesting limit"));
        }
        active.push(ty);
        let span = Location::new_synthesized();
        if let Some((_, cases)) = structural_variant(ty, env) {
            if cases.len() > MAX_STORAGE_LEAVES {
                return Err(unsupported("variant case limit"));
            }
            let mut prepared = Vec::new();
            let mut nodes = 1;
            let mut depth = 0;
            for (tag, payload) in cases {
                let storage = variant_payload_storage_for_type(ty, tag, span, env)
                    .map_err(|_| unsupported("variant storage classification"))?;
                let inline = if storage.is_indirect() {
                    pending.push(payload);
                    None
                } else {
                    self.prepare_inner(payload, env, active, pending)?;
                    Some(self.shape(payload)?)
                };
                nodes += inline.as_ref().map_or(1, |shape| shape.nodes);
                depth = depth.max(inline.as_ref().map_or(0, |shape| shape.depth + 1));
                if nodes > MAX_STORAGE_NODES || depth > MAX_STORAGE_DEPTH {
                    return Err(unsupported("variant storage expansion limit"));
                }
                let next_tag = self.tags.len() as u32;
                self.tags.entry(tag).or_insert(next_tag);
                prepared.push(VariantCase {
                    tag,
                    payload,
                    storage,
                    inline,
                });
            }
            let layout =
                value_layout_for_type(ty, span, env).map_err(|_| unsupported("variant layout"))?;
            let layout = Layout::from_size_align(layout.size as usize, layout.align as usize)
                .map_err(|_| invalid("invalid variant layout"))?;
            check_extent(layout, 0, Layout::new::<u32>())?;
            for case in &prepared {
                let child = case
                    .inline
                    .as_ref()
                    .map_or(Layout::new::<*mut u8>(), |s| s.layout);
                check_extent(
                    layout,
                    variant_payload_offset(child.align() as u32) as usize,
                    child,
                )?;
            }
            self.layouts.insert(
                ty,
                Rc::new(StorageLayout {
                    ty,
                    layout,
                    depth,
                    nodes,
                    members: None,
                    cases: Some(prepared),
                    pointer: false,
                    leaves: vec![],
                }),
            );
        } else {
            // Bound direct member expansion before the layout recipe recursively traverses it.
            let member_types =
                product_member_types(ty, env).ok_or_else(|| unsupported("this storage type"))?;
            if member_types.len() > MAX_STORAGE_LEAVES {
                return Err(unsupported("product storage leaf limit"));
            }
            let mut leaves = 0;
            let mut nodes = 1;
            for member in member_types {
                self.prepare_inner(member, env, active, pending)?;
                let shape = self.shape(member)?;
                if shape.depth >= MAX_STORAGE_DEPTH {
                    return Err(unsupported("product storage nesting limit"));
                }
                if shape.leaves.len() > MAX_STORAGE_LEAVES - leaves {
                    return Err(unsupported("product storage leaf limit"));
                }
                leaves += shape.leaves.len();
                nodes += shape.nodes;
                if nodes > MAX_STORAGE_NODES {
                    return Err(unsupported("storage subobject limit"));
                }
            }
            let spec = product_layout_spec(ty, span, env)
                .ok_or_else(|| unsupported("this storage type"))?;
            let mut members = Vec::new();
            for (index, member) in spec.members.iter().enumerate() {
                let offset = spec
                    .static_field_offset(ProjectionIndex::from_index(index))
                    .ok_or_else(|| unsupported("dynamic product layouts"))?;
                members.push((offset, self.shape(member.ty)?));
            }
            let layout = value_layout_for_type(ty, span, env)
                .map_err(|_| unsupported("this product layout"))?;
            let layout = Layout::from_size_align(layout.size as usize, layout.align as usize)
                .map_err(|_| invalid("invalid product layout"))?;
            self.layouts
                .insert(ty, Rc::new(StorageLayout::product(ty, layout, members)?));
        }
        active.pop();
        Ok(())
    }

    fn shape(&self, ty: Type) -> Result<Rc<StorageLayout>, RuntimeError> {
        self.layouts
            .get(&ty)
            .cloned()
            .ok_or_else(|| unsupported("unprepared storage type"))
    }

    pub(super) fn bind_tags(&mut self, mut intern: impl FnMut(Ustr) -> u32) {
        for (tag, id) in &mut self.tags {
            *id = intern(*tag);
        }
    }

    /// On non-poisoning exits every runtime allocation must still be owned by a host-boundary
    /// root, or have been explicitly released. At this boundary temporary borrowed pointer slots
    /// have been reclaimed: each remaining heap-pointer edge must be the payload's unique owner.
    pub(super) fn check_runtime_ownership(&self) -> Result<(), RuntimeError> {
        if self.live_evidence != 0 {
            return Err(invalid("evidence environment lost its owner"));
        }
        let mut pending = self
            .stack
            .iter()
            .map(|&id| self.address(id, 0))
            .collect::<Vec<_>>();
        let mut seen = FxHashSet::default();
        let mut owners = FxHashSet::default();
        while let Some(address) = pending.pop() {
            if !seen.insert(address) {
                continue;
            }
            let node = self.node(address)?;
            pending.extend(
                node.children
                    .iter()
                    .map(|&child| self.address(address.allocation, child)),
            );
            if let StorageState::Pointer(Some(pointer)) = node.state {
                if self.allocation(pointer)?.heap {
                    if pointer.node != 0 {
                        return Err(invalid("owning pointer is not an allocation base"));
                    }
                    if !owners.insert((pointer.allocation, pointer.generation)) {
                        return Err(invalid("runtime allocation has multiple owners"));
                    }
                }
                pending.push(pointer);
            }
        }
        for (id, allocation) in self.allocations.iter().enumerate() {
            if allocation.as_ref().is_some_and(|a| a.heap) && !seen.contains(&self.address(id, 0)) {
                return Err(invalid("runtime allocation lost its owner"));
            }
        }
        Ok(())
    }

    /// Stack markers count stack allocations only; runtime payloads survive their allocating frame.
    pub(super) fn len(&self) -> usize {
        self.stack.len()
    }
    fn live_allocations(&self) -> usize {
        self.allocations.len() - self.free_allocations.len() + self.live_evidence
    }
    fn check_allocation_limit(&self, span: Option<Location>) -> Result<(), RuntimeError> {
        if self.live_allocations() >= self.allocation_limit {
            return Err(RuntimeError::new_sandbox_violation(
                SandboxViolationKind::EnvironmentCellLimitExceeded {
                    limit: self.allocation_limit,
                },
                span,
            ));
        }
        Ok(())
    }
    pub(super) fn restore(&mut self, marker: usize) {
        while self.stack.len() > marker {
            let id = self.stack.pop().unwrap();
            self.release(id);
        }
    }
    fn release(&mut self, id: usize) {
        self.allocations[id] = None;
        self.free_allocations.push(id);
    }

    pub(super) fn allocate(
        &mut self,
        ty: Type,
        span: Option<Location>,
    ) -> Result<Address, RuntimeError> {
        self.allocate_shape(self.shape(ty)?, false, span)
    }
    pub(super) fn check_type_layout(
        &self,
        ty: Type,
        size: usize,
        align: usize,
    ) -> Result<(), RuntimeError> {
        let layout = self.shape(ty)?.layout;
        if layout.size() != size || layout.align() != align {
            return Err(invalid(
                "layout witness differs from checked storage layout",
            ));
        }
        Ok(())
    }
    pub(super) fn check_layout(
        &self,
        address: Address,
        size: usize,
        align: usize,
    ) -> Result<(), RuntimeError> {
        self.allocation(address)?;
        self.check_type_layout(address.ty, size, align)
    }
    pub(super) fn allocate_witnessed(
        &mut self,
        ty: Type,
        size: usize,
        align: usize,
        span: Option<Location>,
    ) -> Result<Address, RuntimeError> {
        self.check_type_layout(ty, size, align)?;
        self.allocate_shape(self.shape(ty)?, false, span)
    }
    pub(super) fn allocate_place(
        &mut self,
        ty: Type,
        span: Option<Location>,
    ) -> Result<Address, RuntimeError> {
        self.allocate_shape(Rc::new(StorageLayout::pointer(ty)), false, span)
    }
    pub(super) fn allocate_runtime(
        &mut self,
        ty: Type,
        size: usize,
        align: usize,
        span: Option<Location>,
    ) -> Result<Address, RuntimeError> {
        let shape = self.shape(ty)?;
        if shape.layout.size() != size || shape.layout.align() != align {
            return Err(invalid("runtime allocation differs from pointee layout"));
        }
        self.allocate_shape(shape, true, span)
    }
    fn allocate_shape(
        &mut self,
        shape: Rc<StorageLayout>,
        heap: bool,
        span: Option<Location>,
    ) -> Result<Address, RuntimeError> {
        self.check_allocation_limit(span)?;
        self.generation = self
            .generation
            .checked_add(1)
            .ok_or_else(|| invalid("allocation identity exhausted"))?;
        let layout =
            Layout::from_size_align(shape.layout.size().max(1), shape.layout.align()).unwrap();
        // SAFETY: layout is valid and nonzero; null is handled without dereferencing.
        let pointer = NonNull::new(unsafe { alloc(layout) })
            .ok_or_else(|| invalid("physical allocation failed"))?;
        let mut allocation = Allocation {
            pointer,
            layout,
            nodes: vec![],
            free_nodes: vec![],
            version: 0,
            generation: self.generation,
            heap,
        };
        allocation.add_node(shape, 0)?;
        let id = if let Some(id) = self.free_allocations.pop() {
            self.allocations[id] = Some(allocation);
            id
        } else {
            self.allocations.push(Some(allocation));
            self.allocations.len() - 1
        };
        if !heap {
            self.stack.push(id);
        }
        Ok(self.address(id, 0))
    }

    pub(super) fn deallocate(&mut self, address: Address) -> Result<(), RuntimeError> {
        let allocation = self.allocation(address)?;
        if !allocation.heap || address.node != 0 {
            return Err(invalid("release requires a runtime allocation base"));
        }
        // TrivialCopy leaves can remain initialized after no-op drop. Owning indirect payloads
        // must already have been released by explicit lifecycle MIR.
        self.ensure_no_owned_payloads(address)?;
        self.release(address.allocation);
        Ok(())
    }

    fn ensure_no_owned_payloads(&self, address: Address) -> Result<(), RuntimeError> {
        let node = self.node(address)?;
        if let StorageState::Pointer(Some(pointer)) = node.state {
            if self
                .allocation(pointer)
                .is_ok_and(|allocation| allocation.heap)
            {
                return Err(invalid("releasing storage with an owned payload"));
            }
        }
        for &child in &node.children {
            self.ensure_no_owned_payloads(self.address(address.allocation, child))?;
        }
        Ok(())
    }

    fn address(&self, allocation: usize, node: usize) -> Address {
        let owner = self.allocations[allocation].as_ref().unwrap();
        let view = &owner.nodes[node];
        Address {
            allocation,
            generation: owner.generation,
            node,
            version: view.version,
            offset: view.offset,
            ty: view.shape.ty,
        }
    }
    fn allocation(&self, address: Address) -> Result<&Allocation, RuntimeError> {
        let allocation = self
            .allocations
            .get(address.allocation)
            .and_then(Option::as_ref)
            .ok_or_else(|| invalid("address outlived its allocation"))?;
        if allocation.generation != address.generation {
            return Err(invalid("stale allocation address"));
        }
        let node = allocation
            .nodes
            .get(address.node)
            .ok_or_else(|| invalid("invalid subobject"))?;
        if !node.live || node.version != address.version {
            return Err(invalid("stale subobject address"));
        }
        if node.offset != address.offset || node.shape.ty != address.ty {
            return Err(invalid("typed subobject mismatch"));
        }
        check_extent(
            allocation.nodes[0].shape.layout,
            address.offset,
            node.shape.layout,
        )?;
        Ok(allocation)
    }
    fn node(&self, address: Address) -> Result<&StorageNode, RuntimeError> {
        Ok(&self.allocation(address)?.nodes[address.node])
    }
    fn node_mut(&mut self, address: Address) -> Result<&mut StorageNode, RuntimeError> {
        self.allocation(address)?;
        Ok(&mut self.allocations[address.allocation].as_mut().unwrap().nodes[address.node])
    }

    #[cfg(test)]
    fn offset(&self, base: Address, offset: usize, ty: Type) -> Result<Address, RuntimeError> {
        self.project(base, offset, ty, None)
    }
    pub(super) fn project(
        &self,
        base: Address,
        offset: usize,
        ty: Type,
        member: Option<ProjectionIndex>,
    ) -> Result<Address, RuntimeError> {
        let node = self.node(base)?;
        let target = base
            .offset
            .checked_add(offset)
            .ok_or_else(|| invalid("offset overflow"))?;
        if let Some(member) = member {
            if node.shape.members.is_none() {
                return Err(invalid("member projection of non-product"));
            }
            let child = *node
                .children
                .get(member.as_index())
                .ok_or_else(|| invalid("invalid product member"))?;
            let address = self.address(base.allocation, child);
            if address.offset != target || address.ty != ty {
                return Err(invalid("member projection layout mismatch"));
            }
            return Ok(address);
        }
        // A variant projection selects its active inline payload, never a stale/inactive case.
        if node.shape.cases.is_some() {
            let child = *node
                .children
                .first()
                .ok_or_else(|| invalid("projection of absent variant"))?;
            let address = self.address(base.allocation, child);
            if address.offset == target && address.ty == ty && !self.node(address)?.shape.pointer {
                return Ok(address);
            }
            return Err(invalid("invalid active payload projection"));
        }
        if offset == 0 && ty == base.ty {
            return Ok(base);
        }
        let mut candidates = Vec::new();
        self.find_subobjects(base, target, ty, &mut candidates)?;
        match candidates.as_slice() {
            [address] => Ok(*address),
            [] => Err(invalid("address is not a typed subobject")),
            _ => Err(invalid(
                "ambiguous subobject projection requires member identity",
            )),
        }
    }
    fn find_subobjects(
        &self,
        base: Address,
        offset: usize,
        ty: Type,
        found: &mut Vec<Address>,
    ) -> Result<(), RuntimeError> {
        for &child in &self.node(base)?.children {
            let address = self.address(base.allocation, child);
            if address.offset == offset && address.ty == ty {
                found.push(address);
            } else if self.node(address)?.shape.members.is_some() {
                self.find_subobjects(address, offset, ty, found)?;
            }
        }
        Ok(())
    }
    pub(super) fn pointer_slot(
        &self,
        base: Address,
        offset: usize,
    ) -> Result<Address, RuntimeError> {
        let node = self.node(base)?;
        if node.shape.cases.is_none() {
            return Err(invalid("pointer-slot projection of non-variant"));
        }
        let child = *node
            .children
            .first()
            .ok_or_else(|| invalid("absent variant shell"))?;
        let address = self.address(base.allocation, child);
        if !self.node(address)?.shape.pointer
            || base.offset.checked_add(offset) != Some(address.offset)
        {
            return Err(invalid("invalid indirect payload slot"));
        }
        // Release helpers deliberately use one erased pointee type for all indirect cases.
        Ok(address)
    }
    pub(super) fn size(&self, address: Address) -> Result<usize, RuntimeError> {
        Ok(self.node(address)?.shape.layout.size())
    }
    pub(super) fn is_pointer_slot(&self, address: Address) -> Result<bool, RuntimeError> {
        Ok(self.node(address)?.shape.pointer)
    }
    pub(super) fn overlaps(&self, a: Address, b: Address) -> Result<bool, RuntimeError> {
        self.allocation(a)?;
        self.allocation(b)?;
        if a.allocation != b.allocation {
            return Ok(false);
        }
        fn contains(owner: &Allocation, root: usize, node: usize) -> bool {
            root == node
                || owner.nodes[root]
                    .children
                    .iter()
                    .any(|&child| contains(owner, child, node))
        }
        let owner = self.allocation(a)?;
        Ok(contains(owner, a.node, b.node) || contains(owner, b.node, a.node))
    }
    pub(super) fn pointer(&self, address: Address) -> Result<*mut u8, RuntimeError> {
        let owner = self.allocation(address)?;
        // SAFETY: allocation() validates lifetime, logical identity, bounds and alignment.
        Ok(unsafe { owner.pointer.as_ptr().add(address.offset) })
    }

    pub(super) fn initialized(&self, address: Address) -> Result<bool, RuntimeError> {
        let node = self.node(address)?;
        // A variant shell is live independently of its payload. Lowered release helpers must be
        // able to inspect its tag and pointer slot after payload cleanup or failed construction.
        if node.state != StorageState::Product {
            return Ok(node.state.locally_present());
        }
        for &child in &node.children {
            if !self.initialized(self.address(address.allocation, child))? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    pub(super) fn any_initialized(&self, address: Address) -> Result<bool, RuntimeError> {
        let node = self.node(address)?;
        if node.state.locally_present() {
            return Ok(true);
        }
        for &child in &node.children {
            if self.any_initialized(self.address(address.allocation, child))? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    pub(super) fn mark_initialized(&mut self, address: Address) -> Result<(), RuntimeError> {
        if self.any_initialized(address)? {
            return Err(invalid("overwriting initialized storage"));
        }
        let node = self.node_mut(address)?;
        if !matches!(node.state, StorageState::Value(_)) || node.shape.members.is_some() {
            return Err(invalid("native initialization requires scalar storage"));
        }
        node.state = StorageState::Value(true);
        Ok(())
    }
    pub(super) fn clear(&mut self, address: Address) -> Result<(), RuntimeError> {
        let children = self.node(address)?.children.clone();
        for child in children {
            self.clear(self.address(address.allocation, child))?;
        }
        let node = self.node_mut(address)?;
        node.state = StorageState::absent(&node.shape);
        if node.shape.cases.is_some() {
            self.allocations[address.allocation]
                .as_mut()
                .unwrap()
                .retire_children(address.node);
        }
        Ok(())
    }

    pub(super) fn read(&self, address: Address) -> Result<Scalar, RuntimeError> {
        let kind = ScalarKind::for_type(address.ty)?;
        if self.node(address)?.shape.pointer || !self.initialized(address)? {
            return Err(invalid("read of uninitialized scalar storage"));
        }
        let pointer = self.pointer(address)?;
        // SAFETY: exact scalar type, checked bounds/alignment and initialized typed writes.
        Ok(unsafe { Self::read_scalar(pointer, kind) })
    }
    unsafe fn read_scalar(pointer: *mut u8, kind: ScalarKind) -> Scalar {
        // SAFETY: caller establishes type, alignment and initialization.
        unsafe {
            match kind {
                ScalarKind::Unit => Scalar::Unit,
                ScalarKind::Bool => Scalar::Bool(pointer.cast::<bool>().read()),
                ScalarKind::Int => Scalar::Int(pointer.cast::<isize>().read()),
                ScalarKind::Float => Scalar::Float(pointer.cast::<Float>().read()),
            }
        }
    }
    pub(super) fn read_pointer(&self, address: Address) -> Result<Address, RuntimeError> {
        let node = self.node(address)?;
        let StorageState::Pointer(pointer) = node.state else {
            return Err(invalid("expected pointer slot"));
        };
        let pointer = pointer.ok_or_else(|| invalid("read of absent pointer"))?;
        self.allocation(pointer)?;
        Ok(pointer)
    }
    pub(super) fn write_pointer(
        &mut self,
        address: Address,
        value: Address,
    ) -> Result<(), RuntimeError> {
        if !self.node(address)?.shape.pointer || address.ty != value.ty {
            return Err(invalid("pointer store type mismatch"));
        }
        let pointer = self.pointer(value)?;
        let slot = self.pointer(address)?;
        // SAFETY: the slot has pointer size/alignment; provenance also stays in checked metadata.
        unsafe {
            slot.cast::<*mut u8>().write(pointer);
        }
        self.node_mut(address)?.state = StorageState::Pointer(Some(value));
        Ok(())
    }

    pub(super) fn tag(
        &self,
        address: Address,
    ) -> Result<(Ustr, VariantPayloadStorage), RuntimeError> {
        let node = self.node(address)?;
        let StorageState::Variant(Some(tag)) = node.state else {
            return Err(invalid("read of absent variant tag"));
        };
        let case = node
            .shape
            .cases
            .as_ref()
            .and_then(|cases| cases.iter().find(|c| c.tag == tag))
            .ok_or_else(|| invalid("invalid variant tag"))?;
        let pointer = self.pointer(address)?;
        // SAFETY: tag extent/alignment validated during preparation; shell writes initialized it.
        let raw = unsafe { pointer.cast::<u32>().read() };
        let (id, storage) = VariantPayloadStorage::decode_tag(raw);
        if self.tags.get(&tag) != Some(&id) || storage != case.storage {
            return Err(invalid("variant tag representation mismatch"));
        }
        Ok((tag, storage))
    }
    pub(super) fn shell(
        &self,
        ty: Type,
        tag: Ustr,
        storage: VariantPayloadStorage,
    ) -> Result<StoredValue, RuntimeError> {
        let shape = self.shape(ty)?;
        let case = shape
            .cases
            .as_ref()
            .and_then(|cases| cases.iter().find(|c| c.tag == tag))
            .ok_or_else(|| invalid("variant case absent from type"))?;
        if case.storage != storage {
            return Err(invalid("variant payload storage mismatch"));
        }
        let payload = if case.payload == Type::unit() {
            StoredValue {
                ty: Type::unit(),
                data: StoredData::Scalar(Some(Scalar::Unit)),
            }
        } else if let Some(inline) = &case.inline {
            Self::absent(inline)
        } else {
            StoredValue {
                ty: case.payload,
                data: StoredData::Pointer(None),
            }
        };
        Ok(StoredValue {
            ty,
            data: StoredData::Variant(Some((tag, Box::new(payload)))),
        })
    }
    fn absent(shape: &StorageLayout) -> StoredValue {
        let data = if let Some(members) = &shape.members {
            if members.is_empty() {
                StoredData::Empty(false)
            } else {
                StoredData::Product(members.iter().map(|(_, m)| Self::absent(m)).collect())
            }
        } else if shape.cases.is_some() {
            StoredData::Variant(None)
        } else if shape.pointer {
            StoredData::Pointer(None)
        } else {
            StoredData::Scalar(None)
        };
        StoredValue { ty: shape.ty, data }
    }
    pub(super) fn read_value(
        &self,
        address: Address,
        allow_absent: bool,
    ) -> Result<StoredValue, RuntimeError> {
        let node = self.node(address)?;
        let data = match node.state {
            StorageState::Pointer(pointer) => {
                if !allow_absent && pointer.is_none() {
                    return Err(invalid("read of absent pointer"));
                }
                StoredData::Pointer(pointer)
            }
            StorageState::Product => StoredData::Product(
                node.children
                    .iter()
                    .map(|&child| {
                        self.read_value(self.address(address.allocation, child), allow_absent)
                    })
                    .collect::<Result<_, _>>()?,
            ),
            StorageState::Variant(Some(_)) => {
                let (tag, _) = self.tag(address)?;
                StoredData::Variant(Some((
                    tag,
                    Box::new(self.read_value(
                        self.address(address.allocation, node.children[0]),
                        allow_absent,
                    )?),
                )))
            }
            StorageState::Variant(None) => {
                if !allow_absent {
                    return Err(invalid("read of absent variant"));
                }
                StoredData::Variant(None)
            }
            StorageState::Value(present) => {
                // Empty products carry presence even though their payload extent is zero.
                if node.shape.members.is_some() {
                    if !allow_absent && !present {
                        return Err(invalid("read of absent empty product"));
                    }
                    StoredData::Empty(present)
                } else {
                    if !present && !allow_absent {
                        return Err(invalid("read of uninitialized storage"));
                    }
                    StoredData::Scalar(if present {
                        Some(self.read(address)?)
                    } else {
                        None
                    })
                }
            }
        };
        Ok(StoredValue {
            ty: address.ty,
            data,
        })
    }
    pub(super) fn write(&mut self, address: Address, value: Scalar) -> Result<(), RuntimeError> {
        self.write_value(
            address,
            &StoredValue {
                ty: value.kind().ty(),
                data: StoredData::Scalar(Some(value)),
            },
        )
    }
    pub(super) fn write_value(
        &mut self,
        address: Address,
        value: &StoredValue,
    ) -> Result<(), RuntimeError> {
        let shape = self.node(address)?.shape.clone();
        let source = if matches!(value.data, StoredData::Pointer(_)) {
            Rc::new(StorageLayout::pointer(value.ty))
        } else {
            self.shape(value.ty)?
        };
        if !shape.representation_compatible(&source) {
            return Err(invalid("store representation mismatch"));
        }
        match &value.data {
            StoredData::Empty(present) => {
                if shape.members.as_ref().is_none_or(|m| !m.is_empty()) {
                    return Err(invalid("expected empty product storage"));
                }
                self.node_mut(address)?.state = StorageState::Value(*present);
            }
            StoredData::Scalar(value) => {
                let Some(value) = value else {
                    return self.clear(address);
                };
                if shape.leaves.first().map(|(_, kind)| *kind) != Some(value.kind()) {
                    return Err(invalid("scalar store type mismatch"));
                }
                let pointer = self.pointer(address)?;
                // SAFETY: validated scalar layout/type, live allocation, aligned in-bounds pointer.
                unsafe {
                    match value {
                        Scalar::Unit => (),
                        Scalar::Bool(v) => pointer.cast::<bool>().write(*v),
                        Scalar::Int(v) => pointer.cast::<isize>().write(*v),
                        Scalar::Float(v) => pointer.cast::<Float>().write(*v),
                    }
                }
                self.node_mut(address)?.state = StorageState::Value(true);
            }
            StoredData::Pointer(value) => match value {
                Some(value) => self.write_pointer(address, *value)?,
                None => self.clear(address)?,
            },
            StoredData::Product(fields) => {
                let children = self.node(address)?.children.clone();
                if children.len() != fields.len() {
                    return Err(invalid("product snapshot arity mismatch"));
                }
                for (child, field) in children.into_iter().zip(fields) {
                    self.write_value(self.address(address.allocation, child), field)?;
                }
            }
            StoredData::Variant(value) => {
                let Some((tag, payload)) = value else {
                    return self.clear(address);
                };
                let case = shape
                    .cases
                    .as_ref()
                    .and_then(|cases| cases.iter().find(|c| c.tag == *tag))
                    .ok_or_else(|| invalid("invalid variant snapshot tag"))?;
                if self.node(address)?.state != StorageState::Variant(Some(*tag)) {
                    let owner = self.allocations[address.allocation].as_mut().unwrap();
                    owner.retire_children(address.node);
                    let child_shape = case
                        .inline
                        .clone()
                        .unwrap_or_else(|| Rc::new(StorageLayout::pointer(case.payload)));
                    let child_offset = address.offset
                        + variant_payload_offset(child_shape.layout.align() as u32) as usize;
                    let child = owner.add_node(child_shape, child_offset)?;
                    owner.nodes[address.node].children.push(child);
                }
                let tag_id = *self
                    .tags
                    .get(tag)
                    .ok_or_else(|| invalid("unregistered tag"))?;
                let raw = case.storage.encode_tag_id(tag_id);
                let pointer = self.pointer(address)?;
                // SAFETY: layout preparation validated the u32 tag slot and its alignment.
                unsafe {
                    pointer.cast::<u32>().write(raw);
                }
                self.node_mut(address)?.state = StorageState::Variant(Some(*tag));
                let child = self.node(address)?.children[0];
                self.write_value(self.address(address.allocation, child), payload)?;
            }
        }
        Ok(())
    }

    /// Host conversion uses an explicit worklist: recursive payload depth must not consume the
    /// Rust stack. Inline layout recursion remains bounded independently during preparation.
    pub(super) fn import(&mut self, ty: Type, value: &Value) -> Result<StoredValue, RuntimeError> {
        enum Task<'a> {
            Visit(Type, &'a Value),
            Product(Type, usize),
            Variant(Type, Ustr, Type, VariantPayloadStorage),
        }
        let unit = Value::unit();
        let mut tasks = vec![Task::Visit(ty, value)];
        let mut values: Vec<StoredValue> = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(ty, value) => {
                    let shape = self.shape(ty)?;
                    if let Some(members) = &shape.members {
                        let fields = value
                            .as_tuple()
                            .ok_or_else(|| invalid("expected product host value"))?;
                        if fields.len() != members.len() {
                            return Err(invalid("host product arity mismatch"));
                        }
                        tasks.push(Task::Product(ty, fields.len()));
                        tasks.extend(
                            members
                                .iter()
                                .zip(fields.iter())
                                .rev()
                                .map(|((_, m), field)| Task::Visit(m.ty, field)),
                        );
                    } else if let Some(cases) = &shape.cases {
                        let tag = value
                            .variant_tag()
                            .ok_or_else(|| invalid("expected variant host value"))?;
                        let case = cases
                            .iter()
                            .find(|c| c.tag == tag)
                            .ok_or_else(|| invalid("host variant case mismatch"))?;
                        let payload = value.variant_payload().unwrap_or(&unit);
                        tasks.push(Task::Variant(ty, tag, case.payload, case.storage));
                        tasks.push(Task::Visit(case.payload, payload));
                    } else {
                        let scalar = Scalar::from_value(value)?;
                        if ScalarKind::for_type(ty)? != scalar.kind() {
                            return Err(invalid("host scalar type mismatch"));
                        }
                        values.push(StoredValue {
                            ty,
                            data: StoredData::Scalar(Some(scalar)),
                        });
                    }
                }
                Task::Product(ty, count) => {
                    let data = if count == 0 {
                        StoredData::Empty(true)
                    } else {
                        StoredData::Product(values.split_off(values.len() - count))
                    };
                    values.push(StoredValue { ty, data });
                }
                Task::Variant(ty, tag, payload_ty, storage) => {
                    let mut payload = values.pop().unwrap();
                    if storage.is_indirect() {
                        let address = self.allocate_shape(self.shape(payload_ty)?, true, None)?;
                        self.write_value(address, &payload)?;
                        payload = StoredValue {
                            ty: payload_ty,
                            data: StoredData::Pointer(Some(address)),
                        };
                    }
                    values.push(StoredValue {
                        ty,
                        data: StoredData::Variant(Some((tag, Box::new(payload)))),
                    });
                }
            }
        }
        Ok(values.pop().unwrap())
    }

    pub(super) fn export(&self, address: Address) -> Result<Value, RuntimeError> {
        enum Task {
            Visit(Address),
            Product(Address, usize),
            Variant(Address, Ustr, VariantPayloadStorage, bool),
        }
        let mut tasks = vec![Task::Visit(address)];
        let mut values: Vec<Value> = Vec::new();
        let mut active = FxHashSet::default();
        let result = (|| {
            while let Some(task) = tasks.pop() {
                match task {
                    Task::Visit(address) => {
                        if !active.insert(address) {
                            return Err(invalid("cyclic owning payload"));
                        }
                        let node = self.node(address)?;
                        if node.shape.members.is_some() {
                            if !self.initialized(address)? {
                                return Err(invalid("export of absent product"));
                            }
                            tasks.push(Task::Product(address, node.children.len()));
                            tasks.extend(node.children.iter().rev().map(|&child| {
                                Task::Visit(self.address(address.allocation, child))
                            }));
                        } else if node.shape.cases.is_some() {
                            let (tag, storage) = self.tag(address)?;
                            let mut payload = self.address(address.allocation, node.children[0]);
                            if storage.is_indirect() {
                                payload = self.read_pointer(payload)?;
                            }
                            tasks.push(Task::Variant(
                                address,
                                tag,
                                storage,
                                payload.ty == Type::unit(),
                            ));
                            tasks.push(Task::Visit(payload));
                        } else {
                            values.push(self.read(address)?.boxed());
                            active.remove(&address);
                        }
                    }
                    Task::Product(address, count) => {
                        let fields = values.split_off(values.len() - count);
                        values.push(Value::tuple(fields));
                        active.remove(&address);
                    }
                    Task::Variant(address, tag, storage, unit) => {
                        let payload = values.pop().unwrap();
                        values.push(if unit {
                            payload.discard_storage();
                            Value::unit_variant(tag)
                        } else {
                            Value::variant_with_storage(tag, storage, payload)
                        });
                        active.remove(&address);
                    }
                }
            }
            Ok(values.pop().unwrap())
        })();
        // Values already materialized at the host boundary must be reclaimed if validation fails.
        for value in values {
            value.discard_storage();
        }
        result
    }
    pub(super) fn literal(
        &self,
        ty: Type,
        literal: &LiteralValue,
    ) -> Result<StoredValue, RuntimeError> {
        let shape = self.shape(ty)?;
        let data = if let Some(members) = &shape.members {
            let LiteralValue::Tuple(fields) = literal else {
                return Err(invalid("expected product literal"));
            };
            if fields.len() != members.len() {
                return Err(invalid("literal product arity mismatch"));
            }
            if members.is_empty() {
                StoredData::Empty(true)
            } else {
                StoredData::Product(
                    members
                        .iter()
                        .zip(fields.iter())
                        .map(|((_, m), field)| self.literal(m.ty, field))
                        .collect::<Result<_, _>>()?,
                )
            }
        } else {
            let scalar = Scalar::from_literal(literal)?;
            if ScalarKind::for_type(ty)? != scalar.kind() {
                return Err(invalid("literal scalar type mismatch"));
            }
            StoredData::Scalar(Some(scalar))
        };
        Ok(StoredValue { ty, data })
    }
    pub(super) fn matches(
        &self,
        address: Address,
        literal: &LiteralValue,
    ) -> Result<bool, RuntimeError> {
        Ok(self.read_value(address, false)? == self.literal(address.ty, literal)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::{Module, ModuleEnv, ModuleId, path::Path};
    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::wasm_bindgen_test;

    #[cfg_attr(not(target_arch = "wasm32"), test)]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn physical_evidence_shares_transitive_captures() {
        let mut memory = Memory::default();
        let leaf_layout = EvidenceEnvironmentLayout::new([true]).unwrap();
        let pair_layout = EvidenceEnvironmentLayout::new([false, false]).unwrap();
        let leaf = memory
            .allocate_evidence(
                7,
                Type::unit(),
                &leaf_layout,
                &[Evidence::Storage(true)],
                false,
                None,
            )
            .unwrap();
        let parent = memory
            .allocate_evidence(
                11,
                Type::unit(),
                &pair_layout,
                &[leaf.clone(), leaf.clone()],
                false,
                None,
            )
            .unwrap();
        let Evidence::Physical { reference, .. } = &leaf else {
            unreachable!()
        };
        assert_eq!(memory.evidence[&reference.environment].read::<usize>(0), 3);
        let Evidence::Physical {
            reference: parent_ref,
            ..
        } = &parent
        else {
            unreachable!()
        };
        let bytes = &memory.evidence[&parent_ref.environment];
        assert_eq!(bytes.read::<u32>(pair_layout.fields[0].offset), 7);
        assert_eq!(
            bytes.read::<usize>(
                pair_layout.fields[0].offset + offset_of!(DictionaryReference, environment)
            ),
            reference.environment
        );
        assert_eq!(
            memory.evidence_captures(&parent).unwrap(),
            vec![leaf.clone(), leaf.clone()]
        );

        // Model an escaping capture: releasing the constructing owner must leave the retained
        // environment and both of its shared prerequisite edges alive.
        memory.retain_evidence(&parent).unwrap();
        memory.release_evidence(&parent).unwrap();
        memory.release_evidence(&leaf).unwrap();
        assert_eq!(memory.evidence[&reference.environment].read::<usize>(0), 2);
        assert_eq!(
            memory.evidence_captures(&leaf).unwrap(),
            vec![Evidence::Storage(true)]
        );
        memory.release_evidence(&parent).unwrap();
        memory.check_runtime_ownership().unwrap();
        assert!(memory.evidence_captures(&leaf).is_err());
        assert!(memory.release_evidence(&parent).is_err());
    }

    #[cfg_attr(not(target_arch = "wasm32"), test)]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn physical_evidence_static_lifetimes_and_failed_capture() {
        let mut memory = Memory::default();
        let layout = EvidenceEnvironmentLayout::new([true]).unwrap();
        let parent_layout = EvidenceEnvironmentLayout::new([false, false]).unwrap();
        let static_value = memory
            .allocate_evidence(
                1,
                Type::unit(),
                &layout,
                &[Evidence::Storage(false)],
                true,
                None,
            )
            .unwrap();
        memory.retain_evidence(&static_value).unwrap();
        memory.release_evidence(&static_value).unwrap();
        assert_eq!(
            memory.evidence_captures(&static_value).unwrap(),
            vec![Evidence::Storage(false)]
        );

        let leaf = memory
            .allocate_evidence(
                2,
                Type::unit(),
                &layout,
                &[Evidence::Storage(true)],
                false,
                None,
            )
            .unwrap();
        assert!(
            memory
                .allocate_evidence(
                    3,
                    Type::unit(),
                    &parent_layout,
                    &[static_value.clone(), leaf.clone()],
                    true,
                    None
                )
                .is_err()
        );

        // A repeated capture can overflow after an earlier retain succeeded; rollback must
        // restore that earlier retain, rather than leaking a partially constructed environment.
        let Evidence::Physical { reference, .. } = &leaf else {
            unreachable!()
        };
        memory
            .evidence
            .get_mut(&reference.environment)
            .unwrap()
            .write(0, usize::MAX - 1);
        assert!(
            memory
                .allocate_evidence(
                    3,
                    Type::unit(),
                    &parent_layout,
                    &[leaf.clone(), leaf.clone()],
                    false,
                    None
                )
                .is_err()
        );
        assert_eq!(
            memory.evidence[&reference.environment].read::<usize>(0),
            usize::MAX - 1
        );
        memory
            .evidence
            .get_mut(&reference.environment)
            .unwrap()
            .write(0, 1usize);

        let span = Location::new_synthesized();
        memory.allocation_limit = 1;
        let error = memory
            .allocate_evidence(
                3,
                Type::unit(),
                &parent_layout,
                &[static_value, leaf.clone()],
                false,
                Some(span),
            )
            .unwrap_err();
        assert!(matches!(error, RuntimeError::SandboxViolation(_)));
        assert!(memory.allocate(ScalarKind::Int.ty(), Some(span)).is_err());
        memory.release_evidence(&leaf).unwrap();
        memory.check_runtime_ownership().unwrap();
    }

    #[test]
    fn physical_variant_storage_checks_active_payloads_and_reuses_identities() {
        let module = Module::new(ModuleId::from_index(0), Path::single_str("memory_test"));
        let modules = Default::default();
        let env = ModuleEnv::new(&module, &modules);
        let int = ScalarKind::Int.ty();
        let ty = Type::variant(vec![
            ("A".into(), int),
            ("B".into(), int),
            ("Empty".into(), Type::unit()),
        ]);
        let mut memory = Memory::default();
        memory.prepare_type(ty, &env).unwrap();
        memory.bind_tags(|tag| match tag.as_str() {
            "A" => 17,
            "B" => 9,
            _ => 30,
        });
        let root = memory.allocate(ty, None).unwrap();
        let shell = memory
            .shell(ty, "A".into(), VariantPayloadStorage::Inline)
            .unwrap();
        memory.write_value(root, &shell).unwrap();
        assert!(
            memory.initialized(root).unwrap(),
            "a shell stays live during payload construction"
        );
        assert!(memory.read_value(root, false).is_err());
        let offset = variant_payload_offset(align_of::<isize>() as u32) as usize;
        let first = memory.offset(root, offset, int).unwrap();
        memory.write(first, Scalar::Int(42)).unwrap();
        let whole = memory.read_value(root, false).unwrap();
        let copy = memory.allocate(ty, None).unwrap();
        memory.write_value(copy, &whole).unwrap();
        assert_eq!(memory.read_value(copy, false).unwrap(), whole);
        for tag in ["B", "A"].into_iter().cycle().take(128) {
            let shell = memory
                .shell(ty, tag.into(), VariantPayloadStorage::Inline)
                .unwrap();
            memory.write_value(root, &shell).unwrap();
            assert_eq!(memory.tag(root).unwrap().0.as_str(), tag);
            assert!(
                memory.read(first).is_err(),
                "old case views never revive, even at the same address"
            );
            let field = memory.offset(root, offset, int).unwrap();
            memory.write(field, Scalar::Int(7)).unwrap();
        }
        assert_eq!(memory.allocation(root).unwrap().nodes.len(), 2);
        assert!(memory.offset(root, offset, ScalarKind::Bool.ty()).is_err());
        let empty = memory
            .shell(ty, "Empty".into(), VariantPayloadStorage::Inline)
            .unwrap();
        memory.write_value(root, &empty).unwrap();
        assert!(memory.read_value(root, false).is_ok());
        let value = memory.export(root).unwrap();
        assert_eq!(value.variant_tag(), Some("Empty".into()));
        value.discard_storage();
    }

    #[test]
    fn physical_runtime_allocations_survive_frames_and_require_release() {
        let mut memory = Memory::default();
        let int = ScalarKind::Int.ty();
        let slot = memory.allocate_place(int, None).unwrap();
        let marker = memory.len();
        let temporary = memory.allocate(int, None).unwrap();
        let payload = memory
            .allocate_runtime(int, size_of::<isize>(), align_of::<isize>(), None)
            .unwrap();
        memory.write(payload, Scalar::Int(42)).unwrap();
        memory.write_pointer(slot, payload).unwrap();
        memory.restore(marker);
        assert!(memory.read(temporary).is_err());
        assert_eq!(
            memory.read(memory.read_pointer(slot).unwrap()).unwrap(),
            Scalar::Int(42)
        );
        memory.check_runtime_ownership().unwrap();
        // Two distinct slots must not disguise a duplicated owner as shared reachability.
        let duplicate = memory.allocate_place(int, None).unwrap();
        memory.write_pointer(duplicate, payload).unwrap();
        assert!(matches!(memory.check_runtime_ownership(),
            Err(RuntimeError::Backend(message)) if message.contains("multiple owners")));
        memory.restore(marker);
        memory.check_runtime_ownership().unwrap();
        memory.clear(slot).unwrap();
        assert!(
            memory.check_runtime_ownership().is_err(),
            "stack reclamation cannot hide an orphan payload"
        );
        memory.deallocate(payload).unwrap();
        assert!(memory.deallocate(payload).is_err());
        assert!(memory.pointer(payload).is_err());
        memory.restore(0);
        assert_eq!(memory.live_allocations(), 0);
        memory.allocation_limit = 0;
        let span = Some(Location::new_synthesized());
        for allocation in [
            memory.allocate(int, span),
            memory.allocate_place(int, span),
            memory.allocate_runtime(int, size_of::<isize>(), align_of::<isize>(), span),
        ] {
            let Err(RuntimeError::SandboxViolation(violation)) = allocation else {
                panic!("all allocation paths must enforce the storage limit");
            };
            assert_eq!(violation.location(), span);
        }
    }

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
                nodes: 1,
                members: Some(vec![]),
                cases: None,
                pointer: false,
                leaves: vec![(offset, ScalarKind::Int)],
            });
            assert!(StorageLayout::product(ty, layout, vec![(0, malformed)]).is_err());
        }
    }

    #[test]
    fn physical_product_preparation_bounds_expansion() {
        let module = Module::new(ModuleId::from_index(0), Path::single_str("memory_test"));
        let modules = Default::default();
        let env = ModuleEnv::new(&module, &modules);
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
        let module = Module::new(ModuleId::from_index(0), Path::single_str("memory_test"));
        let modules = Default::default();
        let env = ModuleEnv::new(&module, &modules);
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
        let destination = memory.allocate(right, None).unwrap();
        assert!(memory.write_value(destination, &value).is_err());
        assert!(!memory.any_initialized(destination).unwrap());
        let source = memory.allocate(left, None).unwrap();
        memory.write_value(source, &value).unwrap();

        let product = memory.allocate(mixed, None).unwrap();
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
        let module = Module::new(ModuleId::from_index(0), Path::single("memory_test".into()));
        let modules = Default::default();
        let env = ModuleEnv::new(&module, &modules);
        let ty = Type::record(vec![
            ("a".into(), ScalarKind::Bool.ty()),
            ("b".into(), ScalarKind::Int.ty()),
        ]);
        let spec = product_layout_spec(ty, Location::new_synthesized(), &env).unwrap();
        let mut memory = Memory::default();
        memory.prepare_type(ty, &env).unwrap();
        let whole = memory.allocate(ty, None).unwrap();
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
        let copy = memory.allocate(ty, None).unwrap();
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
        let empty = Type::tuple(vec![Type::unit(); 2]);
        let outer = Type::tuple(vec![empty, empty, ScalarKind::Int.ty()]);
        memory.prepare_type(outer, &env).unwrap();
        let root = memory.allocate(outer, None).unwrap();
        let first = memory
            .project(root, 0, empty, Some(ProjectionIndex::from_index(0)))
            .unwrap();
        let second = memory
            .project(root, 0, empty, Some(ProjectionIndex::from_index(1)))
            .unwrap();
        assert_ne!(first, second);
        assert_eq!(
            memory.pointer(first).unwrap(),
            memory.pointer(second).unwrap()
        );
        assert!(!memory.overlaps(first, second).unwrap());
        let value = memory
            .literal(
                empty,
                &LiteralValue::new_tuple(vec![LiteralValue::new_native(()); 2]),
            )
            .unwrap();
        memory.write_value(first, &value).unwrap();
        memory.write_value(second, &value).unwrap();
        memory.clear(first).unwrap();
        assert!(!memory.any_initialized(first).unwrap());
        assert!(memory.initialized(second).unwrap());
    }

    #[test]
    fn physical_memory_checks_initialization_bounds_and_lifetimes() {
        let mut memory = Memory::default();
        let address = memory.allocate(ScalarKind::Int.ty(), None).unwrap();
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
        let replacement = memory.allocate(ScalarKind::Int.ty(), None).unwrap();
        assert_ne!(address, replacement);
        assert!(memory.pointer(address).is_err());
        let unit = memory.allocate(ScalarKind::Unit.ty(), None).unwrap();
        assert!(!memory.initialized(unit).unwrap());
        memory.write(unit, Scalar::Unit).unwrap();
        assert_eq!(memory.read(unit).unwrap(), Scalar::Unit);
        memory.restore(0);
        assert_eq!(memory.len(), 0);
    }
}
