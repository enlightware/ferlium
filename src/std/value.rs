// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{
    any::TypeId,
    cmp::{Ordering, Reverse},
    mem,
};

use ustr::{Ustr, ustr};

use crate::{
    FxHashMap, FxHashSet, Location,
    ast::{Path, UnnamedArg},
    compiler::error::{CompilerLimit, CompilerLimitKind, InternalCompilationError},
    containers::b,
    desugar::DepGraphNode,
    graph::find_strongly_connected_components,
    hir::{
        self, CallArgument, NodeArena, NodeId,
        dictionary::DictionaryReq,
        emit_value_impl::function_value_method,
        function::{CallableDefinition, Function, PendingScriptFunction},
        native_functions::{NativeDropFn, NativeFnN, NativeFnR, NativeOutFnR},
        value::{LiteralValue, NativeValue, VariantPayloadStorage},
        value_dispatch::{
            materialize_static_string, prepare_generated_call_arguments_with_locals,
            static_apply_generated_with_locals, wrap_generated_call_with_temp_cleanup,
        },
    },
    internal_compilation_error,
    module::{
        self, ConcreteTraitImplKey, FunctionId, LocalDecl, LocalDeclId, LocalImplId, Module,
        ModuleEnv, PendingFunctionBody, PendingLocalDrop, PendingModuleFunction, ProjectionIndex,
        ResolvedValueLayout, TraitDictionaryEntry, TraitId, TraitImpl, TraitImplId, TraitImpls,
        TypeDefId, id::Id,
    },
    std::{
        STD_MODULE_ID,
        core_traits_names::{
            BITS_TRAIT_NAME, INSPECT_TRAIT_NAME, NUM_TRAIT_NAME, ORD_TRAIT_NAME, VALUE_TRAIT_NAME,
        },
        hash::hasher_type,
        logic::bool_type,
        math::{Float, float_type, int_type, raw_float_type},
        ordering::ORDERING_GREATER,
        string::{static_str_type, string_type},
    },
    types::{
        effects::{EffType, PrimitiveEffect},
        mutability::{MutType, MutVal},
        r#trait::{
            DerivedRequirements, Deriver, Trait, TraitAssociatedConst, TraitAssociatedConstIndex,
            TraitDictionaryEntryIndex, TraitMethodIndex, structural_members,
        },
        trait_solver::TraitSolver,
        r#type::{
            CallImplType, FnArgType, FnType, REPRESENTATION_HEIGHT_LIMIT,
            REPRESENTATION_SIZE_LIMIT, Type, TypeKind, tuple_type,
        },
        type_like::TypeLike,
        type_mapper::EffectErasingMapper,
        type_properties::{RepresentationMetrics, TypeDefEnv},
        type_scheme::PubTypeConstraint,
    },
};

pub(crate) extern "C" fn equal<T>(lhs: T, rhs: T) -> bool
where
    T: std::cmp::Eq,
{
    lhs == rhs
}

pub(crate) const VALUE_EQ_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex::new(0);
pub(crate) const VALUE_TO_STRING_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex::new(1);
pub(crate) const VALUE_HASH_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex::new(2);
pub(crate) const VALUE_CLONE_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex::new(3);
pub(crate) const VALUE_DROP_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex::new(4);
pub(crate) const VALUE_NE_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex::new(5);
pub(crate) const VALUE_SIZE_ASSOC_CONST_INDEX: TraitAssociatedConstIndex =
    TraitAssociatedConstIndex::new(0);
pub(crate) const VALUE_ALIGN_ASSOC_CONST_INDEX: TraitAssociatedConstIndex =
    TraitAssociatedConstIndex::new(1);
pub(crate) const INSPECT_METHOD_INDEX: TraitMethodIndex = TraitMethodIndex::new(0);
pub(crate) const NO_DERIVE_VALUE_ATTRIBUTE: &str = "no_derive_value";

/// Whether `function` is a method (or dictionary entry wrapper) implementing `Value::drop`.
pub(crate) fn is_value_drop_function(function: FunctionId, env: &ModuleEnv<'_>) -> bool {
    let Some(module) = env.module_by_id(function.module) else {
        return false;
    };
    let value_trait = env.expect_std_trait_id(VALUE_TRAIT_NAME);
    let drop_entry = env
        .trait_def(value_trait)
        .dictionary_method_index(VALUE_DROP_METHOD_INDEX);
    (0..module.impl_count()).any(|index| {
        let impl_id = LocalImplId::from_index(index);
        let implementation = module
            .get_impl_data(impl_id)
            .expect("implementation index came from this module");
        if implementation.trait_id != value_trait {
            return false;
        }
        implementation
            .methods
            .get(VALUE_DROP_METHOD_INDEX.as_index())
            .is_some_and(|method| *method == function.function)
            || matches!(
                implementation.dictionary_value.entry(drop_entry),
                TraitDictionaryEntry::Function(method) if method == function.function
            )
    })
}

const VARIANT_TAG_SIZE: u32 = mem::size_of::<u32>() as u32;
const VARIANT_TAG_ALIGN: u32 = mem::align_of::<u32>() as u32;

pub(crate) fn variant_tag_layout() -> ResolvedValueLayout {
    ResolvedValueLayout {
        size: VARIANT_TAG_SIZE,
        align: VARIANT_TAG_ALIGN,
    }
}

pub(crate) fn variant_payload_offset(payload_align: u32) -> u32 {
    debug_assert!(payload_align.is_power_of_two());
    VARIANT_TAG_SIZE.div_ceil(payload_align) * payload_align
}

/// Dictionary entry and callable surface of one `Value` layout getter.
pub(crate) fn value_layout_getter_entry(
    env: &ModuleEnv<'_>,
    associated_const: TraitAssociatedConstIndex,
) -> (TraitDictionaryEntryIndex, FnType) {
    let value_trait = env.expect_std_trait_id(VALUE_TRAIT_NAME);
    let entry = env
        .trait_def(value_trait)
        .dictionary_associated_const_index(associated_const);
    let ty = FnType::new_by_val(
        [],
        crate::std::math::int_type(),
        crate::types::effects::no_effects(),
    );
    (entry, ty)
}

pub(crate) fn native_layout_associated_consts<T>() -> Vec<LiteralValue> {
    let mut values = [0; 2];
    values[usize::from(VALUE_SIZE_ASSOC_CONST_INDEX)] = mem::size_of::<T>() as isize;
    values[usize::from(VALUE_ALIGN_ASSOC_CONST_INDEX)] = mem::align_of::<T>() as isize;
    values.into_iter().map(LiteralValue::new_native).collect()
}

extern "C" fn native_scalar_clone<T: Copy>(source: T) -> T {
    source
}

extern "C" fn native_unit_clone(_: &()) {}

pub(crate) fn native_value_clone_function<T: Clone + NativeValue>() -> Function {
    // Concrete scalar clones use the same direct transport as ordinary scalar entries.
    // Unit has no scalar representation: its input stays indirect and its result is omitted.
    match TypeId::of::<T>() {
        id if id == TypeId::of::<bool>() => b(NativeFnN::new(native_scalar_clone::<bool>)),
        id if id == TypeId::of::<isize>() => b(NativeFnN::new(native_scalar_clone::<isize>)),
        id if id == TypeId::of::<Float>() => b(NativeFnN::new(native_scalar_clone::<Float>)),
        id if id == TypeId::of::<()>() => b(NativeFnR::new(native_unit_clone)),
        _ => b(NativeOutFnR::from_rust(T::clone)),
    }
}

/// Destroy an initialized native value, leaving its storage uninitialized and still allocated.
///
/// # Safety
/// `target` must point to an exclusively owned, initialized, correctly aligned `T`.
pub(crate) unsafe extern "C" fn native_value_drop<T>(target: *mut T) {
    // SAFETY: the caller supplies an initialized T and ends all access to it after this call.
    unsafe { target.drop_in_place() };
}

pub(crate) fn native_value_drop_function<T: 'static>() -> Function {
    // SAFETY: this entry destroys exactly one T without deallocating its storage. This helper
    // registers only the compiler-owned Value::drop method for that native type.
    b(unsafe { NativeDropFn::new(native_value_drop::<T>) }) as Function
}

#[derive(Debug, Clone, Copy)]
struct ValueLayout {
    size: usize,
    align: usize,
}

impl ValueLayout {
    fn new(size: usize, align: usize) -> Self {
        assert!(
            align.is_power_of_two(),
            "type alignment must be a non-zero power of two"
        );
        assert_eq!(
            size % align,
            0,
            "type size must be divisible by its alignment"
        );
        Self { size, align }
    }

    fn native<T>() -> Self {
        Self::new(mem::size_of::<T>(), mem::align_of::<T>())
    }

    /// Canonical compiled representation shared by first-class functions and subscripts.
    fn callable() -> Self {
        Self::product([Self::native::<u32>(), Self::native::<usize>()])
    }

    fn associated_const_values(
        self,
        span: Location,
    ) -> Result<[isize; 2], InternalCompilationError> {
        let mut values = [0; 2];
        values[usize::from(VALUE_SIZE_ASSOC_CONST_INDEX)] =
            isize::try_from(self.size).map_err(|_| {
                internal_compilation_error!(Internal {
                    error: format!("Value size {} does not fit in int", self.size),
                    span,
                })
            })?;
        values[usize::from(VALUE_ALIGN_ASSOC_CONST_INDEX)] =
            isize::try_from(self.align).map_err(|_| {
                internal_compilation_error!(Internal {
                    error: format!("Value alignment {} does not fit in int", self.align),
                    span,
                })
            })?;
        Ok(values)
    }

    fn product(fields: impl IntoIterator<Item = ValueLayout>) -> Self {
        let mut size = 0;
        let mut align = 1;
        for field in fields {
            size = align_to(size, field.align);
            size += field.size;
            align = align.max(field.align);
        }
        Self::new(align_to(size, align), align)
    }

    #[cfg(test)]
    fn variant(payloads: impl IntoIterator<Item = ValueLayout>) -> Self {
        let tag = Self::native::<u32>();
        let mut size = tag.size;
        let mut align = tag.align;
        for payload in payloads {
            let payload_offset = align_to(tag.size, payload.align);
            size = size.max(payload_offset + payload.size);
            align = align.max(payload.align);
        }
        Self::new(align_to(size, align), align)
    }
}

/// A target-matched `Value` layout expression.
///
/// Static layouts fold to [`Constant`](ValueLayoutExpr::Constant). Open layouts retain only the
/// associated-constant reads and the payload storages which a generated dictionary getter must
/// read at run time. The same expression is evaluated for compile-time layout queries and emitted
/// as HIR for open generated `Value` dictionaries, keeping the two calculations identical by
/// construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValueLayoutExpr {
    Constant(isize),
    AssociatedConst {
        ty: Type,
        index: TraitAssociatedConstIndex,
    },
    Add(Box<Self>, Box<Self>),
    Max(Box<Self>, Box<Self>),
    AlignTo(Box<Self>, Box<Self>),
    /// `indirect` when the payload of a case is behind a pointer, `inline` otherwise. The storage
    /// is open here, so it is read from the evidence of `storage`, a canonical
    /// [`DictionaryReq::VariantPayloadIndirection`] (see [`variant_payload_storage_decision`]).
    PayloadStorage {
        storage: DictionaryReq,
        indirect: Box<Self>,
        inline: Box<Self>,
    },
}

/// The largest size of a value. Layout components are signed sizes, which have 32 bits on a 32-bit
/// host such as Wasm.
pub const VALUE_SIZE_LIMIT: usize = i32::MAX as usize;

impl ValueLayoutExpr {
    /// A layout component, which is a size, an alignment or an offset, so at most
    /// [`VALUE_SIZE_LIMIT`].
    fn constant(value: usize, span: Location) -> Result<Self, InternalCompilationError> {
        if value > VALUE_SIZE_LIMIT {
            return Err(internal_compilation_error!(CompilerLimitExceeded(
                CompilerLimit {
                    kind: CompilerLimitKind::ValueSize,
                    actual: value,
                    limit: VALUE_SIZE_LIMIT,
                    span,
                }
            )));
        }
        Ok(Self::Constant(value as isize))
    }

    fn associated_const(ty: Type, index: TraitAssociatedConstIndex) -> Self {
        Self::AssociatedConst { ty, index }
    }

    fn add(left: Self, right: Self, span: Location) -> Result<Self, InternalCompilationError> {
        match (&left, &right) {
            (Self::Constant(0), _) => Ok(right),
            (_, Self::Constant(0)) => Ok(left),
            (Self::Constant(left), Self::Constant(right)) => {
                // Both are at most `VALUE_SIZE_LIMIT`, so their sum fits in `usize` on every host.
                Self::constant(*left as usize + *right as usize, span)
            }
            _ => Ok(Self::Add(Box::new(left), Box::new(right))),
        }
    }

    fn max(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => Self::Constant((*left).max(*right)),
            _ if left == right => left,
            _ => Self::Max(Box::new(left), Box::new(right)),
        }
    }

    fn align_to(
        offset: Self,
        align: Self,
        span: Location,
    ) -> Result<Self, InternalCompilationError> {
        match (&offset, &align) {
            (_, Self::Constant(1)) | (Self::Constant(0), _) => Ok(offset),
            (Self::Constant(offset), Self::Constant(align)) => {
                let offset = usize::try_from(*offset).expect("layout offsets are non-negative");
                let align = usize::try_from(*align).expect("layout alignments are positive");
                Self::constant(super::value::align_to(offset, align), span)
            }
            _ => Ok(Self::AlignTo(Box::new(offset), Box::new(align))),
        }
    }

    /// A choice whose two layouts are equal reads no storage. The methods of a dictionary find the
    /// storages they read on their own ([`generated_value_storage_requirements`]).
    fn payload_storage(storage: DictionaryReq, indirect: Self, inline: Self) -> Self {
        if indirect == inline {
            inline
        } else {
            Self::PayloadStorage {
                storage,
                indirect: Box::new(indirect),
                inline: Box::new(inline),
            }
        }
    }

    pub(crate) fn constant_value(&self) -> Option<isize> {
        match self {
            Self::Constant(value) => Some(*value),
            _ => None,
        }
    }

    fn collect_evidence(&self, types: &mut Vec<Type>, storages: &mut Vec<DictionaryReq>) {
        match self {
            Self::Constant(_) => {}
            Self::AssociatedConst { ty, .. } => {
                if !types.contains(ty) {
                    types.push(*ty);
                }
            }
            Self::Add(left, right) | Self::Max(left, right) | Self::AlignTo(left, right) => {
                left.collect_evidence(types, storages);
                right.collect_evidence(types, storages);
            }
            Self::PayloadStorage {
                storage,
                indirect,
                inline,
            } => {
                if !storages.contains(storage) {
                    storages.push(storage.clone());
                }
                indirect.collect_evidence(types, storages);
                inline.collect_evidence(types, storages);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ValueLayoutFormula {
    pub(crate) size: ValueLayoutExpr,
    pub(crate) align: ValueLayoutExpr,
}

impl ValueLayoutFormula {
    fn constant(layout: ValueLayout, span: Location) -> Result<Self, InternalCompilationError> {
        Ok(Self {
            size: ValueLayoutExpr::constant(layout.size, span)?,
            align: ValueLayoutExpr::constant(layout.align, span)?,
        })
    }

    fn product(
        fields: impl IntoIterator<Item = Self>,
        span: Location,
    ) -> Result<Self, InternalCompilationError> {
        let mut size = ValueLayoutExpr::Constant(0);
        let mut align = ValueLayoutExpr::Constant(1);
        for field in fields {
            size = ValueLayoutExpr::add(size, field.size, span)?;
            align = ValueLayoutExpr::max(align, field.align);
        }
        size = ValueLayoutExpr::align_to(size, align.clone(), span)?;
        Ok(Self { size, align })
    }

    fn variant(
        payloads: impl IntoIterator<Item = Self>,
        span: Location,
    ) -> Result<Self, InternalCompilationError> {
        let tag_layout = variant_tag_layout();
        let tag = Self::constant(
            ValueLayout::new(tag_layout.size as usize, tag_layout.align as usize),
            span,
        )?;
        let mut size = tag.size.clone();
        let mut align = tag.align.clone();
        for payload in payloads {
            let payload_offset =
                ValueLayoutExpr::align_to(tag.size.clone(), payload.align.clone(), span)?;
            let payload_end = ValueLayoutExpr::add(payload_offset, payload.size, span)?;
            size = ValueLayoutExpr::max(size, payload_end);
            align = ValueLayoutExpr::max(align, payload.align);
        }
        size = ValueLayoutExpr::align_to(size, align.clone(), span)?;
        Ok(Self { size, align })
    }

    fn resolved(&self, span: Location) -> Result<ValueLayout, InternalCompilationError> {
        let Some(size) = self.size.constant_value() else {
            return Err(internal_compilation_error!(Internal {
                error: "cannot compute Value size without run-time evidence".to_owned(),
                span,
            }));
        };
        let Some(align) = self.align.constant_value() else {
            return Err(internal_compilation_error!(Internal {
                error: "cannot compute Value alignment without run-time evidence".to_owned(),
                span,
            }));
        };
        let size = usize::try_from(size).expect("layout sizes are non-negative");
        let align = usize::try_from(align).expect("layout alignments are positive");
        Ok(ValueLayout::new(size, align))
    }

    fn is_constant(&self) -> bool {
        self.size.constant_value().is_some() && self.align.constant_value().is_some()
    }

    /// The layout that `ty`'s own `Value` evidence gives.
    fn symbolic(ty: Type) -> Self {
        Self {
            size: ValueLayoutExpr::associated_const(ty, VALUE_SIZE_ASSOC_CONST_INDEX),
            align: ValueLayoutExpr::associated_const(ty, VALUE_ALIGN_ASSOC_CONST_INDEX),
        }
    }

    fn associated_const(self, index: TraitAssociatedConstIndex) -> ValueLayoutExpr {
        if index == VALUE_SIZE_ASSOC_CONST_INDEX {
            self.size
        } else {
            assert_eq!(index, VALUE_ALIGN_ASSOC_CONST_INDEX);
            self.align
        }
    }
}

fn align_to(offset: usize, align: usize) -> usize {
    debug_assert!(align > 0);
    let rem = offset % align;
    if rem == 0 {
        offset
    } else {
        offset + (align - rem)
    }
}

/// One direct member in the canonical product layout recipe.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ProductMemberLayout {
    /// Present for records and absent for tuple members.
    pub(crate) name: Option<Ustr>,
    pub(crate) ty: Type,
    /// Absent exactly when the member's layout comes from its run-time `Value` evidence.
    pub(crate) static_layout: Option<ResolvedValueLayout>,
}

/// Logical members plus the canonical rule that maps them into physical order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProductLayoutSpec {
    pub(crate) members: Vec<ProductMemberLayout>,
}

impl ProductLayoutSpec {
    /// Return the logical member types whose layout remains open.
    pub(crate) fn dynamic_member_layouts(&self) -> Vec<Type> {
        self.members
            .iter()
            .filter_map(|member| member.static_layout.is_none().then_some(member.ty))
            .collect()
    }

    /// Whether a member precedes another in physical order: decreasing alignment, then
    /// field name for records or numeric index for tuples. Members stay in logical order.
    pub(crate) fn compact_member_precedes(
        &self,
        candidate: ProjectionIndex,
        target: ProjectionIndex,
        alignment_order: Ordering,
    ) -> bool {
        match alignment_order {
            Ordering::Greater => true,
            Ordering::Less => false,
            Ordering::Equal => self.member_tie_key(candidate) < self.member_tie_key(target),
        }
    }

    fn member_tie_key(&self, index: ProjectionIndex) -> (Option<Ustr>, usize) {
        (self.members[index.as_index()].name, index.as_index())
    }

    /// Members whose contribution needs a runtime alignment comparison. The boolean says
    /// whether equal alignment also precedes the target, selecting >= rather than >.
    pub(crate) fn runtime_order_candidates(
        &self,
        target: ProjectionIndex,
    ) -> impl Iterator<Item = (ProjectionIndex, bool)> + '_ {
        let target_static = self.members[target.as_index()].static_layout.is_some();
        self.members
            .iter()
            .enumerate()
            .filter_map(move |(index, member)| {
                if index == target.as_index() || (target_static && member.static_layout.is_some()) {
                    return None;
                }
                let index = ProjectionIndex::from_index(index);
                Some((
                    index,
                    self.compact_member_precedes(index, target, Ordering::Equal),
                ))
            })
    }

    /// Contribution of statically known preceding members. Open members are handled by
    /// the runtime addressor; an open target has no statically known contribution.
    pub(crate) fn static_prefix_offset(&self, index: ProjectionIndex) -> Option<usize> {
        let target_layout = self.members.get(index.as_index())?.static_layout?;
        let mut offset = 0usize;
        for (candidate_index, candidate) in self.members.iter().enumerate() {
            if candidate_index == index.as_index() {
                continue;
            }
            let Some(layout) = candidate.static_layout else {
                continue;
            };
            if self.compact_member_precedes(
                ProjectionIndex::from_index(candidate_index),
                index,
                layout.align.cmp(&target_layout.align),
            ) {
                offset = offset
                    .checked_add(layout.size as usize)
                    .expect("product offset fits in usize");
            }
        }
        Some(offset)
    }

    /// Computes one offset without sorting, when all necessary layouts are static.
    pub(crate) fn static_field_offset(&self, index: ProjectionIndex) -> Option<usize> {
        self.members.get(index.as_index())?;
        if self.members.len() == 1 {
            return Some(0);
        }
        if self
            .members
            .iter()
            .any(|member| member.static_layout.is_none())
        {
            return None;
        }
        self.static_prefix_offset(index)
    }

    /// All offsets in logical order, computed with one O(n log n) sort.
    pub(crate) fn static_field_offsets(&self) -> Option<Vec<usize>> {
        if self.members.len() == 1 {
            return Some(vec![0]);
        }
        let layouts = self
            .members
            .iter()
            .map(|member| member.static_layout)
            .collect::<Option<Vec<_>>>()?;
        let mut order = (0..self.members.len()).collect::<Vec<_>>();
        order.sort_unstable_by_key(|&index| {
            (
                Reverse(layouts[index].align),
                self.member_tie_key(ProjectionIndex::from_index(index)),
            )
        });
        let mut offsets = vec![0; order.len()];
        let mut offset = 0usize;
        for index in order {
            offsets[index] = offset;
            offset = offset
                .checked_add(layouts[index].size as usize)
                .expect("product offset fits in usize");
        }
        Some(offsets)
    }
}

pub(crate) trait TypeLayoutEnv: TypeDefEnv {
    fn current_module_id(&self) -> crate::module::ModuleId;
}

/// Whether `left` and `right` have the same representation: they are equal once every callable is
/// taken as one leaf. A callable has one layout whatever its signature, effects or argument access
/// modes (`doc/abi.md`, "First-class callables"), so a value keeps its bytes when a callable within
/// it is widened, at any depth.
fn same_representation(left: Type, right: Type) -> bool {
    if left == right {
        return true;
    }
    // The first pair allocates nothing when it already differs or has no children, as when a
    // search compares a tuple with a variant.
    let mut pending = Vec::new();
    if !push_representation_children(left, right, &mut pending) {
        return false;
    }
    if pending.is_empty() {
        return true;
    }
    // Pairs being compared are assumed equal when met again: recursive types lead back to them.
    let mut seen = FxHashSet::default();
    seen.insert((left, right));
    while let Some((left, right)) = pending.pop() {
        if left == right || !seen.insert((left, right)) {
            continue;
        }
        if !push_representation_children(left, right, &mut pending) {
            return false;
        }
    }
    true
}

/// Whether `left` and `right` have the same constructor for [`same_representation`]; if so, push
/// the pairs of their children that must have the same representation too.
fn push_representation_children(left: Type, right: Type, pending: &mut Vec<(Type, Type)>) -> bool {
    let left = left.data();
    let right = right.data();
    use TypeKind::*;
    match (&*left, &*right) {
        (Function(_) | Subscript(_), Function(_) | Subscript(_)) => {}
        (Tuple(a), Tuple(b)) if a.len() == b.len() => {
            pending.extend(a.iter().copied().zip(b.iter().copied()))
        }
        (Record(a), Record(b)) | (Variant(a), Variant(b))
            if a.len() == b.len() && a.iter().zip(b).all(|(a, b)| a.0 == b.0) =>
        {
            pending.extend(a.iter().zip(b).map(|(a, b)| (a.1, b.1)))
        }
        (Named(a), Named(b)) if a.def == b.def && a.params.len() == b.params.len() => {
            pending.extend(a.params.iter().copied().zip(b.params.iter().copied()))
        }
        (Native(a), Native(b))
            if a.bare_ty == b.bare_ty && a.arguments.len() == b.arguments.len() =>
        {
            pending.extend(a.arguments.iter().copied().zip(b.arguments.iter().copied()))
        }
        _ => return false,
    }
    true
}

/// Whether following the representation-bearing fields of `start` can return to `target`, up to
/// [`same_representation`].
///
/// Native, function, and subscript type arguments are not embedded fields of those values. Named
/// types, conversely, are transparent wrappers around their instantiated structural shape.
fn representation_reaches(
    start: Type,
    target: Type,
    env: &impl TypeLayoutEnv,
    seen: &mut FxHashSet<Type>,
) -> bool {
    if same_representation(start, target) {
        return true;
    }
    if !seen.insert(start) {
        return false;
    }

    let data = start.data().clone();
    match data {
        TypeKind::Tuple(fields) => fields
            .into_iter()
            .any(|field| representation_reaches(field, target, env, seen)),
        TypeKind::Record(fields) | TypeKind::Variant(fields) => fields
            .into_iter()
            .any(|(_, field)| representation_reaches(field, target, env, seen)),
        TypeKind::Named(named) => {
            let shape = env
                .type_def(named.def)
                .instantiated_shape_with_effects(&named.params, &named.effect_params);
            representation_reaches(shape, target, env, seen)
        }
        TypeKind::Variable(_)
        | TypeKind::Native(_)
        | TypeKind::Function(_)
        | TypeKind::Subscript(_)
        | TypeKind::Never => false,
    }
}

/// Classify one variant payload occurrence. A recursive payload is indirect; every other payload
/// is inline. Products always own their members inline, so recursion is cut only at variant edges.
/// Recursion is found up to callables, so types that differ only within callables, such as by a
/// widened effect, have the same layout.
fn payload_storage_in_variant(
    variant: Type,
    payload: Type,
    env: &impl TypeLayoutEnv,
) -> VariantPayloadStorage {
    VariantPayloadStorage::from_indirect(representation_reaches(
        payload,
        variant,
        env,
        &mut FxHashSet::default(),
    ))
}

pub(crate) fn structural_variant(
    variant_ty: Type,
    env: &impl TypeLayoutEnv,
) -> Option<(Type, Vec<(Ustr, Type)>)> {
    let mut structural_ty = variant_ty;
    let mut seen = FxHashSet::default();
    loop {
        if !seen.insert(structural_ty) {
            return None;
        }
        // Drop the type-universe read guard before instantiating a named shape, which interns the
        // resulting types through the write side of the same lock.
        let data = structural_ty.data().clone();
        match data {
            TypeKind::Variant(cases) => return Some((structural_ty, cases)),
            TypeKind::Named(named) => {
                structural_ty = env
                    .type_def(named.def)
                    .instantiated_shape_with_effects(&named.params, &named.effect_params);
            }
            _ => return None,
        }
    }
}

/// Whether `ty` has a scalar ABI representation (`doc/abi.md`, "Scalar slots"): a value passed
/// and returned directly. MIR and the backends ask this one question so that caller and callee
/// always agree; type definition ids are global, so any environment that reaches the type's
/// definition gives the same answer. Unit has no scalar representation.
pub(crate) fn is_abi_scalar(ty: Type, env: &impl TypeLayoutEnv) -> bool {
    is_primitive_scalar(ty) || is_tag_scalar(ty, env)
}

/// The part of [`is_abi_scalar`] that needs no type definitions: `bool`, `int`, `float` and the
/// compiler-internal `raw_float`.
pub(crate) fn is_primitive_scalar(ty: Type) -> bool {
    [bool_type(), int_type(), float_type(), raw_float_type()].contains(&ty)
}

/// A closed variant whose complete representation is just its canonical u32 tag.
/// Unit payloads have no storage or ownership obligations; larger aggregates never become
/// scalars merely because their layout happens to fit in a machine register.
pub(crate) fn is_tag_scalar(ty: Type, env: &impl TypeLayoutEnv) -> bool {
    if !ty.is_constant() {
        return false;
    }
    // A named variant answers from its definition's shape, without instantiating it: a payload is
    // unit after substitution only if it is unit, or a parameter whose argument is unit. Any other
    // named type, such as a record, is no variant at all.
    let named = match &*ty.data() {
        TypeKind::Named(named) => Some((named.def, named.params.clone())),
        TypeKind::Variant(_) => None,
        _ => return false,
    };
    if let Some((def, params)) = named {
        match &*env.type_def(def).shape_ty().data() {
            TypeKind::Variant(cases) => {
                return !cases.is_empty()
                    && cases.iter().all(|(_, payload)| match &*payload.data() {
                        TypeKind::Variable(parameter) => {
                            params[parameter.name() as usize] == Type::unit()
                        }
                        _ => *payload == Type::unit(),
                    });
            }
            TypeKind::Variable(_) | TypeKind::Named(_) => {}
            _ => return false,
        }
    }
    structural_variant(ty, env).is_some_and(|(_, cases)| {
        !cases.is_empty() && cases.iter().all(|(_, payload)| *payload == Type::unit())
    })
}

/// Whether `ty` has no type variable outside callables. Substitution then cannot change its
/// representation, as every callable has one layout whatever its signature (`doc/abi.md`,
/// "First-class callables"). Effect variables are within callables, so they never count.
///
/// The walk follows what [`same_representation`] compares, which includes the arguments of named
/// and native types, so that a type closed here compares the same under every substitution.
pub(crate) fn representation_is_closed(ty: Type) -> bool {
    let mut seen = FxHashSet::default();
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        if ty.summary().free_ty_vars.is_empty() || !seen.insert(ty) {
            continue;
        }
        let data = ty.data();
        match &*data {
            TypeKind::Variable(_) => return false,
            TypeKind::Function(_) | TypeKind::Subscript(_) | TypeKind::Never => {}
            TypeKind::Tuple(fields) => pending.extend(fields.iter().copied()),
            TypeKind::Record(fields) | TypeKind::Variant(fields) => {
                pending.extend(fields.iter().map(|(_, field)| *field))
            }
            TypeKind::Named(named) => pending.extend(named.params.iter().copied()),
            TypeKind::Native(native) => pending.extend(native.arguments.iter().copied()),
        }
    }
    true
}

/// Where the payload of a variant case is stored, as far as the code at hand can tell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum VariantPayloadStorageDecision {
    /// No substitution can change the storage.
    Static(VariantPayloadStorage),
    /// A substitution may change the storage, so the code receives it as the evidence of this
    /// requirement, from where the type is known.
    Evidence(DictionaryReq),
}

/// Decide where the payload of the case `tag` of `variant_ty` is stored (`doc/abi.md`, "Tagged
/// unions"). The storage is fixed only when no substitution can change it: the payload is
/// indirect already, as substitution only adds paths back to the variant, or the variant has no
/// type variable outside callables. Otherwise it is evidence, whose requirement is in canonical
/// form, so that a function and its callers name it alike: the structural variant type with
/// effects erased, as effects never decide a representation, and the first of its cases with the
/// same payload, as the storage depends on the payload type and not on the case. The form is
/// chosen from the erased variant, so that deciding it again gives it back. A variant type that is
/// a variable keeps the case `tag` and the payload `payload_ty` that inference gave it.
pub(crate) fn variant_payload_storage_decision(
    variant_ty: Type,
    tag: Ustr,
    payload_ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Result<VariantPayloadStorageDecision, InternalCompilationError> {
    use VariantPayloadStorageDecision::*;
    let erase = |ty: Type| ty.map(&mut EffectErasingMapper);
    if variant_ty.data().is_variable() {
        if payload_ty == Type::unit() {
            return Ok(Static(VariantPayloadStorage::Inline));
        }
        return Ok(Evidence(DictionaryReq::new_variant_payload_indirection(
            variant_ty,
            tag,
            erase(payload_ty),
        )));
    }
    let (structural_ty, cases) = structural_variant(variant_ty, env).ok_or_else(|| {
        internal_compilation_error!(Internal {
            error: format!("cannot resolve variant representation for type {variant_ty:?}"),
            span,
        })
    })?;
    let payload_ty = cases
        .into_iter()
        .find_map(|(case_tag, payload_ty)| (case_tag == tag).then_some(payload_ty))
        .ok_or_else(|| {
            internal_compilation_error!(Internal {
                error: format!("variant type {variant_ty:?} has no case .{tag}"),
                span,
            })
        })?;
    if payload_ty == Type::unit() {
        return Ok(Static(VariantPayloadStorage::Inline));
    }
    let storage = payload_storage_in_variant(structural_ty, payload_ty, env);
    if storage.is_indirect() || representation_is_closed(structural_ty) {
        return Ok(Static(storage));
    }
    // Erasing effects changes no representation, hence not the decision either.
    let structural_ty = erase(structural_ty);
    let payload_ty = erase(payload_ty);
    let first_tag = structural_ty
        .data()
        .as_variant()
        .expect("erasing effects keeps a variant")
        .iter()
        .find_map(|(case_tag, case_payload_ty)| {
            (*case_payload_ty == payload_ty).then_some(*case_tag)
        })
        .expect("the case itself has this payload");
    Ok(Evidence(DictionaryReq::new_variant_payload_indirection(
        structural_ty,
        first_tag,
        payload_ty,
    )))
}

/// Normalize a storage obligation whose types are substituted already: `None` once no
/// substitution can change the storage, otherwise the obligation in the canonical form of
/// [`variant_payload_storage_decision`], with its origin and location.
pub(crate) fn normalize_variant_payload_storage(
    constraint: &PubTypeConstraint,
    env: &impl TypeLayoutEnv,
) -> Result<Option<PubTypeConstraint>, InternalCompilationError> {
    let PubTypeConstraint::VariantPayloadStorage {
        origin,
        variant_ty,
        tag,
        payload_ty,
        span,
    } = constraint
    else {
        unreachable!("only a storage obligation is normalized as such, not {constraint:?}")
    };
    Ok(
        match variant_payload_storage_decision(*variant_ty, *tag, *payload_ty, span.use_site, env)?
        {
            VariantPayloadStorageDecision::Static(_) => None,
            VariantPayloadStorageDecision::Evidence(DictionaryReq::VariantPayloadIndirection {
                variant_ty,
                tag,
                payload_ty,
            }) => Some(PubTypeConstraint::VariantPayloadStorage {
                origin: *origin,
                variant_ty,
                tag,
                payload_ty,
                span: span.clone(),
            }),
            VariantPayloadStorageDecision::Evidence(requirement) => {
                unreachable!("storage evidence has a storage requirement, not {requirement:?}")
            }
        },
    )
}

/// Return the storage mode shared by occurrences of `payload_ty` in `variant_ty`, when no
/// substitution can change it, as in [`variant_payload_storage_decision`].
///
/// Storage is a function of the structural variant and payload type, so the case tag does not
/// participate. `None` means that the storage may still change or that the variant does not
/// contain that payload type: the code reads it from the stored tag.
pub(crate) fn variant_payload_storage_for_payload_type(
    variant_ty: Type,
    payload_ty: Type,
    env: &impl TypeLayoutEnv,
) -> Option<VariantPayloadStorage> {
    let (structural_ty, cases) = structural_variant(variant_ty, env)?;
    if !cases.iter().any(|(_, candidate)| *candidate == payload_ty) {
        return None;
    }
    let storage = payload_storage_in_variant(structural_ty, payload_ty, env);
    (storage.is_indirect() || representation_is_closed(structural_ty)).then_some(storage)
}

/// Return one possibly indirect payload type for representation cleanup.
/// Open variants may become recursive after substituting their type arguments.
///
/// Every indirect case uses the same pointer-sized union slot, so one pointee type is sufficient
/// for typed address calculation and representation cleanup.
pub(crate) fn variant_indirect_payload_type(
    variant_ty: Type,
    env: &impl TypeLayoutEnv,
) -> Option<Type> {
    let (structural_ty, cases) = structural_variant(variant_ty, env)?;
    cases.into_iter().find_map(|(_, payload_ty)| {
        (payload_storage_in_variant(structural_ty, payload_ty, env).is_indirect()
            || (!representation_is_closed(structural_ty) && payload_ty != Type::unit()))
        .then_some(payload_ty)
    })
}

/// Return the canonical storage mode of `tag`'s payload in `variant_ty`.
///
/// This is also the value carried as hidden evidence when `variant_ty` is an open generic type.
pub(crate) fn variant_payload_storage_for_type(
    variant_ty: Type,
    tag: Ustr,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Result<VariantPayloadStorage, InternalCompilationError> {
    let (structural_ty, cases) = structural_variant(variant_ty, env).ok_or_else(|| {
        internal_compilation_error!(Internal {
            error: format!("cannot resolve variant representation for type {variant_ty:?}"),
            span,
        })
    })?;
    let payload_ty = cases
        .into_iter()
        .find_map(|(case_tag, payload_ty)| (case_tag == tag).then_some(payload_ty))
        .ok_or_else(|| {
            internal_compilation_error!(Internal {
                error: format!("variant type {variant_ty:?} has no case .{tag}"),
                span,
            })
        })?;
    if payload_ty == Type::unit() {
        return Ok(VariantPayloadStorage::Inline);
    }
    Ok(payload_storage_in_variant(structural_ty, payload_ty, env))
}

impl TypeLayoutEnv for ModuleEnv<'_> {
    fn current_module_id(&self) -> crate::module::ModuleId {
        self.current.module_id()
    }
}

impl TypeLayoutEnv for TraitSolver<'_> {
    fn current_module_id(&self) -> crate::module::ModuleId {
        self.current_type_items.module.id
    }
}

/// One layout query, which computes the layout of each named type whose layout is constant once.
///
/// A constant layout does not depend on where it is asked from, and costs nothing to copy. A
/// symbolic one can: a type met again while it is being walked gets a symbolic formula, so the
/// formula of a type on a cycle depends on where the cycle is entered.
#[derive(Default)]
struct LayoutWalk {
    /// The types being walked.
    active: FxHashSet<Type>,
    constants: FxHashMap<Type, ValueLayoutFormula>,
}

impl LayoutWalk {
    fn formula(
        &mut self,
        ty: Type,
        span: Location,
        env: &impl TypeLayoutEnv,
    ) -> Result<ValueLayoutFormula, InternalCompilationError> {
        if let Some(formula) = leaf_formula(ty, span) {
            return formula;
        }
        if let Some(formula) = self.constants.get(&ty) {
            return Ok(formula.clone());
        }
        if !self.active.insert(ty) {
            // Valid recursive representations encounter a variant payload before returning here,
            // and that payload contributes a pointer-sized constant instead. Keeping any remaining
            // cycle symbolic lets the type/module cycle diagnostics reject it at their proper
            // boundary.
            return Ok(ValueLayoutFormula::symbolic(ty));
        }
        // The types being walked are as many as the walk is deep. A type whose representation was
        // checked never reaches the limit; one first built when specializing can.
        if self.active.len() > REPRESENTATION_HEIGHT_LIMIT as usize {
            return Err(representation_height_exceeded(
                REPRESENTATION_HEIGHT_LIMIT as usize + 1,
                span,
            ));
        }
        let formula = self.uncached_formula(ty, span, env)?;
        self.active.remove(&ty);
        // A walk meets a type again through the named types that hold it, and the query's own
        // type not once it returns.
        if formula.is_constant() && !self.active.is_empty() && ty.data().is_named() {
            self.constants.insert(ty, formula.clone());
        }
        Ok(formula)
    }

    fn uncached_formula(
        &mut self,
        ty: Type,
        span: Location,
        env: &impl TypeLayoutEnv,
    ) -> Result<ValueLayoutFormula, InternalCompilationError> {
        let ty_data = ty.data();
        use TypeKind::*;
        match &*ty_data {
            Tuple(_) | Record(_) => {
                let member_tys = direct_product_member_types(&ty_data).expect("product members");
                drop(ty_data);
                let fields = member_tys
                    .into_iter()
                    .map(|member_ty| self.formula(member_ty, span, env))
                    .collect::<Result<Vec<_>, _>>()?;
                // Decreasing alignment removes interior padding. Tie-breakers affect offsets,
                // but total size is the aligned sum of member sizes for both product kinds.
                ValueLayoutFormula::product(fields, span)
            }
            Variant(variants) => {
                let payload_tys = variants.clone();
                drop(ty_data);
                let payloads = payload_tys
                    .into_iter()
                    .map(|(tag, payload_ty)| {
                        let pointer =
                            || ValueLayoutFormula::constant(ValueLayout::native::<usize>(), span);
                        use VariantPayloadStorageDecision::*;
                        match variant_payload_storage_decision(ty, tag, payload_ty, span, env)? {
                            Static(VariantPayloadStorage::Indirect) => pointer(),
                            Static(VariantPayloadStorage::Inline) => {
                                self.formula(payload_ty, span, env)
                            }
                            Evidence(storage) => {
                                let pointer = pointer()?;
                                let inline = self.formula(payload_ty, span, env)?;
                                Ok(ValueLayoutFormula {
                                    size: ValueLayoutExpr::payload_storage(
                                        storage.clone(),
                                        pointer.size,
                                        inline.size,
                                    ),
                                    align: ValueLayoutExpr::payload_storage(
                                        storage,
                                        pointer.align,
                                        inline.align,
                                    ),
                                })
                            }
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                ValueLayoutFormula::variant(payloads, span)
            }
            Named(named) => {
                let named = named.clone();
                drop(ty_data);
                let type_def = env.type_def(named.def);
                // A representation-open foreign type is an opaque layout leaf supplied by its
                // owner-provided Value dictionary. Effect variables confined to callable fields do
                // not make the representation open, so their fixed layout remains computable here.
                if !ty.is_trait_input_resolved()
                    && (type_def.has_custom_value_impl
                        || type_def
                            .attributes
                            .iter()
                            .any(|attribute| attribute.path.0 == ustr(NO_DERIVE_VALUE_ATTRIBUTE))
                        || (named.def.module != env.current_module_id()
                            && value_type_needs_layout_witness(ty)))
                {
                    return Ok(ValueLayoutFormula::symbolic(ty));
                }
                let shape_ty =
                    type_def.instantiated_shape_with_effects(&named.params, &named.effect_params);
                self.formula(shape_ty, span, env)
            }
            Native(_) | Function(_) | Subscript(_) | Never | Variable(_) => {
                unreachable!("a leaf's formula needs no walk")
            }
        }
    }
}

/// The formula of a type without members, which needs no walk, or `None` for other types.
fn leaf_formula(
    ty: Type,
    span: Location,
) -> Option<Result<ValueLayoutFormula, InternalCompilationError>> {
    use TypeKind::*;
    Some(match &*ty.data() {
        Native(native) => ValueLayoutFormula::constant(
            ValueLayout::new(native.bare_ty.value_size(), native.bare_ty.value_align()),
            span,
        ),
        Function(_) | Subscript(_) => ValueLayoutFormula::constant(ValueLayout::callable(), span),
        Never => ValueLayoutFormula::product([], span),
        Variable(_) => Ok(ValueLayoutFormula::symbolic(ty)),
        Tuple(_) | Record(_) | Variant(_) | Named(_) => return None,
    })
}

pub(crate) fn value_layout_formula_for_type(
    ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Result<ValueLayoutFormula, InternalCompilationError> {
    LayoutWalk::default().formula(ty, span, env)
}

/// Check that the representation of `ty` is within `REPRESENTATION_HEIGHT_LIMIT` and
/// `REPRESENTATION_SIZE_LIMIT`: the type limits do not bound it, as a named type is one level high
/// and one part whatever it stands for.
pub(crate) fn check_representation(
    ty: Type,
    span: Location,
    env: &impl TypeDefEnv,
) -> Result<(), InternalCompilationError> {
    let (height, size) = RepresentationMetrics::new(env).height_and_size(ty);
    check_representation_metrics(height, size, span)
}

/// Check the `height` and the `size` of a representation against their limits.
pub(crate) fn check_representation_metrics(
    height: u32,
    size: u32,
    span: Location,
) -> Result<(), InternalCompilationError> {
    if height > REPRESENTATION_HEIGHT_LIMIT {
        return Err(representation_height_exceeded(height as usize, span));
    }
    if size > REPRESENTATION_SIZE_LIMIT {
        return Err(internal_compilation_error!(CompilerLimitExceeded(
            CompilerLimit {
                kind: CompilerLimitKind::RepresentationSize,
                actual: size as usize,
                limit: REPRESENTATION_SIZE_LIMIT as usize,
                span,
            }
        )));
    }
    Ok(())
}

fn representation_height_exceeded(actual: usize, span: Location) -> InternalCompilationError {
    internal_compilation_error!(CompilerLimitExceeded(CompilerLimit {
        kind: CompilerLimitKind::RepresentationHeight,
        actual,
        limit: REPRESENTATION_HEIGHT_LIMIT as usize,
        span,
    }))
}

/// What layout expressions read: the `Value` of the types whose layouts they read, then their
/// payload storages, each once, in a stable order.
fn value_layout_requirements<'a>(
    exprs: impl IntoIterator<Item = &'a ValueLayoutExpr>,
    value_trait: TraitId,
) -> Vec<DictionaryReq> {
    let mut types = Vec::new();
    let mut storages = Vec::new();
    for expr in exprs {
        expr.collect_evidence(&mut types, &mut storages);
    }
    types
        .into_iter()
        .map(|ty| DictionaryReq::new_trait_impl(value_trait, vec![ty], vec![], vec![]))
        .chain(storages)
        .collect()
}

/// The constraint whose evidence is `requirement`, which is a `Value` or a payload storage.
fn requirement_constraint(requirement: &DictionaryReq, span: Location) -> PubTypeConstraint {
    match requirement {
        DictionaryReq::TraitImpl {
            trait_id,
            input_tys,
            output_tys,
            output_effs,
        } => PubTypeConstraint::new_have_trait(
            *trait_id,
            input_tys.clone(),
            output_tys.clone(),
            output_effs.clone(),
            span,
        ),
        DictionaryReq::VariantPayloadIndirection {
            variant_ty,
            tag,
            payload_ty,
        } => PubTypeConstraint::new_variant_payload_storage(*variant_ty, *tag, *payload_ty, span),
        DictionaryReq::ProjectionSubscript { .. } => {
            unreachable!("a layout reads no field: {requirement:?}")
        }
    }
}

/// What the getter of the layout constant `associated_const` of `ty` reads, in the order of its
/// constraints: see [`generated_value_layout_getter`].
pub(crate) fn value_layout_getter_requirements(
    ty: Type,
    associated_const: TraitAssociatedConstIndex,
    value_trait: TraitId,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Result<Vec<DictionaryReq>, InternalCompilationError> {
    Ok(value_layout_requirements(
        [&value_layout_formula_for_type(ty, span, env)?.associated_const(associated_const)],
        value_trait,
    ))
}

/// The payload storages that the generated `Value` dictionary of `ty` reads: those of every open
/// case of the variants it holds, down to the leaves of [`generated_value_evidence_types`], whose
/// own dictionaries read theirs. Its layout reads those it does not hide behind a pointer, but its
/// methods read them all: `clone` builds the cases and the dictionaries of their payloads. Each is
/// in the canonical form of [`variant_payload_storage_decision`].
pub(crate) fn generated_value_storage_requirements(
    ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Vec<DictionaryReq> {
    let walk = GeneratedValueStorageWalk::new(ty, env);
    let mut storages = Vec::new();
    let mut visited = vec![false; walk.children.len()];
    walk.collect(ty, span, env, &mut visited, &mut storages);
    storages
}

/// The types that [`generated_value_storage_requirements`] walks, each with the types it enters
/// and its strongly connected component. A payload in the component of its variant leads back to
/// it, so it is indirect, as [`representation_reaches`] would find: the walk needs no decision for
/// it, which would go around the component again.
struct GeneratedValueStorageWalk {
    /// The position of each open type that the walk enters, closed types fixing every storage
    /// within them.
    nodes: FxHashMap<Type, usize>,
    /// What the walk enters from each type: the fields of products, the payloads of variants, and
    /// the shape of a named type whose `Value` dictionary is generated here.
    children: Vec<Vec<Type>>,
    component: Vec<usize>,
}

impl GeneratedValueStorageWalk {
    fn new(root: Type, env: &impl TypeLayoutEnv) -> Self {
        let mut nodes = FxHashMap::default();
        let mut children = Vec::new();
        let mut pending = vec![root];
        while let Some(ty) = pending.pop() {
            if nodes.contains_key(&ty) || representation_is_closed(ty) {
                continue;
            }
            nodes.insert(ty, children.len());
            let data = ty.data().clone();
            let entered = match data {
                TypeKind::Tuple(fields) => fields,
                TypeKind::Record(fields) | TypeKind::Variant(fields) => {
                    fields.into_iter().map(|(_, field)| field).collect()
                }
                TypeKind::Named(named) if named_value_is_compiler_derived(named.def, env) => {
                    vec![
                        env.type_def(named.def)
                            .instantiated_shape_with_effects(&named.params, &named.effect_params),
                    ]
                }
                _ => Vec::new(),
            };
            pending.extend(entered.iter().copied());
            children.push(entered);
        }
        let graph: Vec<_> = children
            .iter()
            .map(|entered| {
                DepGraphNode(
                    entered
                        .iter()
                        .filter_map(|ty| nodes.get(ty).copied())
                        .collect(),
                )
            })
            .collect();
        let mut component = vec![0; children.len()];
        for (index, members) in find_strongly_connected_components(&graph)
            .into_iter()
            .enumerate()
        {
            for member in members {
                component[member] = index;
            }
        }
        Self {
            nodes,
            children,
            component,
        }
    }

    fn collect(
        &self,
        ty: Type,
        span: Location,
        env: &impl TypeLayoutEnv,
        visited: &mut [bool],
        storages: &mut Vec<DictionaryReq>,
    ) {
        let Some(&node) = self.nodes.get(&ty) else {
            return;
        };
        if mem::replace(&mut visited[node], true) {
            return;
        }
        let data = ty.data().clone();
        let TypeKind::Variant(cases) = data else {
            for &child in &self.children[node] {
                self.collect(child, span, env, visited, storages);
            }
            return;
        };
        for (tag, payload_ty) in cases {
            let recursive = self
                .nodes
                .get(&payload_ty)
                .is_some_and(|&payload| self.component[payload] == self.component[node]);
            if !recursive
                && let Ok(VariantPayloadStorageDecision::Evidence(storage)) =
                    variant_payload_storage_decision(ty, tag, payload_ty, span, env)
                && !storages.contains(&storage)
            {
                storages.push(storage);
            }
            self.collect(payload_ty, span, env, visited, storages);
        }
    }
}

/// Whether the `Value` dictionary of the named type `def` is generated here from its shape, as
/// [`generated_value_evidence_types`] walks through it, rather than a leaf of its own.
fn named_value_is_compiler_derived(def: TypeDefId, env: &impl TypeLayoutEnv) -> bool {
    let type_def = env.type_def(def);
    def.module == env.current_module_id()
        && !type_def.has_custom_value_impl
        && !type_def
            .attributes
            .iter()
            .any(|attribute| attribute.path.0 == ustr(NO_DERIVE_VALUE_ATTRIBUTE))
}

/// What the generated layout getters of `ty` read, its size or its alignment, as the constraints
/// that require it: see [`value_layout_requirements`].
pub(crate) fn value_layout_getters_constraints(
    ty: Type,
    value_trait: TraitId,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Result<Vec<PubTypeConstraint>, InternalCompilationError> {
    let formula = value_layout_formula_for_type(ty, span, env)?;
    Ok(
        value_layout_requirements([&formula.size, &formula.align], value_trait)
            .iter()
            .map(|requirement| requirement_constraint(requirement, span))
            .collect(),
    )
}

/// As [`generated_value_storage_requirements`], as the constraints that require them.
pub(crate) fn generated_value_storage_constraints(
    ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Vec<PubTypeConstraint> {
    generated_value_storage_requirements(ty, span, env)
        .iter()
        .map(|requirement| requirement_constraint(requirement, span))
        .collect()
}

/// Collects into `evidence` the `Value` evidence of `ty`, a part of `root`. Each type is walked
/// once, so it is evidence once: met again, on the walk's path or after its walk, it adds nothing,
/// but for the root, whose recursive occurrences are evidence too. So a recursive group whose
/// members reach each other along many paths costs its members, not its paths.
fn collect_generated_value_evidence_types(
    ty: Type,
    root: Type,
    env: &impl TypeLayoutEnv,
    visited: &mut FxHashSet<Type>,
    evidence: &mut Vec<Type>,
) {
    if ty.is_constant() || ty.is_function() || ty.is_subscript() {
        return;
    }
    if !visited.insert(ty) {
        if ty == root && !evidence.contains(&ty) {
            evidence.push(ty);
        }
        return;
    }

    let data = ty.data().clone();
    match data {
        TypeKind::Tuple(fields) => {
            for field in fields {
                collect_generated_value_evidence_types(field, root, env, visited, evidence);
            }
        }
        TypeKind::Record(fields) | TypeKind::Variant(fields) => {
            for (_, field) in fields {
                collect_generated_value_evidence_types(field, root, env, visited, evidence);
            }
        }
        TypeKind::Named(named) => {
            if named_value_is_compiler_derived(named.def, env) {
                let shape = env
                    .type_def(named.def)
                    .instantiated_shape_with_effects(&named.params, &named.effect_params);
                collect_generated_value_evidence_types(shape, root, env, visited, evidence);
            } else {
                evidence.push(ty);
            }
        }
        TypeKind::Variable(_) | TypeKind::Native(_) => evidence.push(ty),
        TypeKind::Function(_) | TypeKind::Subscript(_) | TypeKind::Never => {}
    }
}

/// Return the external `Value` evidence from which a compiler-derived dictionary can be built.
/// Recursive occurrences of the root are retained for entry mapping to `SelfDictionary`; they do
/// not become dictionary captures.
pub(crate) fn generated_value_evidence_types(
    ty: Type,
    env: &impl TypeLayoutEnv,
) -> Option<Vec<Type>> {
    let data = ty.data().clone();
    let root_is_derivable = match data {
        TypeKind::Tuple(_) | TypeKind::Record(_) | TypeKind::Variant(_) => true,
        TypeKind::Named(named) => {
            let type_def = env.type_def(named.def);
            named.def.module == env.current_module_id()
                && !type_def.has_custom_value_impl
                && !type_def
                    .attributes
                    .iter()
                    .any(|attribute| attribute.path.0 == ustr(NO_DERIVE_VALUE_ATTRIBUTE))
        }
        TypeKind::Function(_) | TypeKind::Subscript(_) => true,
        TypeKind::Variable(_) | TypeKind::Native(_) | TypeKind::Never => false,
    };
    if !root_is_derivable {
        return None;
    }
    let mut evidence = Vec::new();
    collect_generated_value_evidence_types(ty, ty, env, &mut FxHashSet::default(), &mut evidence);
    Some(evidence)
}

/// Return whether a complete `Value` dictionary for this application is synthesized by the
/// compiler from its external evidence leaves.
pub(crate) fn is_compiler_provided_value_trait_application(
    trait_id: TraitId,
    trait_def: &Trait,
    input_tys: &[Type],
    output_tys: &[Type],
    env: &impl TypeLayoutEnv,
) -> bool {
    is_value_trait(trait_id, trait_def)
        && input_tys.len() == 1
        && output_tys.is_empty()
        && generated_value_evidence_types(input_tys[0], env).is_some()
}

fn layout_for_value_type(
    ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Result<ValueLayout, InternalCompilationError> {
    value_layout_formula_for_type(ty, span, env)?.resolved(span)
}

pub(crate) fn value_layout_for_type(
    ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Result<ResolvedValueLayout, InternalCompilationError> {
    let layout = layout_for_value_type(ty, span, env)?;
    Ok(ResolvedValueLayout {
        size: u32::try_from(layout.size).expect("layout sizes are within VALUE_SIZE_LIMIT"),
        align: u32::try_from(layout.align).expect("layout alignments are within VALUE_SIZE_LIMIT"),
    })
}

pub(crate) fn value_layout_associated_const_values(
    ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Result<[isize; 2], InternalCompilationError> {
    layout_for_value_type(ty, span, env)?.associated_const_values(span)
}

/// Returns whether `ty` has a statically known run-time layout: its size and alignment can be
/// computed without consulting a `Value` dictionary witness.
///
/// A type is statically sized unless it reaches a bare type variable outside a function surface.
/// In particular a `Native` type such as `array<A>` (`[A]`) is statically sized even when generic:
/// its run-time representation is a fixed-layout struct (a header plus a heap `Buffer` pointer)
/// whose size is independent of its type arguments — exactly as `layout_for_value_type` treats a
/// `Native` as a fixed-size leaf. Only a value *of* a bare type variable — or an aggregate that
/// embeds one directly (e.g. `(A, int)`) — has a layout that depends on a run-time witness, the
/// sole case in which `layout_for_value_type` fails.
///
/// Storage of a statically sized type may be allocated with a plain `alloca` and moved with direct
/// `load`/`store`; everything else must go through its `Value` dictionary witness.
pub(crate) fn type_has_static_layout(ty: Type, span: Location, env: &impl TypeLayoutEnv) -> bool {
    layout_for_value_type(ty, span, env).is_ok()
}

/// Return the product members whose physical lowering requires run-time `Value` evidence.
///
/// The returned order is the logical tuple/record order. Named products are inspected through
/// their instantiated structural shape.
pub(crate) fn dynamic_product_member_layouts(
    ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Vec<Type> {
    product_layout_spec(ty, span, env)
        .map(|product| product.dynamic_member_layouts())
        .unwrap_or_default()
}

/// Direct structural members only; named-type resolution belongs to the caller.
fn direct_product_member_types(kind: &TypeKind) -> Option<Vec<Type>> {
    match kind {
        TypeKind::Tuple(members) => Some(members.clone()),
        TypeKind::Record(fields) => Some(fields.iter().map(|(_, ty)| *ty).collect()),
        _ => None,
    }
}

struct DirectProductMembers {
    members: Vec<(Option<Ustr>, Type)>,
}

fn product_members(ty: Type, env: &impl TypeLayoutEnv) -> Option<DirectProductMembers> {
    let mut structural = ty;
    let mut seen = FxHashSet::default();
    loop {
        if !seen.insert(structural) {
            return None;
        }
        let data = structural.data();
        let members = match &*data {
            TypeKind::Tuple(types) => Some(types.iter().map(|&ty| (None, ty)).collect()),
            TypeKind::Record(fields) => {
                Some(fields.iter().map(|&(name, ty)| (Some(name), ty)).collect())
            }
            _ => None,
        };
        if let Some(members) = members {
            return Some(DirectProductMembers { members });
        }
        let TypeKind::Named(named) = &*data else {
            return None;
        };
        let named = named.clone();
        // Release the type-store read guard before instantiating a named shape.
        drop(data);
        structural = env
            .type_def(named.def)
            .instantiated_shape_with_effects(&named.params, &named.effect_params);
    }
}

/// Inspect direct product members without recursively computing their layouts. Consumers can
/// bound representation expansion before asking for the full layout recipe.
pub(crate) fn product_member_types(ty: Type, env: &impl TypeLayoutEnv) -> Option<Vec<Type>> {
    Some(
        product_members(ty, env)?
            .members
            .into_iter()
            .map(|(_, ty)| ty)
            .collect(),
    )
}

/// Build the product layout recipe consumed by physical aggregate lowering.
pub(crate) fn product_layout_spec(
    ty: Type,
    span: Location,
    env: &impl TypeLayoutEnv,
) -> Option<ProductLayoutSpec> {
    let product = product_members(ty, env)?;
    let members = product
        .members
        .into_iter()
        .map(|(name, member_ty)| ProductMemberLayout {
            name,
            ty: member_ty,
            static_layout: value_layout_for_type(member_ty, span, env).ok(),
        })
        .collect();
    Some(ProductLayoutSpec { members })
}

/// Return whether all unresolved variables in `ty` appear only in function types.
/// `active` is the current recursion stack used to stop on recursive types.
fn value_type_is_resolved_ignoring_function_surface(
    ty: Type,
    active: &mut FxHashSet<Type>,
) -> bool {
    if ty.is_constant() {
        return true;
    }
    if !active.insert(ty) {
        return true;
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let resolved = match &*ty_data {
        Function(_) | Subscript(_) => true,
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            let resolved = member_tys.into_iter().all(|member_ty| {
                value_type_is_resolved_ignoring_function_surface(member_ty, active)
            });
            active.remove(&ty);
            return resolved;
        }
        Record(fields) => {
            let field_tys = fields
                .iter()
                .map(|(_, field_ty)| *field_ty)
                .collect::<Vec<_>>();
            drop(ty_data);
            let resolved = field_tys
                .into_iter()
                .all(|field_ty| value_type_is_resolved_ignoring_function_surface(field_ty, active));
            active.remove(&ty);
            return resolved;
        }
        Variant(variants) => {
            let payload_tys = variants
                .iter()
                .map(|(_, payload_ty)| *payload_ty)
                .collect::<Vec<_>>();
            drop(ty_data);
            let resolved = payload_tys.into_iter().all(|payload_ty| {
                value_type_is_resolved_ignoring_function_surface(payload_ty, active)
            });
            active.remove(&ty);
            return resolved;
        }
        Named(named) => {
            let param_tys = named.params.clone();
            drop(ty_data);
            let resolved = param_tys
                .into_iter()
                .all(|param_ty| value_type_is_resolved_ignoring_function_surface(param_ty, active));
            active.remove(&ty);
            return resolved;
        }
        Native(_) => false,
        Never => true,
        Variable(_) => false,
    };
    drop(ty_data);
    active.remove(&ty);
    resolved
}

/// Whether storage for `ty` can only be allocated with a run-time layout witness.
///
/// A type variable outside a function surface leaves the size unknown whatever the type
/// definitions say, so this answers the allocation question without a
/// [`TypeLayoutEnv`] — usable during inference, where the module's own definitions are not yet
/// resolvable. It is the necessary half of [`type_has_static_layout`]: a type this reports as
/// dynamically sized has no static layout, while a resolved type may still lack one for reasons
/// only the layout computation can see.
pub(crate) fn value_type_needs_layout_witness(ty: Type) -> bool {
    !value_type_is_resolved_ignoring_function_surface(ty, &mut FxHashSet::default())
}

/// True when every unresolved part of `ty` appears under a function type.
/// Function `Value` impls are compiler-provided from their hidden closure env,
/// so these types can use generated structural `Value` code without requiring a
/// user-visible dictionary for the function surface.
pub(crate) fn is_function_surface_only_value_type(ty: Type) -> bool {
    !ty.is_constant()
        && value_type_is_resolved_ignoring_function_surface(ty, &mut FxHashSet::default())
}

/// Return whether this is `Value` for a type whose unresolved variables occur only inside function types.
pub(crate) fn is_function_surface_only_value_trait_application(
    trait_id: TraitId,
    trait_def: &Trait,
    input_tys: &[Type],
    output_tys: &[Type],
) -> bool {
    is_value_trait(trait_id, trait_def)
        && input_tys.len() == 1
        && output_tys.is_empty()
        && is_function_surface_only_value_type(input_tys[0])
}

/// Return whether this trait application is `Value` for a function type.
pub(crate) fn is_value_trait_for_function_type(
    trait_id: TraitId,
    trait_def: &Trait,
    input_tys: &[Type],
    output_tys: &[Type],
) -> bool {
    is_value_trait(trait_id, trait_def)
        && input_tys.len() == 1
        && output_tys.is_empty()
        && input_tys[0].is_function()
}

pub(crate) fn is_value_trait(trait_id: TraitId, trait_def: &Trait) -> bool {
    trait_id.module == STD_MODULE_ID && trait_def.name == VALUE_TRAIT_NAME
}

use CallableDefinition as Def;

pub(crate) type ValueCodeEntries = Vec<(PendingFunctionBody, Vec<LocalDecl>)>;

struct ValueBodyCtx<'s, 'm> {
    solver: &'s mut TraitSolver<'m>,
    permits_open_types: bool,
}

fn is_trivial_copy(ctx: &ValueBodyCtx<'_, '_>, ty: Type) -> bool {
    ctx.solver.concrete_type_is_trivial_copy(ty)
}

impl<'s, 'm> ValueBodyCtx<'s, 'm> {
    fn concrete(solver: &'s mut TraitSolver<'m>) -> Self {
        Self {
            solver,
            permits_open_types: false,
        }
    }

    pub(crate) fn generic(solver: &'s mut TraitSolver<'m>) -> Self {
        Self {
            solver,
            permits_open_types: true,
        }
    }

    fn get_local_or_import_function(
        &mut self,
        span: Location,
        module_path: &module::Path,
        function_name: ustr::Ustr,
    ) -> Result<FunctionId, InternalCompilationError> {
        self.solver
            .get_local_or_import_function(span, module_path, function_name)
    }

    fn trait_method_call(
        &mut self,
        method: ValueMethod,
        span: Location,
        arena: &mut NodeArena,
        locals: &mut Vec<LocalDecl>,
        mut arguments: Vec<NodeId>,
    ) -> Result<NodeId, InternalCompilationError> {
        let ValueMethod {
            trait_id,
            input_ty,
            method_index,
        } = method;
        let (fn_ty, ret_ty, method_name, is_function_value) = {
            let trait_def = self.solver.trait_def(trait_id);
            let definition = trait_def
                .instantiate_for_tys(&[input_ty], &[], &[])
                .into_iter()
                .nth(method_index.as_index())
                .expect("Value method index out of bounds");
            let fn_ty = definition.ty_scheme.ty;
            let ret_ty = fn_ty.ret;
            let method_name = trait_def.method(method_index).0;
            let is_function_value =
                is_value_trait_for_function_type(trait_id, trait_def, &[input_ty], &[]);
            (fn_ty, ret_ty, method_name, is_function_value)
        };

        if is_function_value {
            let function = FunctionId::new(
                self.solver.current_type_items.module.id,
                function_value_method(self.solver, method_index, span)?,
            );
            let effects = fn_ty.effects.clone();
            let prepared = prepare_generated_call_arguments_with_locals(
                arena,
                locals,
                self.solver,
                &mut arguments,
                &fn_ty.args,
                span,
            )?;
            let call = arena.alloc(hir::Node::new(
                hir::hir_syn::static_apply_with_argument_passing(
                    function,
                    fn_ty,
                    arguments,
                    prepared.argument_passing,
                    span,
                ),
                ret_ty,
                effects,
                span,
            ));
            return Ok(wrap_generated_call_with_temp_cleanup(
                arena,
                prepared.temp_stores,
                prepared.cleanup,
                call,
                ret_ty,
                span,
            ));
        }

        let effects = fn_ty.effects.clone();
        let prepared = prepare_generated_call_arguments_with_locals(
            arena,
            locals,
            self.solver,
            &mut arguments,
            &fn_ty.args,
            span,
        )?;
        let arguments = CallArgument::from_values_and_passing(arguments, prepared.argument_passing);
        let call = arena.alloc(hir::Node::new(
            hir::NodeKind::TraitMethodApply(crate::containers::b(hir::TraitMethodApplication {
                trait_id,
                method_index,
                method_path: Path::single(method_name, span),
                method_span: span,
                arguments,
                arguments_unnamed: UnnamedArg::All,
                ty: CallImplType::value(fn_ty),
                input_tys: vec![input_ty],
                output_tys: Vec::new(),
                output_effs: Vec::new(),
                inst_data: hir::FnInstData::none(),
            })),
            ret_ty,
            effects,
            span,
        ));
        Ok(wrap_generated_call_with_temp_cleanup(
            arena,
            prepared.temp_stores,
            prepared.cleanup,
            call,
            ret_ty,
            span,
        ))
    }
}

#[derive(Clone, Copy)]
struct ValueMethod {
    trait_id: TraitId,
    input_ty: Type,
    method_index: TraitMethodIndex,
}

fn value_method_call_node(
    ctx: &mut ValueBodyCtx<'_, '_>,
    method: ValueMethod,
    span: Location,
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    arguments: Vec<NodeId>,
) -> Result<NodeId, InternalCompilationError> {
    ctx.trait_method_call(method, span, arena, locals, arguments)
}

fn named_trait_method_call_node(
    ctx: &mut ValueBodyCtx<'_, '_>,
    trait_name: &str,
    method_name: &str,
    arguments: Vec<NodeId>,
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    span: Location,
) -> Result<NodeId, InternalCompilationError> {
    let trait_id = ctx.solver.std_trait_id(trait_name);
    let method_index = ctx
        .solver
        .trait_def(trait_id)
        .method_index(ustr(method_name))
        .expect("compiler-known trait method exists");
    ctx.trait_method_call(
        ValueMethod {
            trait_id,
            input_ty: int_type(),
            method_index,
        },
        span,
        arena,
        locals,
        arguments,
    )
}

fn value_layout_expr_node(
    expr: &ValueLayoutExpr,
    ctx: &mut ValueBodyCtx<'_, '_>,
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    span: Location,
) -> Result<NodeId, InternalCompilationError> {
    let node = match expr {
        ValueLayoutExpr::Constant(value) => {
            alloc_synth_node(arena, hir::hir_syn::native(*value), int_type())
        }
        ValueLayoutExpr::AssociatedConst { ty, index } => {
            let value_trait = ctx.solver.std_trait_id(VALUE_TRAIT_NAME);
            let trait_def = ctx.solver.trait_def(value_trait);
            alloc_synth_node(
                arena,
                hir::NodeKind::GetTraitAssociatedConst(b(hir::GetTraitAssociatedConst {
                    trait_id: value_trait,
                    associated_const_index: *index,
                    associated_const_name: trait_def.associated_const(*index).name,
                    associated_const_span: span,
                    input_tys: vec![*ty],
                    output_tys: vec![],
                    output_effs: vec![],
                })),
                int_type(),
            )
        }
        ValueLayoutExpr::PayloadStorage {
            storage,
            indirect,
            inline,
        } => {
            let DictionaryReq::VariantPayloadIndirection {
                variant_ty,
                tag,
                payload_ty,
            } = storage
            else {
                unreachable!("a payload storage reads a storage requirement, not {storage:?}")
            };
            let is_indirect = alloc_synth_node(
                arena,
                hir::NodeKind::GetVariantPayloadStorage(hir::GetVariantPayloadStorage {
                    variant_ty: *variant_ty,
                    tag: *tag,
                    payload_ty: *payload_ty,
                }),
                bool_type(),
            );
            // Both layouts are computed before the choice, which then only reads one of them:
            // a branch that computed its layout would make the paths through nested choices
            // diverge in the storage they allocate.
            use hir::hir_syn::*;
            let indirect = value_layout_expr_node(indirect, ctx, arena, locals, span)?;
            let inline = value_layout_expr_node(inline, ctx, arena, locals, span)?;
            let local_slot = locals.len();
            let (store_indirect, indirect_id) = store_new_local(
                indirect,
                local_slot,
                "$layout_indirect",
                MutVal::constant(),
                int_type(),
                locals,
            );
            let store_indirect = alloc_synth_node(arena, store_indirect, Type::unit());
            let (store_inline, inline_id) = store_new_local(
                inline,
                local_slot + 1,
                "$layout_inline",
                MutVal::constant(),
                int_type(),
                locals,
            );
            let store_inline = alloc_synth_node(arena, store_inline, Type::unit());
            let take_indirect = alloc_synth_node(arena, load_local(indirect_id), int_type());
            let take_inline = alloc_synth_node(arena, load_local(inline_id), int_type());
            let chosen = alloc_synth_node(
                arena,
                case(
                    is_indirect,
                    vec![(LiteralValue::new_native(true), take_indirect)],
                    take_inline,
                ),
                int_type(),
            );
            alloc_synth_node(
                arena,
                block_with_cleanup(
                    [store_indirect, store_inline, chosen],
                    vec![indirect_id, inline_id],
                ),
                int_type(),
            )
        }
        ValueLayoutExpr::Add(left, right) => {
            let left = value_layout_expr_node(left, ctx, arena, locals, span)?;
            let right = value_layout_expr_node(right, ctx, arena, locals, span)?;
            named_trait_method_call_node(
                ctx,
                NUM_TRAIT_NAME,
                "add",
                vec![left, right],
                arena,
                locals,
                span,
            )?
        }
        ValueLayoutExpr::Max(left, right) => {
            use hir::hir_syn::*;

            let left = value_layout_expr_node(left, ctx, arena, locals, span)?;
            let right = value_layout_expr_node(right, ctx, arena, locals, span)?;
            let local_slot = locals.len();
            let (store_left, left_id) = store_new_local(
                left,
                local_slot,
                "$layout_left",
                MutVal::constant(),
                int_type(),
                locals,
            );
            let store_left = alloc_synth_node(arena, store_left, Type::unit());
            let (store_right, right_id) = store_new_local(
                right,
                local_slot + 1,
                "$layout_right",
                MutVal::constant(),
                int_type(),
                locals,
            );
            let store_right = alloc_synth_node(arena, store_right, Type::unit());
            let left = alloc_synth_node(arena, load_local(left_id), int_type());
            let right = alloc_synth_node(arena, load_local(right_id), int_type());
            let comparison = named_trait_method_call_node(
                ctx,
                ORD_TRAIT_NAME,
                "cmp",
                vec![left, right],
                arena,
                locals,
                span,
            )?;
            let take_left = alloc_synth_node(arena, load_local(left_id), int_type());
            let take_right = alloc_synth_node(arena, load_local(right_id), int_type());
            let maximum = alloc_synth_node(
                arena,
                case(
                    comparison,
                    vec![(
                        LiteralValue::new_variant_tag(ustr(ORDERING_GREATER)),
                        take_left,
                    )],
                    take_right,
                ),
                int_type(),
            );
            alloc_synth_node(
                arena,
                block_with_cleanup([store_left, store_right, maximum], vec![left_id, right_id]),
                int_type(),
            )
        }
        ValueLayoutExpr::AlignTo(offset, align) => {
            let offset = value_layout_expr_node(offset, ctx, arena, locals, span)?;
            let align = value_layout_expr_node(align, ctx, arena, locals, span)?;
            let one = alloc_synth_node(arena, hir::hir_syn::native(1_isize), int_type());
            let align_minus_one = named_trait_method_call_node(
                ctx,
                NUM_TRAIT_NAME,
                "sub",
                vec![align, one],
                arena,
                locals,
                span,
            )?;
            let sum = named_trait_method_call_node(
                ctx,
                NUM_TRAIT_NAME,
                "add",
                vec![offset, align_minus_one],
                arena,
                locals,
                span,
            )?;
            let neg_align = named_trait_method_call_node(
                ctx,
                NUM_TRAIT_NAME,
                "neg",
                vec![align],
                arena,
                locals,
                span,
            )?;
            named_trait_method_call_node(
                ctx,
                BITS_TRAIT_NAME,
                "bit_and",
                vec![sum, neg_align],
                arena,
                locals,
                span,
            )?
        }
    };
    Ok(node)
}

/// Build one executable `Value::SIZE` or `Value::ALIGN` getter for an open structural type.
///
/// The function's hidden constraints are exactly the associated-constant reads retained by the
/// canonical layout expression. Dictionary construction can therefore close the getter over the
/// same evidence without giving associated constants a second runtime representation.
pub(crate) fn generated_value_layout_getter(
    input_ty: Type,
    associated_const: TraitAssociatedConstIndex,
    span: Location,
    solver: &mut TraitSolver<'_>,
) -> Result<PendingModuleFunction, InternalCompilationError> {
    let expression =
        value_layout_formula_for_type(input_ty, span, solver)?.associated_const(associated_const);
    let value_trait = solver.std_trait_id(VALUE_TRAIT_NAME);
    let constraints = value_layout_requirements([&expression], value_trait)
        .iter()
        .map(|requirement| requirement_constraint(requirement, span))
        .collect::<Vec<_>>();
    let definition = CallableDefinition::new_infer_quantifiers_with_constraints(
        FnType::new_by_val([], int_type(), EffType::empty()),
        constraints,
        [],
        "Compiler-generated Value layout getter.",
    );
    let mut arena = NodeArena::default();
    let mut locals = Vec::new();
    let mut ctx = ValueBodyCtx::generic(solver);
    let root = value_layout_expr_node(&expression, &mut ctx, &mut arena, &mut locals, span)?;
    Ok(PendingModuleFunction::new(
        definition,
        PendingScriptFunction::new(arena, root, 0),
        None,
        locals,
    ))
}

const FUNCTION_VALUE_METHOD_NAMES: [&str; 6] = [
    "$_ferlium_function_value_eq",
    "$_ferlium_function_value_to_string",
    "$_ferlium_function_value_hash",
    "$_ferlium_function_value_clone",
    "$_ferlium_function_value_drop",
    "$_ferlium_function_value_ne",
];

pub(crate) fn function_value_method_name(method_index: TraitMethodIndex) -> ustr::Ustr {
    ustr::Ustr::from(FUNCTION_VALUE_METHOD_NAMES[usize::from(method_index)])
}

#[derive(Clone, Copy)]
enum TextPiece {
    Static(NodeId),
    String(NodeId),
}

fn alloc_synth_node(arena: &mut NodeArena, kind: hir::NodeKind, ty: Type) -> NodeId {
    arena.alloc(hir::Node::new(
        kind,
        ty,
        EffType::empty(),
        Location::new_synthesized(),
    ))
}

fn static_str_node(arena: &mut NodeArena, value: &str, span: Location) -> NodeId {
    arena.alloc(hir::Node::new(
        hir::hir_syn::static_str(value),
        static_str_type(),
        EffType::empty(),
        span,
    ))
}

pub(crate) fn variant_payload_storage_type(payload_ty: Type) -> Type {
    if payload_ty == Type::unit() {
        return payload_ty;
    }
    let payload_data = payload_ty.data();
    let stores_payload_directly =
        matches!(&*payload_data, TypeKind::Tuple(_) | TypeKind::Record(_));
    drop(payload_data);
    if stores_payload_directly {
        payload_ty
    } else {
        tuple_type([payload_ty])
    }
}

fn variant_payload_project(
    arena: &mut NodeArena,
    variant_value: NodeId,
    payload_ty: Type,
) -> NodeId {
    let storage_ty = variant_payload_storage_type(payload_ty);
    let storage = alloc_synth_node(
        arena,
        hir::NodeKind::Project(hir::Project::variant_payload(variant_value)),
        storage_ty,
    );
    if storage_ty == payload_ty {
        storage
    } else {
        alloc_synth_node(
            arena,
            hir::hir_syn::project(storage, ProjectionIndex::from_index(0)),
            payload_ty,
        )
    }
}

fn variant_payload_storage_node(
    arena: &mut NodeArena,
    payload: NodeId,
    payload_ty: Type,
) -> NodeId {
    let storage_ty = variant_payload_storage_type(payload_ty);
    if storage_ty == payload_ty {
        payload
    } else {
        alloc_synth_node(arena, hir::hir_syn::tuple([payload]), storage_ty)
    }
}

fn function_value_clone_root(ty: Type, source_id: LocalDeclId, arena: &mut NodeArena) -> NodeId {
    use hir::hir_syn::*;

    let source = alloc_synth_node(arena, load_local(source_id), ty);
    alloc_synth_node(
        arena,
        hir::NodeKind::CloneClosureEnv(hir::CloneClosureEnv { source }),
        ty,
    )
}

fn function_value_clone_body(ty: Type, arena: &mut NodeArena) -> (NodeId, Vec<LocalDecl>) {
    use hir::hir_syn::*;

    let source_id = LocalDeclId::from_index(0);
    let locals = vec![local("source", ty)];
    let root = function_value_clone_root(ty, source_id, arena);
    (root, locals)
}

fn function_value_drop_root(ty: Type, target_id: LocalDeclId, arena: &mut NodeArena) -> NodeId {
    use hir::hir_syn::*;

    let target = alloc_synth_node(arena, load_local(target_id), ty);
    alloc_synth_node(
        arena,
        hir::NodeKind::DropClosureEnv(hir::DropClosureEnv { target }),
        Type::unit(),
    )
}

fn function_value_drop_body(ty: Type, arena: &mut NodeArena) -> (NodeId, Vec<LocalDecl>) {
    let target_id = LocalDeclId::from_index(0);
    let locals = vec![LocalDecl::new(
        (crate::ustr("target"), Location::new_synthesized()),
        MutType::mutable(),
        ty,
        None,
        Location::new_synthesized(),
    )];
    let root = function_value_drop_root(ty, target_id, arena);
    (root, locals)
}

fn subscript_value_clone_root(ty: Type, source_id: LocalDeclId, arena: &mut NodeArena) -> NodeId {
    use hir::hir_syn::*;

    let source = alloc_synth_node(arena, load_local(source_id), ty);
    alloc_synth_node(
        arena,
        hir::NodeKind::CloneSubscriptValue(hir::CloneSubscriptValue { source }),
        ty,
    )
}

fn subscript_value_drop_root(ty: Type, target_id: LocalDeclId, arena: &mut NodeArena) -> NodeId {
    use hir::hir_syn::*;

    let target = alloc_synth_node(arena, load_local(target_id), ty);
    alloc_synth_node(
        arena,
        hir::NodeKind::DropSubscriptValue(hir::DropSubscriptValue { target }),
        Type::unit(),
    )
}

pub(crate) fn function_value_method_function(
    method_index: TraitMethodIndex,
    span: Location,
    solver: &mut TraitSolver<'_>,
) -> Result<PendingModuleFunction, InternalCompilationError> {
    use hir::hir_syn::*;

    let mut arena = NodeArena::default();
    let ty = Type::variable_id(0);
    let unit_ty = Type::unit();
    let (definition, root, locals) = match method_index {
        VALUE_EQ_METHOD_INDEX | VALUE_NE_METHOD_INDEX => {
            let fn_ty = FnType::new_by_val([ty, ty], bool_type(), EffType::empty());
            let definition = Def::new_infer_quantifiers(
                fn_ty,
                ["left", "right"],
                "Compiler-generated function Value equality.",
            );
            let locals = vec![local("left", ty), local("right", ty)];
            // Function equality is always false, so its default inequality specializes to true.
            let root = alloc_synth_node(
                &mut arena,
                native(method_index == VALUE_NE_METHOD_INDEX),
                bool_type(),
            );
            (definition, root, locals)
        }
        VALUE_TO_STRING_METHOD_INDEX => {
            let fn_ty = FnType::new_by_val([ty], string_type(), EffType::empty());
            let definition = Def::new_infer_quantifiers(
                fn_ty,
                ["self"],
                "Compiler-generated function Value string conversion.",
            );
            let mut locals = vec![local("self", ty)];
            let root =
                materialize_static_string(&mut arena, &mut locals, solver, "<function>", span)?;
            (definition, root, locals)
        }
        VALUE_HASH_METHOD_INDEX => {
            let hasher_ty = hasher_type();
            let hasher_write_static_str = solver.get_local_or_import_function(
                span,
                &module::Path::single_str("std"),
                crate::ustr("hasher_write_static_str"),
            )?;
            let fn_ty = FnType::new(
                vec![
                    FnArgType::new_by_val(ty),
                    FnArgType::new(hasher_ty, MutType::mutable()),
                ],
                unit_ty,
                EffType::empty(),
            );
            let definition = Def::new_infer_quantifiers(
                fn_ty,
                ["self", "state"],
                "Compiler-generated function Value hashing.",
            );
            let state_id = LocalDeclId::from_index(1);
            let mut locals = vec![
                local("self", ty),
                LocalDecl::new(
                    (crate::ustr("state"), Location::new_synthesized()),
                    MutType::mutable(),
                    hasher_ty,
                    None,
                    Location::new_synthesized(),
                ),
            ];
            let state = alloc_synth_node(&mut arena, load_local(state_id), hasher_ty);
            let marker = static_str_node(&mut arena, "<function>", span);
            let write = static_apply_generated_with_locals(
                &mut arena,
                &mut locals,
                solver,
                hasher_write_static_str,
                [state, marker],
                FnType::new(
                    vec![
                        FnArgType::new(hasher_ty, MutType::mutable()),
                        FnArgType::new_by_val(static_str_type()),
                    ],
                    unit_ty,
                    EffType::empty(),
                ),
                span,
            )?;
            let unit = alloc_synth_node(&mut arena, native(()), unit_ty);
            let root = alloc_synth_node(&mut arena, block([write, unit]), unit_ty);
            (definition, root, locals)
        }
        VALUE_CLONE_METHOD_INDEX => {
            let fn_ty = FnType::new_by_val([ty], ty, EffType::empty());
            let definition = Def::new_infer_quantifiers(
                fn_ty,
                ["source"],
                "Compiler-generated function Value clone.",
            );
            let (root, locals) = function_value_clone_body(ty, &mut arena);
            (definition, root, locals)
        }
        VALUE_DROP_METHOD_INDEX => {
            let fn_ty = FnType::new(
                vec![FnArgType::new(ty, MutType::mutable())],
                unit_ty,
                EffType::empty(),
            );
            let definition = Def::new_infer_quantifiers(
                fn_ty,
                ["target"],
                "Compiler-generated function Value drop.",
            );
            let (root, locals) = function_value_drop_body(ty, &mut arena);
            (definition, root, locals)
        }
        _ => panic!("function Value method index out of bounds"),
    };

    let runtime_arg_count = definition.arg_names.len();
    Ok(PendingModuleFunction::new(
        definition,
        PendingScriptFunction::new(arena, root, runtime_arg_count),
        None,
        locals,
    ))
}

fn derive_structural_text_body(
    trait_id: TraitId,
    method_index: TraitMethodIndex,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

    assert!(input_types.len() == 1);
    let ty = input_types[0];
    assert!(ctx.permits_open_types || ty.is_constant());

    let n = alloc_synth_node;

    let string_push_str = ctx.get_local_or_import_function(
        span,
        &module::Path::single_str("std"),
        crate::ustr("string_push_str"),
    )?;
    let string_push_static_str = ctx.get_local_or_import_function(
        span,
        &module::Path::single_str("std"),
        crate::ustr("string_push_static_str"),
    )?;

    macro_rules! string_lit {
        ($arena:expr, $locals:expr, $text:expr) => {
            materialize_static_string($arena, $locals, ctx.solver, $text, span)?
        };
    }
    macro_rules! static_piece {
        ($arena:expr, $text:expr) => {
            TextPiece::Static(static_str_node($arena, $text, span))
        };
    }
    macro_rules! build_text {
        ($arena:expr, $locals:expr, $value:expr, $value_ty:expr) => {
            TextPiece::String(value_method_call_node(
                ctx,
                ValueMethod {
                    trait_id,
                    input_ty: $value_ty,
                    method_index,
                },
                span,
                $arena,
                $locals,
                vec![$value],
            )?)
        };
    }
    let build_string_block = |arena: &mut NodeArena,
                              solver: &mut TraitSolver<'_>,
                              locals: &mut Vec<LocalDecl>,
                              initial: &str,
                              mut pieces: Vec<TextPiece>|
     -> Result<NodeId, InternalCompilationError> {
        let initial_value = materialize_static_string(arena, locals, solver, initial, span)?;
        let next_local = locals.len();
        let (store_rendered, l_rendered_id) = store_new_local(
            initial_value,
            next_local,
            "rendered",
            MutVal::mutable(),
            string_type(),
            locals,
        );
        let mut statements = Vec::with_capacity(pieces.len() + 2);
        statements.push(n(arena, store_rendered, Type::unit()));
        for piece in pieces.drain(..) {
            let target = n(arena, load_local(l_rendered_id), string_type());
            let push = match piece {
                TextPiece::Static(piece) => static_apply_generated_with_locals(
                    arena,
                    locals,
                    solver,
                    string_push_static_str,
                    [target, piece],
                    FnType::new(
                        vec![
                            FnArgType::new(string_type(), MutType::mutable()),
                            FnArgType::new_by_val(static_str_type()),
                        ],
                        Type::unit(),
                        EffType::empty(),
                    ),
                    span,
                )?,
                TextPiece::String(piece) => static_apply_generated_with_locals(
                    arena,
                    locals,
                    solver,
                    string_push_str,
                    [target, piece],
                    FnType::new(
                        vec![
                            FnArgType::new(string_type(), MutType::mutable()),
                            FnArgType::new_by_val(string_type()),
                        ],
                        Type::unit(),
                        EffType::empty(),
                    ),
                    span,
                )?,
            };
            statements.push(push);
        }
        let rendered = n(arena, take_local_value(l_rendered_id), string_type());
        statements.push(rendered);
        Ok(n(arena, block(statements), string_type()))
    };

    let locals = vec![local("self", ty)];
    let l_self_id = LocalDeclId::from_index(0);

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            let load_self = n(arena, load_local(l_self_id), ty);
            let mut locals = locals;
            let mut pieces = Vec::with_capacity(member_tys.len() * 2 + 1);
            for (index, member_ty) in member_tys.into_iter().enumerate() {
                if index > 0 {
                    pieces.push(static_piece!(arena, ", "));
                }
                let member = n(
                    arena,
                    project(load_self, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                pieces.push(build_text!(arena, &mut locals, member, member_ty));
            }
            pieces.push(static_piece!(arena, ")"));
            Some((
                build_string_block(arena, ctx.solver, &mut locals, "(", pieces)?,
                locals,
            ))
        }
        Record(fields) => {
            let fields = fields.clone();
            drop(ty_data);
            let load_self = n(arena, load_local(l_self_id), ty);
            let mut locals = locals;
            let mut pieces = Vec::with_capacity(fields.len() * 4 + 1);
            for (index, (name, member_ty)) in fields.into_iter().enumerate() {
                if index > 0 {
                    pieces.push(static_piece!(arena, ", "));
                }
                pieces.push(static_piece!(arena, name.as_str()));
                pieces.push(static_piece!(arena, ": "));
                let member = n(
                    arena,
                    project(load_self, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                pieces.push(build_text!(arena, &mut locals, member, member_ty));
            }
            pieces.push(static_piece!(arena, " }"));
            Some((
                build_string_block(arena, ctx.solver, &mut locals, "{ ", pieces)?,
                locals,
            ))
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            let self_value = n(arena, load_local(l_self_id), ty);
            let mut locals = locals;
            let mut alternatives = Vec::with_capacity(variants.len());
            for (tag, payload_ty) in variants {
                let tag_val = LiteralValue::new_variant_tag(tag);
                let rendered = if payload_ty == Type::unit() {
                    string_lit!(arena, &mut locals, tag.as_str())
                } else {
                    let self_value = n(arena, load_local(l_self_id), ty);
                    let payload = variant_payload_project(arena, self_value, payload_ty);
                    let payload_str = build_text!(arena, &mut locals, payload, payload_ty);
                    if payload_ty.data().is_tuple() {
                        build_string_block(
                            arena,
                            ctx.solver,
                            &mut locals,
                            &format!("{} ", tag),
                            vec![payload_str],
                        )?
                    } else {
                        let close = static_piece!(arena, ")");
                        build_string_block(
                            arena,
                            ctx.solver,
                            &mut locals,
                            &format!("{}(", tag),
                            vec![payload_str, close],
                        )?
                    }
                };
                alternatives.push((tag_val, rendered));
            }
            let default = string_lit!(arena, &mut locals, "");
            Some((
                n(
                    arena,
                    case(self_value, alternatives, default),
                    string_type(),
                ),
                locals,
            ))
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let type_def = ctx.solver.type_def(named.def);
            let type_name = type_def.name;
            let shape_ty =
                type_def.instantiated_shape_with_effects(&named.params, &named.effect_params);
            let load_self = n(arena, load_local(l_self_id), ty);
            let mut locals = locals;
            let shape_data = shape_ty.data();
            let root = match &*shape_data {
                Tuple(member_tys) => {
                    let member_tys = member_tys.clone();
                    drop(shape_data);
                    let mut pieces = Vec::with_capacity(member_tys.len() * 2 + 1);
                    for (index, member_ty) in member_tys.into_iter().enumerate() {
                        if index > 0 {
                            pieces.push(static_piece!(arena, ", "));
                        }
                        let member = n(
                            arena,
                            project(load_self, ProjectionIndex::from_index(index)),
                            member_ty,
                        );
                        pieces.push(build_text!(arena, &mut locals, member, member_ty));
                    }
                    pieces.push(static_piece!(arena, ")"));
                    build_string_block(
                        arena,
                        ctx.solver,
                        &mut locals,
                        &format!("{} (", type_name),
                        pieces,
                    )?
                }
                Record(fields) => {
                    let fields = fields.clone();
                    drop(shape_data);
                    let mut pieces = Vec::with_capacity(fields.len() * 4 + 1);
                    for (index, (name, member_ty)) in fields.into_iter().enumerate() {
                        if index > 0 {
                            pieces.push(static_piece!(arena, ", "));
                        }
                        pieces.push(static_piece!(arena, name.as_str()));
                        pieces.push(static_piece!(arena, ": "));
                        let member = n(
                            arena,
                            project(load_self, ProjectionIndex::from_index(index)),
                            member_ty,
                        );
                        pieces.push(build_text!(arena, &mut locals, member, member_ty));
                    }
                    pieces.push(static_piece!(arena, " }"));
                    build_string_block(
                        arena,
                        ctx.solver,
                        &mut locals,
                        &format!("{} {{ ", type_name),
                        pieces,
                    )?
                }
                Variant(variants) => {
                    let variants = variants.clone();
                    drop(shape_data);
                    let mut alternatives = Vec::with_capacity(variants.len());
                    for (tag, payload_ty) in variants {
                        let tag_val = LiteralValue::new_variant_tag(tag);
                        let rendered = if payload_ty == Type::unit() {
                            string_lit!(arena, &mut locals, &format!("{}::{}", type_name, tag))
                        } else {
                            let self_value = n(arena, load_local(l_self_id), ty);
                            let payload = variant_payload_project(arena, self_value, payload_ty);
                            let payload_str = build_text!(arena, &mut locals, payload, payload_ty);
                            if payload_ty.data().is_tuple() {
                                build_string_block(
                                    arena,
                                    ctx.solver,
                                    &mut locals,
                                    &format!("{}::{} ", type_name, tag),
                                    vec![payload_str],
                                )?
                            } else {
                                let close = static_piece!(arena, ")");
                                build_string_block(
                                    arena,
                                    ctx.solver,
                                    &mut locals,
                                    &format!("{}::{}(", type_name, tag),
                                    vec![payload_str, close],
                                )?
                            }
                        };
                        alternatives.push((tag_val, rendered));
                    }
                    let default = string_lit!(arena, &mut locals, "");
                    n(arena, case(load_self, alternatives, default), string_type())
                }
                Never => {
                    drop(shape_data);
                    string_lit!(arena, &mut locals, &format!("{}::<empty>", type_name))
                }
                _ => {
                    drop(shape_data);
                    let load_self = n(arena, load_local(l_self_id), shape_ty);
                    let payload_str = build_text!(arena, &mut locals, load_self, shape_ty);
                    build_string_block(
                        arena,
                        ctx.solver,
                        &mut locals,
                        &format!("{} ", type_name),
                        vec![payload_str],
                    )?
                }
            };
            Some((root, locals))
        }
        Function(_) => {
            drop(ty_data);
            let mut locals = locals;
            let root = string_lit!(arena, &mut locals, "<function>");
            Some((root, locals))
        }
        Subscript(_) => {
            drop(ty_data);
            let mut locals = locals;
            let root = string_lit!(arena, &mut locals, "<subscript>");
            Some((root, locals))
        }
        _ => {
            drop(ty_data);
            None
        }
    };

    Ok(root)
}

fn derive_value_to_string_body(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    derive_structural_text_body(
        trait_id,
        VALUE_TO_STRING_METHOD_INDEX,
        input_types,
        span,
        arena,
        ctx,
    )
}

fn derive_inspect_body(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    derive_structural_text_body(
        trait_id,
        INSPECT_METHOD_INDEX,
        input_types,
        span,
        arena,
        ctx,
    )
}

#[derive(Debug, Clone)]
struct InspectDeriver;

impl Deriver for InspectDeriver {
    fn derived_members(&self, ty: Type, solver: &TraitSolver) -> Vec<Type> {
        structural_members(ty, solver)
    }

    fn requirements(
        &self,
        _trait_id: TraitId,
        input_types: &[Type],
        _solver: &TraitSolver,
    ) -> Option<DerivedRequirements> {
        // As for `Value`, the members' dictionaries are found once the body is compiled.
        has_structural_derivation(input_types[0]).then(DerivedRequirements::none)
    }

    fn derive_impl(
        &self,
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        _arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        assert!(ty.is_constant());

        let snapshot = solver.snapshot_derived_impl_state();
        let impl_id =
            solver.reserve_concrete_impl_from_code_entries(trait_id, input_types, &[], &[], []);
        let mut body_arena = NodeArena::default();
        let mut ctx = ValueBodyCtx::concrete(solver);
        let Some((root, locals)) =
            derive_inspect_body(trait_id, input_types, span, &mut body_arena, &mut ctx)?
        else {
            ctx.solver.rollback_derived_impl_state(snapshot);
            return Ok(None);
        };
        ctx.solver.replace_concrete_impl_code_entries(
            impl_id,
            trait_id,
            input_types,
            &[],
            &[],
            &[],
            [(PendingFunctionBody::new(body_arena, root), locals)],
        );
        Ok(Some(TraitImplId::new(
            ctx.solver.current_type_items.module.id,
            impl_id,
        )))
    }
}

fn derive_value_eq_body(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

    assert!(input_types.len() == 1);
    let ty = input_types[0];
    assert!(ctx.permits_open_types || ty.is_constant());

    let n = alloc_synth_node;

    let bool_ty = bool_type();
    let mut locals = vec![local("left", ty), local("right", ty)];
    let l_left_id = LocalDeclId::from_index(0);
    let l_right_id = LocalDeclId::from_index(1);

    macro_rules! build_product_eq {
        ($arena:expr, $member_tys:expr) => {{
            let mut eq_pairs: Vec<NodeId> = Vec::new();
            for (index, member_ty) in $member_tys.into_iter().enumerate() {
                let load_left_i = n($arena, load_local(l_left_id), ty);
                let left_i = n(
                    $arena,
                    project(load_left_i, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                let load_right_i = n($arena, load_local(l_right_id), ty);
                let right_i = n(
                    $arena,
                    project(load_right_i, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                let eq_i = value_method_call_node(
                    ctx,
                    ValueMethod {
                        trait_id,
                        input_ty: member_ty,
                        method_index: VALUE_EQ_METHOD_INDEX,
                    },
                    span,
                    $arena,
                    &mut locals,
                    vec![left_i, right_i],
                )?;
                eq_pairs.push(eq_i);
            }
            let mut root = n($arena, native(true), bool_ty);
            for eq_i in eq_pairs.into_iter().rev() {
                let false_n = n($arena, native(false), bool_ty);
                root = n(
                    $arena,
                    case(eq_i, vec![(LiteralValue::new_native(true), root)], false_n),
                    bool_ty,
                );
            }
            root
        }};
    }
    macro_rules! build_variant_eq {
        ($arena:expr, $variants:expr) => {{
            let mut alternatives: Vec<(LiteralValue, NodeId)> = Vec::new();
            for (tag, payload_ty) in $variants {
                let tag_val = LiteralValue::new_variant_tag(tag);
                let load_right_outer = n($arena, load_local(l_right_id), ty);
                let inner_body = if payload_ty == Type::unit() {
                    n($arena, native(true), bool_ty)
                } else {
                    let load_left_v = n($arena, load_local(l_left_id), ty);
                    let left_payload = variant_payload_project($arena, load_left_v, payload_ty);
                    let load_right_v = n($arena, load_local(l_right_id), ty);
                    let right_payload = variant_payload_project($arena, load_right_v, payload_ty);
                    value_method_call_node(
                        ctx,
                        ValueMethod {
                            trait_id,
                            input_ty: payload_ty,
                            method_index: VALUE_EQ_METHOD_INDEX,
                        },
                        span,
                        $arena,
                        &mut locals,
                        vec![left_payload, right_payload],
                    )?
                };
                let false_imm = n($arena, native(false), bool_ty);
                let inner_case = n(
                    $arena,
                    case(
                        load_right_outer,
                        vec![(tag_val.clone(), inner_body)],
                        false_imm,
                    ),
                    bool_ty,
                );
                alternatives.push((tag_val, inner_case));
            }
            let load_left_outer = n($arena, load_local(l_left_id), ty);
            let false_default = n($arena, native(false), bool_ty);
            n(
                $arena,
                case(load_left_outer, alternatives, false_default),
                bool_ty,
            )
        }};
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            Some(build_product_eq!(arena, member_tys))
        }
        Record(fields) => {
            let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
            drop(ty_data);
            Some(build_product_eq!(arena, member_tys))
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            Some(build_variant_eq!(arena, variants))
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = ctx
                .solver
                .type_def(named.def)
                .instantiated_shape_with_effects(&named.params, &named.effect_params);
            let shape_data = shape_ty.data();
            match &*shape_data {
                Tuple(member_tys) => {
                    let member_tys = member_tys.clone();
                    drop(shape_data);
                    Some(build_product_eq!(arena, member_tys))
                }
                Record(fields) => {
                    let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
                    drop(shape_data);
                    Some(build_product_eq!(arena, member_tys))
                }
                Variant(variants) => {
                    let variants = variants.clone();
                    drop(shape_data);
                    Some(build_variant_eq!(arena, variants))
                }
                Never => {
                    drop(shape_data);
                    Some(n(arena, native(true), bool_ty))
                }
                _ => {
                    drop(shape_data);
                    let load_left = n(arena, load_local(l_left_id), shape_ty);
                    let load_right = n(arena, load_local(l_right_id), shape_ty);
                    Some(value_method_call_node(
                        ctx,
                        ValueMethod {
                            trait_id,
                            input_ty: shape_ty,
                            method_index: VALUE_EQ_METHOD_INDEX,
                        },
                        span,
                        arena,
                        &mut locals,
                        vec![load_left, load_right],
                    )?)
                }
            }
        }
        Function(_) => {
            drop(ty_data);
            Some(n(arena, native(false), bool_ty))
        }
        Subscript(_) => {
            drop(ty_data);
            Some(n(arena, native(false), bool_ty))
        }
        _ => {
            drop(ty_data);
            None
        }
    };

    Ok(root.map(|root| (root, locals)))
}

fn derive_value_hash_body(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

    assert!(input_types.len() == 1);
    let ty = input_types[0];
    assert!(ctx.permits_open_types || ty.is_constant());

    let n = alloc_synth_node;

    let unit_ty = Type::unit();
    let hasher_ty = hasher_type();
    let hasher_write_static_str = ctx.get_local_or_import_function(
        span,
        &module::Path::single_str("std"),
        crate::ustr("hasher_write_static_str"),
    )?;

    let mut locals = vec![
        local("self", ty),
        LocalDecl::new(
            (crate::ustr("state"), Location::new_synthesized()),
            MutType::mutable(),
            hasher_ty,
            None,
            Location::new_synthesized(),
        ),
    ];
    let l_self_id = LocalDeclId::from_index(0);
    let l_state_id = LocalDeclId::from_index(1);

    let build_write_static_str = |arena: &mut NodeArena,
                                  solver: &mut TraitSolver<'_>,
                                  locals: &mut Vec<LocalDecl>,
                                  value: &str|
     -> Result<NodeId, InternalCompilationError> {
        let state = n(arena, load_local(l_state_id), hasher_ty);
        let value = static_str_node(arena, value, span);
        static_apply_generated_with_locals(
            arena,
            locals,
            solver,
            hasher_write_static_str,
            [state, value],
            FnType::new(
                vec![
                    FnArgType::new(hasher_ty, MutType::mutable()),
                    FnArgType::new_by_val(static_str_type()),
                ],
                unit_ty,
                EffType::empty(),
            ),
            span,
        )
    };
    macro_rules! build_hash_value {
        ($arena:expr, $value:expr, $value_ty:expr) => {{
            let state = n($arena, load_local(l_state_id), hasher_ty);
            value_method_call_node(
                ctx,
                ValueMethod {
                    trait_id,
                    input_ty: $value_ty,
                    method_index: VALUE_HASH_METHOD_INDEX,
                },
                span,
                $arena,
                &mut locals,
                vec![$value, state],
            )
        }};
    }

    macro_rules! build_product_hash {
        ($arena:expr, $member_tys:expr) => {{
            let load_self = n($arena, load_local(l_self_id), ty);
            let mut statements = Vec::with_capacity($member_tys.len() + 1);
            for (index, member_ty) in $member_tys.into_iter().enumerate() {
                let member = n(
                    $arena,
                    project(load_self, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                statements.push(build_hash_value!($arena, member, member_ty)?);
            }
            statements.push(n($arena, native(()), unit_ty));
            n($arena, block(statements), unit_ty)
        }};
    }

    macro_rules! build_variant_hash {
        ($arena:expr, $variants:expr) => {{
            let self_value = n($arena, load_local(l_self_id), ty);
            let mut alternatives = Vec::with_capacity($variants.len());

            for (tag, payload_ty) in $variants.into_iter() {
                let tag_val = LiteralValue::new_variant_tag(tag);
                let mut statements = vec![build_write_static_str(
                    $arena,
                    ctx.solver,
                    &mut locals,
                    tag.as_str(),
                )?];
                if payload_ty != Type::unit() {
                    let self_value = n($arena, load_local(l_self_id), ty);
                    let payload = variant_payload_project($arena, self_value, payload_ty);
                    statements.push(build_hash_value!($arena, payload, payload_ty)?);
                }
                statements.push(n($arena, native(()), unit_ty));
                let branch = n($arena, block(statements), unit_ty);
                alternatives.push((tag_val, branch));
            }

            let default = n($arena, native(()), unit_ty);
            n($arena, case(self_value, alternatives, default), unit_ty)
        }};
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            Some((build_product_hash!(arena, member_tys), locals))
        }
        Record(fields) => {
            let fields = fields.clone();
            drop(ty_data);
            let member_tys: Vec<Type> = fields.into_iter().map(|(_, ty)| ty).collect();
            Some((build_product_hash!(arena, member_tys), locals))
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            Some((build_variant_hash!(arena, variants), locals))
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = ctx
                .solver
                .type_def(named.def)
                .instantiated_shape_with_effects(&named.params, &named.effect_params);
            let shape_data = shape_ty.data();
            match &*shape_data {
                Tuple(member_tys) => {
                    let member_tys = member_tys.clone();
                    drop(shape_data);
                    Some((build_product_hash!(arena, member_tys), locals))
                }
                Record(fields) => {
                    let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
                    drop(shape_data);
                    Some((build_product_hash!(arena, member_tys), locals))
                }
                Variant(variants) => {
                    let variants = variants.clone();
                    drop(shape_data);
                    Some((build_variant_hash!(arena, variants), locals))
                }
                Never => {
                    drop(shape_data);
                    Some((n(arena, native(()), unit_ty), locals))
                }
                _ => {
                    drop(shape_data);
                    let load_self = n(arena, load_local(l_self_id), shape_ty);
                    Some((build_hash_value!(arena, load_self, shape_ty)?, locals))
                }
            }
        }
        Function(_) => {
            drop(ty_data);
            let statements = vec![
                build_write_static_str(arena, ctx.solver, &mut locals, "<function>")?,
                n(arena, native(()), unit_ty),
            ];
            Some((n(arena, block(statements), unit_ty), locals))
        }
        Subscript(_) => {
            drop(ty_data);
            let statements = vec![
                build_write_static_str(arena, ctx.solver, &mut locals, "<subscript>")?,
                n(arena, native(()), unit_ty),
            ];
            Some((n(arena, block(statements), unit_ty), locals))
        }
        _ => {
            drop(ty_data);
            None
        }
    };

    Ok(root)
}

fn derive_value_clone_body(
    trait_id: TraitId,
    input_types: &[Type],
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<Option<(NodeId, Vec<LocalDecl>)>, InternalCompilationError> {
    use hir::hir_syn::*;

    assert!(input_types.len() == 1);
    let ty = input_types[0];
    assert!(ctx.permits_open_types || ty.is_constant());

    let n = alloc_synth_node;

    let source_id = LocalDeclId::from_index(0);
    let mut locals = vec![local("source", ty)];
    let build_assign_whole = |arena: &mut NodeArena| n(arena, load_local(source_id), ty);

    // A generated structural `Value` impl has no custom ownership behaviour of its own. If its
    // complete concrete representation is `TrivialCopy`, cloning the representation is therefore
    // the complete implementation. Besides being cheaper than walking the shape, this keeps a
    // zero-sized payload such as the `((),)` of `Some(())` from turning into ordinary calls to the
    // native unit clone which MIR's ownership simplification cannot recognize as a `clone`.
    if is_trivial_copy(ctx, ty) {
        return Ok(Some((build_assign_whole(arena), locals)));
    }

    macro_rules! build_product_clone {
        ($arena:expr, $member_tys:expr) => {{
            let member_tys = $member_tys;
            let mut cloned_members = Vec::with_capacity(member_tys.len());
            for (index, &member_ty) in member_tys.iter().enumerate() {
                let source = n($arena, load_local(source_id), ty);
                let source_member = n(
                    $arena,
                    project(source, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                let member_is_trivial = is_trivial_copy(ctx, member_ty);
                cloned_members.push(if member_is_trivial {
                    source_member
                } else {
                    value_method_call_node(
                        ctx,
                        ValueMethod {
                            trait_id,
                            input_ty: member_ty,
                            method_index: VALUE_CLONE_METHOD_INDEX,
                        },
                        Location::new_synthesized(),
                        $arena,
                        &mut locals,
                        vec![source_member],
                    )?
                });
            }
            n($arena, tuple(cloned_members), ty)
        }};
    }
    macro_rules! build_variant_clone {
        ($arena:expr, $variants:expr) => {{
            let source = n($arena, load_local(source_id), ty);
            let mut alternatives = Vec::with_capacity($variants.len());
            for (tag, payload_ty) in $variants {
                let tag_val = LiteralValue::new_variant_tag(tag);
                let branch = if payload_ty == Type::unit() {
                    let payload = n($arena, native(()), Type::unit());
                    n($arena, variant(tag, payload), ty)
                } else {
                    let source = n($arena, load_local(source_id), ty);
                    let source_payload = variant_payload_project($arena, source, payload_ty);
                    let payload_is_trivial = is_trivial_copy(ctx, payload_ty);
                    let cloned_payload = if payload_is_trivial {
                        source_payload
                    } else {
                        value_method_call_node(
                            ctx,
                            ValueMethod {
                                trait_id,
                                input_ty: payload_ty,
                                method_index: VALUE_CLONE_METHOD_INDEX,
                            },
                            Location::new_synthesized(),
                            $arena,
                            &mut locals,
                            vec![source_payload],
                        )?
                    };
                    let payload = variant_payload_storage_node($arena, cloned_payload, payload_ty);
                    n($arena, variant(tag, payload), ty)
                };
                alternatives.push((tag_val, branch));
            }
            let default = n($arena, hir::NodeKind::Uninit, ty);
            n($arena, case(source, alternatives, default), ty)
        }};
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            build_product_clone!(arena, member_tys)
        }
        Record(fields) => {
            let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
            drop(ty_data);
            build_product_clone!(arena, member_tys)
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            build_variant_clone!(arena, variants)
        }
        Function(_) => {
            drop(ty_data);
            function_value_clone_root(ty, source_id, arena)
        }
        Subscript(_) => {
            drop(ty_data);
            subscript_value_clone_root(ty, source_id, arena)
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = ctx
                .solver
                .type_def(named.def)
                .instantiated_shape_with_effects(&named.params, &named.effect_params);
            let shape_data = shape_ty.data();
            match &*shape_data {
                Tuple(member_tys) => {
                    let member_tys = member_tys.clone();
                    drop(shape_data);
                    build_product_clone!(arena, member_tys)
                }
                Record(fields) => {
                    let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
                    drop(shape_data);
                    build_product_clone!(arena, member_tys)
                }
                Variant(variants) => {
                    let variants = variants.clone();
                    drop(shape_data);
                    build_variant_clone!(arena, variants)
                }
                Never => {
                    drop(shape_data);
                    n(arena, hir::NodeKind::Uninit, ty)
                }
                _ => {
                    drop(shape_data);
                    if shape_ty == Type::unit() {
                        // A concrete generated named type with this empty representation already
                        // returned through the `TrivialCopy` fast path. Here the named type can be
                        // generic, so construct its unit representation rather than copying the
                        // named value whole: the verifier cannot prove a generic named type
                        // representation-copyable, and such a `memcpy` would be invalid MIR.
                        n(arena, native(()), Type::unit())
                    } else {
                        build_assign_whole(arena)
                    }
                }
            }
        }
        _ => {
            drop(ty_data);
            build_assign_whole(arena)
        }
    };

    Ok(Some((root, locals)))
}

fn derive_value_drop_body(
    _trait_id: TraitId,
    input_types: &[Type],
    arena: &mut NodeArena,
    ctx: &mut ValueBodyCtx<'_, '_>,
) -> Result<(NodeId, Vec<LocalDecl>), InternalCompilationError> {
    use hir::hir_syn::*;

    assert!(input_types.len() == 1);
    let ty = input_types[0];
    assert!(ctx.permits_open_types || ty.is_constant());

    let n = alloc_synth_node;
    let target_id = LocalDeclId::from_index(0);
    let locals = vec![LocalDecl::new(
        (crate::ustr("target"), Location::new_synthesized()),
        MutType::mutable(),
        ty,
        None,
        Location::new_synthesized(),
    )];
    let build_unit = |arena: &mut NodeArena| n(arena, native(()), Type::unit());
    let build_drop = |arena: &mut NodeArena, target| {
        n(
            arena,
            hir::NodeKind::DropValue(hir::DropValue {
                target,
                drop: PendingLocalDrop::Unknown,
            }),
            Type::unit(),
        )
    };

    // Match ordinary ownership elaboration: a concrete `TrivialCopy` value has no semantic drop,
    // even when its structural shape contains fields for which a native `Value::drop` function
    // exists. Zero size alone is deliberately not enough here; a zero-sized named type with a
    // custom `Value` impl must still run that impl.
    if is_trivial_copy(ctx, ty) {
        return Ok((build_unit(arena), locals));
    }

    macro_rules! build_product_drop {
        ($arena:expr, $member_tys:expr) => {{
            let mut statements = Vec::with_capacity($member_tys.len() + 1);
            for (index, member_ty) in $member_tys.into_iter().enumerate() {
                if is_trivial_copy(ctx, member_ty) {
                    continue;
                }
                let target = n($arena, load_local(target_id), ty);
                let target_member = n(
                    $arena,
                    project(target, ProjectionIndex::from_index(index)),
                    member_ty,
                );
                statements.push(build_drop($arena, target_member));
            }
            statements.push(n($arena, native(()), Type::unit()));
            n($arena, block(statements), Type::unit())
        }};
    }
    macro_rules! build_variant_drop {
        ($arena:expr, $variants:expr) => {{
            let target = n($arena, load_local(target_id), ty);
            let mut alternatives = Vec::with_capacity($variants.len());
            for (tag, payload_ty) in $variants {
                let tag_val = LiteralValue::new_variant_tag(tag);
                let payload_is_trivial = is_trivial_copy(ctx, payload_ty);
                let branch = if payload_is_trivial {
                    n($arena, native(()), Type::unit())
                } else {
                    let target = n($arena, load_local(target_id), ty);
                    let target_payload = variant_payload_project($arena, target, payload_ty);
                    build_drop($arena, target_payload)
                };
                alternatives.push((tag_val, branch));
            }
            let default = n($arena, native(()), Type::unit());
            n($arena, case(target, alternatives, default), Type::unit())
        }};
    }

    let ty_data = ty.data();
    use TypeKind::*;
    let root = match &*ty_data {
        Tuple(member_tys) => {
            let member_tys = member_tys.clone();
            drop(ty_data);
            build_product_drop!(arena, member_tys)
        }
        Record(fields) => {
            let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
            drop(ty_data);
            build_product_drop!(arena, member_tys)
        }
        Variant(variants) => {
            let variants = variants.clone();
            drop(ty_data);
            build_variant_drop!(arena, variants)
        }
        Function(_) => {
            drop(ty_data);
            function_value_drop_root(ty, target_id, arena)
        }
        Subscript(_) => {
            drop(ty_data);
            subscript_value_drop_root(ty, target_id, arena)
        }
        Named(named) => {
            let named = named.clone();
            drop(ty_data);
            let shape_ty = ctx
                .solver
                .type_def(named.def)
                .instantiated_shape_with_effects(&named.params, &named.effect_params);
            let shape_data = shape_ty.data();
            match &*shape_data {
                Tuple(member_tys) => {
                    let member_tys = member_tys.clone();
                    drop(shape_data);
                    build_product_drop!(arena, member_tys)
                }
                Record(fields) => {
                    let member_tys: Vec<Type> = fields.iter().map(|(_, ty)| *ty).collect();
                    drop(shape_data);
                    build_product_drop!(arena, member_tys)
                }
                Variant(variants) => {
                    let variants = variants.clone();
                    drop(shape_data);
                    build_variant_drop!(arena, variants)
                }
                Never => {
                    drop(shape_data);
                    build_unit(arena)
                }
                _ => {
                    drop(shape_data);
                    build_unit(arena)
                }
            }
        }
        _ => {
            drop(ty_data);
            build_unit(arena)
        }
    };
    Ok((root, locals))
}

fn derive_function_value_impl(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    solver: &mut TraitSolver<'_>,
) -> Result<TraitImplId, InternalCompilationError> {
    let associated_const_values: Vec<LiteralValue> =
        value_layout_associated_const_values(input_types[0], span, solver)?
            .into_iter()
            .map(LiteralValue::new_native)
            .collect();
    let (method_count, definitions) = {
        let trait_def = solver.trait_def(trait_id);
        (
            trait_def.methods.len(),
            trait_def.instantiate_for_tys(input_types, &[], &[]),
        )
    };
    let methods = (0..method_count)
        .map(TraitMethodIndex::from_index)
        .map(|method_index| function_value_method(solver, method_index, span))
        .collect::<Result<Vec<_>, _>>()?;
    let tys = definitions
        .into_iter()
        .map(|definition| Type::function_type(definition.ty_scheme.ty))
        .collect::<Vec<_>>();
    let associated_const_tys = solver
        .trait_def(trait_id)
        .instantiate_associated_const_tys_for_tys(input_types, &[], &[]);
    let associated_const_names =
        solver.impl_associated_const_names(trait_id, input_types, &[], &[], 0, 0, &[]);
    let associated_const_getters = TraitImpls::bundle_pending_trivial_associated_const_getters(
        &associated_const_values,
        &associated_const_tys,
        &mut solver.fn_collector,
        |index| associated_const_names[index],
    );
    let dictionary_ty = TraitImpls::dictionary_ty(tys, associated_const_tys);
    let dictionary_value = module::build_dictionary_value(&methods, &associated_const_getters);
    let imp = TraitImpl::new(
        trait_id,
        input_types.to_vec(),
        Vec::new(),
        Vec::new(),
        methods,
        dictionary_value,
        dictionary_ty,
        false,
        None,
    )
    .with_associated_const_values(associated_const_values)
    .with_associated_const_getters(associated_const_getters);
    let key = ConcreteTraitImplKey::new(trait_id, input_types.to_vec());
    let impl_id = solver.impls.add_concrete_struct(key, imp);
    Ok(TraitImplId::new(
        solver.current_type_items.module.id,
        impl_id,
    ))
}

/// Whether the structural derivations of `Value` and `Inspect` cover the kind of `ty`.
fn has_structural_derivation(ty: Type) -> bool {
    ty.is_constant()
        && matches!(
            &*ty.data(),
            TypeKind::Tuple(_)
                | TypeKind::Record(_)
                | TypeKind::Variant(_)
                | TypeKind::Function(_)
                | TypeKind::Subscript(_)
                | TypeKind::Named(_)
        )
}

/// Whether `Value` is derived for `ty`.
fn derives_value(ty: Type, solver: &TraitSolver) -> bool {
    if let Some(named) = ty.data().as_named() {
        // A type with a custom `Value` impl has no other one, even where that impl does not apply.
        let type_def = solver.type_def(named.def);
        if type_def.has_custom_value_impl
            || type_def
                .attributes
                .iter()
                .any(|attribute| attribute.path.0 == ustr(NO_DERIVE_VALUE_ATTRIBUTE))
        {
            return false;
        }
    }
    has_structural_derivation(ty)
}

fn derive_structural_value_impl(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    _arena: &mut NodeArena,
    solver: &mut TraitSolver,
) -> Result<Option<TraitImplId>, InternalCompilationError> {
    if !derives_value(input_types[0], solver) {
        return Ok(None);
    }

    if input_types[0].is_function() {
        return Ok(Some(derive_function_value_impl(
            trait_id,
            input_types,
            span,
            solver,
        )?));
    }

    let associated_const_values: Vec<LiteralValue> =
        value_layout_associated_const_values(input_types[0], span, solver)?
            .into_iter()
            .map(LiteralValue::new_native)
            .collect();
    let snapshot = solver.snapshot_derived_impl_state();
    let impl_id = solver.reserve_concrete_impl_from_code_entries(
        trait_id,
        input_types,
        &[],
        &[],
        associated_const_values,
    );
    let mut ctx = ValueBodyCtx::concrete(solver);

    let mut eq_arena = NodeArena::default();
    let Some((eq_root, eq_locals)) =
        (match derive_value_eq_body(trait_id, input_types, span, &mut eq_arena, &mut ctx) {
            Ok(value) => value,
            Err(err) => {
                ctx.solver.rollback_derived_impl_state(snapshot);
                return Err(err);
            }
        })
    else {
        ctx.solver.rollback_derived_impl_state(snapshot);
        return Ok(None);
    };
    let eq = (PendingFunctionBody::new(eq_arena, eq_root), eq_locals);

    let mut to_string_arena = NodeArena::default();
    let Some((to_string_root, to_string_locals)) = (match derive_value_to_string_body(
        trait_id,
        input_types,
        span,
        &mut to_string_arena,
        &mut ctx,
    ) {
        Ok(value) => value,
        Err(err) => {
            ctx.solver.rollback_derived_impl_state(snapshot);
            return Err(err);
        }
    }) else {
        ctx.solver.rollback_derived_impl_state(snapshot);
        return Ok(None);
    };
    let to_string = (
        PendingFunctionBody::new(to_string_arena, to_string_root),
        to_string_locals,
    );

    let mut hash_arena = NodeArena::default();
    let Some((hash_root, hash_locals)) =
        (match derive_value_hash_body(trait_id, input_types, span, &mut hash_arena, &mut ctx) {
            Ok(value) => value,
            Err(err) => {
                ctx.solver.rollback_derived_impl_state(snapshot);
                return Err(err);
            }
        })
    else {
        ctx.solver.rollback_derived_impl_state(snapshot);
        return Ok(None);
    };
    let hash = (PendingFunctionBody::new(hash_arena, hash_root), hash_locals);

    let mut clone_arena = NodeArena::default();
    let Some((clone_root, clone_locals)) =
        derive_value_clone_body(trait_id, input_types, &mut clone_arena, &mut ctx)?
    else {
        ctx.solver.rollback_derived_impl_state(snapshot);
        return Ok(None);
    };
    let clone = (
        PendingFunctionBody::new(clone_arena, clone_root),
        clone_locals,
    );

    let mut drop_arena = NodeArena::default();
    let (drop_root, drop_locals) =
        derive_value_drop_body(trait_id, input_types, &mut drop_arena, &mut ctx)?;
    let drop = (PendingFunctionBody::new(drop_arena, drop_root), drop_locals);

    ctx.solver.replace_concrete_impl_code_entries(
        impl_id,
        trait_id,
        input_types,
        &[],
        &[],
        &[],
        [eq, to_string, hash, clone, drop],
    );
    Ok(Some(TraitImplId::new(
        solver.current_type_items.module.id,
        impl_id,
    )))
}

pub(crate) fn derive_generic_value_code_entries(
    trait_id: TraitId,
    input_types: &[Type],
    span: Location,
    _arena: &mut NodeArena,
    solver: &mut TraitSolver,
) -> Result<Option<ValueCodeEntries>, InternalCompilationError> {
    let mut ctx = ValueBodyCtx::generic(solver);

    let mut eq_arena = NodeArena::default();
    let Some((eq_root, eq_locals)) =
        derive_value_eq_body(trait_id, input_types, span, &mut eq_arena, &mut ctx)?
    else {
        return Ok(None);
    };
    let eq = (PendingFunctionBody::new(eq_arena, eq_root), eq_locals);

    let mut to_string_arena = NodeArena::default();
    let Some((to_string_root, to_string_locals)) =
        derive_value_to_string_body(trait_id, input_types, span, &mut to_string_arena, &mut ctx)?
    else {
        return Ok(None);
    };
    let to_string = (
        PendingFunctionBody::new(to_string_arena, to_string_root),
        to_string_locals,
    );

    let mut hash_arena = NodeArena::default();
    let Some((hash_root, hash_locals)) =
        derive_value_hash_body(trait_id, input_types, span, &mut hash_arena, &mut ctx)?
    else {
        return Ok(None);
    };
    let hash = (PendingFunctionBody::new(hash_arena, hash_root), hash_locals);

    let mut clone_arena = NodeArena::default();
    let Some((clone_root, clone_locals)) =
        derive_value_clone_body(trait_id, input_types, &mut clone_arena, &mut ctx)?
    else {
        return Ok(None);
    };
    let clone = (
        PendingFunctionBody::new(clone_arena, clone_root),
        clone_locals,
    );

    let mut drop_arena = NodeArena::default();
    let (drop_root, drop_locals) =
        derive_value_drop_body(trait_id, input_types, &mut drop_arena, &mut ctx)?;
    let drop = (PendingFunctionBody::new(drop_arena, drop_root), drop_locals);

    Ok(Some(vec![eq, to_string, hash, clone, drop]))
}

/// A deriver for the `Value` trait that auto-derives the full impl for algebraic types.
#[derive(Debug, Clone)]
struct ValueDeriver;

impl Deriver for ValueDeriver {
    fn derived_members(&self, ty: Type, solver: &TraitSolver) -> Vec<Type> {
        structural_members(ty, solver)
    }

    fn requirements(
        &self,
        _trait_id: TraitId,
        input_types: &[Type],
        solver: &TraitSolver,
    ) -> Option<DerivedRequirements> {
        // The methods call those of the members, whose dictionaries are found once the impl's
        // body is compiled.
        derives_value(input_types[0], solver).then(DerivedRequirements::none)
    }

    fn derive_impl(
        &self,
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        arena: &mut NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        assert!(input_types.len() == 1);
        let ty = input_types[0];
        if !ty.is_constant() {
            return Ok(None);
        }

        derive_structural_value_impl(trait_id, input_types, span, arena, solver)
    }
}

pub fn value_trait() -> Trait {
    let var_ty = Type::variable_id(0);
    let binary_fn_ty = FnType::new_by_val([var_ty, var_ty], bool_type(), EffType::empty());
    let unary_to_string_ty = FnType::new_by_val([var_ty], string_type(), EffType::empty());
    let binary_hash_ty = FnType::new(
        vec![
            FnArgType::new_by_val(var_ty),
            FnArgType::new(hasher_type(), MutType::mutable()),
        ],
        Type::unit(),
        EffType::empty(),
    );
    let clone_ty = FnType::new_by_val([var_ty], var_ty, EffType::empty());
    let drop_ty = FnType::new(
        vec![FnArgType::new(var_ty, MutType::mutable())],
        Type::unit(),
        EffType::empty(),
    );
    Trait::new_with_self_input_type(
        "Value",
        "A type supporting equality, string conversion, hashing, ownership, and layout. `clone` must return an independent, observationally equivalent value, while `drop` may only end ownership; therefore `clone(x); drop(x)` is equivalent to moving `x`.",
        [],
        [
            (
                "eq",
                Def::new_infer_quantifiers(
                    binary_fn_ty.clone(),
                    ["left", "right"],
                    "Returns whether `left` equals `right`.",
                ),
            ),
            (
                "to_string",
                Def::new_infer_quantifiers(
                    unary_to_string_ty,
                    ["value"],
                    "Returns the string representation of `value`.",
                ),
            ),
            (
                "hash",
                Def::new_infer_quantifiers(
                    binary_hash_ty,
                    ["value", "state"],
                    "Writes the hash of `value` into `state`.",
                ),
            ),
            (
                "clone",
                Def::new_infer_quantifiers(
                    clone_ty,
                    ["source"],
                    "Compiler-owned method that returns an independent, observationally equivalent owned clone of `source`.",
                ),
            ),
            (
                "drop",
                Def::new_infer_quantifiers(
                    drop_ty,
                    ["target"],
                    "Compiler-owned method that ends `target`'s ownership in place without an observable language-level effect.",
                ),
            ),
            (
                "ne",
                Def::new_infer_quantifiers(
                    binary_fn_ty,
                    ["left", "right"],
                    "Returns whether `left` differs from `right`. Defaults to `not eq(left, right)`.",
                ),
            ),
        ],
    )
    .with_associated_consts([
        TraitAssociatedConst::new("SIZE", Type::primitive::<isize>(), "Size in bytes."),
        TraitAssociatedConst::new("ALIGN", Type::primitive::<isize>(), "Alignment in bytes."),
    ])
    .with_deriver(ValueDeriver)
}

pub fn inspect_trait() -> Trait {
    let var_ty = Type::variable_id(0);
    let inspect_ty = FnType::new_by_val(
        [var_ty],
        string_type(),
        EffType::single_primitive(PrimitiveEffect::Fallible),
    );
    Trait::new_with_self_input_type(
        INSPECT_TRAIT_NAME,
        "A type that can render values for interactive inspection and debugging.",
        [],
        [(
            "inspect",
            CallableDefinition::new_infer_quantifiers(
                inspect_ty,
                ["value"],
                "Returns an inspection representation of `value`.",
            ),
        )],
    )
    .with_deriver(InspectDeriver)
}

pub fn add_to_module(to: &mut Module) {
    let value_trait_id = to.add_trait(value_trait());
    let value_trait_id = TraitId::new(to.module_id(), value_trait_id);
    debug_assert_eq!(to.trait_def(value_trait_id).name, VALUE_TRAIT_NAME);
    crate::hir::trait_defaults::register_value_ne(to, value_trait_id);
    let inspect_trait_id = to.add_trait(inspect_trait());
    let inspect_trait_id = TraitId::new(to.module_id(), inspect_trait_id);
    debug_assert_eq!(to.trait_def(inspect_trait_id).name, INSPECT_TRAIT_NAME);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CompilerSession;

    #[test]
    fn tag_scalars_resolve_named_variants_without_classifying_small_products() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "enum Signal { Stop, Go } enum WithPayload { Empty, Item(bool) } struct Small(bool)",
                "tag_scalars",
                crate::Path::single_str("tag_scalars"),
            )
            .unwrap()
            .module_id;
        let module = session.expect_fresh_module(module);
        let env = ModuleEnv::new(module, session.raw_modules());
        let named = |name| Type::named(module.get_type_def_id(ustr(name)).unwrap(), []);
        assert!(is_tag_scalar(named("Signal"), &env));
        assert!(is_tag_scalar(crate::std::ordering::ordering_type(), &env));
        assert!(!is_tag_scalar(named("WithPayload"), &env));
        assert!(!is_tag_scalar(named("Small"), &env));
        assert!(!is_tag_scalar(Type::variable_id(0), &env));
    }

    /// A storage decision has one identity: deciding a canonical key again gives it back, even
    /// when cases differ only in effects, which the key erases.
    #[test]
    fn canonical_payload_storage_keys_are_stable() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let span = Location::new_synthesized();
        let callback = |effects| Type::function_type(FnType::new_by_val([], int_type(), effects));
        let variant = Type::variant([
            (ustr("A"), callback(EffType::empty())),
            (
                ustr("B"),
                callback(EffType::single_primitive(PrimitiveEffect::Fallible)),
            ),
            (ustr("C"), Type::variable_id(0)),
        ]);
        let decide = |variant_ty, tag, payload_ty| {
            variant_payload_storage_decision(variant_ty, tag, payload_ty, span, &env).unwrap()
        };
        let cases = variant.data().as_variant().unwrap().clone();
        for (tag, payload_ty) in cases {
            let VariantPayloadStorageDecision::Evidence(key) = decide(variant, tag, payload_ty)
            else {
                panic!("the storage of case {tag} is open");
            };
            let DictionaryReq::VariantPayloadIndirection {
                variant_ty,
                tag,
                payload_ty,
            } = key.clone()
            else {
                unreachable!()
            };
            assert_eq!(
                decide(variant_ty, tag, payload_ty),
                VariantPayloadStorageDecision::Evidence(key)
            );
        }
    }

    #[test]
    fn variant_layout_uses_a_u32_tag_and_case_specific_payload_offsets() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let no_payload = Type::variant([(ustr("None"), Type::unit())]);
        let bool_payload =
            Type::variant([(ustr("None"), Type::unit()), (ustr("Some"), bool_type())]);

        assert_eq!(
            value_layout_for_type(no_payload, Location::new_synthesized(), &env).unwrap(),
            ResolvedValueLayout { size: 4, align: 4 }
        );
        assert_eq!(
            value_layout_for_type(bool_payload, Location::new_synthesized(), &env).unwrap(),
            ResolvedValueLayout { size: 8, align: 4 }
        );

        // A common union payload offset would make this 24 bytes: the twelve-byte payload would
        // be placed after padding the tag to the eight-byte alignment required only by `u64`.
        // Computing each case independently lets both payloads end at byte 16.
        let smalls = ValueLayout::product([ValueLayout::native::<u8>(); 12]);
        let layout = ValueLayout::variant([smalls, ValueLayout::native::<u64>()]);
        assert_eq!(layout.size, 16);
        assert_eq!(layout.align, 8);
    }

    #[test]
    fn functions_and_subscripts_use_the_callable_layout() {
        let session = CompilerSession::new();
        let env = session.module_env();
        use crate::types::r#type::{SubscriptMemberType, SubscriptResultConvention, SubscriptType};

        let word_size = u32::try_from(mem::size_of::<usize>()).unwrap();
        let word_align = u32::try_from(mem::align_of::<usize>()).unwrap();
        let expected = ResolvedValueLayout {
            size: 2 * word_size,
            align: word_align,
        };

        let concrete = Type::nullary_function_by_val(Type::unit());
        let generic = Type::function_by_val([Type::variable_id(0)], Type::variable_id(1));
        let subscript = Type::subscript_type(SubscriptType::new(
            vec![FnArgType::new_by_val(Type::variable_id(0))],
            Type::variable_id(1),
            Some(SubscriptMemberType::new(
                EffType::empty(),
                SubscriptResultConvention::AddressorPlace,
            )),
            None,
        ));
        for ty in [concrete, generic, subscript] {
            assert_eq!(
                value_layout_for_type(ty, Location::new_synthesized(), &env).unwrap(),
                expected
            );
        }

        let containing_tuple = Type::tuple([bool_type(), generic]);
        assert_eq!(
            value_layout_for_type(containing_tuple, Location::new_synthesized(), &env).unwrap(),
            ResolvedValueLayout {
                size: 3 * word_size,
                align: word_align,
            }
        );
    }

    #[test]
    fn tuples_use_compact_alignment_then_numeric_index_order() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let word = Type::primitive::<isize>();
        let ty = Type::tuple([bool_type(), word, bool_type()]);
        let spec = product_layout_spec(ty, Location::new_synthesized(), &env).unwrap();
        let size = mem::size_of::<isize>();
        assert_eq!(
            spec.static_field_offset(ProjectionIndex::new(0)),
            Some(size)
        );
        assert_eq!(spec.static_field_offset(ProjectionIndex::new(1)), Some(0));
        assert_eq!(
            spec.static_field_offset(ProjectionIndex::new(2)),
            Some(size + 1)
        );
        assert_eq!(
            value_layout_for_type(ty, Location::new_synthesized(), &env)
                .unwrap()
                .size as usize,
            2 * size
        );
        let spec = product_layout_spec(
            Type::tuple([bool_type(); 12]),
            Location::new_synthesized(),
            &env,
        )
        .unwrap();
        // Tuple indices are numeric: index 10 follows index 9, rather than index 1.
        assert_eq!(spec.static_field_offset(ProjectionIndex::new(10)), Some(10));
        for ty in [ty, Type::tuple([bool_type(); 12])] {
            let spec = product_layout_spec(ty, Location::new_synthesized(), &env).unwrap();
            let offsets = spec.static_field_offsets().unwrap();
            for (index, offset) in offsets.into_iter().enumerate() {
                assert_eq!(
                    spec.static_field_offset(ProjectionIndex::from_index(index)),
                    Some(offset)
                );
            }
        }
    }

    #[test]
    fn records_use_compact_alignment_then_name_order() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let record = Type::record(vec![
            (ustr("a"), bool_type()),
            (ustr("b"), Type::primitive::<isize>()),
            (ustr("c"), bool_type()),
        ]);
        let word_size = u32::try_from(mem::size_of::<isize>()).unwrap();
        let word_align = u32::try_from(mem::align_of::<isize>()).unwrap();

        assert_eq!(
            value_layout_for_type(record, Location::new_synthesized(), &env).unwrap(),
            ResolvedValueLayout {
                size: 2 * word_size,
                align: word_align,
            }
        );
        let spec = product_layout_spec(record, Location::new_synthesized(), &env).unwrap();
        assert_eq!(
            spec.static_field_offset(ProjectionIndex::new(0)),
            Some(word_size as usize)
        );
        assert_eq!(spec.static_field_offset(ProjectionIndex::new(1)), Some(0));
        assert_eq!(
            spec.static_field_offset(ProjectionIndex::new(2)),
            Some(word_size as usize + 1)
        );
    }
}
