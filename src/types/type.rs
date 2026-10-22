// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{
    any::{TypeId, type_name},
    borrow::Borrow,
    cell::RefCell,
    cmp::Ordering,
    fmt::{self, Debug, Display},
    hash::{Hash, Hasher},
    mem::{align_of, size_of},
    ops::Deref,
    sync::{OnceLock, RwLock, RwLockReadGuard},
};

use derive_new::new;
use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use indexmap::IndexSet;
use nonmax::NonMaxU32;
use rustc_hash::FxBuildHasher;
use ustr::{Ustr, ustr};

use crate::{
    FxHashMap, FxHashSet, Location,
    assert::assert_unique_strings,
    ast::{Attribute, UstrSpan},
    containers::{B, DenseBitSet, FromIndex, SVec2, b, compare_by},
    define_id_type,
    format::{
        FormatWith, escape_identifier, format_generic_param_list,
        type_variable_index_to_string_latin, write_identifier, write_with_separator_and_format_fn,
    },
    graph::{self, find_strongly_connected_components, topological_sort_sccs},
    hir::value::LiteralValue,
    module::{LocalDecl, ModuleEnv, QualifiedNameEnv, TypeDefId, id::Id},
    std::array::array_type_def,
    sync::SyncPhantomData,
    types::{
        effect_polarity::EffectVarPolarities,
        effects::{EffType, Effect, EffectVar, PrimitiveEffect, format_effect_binding_value},
        mutability::{FormatInFnArg, MutType, MutVar},
        type_like::{CastableToType, TypeLike},
        type_mapper::TypeMapper,
        type_scheme::TypeScheme,
        type_substitution::{instantiate_type, map_type_recursive},
        type_visitor::TypeInnerVisitor,
        var_set::KindVarSet,
    },
};

pub const PRIVATE_REPR_ATTRIBUTE: &str = "private_repr";

// use crate::types::typing_env::Local;

#[macro_export]
macro_rules! cached_primitive_ty {
    ($ty:ty) => {{ $crate::cached_ty!(Type::primitive::<$ty>) }};
}

#[macro_export]
macro_rules! cached_ty {
    ($ty:expr) => {{
        static TY: std::sync::OnceLock<Type> = std::sync::OnceLock::new();
        *TY.get_or_init($ty)
    }};
}

/// A generic variable for a type
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, new)]
pub struct TypeVar {
    /// The name of this type variable, its identity in the context considered
    name: u32,
}

impl TypeVar {
    pub fn name(&self) -> u32 {
        self.name
    }
    pub fn format_rust_style(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", type_variable_index_to_string_latin(self.name))
    }
    pub fn instantiate(&self, subst: &TypeInstSubst) -> Type {
        if let Some(ty) = subst.get(self) {
            *ty
        } else {
            Type::variable(*self)
        }
    }
}

impl Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format_rust_style(f)
    }
}

impl FromIndex for TypeVar {
    fn from_index(index: usize) -> Self {
        Self::new(index as u32)
    }
}

pub type TyVarKey = TypeVar;

pub trait BareNativeType: DynClone + DynEq + Send + Sync {
    /// Concrete Rust payload identity, distinct from this descriptor's `type_id`.
    /// Compiler-defined representations (such as Buffer) use their explicit lowering instead.
    fn value_type_id(&self) -> Option<TypeId> {
        None
    }
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
    fn type_name(&self) -> &'static str {
        type_name::<Self>()
    }
    fn value_size(&self) -> usize;
    fn value_align(&self) -> usize;
}

impl FormatWith<ModuleEnv<'_>> for BareNativeTypeB {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        match env.bare_native_name(self) {
            Some(name) => write!(f, "{name}"),
            None => write!(f, "{}", self.as_ref().type_name()),
        }
    }
}

impl FormatWith<QualifiedNameEnv<'_>> for BareNativeTypeB {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &QualifiedNameEnv<'_>) -> fmt::Result {
        match env.bare_native_name(self) {
            Some(name) => write!(f, "{name}"),
            None => write!(f, "{}", self.as_ref().type_name()),
        }
    }
}

pub fn bare_native_type<T: 'static>() -> BareNativeTypeB {
    b(BareNativeTypeImpl::<T>::new())
}

dyn_clone::clone_trait_object!(BareNativeType);
dyn_eq::eq_trait_object!(BareNativeType);

impl Ord for dyn BareNativeType {
    fn cmp(&self, other: &Self) -> Ordering {
        BareNativeType::type_id(self).cmp(&BareNativeType::type_id(other))
    }
}

impl PartialOrd for dyn BareNativeType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for dyn BareNativeType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        BareNativeType::type_id(self).hash(state)
    }
}

/// A boxed bare native type.
pub type BareNativeTypeB = B<dyn BareNativeType>;

#[derive(Default)]
pub struct BareNativeTypeImpl<T> {
    _marker: SyncPhantomData<T>,
}
impl<T> Clone for BareNativeTypeImpl<T> {
    fn clone(&self) -> Self {
        Self::new()
    }
}
impl<T> BareNativeTypeImpl<T> {
    pub fn new() -> Self {
        Self {
            _marker: SyncPhantomData::default(),
        }
    }
}

impl<T> PartialEq for BareNativeTypeImpl<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<T> Eq for BareNativeTypeImpl<T> {}

impl<T: 'static> BareNativeType for BareNativeTypeImpl<T> {
    fn value_type_id(&self) -> Option<TypeId> {
        Some(TypeId::of::<T>())
    }
    // fn type_id(&self) -> TypeId {
    //     TypeId::of::<T>()
    // }

    // fn type_name(&self) -> &'static str {
    //     type_name::<T>()
    // }
    fn value_size(&self) -> usize {
        size_of::<T>()
    }

    fn value_align(&self) -> usize {
        align_of::<T>()
    }
}

impl Debug for dyn BareNativeType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.type_name())
    }
}

/// A generic type implemented in Rust.
/// If arguments is empty, we call it a primitive type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, new)]
pub struct NativeType {
    pub bare_ty: BareNativeTypeB,
    pub arguments: Vec<Type>,
}

impl NativeType {
    pub fn new_primitive<T: 'static>() -> Self {
        Self {
            bare_ty: bare_native_type::<T>(),
            arguments: vec![],
        }
    }
    fn local_cmp(&self, other: &Self) -> Ordering {
        (*self.bare_ty).cmp(&*other.bare_ty).then(compare_by(
            &self.arguments,
            &other.arguments,
            Type::local_cmp,
        ))
    }
}

impl FormatWith<ModuleEnv<'_>> for NativeType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        fmt_native_type_with_env(self, f, env)
    }
}

impl FormatWith<TypeDisplayEnv<'_, '_>> for NativeType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &TypeDisplayEnv<'_, '_>) -> fmt::Result {
        fmt_native_type_with_env(self, f, env)
    }
}

impl FormatWith<QualifiedNameEnv<'_>> for NativeType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &QualifiedNameEnv<'_>) -> fmt::Result {
        if let Some(name) = env.native_type_name(self) {
            return write!(f, "{name}");
        }
        self.bare_ty.fmt_with(f, env)?;
        if !self.arguments.is_empty() {
            write!(f, "<")?;
            for (i, ty) in self.arguments.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                ty.fmt_with(f, env)?;
            }
            write!(f, ">")?;
        }
        Ok(())
    }
}

fn fmt_native_type_with_env<Env>(
    native: &NativeType,
    f: &mut fmt::Formatter,
    env: &Env,
) -> fmt::Result
where
    Env: TypeFormatEnv,
    Type: FormatWith<Env>,
{
    native.bare_ty.fmt_with(f, env.module_env())?;
    if !native.arguments.is_empty() {
        write!(f, "<")?;
        for (i, ty) in native.arguments.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            ty.fmt_with(f, env)?;
        }
        write!(f, ">")?;
    }
    Ok(())
}

pub struct TypeDisplayEnv<'a, 'm> {
    pub module_env: &'a ModuleEnv<'m>,
    pub ty_var_names: &'a FxHashMap<TypeVar, Ustr>,
    pub eff_var_names: Option<&'a FxHashMap<EffectVar, Ustr>>,
    effect_display: EffectDisplay<'a>,
}

#[derive(Clone, Copy)]
enum EffectDisplay<'a> {
    Full,
    Light {
        hidden_vars: &'a FxHashSet<EffectVar>,
    },
}

impl<'a, 'm> TypeDisplayEnv<'a, 'm> {
    pub fn new(module_env: &'a ModuleEnv<'m>, ty_var_names: &'a FxHashMap<TypeVar, Ustr>) -> Self {
        Self {
            module_env,
            ty_var_names,
            eff_var_names: None,
            effect_display: EffectDisplay::Full,
        }
    }

    pub(crate) fn with_eff_var_names(
        mut self,
        eff_var_names: &'a FxHashMap<EffectVar, Ustr>,
    ) -> Self {
        self.eff_var_names = Some(eff_var_names);
        self
    }

    pub(crate) fn with_light_effect_display(
        mut self,
        hidden_vars: &'a FxHashSet<EffectVar>,
    ) -> Self {
        self.effect_display = EffectDisplay::Light { hidden_vars };
        self
    }

    pub(crate) fn hides_effect_var(&self, var: EffectVar) -> bool {
        match self.effect_display {
            EffectDisplay::Full => false,
            EffectDisplay::Light { hidden_vars } => hidden_vars.contains(&var),
        }
    }

    pub(crate) fn displayed_effects(&self, effects: &EffType) -> EffType {
        match self.effect_display {
            EffectDisplay::Full => effects.clone(),
            EffectDisplay::Light { hidden_vars } => effects
                .iter()
                .filter(|effect| match effect {
                    Effect::Primitive(PrimitiveEffect::Fallible) => false,
                    Effect::Variable(var) => !hidden_vars.contains(var),
                    _ => true,
                })
                .collect(),
        }
    }

    pub(crate) fn is_light_effect_display(&self) -> bool {
        matches!(self.effect_display, EffectDisplay::Light { .. })
    }

    fn format_type(&self, ty: Type) -> String {
        ty.format_with(self).to_string()
    }
}

pub(crate) trait TypeFormatEnv {
    fn module_env(&self) -> &ModuleEnv<'_>;

    fn displayed_effects(&self, effects: &EffType) -> EffType {
        effects.clone()
    }

    fn is_light_effect_display(&self) -> bool {
        false
    }

    fn fmt_type_alias_name(&self, ty: Type, f: &mut fmt::Formatter<'_>)
    -> Result<bool, fmt::Error>;

    fn fmt_type_var(&self, var: TypeVar, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    fn fmt_effect_var(&self, var: EffectVar, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl TypeFormatEnv for ModuleEnv<'_> {
    fn module_env(&self) -> &ModuleEnv<'_> {
        self
    }

    fn fmt_type_alias_name(
        &self,
        ty: Type,
        f: &mut fmt::Formatter<'_>,
    ) -> Result<bool, fmt::Error> {
        if let Some(name) = self.type_alias_name(ty) {
            write!(f, "{name}")?;
            return Ok(true);
        }
        Ok(false)
    }

    fn fmt_type_var(&self, var: TypeVar, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{var}")
    }

    fn fmt_effect_var(&self, var: EffectVar, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{var}")
    }
}

impl TypeFormatEnv for TypeDisplayEnv<'_, '_> {
    fn module_env(&self) -> &ModuleEnv<'_> {
        self.module_env
    }

    fn displayed_effects(&self, effects: &EffType) -> EffType {
        self.displayed_effects(effects)
    }

    fn is_light_effect_display(&self) -> bool {
        self.is_light_effect_display()
    }

    fn fmt_type_alias_name(
        &self,
        ty: Type,
        f: &mut fmt::Formatter<'_>,
    ) -> Result<bool, fmt::Error> {
        if let Some(name) = self
            .module_env
            .type_alias_name_with(ty, |ty| self.format_type(ty))
        {
            write!(f, "{name}")?;
            return Ok(true);
        }
        Ok(false)
    }

    fn fmt_type_var(&self, var: TypeVar, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ty_var_names.get(&var) {
            Some(name) => write_identifier(f, name.as_str()),
            None => write!(f, "{var}"),
        }
    }

    fn fmt_effect_var(&self, var: EffectVar, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.eff_var_names.and_then(|names| names.get(&var)) {
            Some(name) => write_identifier(f, name.as_str()),
            None => write!(f, "{var}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, new)]
pub struct FnArgType {
    pub ty: Type,
    pub mut_ty: MutType,
}
impl FnArgType {
    pub fn new_by_val(ty: Type) -> Self {
        Self {
            ty,
            mut_ty: MutType::constant(),
        }
    }
    fn local_cmp(&self, other: &Self) -> Ordering {
        self.ty
            .local_cmp(&other.ty)
            .then(self.mut_ty.cmp(&other.mut_ty))
    }
}
impl FormatWith<ModuleEnv<'_>> for FnArgType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        fmt_fn_arg_type_with_env(self, f, env)
    }
}

impl FormatWith<TypeDisplayEnv<'_, '_>> for FnArgType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &TypeDisplayEnv<'_, '_>) -> fmt::Result {
        fmt_fn_arg_type_with_env(self, f, env)
    }
}

impl FormatWith<QualifiedNameEnv<'_>> for FnArgType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &QualifiedNameEnv<'_>) -> fmt::Result {
        self.mut_ty.format_in_fn_arg(f)?;
        self.ty.fmt_with(f, env)
    }
}

fn fmt_fn_arg_type_with_env<Env>(arg: &FnArgType, f: &mut fmt::Formatter, env: &Env) -> fmt::Result
where
    Type: FormatWith<Env>,
{
    arg.mut_ty.format_in_fn_arg(f)?;
    arg.ty.fmt_with(f, env)
}

/// How a subscript member exposes its projected place.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SubscriptResultConvention {
    /// A scoped, callee-rooted yielded place. It must be consumed through a
    /// `WithYielded` driver and cannot escape as caller-rooted storage.
    YieldedOnce,
    /// A caller-rooted place, used by selected native or source subscript
    /// member implementations. This is the strongest subscript result
    /// convention because it can also satisfy scoped-yield consumers.
    AddressorPlace,
}

impl SubscriptResultConvention {
    pub fn returns_caller_rooted_place(self) -> bool {
        matches!(self, Self::AddressorPlace)
    }

    pub fn requires_yield_driver(self) -> bool {
        matches!(self, Self::YieldedOnce)
    }

    pub fn can_satisfy(self, expected: Self) -> bool {
        match expected {
            Self::YieldedOnce => matches!(self, Self::YieldedOnce | Self::AddressorPlace),
            Self::AddressorPlace => matches!(self, Self::AddressorPlace),
        }
    }
}

/// How a selected callable implementation yields its result.
///
/// Borrow-returning conventions are call-result conventions, not first-class
/// reference types. The return value still has type `ret`; the convention only
/// controls whether and how the immediate call result may be consumed as a
/// place before being materialized.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum CallResultConvention {
    /// A normal value return.
    #[default]
    Value,
    /// Statically zero-sized result, with no caller-provided result storage.
    NoValue,
    Subscript(SubscriptResultConvention),
}

impl CallResultConvention {
    pub const YIELDED_ONCE: Self = Self::Subscript(SubscriptResultConvention::YieldedOnce);
    pub const ADDRESSOR_PLACE: Self = Self::Subscript(SubscriptResultConvention::AddressorPlace);

    pub fn returns_borrow(self) -> bool {
        matches!(self, Self::Subscript(_))
    }

    pub fn returns_caller_rooted_place(self) -> bool {
        match self {
            Self::Value | Self::NoValue => false,
            Self::Subscript(convention) => convention.returns_caller_rooted_place(),
        }
    }

    pub fn requires_yield_driver(self) -> bool {
        match self {
            Self::Value | Self::NoValue => false,
            Self::Subscript(convention) => convention.requires_yield_driver(),
        }
    }

    pub fn returns_place(self) -> bool {
        self.returns_caller_rooted_place()
    }

    pub fn can_satisfy(self, expected: Self) -> bool {
        match (self, expected) {
            (Self::Value, Self::Value) | (Self::NoValue, Self::NoValue) => true,
            (Self::Subscript(SubscriptResultConvention::AddressorPlace), Self::Value) => true,
            (Self::Subscript(current), Self::Subscript(expected)) => current.can_satisfy(expected),
            _ => false,
        }
    }
}

/// The type of a function
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnType {
    pub args: Vec<FnArgType>,
    pub ret: Type,
    pub effects: EffType,
}

impl FnType {
    pub fn new(args: Vec<FnArgType>, ret: Type, effects: EffType) -> Self {
        Self { args, ret, effects }
    }

    /// The effect variables occurring only in effects that a value of this type performs,
    /// never in effects it receives or in invariant positions. Nothing can observe more of such
    /// a variable than its least solution.
    pub fn positive_only_effect_vars(&self) -> FxHashSet<EffectVar> {
        let mut polarities = EffectVarPolarities::default();
        polarities.visit_fn(self, true);
        polarities.positive_only()
    }

    pub fn new_mut_resolved(
        args: impl IntoIterator<Item = (Type, bool)>,
        ret: Type,
        effects: EffType,
    ) -> Self {
        Self {
            args: args
                .into_iter()
                .map(|(ty, mutable)| FnArgType::new(ty, MutType::from(mutable)))
                .collect(),
            ret,
            effects,
        }
    }

    pub fn new_by_val(args: impl IntoIterator<Item = Type>, ret: Type, effects: EffType) -> Self {
        Self {
            args: args
                .into_iter()
                .map(|ty| FnArgType {
                    ty,
                    mut_ty: MutType::constant(),
                })
                .collect(),
            ret,
            effects,
        }
    }

    pub fn as_locals_no_bound<'a>(
        &self,
        arg_names: impl Iterator<Item = &'a UstrSpan>,
    ) -> Vec<LocalDecl> {
        let mut locals = arg_names
            .zip(self.args.iter())
            .map(|(name, arg)| LocalDecl::new(*name, arg.mut_ty, arg.ty, None, name.1))
            .collect::<Vec<_>>();
        LocalDecl::assign_sequential_slots(&mut locals);
        locals
    }

    pub fn args_ty(&self) -> impl Iterator<Item = Type> + '_ {
        self.args.iter().map(|arg| arg.ty)
    }

    fn local_cmp(&self, other: &Self) -> Ordering {
        compare_by(&self.args, &other.args, FnArgType::local_cmp)
            .then(self.ret.local_cmp(&other.ret))
    }
}

/// Type and result convention of a selected callable implementation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, new)]
pub struct CallImplType {
    pub fn_ty: FnType,
    pub result_convention: CallResultConvention,
}

impl CallImplType {
    pub fn value(fn_ty: FnType) -> Self {
        Self::new(fn_ty, CallResultConvention::Value)
    }

    pub fn returns_place(&self) -> bool {
        self.result_convention.returns_place()
    }

    pub fn ret(&self) -> Type {
        self.fn_ty.ret
    }

    pub fn effects(&self) -> &EffType {
        &self.fn_ty.effects
    }
}

/// Type-level capability for one member of a subscript.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, new)]
pub struct SubscriptMemberType {
    pub effects: EffType,
    pub result_convention: SubscriptResultConvention,
}

impl SubscriptMemberType {
    fn can_satisfy(&self, expected: &Self) -> bool {
        self.result_convention
            .can_satisfy(expected.result_convention)
    }
}

/// First-class type of a subscript/projection capability.
///
/// This is intentionally distinct from `FnType`: a subscript is selected and
/// consumed as a place-producing projection capability, not called as an
/// ordinary function.
#[derive(Debug, Clone, PartialEq, Eq, Hash, new)]
pub struct SubscriptType {
    pub args: Vec<FnArgType>,
    pub ret: Type,
    pub ref_member: Option<SubscriptMemberType>,
    pub mut_member: Option<SubscriptMemberType>,
}

impl SubscriptType {
    pub(crate) fn members(&self) -> impl Iterator<Item = &SubscriptMemberType> {
        self.ref_member.iter().chain(self.mut_member.iter())
    }

    fn local_cmp(&self, other: &Self) -> Ordering {
        compare_by(&self.args, &other.args, FnArgType::local_cmp)
            .then(self.ret.local_cmp(&other.ret))
            .then(self.ref_member.cmp(&other.ref_member))
            .then(self.mut_member.cmp(&other.mut_member))
    }

    pub(crate) fn can_satisfy_members(&self, expected: &Self) -> bool {
        member_can_satisfy(&self.ref_member, &expected.ref_member)
            && member_can_satisfy(&self.mut_member, &expected.mut_member)
    }

    pub(crate) fn receiver_ty(&self) -> Type {
        self.args
            .first()
            .expect("subscript type should have at least a receiver argument")
            .ty
    }
}

fn member_can_satisfy(
    current: &Option<SubscriptMemberType>,
    expected: &Option<SubscriptMemberType>,
) -> bool {
    match expected {
        None => true,
        Some(expected) => current
            .as_ref()
            .is_some_and(|current| current.can_satisfy(expected)),
    }
}

impl TypeLike for CallImplType {
    fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
        self.fn_ty.visit(visitor);
    }

    fn map(&self, f: &mut impl TypeMapper) -> Self {
        Self {
            fn_ty: self.fn_ty.map(f),
            result_convention: self.result_convention,
        }
    }

    fn fill_with_input_effect_vars(&self, vars: &mut FxHashSet<EffectVar>) {
        self.fn_ty.fill_with_input_effect_vars(vars);
    }

    fn fill_with_output_effect_vars(&self, vars: &mut FxHashSet<EffectVar>) {
        self.fn_ty.fill_with_output_effect_vars(vars);
    }
}

impl TypeLike for FnType {
    fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
        self.args.iter().for_each(|arg| {
            visitor.visit_mut_ty(arg.mut_ty);
            arg.ty.data().visit(visitor)
        });
        self.ret.data().visit(visitor);
        visitor.visit_eff_ty(&self.effects);
    }

    fn map(&self, f: &mut impl TypeMapper) -> Self {
        Self {
            args: self
                .args
                .iter()
                .map(|arg| FnArgType {
                    ty: arg.ty.map(f),
                    mut_ty: f.map_mut_type(arg.mut_ty),
                })
                .collect(),
            ret: self.ret.map(f),
            effects: f.map_effect_type(&self.effects),
        }
    }

    fn fill_with_input_effect_vars(&self, vars: &mut FxHashSet<EffectVar>) {
        for arg in &self.args {
            arg.ty.fill_with_inner_effect_vars(vars);
        }
        self.ret.fill_with_inner_effect_vars(vars);
    }

    fn fill_with_output_effect_vars(&self, vars: &mut FxHashSet<EffectVar>) {
        self.effects.fill_with_inner_effect_vars(vars);
    }
}

impl TypeLike for SubscriptType {
    fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
        self.args.iter().for_each(|arg| {
            visitor.visit_mut_ty(arg.mut_ty);
            arg.ty.data().visit(visitor)
        });
        self.ret.data().visit(visitor);
        for member in self.members() {
            visitor.visit_eff_ty(&member.effects);
        }
    }

    fn map(&self, f: &mut impl TypeMapper) -> Self {
        Self {
            args: self
                .args
                .iter()
                .map(|arg| FnArgType {
                    ty: arg.ty.map(f),
                    mut_ty: f.map_mut_type(arg.mut_ty),
                })
                .collect(),
            ret: self.ret.map(f),
            ref_member: self.ref_member.as_ref().map(|member| SubscriptMemberType {
                effects: f.map_effect_type(&member.effects),
                result_convention: member.result_convention,
            }),
            mut_member: self.mut_member.as_ref().map(|member| SubscriptMemberType {
                effects: f.map_effect_type(&member.effects),
                result_convention: member.result_convention,
            }),
        }
    }

    fn fill_with_input_effect_vars(&self, vars: &mut FxHashSet<EffectVar>) {
        for arg in &self.args {
            arg.ty.fill_with_inner_effect_vars(vars);
        }
        self.ret.fill_with_inner_effect_vars(vars);
    }

    fn fill_with_output_effect_vars(&self, vars: &mut FxHashSet<EffectVar>) {
        for member in self.members() {
            member.effects.fill_with_inner_effect_vars(vars);
        }
    }
}

impl CastableToType for FnType {
    fn to_type(&self) -> Type {
        Type::function_type(self.clone())
    }
}

impl CastableToType for SubscriptType {
    fn to_type(&self) -> Type {
        Type::subscript_type(self.clone())
    }
}

impl FormatWith<ModuleEnv<'_>> for FnType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        fmt_fn_type_with_env(self, f, env)
    }
}

impl FormatWith<ModuleEnv<'_>> for CallImplType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        fmt_call_impl_type_with_env(self, f, env)
    }
}

impl FormatWith<ModuleEnv<'_>> for SubscriptType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        fmt_subscript_type_with_env(self, f, env)
    }
}

impl FormatWith<TypeDisplayEnv<'_, '_>> for FnType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &TypeDisplayEnv<'_, '_>) -> fmt::Result {
        fmt_fn_type_with_env(self, f, env)
    }
}

impl FormatWith<TypeDisplayEnv<'_, '_>> for CallImplType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &TypeDisplayEnv<'_, '_>) -> fmt::Result {
        fmt_call_impl_type_with_env(self, f, env)
    }
}

impl FormatWith<TypeDisplayEnv<'_, '_>> for SubscriptType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &TypeDisplayEnv<'_, '_>) -> fmt::Result {
        fmt_subscript_type_with_env(self, f, env)
    }
}

impl FormatWith<QualifiedNameEnv<'_>> for FnType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &QualifiedNameEnv<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            arg.fmt_with(f, env)?;
        }
        write!(f, ") -> ")?;
        self.ret.fmt_with(f, env)?;
        if !self.effects.is_empty() {
            write!(f, " ! ")?;
            format_effect_binding_value(&self.effects, f)?;
        }
        Ok(())
    }
}

impl FormatWith<QualifiedNameEnv<'_>> for SubscriptType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &QualifiedNameEnv<'_>) -> fmt::Result {
        fmt_subscript_type_with_qualified_name_env(self, f, env)
    }
}

impl FormatWith<QualifiedNameEnv<'_>> for CallImplType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &QualifiedNameEnv<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, arg) in self.fn_ty.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            arg.fmt_with(f, env)?;
        }
        write!(f, ") -> ")?;
        if self.returns_place() {
            write!(f, "place ")?;
        }
        self.fn_ty.ret.fmt_with(f, env)?;
        if !self.fn_ty.effects.is_empty() {
            write!(f, " ! ")?;
            format_effect_binding_value(&self.fn_ty.effects, f)?;
        }
        Ok(())
    }
}

fn fmt_fn_type_with_env<Env>(function: &FnType, f: &mut fmt::Formatter, env: &Env) -> fmt::Result
where
    FnArgType: FormatWith<Env>,
    Type: FormatWith<Env>,
    Env: TypeFormatEnv,
{
    write!(f, "(")?;
    for (i, arg) in function.args.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        arg.fmt_with(f, env)?;
    }
    write!(f, ") -> ")?;
    function.ret.fmt_with(f, env)?;
    format_function_effect_suffix_with_env(&env.displayed_effects(&function.effects), f, env)
}

fn fmt_call_impl_type_with_env<Env>(
    function: &CallImplType,
    f: &mut fmt::Formatter,
    env: &Env,
) -> fmt::Result
where
    FnArgType: FormatWith<Env>,
    Type: FormatWith<Env>,
    Env: TypeFormatEnv,
{
    write!(f, "(")?;
    for (i, arg) in function.fn_ty.args.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        arg.fmt_with(f, env)?;
    }
    write!(f, ") -> ")?;
    if function.returns_place() {
        write!(f, "place ")?;
    }
    function.fn_ty.ret.fmt_with(f, env)?;
    format_function_effect_suffix_with_env(&env.displayed_effects(&function.fn_ty.effects), f, env)
}

fn fmt_subscript_type_with_env<Env>(
    subscript: &SubscriptType,
    f: &mut fmt::Formatter,
    env: &Env,
) -> fmt::Result
where
    FnArgType: FormatWith<Env>,
    Type: FormatWith<Env>,
    Env: TypeFormatEnv,
{
    fmt_subscript_type_signature(
        subscript,
        f,
        |arg, f| arg.fmt_with(f, env),
        |ty, f| ty.fmt_with(f, env),
    )?;
    fmt_subscript_type_members(subscript, f, |effects, f| {
        format_function_effect_suffix_with_env(&env.displayed_effects(effects), f, env)
    })
}

fn fmt_subscript_type_with_qualified_name_env(
    subscript: &SubscriptType,
    f: &mut fmt::Formatter,
    env: &QualifiedNameEnv<'_>,
) -> fmt::Result {
    fmt_subscript_type_signature(
        subscript,
        f,
        |arg, f| arg.fmt_with(f, env),
        |ty, f| ty.fmt_with(f, env),
    )?;
    fmt_subscript_type_members(subscript, f, |effects, f| {
        if effects.is_empty() {
            Ok(())
        } else {
            write!(f, " ! ")?;
            format_effect_binding_value(effects, f)
        }
    })
}

fn fmt_subscript_type_signature(
    subscript: &SubscriptType,
    f: &mut fmt::Formatter,
    mut fmt_arg: impl FnMut(&FnArgType, &mut fmt::Formatter) -> fmt::Result,
    mut fmt_ret: impl FnMut(Type, &mut fmt::Formatter) -> fmt::Result,
) -> fmt::Result {
    write!(f, "subscript (")?;
    for (i, arg) in subscript.args.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        fmt_arg(arg, f)?;
    }
    write!(f, ") -> ")?;
    fmt_ret(subscript.ret, f)
}

fn fmt_subscript_type_members(
    subscript: &SubscriptType,
    f: &mut fmt::Formatter,
    mut fmt_effects: impl FnMut(&EffType, &mut fmt::Formatter) -> fmt::Result,
) -> fmt::Result {
    write!(f, " {{")?;
    let mut needs_separator = false;
    if let Some(member) = &subscript.ref_member {
        write!(f, " ref")?;
        format_subscript_member_result_convention(member.result_convention, f)?;
        fmt_effects(&member.effects, f)?;
        needs_separator = true;
    }
    if let Some(member) = &subscript.mut_member {
        if needs_separator {
            write!(f, ";")?;
        }
        write!(f, " mut")?;
        format_subscript_member_result_convention(member.result_convention, f)?;
        fmt_effects(&member.effects, f)?;
    }
    write!(f, " }}")
}

fn format_subscript_member_result_convention(
    convention: SubscriptResultConvention,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    match convention {
        SubscriptResultConvention::YieldedOnce => write!(f, " yielded"),
        SubscriptResultConvention::AddressorPlace => write!(f, " place"),
    }
}

pub(crate) fn fmt_fn_type_with_arg_names<Env>(
    fn_ty: &FnType,
    arg_names: &[Ustr],
    f: &mut fmt::Formatter,
    env: &Env,
) -> fmt::Result
where
    FnArgType: FormatWith<Env>,
    Type: FormatWith<Env>,
    Env: TypeFormatEnv,
{
    write!(f, "(")?;
    for (i, (arg_ty, arg_name)) in fn_ty.args.iter().zip(arg_names).enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{arg_name}: ")?;
        arg_ty.fmt_with(f, env)?;
    }
    write!(f, ") -> ")?;
    fn_ty.ret.fmt_with(f, env)?;
    format_function_effect_suffix_with_env(&env.displayed_effects(&fn_ty.effects), f, env)
}

pub(crate) fn fmt_call_impl_type_with_arg_names<Env>(
    call_ty: &CallImplType,
    arg_names: &[Ustr],
    f: &mut fmt::Formatter,
    env: &Env,
) -> fmt::Result
where
    FnArgType: FormatWith<Env>,
    Type: FormatWith<Env>,
    Env: TypeFormatEnv,
{
    write!(f, "(")?;
    for (i, (arg_ty, arg_name)) in call_ty.fn_ty.args.iter().zip(arg_names).enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{arg_name}: ")?;
        arg_ty.fmt_with(f, env)?;
    }
    write!(f, ") -> ")?;
    if call_ty.returns_place() {
        write!(f, "place ")?;
    }
    call_ty.fn_ty.ret.fmt_with(f, env)?;
    format_function_effect_suffix_with_env(&env.displayed_effects(&call_ty.fn_ty.effects), f, env)
}

pub(crate) fn format_effect_binding_value_with_env<Env>(
    eff: &EffType,
    f: &mut fmt::Formatter<'_>,
    env: &Env,
) -> fmt::Result
where
    Env: TypeFormatEnv,
{
    match eff.as_single() {
        Some(Effect::Variable(var)) => env.fmt_effect_var(var, f),
        Some(effect) => Display::fmt(&effect, f),
        None if eff.is_empty() => write!(f, "()"),
        None => {
            write!(f, "(")?;
            write_with_separator_and_format_fn(
                eff.iter(),
                ", ",
                |effect, f| match effect {
                    Effect::Variable(var) => env.fmt_effect_var(var, f),
                    effect => Display::fmt(&effect, f),
                },
                f,
            )?;
            write!(f, ")")
        }
    }
}

pub(crate) fn display_effect_binding_value_with_env<'a, Env>(
    eff: &'a EffType,
    env: &'a Env,
) -> impl Display + 'a
where
    Env: TypeFormatEnv,
{
    struct EffectBindingValueDisplay<'a, Env> {
        eff: &'a EffType,
        env: &'a Env,
    }

    impl<Env> Display for EffectBindingValueDisplay<'_, Env>
    where
        Env: TypeFormatEnv,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            format_effect_binding_value_with_env(self.eff, f, self.env)
        }
    }

    EffectBindingValueDisplay { eff, env }
}

fn format_function_effect_suffix_with_env<Env>(
    eff: &EffType,
    f: &mut fmt::Formatter<'_>,
    env: &Env,
) -> fmt::Result
where
    Env: TypeFormatEnv,
{
    if eff.is_empty() {
        Ok(())
    } else {
        write!(f, " ! {}", display_effect_binding_value_with_env(eff, env))
    }
}

/// A type identifier, unique for a given type of a given mathematical structure
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Type {
    world: Option<NonMaxU32>, // If None, current local world
    index: u32,
}

impl Type {
    // helper constructors
    pub fn unit() -> Self {
        cached_primitive_ty!(())
    }

    pub fn primitive<T: 'static>() -> Self {
        Self::native::<T>([])
    }

    pub fn native<T: 'static>(arguments: impl Into<Vec<Type>>) -> Self {
        let bare_ty = bare_native_type::<T>();
        TypeKind::Native(b(NativeType {
            arguments: arguments.into(),
            bare_ty,
        }))
        .store()
    }

    pub fn native_type(native_type: NativeType) -> Self {
        TypeKind::Native(b(native_type)).store()
    }

    pub fn variable_id(id: u32) -> Self {
        Self::variable(TypeVar::new(id))
    }

    pub fn variable(var: TypeVar) -> Self {
        TypeKind::Variable(var).store()
    }

    pub fn variant(types: impl Into<Vec<(Ustr, Self)>>) -> Self {
        let types = types.into();
        if types.is_empty() {
            return Self::never();
        }
        TypeKind::Variant(types).store()
    }

    pub fn tuple(elements: impl Into<Vec<Self>>) -> Self {
        let elements = elements.into();
        if elements.is_empty() {
            return Self::unit();
        }
        TypeKind::Tuple(elements).store()
    }

    pub fn record(fields: impl Into<Vec<(Ustr, Self)>>) -> Self {
        TypeKind::Record(fields.into()).store()
    }

    pub fn function_type(ty: FnType) -> Self {
        TypeKind::Function(b(ty)).store()
    }

    pub fn subscript_type(ty: SubscriptType) -> Self {
        TypeKind::Subscript(b(ty)).store()
    }

    pub fn function_by_val_with_effects(
        args: impl IntoIterator<Item = Self>,
        ret: Self,
        effects: EffType,
    ) -> Self {
        Self::function_type(FnType::new_by_val(args, ret, effects))
    }

    pub fn function_by_val(args: impl IntoIterator<Item = Self>, ret: Self) -> Self {
        Self::function_by_val_with_effects(args, ret, EffType::empty())
    }

    pub fn nullary_function_by_val(ret: Self) -> Self {
        Self::function_by_val([], ret)
    }

    pub fn unary_function_by_val(arg: Self, ret: Self) -> Self {
        Self::function_by_val([arg], ret)
    }

    pub fn binary_function_by_val(arg1: Self, arg2: Self, ret: Self) -> Self {
        Self::function_by_val([arg1, arg2], ret)
    }

    pub fn named(decl: TypeDefId, arg_tys: impl Into<Vec<Self>>) -> Self {
        Self::named_with_effects(decl, arg_tys, Vec::new())
    }

    pub fn named_with_effects(
        decl: TypeDefId,
        arg_tys: impl Into<Vec<Self>>,
        effect_args: impl Into<Vec<EffType>>,
    ) -> Self {
        TypeKind::Named(NamedType {
            def: decl,
            params: arg_tys.into(),
            effect_params: effect_args.into(),
        })
        .store()
    }

    pub fn never() -> Self {
        cached_ty!(|| TypeKind::Never.store())
    }

    pub fn new_local(index: u32) -> Self {
        Self { world: None, index }
    }

    pub fn new_global(world: u32, index: u32) -> Self {
        Self {
            world: Some(NonMaxU32::new(world).unwrap()),
            index,
        }
    }

    // getter
    pub fn world(self) -> Option<NonMaxU32> {
        self.world
    }

    pub fn index(self) -> u32 {
        self.index
    }

    pub fn is_global_recursive(&self) -> bool {
        self.world.is_some_and(|w| w.get() > 0)
    }

    pub fn is_function(self) -> bool {
        matches!(&*self.data(), TypeKind::Function(_))
    }

    pub fn is_subscript(self) -> bool {
        matches!(&*self.data(), TypeKind::Subscript(_))
    }

    pub fn data<'t>(self) -> TypeDataRef<'t> {
        let guard = types().read().unwrap();
        TypeDataRef { ty: self, guard }
    }

    /// Cached free-variable summary for this interned type.
    pub fn summary<'t>(self) -> TypeSummaryRef<'t> {
        let guard = types().read().unwrap();
        TypeSummaryRef { ty: self, guard }
    }

    /// Whether this type's shape is known enough for trait impl selection.
    ///
    /// Effect variables do not make the selected impl ambiguous: once the type
    /// and mutability shape has selected an impl head, effect arguments are
    /// solved by the ordinary effect constraints produced while matching that
    /// head.
    pub fn is_trait_input_resolved(self) -> bool {
        let summary = self.summary();
        summary.free_ty_vars.is_empty() && summary.free_mut_vars.is_empty()
    }

    // filter
    pub fn is_local(self) -> bool {
        self.world.is_none()
    }

    // other
    fn local_cmp(&self, other: &Self) -> Ordering {
        if (self.world, other.world) == (None, None) {
            Ordering::Equal
        } else {
            self.cmp(other)
        }
    }

    /// Apply f to self if we are not in a self-calling cycle.
    /// Takes two function for normal and cyclic cases, and a context
    fn with_cycle_detection<F, D, C, R>(&self, normal: F, cycle: D, ctx: C) -> R
    where
        F: FnOnce(&Self, C) -> R,
        D: FnOnce(&Self, C) -> R,
    {
        // Thread-local hash-map for cycle detection
        thread_local! {
            static TYPE_VISITED: RefCell<FxHashSet<Type>> = RefCell::new(FxHashSet::default());
        }

        // Check for cycle and insert the type into the HashSet
        let cycle_detected = TYPE_VISITED.with(|visited| {
            let mut visited = visited.borrow_mut();
            if visited.contains(self) {
                true // Cycle detected
            } else {
                visited.insert(*self);
                false
            }
        });

        // Return special case if cycle detected
        if cycle_detected {
            return cycle(self, ctx);
        }

        // Normal case, can possibly recurse
        let result = normal(self, ctx);

        // Remove the type on back-tracking
        TYPE_VISITED.with(|visited| {
            visited.borrow_mut().remove(self);
        });

        result
    }
}

impl TypeLike for Type {
    fn map(&self, f: &mut impl TypeMapper) -> Self {
        map_type_recursive(*self, f)
    }

    fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
        self.data().visit(visitor)
    }

    // Overrides of the default `TypeLike` query methods that consult the
    // cached free-variable summary instead of walking the type tree.

    fn inner_ty_vars(&self) -> Vec<TypeVar> {
        self.summary().free_ty_vars.iter().collect()
    }

    fn inner_mut_ty_vars(&self) -> Vec<MutVar> {
        self.summary().free_mut_vars.iter().collect()
    }

    fn input_effect_vars(&self) -> FxHashSet<EffectVar> {
        self.summary().free_eff_vars.iter().collect()
    }

    fn inner_effect_vars(&self) -> FxHashSet<EffectVar> {
        // `Type` has no output-only effect vars (the default `fill_with_output_effect_vars` is a no-op),
        // so the union equals the input set.
        self.input_effect_vars()
    }

    fn contains_any_type_var(&self, var: TypeVar) -> bool {
        self.summary().free_ty_vars.contains(var)
    }

    fn contains_any_ty_vars(&self, vars: &[TypeVar]) -> bool {
        let summary = self.summary();
        vars.iter().any(|v| summary.free_ty_vars.contains(*v))
    }

    fn is_constant(&self) -> bool {
        let summary = self.summary();
        summary.free_ty_vars.is_empty()
            && summary.free_mut_vars.is_empty()
            && summary.free_eff_vars.is_empty()
    }
}

impl CastableToType for Type {
    fn to_type(&self) -> Type {
        *self
    }
}

impl FormatWith<ModuleEnv<'_>> for Type {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        fmt_type_with_env(self, f, env)
    }
}

impl FormatWith<TypeDisplayEnv<'_, '_>> for Type {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &TypeDisplayEnv<'_, '_>) -> fmt::Result {
        fmt_type_with_env(self, f, env)
    }
}

impl FormatWith<QualifiedNameEnv<'_>> for Type {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &QualifiedNameEnv<'_>) -> fmt::Result {
        self.with_cycle_detection(
            |ty, (f, env)| ty.data().fmt_with(f, env),
            |_, (f, _)| write!(f, "Self"),
            (f, env),
        )
    }
}

fn fmt_type_with_env<Env>(ty: &Type, f: &mut fmt::Formatter, env: &Env) -> fmt::Result
where
    Env: TypeFormatEnv,
    TypeKind: FormatWith<Env>,
{
    if env.fmt_type_alias_name(*ty, f)? {
        return Ok(());
    }
    ty.with_cycle_detection(
        |ty, (f, env)| ty.data().fmt_with(f, env),
        |_, (f, _)| write!(f, "Self"),
        (f, env),
    )
}

impl Ord for Type {
    fn cmp(&self, other: &Self) -> Ordering {
        self.world
            .cmp(&other.world)
            .then(self.index.cmp(&other.index))
    }
}

impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Instantiation substitution that maps type variables to actual types.
pub type TypeInstSubst = FxHashMap<TypeVar, Type>;

define_id_type!(
    /// ID of a type alias definition within a module
    LocalTypeAliasId
);

/// A single type alias entry, potentially generic.
#[derive(Debug, Clone)]
pub struct TypeAliasEntry {
    pub name: Ustr,
    pub generic_params: Vec<UstrSpan>,
    pub ty_var_count: u32,
    pub ty: Type,
    pub doc: Option<String>,
}

impl TypeAliasEntry {
    pub fn param_count(&self) -> usize {
        self.generic_params.len()
    }

    pub fn doc_with_fallback<'a>(&'a self, env: &'a ModuleEnv<'_>) -> Option<&'a str> {
        self.doc.as_deref().or_else(|| {
            let type_def = match &*self.ty.data() {
                TypeKind::Named(named) => named.def,
                _ => return None,
            };
            env.try_type_def(type_def)?.doc.as_deref()
        })
    }
}

/// Aliased types
#[derive(Debug, Clone, Default)]
pub(crate) struct TypeAliases {
    entries: Vec<TypeAliasEntry>,
    type_to_name: FxHashMap<Type, Ustr>,
    /// Names for the native part of generic native types, used for formatting
    bare_native_to_name: FxHashMap<BareNativeTypeB, Ustr>,
    /// Reverse mapping: name → bare native type, used for type resolution in Ferlium code
    name_to_bare_native: FxHashMap<Ustr, BareNativeTypeB>,
}
impl TypeAliases {
    pub fn set(
        &mut self,
        alias: Ustr,
        generic_params: Vec<UstrSpan>,
        ty_var_count: u32,
        ty: Type,
        doc: Option<String>,
    ) {
        // Only register non-generic aliases in the reverse name lookup
        if generic_params.is_empty() {
            self.type_to_name.insert(ty, alias);
        }
        assert_eq!(generic_params.len(), ty_var_count as usize);
        self.entries.push(TypeAliasEntry {
            name: alias,
            generic_params,
            ty_var_count,
            ty,
            doc,
        });
    }

    pub fn get_name(&self, ty: Type) -> Option<Ustr> {
        self.type_to_name.get(&ty).copied()
    }

    pub fn get_native_name(&self, native: &NativeType) -> Option<Ustr> {
        self.entries.iter().find_map(|entry| {
            if !entry.generic_params.is_empty() {
                return None;
            }
            match &*entry.ty.data() {
                TypeKind::Native(alias_native) if alias_native.as_ref() == native => {
                    Some(entry.name)
                }
                _ => None,
            }
        })
    }

    pub fn get_entry(&self, id: LocalTypeAliasId) -> &TypeAliasEntry {
        &self.entries[id.as_index()]
    }

    pub fn type_len(&self) -> usize {
        self.entries.len()
    }

    pub fn type_entries(&self) -> impl Iterator<Item = &TypeAliasEntry> + '_ {
        self.entries.iter()
    }

    pub fn set_bare_native(&mut self, alias: Ustr, bare: BareNativeTypeB) {
        self.name_to_bare_native.insert(alias, bare.clone());
        self.bare_native_to_name.insert(bare, alias);
    }

    pub fn get_bare_native_name(&self, bare: &BareNativeTypeB) -> Option<Ustr> {
        self.bare_native_to_name.get(bare).copied()
    }

    pub fn get_bare_native_by_name(&self, name: Ustr) -> Option<&BareNativeTypeB> {
        self.name_to_bare_native.get(&name)
    }

    pub fn bare_native_iter(&self) -> impl Iterator<Item = (Ustr, &BareNativeTypeB)> {
        self.bare_native_to_name
            .iter()
            .map(|(bare, name)| (*name, bare))
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
            && self.type_to_name.is_empty()
            && self.bare_native_to_name.is_empty()
    }
}

/// Named type declaration
#[derive(Debug, Clone)]
pub struct TypeDef {
    /// The name of the type
    pub name: Ustr,
    /// Optional documentation for the type.
    pub doc: Option<String>,
    /// The generic parameters of this type, if any.
    pub generic_params: Vec<UstrSpan>,
    /// The generic effect parameters accepted by this type constructor.
    pub generic_effect_params: Vec<UstrSpan>,
    /// The inner type data, possibly with generic arguments
    pub shape: TypeScheme<Type>,
    /// Documentation for the declared struct fields or enum variants.
    pub shape_docs: TypeDefShapeDocs,
    /// The location of the type declaration in the source code
    pub span: Location,
    /// The attributes of the type
    pub attributes: Vec<Attribute>,
    /// The default enum variant for `Default`, if any.
    pub default_variant: Option<Ustr>,
    /// Whether this type constructor has an explicit, non-derived `Value` impl.
    pub has_custom_value_impl: bool,
}

/// Documentation attached to the declared product shape of a struct or enum variant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDefProductDocs {
    Unit,
    Tuple(Vec<Option<String>>),
    Record(Vec<(Ustr, Option<String>)>),
}

impl TypeDefProductDocs {
    pub fn has_docs(&self) -> bool {
        match self {
            Self::Unit => false,
            Self::Tuple(fields) => fields.iter().any(Option::is_some),
            Self::Record(fields) => fields.iter().any(|(_, doc)| doc.is_some()),
        }
    }
}

/// Documentation attached to a declared enum variant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDefVariantDocs {
    pub name: Ustr,
    pub doc: Option<String>,
    pub payload: TypeDefProductDocs,
}

impl TypeDefVariantDocs {
    pub fn has_docs(&self) -> bool {
        self.doc.is_some() || self.payload.has_docs()
    }
}

/// Documentation attached to the declared shape of a named type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDefShapeDocs {
    Struct(TypeDefProductDocs),
    Enum(Vec<TypeDefVariantDocs>),
}

impl TypeDefShapeDocs {
    pub fn has_docs(&self) -> bool {
        match self {
            Self::Struct(product) => product.has_docs(),
            Self::Enum(variants) => variants.iter().any(TypeDefVariantDocs::has_docs),
        }
    }
}

fn write_doc_lines(f: &mut fmt::Formatter, indent: &str, doc: &str) -> fmt::Result {
    for line in doc.split('\n') {
        writeln!(f, "{indent}/// {line}")?;
    }
    Ok(())
}

fn write_product_docs(
    f: &mut fmt::Formatter,
    product: &TypeDefProductDocs,
    ty: Type,
    env: &TypeDisplayEnv<'_, '_>,
    indent: &str,
) -> fmt::Result {
    match product {
        TypeDefProductDocs::Unit => write!(f, ";"),
        TypeDefProductDocs::Tuple(field_docs) => {
            let tuple_fields = ty.data();
            let tuple_fields = tuple_fields.as_tuple().map_or(&[][..], Vec::as_slice);
            writeln!(f, "(")?;
            let field_indent = format!("{indent}    ");
            for (index, field_ty) in tuple_fields.iter().enumerate() {
                if let Some(Some(doc)) = field_docs.get(index) {
                    write_doc_lines(f, &field_indent, doc)?;
                }
                write!(f, "{field_indent}")?;
                field_ty.fmt_with(f, env)?;
                writeln!(f, ",")?;
            }
            write!(f, "{indent})")
        }
        TypeDefProductDocs::Record(field_docs) => {
            let record_fields = ty.data();
            let record_fields = record_fields.as_record().map_or(&[][..], Vec::as_slice);
            writeln!(f, "{{")?;
            let field_indent = format!("{indent}    ");
            for (name, field_ty) in record_fields {
                if let Some(doc) = field_docs
                    .iter()
                    .find_map(|(doc_name, doc)| (*doc_name == *name).then_some(doc))
                    .and_then(Option::as_ref)
                {
                    write_doc_lines(f, &field_indent, doc)?;
                }
                write!(f, "{field_indent}")?;
                write_identifier(f, name.as_str())?;
                write!(f, ": ")?;
                field_ty.fmt_with(f, env)?;
                writeln!(f, ",")?;
            }
            write!(f, "{indent}}}")
        }
    }
}

impl TypeDef {
    pub fn has_private_repr(&self) -> bool {
        self.attributes
            .iter()
            .any(|attribute| attribute.path.0 == ustr(PRIVATE_REPR_ATTRIBUTE))
    }

    pub fn param_names(&self) -> impl ExactSizeIterator<Item = Ustr> + '_ {
        self.generic_params.iter().map(|(name, _)| *name)
    }

    pub fn param_spans(&self) -> impl ExactSizeIterator<Item = Location> + '_ {
        self.generic_params.iter().map(|(_, span)| *span)
    }

    pub fn param_count(&self) -> usize {
        self.generic_params.len()
    }

    pub fn effect_param_count(&self) -> usize {
        self.generic_effect_params.len()
    }

    pub(crate) fn validate(&self) {
        assert_eq!(
            self.param_count(),
            self.shape.ty_quantifiers.len(),
            "Type definition `{}` has {} generic parameters but {} type quantifiers",
            self.name,
            self.param_count(),
            self.shape.ty_quantifiers.len(),
        );
        for (index, quantifier) in self.shape.ty_quantifiers.iter().enumerate() {
            assert_eq!(
                quantifier.name(),
                index as u32,
                "Type definition `{}` has non-canonical type quantifier ordering",
                self.name,
            );
        }
        for (index, param) in self.generic_effect_params.iter().enumerate() {
            let quantifier = EffectVar::new(index as u32);
            assert!(
                self.shape.eff_quantifiers.contains(&quantifier),
                "Type definition `{}` declares effect parameter `{}` but its scheme does not quantify it",
                self.name,
                param.0,
            );
        }
        if let Some(default_variant) = self.default_variant {
            assert!(
                self.is_enum(),
                "Type definition `{}` stores a default variant but is not an enum",
                self.name,
            );
            assert!(
                self.shape
                    .ty
                    .data()
                    .as_variant()
                    .is_some_and(|variants| variants
                        .iter()
                        .any(|(name, _)| *name == default_variant)),
                "Type definition `{}` stores unknown default variant `{default_variant}`",
                self.name,
            );
        }
    }

    pub fn shape_ty(&self) -> Type {
        self.shape.ty
    }

    pub fn instantiated_shape(&self, params: &[Type]) -> Type {
        self.instantiated_shape_with_effects(params, &[])
    }

    pub fn instantiated_shape_with_effects(
        &self,
        params: &[Type],
        effect_params: &[EffType],
    ) -> Type {
        assert_eq!(
            params.len(),
            self.param_count(),
            "Type definition `{}` expects {} parameters, got {}",
            self.name,
            self.param_count(),
            params.len(),
        );
        assert_eq!(
            effect_params.len(),
            self.effect_param_count(),
            "Type definition `{}` expects {} effect parameters, got {}",
            self.name,
            self.effect_param_count(),
            effect_params.len(),
        );
        let ty_subst = self
            .shape
            .ty_quantifiers
            .iter()
            .copied()
            .zip(params.iter().copied())
            .collect();
        let eff_subst = self
            .generic_effect_params
            .iter()
            .enumerate()
            .map(|(index, _)| EffectVar::new(index as u32))
            .zip(effect_params.iter().cloned())
            .collect();
        instantiate_type(self.shape.ty, &(ty_subst, eff_subst))
    }

    pub fn payload_scheme(&self, tag: Option<Ustr>) -> TypeScheme<Type> {
        let ty = if let Some(tag) = tag {
            *self
                .shape
                .ty
                .data()
                .as_variant()
                .unwrap()
                .iter()
                .find_map(|(name, ty)| if *name == tag { Some(ty) } else { None })
                .unwrap_or_else(|| panic!("Variant `{tag}` not found in `{}`", self.name))
        } else {
            self.shape.ty
        };
        TypeScheme {
            ty_quantifiers: self.shape.ty_quantifiers.clone(),
            eff_quantifiers: self.shape.eff_quantifiers.clone(),
            ty,
            constraints: self.shape.constraints.clone(),
        }
    }

    pub fn is_enum(&self) -> bool {
        self.shape.ty.data().is_variant()
    }

    pub fn is_record_struct(&self) -> bool {
        self.shape.ty.data().is_record()
    }

    pub fn is_tuple_struct(&self) -> bool {
        self.shape.ty.data().is_tuple()
    }

    pub fn is_unit_struct(&self) -> bool {
        self.shape.ty == Type::unit()
    }

    pub fn is_struct_like(&self) -> bool {
        self.is_record_struct() || self.is_tuple_struct() || self.is_unit_struct()
    }

    pub fn format_details(&self, env: &ModuleEnv<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(doc) = &self.doc {
            for line in doc.split('\n') {
                writeln!(f, "/// {line}")?;
            }
        }
        if self.is_struct_like() {
            write!(f, "struct")?;
        } else {
            write!(f, "enum")?;
        }
        write!(f, " ")?;
        write_identifier(f, self.name.as_str())?;
        let type_params = self
            .generic_params
            .iter()
            .map(|(name, _)| escape_identifier(name.as_str()))
            .collect::<Vec<_>>();
        let effect_params = self
            .generic_effect_params
            .iter()
            .map(|(name, _)| escape_identifier(name.as_str()))
            .collect::<Vec<_>>();
        if let Some(generic_params) = format_generic_param_list(&type_params, &effect_params) {
            write!(f, "{generic_params}")?;
        }
        let ty_var_names = self
            .shape
            .display_ty_var_names_with_source_params(&self.generic_params);
        let eff_var_names = self
            .shape
            .display_eff_var_names_with_source_params(&self.generic_effect_params);
        let type_env = self
            .shape
            .type_display_env(env, &ty_var_names)
            .with_eff_var_names(&eff_var_names);
        if !self.shape.constraints.is_empty() {
            write!(f, " ")?;
            self.shape.format_constraints_with_type_env(f, &type_env)?;
        }
        if self.shape_docs.has_docs() {
            write!(f, " ")?;
            match &self.shape_docs {
                TypeDefShapeDocs::Struct(product) => {
                    write_product_docs(f, product, self.shape.ty, &type_env, "")?;
                }
                TypeDefShapeDocs::Enum(variant_docs) => {
                    writeln!(f, "{{")?;
                    if let Some(variants) = self.shape.ty.data().as_variant() {
                        for (name, ty) in variants {
                            let docs = variant_docs.iter().find(|docs| docs.name == *name);
                            if let Some(Some(doc)) = docs.map(|docs| docs.doc.as_ref()) {
                                write_doc_lines(f, "    ", doc)?;
                            }
                            write!(f, "    ")?;
                            write_identifier(f, name.as_str())?;
                            if let Some(docs) = docs
                                && docs.payload.has_docs()
                            {
                                if matches!(docs.payload, TypeDefProductDocs::Record(_)) {
                                    write!(f, " ")?;
                                }
                                write_product_docs(f, &docs.payload, *ty, &type_env, "    ")?;
                                writeln!(f, ",")?;
                            } else if *ty == Type::unit() {
                                writeln!(f, ",")?;
                            } else {
                                write!(f, " ")?;
                                ty.fmt_with(f, &type_env)?;
                                writeln!(f, ",")?;
                            }
                        }
                    }
                    write!(f, "}}")?;
                }
            }
            return Ok(());
        }
        write!(f, " ")?;
        if self.is_enum() {
            write!(f, "{{ ")?;
            if self.shape.ty != Type::never() {
                for (i, (name, ty)) in self
                    .shape
                    .ty
                    .data()
                    .as_variant()
                    .unwrap()
                    .iter()
                    .enumerate()
                {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    if *ty == Type::unit() {
                        write_identifier(f, name.as_str())?;
                    } else {
                        write_identifier(f, name.as_str())?;
                        write!(f, " ")?;
                        ty.fmt_with(f, &type_env)?;
                    }
                }
            }
            write!(f, " }}")?;
        } else {
            self.shape.ty.fmt_with(f, &type_env)?;
        }
        Ok(())
    }
}

/// Header metadata kept only while a recursive type definition slot is reserved.
#[derive(Debug, Clone)]
pub(crate) struct TypeDefHeader {
    name: Ustr,
    generic_params: Vec<UstrSpan>,
    generic_effect_params: Vec<UstrSpan>,
    span: Location,
}

impl TypeDefHeader {
    fn new(
        name: Ustr,
        generic_params: Vec<UstrSpan>,
        generic_effect_params: Vec<UstrSpan>,
        span: Location,
    ) -> Self {
        Self {
            name,
            generic_params,
            generic_effect_params,
            span,
        }
    }
}

/// Module-owned type definition slot, reserved before recursive SCCs are filled.
#[derive(Debug, Clone)]
pub(crate) enum TypeDefSlot {
    Reserved(TypeDefHeader),
    Resolved(TypeDef),
}

impl TypeDefSlot {
    pub(crate) fn resolved(def: TypeDef) -> Self {
        def.validate();
        Self::Resolved(def)
    }

    pub(crate) fn reserved(
        name: Ustr,
        generic_params: Vec<UstrSpan>,
        generic_effect_params: Vec<UstrSpan>,
        span: Location,
    ) -> Self {
        Self::Reserved(TypeDefHeader::new(
            name,
            generic_params,
            generic_effect_params,
            span,
        ))
    }

    pub(crate) fn fill(&mut self, def: TypeDef) {
        let Self::Reserved(header) = self else {
            panic!("Type definition `{}` was already filled", self.name())
        };
        assert_eq!(header.name, def.name);
        assert_eq!(header.generic_params, def.generic_params);
        assert_eq!(header.generic_effect_params, def.generic_effect_params);
        assert_eq!(header.span, def.span);
        def.validate();
        *self = Self::Resolved(def);
    }

    pub(crate) fn name(&self) -> Ustr {
        match self {
            Self::Reserved(header) => header.name,
            Self::Resolved(def) => def.name,
        }
    }

    pub(crate) fn generic_params(&self) -> &[UstrSpan] {
        match self {
            Self::Reserved(header) => &header.generic_params,
            Self::Resolved(def) => &def.generic_params,
        }
    }

    pub(crate) fn generic_effect_params(&self) -> &[UstrSpan] {
        match self {
            Self::Reserved(header) => &header.generic_effect_params,
            Self::Resolved(def) => &def.generic_effect_params,
        }
    }

    pub(crate) fn param_names(&self) -> impl ExactSizeIterator<Item = Ustr> + '_ {
        self.generic_params().iter().map(|(name, _)| *name)
    }

    pub(crate) fn param_spans(&self) -> impl ExactSizeIterator<Item = Location> + '_ {
        self.generic_params().iter().map(|(_, span)| *span)
    }

    pub(crate) fn effect_param_count(&self) -> usize {
        self.generic_effect_params().len()
    }

    pub(crate) fn span(&self) -> Location {
        match self {
            Self::Reserved(header) => header.span,
            Self::Resolved(def) => def.span,
        }
    }

    pub(crate) fn def(&self) -> &TypeDef {
        match self {
            Self::Resolved(def) => def,
            Self::Reserved(header) => {
                panic!(
                    "Type definition `{}` was used before its declaration was filled",
                    header.name
                )
            }
        }
    }
}

/// A named type, possibly with type arguments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NamedType {
    /// The type declaration reference
    pub def: TypeDefId,
    /// The type arguments for this named type to replace its generic variables
    pub params: Vec<Type>,
    /// The effect arguments for this named type to replace its generic effect variables
    pub effect_params: Vec<EffType>,
    // TODO: add constraints for the type arguments
}

impl NamedType {
    pub fn instantiated_shape(&self, env: &ModuleEnv<'_>) -> Type {
        env.type_def(self.def)
            .instantiated_shape_with_effects(&self.params, &self.effect_params)
    }
}

/// The representation of a type in the system
#[derive(Debug, Clone, PartialEq, Eq, Hash, EnumAsInner)]
pub enum TypeKind {
    /// A type variable, to be used in generics context.
    /// Its parameter is its identity in the context considered, as it is bound.
    Variable(TypeVar), // TODO: add bounds
    /// A native type implemented in Rust, possibly with generics
    Native(B<NativeType>),
    /// Tagged union sum type
    Variant(Vec<(Ustr, Type)>),
    /// Position-based product type
    Tuple(Vec<Type>),
    /// Named product type
    Record(Vec<(Ustr, Type)>),
    /// A function type
    Function(B<FnType>),
    /// A first-class subscript/projection capability type
    Subscript(B<SubscriptType>),
    /// A named newtype, with its instantiated type-arguments
    Named(NamedType),
    /// Bottom type
    Never,
}
// TODO: traits as bounds of generics

/// Return the Cartesian product of all values of each element type, stored as
/// `LiteralValue::Tuple` entries, or `None` if any element is not enumerable or the
/// total cardinality exceeds `max_cardinality`.
fn cartesian_product_values(
    element_types: impl Iterator<Item = Type>,
    max_cardinality: usize,
) -> Option<Vec<LiteralValue>> {
    let mut cardinality = 1usize;
    let element_values = element_types
        .map(|ty| {
            let all_values = ty.data().all_values()?;
            cardinality = cardinality.saturating_mul(all_values.len());
            Some(all_values)
        })
        .collect::<Option<Vec<_>>>()?;
    if cardinality > max_cardinality {
        return None;
    }
    let mut result = vec![vec![]];
    for pool in element_values {
        let mut new_result = Vec::with_capacity(result.len() * pool.len());
        for prefix in &result {
            for item in &pool {
                let mut new_prefix = prefix.clone();
                new_prefix.push(item.clone());
                new_result.push(new_prefix);
            }
        }
        result = new_result;
    }
    Some(result.into_iter().map(LiteralValue::new_tuple).collect())
}

impl TypeKind {
    /// Store in the type system and return a type identifier
    pub fn store(self) -> Type {
        store_type(self)
    }

    /// Return true if the type variable is only found in variant payload positions.
    pub fn is_ty_var_only_in_variants(&self, ty_var: TypeVar, env: &ModuleEnv<'_>) -> bool {
        fn go_kind(
            ty: &TypeKind,
            ty_var: TypeVar,
            env: &ModuleEnv<'_>,
            seen_named: &mut FxHashSet<TypeDefId>,
            in_variant: bool,
        ) -> bool {
            match ty {
                TypeKind::Variable(var) => *var != ty_var || in_variant,
                TypeKind::Native(native) => native
                    .arguments
                    .iter()
                    .all(|arg| go(*arg, ty_var, env, seen_named, in_variant)),
                TypeKind::Variant(variants) => variants
                    .iter()
                    .all(|(_, payload)| go(*payload, ty_var, env, seen_named, true)),
                TypeKind::Tuple(items) => items
                    .iter()
                    .all(|item| go(*item, ty_var, env, seen_named, in_variant)),
                TypeKind::Record(fields) => fields
                    .iter()
                    .all(|(_, field)| go(*field, ty_var, env, seen_named, in_variant)),
                TypeKind::Function(function) => {
                    function
                        .args
                        .iter()
                        .all(|arg| go(arg.ty, ty_var, env, seen_named, in_variant))
                        && go(function.ret, ty_var, env, seen_named, in_variant)
                }
                TypeKind::Subscript(subscript) => {
                    subscript
                        .args
                        .iter()
                        .all(|arg| go(arg.ty, ty_var, env, seen_named, in_variant))
                        && go(subscript.ret, ty_var, env, seen_named, in_variant)
                }
                TypeKind::Named(named) => {
                    if in_variant {
                        return true;
                    }
                    if !seen_named.insert(named.def) {
                        return true;
                    }
                    let type_def = env.type_def(named.def);
                    let result = named.params.iter().zip(&type_def.shape.ty_quantifiers).all(
                        |(param, quantifier)| {
                            !param.contains_any_type_var(ty_var)
                                || go(type_def.shape.ty, *quantifier, env, seen_named, false)
                        },
                    );
                    seen_named.remove(&named.def);
                    result
                }
                TypeKind::Never => true,
            }
        }

        fn go(
            ty: Type,
            ty_var: TypeVar,
            env: &ModuleEnv<'_>,
            seen_named: &mut FxHashSet<TypeDefId>,
            in_variant: bool,
        ) -> bool {
            go_kind(&ty.data(), ty_var, env, seen_named, in_variant)
        }

        go_kind(self, ty_var, env, &mut FxHashSet::default(), false)
    }

    /// Apply f recursively to content
    pub fn map(&self, f: &mut impl TypeMapper) -> Type {
        use TypeKind::*;
        match self {
            Variable(var) => Type::variable(*var),
            Native(native_ty) => Type::native_type(NativeType::new(
                native_ty.bare_ty.clone(),
                native_ty
                    .arguments
                    .iter()
                    .map(|ty| ty.map(f))
                    .collect::<Vec<_>>(),
            )),
            Variant(types) => Type::variant(
                types
                    .iter()
                    .map(|(name, ty)| (*name, ty.map(f)))
                    .collect::<Vec<_>>(),
            ),
            Tuple(tuple) => Type::tuple(tuple.iter().map(|ty| ty.map(f)).collect::<Vec<_>>()),
            Record(fields) => Type::record(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, ty.map(f)))
                    .collect::<Vec<_>>(),
            ),
            Function(fn_type) => Type::function_type(fn_type.map(f)),
            Subscript(subscript) => Type::subscript_type(subscript.map(f)),
            Named(NamedType {
                def: decl,
                params: args,
                effect_params,
            }) => Type::named_with_effects(
                *decl,
                args.iter().map(|ty| ty.map(f)).collect::<Vec<_>>(),
                effect_params
                    .iter()
                    .map(|eff| f.map_effect_type(eff))
                    .collect::<Vec<_>>(),
            ),
            Never => Type::never(),
        }
    }

    /// Visit this type, allowing for multiple traversal strategies thanks to the TypeInnerVisitor trait.
    pub fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
        // helper for doing cycle detection on type
        fn process_ty(ty: Type, visitor: &mut impl TypeInnerVisitor) {
            ty.with_cycle_detection(|ty, visitor| ty.data().visit(visitor), |_, _| (), visitor)
        }

        // start visit
        visitor.visit_ty_kind_start(self);

        // recurse
        use TypeKind::*;
        match self {
            Variable(_) | Never => (),
            Native(native) => native
                .arguments
                .iter()
                .for_each(|ty| process_ty(*ty, visitor)),
            Variant(types) => types.iter().for_each(|(_, ty)| process_ty(*ty, visitor)),
            Tuple(types) => types.iter().for_each(|ty| process_ty(*ty, visitor)),
            Record(fields) => fields.iter().for_each(|(_, ty)| process_ty(*ty, visitor)),
            Function(fn_type) => fn_type.visit(visitor),
            Subscript(subscript) => subscript.visit(visitor),
            Named(NamedType {
                params: args,
                effect_params,
                ..
            }) => {
                args.iter().for_each(|ty| process_ty(*ty, visitor));
                effect_params
                    .iter()
                    .for_each(|eff| visitor.visit_eff_ty(eff));
            }
        };

        // process self
        visitor.visit_ty_kind_end(self);
    }

    #[inline]
    fn for_each_inner_type(&self, mut f: impl FnMut(Type)) {
        use TypeKind::*;
        match self {
            Native(g) => {
                for &ty in &g.arguments {
                    f(ty);
                }
            }
            Variable(_) | Never => {}
            Variant(types) => {
                for (_, ty) in types {
                    f(*ty);
                }
            }
            Tuple(types) => {
                for &ty in types {
                    f(ty);
                }
            }
            Record(fields) => {
                for (_, ty) in fields {
                    f(*ty);
                }
            }
            Function(function) => {
                for arg in &function.args {
                    f(arg.ty);
                }
                f(function.ret);
            }
            Subscript(subscript) => {
                for arg in &subscript.args {
                    f(arg.ty);
                }
                f(subscript.ret);
            }
            Named(NamedType { params, .. }) => {
                for &ty in params {
                    f(ty);
                }
            }
        }
    }

    #[inline]
    pub(crate) fn for_each_inner_type_mut(&mut self, mut f: impl FnMut(&mut Type)) {
        use TypeKind::*;
        match self {
            Native(g) => {
                for ty in &mut g.arguments {
                    f(ty);
                }
            }
            Variable(_) | Never => {}
            Variant(types) => {
                for (_, ty) in types {
                    f(ty);
                }
            }
            Tuple(types) => {
                for ty in types {
                    f(ty);
                }
            }
            Record(fields) => {
                for (_, ty) in fields {
                    f(ty);
                }
            }
            Function(function) => {
                for arg in &mut function.args {
                    f(&mut arg.ty);
                }
                f(&mut function.ret);
            }
            Subscript(subscript) => {
                for arg in &mut subscript.args {
                    f(&mut arg.ty);
                }
                f(&mut subscript.ret);
            }
            Named(named) => {
                for ty in &mut named.params {
                    f(ty);
                }
            }
        }
    }

    fn recursive_worlds_if_no_local_refs(&self) -> Option<SVec2<NonMaxU32>> {
        let mut worlds_to_check = SVec2::new();
        let mut has_local_ref = false;
        self.for_each_inner_type(|ty| {
            if has_local_ref {
                return;
            }
            if ty.is_local() {
                has_local_ref = true;
                return;
            }
            if ty.is_global_recursive() {
                let world = ty.world().unwrap();
                // Adjacent-dedup, matching the previous itertools::dedup behaviour.
                if worlds_to_check.last() != Some(&world) {
                    worlds_to_check.push(world);
                }
            }
        });
        (!has_local_ref).then_some(worlds_to_check)
    }

    fn local_cmp(&self, other: &Self) -> Ordering {
        use TypeKind::*;
        match (self, other) {
            // Compare the raw pointers (addresses) of the weak references
            (Native(a), Native(b)) => a.local_cmp(b),
            (Variable(a), Variable(b)) => a.cmp(b),
            (Variant(a), Variant(b)) => compare_by(a, b, |(a_s, a_t), (b_s, b_t)| {
                a_s.cmp(b_s).then(a_t.local_cmp(b_t))
            }),
            (Tuple(a), Tuple(b)) => compare_by(a, b, Type::local_cmp),
            (Record(a), Record(b)) => compare_by(a, b, |(a_s, a_t), (b_s, b_t)| {
                a_s.cmp(b_s).then(a_t.local_cmp(b_t))
            }),
            (Function(a), Function(b)) => a.local_cmp(b),
            (Subscript(a), Subscript(b)) => a.local_cmp(b),
            _ => self.rank().cmp(&other.rank()),
        }
    }

    /// Substitute the indices of local types using `subst`, where
    /// `subst[i]` is the new index for local type `i`. A value of
    /// `u32::MAX` means "not in this substitution" and panics if reached.
    fn substitute_locals(&mut self, subst: &[u32]) {
        self.for_each_inner_type_mut(|ty| {
            if ty.world().is_none() {
                let mapped = subst.get(ty.index as usize).copied().unwrap_or(u32::MAX);
                if mapped == u32::MAX {
                    panic!(
                        "Local type index {} not found in substitution {subst:?}",
                        ty.index
                    );
                }
                ty.index = mapped;
            }
        });
    }

    // helper functions
    fn rank(&self) -> usize {
        use TypeKind::*;
        match self {
            Native(_) => 1,
            Variable(_) => 2,
            Variant(_) => 3,
            Tuple(_) => 4,
            Record(_) => 5,
            Function(_) => 6,
            Subscript(_) => 7,
            Named(_) => 8,
            Never => 9,
        }
    }

    /// Make sure the type is consistent
    fn validate(&self) {
        use TypeKind::*;
        match self {
            Variant(items) => assert_unique_strings(items),
            Record(fields) => assert_unique_strings(fields),
            _ => (),
        }
    }

    /// Normalize the types: sort variant and record fields
    fn normalize(&mut self) {
        self.validate();
        use TypeKind::*;
        match self {
            Variant(items) => items.sort_by_key(|(a, _)| *a),
            Record(fields) => fields.sort_by_key(|a| a.0),
            _ => (),
        }
    }

    /// If all values can be exhaustively enumerated, return them,
    pub fn all_values(&self) -> Option<Vec<LiteralValue>> {
        // The maximum cardinality for a type to agree to be enumerated
        const MAX_CARDINALITY: usize = 1000;
        use TypeKind::*;
        match self {
            Native(native) => {
                if native.arguments.is_empty() {
                    if native.bare_ty == bare_native_type::<()>() {
                        Some(vec![LiteralValue::new_native(())])
                    } else if native.bare_ty == bare_native_type::<bool>() {
                        Some(vec![
                            LiteralValue::new_native(false),
                            LiteralValue::new_native(true),
                        ])
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Tuple(elements) => cartesian_product_values(elements.iter().copied(), MAX_CARDINALITY),
            Record(fields) => {
                // Records are stored as tuples (fields sorted alphabetically), so
                // we enumerate the Cartesian product of field values the same way.
                cartesian_product_values(fields.iter().map(|(_, ty)| *ty), MAX_CARDINALITY)
            }
            Never => Some(vec![]),
            _ => None,
        }
    }
}

impl FormatWith<ModuleEnv<'_>> for TypeKind {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        fmt_type_kind_with_env(self, f, env)
    }
}

impl FormatWith<TypeDisplayEnv<'_, '_>> for TypeKind {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &TypeDisplayEnv<'_, '_>) -> fmt::Result {
        fmt_type_kind_with_env(self, f, env)
    }
}

impl FormatWith<QualifiedNameEnv<'_>> for TypeKind {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &QualifiedNameEnv<'_>) -> fmt::Result {
        fmt_type_kind_with_qualified_name_env(self, f, env)
    }
}

fn fmt_type_kind_with_env<Env>(kind: &TypeKind, f: &mut fmt::Formatter, env: &Env) -> fmt::Result
where
    Env: TypeFormatEnv,
    FnType: FormatWith<Env>,
    NativeType: FormatWith<Env>,
    SubscriptType: FormatWith<Env>,
    Type: FormatWith<Env>,
{
    use TypeKind::*;
    match kind {
        Variable(var) => env.fmt_type_var(*var, f),
        Native(native) => native.fmt_with(f, env),
        Variant(types) => {
            for (i, (name, ty)) in types.iter().enumerate() {
                if i > 0 {
                    write!(f, " | ")?;
                }
                if *ty == Type::unit() {
                    write_identifier(f, name.as_str())?;
                } else {
                    write_identifier(f, name.as_str())?;
                    write!(f, " ")?;
                    let ty_data = ty.data();
                    if let Tuple(tuple_ty) = &*ty_data {
                        if tuple_ty.len() == 1 {
                            // Special case to avoid the (X,) syntax for single-element tuples.
                            write!(f, "(")?;
                            tuple_ty[0].fmt_with(f, env)?;
                            write!(f, ")")?;
                        } else {
                            ty.fmt_with(f, env)?;
                        }
                    } else {
                        ty.fmt_with(f, env)?;
                    }
                }
            }
            Ok(())
        }
        Tuple(elements) => {
            write!(f, "(")?;
            for (i, ty) in elements.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                ty.fmt_with(f, env)?;
                if elements.len() == 1 {
                    write!(f, ",")?;
                }
            }
            write!(f, ")")
        }
        Record(fields) => {
            write!(f, "{{ ")?;
            for (i, (name, ty)) in fields.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write_identifier(f, name.as_str())?;
                write!(f, ": ")?;
                ty.fmt_with(f, env)?;
            }
            write!(f, " }}")
        }
        Function(function) => function.fmt_with(f, env),
        Subscript(subscript) => subscript.fmt_with(f, env),
        Named(NamedType {
            def,
            params: args,
            effect_params: _,
        }) if *def == array_type_def() && args.len() == 1 => {
            write!(f, "[")?;
            args[0].fmt_with(f, env)?;
            write!(f, "]")
        }
        Named(NamedType {
            def,
            params: args,
            effect_params,
        }) => {
            match env.module_env().try_type_def_name(*def) {
                Some(name) => write!(f, "{name}")?,
                None => write!(f, "#{}:{}", def.module, def.index)?,
            }
            let displayed_effect_params = effect_params
                .iter()
                .map(|eff| env.displayed_effects(eff))
                .collect::<Vec<_>>();
            let display_effect_params = !displayed_effect_params.is_empty()
                && (!env.is_light_effect_display()
                    || displayed_effect_params.iter().any(EffType::any));
            if !args.is_empty() || display_effect_params {
                write!(f, "<")?;
                for (i, ty) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    ty.fmt_with(f, env)?;
                }
                if display_effect_params {
                    if !args.is_empty() {
                        write!(f, " ")?;
                    }
                    write!(f, "! ")?;
                    for (i, eff) in displayed_effect_params.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        format_effect_binding_value_with_env(eff, f, env)?;
                    }
                }
                write!(f, ">")?;
            }
            Ok(())
        }
        Never => write!(f, "never"),
    }
}

fn fmt_type_kind_with_qualified_name_env(
    kind: &TypeKind,
    f: &mut fmt::Formatter,
    env: &QualifiedNameEnv<'_>,
) -> fmt::Result {
    use TypeKind::*;
    match kind {
        Variable(var) => write!(f, "{var}"),
        Native(native) => native.fmt_with(f, env),
        Variant(types) => {
            for (i, (name, ty)) in types.iter().enumerate() {
                if i > 0 {
                    write!(f, " | ")?;
                }
                write_identifier(f, name.as_str())?;
                if *ty != Type::unit() {
                    write!(f, " ")?;
                    let ty_data = ty.data();
                    if let Tuple(tuple_ty) = &*ty_data {
                        if tuple_ty.len() == 1 {
                            write!(f, "(")?;
                            tuple_ty[0].fmt_with(f, env)?;
                            write!(f, ")")?;
                        } else {
                            ty.fmt_with(f, env)?;
                        }
                    } else {
                        ty.fmt_with(f, env)?;
                    }
                }
            }
            Ok(())
        }
        Tuple(elements) => {
            write!(f, "(")?;
            for (i, ty) in elements.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                ty.fmt_with(f, env)?;
                if elements.len() == 1 {
                    write!(f, ",")?;
                }
            }
            write!(f, ")")
        }
        Record(fields) => {
            write!(f, "{{ ")?;
            for (i, (name, ty)) in fields.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write_identifier(f, name.as_str())?;
                write!(f, ": ")?;
                ty.fmt_with(f, env)?;
            }
            write!(f, " }}")
        }
        Function(function) => function.fmt_with(f, env),
        Subscript(subscript) => subscript.fmt_with(f, env),
        Named(NamedType {
            def,
            params: args,
            effect_params: _,
        }) if *def == array_type_def() && args.len() == 1 => {
            write!(f, "[")?;
            args[0].fmt_with(f, env)?;
            write!(f, "]")
        }
        Named(NamedType {
            def,
            params: args,
            effect_params,
        }) => {
            write!(f, "{}", env.format_type_def_id(*def))?;
            if !args.is_empty() || !effect_params.is_empty() {
                write!(f, "<")?;
                for (i, ty) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    ty.fmt_with(f, env)?;
                }
                if !effect_params.is_empty() {
                    if !args.is_empty() {
                        write!(f, " ")?;
                    }
                    write!(f, "! ")?;
                    for (i, eff) in effect_params.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        format_effect_binding_value(eff, f)?;
                    }
                }
                write!(f, ">")?;
            }
            Ok(())
        }
        Never => write!(f, "never"),
    }
}

impl Ord for TypeKind {
    fn cmp(&self, other: &Self) -> Ordering {
        use TypeKind::*;
        match (self, other) {
            // Compare the raw pointers (addresses) of the weak references
            (Native(a), Native(b)) => a.cmp(b),
            (Variable(a), Variable(b)) => a.cmp(b),
            (Variant(a), Variant(b)) => a.cmp(b),
            (Tuple(a), Tuple(b)) => a.cmp(b),
            (Record(a), Record(b)) => a.cmp(b),
            (Function(a), Function(b)) => a.args.cmp(&b.args).then_with(|| a.ret.cmp(&b.ret)),
            (Subscript(a), Subscript(b)) => a
                .args
                .cmp(&b.args)
                .then_with(|| a.ret.cmp(&b.ret))
                .then_with(|| a.ref_member.cmp(&b.ref_member))
                .then_with(|| a.mut_member.cmp(&b.mut_member)),
            _ => self.rank().cmp(&other.rank()),
        }
    }
}

impl PartialOrd for TypeKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl graph::Node for TypeKind {
    // A position, because every consumer of these components indexes `kinds`, `resolved` and
    // `subst_to_local` with them.
    type Index = usize;

    fn neighbors(&self) -> impl Iterator<Item = Self::Index> {
        let mut neighbors = Vec::new();
        self.for_each_inner_type(|ty| {
            if ty.is_local() {
                neighbors.push(ty.index() as usize);
            }
        });
        neighbors.into_iter()
    }
}

/// A set of types representing a "world" of types,
/// i.e. a collection of types that can reference each other.
/// Positions follow insertion order, so the hasher never affects which index a type receives.
type TypeWorld = IndexSet<InternedType, FxBuildHasher>;

/// Cached set of free variables of an interned type, used to short-circuit  substitutions that cannot affect the type.
/// Computed once per interned type at insertion time and stored alongside its `TypeKind` in `InternedType`.
#[derive(Debug, Clone, Default)]
pub struct TypeSummary {
    pub free_ty_vars: KindVarSet<TypeVar>,
    pub free_mut_vars: KindVarSet<MutVar>,
    pub free_eff_vars: KindVarSet<EffectVar>,
}

/// An interned type entry: a `TypeKind` paired with its cached free-variable summary.
#[derive(Debug, Clone)]
pub struct InternedType {
    pub kind: TypeKind,
    pub summary: TypeSummary,
}

impl Hash for InternedType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
    }
}

impl PartialEq for InternedType {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}
impl Eq for InternedType {}

impl Borrow<TypeKind> for InternedType {
    fn borrow(&self) -> &TypeKind {
        &self.kind
    }
}

/// Candidate key preserving constructor attributes and world-0 children. A local
/// cyclic node cannot equal a canonical world-0 node, so those IDs safely narrow
/// the search. Erase BOTH local and stored recursive children: an incoming SCC
/// may refer to an existing recursive node where the stored graph has a cycle edge.
fn recursive_candidate_signature(kind: &TypeKind) -> TypeKind {
    let mut signature = kind.clone();
    signature.for_each_inner_type_mut(|ty| {
        if ty.is_local() || ty.is_global_recursive() {
            *ty = Type::new_local(0);
        }
    });
    signature
}

/// Minimize a recursive component by bisimulation, treating already-canonical
/// global children as distinct constants. The caller first checks whether this
/// component maps into stored types: if any node of an SCC equals a stored type,
/// following its local edges supplies stored representatives for the entire SCC.
/// Consequently, when that check fails, no local node can equal a global child.
///
/// Initial blocks agree on every constructor attribute and global child. Refine
/// them by ordered local-child edges, using predecessor lists and the smaller-half
/// splitter rule. Each edge participates in O(log n) splitters; no unfolding or
/// permutation search is needed. Return the quotient and an original-to-quotient
/// map, including an entry for every duplicate input node.
fn minimize_recursive_component(kinds: &[TypeKind]) -> (Vec<TypeKind>, Vec<u32>) {
    let mut signatures = FxHashMap::default();
    let mut blocks: Vec<Vec<usize>> = Vec::new();
    let mut classes = vec![0; kinds.len()];
    let mut positions = vec![0; kinds.len()];
    let mut predecessors = vec![Vec::new(); kinds.len()];
    for (node, kind) in kinds.iter().enumerate() {
        let mut signature = kind.clone();
        let mut edge = 0;
        signature.for_each_inner_type_mut(|ty| {
            if ty.is_local() {
                predecessors[ty.index() as usize].push((node, edge));
                *ty = Type::new_local(0);
            }
            edge += 1;
        });
        let next_class = blocks.len();
        let class = *signatures.entry(signature).or_insert(next_class);
        if class == blocks.len() {
            blocks.push(Vec::new());
        }
        classes[node] = class;
        positions[node] = blocks[class].len();
        blocks[class].push(node);
    }

    let mut pending: Vec<_> = (0..blocks.len()).collect();
    let mut queued = DenseBitSet::with_capacity(blocks.len());
    for class in 0..blocks.len() {
        queued.insert(class);
    }
    while let Some(splitter) = pending.pop() {
        queued.remove(splitter);
        // Snapshot all predecessor sets before splitting: the splitter itself
        // may be split while processing one of these edge positions.
        let mut by_edge: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        for &target in &blocks[splitter] {
            for &(source, edge) in &predecessors[target] {
                by_edge.entry(edge).or_default().push(source);
            }
        }
        for sources in by_edge.into_values() {
            let mut affected: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
            for source in sources {
                affected.entry(classes[source]).or_default().push(source);
            }
            for (class, members) in affected {
                if members.len() == blocks[class].len() {
                    continue;
                }
                let new_class = blocks.len();
                for (position, &node) in members.iter().enumerate() {
                    let old_position = positions[node];
                    blocks[class].swap_remove(old_position);
                    if let Some(&moved) = blocks[class].get(old_position) {
                        positions[moved] = old_position;
                    }
                    classes[node] = new_class;
                    positions[node] = position;
                }
                blocks.push(members);
                // If the old block is pending, both halves must be processed.
                // Otherwise its previous processing lets us use the smaller half.
                let enqueue =
                    if queued.contains(class) || blocks[new_class].len() < blocks[class].len() {
                        new_class
                    } else {
                        class
                    };
                queued.insert(enqueue);
                pending.push(enqueue);
            }
        }
    }

    // Refinement may visit hash buckets in any order. Number the final classes
    // by first input occurrence so neither their IDs nor representative selection
    // depend on hashing (including differences between 32- and 64-bit targets).
    let mut class_to_quotient = vec![None; blocks.len()];
    let mut representatives = Vec::with_capacity(blocks.len());
    let mapping: Vec<_> = classes
        .into_iter()
        .enumerate()
        .map(|(node, class)| {
            *class_to_quotient[class].get_or_insert_with(|| {
                let index = representatives.len() as u32;
                representatives.push(node);
                index
            })
        })
        .collect();
    let quotient = representatives
        .into_iter()
        .map(|node| {
            let mut kind = kinds[node].clone();
            kind.substitute_locals(&mapping);
            kind
        })
        .collect();
    (quotient, mapping)
}

/// The type universe, containing all known types organized in worlds.
///
/// Invariant: distinct published IDs denote inequivalent infinite unfoldings
/// (ordered-child bisimulation), across ALL worlds. Published IDs never change.
/// World 0 contains non-recursive nodes: none participates in a cycle, although
/// a node may contain a recursive type and thus have an infinite unfolding.
/// Each other world is a minimal strongly connected component of recursive nodes.
///
/// Canonical child IDs make exact hash-consing sufficient for world 0, including
/// reuse of recursive nodes through their immediate children's worlds. The same
/// invariant makes forced recursive matching complete: conflicting stored targets
/// cannot be equivalent, and an SCC's partner must lie on a stored cycle. Only
/// after matching fails may minimization treat all global children as constants.
#[derive(Debug)]
struct TypeUniverse {
    /// The list of worlds, each being a set of types.
    /// The first world (index 0) is the global non-recursive world.
    /// Subsequent worlds contain SCC of recursive types.
    worlds: Vec<TypeWorld>,
    /// Exact-input cache, including the representative of every duplicate node.
    /// Entries contain stable global IDs and need no inference-dependent invalidation.
    local_to_world: FxHashMap<Vec<TypeKind>, Vec<Type>>,
    /// Stored recursive nodes indexed by constructor attributes and world-0 children.
    recursive_candidates: FxHashMap<TypeKind, Vec<Type>>,
}

impl TypeUniverse {
    fn new_empty() -> Self {
        Self {
            worlds: vec![TypeWorld::default()],
            local_to_world: FxHashMap::default(),
            recursive_candidates: FxHashMap::default(),
        }
    }

    fn insert_type(&mut self, tk: TypeKind) -> Type {
        self.insert_types(&[tk])[0]
    }

    fn insert_non_recursive_kind(
        &mut self,
        kind: &TypeKind,
        worlds_to_check: SVec2<NonMaxU32>,
    ) -> Type {
        // Before adding to world 0, check if this matches an existing recursive type
        // by checking if any recursive type's world contains this exact TypeKind.
        // This handles equirecursive types where an "unfolded" variant equals
        // a canonical recursive type.
        for world_idx in worlds_to_check {
            let world_idx = world_idx.get();
            let world = &self.worlds[world_idx as usize];

            // Check if kind matches any TypeKind in this world
            if let Some((idx, _)) = world.get_full(kind) {
                // Found a match! Return the type from that world
                let resolved_ty = Type::new_global(world_idx, idx as u32);
                assert!(!resolved_ty.is_local());
                return resolved_ty;
            }
        }

        // No match in recursive worlds, add to world 0.
        let index = if let Some((index, _)) = self.worlds[0].get_full(kind) {
            index
        } else {
            // Compute the summary using already-interned children, then store.
            let summary = self.summary_with_global_children(kind);
            self.worlds[0]
                .insert_full(InternedType {
                    kind: kind.clone(),
                    summary,
                })
                .0
        };
        let resolved_ty = Type::new_global(0, index as u32);
        assert!(!resolved_ty.is_local());
        resolved_ty
    }

    /// Find a bisimulation from a local SCC into the canonical stored graph.
    /// Ordered child edges force the entire mapping once a root is chosen. Many
    /// local nodes may map to one stored node; repeated visits to a local node
    /// must agree because distinct stored IDs denote inequivalent types.
    fn match_recursive_component(&self, kinds: &[TypeKind]) -> Option<Vec<Type>> {
        let (root, candidates) = kinds
            .iter()
            .enumerate()
            .map(|(index, kind)| {
                Some((
                    index,
                    self.recursive_candidates
                        .get(&recursive_candidate_signature(kind))?,
                ))
            })
            .collect::<Option<Vec<_>>>()?
            .into_iter()
            .min_by_key(|(_, candidates)| candidates.len())?;
        for &candidate in candidates {
            if let Some(mapping) = self.match_recursive_root(kinds, root, candidate) {
                return Some(mapping);
            }
        }
        None
    }

    fn match_recursive_root(
        &self,
        kinds: &[TypeKind],
        root: usize,
        candidate: Type,
    ) -> Option<Vec<Type>> {
        let mut mapping = vec![None; kinds.len()];
        let mut pending = vec![(root, candidate)];
        while let Some((local, global)) = pending.pop() {
            if let Some(previous) = mapping[local] {
                if previous != global {
                    return None;
                }
                continue;
            }
            mapping[local] = Some(global);
            let existing = self.get_type_data(global);
            let mut children = Vec::new();
            existing.for_each_inner_type(|ty| children.push(ty));
            let mut children = children.into_iter();
            let mut remapped = kinds[local].clone();
            let mut compatible = true;
            remapped.for_each_inner_type_mut(|ty| {
                let Some(child) = children.next() else {
                    compatible = false;
                    return;
                };
                if ty.is_local() {
                    pending.push((ty.index() as usize, child));
                } else if *ty != child {
                    compatible = false;
                }
                *ty = child;
            });
            if !compatible || children.next().is_some() || remapped != *existing {
                return None;
            }
        }
        // Every local node is reachable from the root because this is an SCC.
        Some(mapping.into_iter().map(Option::unwrap).collect())
    }

    /// Intern a strongly connected local graph after its dependencies have been
    /// interned. Matching first makes global references safe constants during
    /// minimization; a quotient of an SCC is again strongly connected.
    fn intern_recursive_component(&mut self, local_world: Vec<TypeKind>) -> Vec<Type> {
        if let Some(mapping) = self.local_to_world.get(&local_world) {
            return mapping.clone();
        }
        if let Some(mapping) = self.match_recursive_component(&local_world) {
            self.local_to_world.insert(local_world, mapping.clone());
            return mapping;
        }

        let (mut quotient, local_to_quotient) = minimize_recursive_component(&local_world);
        let world_index = self.worlds.len() as u32;
        let mapping: Vec<_> = local_to_quotient
            .into_iter()
            .map(|index| Type::new_global(world_index, index))
            .collect();
        for kind in &mut quotient {
            kind.for_each_inner_type_mut(|ty| {
                if ty.is_local() {
                    *ty = Type::new_global(world_index, ty.index());
                }
            });
        }
        let summaries = self.compute_scc_summaries(&quotient, world_index);
        let node_count = quotient.len();
        let world: TypeWorld = quotient
            .into_iter()
            .zip(summaries)
            .map(|(kind, summary)| InternedType { kind, summary })
            .collect();
        assert_eq!(
            world.len(),
            node_count,
            "minimized recursive nodes must be distinct"
        );
        for (index, entry) in world.iter().enumerate() {
            self.recursive_candidates
                .entry(recursive_candidate_signature(&entry.kind))
                .or_default()
                .push(Type::new_global(world_index, index as u32));
        }
        self.worlds.push(world);
        self.local_to_world.insert(local_world, mapping.clone());
        mapping
    }

    fn insert_types(&mut self, kinds: impl Into<Vec<TypeKind>>) -> Vec<Type> {
        let mut kinds: Vec<_> = kinds.into();
        kinds.iter_mut().for_each(TypeKind::normalize);

        if let Some(worlds_to_check) = kinds
            .iter()
            .map(TypeKind::recursive_worlds_if_no_local_refs)
            .collect::<Option<Vec<_>>>()
        {
            let mut types = vec![Type::new_local(0); kinds.len()];
            for input_index in (0..kinds.len()).rev() {
                types[input_index] = self.insert_non_recursive_kind(
                    &kinds[input_index],
                    worlds_to_check[input_index].clone(),
                );
            }
            return types;
        }

        let sorted_sccs = if kinds.len() == 1 {
            vec![vec![0]]
        } else {
            let sccs = find_strongly_connected_components(&kinds);
            let mut sorted = topological_sort_sccs(&kinds, &sccs);
            sorted.reverse();
            sorted
        };
        let mut resolved = vec![None; kinds.len()];
        // Reuse the allocation across components. Previously assigned entries
        // cannot be read: references to those dependencies become global below.
        let mut subst_to_local = vec![u32::MAX; kinds.len()];
        for mut input_indices in sorted_sccs {
            for &input in &input_indices {
                kinds[input].for_each_inner_type_mut(|ty| {
                    if ty.is_local() {
                        if let Some(global) = resolved[ty.index() as usize] {
                            *ty = global;
                        }
                    }
                });
            }
            if input_indices.len() == 1 {
                let input = input_indices[0];
                if let Some(worlds) = kinds[input].recursive_worlds_if_no_local_refs() {
                    resolved[input] = Some(self.insert_non_recursive_kind(&kinds[input], worlds));
                    continue;
                }
            }

            // A stable constructor ordering improves exact-input cache reuse;
            // correctness does not depend on it being a canonical graph ordering.
            input_indices.sort_by(|&a, &b| kinds[a].local_cmp(&kinds[b]));
            for (local, &input) in input_indices.iter().enumerate() {
                subst_to_local[input] = local as u32;
            }
            let local_world = input_indices
                .iter()
                .map(|&input| {
                    let mut kind = kinds[input].clone();
                    kind.substitute_locals(&subst_to_local);
                    kind
                })
                .collect();
            let mapping = self.intern_recursive_component(local_world);
            // Check every input edge, including cached and many-to-one mappings.
            // The independent test oracle checks the stronger uniqueness invariant.
            debug_assert_eq!(mapping.len(), input_indices.len());
            #[cfg(debug_assertions)]
            for (&input, &ty) in input_indices.iter().zip(&mapping) {
                let mut expected = kinds[input].clone();
                expected.for_each_inner_type_mut(|child| {
                    if child.is_local() {
                        *child = mapping[subst_to_local[child.index() as usize] as usize];
                    }
                });
                debug_assert_eq!(&expected, self.get_type_data(ty));
            }
            for (input, ty) in input_indices.into_iter().zip(mapping) {
                resolved[input] = Some(ty);
            }
        }
        resolved.into_iter().map(Option::unwrap).collect()
    }

    fn get_type_data(&self, r: Type) -> &TypeKind {
        &self.get_interned(r).kind
    }

    fn get_type_summary(&self, r: Type) -> &TypeSummary {
        &self.get_interned(r).summary
    }

    fn get_interned(&self, r: Type) -> &InternedType {
        self.worlds[r
            .world
            .expect("Attempted to get type data for local world")
            .get() as usize]
            .get_index(r.index as usize)
            .expect("Attempted to get type data for non-existent type")
    }

    /// Compute the free-variable summary of a `TypeKind` whose children are all already interned globally.
    /// Used for non-recursive singletons inserted into world 0.
    fn summary_with_global_children(&self, kind: &TypeKind) -> TypeSummary {
        let mut summary = TypeSummary::default();
        let mut visited = FxHashSet::default();
        self.collect_into_summary(kind, &mut summary, &mut visited, |ty| {
            self.get_interned(ty).summary.clone()
        });
        summary
    }

    /// Compute summaries for an SCC of kinds being added as a new world. Local
    /// references that point into the same SCC (world == `scc_world_idx`) are
    /// resolved against an in-progress `summaries` vector via fixed-point
    /// iteration; references to types in other worlds use the cached summary.
    fn compute_scc_summaries(&self, kinds: &[TypeKind], scc_world_idx: u32) -> Vec<TypeSummary> {
        let n = kinds.len();
        let mut summaries: Vec<TypeSummary> = vec![TypeSummary::default(); n];
        loop {
            let mut changed = false;
            for i in 0..n {
                let mut new_summary = TypeSummary::default();
                let mut visited = FxHashSet::default();
                self.collect_into_summary(&kinds[i], &mut new_summary, &mut visited, |ty| {
                    if ty.world.map(|w| w.get()) == Some(scc_world_idx) {
                        summaries[ty.index as usize].clone()
                    } else {
                        self.get_interned(ty).summary.clone()
                    }
                });
                if !summaries_eq(&new_summary, &summaries[i]) {
                    summaries[i] = new_summary;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        summaries
    }

    /// Generic kind walker that accumulates direct vars into `summary` and
    /// folds in child summaries via `lookup`. Cycles are bounded by `visited`.
    fn collect_into_summary(
        &self,
        kind: &TypeKind,
        summary: &mut TypeSummary,
        visited: &mut FxHashSet<Type>,
        mut lookup: impl FnMut(Type) -> TypeSummary,
    ) {
        use TypeKind::*;
        match kind {
            Variable(v) => summary.free_ty_vars.insert(*v),
            Function(fn_ty) => {
                for arg in &fn_ty.args {
                    if let Some(var) = arg.mut_ty.as_variable() {
                        summary.free_mut_vars.insert(*var);
                    }
                    self.fold_child(arg.ty, summary, visited, &mut lookup);
                }
                for eff in fn_ty.effects.iter() {
                    if let Some(var) = eff.as_variable() {
                        summary.free_eff_vars.insert(*var);
                    }
                }
                self.fold_child(fn_ty.ret, summary, visited, &mut lookup);
            }
            Subscript(subscript) => {
                for arg in &subscript.args {
                    if let Some(var) = arg.mut_ty.as_variable() {
                        summary.free_mut_vars.insert(*var);
                    }
                    self.fold_child(arg.ty, summary, visited, &mut lookup);
                }
                for member in subscript.members() {
                    for eff in member.effects.iter() {
                        if let Some(var) = eff.as_variable() {
                            summary.free_eff_vars.insert(*var);
                        }
                    }
                }
                self.fold_child(subscript.ret, summary, visited, &mut lookup);
            }
            Native(g) => {
                for ty in &g.arguments {
                    self.fold_child(*ty, summary, visited, &mut lookup);
                }
            }
            Variant(types) => {
                for (_, ty) in types {
                    self.fold_child(*ty, summary, visited, &mut lookup);
                }
            }
            Tuple(types) => {
                for ty in types {
                    self.fold_child(*ty, summary, visited, &mut lookup);
                }
            }
            Record(fields) => {
                for (_, ty) in fields {
                    self.fold_child(*ty, summary, visited, &mut lookup);
                }
            }
            Named(NamedType {
                params,
                effect_params,
                ..
            }) => {
                for ty in params {
                    self.fold_child(*ty, summary, visited, &mut lookup);
                }
                for eff in effect_params {
                    let mut vars = FxHashSet::default();
                    eff.fill_with_inner_effect_vars(&mut vars);
                    for var in vars {
                        summary.free_eff_vars.insert(var);
                    }
                }
            }
            Never => {}
        }
    }

    fn fold_child(
        &self,
        ty: Type,
        summary: &mut TypeSummary,
        visited: &mut FxHashSet<Type>,
        lookup: &mut impl FnMut(Type) -> TypeSummary,
    ) {
        if !visited.insert(ty) {
            return;
        }
        let child = lookup(ty);
        summary.free_ty_vars.union_with(&child.free_ty_vars);
        summary.free_mut_vars.union_with(&child.free_mut_vars);
        summary.free_eff_vars.union_with(&child.free_eff_vars);
    }
}

fn summaries_eq(a: &TypeSummary, b: &TypeSummary) -> bool {
    a.free_ty_vars == b.free_ty_vars
        && a.free_mut_vars == b.free_mut_vars
        && a.free_eff_vars == b.free_eff_vars
}

/// An ergonomic constructor for a tuple type when constructing it from a list of types
pub fn tuple_type(types: impl Into<Vec<Type>>) -> Type {
    Type::tuple(types.into())
}

/// An ergonomic constructor for a variant type when constructing it from a list of strings and types
pub fn variant_type<'s>(types: impl IntoIterator<Item = (&'s str, Type)>) -> Type {
    let types: Vec<_> = types
        .into_iter()
        .map(|(name, ty)| (ustr(name), ty))
        .collect();
    Type::variant(types)
}

/// An ergonomic constructor for a record type when constructing it from a list of strings and types
pub fn record_type<'s>(fields: impl IntoIterator<Item = (&'s str, Type)>) -> Type {
    let fields: Vec<_> = fields
        .into_iter()
        .map(|(name, ty)| (ustr(name), ty))
        .collect();
    Type::record(fields)
}

fn types() -> &'static RwLock<TypeUniverse> {
    static TYPES: OnceLock<RwLock<TypeUniverse>> = OnceLock::new();
    TYPES.get_or_init(|| RwLock::new(TypeUniverse::new_empty()))
}

/// Store a type in the type system and return a type identifier
pub fn store_type(type_data: TypeKind) -> Type {
    types()
        .try_write()
        .expect("Cannot get a write lock to type universes")
        .insert_type(type_data)
}

/// Store a list of types in the type system and return a list of type identifiers
pub fn store_types(types_data: &[TypeKind]) -> Vec<Type> {
    types()
        .try_write()
        .expect("Cannot get a write lock to type universes")
        .insert_types(types_data)
}

/// Visit every interned `TypeKind` across all worlds.
/// Intended for diagnostics/measurement.
pub fn for_each_stored_kind(mut f: impl FnMut(&TypeKind)) {
    let universe = types()
        .try_read()
        .expect("Cannot get a read lock to type universes");
    for world in &universe.worlds {
        for entry in world.iter() {
            f(&entry.kind);
        }
    }
}

pub fn dump_type_world(index: usize, env: &ModuleEnv<'_>) {
    let universe = types().read().unwrap();
    for (i, entry) in universe.worlds[index].iter().enumerate() {
        println!("{}: {}", i, entry.kind.format_with(env));
    }
}

pub struct TypeDataRef<'a> {
    ty: Type,
    guard: RwLockReadGuard<'a, TypeUniverse>,
}
impl Deref for TypeDataRef<'_> {
    type Target = TypeKind;
    fn deref(&self) -> &Self::Target {
        self.guard.get_type_data(self.ty)
    }
}

pub struct TypeSummaryRef<'a> {
    ty: Type,
    guard: RwLockReadGuard<'a, TypeUniverse>,
}
impl Deref for TypeSummaryRef<'_> {
    type Target = TypeSummary;
    fn deref(&self) -> &Self::Target {
        self.guard.get_type_summary(self.ty)
    }
}

pub struct TypeNames {
    pub names_to_types: FxHashMap<Ustr, Type>,
    pub types_to_names: FxHashMap<Type, Ustr>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession,
        module::{LocalTypeDefId, ModuleId},
        parser::location::{Location, SourceTable},
        std::{
            array::array_type,
            logic::bool_type,
            math::{Int, int_type},
            std_module,
            string::string_type,
        },
        types::{
            effects::{EffType, Effect, EffectsInstSubst, PrimitiveEffect},
            type_inference::unify::UnifiedTypeInference,
            type_like::TypeLike,
            type_mapper::SimpleInstantiationMapper,
        },
    };

    #[derive(Debug)]
    struct SyntheticContainer;

    fn container_kind(element_ty: Type) -> TypeKind {
        TypeKind::Native(b(NativeType::new(
            bare_native_type::<SyntheticContainer>(),
            vec![element_ty],
        )))
    }

    #[test]
    fn yielded_once_return_convention_does_not_satisfy_value() {
        assert!(CallResultConvention::Value.can_satisfy(CallResultConvention::Value));
        assert!(!CallResultConvention::Value.can_satisfy(CallResultConvention::YIELDED_ONCE));
        assert!(!CallResultConvention::Value.can_satisfy(CallResultConvention::ADDRESSOR_PLACE));

        assert!(!CallResultConvention::YIELDED_ONCE.can_satisfy(CallResultConvention::Value));
        assert!(CallResultConvention::YIELDED_ONCE.can_satisfy(CallResultConvention::YIELDED_ONCE));
        assert!(
            !CallResultConvention::YIELDED_ONCE.can_satisfy(CallResultConvention::ADDRESSOR_PLACE)
        );

        assert!(CallResultConvention::ADDRESSOR_PLACE.can_satisfy(CallResultConvention::Value));
        assert!(
            CallResultConvention::ADDRESSOR_PLACE.can_satisfy(CallResultConvention::YIELDED_ONCE)
        );
        assert!(
            CallResultConvention::ADDRESSOR_PLACE
                .can_satisfy(CallResultConvention::ADDRESSOR_PLACE)
        );
    }

    fn test_subscript_member(result_convention: SubscriptResultConvention) -> SubscriptMemberType {
        SubscriptMemberType::new(EffType::empty(), result_convention)
    }

    fn test_ref_subscript_type(arg: Type, ret: Type) -> SubscriptType {
        SubscriptType::new(
            vec![FnArgType::new_by_val(arg)],
            ret,
            Some(test_subscript_member(
                SubscriptResultConvention::AddressorPlace,
            )),
            None,
        )
    }

    fn test_ref_mut_subscript_type(arg: Type, ret: Type) -> SubscriptType {
        SubscriptType::new(
            vec![FnArgType::new_by_val(arg)],
            ret,
            Some(test_subscript_member(
                SubscriptResultConvention::AddressorPlace,
            )),
            Some(test_subscript_member(
                SubscriptResultConvention::AddressorPlace,
            )),
        )
    }

    fn named_subscript_type(subscript: SubscriptType) -> Type {
        // Comparing arguments of the same named type does not consult its definition.
        let def = TypeDefId::new(ModuleId::new(0), LocalTypeDefId::new(0));
        Type::named(def, vec![Type::subscript_type(subscript)])
    }

    #[test]
    fn named_subscript_arguments_preserve_members() {
        let actual = test_ref_mut_subscript_type(int_type(), bool_type());
        let span = Location::new_synthesized();
        for remove_ref in [false, true] {
            let mut expected = actual.clone();
            if remove_ref {
                expected.ref_member = None;
            } else {
                expected.mut_member = None;
            }
            UnifiedTypeInference::default()
                .unify_sub_type(
                    Type::subscript_type(actual.clone()),
                    span,
                    Type::subscript_type(expected.clone()),
                    span,
                )
                .expect("a subscript can supply a subset of its members");
            assert!(
                UnifiedTypeInference::default()
                    .unify_sub_type(
                        named_subscript_type(actual.clone()),
                        span,
                        named_subscript_type(expected),
                        span
                    )
                    .is_err(),
                "a named type argument must preserve both members"
            );
        }
    }

    #[test]
    fn named_subscript_arguments_preserve_result_conventions() {
        let actual = test_ref_mut_subscript_type(int_type(), bool_type());
        let span = Location::new_synthesized();
        for change_ref in [false, true] {
            let mut expected = actual.clone();
            let member = if change_ref {
                &mut expected.ref_member
            } else {
                &mut expected.mut_member
            };
            member.as_mut().unwrap().result_convention = SubscriptResultConvention::YieldedOnce;
            UnifiedTypeInference::default()
                .unify_sub_type(
                    Type::subscript_type(actual.clone()),
                    span,
                    Type::subscript_type(expected.clone()),
                    span,
                )
                .expect("an addressor can satisfy a yielded-place capability");
            assert!(
                UnifiedTypeInference::default()
                    .unify_sub_type(
                        named_subscript_type(actual.clone()),
                        span,
                        named_subscript_type(expected),
                        span
                    )
                    .is_err(),
                "a named type argument must preserve each result convention"
            );
        }
    }

    #[test]
    fn named_subscript_arguments_preserve_member_effects() {
        let actual = test_ref_mut_subscript_type(int_type(), bool_type());
        let span = Location::new_synthesized();
        for change_ref in [false, true] {
            let mut expected = actual.clone();
            let member = if change_ref {
                &mut expected.ref_member
            } else {
                &mut expected.mut_member
            };
            member.as_mut().unwrap().effects = EffType::single_primitive(PrimitiveEffect::Fallible);
            UnifiedTypeInference::default()
                .unify_sub_type(
                    Type::subscript_type(actual.clone()),
                    span,
                    Type::subscript_type(expected.clone()),
                    span,
                )
                .expect("a pure subscript member can satisfy a fallible capability");
            assert!(
                UnifiedTypeInference::default()
                    .unify_sub_type(
                        named_subscript_type(actual.clone()),
                        span,
                        named_subscript_type(expected.clone()),
                        span
                    )
                    .is_err(),
                "a named type argument must preserve each member's effects"
            );

            // Invariance must still infer a member's unknown effects from the other argument.
            let member = if change_ref {
                &mut expected.ref_member
            } else {
                &mut expected.mut_member
            };
            member.as_mut().unwrap().effects = EffType::single_variable(EffectVar::new(0));
            let actual = named_subscript_type(actual.clone());
            let expected = named_subscript_type(expected);
            let mut inference = UnifiedTypeInference::default();
            inference
                .unify_sub_type(actual, span, expected, span)
                .unwrap();
            inference.finalize_effect_dependencies().unwrap();
            assert_eq!(inference.substitute_in_type(expected), actual);
        }
    }

    #[test]
    fn subscript_type_is_distinct_from_function_type() {
        let arg_ty = int_type();
        let ret_ty = bool_type();
        let fn_ty = Type::function_by_val([arg_ty], ret_ty);
        let subscript_ty = Type::subscript_type(test_ref_subscript_type(arg_ty, ret_ty));

        assert!(fn_ty.is_function());
        assert!(subscript_ty.is_subscript());
        assert_ne!(fn_ty, subscript_ty);
    }

    #[test]
    fn subscript_type_with_mut_member_satisfies_ref_only_capability() {
        let actual = Type::subscript_type(test_ref_mut_subscript_type(int_type(), bool_type()));
        let expected = Type::subscript_type(test_ref_subscript_type(int_type(), bool_type()));

        UnifiedTypeInference::default()
            .unify_sub_type(
                actual,
                Location::new_synthesized(),
                expected,
                Location::new_synthesized(),
            )
            .unwrap();
    }

    #[test]
    fn subscript_type_without_mut_member_does_not_satisfy_mut_capability() {
        let actual = Type::subscript_type(test_ref_subscript_type(int_type(), bool_type()));
        let expected = Type::subscript_type(SubscriptType::new(
            vec![FnArgType::new_by_val(int_type())],
            bool_type(),
            None,
            Some(test_subscript_member(
                SubscriptResultConvention::AddressorPlace,
            )),
        ));

        let result = UnifiedTypeInference::default().unify_sub_type(
            actual,
            Location::new_synthesized(),
            expected,
            Location::new_synthesized(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn subscript_type_tracks_member_effect_variables() {
        let effect_var = EffectVar::new(0);
        let subscript_ty = Type::subscript_type(SubscriptType::new(
            vec![FnArgType::new_by_val(int_type())],
            bool_type(),
            Some(SubscriptMemberType::new(
                EffType::single_variable(effect_var),
                SubscriptResultConvention::YieldedOnce,
            )),
            Some(SubscriptMemberType::new(
                EffType::single_primitive(PrimitiveEffect::Write),
                SubscriptResultConvention::YieldedOnce,
            )),
        ));

        let summary = subscript_ty.summary();
        assert!(summary.free_eff_vars.contains(effect_var));
    }

    #[test]
    fn subscript_type_member_effects_are_checked_independently() {
        let actual = Type::subscript_type(SubscriptType::new(
            vec![FnArgType::new_by_val(int_type())],
            bool_type(),
            Some(SubscriptMemberType::new(
                EffType::single_primitive(PrimitiveEffect::Read),
                SubscriptResultConvention::AddressorPlace,
            )),
            Some(SubscriptMemberType::new(
                EffType::single_primitive(PrimitiveEffect::Write),
                SubscriptResultConvention::AddressorPlace,
            )),
        ));
        let ref_only_expected = Type::subscript_type(SubscriptType::new(
            vec![FnArgType::new_by_val(int_type())],
            bool_type(),
            Some(SubscriptMemberType::new(
                EffType::single_primitive(PrimitiveEffect::Read),
                SubscriptResultConvention::AddressorPlace,
            )),
            None,
        ));

        UnifiedTypeInference::default()
            .unify_sub_type(
                actual,
                Location::new_synthesized(),
                ref_only_expected,
                Location::new_synthesized(),
            )
            .unwrap();

        let wrong_ref_expected = Type::subscript_type(SubscriptType::new(
            vec![FnArgType::new_by_val(int_type())],
            bool_type(),
            Some(SubscriptMemberType::new(
                EffType::single_primitive(PrimitiveEffect::Write),
                SubscriptResultConvention::AddressorPlace,
            )),
            Some(SubscriptMemberType::new(
                EffType::single_primitive(PrimitiveEffect::Write),
                SubscriptResultConvention::AddressorPlace,
            )),
        ));
        let result = UnifiedTypeInference::default().unify_sub_type(
            actual,
            Location::new_synthesized(),
            wrong_ref_expected,
            Location::new_synthesized(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn subscript_type_instantiation_reaches_args_return_and_member_effects() {
        let arg_var = TypeVar::new(0);
        let ret_var = TypeVar::new(1);
        let effect_var = EffectVar::new(0);
        let subscript_ty = Type::subscript_type(SubscriptType::new(
            vec![FnArgType::new_by_val(Type::variable(arg_var))],
            Type::variable(ret_var),
            Some(SubscriptMemberType::new(
                EffType::single_variable(effect_var),
                SubscriptResultConvention::YieldedOnce,
            )),
            None,
        ));
        let ty_subst = FxHashMap::from_iter([(arg_var, int_type()), (ret_var, bool_type())]);
        let eff_subst = EffectsInstSubst::from_iter([(
            effect_var,
            EffType::single_primitive(PrimitiveEffect::Read),
        )]);
        let subst = (ty_subst, eff_subst);
        let mut mapper = SimpleInstantiationMapper::new(&subst);

        let mapped = subscript_ty.map(&mut mapper);
        let mapped_data = mapped.data();
        let TypeKind::Subscript(mapped_subscript) = &*mapped_data else {
            panic!("subscript type instantiation must preserve TypeKind::Subscript");
        };

        assert_eq!(mapped_subscript.args[0].ty, int_type());
        assert_eq!(mapped_subscript.ret, bool_type());
        assert_eq!(
            mapped_subscript
                .ref_member
                .as_ref()
                .unwrap()
                .effects
                .clone(),
            EffType::single_primitive(PrimitiveEffect::Read)
        );
        assert!(
            mapped_subscript
                .ref_member
                .as_ref()
                .unwrap()
                .effects
                .contains(Effect::Primitive(PrimitiveEffect::Read))
        );
    }

    #[test]
    fn parse_and_format() {
        let mut session = CompilerSession::new();
        let mut check_format = |src: &str, expected: &str| {
            let ty = session
                .resolve_defined_type_with_std("<test>", src)
                .unwrap();
            let env = session.module_env();
            let formatted = format!("{}", ty.format_with(&env));
            assert_eq!(expected, formatted);
        };
        check_format("()", "()");
        check_format("bool", "bool");
        check_format("int", "int");
        check_format("float", "float");
        check_format("string", "string");
        check_format("[int]", "[int]");
        check_format("[float]", "[float]");
        check_format("(bool,)", "(bool,)");
        check_format("(bool, bool)", "(bool, bool)");
        check_format("(bool, (string, int))", "(bool, (string, int))");
        check_format("{ a: int, b: float }", "{ a: int, b: float }");
        check_format(
            "{ a: int, b: { c: bool, d: string } }",
            "{ a: int, b: { c: bool, d: string } }",
        );
        check_format("Option<int>", "Option<int>");
        check_format(
            "Color (string) | RGB (int, int, int)",
            "Color (string) | RGB (int, int, int)",
        );
        check_format(
            "[[(string, { age: int, name: string, nick: Option<string> })]]",
            "[[(string, { age: int, name: string, nick: Option<string> })]]",
        );
    }

    #[test]
    fn interning() {
        let var0 = Type::variable_id(0);
        let empty_tuple = Type::unit();

        // ADT recursive list
        let adt_list_element = TypeKind::Tuple(vec![var0, Type::new_local(1)]);
        let adt_list = TypeKind::Variant(vec![
            (ustr("Nil"), empty_tuple),
            (ustr("Cons"), Type::new_local(0)),
        ]);
        let stored = store_types(&[adt_list_element, adt_list]);
        assert_eq!(stored.len(), 2);

        // Tuple of two native types
        let std_int = int_type();
        let native_int = TypeKind::Native(b(NativeType {
            bare_ty: bare_native_type::<Int>(),
            arguments: vec![],
        }));
        let std_bool = bool_type();
        let native_bool = TypeKind::Native(b(NativeType {
            bare_ty: bare_native_type::<bool>(),
            arguments: vec![],
        }));
        let tuple = TypeKind::Tuple(vec![Type::new_local(0), Type::new_local(1)]);
        let stored = store_types(&[native_int, native_bool, tuple]);
        assert_eq!(stored.len(), 3);
        let ty_data = stored[2].data();
        let tuple = ty_data.as_tuple().unwrap();
        assert_eq!(tuple[0], std_int);
        assert_eq!(tuple[1], std_bool);
    }

    #[test]
    fn simple_recursive_type_interning() {
        // Test 1: Simple self-referential type
        // type T = Cons(int, T) | Nil
        let int = int_type();
        let nil = Type::unit();

        let recursive_list = TypeKind::Variant(vec![
            (ustr("Cons"), Type::tuple([int, Type::new_local(0)])),
            (ustr("Nil"), nil),
        ]);

        let stored1 = store_type(recursive_list.clone());
        let stored2 = store_type(recursive_list);

        // Should intern to the same type
        assert_eq!(
            stored1, stored2,
            "Same recursive structure should intern to same type"
        );
    }

    #[test]
    fn mutually_recursive_types_interning() {
        // Test mutually recursive types: Tree(Node) | Leaf, Node = (int, Tree)
        let int = int_type();

        // Tree = Leaf | Branch(Node)
        // Node = (int, Tree)
        let node_tuple = TypeKind::Tuple(vec![int, Type::new_local(0)]);
        let tree_variant = TypeKind::Variant(vec![
            (ustr("Branch"), Type::new_local(1)),
            (ustr("Leaf"), Type::unit()),
        ]);

        let stored = store_types(&[tree_variant, node_tuple]);

        // Store the same structure again
        let node_tuple2 = TypeKind::Tuple(vec![int, Type::new_local(0)]);
        let tree_variant2 = TypeKind::Variant(vec![
            (ustr("Branch"), Type::new_local(1)),
            (ustr("Leaf"), Type::unit()),
        ]);
        let stored2 = store_types(&[tree_variant2, node_tuple2]);

        // Should intern to same types
        assert_eq!(stored[0], stored2[0]);
        assert_eq!(stored[1], stored2[1]);
    }

    #[test]
    fn json_like_variant_interning() {
        // Simplified version of the Variant type from variant.rs
        let int = int_type();
        let string = string_type();

        // Variant = Int(int) | String(string) | Array([Variant])
        let variant = TypeKind::Variant(vec![
            (ustr("Array"), Type::tuple([array_type(Type::new_local(0))])),
            (ustr("Int"), Type::tuple([int])),
            (ustr("String"), Type::tuple([string])),
        ]);

        let stored1 = store_type(variant.clone());
        let stored2 = store_type(variant);

        assert_eq!(
            stored1, stored2,
            "JSON-like variant should intern consistently"
        );

        // Verify the structure
        let data = stored1.data();
        if let TypeKind::Variant(variants) = &*data {
            assert_eq!(variants.len(), 3);
            assert_eq!(variants[0].0, ustr("Array"));
            assert_eq!(variants[1].0, ustr("Int"));
            assert_eq!(variants[2].0, ustr("String"));
        } else {
            panic!("Expected Variant type");
        }
    }

    #[test]
    fn deeply_nested_same_structure() {
        // Test that the same structure at different nesting levels interns correctly
        let int = int_type();

        // Level 1: (int, (int,))
        let ty1 = Type::tuple([int, Type::tuple([int])]);

        // Level 2: (int, (int, (int,)))
        let ty2 = Type::tuple([int, Type::tuple([int, Type::tuple([int])])]);

        // Create them again - should intern to same values
        let ty1_again = Type::tuple([int, Type::tuple([int])]);
        let ty2_again = Type::tuple([int, Type::tuple([int, Type::tuple([int])])]);

        assert_eq!(ty1, ty1_again);
        assert_eq!(ty2, ty2_again);
    }

    #[test]
    fn variant_field_order_normalization() {
        // Test that variants with fields in different orders intern to the same type
        let int = int_type();
        let string = string_type();
        let bool = bool_type();

        // Create variant with fields in one order
        let variant1 = TypeKind::Variant(vec![
            (ustr("Int"), Type::tuple([int])),
            (ustr("String"), Type::tuple([string])),
            (ustr("Bool"), Type::tuple([bool])),
        ]);

        // Create the same variant with fields in a different order
        let variant2 = TypeKind::Variant(vec![
            (ustr("String"), Type::tuple([string])),
            (ustr("Bool"), Type::tuple([bool])),
            (ustr("Int"), Type::tuple([int])),
        ]);

        // Create yet another order
        let variant3 = TypeKind::Variant(vec![
            (ustr("Bool"), Type::tuple([bool])),
            (ustr("Int"), Type::tuple([int])),
            (ustr("String"), Type::tuple([string])),
        ]);

        let stored1 = store_type(variant1);
        let stored2 = store_type(variant2);
        let stored3 = store_type(variant3);

        // All should intern to the same type thanks to normalization
        assert_eq!(
            stored1, stored2,
            "Variants with different field order should intern to same type"
        );
        assert_eq!(
            stored2, stored3,
            "Variants with different field order should intern to same type"
        );
        assert_eq!(
            stored1, stored3,
            "Variants with different field order should intern to same type"
        );
    }

    #[test]
    fn record_field_order_normalization() {
        // Test that records with fields in different orders intern to the same type
        let int = int_type();
        let string = string_type();
        let bool = bool_type();

        // Create record with fields in one order
        let record1 = TypeKind::Record(vec![
            (ustr("name"), string),
            (ustr("age"), int),
            (ustr("active"), bool),
        ]);

        // Create the same record with fields in a different order
        let record2 = TypeKind::Record(vec![
            (ustr("active"), bool),
            (ustr("name"), string),
            (ustr("age"), int),
        ]);

        // Create yet another order
        let record3 = TypeKind::Record(vec![
            (ustr("age"), int),
            (ustr("active"), bool),
            (ustr("name"), string),
        ]);

        let stored1 = store_type(record1);
        let stored2 = store_type(record2);
        let stored3 = store_type(record3);

        // All should intern to the same type thanks to normalization
        assert_eq!(
            stored1, stored2,
            "Records with different field order should intern to same type"
        );
        assert_eq!(
            stored2, stored3,
            "Records with different field order should intern to same type"
        );
        assert_eq!(
            stored1, stored3,
            "Records with different field order should intern to same type"
        );
    }

    #[test]
    fn recursive_variant_field_order_normalization() {
        // Test that recursive variants with fields in different orders intern to the same type
        let int = int_type();

        // Tree = Branch(int, Tree, Tree) | Leaf
        let tree1 = TypeKind::Variant(vec![
            (
                ustr("Branch"),
                Type::tuple([int, Type::new_local(0), Type::new_local(0)]),
            ),
            (ustr("Leaf"), Type::unit()),
        ]);

        // Same structure but fields in different order
        let tree2 = TypeKind::Variant(vec![
            (ustr("Leaf"), Type::unit()),
            (
                ustr("Branch"),
                Type::tuple([int, Type::new_local(0), Type::new_local(0)]),
            ),
        ]);

        let stored1 = store_type(tree1);
        let stored2 = store_type(tree2);

        // Should intern to the same type
        assert_eq!(
            stored1, stored2,
            "Recursive variants with different field order should intern to same type"
        );
    }

    #[test]
    fn data_value_type_is_named_std_type() {
        use crate::std::data_value::{data_value_type, data_value_type_def};

        let mut source_table = SourceTable::default();
        std_module(&mut source_table);

        let data_value = data_value_type();
        let ty_data = data_value.data();
        let TypeKind::Named(named) = &*ty_data else {
            panic!("DataValue should be a named std type, got {data_value:?}");
        };
        assert_eq!(named.def, data_value_type_def());
        assert!(named.params.is_empty());
    }

    #[test]
    fn recursive_variant_unfolding_equivalence() {
        let int = int_type();
        let original = store_types(&[
            TypeKind::Variant(vec![
                (ustr("Next"), Type::new_local(1)),
                (ustr("Leaf"), int),
            ]),
            TypeKind::Tuple(vec![Type::new_local(2)]),
            TypeKind::Named(NamedType {
                def: array_type_def(),
                params: vec![Type::new_local(0)],
                effect_params: vec![],
            }),
        ])[0];
        for _ in 0..3 {
            let unfolded = store_type(TypeKind::Variant(vec![
                (ustr("Next"), Type::tuple([array_type(original)])),
                (ustr("Leaf"), int),
            ]));
            assert_eq!(original, unfolded);
        }
    }

    #[test]
    fn recursive_interning_refines_long_periodic_cycles() {
        // A single marked node distinguishes every position of a long cycle.
        // Doubling the period introduces equivalent nodes with different indices.
        // This requires propagation around the entire cycle without full rescans.
        for period in [256, 4096] {
            let count = 2 * period;
            let graph: Vec<_> = (0..count)
                .map(|i| {
                    let next = Type::new_local(((i + 1) % count) as u32);
                    if i % period == 0 {
                        TypeKind::Record(vec![(ustr("mark"), next)])
                    } else {
                        TypeKind::Tuple(vec![next])
                    }
                })
                .collect();
            let (quotient, mapping) = minimize_recursive_component(&graph);
            assert_eq!(quotient.len(), period);
            assert_eq!(mapping[..period], mapping[period..]);
            // Quotient indices follow first input occurrence, regardless of the
            // order in which the refinement splitters happened to run.
            assert_eq!(mapping[..period], (0..period as u32).collect::<Vec<_>>());
            for (index, mut kind) in graph.into_iter().enumerate() {
                kind.substitute_locals(&mapping);
                assert_eq!(kind, quotient[mapping[index] as usize]);
            }
        }
    }

    /// Check every original edge, including edges from duplicate input nodes.
    fn assert_interned_graph(universe: &TypeUniverse, kinds: &[TypeKind], stored: &[Type]) {
        assert_eq!(kinds.len(), stored.len());
        for (kind, &ty) in kinds.iter().zip(stored) {
            let mut expected = kind.clone();
            expected.normalize();
            expected.for_each_inner_type_mut(|child| {
                if child.is_local() {
                    *child = stored[child.index() as usize];
                }
            });
            assert_eq!(&expected, universe.get_type_data(ty));
        }
    }

    #[test]
    fn recursive_interning_minimizes_duplicate_nodes_in_both_orders() {
        let local = Type::new_local;
        let shared = vec![
            TypeKind::Tuple(vec![local(1), local(1)]),
            container_kind(local(2)),
            TypeKind::Record(vec![(ustr("tail"), local(0))]),
        ];
        let exact_duplicates = vec![
            TypeKind::Tuple(vec![local(1), local(3)]),
            container_kind(local(2)),
            TypeKind::Record(vec![(ustr("tail"), local(0))]),
            container_kind(local(2)),
        ];
        let equivalent_cycles = vec![
            TypeKind::Tuple(vec![local(1), local(3)]),
            container_kind(local(2)),
            TypeKind::Record(vec![(ustr("tail"), local(0))]),
            container_kind(local(4)),
            TypeKind::Record(vec![(ustr("tail"), local(0))]),
        ];
        for duplicated in [exact_duplicates, equivalent_cycles] {
            for duplicate_first in [false, true] {
                let mut universe = TypeUniverse::new_empty();
                let (first, second) = if duplicate_first {
                    (&duplicated, &shared)
                } else {
                    (&shared, &duplicated)
                };
                let a = universe.insert_types(first.clone());
                let b = universe.insert_types(second.clone());
                assert_interned_graph(&universe, first, &a);
                assert_interned_graph(&universe, second, &b);
                assert_eq!(a[0], b[0]);
                assert_eq!(universe.worlds.len(), 2);
                assert_eq!(universe.worlds[1].len(), 3);
                // Exercise both cached original-to-quotient mappings.
                assert_eq!(a, universe.insert_types(first.clone()));
                assert_eq!(b, universe.insert_types(second.clone()));
            }
        }
    }

    #[test]
    fn recursive_interning_minimizes_cycle_lengths_and_separate_components() {
        for long_first in [false, true] {
            let mut universe = TypeUniverse::new_empty();
            let single = vec![container_kind(Type::new_local(0))];
            let cycle = vec![
                container_kind(Type::new_local(1)),
                container_kind(Type::new_local(0)),
            ];
            let (first, second) = if long_first {
                (&cycle, &single)
            } else {
                (&single, &cycle)
            };
            let a = universe.insert_types(first.clone());
            let b = universe.insert_types(second.clone());
            assert_interned_graph(&universe, first, &a);
            assert_interned_graph(&universe, second, &b);
            assert!(a.iter().chain(&b).all(|ty| *ty == a[0]));
            let separate = universe.insert_types(vec![
                container_kind(Type::new_local(0)),
                container_kind(Type::new_local(1)),
                TypeKind::Tuple(vec![Type::new_local(0), Type::new_local(1)]),
            ]);
            assert_eq!(separate[0], a[0]);
            assert_eq!(separate[1], a[0]);
            assert_eq!(universe.worlds[1].len(), 1);
        }
    }

    #[test]
    fn recursive_interning_reuses_part_of_existing_component() {
        let mut universe = TypeUniverse::new_empty();
        // A = (A, B), B = Native<A>; X = (X, B) is A, although X's
        // local SCC has one node and the stored SCC has two.
        let graph = vec![
            TypeKind::Tuple(vec![Type::new_local(0), Type::new_local(1)]),
            container_kind(Type::new_local(0)),
        ];
        let stored = universe.insert_types(graph.clone());
        let partial = vec![TypeKind::Tuple(vec![Type::new_local(0), stored[1]])];
        let reused = universe.insert_types(partial.clone());
        assert_eq!(reused, vec![stored[0]]);
        assert_interned_graph(&universe, &partial, &reused);
        assert_eq!(universe.insert_types(partial), reused);
        // A finite unfolding must use the same identity, too.
        assert_eq!(
            universe.insert_type(TypeKind::Tuple(stored.clone())),
            stored[0]
        );
        assert_eq!(universe.worlds.len(), 2);
        assert_interned_graph(&universe, &graph, &stored);
    }

    #[test]
    fn recursive_interning_matches_mixed_local_and_global_tree_edges() {
        let mut universe = TypeUniverse::new_empty();
        let leaf = universe.insert_type(TypeKind::Tuple(vec![]));
        // T = Leaf | Node(N), N = (T, T).
        let tree = vec![
            TypeKind::Variant(vec![
                (ustr("Leaf"), leaf),
                (ustr("Node"), Type::new_local(1)),
            ]),
            TypeKind::Tuple(vec![Type::new_local(0), Type::new_local(0)]),
        ];
        let stored = universe.insert_types(tree.clone());
        // a = Leaf | Node(b), b = (a, T_global). Candidate signatures must
        // erase both kinds of recursive edge or this creates a duplicate world.
        let mut mixed = tree;
        mixed[1] = TypeKind::Tuple(vec![Type::new_local(0), stored[0]]);
        let reused = universe.insert_types(mixed.clone());
        assert_eq!(reused, stored);
        assert_interned_graph(&universe, &mixed, &reused);
        assert_eq!(universe.worlds.len(), 2);
    }

    #[test]
    fn recursive_interning_indexes_world_zero_children() {
        let mut universe = TypeUniverse::new_empty();
        for variable in 0..16 {
            let payload = universe.insert_type(TypeKind::Variable(TypeVar::new(variable)));
            let list = vec![
                TypeKind::Record(vec![(ustr("cons"), Type::new_local(1))]),
                TypeKind::Tuple(vec![payload, Type::new_local(0)]),
            ];
            let stored = universe.insert_types(list);
            let key = recursive_candidate_signature(universe.get_type_data(stored[1]));
            // Different nonrecursive payloads must not accumulate in one bucket.
            assert_eq!(universe.recursive_candidates[&key], vec![stored[1]]);
        }
    }

    #[test]
    fn recursive_interning_preserves_constructor_attributes() {
        let root = Type::new_local(0);
        let pure = EffType::empty();
        let fallible = EffType::single_primitive(PrimitiveEffect::Fallible);
        let def = TypeDefId::new(ModuleId::new(0), LocalTypeDefId::new(0));
        let other_def = TypeDefId::new(ModuleId::new(0), LocalTypeDefId::new(1));
        let named = |def, effects| {
            TypeKind::Named(NamedType {
                def,
                params: vec![root],
                effect_params: vec![effects],
            })
        };
        let function = |mut_ty, effects| {
            TypeKind::Function(b(FnType::new(
                vec![FnArgType::new(root, mut_ty)],
                root,
                effects,
            )))
        };
        let subscript = |effects, convention| {
            TypeKind::Subscript(b(SubscriptType::new(
                vec![FnArgType::new_by_val(root)],
                root,
                Some(SubscriptMemberType::new(effects, convention)),
                None,
            )))
        };
        let variants = vec![
            named(def, pure.clone()),
            named(def, fallible.clone()),
            named(other_def, pure.clone()),
            function(MutType::constant(), pure.clone()),
            function(MutType::mutable(), pure.clone()),
            function(MutType::constant(), fallible.clone()),
            subscript(pure.clone(), SubscriptResultConvention::AddressorPlace),
            subscript(fallible, SubscriptResultConvention::AddressorPlace),
            subscript(pure, SubscriptResultConvention::YieldedOnce),
            TypeKind::Record(vec![(ustr("a"), root)]),
            TypeKind::Record(vec![(ustr("b"), root)]),
            TypeKind::Variant(vec![(ustr("a"), root)]),
            TypeKind::Variant(vec![(ustr("b"), root)]),
            container_kind(root),
            TypeKind::Native(b(NativeType::new(bare_native_type::<bool>(), vec![root]))),
        ];
        // All nodes belong to one SCC, exercising minimization as well as lookup.
        let mut graph = vec![TypeKind::Tuple(
            (1..=variants.len())
                .map(|i| Type::new_local(i as u32))
                .collect(),
        )];
        graph.extend(variants);
        let mut universe = TypeUniverse::new_empty();
        let stored = universe.insert_types(graph.clone());
        assert_eq!(stored.iter().collect::<FxHashSet<_>>().len(), graph.len());
        assert_interned_graph(&universe, &graph, &stored);
        // Renumber every node so this cannot take the exact-input cache path.
        let reverse: Vec<_> = (0..graph.len() as u32).rev().collect();
        let mut reordered = graph.clone();
        reordered.reverse();
        for kind in &mut reordered {
            kind.substitute_locals(&reverse);
        }
        universe.local_to_world.clear();
        let reused = universe.insert_types(reordered.clone());
        assert_eq!(reused, stored.iter().rev().copied().collect::<Vec<_>>());
        assert_interned_graph(&universe, &reordered, &reused);

        // Distinct named effects alone must also prevent reuse of a stored SCC.
        let a = universe.insert_type(named(def, EffType::empty()));
        let b = universe.insert_type(named(
            def,
            EffType::single_primitive(PrimitiveEffect::Fallible),
        ));
        assert_ne!(a, b);
    }

    #[test]
    fn recursive_interning_preserves_variables_and_summaries() {
        let mut universe = TypeUniverse::new_empty();
        let vars: Vec<_> = (0..2)
            .map(|i| universe.insert_type(TypeKind::Variable(TypeVar::new(i))))
            .collect();
        let eff = EffectVar::new(7);
        let mut_var = MutVar::new(9);
        let graph = vec![
            TypeKind::Tuple(vec![Type::new_local(1), Type::new_local(2), vars[0]]),
            TypeKind::Function(b(FnType::new(
                vec![FnArgType::new(
                    Type::new_local(0),
                    MutType::Variable(mut_var),
                )],
                Type::new_local(0),
                EffType::single_variable(eff),
            ))),
            TypeKind::Function(b(FnType::new(
                vec![FnArgType::new(
                    Type::new_local(0),
                    MutType::Variable(mut_var),
                )],
                Type::new_local(0),
                EffType::single_variable(eff),
            ))),
        ];
        let stored = universe.insert_types(graph.clone());
        assert_eq!(stored[1], stored[2]);
        assert_interned_graph(&universe, &graph, &stored);
        for ty in &stored {
            let summary = universe.get_type_summary(*ty);
            assert!(summary.free_ty_vars.contains(TypeVar::new(0)));
            assert!(summary.free_mut_vars.contains(mut_var));
            assert!(summary.free_eff_vars.contains(eff));
        }
        let mut other = graph;
        other[0].for_each_inner_type_mut(|ty| {
            if *ty == vars[0] {
                *ty = vars[1];
            }
        });
        let distinct = universe.insert_types(other.clone());
        assert_ne!(stored[0], distinct[0]);
        assert_interned_graph(&universe, &other, &distinct);
    }

    #[test]
    fn recursive_interning_agrees_with_pairwise_bisimulation() {
        // Independent oracle: unfold local and global references alike and close
        // already-seen pairs. In particular, never assume global IDs distinguish
        // types: that is the interner invariant this test is checking.
        fn equivalent(
            universe: &TypeUniverse,
            a: &[TypeKind],
            ai: Type,
            b: &[TypeKind],
            bi: Type,
        ) -> bool {
            let mut seen = FxHashSet::default();
            let mut pending = vec![(ai, bi)];
            while let Some((ai, bi)) = pending.pop() {
                if !seen.insert((ai, bi)) {
                    continue;
                }
                let ak = if ai.is_local() {
                    &a[ai.index() as usize]
                } else {
                    universe.get_type_data(ai)
                };
                let bk = if bi.is_local() {
                    &b[bi.index() as usize]
                } else {
                    universe.get_type_data(bi)
                };
                match (ak, bk) {
                    (TypeKind::Variable(a), TypeKind::Variable(b)) if a == b => {}
                    (TypeKind::Tuple(a), TypeKind::Tuple(b)) if a.len() == b.len() => {
                        pending.extend(a.iter().copied().zip(b.iter().copied()));
                    }
                    (TypeKind::Record(a), TypeKind::Record(b)) if a.len() == b.len() => {
                        for ((an, at), (bn, bt)) in a.iter().zip(b) {
                            if an != bn {
                                return false;
                            }
                            pending.push((*at, *bt));
                        }
                    }
                    _ => return false,
                }
            }
            true
        }
        for reverse in [false, true] {
            let mut universe = TypeUniverse::new_empty();
            let var0 = universe.insert_type(TypeKind::Variable(TypeVar::new(0)));
            let var1 = universe.insert_type(TypeKind::Variable(TypeVar::new(1)));
            let recursive = universe.insert_type(TypeKind::Tuple(vec![Type::new_local(0), var0]));
            let wrapper = universe.insert_type(TypeKind::Tuple(vec![recursive]));
            assert_eq!(wrapper.world().unwrap().get(), 0);
            let record =
                universe.insert_type(TypeKind::Record(vec![(ustr("next"), Type::new_local(0))]));
            let globals = [var0, var1, recursive, wrapper, record];
            let mut seed = 0x12345678u32;
            let mut random = || {
                seed ^= seed << 13;
                seed ^= seed >> 17;
                seed ^= seed << 5;
                seed as usize
            };
            // Explicitly include local/global encodings of the same type. The
            // random cases then exercise leaves, constants and arbitrary sharing.
            let mut graphs = vec![
                vec![TypeKind::Tuple(vec![Type::new_local(0), var0])],
                vec![
                    TypeKind::Tuple(vec![Type::new_local(0), Type::new_local(1)]),
                    TypeKind::Variable(TypeVar::new(0)),
                ],
                vec![TypeKind::Tuple(vec![recursive, var0])],
                vec![TypeKind::Record(vec![(ustr("next"), Type::new_local(0))])],
            ];
            graphs.extend((0..80).map(|case| {
                let count = 1 + case % 7;
                (0..count)
                    .map(|_| {
                        if random() % 4 == 0 {
                            return TypeKind::Variable(TypeVar::new((random() % 2) as u32));
                        }
                        let edges: Vec<_> = (0..1 + random() % 2)
                            .map(|_| {
                                if random() % 3 == 0 {
                                    globals[random() % globals.len()]
                                } else {
                                    Type::new_local((random() % count) as u32)
                                }
                            })
                            .collect();
                        if random() % 3 == 0 {
                            TypeKind::Record(vec![(ustr("next"), edges[0])])
                        } else {
                            TypeKind::Tuple(edges)
                        }
                    })
                    .collect::<Vec<_>>()
            }));
            let mut previous: Vec<(usize, Vec<Type>)> = Vec::new();
            let order: Vec<_> = if reverse {
                (0..graphs.len()).rev().collect()
            } else {
                (0..graphs.len()).collect()
            };
            for index in order {
                let graph = &graphs[index];
                let stored = universe.insert_types(graph.clone());
                assert_interned_graph(&universe, graph, &stored);
                for (node, &ty) in stored.iter().enumerate() {
                    assert!(equivalent(
                        &universe,
                        graph,
                        Type::new_local(node as u32),
                        &[],
                        ty
                    ));
                }
                // Replace random local edges by their already-interned partners,
                // changing SCC boundaries without changing the unfolded types.
                let mut mixed = graph.clone();
                for kind in &mut mixed {
                    kind.for_each_inner_type_mut(|child| {
                        if child.is_local() && random() % 2 == 0 {
                            *child = stored[child.index() as usize];
                        }
                    });
                }
                let reused = universe.insert_types(mixed.clone());
                assert_eq!(reused, stored);
                assert_interned_graph(&universe, &mixed, &reused);
                previous.push((index, stored.clone()));
                for (other_index, other_stored) in &previous {
                    for (ai, a) in stored.iter().enumerate() {
                        for (bi, b) in other_stored.iter().enumerate() {
                            assert_eq!(
                                *a == *b,
                                equivalent(
                                    &universe,
                                    graph,
                                    Type::new_local(ai as u32),
                                    &graphs[*other_index],
                                    Type::new_local(bi as u32)
                                ),
                                "graphs {index}:{ai} and {other_index}:{bi}"
                            );
                        }
                    }
                }
            }
        }
    }
}
