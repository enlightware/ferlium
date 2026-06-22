// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::any::TypeId;
use std::any::type_name;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::Display;
use std::fmt::{self, Debug};
use std::hash::Hash;
use std::hash::Hasher;
use std::sync::OnceLock;
use std::sync::RwLock;

use crate::ast::Attribute;
use crate::ast::UstrSpan;
use crate::containers::FromIndex;
use crate::define_id_type;
use crate::format::{
    FormatWith, escape_identifier, format_generic_param_list, write_identifier,
    write_with_separator_and_format_fn,
};
use crate::graph::find_strongly_connected_components;
use crate::graph::topological_sort_sccs;
use crate::hir::value::LiteralValue;
use crate::module::id::Id;
use crate::module::{LocalDecl, TypeDefId};
use crate::types::mutability::FormatInFnArg;
use crate::types::type_like::CastableToType;
use crate::types::type_like::TypeLike;
use crate::types::type_mapper::TypeMapper;
use crate::types::type_substitution::{instantiate_type, map_type_recursive};
use crate::types::type_visitor::TypeInnerVisitor;
use crate::types::var_set::KindVarSet;
use crate::{FxHashMap, FxHashSet, Location};
use derive_new::new;
use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use indexmap::IndexSet;
use nonmax::NonMaxU32;
use ustr::{Ustr, ustr};

use crate::assert::assert_unique_strings;
use crate::containers::compare_by;
use crate::containers::{B, DenseBitSet, SVec2, b};
use crate::format::type_variable_index_to_string_latin;
use crate::graph;
use crate::module::ModuleEnv;
use crate::sync::SyncPhantomData;
use crate::types::effects::{EffType, Effect, EffectVar, PrimitiveEffect};
use crate::types::mutability::{MutType, MutVar};
use crate::types::type_scheme::TypeScheme;

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
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
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
    // fn type_id(&self) -> TypeId {
    //     TypeId::of::<T>()
    // }

    // fn type_name(&self) -> &'static str {
    //     type_name::<T>()
    // }
    fn value_size(&self) -> usize {
        std::mem::size_of::<T>()
    }

    fn value_align(&self) -> usize {
        std::mem::align_of::<T>()
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

fn fmt_fn_arg_type_with_env<Env>(arg: &FnArgType, f: &mut fmt::Formatter, env: &Env) -> fmt::Result
where
    Type: FormatWith<Env>,
{
    arg.mut_ty.format_in_fn_arg(f)?;
    arg.ty.fmt_with(f, env)
}

/// How a function call yields its result.
///
/// Borrow-returning conventions are call-result conventions, not first-class
/// reference types. The return value still has type `ret`; the convention only
/// controls whether and how the immediate call result may be consumed as a
/// place before being materialized.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum FnReturnConvention {
    #[default]
    Value,
    /// A scoped, callee-rooted yielded place. It must be consumed through a
    /// `WithYielded` driver and cannot escape as caller-rooted storage.
    YieldedOnce,
    /// A caller-rooted place, used by addressor functions and addressor
    /// subscript members such as array indexing. This is the strongest
    /// borrow-returning convention because it can also satisfy scoped-yield
    /// consumers.
    AddressorPlace,
}

impl FnReturnConvention {
    pub fn returns_borrow(self) -> bool {
        matches!(self, Self::YieldedOnce | Self::AddressorPlace)
    }

    pub fn returns_caller_rooted_place(self) -> bool {
        matches!(self, Self::AddressorPlace)
    }

    pub fn requires_yield_driver(self) -> bool {
        matches!(self, Self::YieldedOnce)
    }

    pub fn returns_place(self) -> bool {
        self.returns_caller_rooted_place()
    }

    pub fn can_satisfy(self, expected: Self) -> bool {
        match expected {
            Self::Value => matches!(self, Self::Value | Self::AddressorPlace),
            Self::YieldedOnce => matches!(self, Self::YieldedOnce | Self::AddressorPlace),
            Self::AddressorPlace => matches!(self, Self::AddressorPlace),
        }
    }
}

/// The type of a function
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnType {
    pub args: Vec<FnArgType>,
    pub ret: Type,
    pub effects: EffType,
    pub return_convention: FnReturnConvention,
}

impl FnType {
    pub fn new(args: Vec<FnArgType>, ret: Type, effects: EffType) -> Self {
        Self {
            args,
            ret,
            effects,
            return_convention: FnReturnConvention::Value,
        }
    }

    pub fn new_with_return_convention(
        args: Vec<FnArgType>,
        ret: Type,
        effects: EffType,
        return_convention: FnReturnConvention,
    ) -> Self {
        Self {
            args,
            ret,
            effects,
            return_convention,
        }
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
            return_convention: FnReturnConvention::Value,
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
            return_convention: FnReturnConvention::Value,
        }
    }

    pub fn returns_place(&self) -> bool {
        self.return_convention.returns_place()
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
            .then(self.return_convention.cmp(&other.return_convention))
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
            return_convention: self.return_convention,
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

impl CastableToType for FnType {
    fn to_type(&self) -> Type {
        Type::function_type(self.clone())
    }
}

impl FormatWith<ModuleEnv<'_>> for FnType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        fmt_fn_type_with_env(self, f, env)
    }
}

impl FormatWith<TypeDisplayEnv<'_, '_>> for FnType {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &TypeDisplayEnv<'_, '_>) -> fmt::Result {
        fmt_fn_type_with_env(self, f, env)
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
    if function.returns_place() {
        write!(f, "place ")?;
    }
    function.ret.fmt_with(f, env)?;
    format_function_effect_suffix_with_env(&env.displayed_effects(&function.effects), f, env)
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
    if fn_ty.returns_place() {
        write!(f, "place ")?;
    }
    fn_ty.ret.fmt_with(f, env)?;
    format_function_effect_suffix_with_env(&env.displayed_effects(&fn_ty.effects), f, env)
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
            Named(NamedType { params, .. }) => {
                for &ty in params {
                    f(ty);
                }
            }
        }
    }

    #[inline]
    fn for_each_inner_type_mut(&mut self, mut f: impl FnMut(&mut Type)) {
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
            Named(_) => 7,
            Never => 8,
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

fn fmt_type_kind_with_env<Env>(kind: &TypeKind, f: &mut fmt::Formatter, env: &Env) -> fmt::Result
where
    Env: TypeFormatEnv,
    FnType: FormatWith<Env>,
    NativeType: FormatWith<Env>,
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
        Named(NamedType {
            def,
            params: args,
            effect_params: _,
        }) if *def == crate::std::array::array_type_def() && args.len() == 1 => {
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
            (Function(a), Function(b)) => a
                .args
                .cmp(&b.args)
                .then_with(|| a.ret.cmp(&b.ret))
                .then_with(|| a.return_convention.cmp(&b.return_convention)),
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
    type Index = u32;

    fn neighbors(&self) -> impl Iterator<Item = Self::Index> {
        let mut neighbors = Vec::new();
        self.for_each_inner_type(|ty| {
            if ty.is_local() {
                neighbors.push(ty.index());
            }
        });
        neighbors.into_iter()
    }
}

/// A set of types representing a "world" of types,
/// i.e. a collection of types that can reference each other.
type TypeWorld = IndexSet<InternedType>;

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

impl std::borrow::Borrow<TypeKind> for InternedType {
    fn borrow(&self) -> &TypeKind {
        &self.kind
    }
}

/// Attempts to find an isomorphism (bijection) between local_world and existing_world.
/// Returns a Vec where result[local_idx] = global_idx in existing_world, if an isomorphism exists.
///
/// Two worlds are isomorphic if there exists a bijection f: local → existing such that
/// when we remap all local type references in local_world[i] using f, we get existing_world[f(i)].
fn find_world_isomorphism(
    local_world: &[TypeKind],
    existing_world: &TypeWorld,
    world_idx: usize,
) -> Option<Vec<u32>> {
    let n = local_world.len();
    assert_eq!(n, existing_world.len());

    let mut mapping: Vec<Option<usize>> = vec![None; n];

    // For each local type, find all possible matches in existing_world
    let mut candidates: Vec<(usize, DenseBitSet)> = (0..n)
        .map(|local_idx| {
            let local_kind = &local_world[local_idx];
            let mut possible = DenseBitSet::with_capacity(n);
            for existing_idx in 0..n {
                // Quick structural check: compare ignoring type references.
                if types_could_match(local_kind, &existing_world[existing_idx].kind) {
                    possible.insert(existing_idx);
                }
            }
            (local_idx, possible)
        })
        .collect();
    if candidates.iter().any(|(_, possible)| possible.is_empty()) {
        return None;
    }

    // Sort by number of candidates (fewest first for constraint propagation)
    candidates.sort_by_key(|(_, possible)| possible.len());
    let mut used_existing = DenseBitSet::with_capacity(n);

    // Recursive backtracking search
    fn search(
        local_world: &[TypeKind],
        existing_world: &TypeWorld,
        world_idx: usize,
        candidates: &[(usize, DenseBitSet)],
        mapping: &mut Vec<Option<usize>>,
        used_existing: &mut DenseBitSet,
        depth: usize,
    ) -> bool {
        if depth == candidates.len() {
            // Check if complete mapping is valid
            return verify_mapping(local_world, existing_world, world_idx, mapping);
        }

        let (local_idx, possible) = &candidates[depth];
        for existing_idx in possible.iter_ones() {
            if used_existing.contains(existing_idx) {
                continue; // Already mapped
            }

            // Try this mapping
            mapping[*local_idx] = Some(existing_idx);
            used_existing.insert(existing_idx);

            if search(
                local_world,
                existing_world,
                world_idx,
                candidates,
                mapping,
                used_existing,
                depth + 1,
            ) {
                return true;
            }

            // Backtrack
            mapping[*local_idx] = None;
            used_existing.remove(existing_idx);
        }

        false
    }

    if search(
        local_world,
        existing_world,
        world_idx,
        &candidates,
        &mut mapping,
        &mut used_existing,
        0,
    ) {
        Some(mapping.into_iter().map(|opt| opt.unwrap() as u32).collect())
    } else {
        None
    }
}

/// Quick structural check to see if two TypeKinds could potentially match
/// (ignoring the actual type indices they reference)
fn types_could_match(a: &TypeKind, b: &TypeKind) -> bool {
    match (a, b) {
        (TypeKind::Never, TypeKind::Never) => true,
        (TypeKind::Variable(_), TypeKind::Variable(_)) => true,
        (TypeKind::Tuple(a), TypeKind::Tuple(b)) => a.len() == b.len(),
        (TypeKind::Record(a), TypeKind::Record(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.0 == y.0)
        }
        (TypeKind::Variant(a), TypeKind::Variant(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.0 == y.0)
        }
        (TypeKind::Function(a), TypeKind::Function(b)) => {
            a.return_convention == b.return_convention
        } // Could compare arity, but skip for now
        (TypeKind::Native(a), TypeKind::Native(b)) => {
            a.bare_ty == b.bare_ty && a.arguments.len() == b.arguments.len()
        }
        (TypeKind::Named(a), TypeKind::Named(b)) => a.def == b.def,
        _ => false,
    }
}

/// Verify that a complete mapping is valid by checking that when we remap
/// local_world using the mapping, it exactly matches existing_world
fn verify_mapping(
    local_world: &[TypeKind],
    existing_world: &TypeWorld,
    world_idx: usize,
    mapping: &[Option<usize>],
) -> bool {
    // Check that the mapping is complete (bijective)
    if mapping.len() != local_world.len() {
        return false;
    }

    for (local_idx, existing_idx) in mapping.iter().copied().enumerate() {
        let Some(existing_idx) = existing_idx else {
            return false;
        };
        let local_kind = &local_world[local_idx];
        let existing_kind = &existing_world[existing_idx].kind;
        // Compare local references through `mapping` without cloning the local kind.
        if !type_kinds_match_with_mapping(local_kind, existing_kind, world_idx, mapping) {
            return false;
        }
    }

    true
}

fn type_kinds_match_with_mapping(
    local: &TypeKind,
    existing: &TypeKind,
    world_idx: usize,
    mapping: &[Option<usize>],
) -> bool {
    match (local, existing) {
        (TypeKind::Never, TypeKind::Never) => true,
        (TypeKind::Variable(a), TypeKind::Variable(b)) => a == b,
        (TypeKind::Tuple(a), TypeKind::Tuple(b)) => {
            type_slices_match_with_mapping(a, b, world_idx, mapping)
        }
        (TypeKind::Record(a), TypeKind::Record(b)) => {
            tagged_type_slices_match_with_mapping(a, b, world_idx, mapping)
        }
        (TypeKind::Variant(a), TypeKind::Variant(b)) => {
            tagged_type_slices_match_with_mapping(a, b, world_idx, mapping)
        }
        (TypeKind::Function(a), TypeKind::Function(b)) => {
            a.effects == b.effects
                && a.args.len() == b.args.len()
                && a.args.iter().zip(&b.args).all(|(a, b)| {
                    a.mut_ty == b.mut_ty
                        && type_matches_with_mapping(a.ty, b.ty, world_idx, mapping)
                })
                && type_matches_with_mapping(a.ret, b.ret, world_idx, mapping)
        }
        (TypeKind::Native(a), TypeKind::Native(b)) => {
            a.bare_ty == b.bare_ty
                && type_slices_match_with_mapping(&a.arguments, &b.arguments, world_idx, mapping)
        }
        (TypeKind::Named(a), TypeKind::Named(b)) => {
            a.def == b.def
                && type_slices_match_with_mapping(&a.params, &b.params, world_idx, mapping)
        }
        _ => false,
    }
}

fn type_slices_match_with_mapping(
    local: &[Type],
    existing: &[Type],
    world_idx: usize,
    mapping: &[Option<usize>],
) -> bool {
    local.len() == existing.len()
        && local.iter().zip(existing).all(|(&local, &existing)| {
            type_matches_with_mapping(local, existing, world_idx, mapping)
        })
}

fn tagged_type_slices_match_with_mapping(
    local: &[(Ustr, Type)],
    existing: &[(Ustr, Type)],
    world_idx: usize,
    mapping: &[Option<usize>],
) -> bool {
    local.len() == existing.len()
        && local.iter().zip(existing).all(
            |(&(local_name, local_ty), &(existing_name, existing_ty))| {
                local_name == existing_name
                    && type_matches_with_mapping(local_ty, existing_ty, world_idx, mapping)
            },
        )
}

fn type_matches_with_mapping(
    local: Type,
    existing: Type,
    world_idx: usize,
    mapping: &[Option<usize>],
) -> bool {
    if !local.is_local() {
        return local == existing;
    }
    let Some(mapped_idx) = mapping.get(local.index as usize).copied().flatten() else {
        return false;
    };
    Type::new_global(world_idx as u32, mapped_idx as u32) == existing
}

/// A mapping from a local world to a global world
#[derive(Debug, Clone)]
struct WorldMapping {
    /// The index of the global world
    world_idx: usize,
    /// The mapping from local indices to global indices in the global world
    local_to_global_map: Vec<u32>,
}

/// The type universe, containing all known types organized in worlds.
#[derive(Debug)]
struct TypeUniverse {
    /// The list of worlds, each being a set of types.
    /// The first world (index 0) is the global non-recursive world.
    /// Subsequent worlds contain SCC of recursive types.
    worlds: Vec<TypeWorld>,
    /// A cache mapping local worlds to their corresponding global world and index mapping.
    /// This is used to intern types efficiently.
    local_to_world: FxHashMap<Vec<TypeKind>, WorldMapping>,
}

impl TypeUniverse {
    fn new_empty() -> Self {
        Self {
            worlds: vec![IndexSet::new()],
            local_to_world: FxHashMap::default(),
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

        // Partition tks into sub-graphs of strongly connected recursive types.
        let sorted_sccs = if kinds.len() == 1 {
            vec![vec![0]]
        } else {
            let sccs = find_strongly_connected_components(&kinds);
            let mut sorted_sccs = topological_sort_sccs(&kinds, &sccs);
            sorted_sccs.reverse();
            sorted_sccs
        };

        // TODO: somewhere, renormalize generics to be in the same order.

        // For each strongly connected component, starting from the leaves...
        // Note: Using local types as placeholders to build the array without having to
        // get a recursive lock on the universe.
        let mut types = vec![Type::new_local(0); kinds.len()];
        // Resolved global types per input index. Indexed by `input_index`
        // (0..kinds.len()); `None` means not yet resolved.
        let mut resolved: Vec<Option<Type>> = vec![None; kinds.len()];
        sorted_sccs
            .into_iter()
            .flat_map(|mut input_indices| {
                // Replace the already-processed local types with their true values in the type kind.
                input_indices.iter().for_each(|input_index| {
                    kinds[*input_index].for_each_inner_type_mut(|ty| {
                        if ty.is_local() {
                            if let Some(resolved_ty) = resolved[ty.index as usize] {
                                *ty = resolved_ty;
                            }
                        }
                    })
                });

                // Detect singletons and put them in the main world if they have no cycle.
                if input_indices.len() == 1 {
                    let input_index = input_indices[0];
                    let kind = &kinds[input_index];
                    if let Some(worlds_to_check) = kind.recursive_worlds_if_no_local_refs() {
                        let resolved_ty = self.insert_non_recursive_kind(kind, worlds_to_check);
                        resolved[input_index] = Some(resolved_ty);
                        return vec![(input_index, resolved_ty)];
                    }
                }

                // Sort each sub-graph, for early existing world matching.
                input_indices.sort_by(|&a, &b| {
                    // Note: ignore local types while sorting.
                    kinds[a].local_cmp(&kinds[b])
                });

                // Renormalize local indices and store into local world.
                // `subst_to_local[input_index] = local_index` for the SCC's
                // members; `u32::MAX` for unrelated input indices (which
                // `substitute_locals` will panic on if encountered).
                let mut subst_to_local: Vec<u32> = vec![u32::MAX; kinds.len()];
                for (local_index, &input_index) in input_indices.iter().enumerate() {
                    subst_to_local[input_index] = local_index as u32;
                }
                let local_world: Vec<_> = input_indices
                    .iter()
                    .map(|&index| {
                        let mut kind = kinds[index].clone();
                        kind.substitute_locals(&subst_to_local);
                        kind
                    })
                    .collect();
                assert!(local_world.iter().all(|kind| {
                    let mut valid = true;
                    kind.for_each_inner_type(|ty| {
                        if ty.is_local() && (ty.index as usize) >= local_world.len() {
                            valid = false;
                        }
                    });
                    valid
                }));

                // Some helper functions to get the global indices from the local input indices.
                let global_world_indices = |mapping: &WorldMapping| -> Vec<(usize, Type)> {
                    let world_index = mapping.world_idx;
                    input_indices
                        .iter()
                        .enumerate()
                        .map(|(local_idx, &input_index)| {
                            let global_idx = mapping.local_to_global_map[local_idx];
                            (
                                input_index,
                                Type::new_global(world_index as u32, global_idx),
                            )
                        })
                        .collect()
                };
                let mut mark_indices_as_resolved = |indices_and_tys: &[(usize, Type)]| {
                    indices_and_tys
                        .iter()
                        .for_each(|(input_index, resolved_ty)| {
                            assert!(!resolved_ty.is_local());
                            assert!(resolved[*input_index].is_none());
                            resolved[*input_index] = Some(*resolved_ty);
                        });
                };

                // Local world is now a key, is it a known global world?
                if let Some(mapping) = self.local_to_world.get(&local_world) {
                    // If so, store processed and return.
                    let indices_and_tys = global_world_indices(mapping);
                    mark_indices_as_resolved(&indices_and_tys);
                    return indices_and_tys;
                }

                // Before creating a new world, check if any existing recursive world
                // (world index > 0) is structurally equivalent to local_world.
                // This catches cases where type inference creates a new SCC that's
                // equivalent to an existing canonical recursive type.
                // We need permutation-invariant matching because the internal ordering
                // within worlds may differ due to sorting.
                for (world_idx, existing_world) in self.worlds.iter().enumerate().skip(1) {
                    if existing_world.len() == local_world.len() {
                        // Try to find a bijection (permutation) from local indices to existing world indices
                        // such that when we remap local_world using this bijection, it matches existing_world
                        if let Some(local_to_global_map) =
                            find_world_isomorphism(&local_world, existing_world, world_idx)
                        {
                            // Found an equivalent world! Return types from that world using the mapping
                            // Build the result by mapping each local index (0..n) to its corresponding global type,
                            // local_to_global_map[local_idx] gives the corresponding index in existing_world.
                            let indices_and_tys: Vec<_> = input_indices
                                .iter()
                                .enumerate()
                                .map(|(local_idx, &input_idx)| {
                                    let global_idx = local_to_global_map[local_idx];
                                    let ty = Type {
                                        world: Some(NonMaxU32::new(world_idx as u32).unwrap()),
                                        index: global_idx,
                                    };
                                    (input_idx, ty)
                                })
                                .collect();
                            mark_indices_as_resolved(&indices_and_tys);
                            // Cache this for future lookups.
                            let mapping = WorldMapping {
                                world_idx,
                                local_to_global_map,
                            };
                            self.local_to_world.insert(local_world.clone(), mapping);
                            return indices_and_tys;
                        }
                    }
                }

                // If not, create a new one.
                let global_world_index = self.worlds.len() as u32;
                let mapping = WorldMapping {
                    world_idx: global_world_index as usize,
                    local_to_global_map: (0..local_world.len() as u32).collect(),
                };
                self.local_to_world
                    .insert(local_world.clone(), mapping.clone());

                // Renormalize local indices to global indices.
                let kinds_renormalized: Vec<TypeKind> = local_world
                    .into_iter()
                    .map(|mut td| {
                        td.for_each_inner_type_mut(|ty| {
                            if ty.is_local() {
                                ty.world = Some(NonMaxU32::new(global_world_index).unwrap());
                            }
                        });
                        td
                    })
                    .collect();
                let summaries = self.compute_scc_summaries(&kinds_renormalized, global_world_index);
                let global_world: IndexSet<_> = kinds_renormalized
                    .into_iter()
                    .zip(summaries)
                    .map(|(kind, summary)| InternedType { kind, summary })
                    .collect();
                self.worlds.push(global_world);

                // Collect indices, store processed and return.
                let indices_and_tys = global_world_indices(&mapping);
                mark_indices_as_resolved(&indices_and_tys);
                indices_and_tys
            })
            .for_each(|(ty_index, ty)| types[ty_index] = ty);
        types
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
    guard: std::sync::RwLockReadGuard<'a, TypeUniverse>,
}
impl std::ops::Deref for TypeDataRef<'_> {
    type Target = TypeKind;
    fn deref(&self) -> &Self::Target {
        self.guard.get_type_data(self.ty)
    }
}

pub struct TypeSummaryRef<'a> {
    ty: Type,
    guard: std::sync::RwLockReadGuard<'a, TypeUniverse>,
}
impl std::ops::Deref for TypeSummaryRef<'_> {
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
    use crate::{
        CompilerSession,
        std::{
            array::array_type,
            logic::bool_type,
            math::{Int, int_type},
            string::string_type,
        },
    };

    use super::*;

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
        assert!(FnReturnConvention::Value.can_satisfy(FnReturnConvention::Value));
        assert!(!FnReturnConvention::Value.can_satisfy(FnReturnConvention::YieldedOnce));
        assert!(!FnReturnConvention::Value.can_satisfy(FnReturnConvention::AddressorPlace));

        assert!(!FnReturnConvention::YieldedOnce.can_satisfy(FnReturnConvention::Value));
        assert!(FnReturnConvention::YieldedOnce.can_satisfy(FnReturnConvention::YieldedOnce));
        assert!(!FnReturnConvention::YieldedOnce.can_satisfy(FnReturnConvention::AddressorPlace));

        assert!(FnReturnConvention::AddressorPlace.can_satisfy(FnReturnConvention::Value));
        assert!(FnReturnConvention::AddressorPlace.can_satisfy(FnReturnConvention::YieldedOnce));
        assert!(FnReturnConvention::AddressorPlace.can_satisfy(FnReturnConvention::AddressorPlace));
    }

    /// Wrap a `TypeKind` in an `InternedType` with an empty summary, for tests
    /// that only exercise the structural-isomorphism logic which never reads
    /// the summary.
    fn test_interned(kind: TypeKind) -> InternedType {
        InternedType {
            kind,
            summary: TypeSummary::default(),
        }
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
    fn recursive_variant_with_peeling() {
        // Test that different "peelings" of the same recursive type intern correctly
        // This simulates what happens during unification

        let int = int_type();
        let string = string_type();

        // Original: Variant = Array([Variant]) | Int(int) | String(string)
        let variant_original = TypeKind::Variant(vec![
            (ustr("Array"), Type::tuple([array_type(Type::new_local(0))])),
            (ustr("Int"), Type::tuple([int])),
            (ustr("String"), Type::tuple([string])),
        ]);
        let stored_original = store_type(variant_original);

        // Peeled once: the Array payload now contains the full variant definition
        // Array([Array([Variant]) | Int(int) | String(string)]) | Int(int) | String(string)
        let variant_peeled = TypeKind::Variant(vec![
            (ustr("Array"), Type::tuple([array_type(stored_original)])),
            (ustr("Int"), Type::tuple([int])),
            (ustr("String"), Type::tuple([string])),
        ]);
        let stored_peeled = store_type(variant_peeled);

        // These should be recognized as the same equirecursive type
        // However, they currently won't be because stored_original is already resolved
        // This test documents the current limitation
        println!("Original: {:?}", stored_original);
        println!("Peeled: {:?}", stored_peeled);

        // For now, just verify they're both valid types
        assert!(stored_original.world().is_some());
        assert!(stored_peeled.world().is_some());
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

        let mut source_table = crate::parser::location::SourceTable::default();
        crate::std::std_module(&mut source_table);

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
        // This test demonstrates the key issue: when a recursive variant is "unfolded"
        // during unification, does it create an equivalent type?

        let int = int_type();
        let string = string_type();

        // Original recursive Variant type:
        // V = Array([V]) | Int(int) | String(string)
        let v_def = TypeKind::Variant(vec![
            (ustr("Array"), Type::tuple([array_type(Type::new_local(0))])),
            (ustr("Int"), Type::tuple([int])),
            (ustr("String"), Type::tuple([string])),
        ]);
        let v = store_type(v_def);

        // Now create the "unfolded" version where Array's payload explicitly contains V:
        // V_unfolded = Array([Array([V]) | Int(int) | String(string)]) | Int(int) | String(string)
        let v_unfolded_def = TypeKind::Variant(vec![
            (ustr("Array"), Type::tuple([array_type(v)])),
            (ustr("Int"), Type::tuple([int])),
            (ustr("String"), Type::tuple([string])),
        ]);
        let v_unfolded = store_type(v_unfolded_def);

        // These are equirecursive - they represent the same infinite tree
        // With proper recursive type handling, they should be recognized as equal
        println!("Original:  {:?}", v);
        println!("Unfolded:  {:?}", v_unfolded);
        println!("Are equal: {}", v == v_unfolded);

        // Currently this will likely fail because the interning doesn't recognize
        // that unfolding a recursive type creates the same structure
        // This documents the limitation that needs to be fixed

        // For now, just ensure both are valid
        assert!(v.world().is_some());
        assert!(v_unfolded.world().is_some());

        // The REAL fix would make this assertion pass:
        // assert_eq!(v, v_unfolded, "Equirecursive types should be recognized as equal");
    }

    #[test]
    fn test_find_world_isomorphism_recursive() {
        // Test recursive references
        // Local: [Array([local[0]]), Tuple([int, local[0]])]
        // Existing: [Array([global[1, 0]]), Tuple([int, global[1, 0]])]
        let int = int_type();

        let local_world = vec![
            container_kind(Type::new_local(0)),
            TypeKind::Tuple(vec![int, Type::new_local(0)]),
        ];

        let mut existing_world = IndexSet::new();
        existing_world.insert(test_interned(container_kind(Type::new_global(1, 0))));
        existing_world.insert(test_interned(TypeKind::Tuple(vec![
            int,
            Type::new_global(1, 0),
        ])));

        let mapping = find_world_isomorphism(&local_world, &existing_world, 1);

        assert!(
            mapping.is_some(),
            "Should find isomorphism for recursive worlds"
        );
        let mapping = mapping.unwrap();

        assert_eq!(mapping.len(), 2);
        assert_eq!(mapping[0], 0);
        assert_eq!(mapping[1], 1);
    }

    #[test]
    fn test_find_world_isomorphism_variant_case() {
        // THIS IS THE KEY TEST - simulates the real Variant case
        // Simplified: two mutually recursive types where order matters

        // Local: [Array([local[1]]), Variant{V(local[0]), Tuple(local[0], )}]
        let local_world = vec![
            // local[0] = Array([local[1]])
            container_kind(Type::new_local(1)),
            // local[1] = Variant with field referencing local[0]
            TypeKind::Variant(vec![(ustr("V"), Type::new_local(2))]),
            TypeKind::Tuple(vec![Type::new_local(0)]), // local[2] = Tuple([local[0]])
        ];

        // Existing: [Variant{V(global[1,1])}, Array([global[1,0]])]
        // Same types but REVERSED order
        let mut existing_world = IndexSet::new();
        existing_world.insert(test_interned(TypeKind::Variant(vec![(
            ustr("V"),
            Type::new_global(1, 2),
        )])));
        existing_world.insert(test_interned(container_kind(Type::new_global(1, 0))));
        existing_world.insert(test_interned(TypeKind::Tuple(vec![Type::new_global(1, 1)])));

        let mapping = find_world_isomorphism(&local_world, &existing_world, 1);

        assert!(mapping.is_some(), "Should find isomorphism");
        let mapping = mapping.unwrap();

        assert_eq!(mapping.len(), 3);

        // After remapping:
        // local[0] = Array([local[1]]) -> Array([global[1,?]])
        //   where local[1] maps to some global index
        // local[1] = Variant{V(local[0])} -> Variant{V(global[1,?])}
        //   where local[0] maps to some global index

        // For this to be valid:
        // - local[0] must map to existing[1] (the Array)
        // - local[1] must map to existing[0] (the Variant)

        assert_eq!(mapping[0], 1, "local[0] (Array) should map to existing[1]");
        assert_eq!(
            mapping[1], 0,
            "local[1] (Variant) should map to existing[0]"
        );
        assert_eq!(mapping[2], 2, "local[2] (Tuple) should map to existing[2]");
    }

    #[test]
    fn test_find_world_isomorphism_ambiguous() {
        // Test case with ambiguous matching - two structurally similar types
        // This is the REAL bug case: when there are multiple valid isomorphisms

        // Both types are self-referential in structurally similar ways
        // Local: [Array([local[0]]), Array([local[1]])]
        let local_world = vec![
            container_kind(Type::new_local(0)),
            container_kind(Type::new_local(1)),
        ];

        // Existing: [Array([global[1,0]]), Array([global[1,1]])]
        let mut existing_world = IndexSet::new();
        existing_world.insert(test_interned(container_kind(Type::new_global(1, 0))));
        existing_world.insert(test_interned(container_kind(Type::new_global(1, 1))));

        let mapping = find_world_isomorphism(&local_world, &existing_world, 1);

        // There are two valid isomorphisms:
        // 1. [0->0, 1->1] (identity)
        // 2. [0->1, 1->0] (swap)
        // Both are structurally valid!

        assert!(mapping.is_some(), "Should find an isomorphism");
        let mapping = mapping.unwrap();

        // The algorithm should pick one consistently, but which one?
        // The identity mapping [0->0, 1->1] is semantically correct
        assert_eq!(mapping.len(), 2);

        // Ideally we want identity mapping, but the algorithm might find either
        // This test documents the ambiguity problem
    }
}
