// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::any::type_name;
use std::any::TypeId;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Display;
use std::fmt::{self, Debug};
use std::hash::Hash;
use std::iter;
use std::sync::OnceLock;
use std::sync::RwLock;

use crate::containers::FromIndex;
use crate::graph::find_strongly_connected_components;
use crate::graph::topological_sort_sccs;
use crate::type_like::CastableToType;
use crate::type_like::TypeLike;
use crate::type_mapper::TypeMapper;
use crate::type_visitor::TypeInnerVisitor;
use crate::value::Value;
use crate::Location;
use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use indexmap::IndexSet;
use nonmax::NonMaxU32;
use ustr::{ustr, Ustr};

use crate::assert::assert_unique_strings;
use crate::containers::compare_by;
use crate::containers::{b, B};
use crate::effects::EffType;
use crate::effects::EffectVar;
use crate::format::type_variable_index_to_string_greek;
use crate::format::type_variable_index_to_string_latin;
use crate::graph;
use crate::module::FmtWithModuleEnv;
use crate::module::ModuleEnv;
use crate::mutability::MutType;
use crate::sync::SyncPhantomData;

use crate::typing_env::Local;

#[macro_export]
macro_rules! cached_primitive_ty {
    ($ty:ty) => {{
        $crate::cached_ty!(Type::primitive::<$ty>)
    }};
}

#[macro_export]
macro_rules! cached_ty {
    ($ty:expr) => {{
        static TY: std::sync::OnceLock<Type> = std::sync::OnceLock::new();
        *TY.get_or_init($ty)
    }};
}

/// A generic variable for a type
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeVar {
    /// The name of this type variable, its identity in the context considered
    name: u32,
}

impl TypeVar {
    pub fn new(name: u32) -> Self {
        Self { name }
    }
    pub fn name(&self) -> u32 {
        self.name
    }
    pub fn format_rust_style(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", type_variable_index_to_string_latin(self.name))
    }
    pub fn format_math_style(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", type_variable_index_to_string_greek(self.name))
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
}

impl FmtWithModuleEnv for B<dyn BareNativeType> {
    fn fmt_with_module_env(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        match env.bare_native_name(self) {
            Some(name) => write!(f, "{name}"),
            None => write!(f, "{}", self.as_ref().type_name()),
        }
    }
}

pub fn bare_native_type<T: 'static>() -> B<dyn BareNativeType> {
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
}

impl Debug for dyn BareNativeType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.type_name())
    }
}

/// A generic type implemented in Rust.
/// If arguments is empty, we call it a primitive type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NativeType {
    pub bare_ty: B<dyn BareNativeType>,
    pub arguments: Vec<Type>,
}

impl NativeType {
    pub fn new(bare_ty: B<dyn BareNativeType>, arguments: Vec<Type>) -> Self {
        Self { bare_ty, arguments }
    }
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

impl FmtWithModuleEnv for NativeType {
    fn fmt_with_module_env(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        self.bare_ty.fmt_with_module_env(f, env)?;
        if !self.arguments.is_empty() {
            write!(f, "<")?;
            for (i, ty) in self.arguments.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                ty.fmt_with_module_env(f, env)?;
            }
            write!(f, ">")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FnArgType {
    pub ty: Type,
    pub mut_ty: MutType,
}
impl FnArgType {
    pub fn new(ty: Type, mut_ty: MutType) -> Self {
        Self { ty, mut_ty }
    }
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
impl FmtWithModuleEnv for FnArgType {
    fn fmt_with_module_env(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        self.mut_ty.format_in_fn_arg(f)?;
        self.ty.fmt_with_module_env(f, env)
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

    pub fn new_mut_resolved(args: &[(Type, bool)], ret: Type, effects: EffType) -> Self {
        Self {
            args: args
                .iter()
                .map(|(ty, mutable)| FnArgType::new(*ty, MutType::from(*mutable)))
                .collect(),
            ret,
            effects,
        }
    }

    pub fn new_by_val(args: &[Type], ret: Type, effects: EffType) -> Self {
        Self {
            args: args
                .iter()
                .map(|&ty| FnArgType {
                    ty,
                    mut_ty: MutType::constant(),
                })
                .collect(),
            ret,
            effects,
        }
    }

    pub fn as_locals_no_bound(&self, arg_names: &[(Ustr, Location)]) -> Vec<Local> {
        arg_names
            .iter()
            .zip(self.args.iter())
            .map(|((name, span), arg)| Local::new(*name, arg.mut_ty, arg.ty, *span))
            .collect()
    }

    pub fn args_ty(&self) -> impl Iterator<Item = Type> + '_ {
        self.args.iter().map(|arg| arg.ty)
    }

    fn local_cmp(&self, other: &Self) -> Ordering {
        compare_by(&self.args, &other.args, FnArgType::local_cmp)
            .then(self.ret.local_cmp(&other.ret))
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

    fn fill_with_input_effect_vars(&self, vars: &mut HashSet<EffectVar>) {
        for arg in &self.args {
            arg.ty.fill_with_inner_effect_vars(vars);
        }
        self.ret.fill_with_inner_effect_vars(vars);
    }

    fn fill_with_output_effect_vars(&self, vars: &mut HashSet<EffectVar>) {
        self.effects.fill_with_inner_effect_vars(vars);
    }
}

impl CastableToType for FnType {
    fn to_type(&self) -> Type {
        Type::function_type(self.clone())
    }
}

impl FmtWithModuleEnv for FnType {
    fn fmt_with_module_env(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            arg.fmt_with_module_env(f, env)?;
        }
        write!(f, ") -> ")?;
        self.ret.fmt_with_module_env(f, env)?;
        if self.effects.is_empty() {
            Ok(())
        } else {
            write!(f, " ! {}", self.effects)
        }
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

    pub fn primitive<T: Clone + 'static>() -> Self {
        Self::native::<T>(vec![])
    }

    pub fn native<T: Clone + 'static>(arguments: Vec<Type>) -> Self {
        let bare_ty = bare_native_type::<T>();
        TypeKind::Native(b(NativeType { arguments, bare_ty })).store()
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

    pub fn variant(types: Vec<(Ustr, Self)>) -> Self {
        TypeKind::Variant(types).store()
    }

    pub fn tuple(elements: Vec<Self>) -> Self {
        TypeKind::Tuple(elements).store()
    }

    pub fn record(fields: Vec<(Ustr, Self)>) -> Self {
        TypeKind::Record(fields).store()
    }

    pub fn function_type(ty: FnType) -> Self {
        TypeKind::Function(b(ty)).store()
    }

    pub fn function_by_val_with_effects(args: &[Self], ret: Self, effects: EffType) -> Self {
        Self::function_type(FnType::new_by_val(args, ret, effects))
    }

    pub fn function_by_val(args: &[Self], ret: Self) -> Self {
        Self::function_by_val_with_effects(args, ret, EffType::empty())
    }

    pub fn nullary_function_by_val(ret: Self) -> Self {
        Self::function_by_val(&[], ret)
    }

    pub fn unary_function_by_val(arg: Self, ret: Self) -> Self {
        Self::function_by_val(&[arg], ret)
    }

    pub fn binary_function_by_val(arg1: Self, arg2: Self, ret: Self) -> Self {
        Self::function_by_val(&[arg1, arg2], ret)
    }

    pub fn new_type(name: Ustr, ty: Self) -> Self {
        TypeKind::Newtype(name, ty).store()
    }

    pub fn never() -> Self {
        static TY: OnceLock<Type> = OnceLock::new();
        *TY.get_or_init(|| TypeKind::Never.store())
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

    pub fn data<'t>(self) -> TypeDataRef<'t> {
        let guard = types().read().unwrap();
        TypeDataRef { ty: self, guard }
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
            static TYPE_VISITED: RefCell<HashSet<Type>> = RefCell::new(HashSet::new());
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
        self.with_cycle_detection(
            |ty, _| {
                let kind = ty.data().clone();
                let new_ty = kind.map(f);
                f.map_type(new_ty)
            },
            |ty, _| *ty,
            (),
        )
    }

    fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
        self.data().visit(visitor)
    }
}

impl CastableToType for Type {
    fn to_type(&self) -> Type {
        *self
    }
}

impl FmtWithModuleEnv for Type {
    fn fmt_with_module_env(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        // If we have a name for this type, use it
        if let Some(name) = env.type_name(*self) {
            return write!(f, "{}", name);
        }

        self.with_cycle_detection(
            |ty, (f, env)| ty.data().fmt_with_module_env(f, env),
            |_, (f, _)| write!(f, "Self"),
            (f, env),
        )
    }
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

pub type TypeSubstitution = HashMap<TypeVar, Type>;

/// Named types
#[derive(Debug, Clone, Default)]
pub struct TypeAliases {
    name_to_type: HashMap<Ustr, Type>,
    type_to_name: HashMap<Type, Ustr>,
    bare_native_to_name: HashMap<B<dyn BareNativeType>, Ustr>,
}
impl TypeAliases {
    // TODO: handle errors
    pub fn set(&mut self, alias: &str, ty: Type) {
        let alias = ustr(alias);
        self.set_with_ustr(alias, ty);
    }

    pub fn set_with_ustr(&mut self, alias: Ustr, ty: Type) {
        self.name_to_type.insert(alias, ty);
        self.type_to_name.insert(ty, alias);
    }

    pub fn get_name(&self, ty: Type) -> Option<Ustr> {
        self.type_to_name.get(&ty).copied()
    }
    pub fn get_type(&self, name: &str) -> Option<Type> {
        let name = ustr(name);
        self.name_to_type.get(&name).copied()
    }

    pub fn set_bare_native(&mut self, alias: &str, bare: B<dyn BareNativeType>) {
        let alias = ustr(alias);
        self.bare_native_to_name.insert(bare, alias);
    }

    pub fn get_bare_native_name(&self, bare: &B<dyn BareNativeType>) -> Option<Ustr> {
        self.bare_native_to_name.get(bare).copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Ustr, &Type)> {
        self.name_to_type.iter()
    }

    pub fn extend(&mut self, other: Self) {
        self.name_to_type.extend(other.name_to_type);
        self.type_to_name.extend(other.type_to_name);
        self.bare_native_to_name.extend(other.bare_native_to_name);
    }
    pub fn is_empty(&self) -> bool {
        self.name_to_type.is_empty()
            && self.type_to_name.is_empty()
            && self.bare_native_to_name.is_empty()
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
    /// A named newtype
    Newtype(Ustr, Type),
    /// Bottom type
    Never,
}
// TODO: traits as bounds of generics

impl TypeKind {
    /// Store in the type system and return a type identifier
    pub fn store(self) -> Type {
        store_type(self)
    }

    /// Return true if the type variable is only found in variants
    pub fn is_ty_var_only_in_variants(&self, ty_var: TypeVar) -> bool {
        struct Visitor {
            ty_var: TypeVar,
            depth: usize,
            variant_start: Option<usize>,
            output: bool,
        }
        impl TypeInnerVisitor for Visitor {
            fn visit_ty_kind_start(&mut self, ty: &TypeKind) {
                if self.variant_start.is_none() {
                    if ty.is_variant() {
                        self.variant_start = Some(self.depth);
                    } else if let Some(var) = ty.as_variable() {
                        if var == &self.ty_var {
                            self.output = false;
                        }
                    }
                }
                self.depth += 1;
            }

            fn visit_ty_kind_end(&mut self, _ty: &TypeKind) {
                self.depth -= 1;
                if let Some(start_depth) = self.variant_start {
                    if start_depth == self.depth {
                        self.variant_start = None;
                    }
                }
            }
        }

        let mut visitor = Visitor {
            ty_var,
            depth: 0,
            variant_start: None,
            output: true,
        };
        self.visit(&mut visitor);
        visitor.output
    }

    /// Apply f recursively to content
    pub fn map(&self, f: &mut impl TypeMapper) -> Type {
        use TypeKind::*;
        match self {
            Variable(var) => Type::variable(*var),
            Native(native_ty) => Type::native_type(NativeType::new(
                native_ty.bare_ty.clone(),
                native_ty.arguments.iter().map(|ty| ty.map(f)).collect(),
            )),
            Variant(types) => {
                Type::variant(types.iter().map(|(name, ty)| (*name, ty.map(f))).collect())
            }
            Tuple(tuple) => Type::tuple(tuple.iter().map(|ty| ty.map(f)).collect()),
            Record(fields) => {
                Type::record(fields.iter().map(|(name, ty)| (*name, ty.map(f))).collect())
            }
            Function(fn_type) => Type::function_type(fn_type.map(f)),
            Newtype(name, ty) => Type::new_type(*name, ty.map(f)),
            Never => Type::never(),
        }
    }

    /// Visit this type, allowing for multiple traversal strategies thanks to the TypeInnerVisitor trait.
    pub(crate) fn visit(&self, visitor: &mut impl TypeInnerVisitor) {
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
            Newtype(_, ty) => process_ty(*ty, visitor),
        };

        // process self
        visitor.visit_ty_kind_end(self);
    }

    pub fn inner_types(&self) -> B<dyn Iterator<Item = Type> + '_> {
        use TypeKind::*;
        match self {
            Native(g) => b(g.arguments.iter().copied()),
            Variable(_) => b(iter::empty()),
            Variant(types) => b(types.iter().map(|(_, ty)| *ty)),
            Tuple(types) => b(types.iter().copied()),
            Record(fields) => b(fields.iter().map(|(_, ty)| *ty)),
            Function(function) => b(function
                .args
                .iter()
                .map(|arg| arg.ty)
                .chain(iter::once(function.ret))),
            Newtype(_, ty) => b(iter::once(*ty)),
            Never => b(iter::empty()),
        }
    }

    pub fn inner_types_mut(&mut self) -> B<dyn Iterator<Item = &mut Type> + '_> {
        use TypeKind::*;
        match self {
            Native(g) => b(g.arguments.iter_mut()),
            Variable(_) => b(iter::empty()),
            Variant(types) => b(types.iter_mut().map(|(_, ty)| ty)),
            Tuple(types) => b(types.iter_mut()),
            Record(fields) => b(fields.iter_mut().map(|(_, ty)| ty)),
            Function(function) => b(function
                .args
                .iter_mut()
                .map(|arg| &mut arg.ty)
                .chain(iter::once(&mut function.ret))),
            Newtype(_, ty) => b(iter::once(ty)),
            Never => b(iter::empty()),
        }
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

    /// Substitute the indices of local types using subst
    fn substitute_locals(&mut self, subst: &HashMap<u32, u32>) {
        self.inner_types_mut().for_each(|ty| {
            if ty.world().is_none() {
                ty.index = *subst.get(&ty.index).unwrap_or_else(|| {
                    panic!(
                        "Local type index {} not found in substitution {subst:?}",
                        ty.index
                    )
                });
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
            Newtype(_, _) => 7,
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
            Variant(items) => items.sort_by(|(a, _), (b, _)| a.cmp(b)),
            Record(fields) => fields.sort_by(|a, b| a.0.cmp(&b.0)),
            _ => (),
        }
    }

    /// If all values can be exhaustively enumerated, return them,
    pub fn all_values(&self) -> Option<Vec<Value>> {
        // The maximum cardinality for a type to agree to be enumerated
        const MAX_CARDINALITY: usize = 1000;
        use TypeKind::*;
        match self {
            Native(native) => {
                if native.arguments.is_empty() {
                    if native.bare_ty == bare_native_type::<()>() {
                        Some(vec![Value::unit()])
                    } else if native.bare_ty == bare_native_type::<bool>() {
                        Some(vec![Value::native(false), Value::native(true)])
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Tuple(elements) => {
                let mut cardinality = 1;
                let element_values = elements
                    .iter()
                    .map(|element| {
                        let all_values = element.data().all_values()?;
                        cardinality *= all_values.len();
                        Some(all_values)
                    })
                    .collect::<Option<Vec<_>>>()?;
                if cardinality > MAX_CARDINALITY {
                    None
                } else {
                    // We do the Cartesian product of the values of the tuple elements
                    let mut result = vec![vec![]];
                    for pool in element_values {
                        let mut new_result = Vec::new();
                        for prefix in &result {
                            for item in &pool {
                                let mut new_prefix = prefix.clone();
                                new_prefix.push(item.clone());
                                new_result.push(new_prefix);
                            }
                        }
                        result = new_result;
                    }
                    let result = result.into_iter().map(Value::tuple).collect::<Vec<_>>();
                    Some(result)
                }
            }
            Never => Some(vec![]),
            _ => None,
        }
    }
}

impl FmtWithModuleEnv for TypeKind {
    fn fmt_with_module_env(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        use TypeKind::*;
        match self {
            Variable(var) => write!(f, "{var}"),
            Native(native) => {
                use crate::std::array::Array;
                if native.bare_ty == bare_native_type::<Array>() {
                    write!(f, "[")?;
                    native.arguments[0].fmt_with_module_env(f, env)?;
                    write!(f, "]")
                } else {
                    native.fmt_with_module_env(f, env)
                }
            }
            Variant(types) => {
                for (i, (name, ty)) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    if *ty == Type::unit() {
                        write!(f, "{name}")?;
                    } else {
                        write!(f, "{name} ")?;
                        if ty.data().is_tuple() {
                            ty.fmt_with_module_env(f, env)?;
                        } else {
                            write!(f, "(")?;
                            ty.fmt_with_module_env(f, env)?;
                            write!(f, ")")?;
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
                    ty.fmt_with_module_env(f, env)?;
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
                    write!(f, "{name}: ")?;
                    ty.fmt_with_module_env(f, env)?;
                }
                write!(f, " }}")
            }
            Function(function) => function.fmt_with_module_env(f, env),
            Newtype(name, ty) => {
                write!(f, "{name}(")?;
                ty.fmt_with_module_env(f, env)?;
                write!(f, ")")
            }
            Never => write!(f, "never"),
        }
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
        self.inner_types()
            .filter(|t| t.is_local())
            .map(Type::index)
            .collect::<Vec<_>>()
            .into_iter()
    }
}

type TypeWorld = IndexSet<TypeKind>;

struct TypeUniverse {
    worlds: Vec<TypeWorld>,
    local_to_world: HashMap<Vec<TypeKind>, usize>,
}

impl TypeUniverse {
    fn new() -> Self {
        Self {
            worlds: vec![IndexSet::new()],
            local_to_world: HashMap::new(),
        }
    }

    fn insert_type(&mut self, tk: TypeKind) -> Type {
        self.insert_types(&[tk])[0]
    }

    fn insert_types(&mut self, kinds: impl Into<Vec<TypeKind>>) -> Vec<Type> {
        let mut kinds: Vec<_> = kinds.into();
        kinds.iter_mut().for_each(TypeKind::normalize);
        // Partition tks into sub-graphs of strongly connected recursive types.
        let sccs = find_strongly_connected_components(&kinds);
        let mut sorted_sccs = topological_sort_sccs(&kinds, &sccs);
        sorted_sccs.reverse();

        // TODO: somewhere, renormalize generics to be in the same order.

        // For each strongly connected component, starting from the leaves...
        // Note: Using local types as placeholders to build the array without having to
        // get a recursive lock on the universe.
        let mut types = vec![Type::new_local(0); kinds.len()];
        let mut resolved = HashMap::<usize, Type>::new();
        sorted_sccs
            .into_iter()
            .flat_map(|mut input_indices| {
                // Replace the already-processed local types with their true values in the type kind.
                input_indices.iter().for_each(|input_index| {
                    kinds[*input_index].inner_types_mut().for_each(|ty| {
                        if ty.is_local() {
                            if let Some(resolved_ty) = resolved.get(&(ty.index as usize)) {
                                *ty = *resolved_ty;
                            }
                        }
                    })
                });

                // Detect singletons and put them in the main world if they have no cycle.
                if input_indices.len() == 1 {
                    let input_index = input_indices[0];
                    let kind = &kinds[input_index];
                    let inner_all_global = kind.inner_types().all(|ty| !ty.is_local());
                    if inner_all_global {
                        let first_world = &mut self.worlds[0];
                        // Is it already present?
                        let index = if let Some((index, _)) = first_world.get_full(kind) {
                            index
                        } else {
                            first_world.insert_full(kind.clone()).0
                        };
                        let resolved_ty = Type::new_global(0, index as u32);
                        resolved.insert(input_index, resolved_ty);
                        assert!(!resolved_ty.is_local());
                        return vec![(input_index, resolved_ty)];
                    }
                }

                // Sort each sub-graph.
                input_indices.sort_by(|&a, &b| {
                    // Note: ignore local types while sorting.
                    kinds[a].local_cmp(&kinds[b])
                    // TODO: look at permutations for the secondary sorting.
                });

                // Renormalize local indices and store into local world.
                let subst_to_local: HashMap<_, _> = input_indices
                    .iter()
                    .enumerate()
                    .map(|(local_index, &input_index)| (input_index as u32, local_index as u32))
                    .collect();
                let local_world: Vec<_> = input_indices
                    .iter()
                    .map(|&index| {
                        let mut kind = kinds[index].clone();
                        kind.substitute_locals(&subst_to_local);
                        kind
                    })
                    .collect();
                assert!(local_world.iter().all(|kind| kind
                    .inner_types()
                    .filter(|ty| ty.is_local())
                    .all(|ty| (ty.index as usize) < local_world.len())));

                // Some helper functions to get the global indices from the local input indices.
                let global_world_indices = |worlds: &Vec<TypeWorld>, world_index| {
                    let global_world: &TypeWorld = &worlds[world_index];
                    let global_world_size = global_world.len() as u32;
                    b((0..global_world_size)
                        .zip(input_indices)
                        .map(move |(index, input_index)| {
                            (input_index, Type::new_global(world_index as u32, index))
                        }))
                };
                let mut mark_indices_as_resolved = |indices_and_tys: &[(usize, Type)]| {
                    indices_and_tys
                        .iter()
                        .for_each(|(input_index, resolved_ty)| {
                            assert!(!resolved_ty.is_local());
                            let result = resolved.insert(*input_index, *resolved_ty);
                            assert!(result.is_none());
                        });
                };

                // Local world is now a key, is it a known global world?
                if let Some(&index) = self.local_to_world.get(&local_world) {
                    // If so, store processed and return.
                    let indices_and_tys: Vec<_> =
                        global_world_indices(&self.worlds, index).collect();
                    mark_indices_as_resolved(&indices_and_tys);
                    return indices_and_tys;
                }
                // If not, create a new one.
                let global_world_index = self.worlds.len() as u32;
                self.local_to_world
                    .insert(local_world.clone(), global_world_index as usize);

                // Renormalize local indices to global indices and store into global world.
                let global_world: IndexSet<_> = local_world
                    .into_iter()
                    .map(|mut td| {
                        td.inner_types_mut().for_each(|ty| {
                            if ty.is_local() {
                                ty.world = Some(NonMaxU32::new(global_world_index).unwrap());
                            }
                        });
                        td
                    })
                    .collect();
                self.worlds.push(global_world);

                // Collect indices, store processed and return.
                let indices_and_tys: Vec<_> =
                    global_world_indices(&self.worlds, global_world_index as usize).collect();
                mark_indices_as_resolved(&indices_and_tys);
                indices_and_tys
            })
            .for_each(|(ty_index, ty)| types[ty_index] = ty);
        types
    }

    fn get_type_data(&self, r: Type) -> &TypeKind {
        self.worlds[r
            .world
            .expect("Attempted to get type data for local world")
            .get() as usize]
            .get_index(r.index as usize)
            .expect("Attempted to get type data for non-existent type")
    }
}

/// An ergonomic constructor for a tuple type when constructing it from a list of types
pub fn tuple_type(types: impl Into<Vec<Type>>) -> Type {
    Type::tuple(types.into())
}

/// An ergonomic constructor for a variant type when constructing it from a list of strings and types
pub fn variant_type(types: &[(&str, Type)]) -> Type {
    let types = types.iter().map(|(name, ty)| (ustr(name), *ty)).collect();
    Type::variant(types)
}

/// An ergonomic constructor for a record type when constructing it from a list of strings and types
pub fn record_type(fields: &[(&str, Type)]) -> Type {
    let fields = fields.iter().map(|(name, ty)| (ustr(name), *ty)).collect();
    Type::record(fields)
}

fn types() -> &'static RwLock<TypeUniverse> {
    static TYPES: OnceLock<RwLock<TypeUniverse>> = OnceLock::new();
    TYPES.get_or_init(|| RwLock::new(TypeUniverse::new()))
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

pub fn dump_type_world(index: usize, env: &ModuleEnv<'_>) {
    let world: &IndexSet<TypeKind> = &types().read().unwrap().worlds[index];
    for (i, ty) in world.iter().enumerate() {
        println!("{}: {}", i, ty.format_with(env));
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

pub struct TypeNames {
    pub names_to_types: HashMap<Ustr, Type>,
    pub types_to_names: HashMap<Type, Ustr>,
}

#[cfg(test)]
mod tests {
    use crate::{
        parse_concrete_type,
        std::{
            logic::bool_type,
            math::{int_type, Int},
            new_module_using_std, new_std_modules,
        },
    };

    use super::*;

    #[test]
    fn parse_and_format() {
        let std_env = new_std_modules();
        let current_module = new_module_using_std();
        let mod_env = ModuleEnv::new(&current_module, &std_env);
        let check = |name: &str| {
            let ty = parse_concrete_type(name).unwrap();
            let formatted = format!("{}", ty.format_with(&mod_env));
            assert_eq!(name, formatted);
        };
        check("()");
        check("bool");
        check("int");
        check("float");
        check("string");
        check("[int]");
        check("[float]");
        check("(bool,)");
        check("(bool, bool)");
        check("(bool, (string, int))");
        check("{ a: int, b: float }");
        check("{ a: int, b: { c: bool, d: string } }");
        check("None | Some (int)");
        check("Color (string) | RGB (int, int, int)");
        check("[[(string, { age: int, name: string, nick: None | Some (string) })]]");
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
}
