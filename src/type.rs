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

use crate::Location;
use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use indexmap::IndexSet;
use itertools::Itertools;
use nonmax::NonMaxU32;
use ustr::Ustr;

use crate::assert::assert_unique_strings;
use crate::containers::compare_by;
use crate::containers::{b, B};
use crate::effects::EffType;
use crate::effects::EffectVar;
use crate::format::type_variable_index_to_string_greek;
use crate::format::type_variable_index_to_string_latin;
use crate::graph;
use crate::graph::find_disjoint_subgraphs;
use crate::module::FmtWithModuleEnv;
use crate::module::ModuleEnv;
use crate::mutability::MutType;
use crate::sync::SyncPhantomData;
use crate::type_inference::InstSubstitution;
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

/// Something that is a type or part of it, and that can
/// be instantiated and queried for its free type variables.
pub trait TypeLike {
    /// Instantiate the type variables within this type with the given substitutions
    fn instantiate(&self, subst: &InstSubstitution) -> Self;

    /// Return all type variables contained in this type
    fn inner_ty_vars(&self) -> Vec<TypeVar>;

    /// Return all effect variables contained as input (i.e. must be retained)
    fn fill_with_input_effect_vars(&self, vars: &mut HashSet<EffectVar>);

    /// Return all effect variables contained as input (i.e. must be retained)
    fn input_effect_vars(&self) -> HashSet<EffectVar> {
        let mut vars = HashSet::new();
        self.fill_with_input_effect_vars(&mut vars);
        vars
    }

    /// Return all effect variables contained as output (i.e. can be dropped if not used as input)
    fn fill_with_output_effect_vars(&self, _vars: &mut HashSet<EffectVar>) {
        // default no output effect variables
    }

    /// Return all effect variables contained as output (i.e. can be dropped if not used as input)
    fn output_effect_vars(&self) -> HashSet<EffectVar> {
        let mut vars = HashSet::new();
        self.fill_with_output_effect_vars(&mut vars);
        vars
    }

    /// Fill the given set with all effect variables contained in this type, union of input and output ones
    fn fill_with_inner_effect_vars(&self, vars: &mut HashSet<EffectVar>) {
        self.fill_with_input_effect_vars(vars);
        self.fill_with_output_effect_vars(vars);
    }

    /// Return all effect variables contained in this type, union of input and output ones
    fn inner_effect_vars(&self) -> HashSet<EffectVar> {
        let mut vars = HashSet::new();
        self.fill_with_inner_effect_vars(&mut vars);
        vars
    }

    /// Return true if the type does not contain any type or effect variables
    fn is_constant(&self) -> bool {
        self.inner_ty_vars().is_empty() && self.inner_effect_vars().is_empty()
    }
}

/// Something that is like a type and can be casted to a type.
pub trait CastableToType: TypeLike {
    /// Return this as a type
    fn to_type(&self) -> Type;
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
    pub inout: MutType,
}
impl FnArgType {
    pub fn new(ty: Type, inout: MutType) -> Self {
        Self { ty, inout }
    }
    pub fn new_by_val(ty: Type) -> Self {
        Self {
            ty,
            inout: MutType::constant(),
        }
    }
    fn local_cmp(&self, other: &Self) -> Ordering {
        self.ty
            .local_cmp(&other.ty)
            .then(self.inout.cmp(&other.inout))
    }
}
impl FmtWithModuleEnv for FnArgType {
    fn fmt_with_module_env(&self, f: &mut fmt::Formatter, env: &ModuleEnv<'_>) -> fmt::Result {
        self.inout.format_in_fn_arg(f)?;
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
                .map(|(ty, inout)| FnArgType::new(*ty, MutType::from(*inout)))
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
                    inout: MutType::constant(),
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
            .map(|((name, span), arg)| Local::new(*name, arg.inout, arg.ty, *span))
            .collect()
    }

    pub fn args_ty(&self) -> impl Iterator<Item = Type> + '_ {
        self.args.iter().map(|arg| arg.ty)
    }

    fn local_cmp(&self, other: &Self) -> Ordering {
        compare_by(&self.args, &other.args, FnArgType::local_cmp)
            .then(self.ret.local_cmp(&other.ret))
    }

    #[allow(dead_code)]
    fn fold<V: Clone, F>(&self, f: &F, v: V) -> V
    where
        F: Fn(&TypeKind, V) -> V,
    {
        let v = self.args.iter().fold(v, |v, arg| arg.ty.data().fold(f, v));
        self.ret.data().fold(f, v)
    }

    fn fold_in_place<V, F>(&self, f: &F, v: &mut V)
    where
        F: Fn(&TypeKind, &mut V),
    {
        self.args
            .iter()
            .for_each(|arg| arg.ty.data().fold_in_place(f, v));
        self.ret.data().fold_in_place(f, v);
    }

    fn visit(&self, visitor: &mut impl TypeKindVisitor) {
        self.args
            .iter()
            .for_each(|arg| arg.ty.data().visit(visitor));
        self.ret.data().visit(visitor);
    }
}

impl TypeLike for FnType {
    fn instantiate(&self, subst: &InstSubstitution) -> Self {
        Self {
            args: self
                .args
                .iter()
                .map(|arg| FnArgType {
                    ty: arg.ty.instantiate(subst),
                    inout: arg.inout,
                })
                .collect(),
            ret: self.ret.instantiate(subst),
            effects: self.effects.instantiate(&subst.1),
        }
    }

    fn inner_ty_vars(&self) -> Vec<TypeVar> {
        let mut vars = vec![];
        self.fold_in_place(&TypeKind::extend_ty_vars, &mut vars);
        vars.into_iter().unique().collect()
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
        write!(f, ") → ")?;
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

    pub fn variant(mut types: Vec<(Ustr, Self)>) -> Self {
        assert_unique_strings(&types);
        types.sort_by(|(a, _), (b, _)| a.cmp(b));
        TypeKind::Variant(types).store()
    }

    pub fn tuple(elements: Vec<Self>) -> Self {
        TypeKind::Tuple(elements).store()
    }

    pub fn record(mut fields: Vec<(Ustr, Self)>) -> Self {
        assert_unique_strings(&fields);
        fields.sort_by(|a, b| a.0.cmp(&b.0));
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
    fn instantiate(&self, subst: &InstSubstitution) -> Self {
        self.with_cycle_detection(
            |ty, _| {
                let kind = ty.data().clone();
                kind.instantiate(subst)
            },
            |ty, _| *ty,
            (),
        )
    }

    fn inner_ty_vars(&self) -> Vec<TypeVar> {
        self.with_cycle_detection(|ty, _| ty.data().inner_ty_vars(), |_, _| vec![], ())
    }

    fn fill_with_input_effect_vars(&self, vars: &mut HashSet<EffectVar>) {
        self.with_cycle_detection(
            |ty, vars| ty.data().fill_with_inner_effect_vars(vars),
            |_, _| (),
            vars,
        )
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
    pub fn set(&mut self, alias: Ustr, ty: Type) {
        self.name_to_type.insert(alias, ty);
        self.type_to_name.insert(ty, alias);
    }

    pub fn get_name(&self, ty: Type) -> Option<Ustr> {
        self.type_to_name.get(&ty).copied()
    }
    pub fn get_type(&self, name: Ustr) -> Option<Type> {
        self.name_to_type.get(&name).copied()
    }

    pub fn set_bare_native(&mut self, alias: Ustr, bare: B<dyn BareNativeType>) {
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

    /// Instantiate the type variables within this type with the given substitutions, recursively
    fn instantiate(&self, subst: &InstSubstitution) -> Type {
        use TypeKind::*;
        match self {
            Variable(var) => match subst.0.get(var) {
                Some(ty) => *ty,
                None => Type::variable(*var),
            },
            Native(native_ty) => Type::native_type(NativeType::new(
                native_ty.bare_ty.clone(),
                native_ty
                    .arguments
                    .iter()
                    .map(|ty| ty.instantiate(subst))
                    .collect(),
            )),
            Variant(types) => Type::variant(
                types
                    .iter()
                    .map(|(name, ty)| (*name, ty.instantiate(subst)))
                    .collect(),
            ),
            Tuple(tuple) => Type::tuple(tuple.iter().map(|ty| ty.instantiate(subst)).collect()),
            Record(fields) => Type::record(
                fields
                    .iter()
                    .map(|(name, ty)| (*name, ty.instantiate(subst)))
                    .collect(),
            ),
            Function(fn_type) => Type::function_type(fn_type.instantiate(subst)),
            Newtype(name, ty) => Type::new_type(*name, ty.instantiate(subst)),
            Never => Type::never(),
        }
    }

    /// Return all type variables contained in this type, recursively
    fn inner_ty_vars(&self) -> Vec<TypeVar> {
        let mut vars = vec![];
        self.fold_in_place(&Self::extend_ty_vars, &mut vars);
        vars.into_iter().unique().collect()
    }

    fn extend_ty_vars(&self, vars: &mut Vec<TypeVar>) {
        if let TypeKind::Variable(var) = self {
            vars.push(*var);
        }
    }

    /// Return true if the type variable is only found in variants
    pub fn is_ty_var_only_in_variants(&self, ty_var: TypeVar) -> bool {
        struct Visitor {
            ty_var: TypeVar,
            depth: usize,
            variant_start: Option<usize>,
            output: bool,
        }
        impl TypeKindVisitor for Visitor {
            fn visit_start(&mut self, ty: &TypeKind) {
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

            fn visit_end(&mut self, _ty: &TypeKind) {
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

    fn fill_with_inner_effect_vars(&self, vars: &mut HashSet<EffectVar>) {
        self.fold_in_place(&Self::extend_effect_vars, vars);
    }

    fn extend_effect_vars(&self, vars: &mut HashSet<EffectVar>) {
        if let TypeKind::Function(fn_type) = self {
            fn_type.effects.fill_with_inner_effect_vars(vars);
        }
    }

    /// Reduce using fold function f and initial value v, post-order traversal
    fn fold<V: Clone>(&self, f: &impl Fn(&Self, V) -> V, v: V) -> V {
        struct Visitor<'a, V: Clone, F: Fn(&TypeKind, V) -> V> {
            f: &'a F,
            v: V,
        }
        impl<V: Clone, F: Fn(&TypeKind, V) -> V> TypeKindVisitor for Visitor<'_, V, F> {
            fn visit_end(&mut self, ty: &TypeKind) {
                self.v = (self.f)(ty, self.v.clone());
            }
        }

        let mut visitor = Visitor { f, v };
        self.visit(&mut visitor);
        visitor.v
    }

    /// Reduce using fold function f and a mutable value v, post-order traversal
    fn fold_in_place<V>(&self, f: &impl Fn(&Self, &mut V), v: &mut V) {
        struct Visitor<'a, V, F: Fn(&TypeKind, &mut V)> {
            f: &'a F,
            v: &'a mut V,
        }
        impl<V, F: Fn(&TypeKind, &mut V)> TypeKindVisitor for Visitor<'_, V, F> {
            fn visit_end(&mut self, ty: &TypeKind) {
                (self.f)(ty, self.v);
            }
        }

        self.visit(&mut Visitor { f, v });
    }

    /// Visit this type, allowing for multiple travesal strategies thanks to the TypeKindVisitor trait.
    fn visit(&self, visitor: &mut impl TypeKindVisitor) {
        // helper for doing cycle detection on type
        fn process_ty(ty: Type, visitor: &mut impl TypeKindVisitor) {
            ty.with_cycle_detection(|ty, visitor| ty.data().visit(visitor), |_, _| (), visitor)
        }

        // start visit
        visitor.visit_start(self);

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
        visitor.visit_end(self);
    }

    /// Returns whether the type contains the given type variable
    pub fn contains_any_type_var(&self, var: TypeVar) -> bool {
        self.contains_any_ty_vars(&[var])
    }

    /// Returns whether the type contains any of the given type variables
    pub fn contains_any_ty_vars(&self, vars: &[TypeVar]) -> bool {
        self.fold(
            &|kind, found| {
                found
                    || if let TypeKind::Variable(v) = kind {
                        vars.contains(v)
                    } else {
                        false
                    }
            },
            false,
        )
    }

    /// Returns whether all type variables in the type are in the given list
    pub fn contains_only_ty_vars(&self, vars: &[TypeVar]) -> bool {
        self.fold(
            &|kind, all_in| {
                all_in
                    && if let TypeKind::Variable(v) = kind {
                        vars.contains(v)
                    } else {
                        true
                    }
            },
            true,
        )
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
                ty.index = *subst.get(&ty.index).unwrap();
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

/// Allow for multiple TypeKind traversal strategies
trait TypeKindVisitor {
    fn visit_start(&mut self, _ty: &TypeKind) {}
    fn visit_end(&mut self, _ty: &TypeKind) {}
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

    fn insert_type(&mut self, td: TypeKind) -> Type {
        self.insert_types(&[td])[0]
    }

    fn insert_types<const N: usize>(&mut self, tds: &[TypeKind; N]) -> [Type; N] {
        // 1. partition tds into sub-graphs of connected recursive types
        let partitioned_indices = find_disjoint_subgraphs(tds);

        // TODO: somewhere, renormalize generics to be in the same order

        // for each sub-graph
        let mut types = [Type::new_local(0); N];
        partitioned_indices
            .into_iter()
            .flat_map(|mut input_indices| {
                // 2. detect singletons and put them in the main world if they have no cycle
                if input_indices.len() == 1 {
                    let input_index = input_indices[0];
                    let td = &tds[input_index];
                    if td.inner_types().all(|ty| !ty.is_local()) {
                        let first_world = &mut self.worlds[0];
                        // is it already present?
                        let index = if let Some((index, _)) = first_world.get_full(td) {
                            index
                        } else {
                            first_world.insert_full(td.clone()).0
                        };
                        let ty = Type::new_global(0, index as u32);
                        return b(iter::once((input_index, ty))) as B<dyn Iterator<Item = _>>;
                    }
                }

                // 3. sort each sub-graph
                input_indices.sort_by(|&a, &b| {
                    // ignore local types while sorting
                    tds[a].local_cmp(&tds[b])
                    // TODO: look at permutations for the secondary sorting
                });

                // 4. renormalize local indices and store into local world
                let subst_to_local: HashMap<_, _> = input_indices
                    .iter()
                    .enumerate()
                    .map(|(local_index, &input_index)| (input_index as u32, local_index as u32))
                    .collect();
                let local_world: Vec<_> = input_indices
                    .iter()
                    .map(|&index| {
                        let mut td = tds[index].clone();
                        td.substitute_locals(&subst_to_local);
                        td
                    })
                    .collect();
                assert!(local_world.iter().all(|td| td
                    .inner_types()
                    .filter(|ty| ty.is_local())
                    .all(|ty| (ty.index as usize) < local_world.len())));

                // 5. local world is now a key
                let global_world_indices = |worlds: &Vec<TypeWorld>, world_index| {
                    let global_world: &TypeWorld = &worlds[world_index];
                    let global_world_size = global_world.len() as u32;
                    b((0..global_world_size)
                        .zip(input_indices)
                        .map(move |(index, ty_index)| {
                            (ty_index, Type::new_global(world_index as u32, index))
                        }))
                };
                if let Some(&index) = self.local_to_world.get(&local_world) {
                    return global_world_indices(&self.worlds, index);
                }
                let global_world_index = self.worlds.len() as u32;
                self.local_to_world
                    .insert(local_world.clone(), global_world_index as usize);

                // 6. renormalize local indices to global indices and store into global world
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

                // 7. collect indices
                global_world_indices(&self.worlds, global_world_index as usize)
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
pub fn store_types<const N: usize>(types_data: &[TypeKind; N]) -> [Type; N] {
    types()
        .try_write()
        .expect("Cannot get a write lock to type universes")
        .insert_types(types_data)
}

pub fn dump_type_world(index: usize, env: &ModuleEnv<'_>) {
    let world = &types().read().unwrap().worlds[index];
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
        parse_type,
        std::{new_module_with_prelude, new_std_module_env},
    };

    use super::*;
    use ustr::ustr;

    #[test]
    fn can_be_used_in_place_of() {
        // A bunch of types
        let _i32 = Type::primitive::<i32>();
        let _f32 = Type::primitive::<f32>();
        let _string = Type::primitive::<String>();
        let _gen_arg0 = Type::variable_id(0);

        // Generics
        let _gen_arg1 = Type::variable_id(1);
        #[derive(Debug, Clone)]
        struct List;
        let _gen_unbound = Type::native::<List>(vec![_gen_arg0]);
        let _gen_bound_i32 = Type::native::<List>(vec![_i32]);
        let _gen_bound_string = Type::native::<List>(vec![_string]);
        #[derive(Debug, Clone)]
        struct Map;
        let _gen_2_unbound_a_b = Type::native::<Map>(vec![_gen_arg0, _gen_arg1]);
        let _gen_2_unbound_b_a = Type::native::<Map>(vec![_gen_arg1, _gen_arg0]);
        let _gen_2_partial_bound_i32_a = Type::native::<Map>(vec![_i32, _gen_arg0]);
        let _gen_2_partial_bound_a_i32 = Type::native::<Map>(vec![_gen_arg0, _i32]);
        let _gen_2_bound_i32_i32 = Type::native::<Map>(vec![_i32, _i32]);
        let _gen_2_bound_i32_f32 = Type::native::<Map>(vec![_i32, _f32]);

        // Variants
        let _i_s = ustr("i");
        let _f_s = ustr("f");
        let _s_s = ustr("s");
        let _variant_i32_f32 = Type::variant(vec![(_i_s, _i32), (_f_s, _f32)]);
        let _variant_f32_i32 = Type::variant(vec![(_f_s, _f32), (_i_s, _i32)]);
        let _variant_i32_f32_string =
            Type::variant(vec![(_i_s, _i32), (_f_s, _f32), (_s_s, _string)]);
        let _union_string_i32_f32 =
            Type::variant(vec![(_s_s, _string), (_i_s, _i32), (_f_s, _f32)]);

        // Recursive variants
        let empty_tuple = Type::tuple(vec![]);
        let adt_gen_list_element_td = TypeKind::Tuple(vec![_gen_arg0, Type::new_local(1)]);
        let adt_list_td = TypeKind::Variant(vec![
            (ustr("Nil"), empty_tuple),
            (ustr("Cons"), Type::new_local(0)),
        ]);
        let [_adt_gen_list_element, _adt_gen_list] =
            store_types(&[adt_gen_list_element_td, adt_list_td.clone()]);
        // FIXME: support recursive types
        // TODO: read Subtyping Recursive Types, Luca Cardelli, 1993
        // let adt_int_list_element_td = TypeData::Tuple(vec![_i32, Type::new_local(1)]);
        // let [adt_int_list_element, adt_int_list] = store_types(&[adt_int_list_element_td, adt_list_td]);

        // Tuples
        let _tuple_i32 = Type::tuple(vec![_i32]);
        let _tuple_f32 = Type::tuple(vec![_f32]);
        let _tuple_i32_i32 = Type::tuple(vec![_i32, _i32]);
        let _tuple_i32_f32 = Type::tuple(vec![_i32, _f32]);
        let _tuple_f32_i32 = Type::tuple(vec![_f32, _i32]);
        let _tuple_gen0_gen1 = Type::tuple(vec![_gen_arg0, _gen_arg1]);
        let _tuple_i32_tuple_f32_i32 = Type::tuple(vec![_i32, _tuple_f32_i32]);
        let _gen_arg2 = Type::variable_id(2);
        let _tuple_i32_tuple_f32_gen2 = Type::tuple(vec![_i32, Type::tuple(vec![_f32, _gen_arg2])]);

        // Record
        let x = ustr("x");
        let y = ustr("y");
        let z = ustr("z");
        let _record_vec2_i32 = Type::record(vec![(x, _i32), (y, _i32)]);
        let _record_vec2_f32 = Type::record(vec![(x, _f32), (y, _f32)]);
        let _record_vec3_f32 = Type::record(vec![(x, _f32), (y, _f32), (z, _f32)]);
        let _record_vec3_f32_shuffled = Type::record(vec![(z, _f32), (x, _f32), (y, _f32)]);
        let _record_vec2_gen = Type::record(vec![(x, _gen_arg0), (y, _gen_arg0)]);
        let _record_het = Type::record(vec![(x, _i32), (y, _f32)]);

        // Native functions
        // unary functions
        let _native_fn_i32_i32 = Type::unary_function_by_val(_i32, _i32);
        let _native_fn_i32_f32 = Type::unary_function_by_val(_i32, _f32);
        let _native_fn_f32_i32 = Type::unary_function_by_val(_f32, _i32);
        let _native_fn_f32_f32 = Type::unary_function_by_val(_f32, _f32);
        let _native_fn_any_i32 = Type::unary_function_by_val(_gen_arg0, _i32);
        let _native_fn_i32_any = Type::unary_function_by_val(_i32, _gen_arg0);

        // binary functions
        // TODO: add more tests

        // new types
        let _int = Type::new_type(ustr("Int"), _i32);
        let _other_int = Type::new_type(ustr("OtherInt"), _i32);
    }

    #[test]
    fn parse_and_format() {
        let std_env = new_std_module_env();
        let current_module = new_module_with_prelude();
        let mod_env = ModuleEnv::new(&current_module, &std_env);
        let check = |name: &str| {
            let ty = parse_type(name).unwrap();
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
}
