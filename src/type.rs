use std::any::type_name;
use std::any::TypeId;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::{self, Debug};
use std::hash::Hash;
use std::iter;
use std::sync::OnceLock;
use std::sync::RwLock;

use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use indexmap::IndexSet;
use nonmax::NonMaxU32;
use ustr::Ustr;

use crate::assert::assert_unique_strings;
use crate::containers::compare_by;
use crate::containers::B;
use crate::graph;
use crate::graph::find_disjoint_subgraphs;
use crate::sync::SyncPhantomData;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct TypeVar(pub(crate) u32);

pub trait BareNativeType: DynClone + DynEq + Send + Sync {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
    fn type_name(&self) -> &'static str {
        type_name::<Self>()
    }
}

pub fn bare_native_type<T: 'static>() -> B<dyn BareNativeType> {
    B::new(BareNativeTypeImpl::<T>::new())
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

/// For a native value, return its type
pub trait TypeOfNativeValue {
    fn type_of_value(&self) -> NativeType;
}

#[macro_export]
macro_rules! impl_bare_native_type {
    ($t:ty) => {
        impl $crate::r#type::TypeOfNativeValue for $t {
            fn type_of_value(&self) -> $crate::r#type::NativeType {
                $crate::r#type::NativeType::new_primitive::<Self>()
            }
        }
    };
}

/// A generic type implemented in Rust.
/// If arguments is empty, we call it a primitive type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NativeType {
    bare_ty: B<dyn BareNativeType>,
    arguments: Vec<Type>,
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

fn count_generics_rec(args: &[Type], counts: &mut TypeGenericCountMap) -> u32 {
    args.iter()
        .map(|ty| ty.count_generics_rec(counts))
        .max()
        .unwrap_or(0)
}

fn count_arg_generics_rec(args: &[FnArgType], counts: &mut TypeGenericCountMap) -> u32 {
    args.iter()
        .map(|arg| arg.ty.count_generics_rec(counts))
        .max()
        .unwrap_or(0)
}

fn format_generics(count: u32) -> String {
    if count > 0 {
        let generics = (0..count)
            .map(generic_index_to_char)
            .map(String::from)
            .collect::<Vec<_>>();
        format!("<{}>", generics.join(", "))
    } else {
        String::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FnArgType {
    pub ty: Type,
    pub inout: bool,
}
impl FnArgType {
    fn new(ty: Type, inout: bool) -> Self {
        Self { ty, inout }
    }
    fn local_cmp(&self, other: &Self) -> Ordering {
        self.ty
            .local_cmp(&other.ty)
            .then(self.inout.cmp(&other.inout))
    }
    fn can_be_used_in_place_of_with_subst(
        self,
        other: Self,
        substitutions: &mut Substitutions,
        seen: &mut HashSet<(Type, Type)>,
    ) -> bool {
        self.ty
            .can_be_used_in_place_of_with_subst(other.ty, substitutions, seen)
            && (self.inout || !other.inout)
    }
}
impl fmt::Display for FnArgType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.inout {
            write!(f, "inout ")
        } else {
            Ok(())
        }?;
        write!(f, "{}", self.ty)
    }
}

/// The type of a function
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnType {
    pub args: Vec<FnArgType>,
    pub ret: Type,
}

impl FnType {
    pub fn new(args: &[(Type, bool)], ret: Type) -> Self {
        Self {
            args: args
                .iter()
                .map(|(ty, inout)| FnArgType::new(*ty, *inout))
                .collect(),
            ret,
        }
    }
    pub fn new_by_val(args: &[Type], ret: Type) -> Self {
        Self {
            args: args
                .iter()
                .map(|&ty| FnArgType { ty, inout: false })
                .collect(),
            ret,
        }
    }
    fn local_cmp(&self, other: &Self) -> Ordering {
        compare_by(&self.args, &other.args, FnArgType::local_cmp)
            .then(self.ret.local_cmp(&other.ret))
    }
}

type TypeGenericCountMap = HashMap<Type, u32>;

/// A type identifier, unique for a given type of a given mathematical structure
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Type {
    world: Option<NonMaxU32>, // If None, current local world
    index: u32,
}

impl Type {
    // helper constructors
    pub fn unit() -> Self {
        Type::tuple(vec![])
    }

    pub fn primitive<T: Clone + 'static>() -> Self {
        Self::native::<T>(vec![])
    }

    pub fn native<T: Clone + 'static>(arguments: Vec<Type>) -> Self {
        let bare_ty = bare_native_type::<T>();
        TypeKind::Native(B::new(NativeType { arguments, bare_ty })).store()
    }

    pub fn native_type(native_type: NativeType) -> Self {
        TypeKind::Native(B::new(native_type)).store()
    }

    pub fn variable_id(id: u32) -> Self {
        Self::variable(TypeVar(id))
    }

    pub fn variable(var: TypeVar) -> Self {
        TypeKind::Variable(var).store()
    }

    pub fn variant(mut types: Vec<(Ustr, Self)>) -> Self {
        types.sort_by(|(a, _), (b, _)| a.cmp(b));
        TypeKind::Variant(types).store()
    }

    pub fn tuple(elements: Vec<Self>) -> Self {
        TypeKind::Tuple(elements).store()
    }

    pub fn record(mut fields: Vec<(Ustr, Self)>) -> Self {
        assert_unique_strings(&fields);
        fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        TypeKind::Record(fields).store()
    }

    pub fn function_type(ty: FnType) -> Self {
        TypeKind::Function(B::new(ty)).store()
    }

    pub fn function(args: &[Self], ret: Self) -> Self {
        Self::function_type(FnType::new_by_val(args, ret))
    }

    pub fn nullary_function(ret: Self) -> Self {
        Self::function(&[], ret)
    }

    pub fn unary_function(arg: Self, ret: Self) -> Self {
        Self::function(&[arg], ret)
    }

    pub fn binary_function(arg1: Self, arg2: Self, ret: Self) -> Self {
        Self::function(&[arg1, arg2], ret)
    }

    pub fn new_type(name: Ustr, ty: Self) -> Self {
        TypeKind::Newtype(name, ty).store()
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

    // subtyping
    pub fn can_be_used_in_place_of_with_subst(
        self,
        other: Self,
        substitutions: &mut Substitutions,
        seen: &mut HashSet<(Type, Type)>,
    ) -> bool {
        // If the types are the same, they can be used in place of each other
        if self == other {
            return true;
        }
        // If we are recursing, prevent subtyping cycles
        // TODO: do smarter matching to support recursive types
        if seen.contains(&(self, other)) {
            return false;
        }
        // A generic ref can be replaced by anything, but keep in mind the substitutions
        if let TypeKind::Variable(that_index) = *other.data() {
            match substitutions.get(&that_index) {
                Some(subst) => {
                    seen.insert((self, other));
                    return self.can_be_used_in_place_of_with_subst(*subst, substitutions, seen);
                }
                None => {
                    // do not perform substitution if we already have the correct index
                    if let TypeKind::Variable(this_index) = *self.data() {
                        if this_index == that_index {
                            return true;
                        }
                    }
                    substitutions.insert(that_index, self);
                    return true;
                }
            }
        }
        // Otherwise, we need to do a structural comparison
        seen.insert((self, other));
        self.data()
            .can_be_used_in_place_of_with_subst(other, substitutions, seen)
    }

    pub fn can_be_used_in_place_of(self, that: Self) -> bool {
        self.can_be_used_in_place_of_with_subst(that, &mut HashMap::new(), &mut HashSet::new())
    }

    // generic counting
    fn count_generics_rec(self, counts: &mut TypeGenericCountMap) -> u32 {
        if counts.get(&self).is_none() {
            counts.insert(self, 0);
            let count = self.data().count_generics_rec(counts);
            counts.insert(self, count);
        }
        0
    }

    fn count_generics(self) -> u32 {
        let mut counts = HashMap::new();
        let local_count = self.count_generics_rec(&mut counts);
        local_count + counts.values().sum::<u32>()
    }

    pub fn format_generics(self) -> String {
        format_generics(self.count_generics())
    }

    // other
    fn local_cmp(&self, other: &Self) -> Ordering {
        if (self.world, other.world) == (None, None) {
            Ordering::Equal
        } else {
            self.cmp(other)
        }
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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Check for cycle and insert the type into the HashSet
        let cycle_detected = TYPE_DISPLAY_VISITED.with(|visited| {
            let mut visited = visited.borrow_mut();
            if visited.contains(self) {
                true // Cycle detected
            } else {
                visited.insert(*self);
                false
            }
        });

        // Print self type if cycle detected
        if cycle_detected {
            return write!(f, "Self");
        }

        // Recurse
        let result = write!(f, "{}", *self.data());

        // Remove the value on back-tracking
        TYPE_DISPLAY_VISITED.with(|visited| {
            visited.borrow_mut().remove(self);
        });

        result
    }
}

type Substitutions = HashMap<TypeVar, Type>;

/// Named types
#[derive(Debug, Clone, Default)]
pub struct TypeAliases {
    name_to_type: HashMap<Ustr, Type>,
    type_to_name: HashMap<Type, Ustr>,
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

    pub fn iter(&self) -> impl Iterator<Item = (&Ustr, &Type)> {
        self.name_to_type.iter()
    }

    pub fn extend(&mut self, other: Self) {
        self.name_to_type.extend(other.name_to_type);
        self.type_to_name.extend(other.type_to_name);
    }
    pub fn is_empty(&self) -> bool {
        self.name_to_type.is_empty() && self.type_to_name.is_empty()
    }
}

thread_local! {
    static TYPE_DISPLAY_VISITED: RefCell<HashSet<Type>> = RefCell::new(HashSet::new());
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
}
// TODO: traits as bounds of generics

impl TypeKind {
    /// Store in the type system and return a type identifier
    pub fn store(self) -> Type {
        store_type(self)
    }

    /// Somewhat a sub-type, but named differently to accommodate generics
    fn can_be_used_in_place_of_with_subst(
        &self,
        other: Type,
        substitutions: &mut Substitutions,
        seen: &mut HashSet<(Type, Type)>,
    ) -> bool {
        // We know that that is not a GenericArg
        match self {
            // A generic type can be used in place of itself with compatible type arguments, or instantiate a generics
            TypeKind::Native(this_gen) => match &*other.data() {
                TypeKind::Native(that_gen) => {
                    this_gen.bare_ty == that_gen.bare_ty
                        && this_gen.arguments.len() == that_gen.arguments.len()
                        && this_gen // covariant argument types
                            .arguments
                            .iter()
                            .zip(that_gen.arguments.iter())
                            .all(|(this_ty, that_ty)| {
                                this_ty.can_be_used_in_place_of_with_subst(
                                    *that_ty,
                                    substitutions,
                                    seen,
                                )
                            })
                }
                _ => false,
            },
            // We trait generics as invariant
            TypeKind::Variable(_) => false,
            // This variant can be used in place of that variant if for every constructor and argument in that variant,
            // there is a constructor and argument in this union that can be used in place of it.
            TypeKind::Variant(this_variant) => match &*other.data() {
                TypeKind::Variant(that_variant) => that_variant.iter().all(|that_ctor| {
                    this_variant.iter().any(|this_ctor| {
                        this_ctor.0 == that_ctor.0
                            && this_ctor.1.can_be_used_in_place_of_with_subst(
                                that_ctor.1,
                                substitutions,
                                seen,
                            )
                    })
                }),
                _ => false,
            },
            // Larger tuples can be used in place of smaller tuples
            TypeKind::Tuple(this_tuple) => match &*other.data() {
                TypeKind::Tuple(that_tuple) => {
                    this_tuple.len() >= that_tuple.len()
                        && this_tuple // covariant element types
                            .iter()
                            .zip(that_tuple.iter())
                            .all(|(this_ty, that_ty)| {
                                this_ty.can_be_used_in_place_of_with_subst(
                                    *that_ty,
                                    substitutions,
                                    seen,
                                )
                            })
                }
                _ => false,
            },
            // This record can be used in place of that record if for every field in that record,
            // there is a field in this record that can be used in place of it.
            // FIXME: this currently will generate wrong code because of the order of fields
            TypeKind::Record(this_record) => match &*other.data() {
                TypeKind::Record(that_record) => that_record.iter().all(|(that_name, that_ty)| {
                    this_record.iter().any(|(this_name, this_ty)| {
                        this_name == that_name
                            && this_ty.can_be_used_in_place_of_with_subst(
                                *that_ty,
                                substitutions,
                                seen,
                            )
                    })
                }),
                _ => false,
            },
            // A function can be used in place of another function if the argument types are contravariant and return type covariant.
            TypeKind::Function(this_fn) => {
                let this_args = &this_fn.args;
                let this_ty = &this_fn.ret;
                match &*other.data() {
                    TypeKind::Function(that_fun) => {
                        let that_args = &that_fun.args;
                        let that_ty = &that_fun.ret;
                        this_args.len() == that_args.len()
                            && this_args // contravariant argument types
                                .iter()
                                .zip(that_args.iter())
                                .all(|(this_ty, that_ty)| {
                                    that_ty.can_be_used_in_place_of_with_subst(
                                        *this_ty,
                                        substitutions,
                                        seen,
                                    )
                                })
                            && this_ty.can_be_used_in_place_of_with_subst(
                                *that_ty,
                                substitutions,
                                seen,
                            )
                        // covariant return type
                    }
                    _ => false,
                }
            }
            // A new type can be used in place of the type it wraps
            TypeKind::Newtype(_, this_ty) => {
                this_ty.can_be_used_in_place_of_with_subst(other, substitutions, seen)
            }
        }
    }

    pub fn can_be_used_in_place_of(&self, that: Type) -> bool {
        self.can_be_used_in_place_of_with_subst(that, &mut HashMap::new(), &mut HashSet::new())
    }

    pub fn inner_types(&self) -> B<dyn Iterator<Item = Type> + '_> {
        match self {
            TypeKind::Native(g) => B::new(g.arguments.iter().copied()),
            TypeKind::Variable(_) => B::new(iter::empty()),
            TypeKind::Variant(types) => B::new(types.iter().map(|(_, ty)| *ty)),
            TypeKind::Tuple(types) => B::new(types.iter().copied()),
            TypeKind::Record(fields) => B::new(fields.iter().map(|(_, ty)| *ty)),
            TypeKind::Function(function) => B::new(
                function
                    .args
                    .iter()
                    .map(|arg| arg.ty)
                    .chain(iter::once(function.ret)),
            ),
            TypeKind::Newtype(_, ty) => B::new(iter::once(*ty)),
        }
    }

    pub fn inner_types_mut(&mut self) -> B<dyn Iterator<Item = &mut Type> + '_> {
        match self {
            TypeKind::Native(g) => B::new(g.arguments.iter_mut()),
            TypeKind::Variable(_) => B::new(iter::empty()),
            TypeKind::Variant(types) => B::new(types.iter_mut().map(|(_, ty)| ty)),
            TypeKind::Tuple(types) => B::new(types.iter_mut()),
            TypeKind::Record(fields) => B::new(fields.iter_mut().map(|(_, ty)| ty)),
            TypeKind::Function(function) => B::new(
                function
                    .args
                    .iter_mut()
                    .map(|arg| &mut arg.ty)
                    .chain(iter::once(&mut function.ret)),
            ),
            TypeKind::Newtype(_, ty) => B::new(iter::once(ty)),
        }
    }

    fn local_cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            // Compare the raw pointers (addresses) of the weak references
            (TypeKind::Native(a), TypeKind::Native(b)) => a.local_cmp(b),
            (TypeKind::Variable(a), TypeKind::Variable(b)) => a.cmp(b),
            (TypeKind::Variant(a), TypeKind::Variant(b)) => {
                compare_by(a, b, |(a_s, a_t), (b_s, b_t)| {
                    a_s.cmp(b_s).then(a_t.local_cmp(b_t))
                })
            }
            (TypeKind::Tuple(a), TypeKind::Tuple(b)) => compare_by(a, b, Type::local_cmp),
            (TypeKind::Record(a), TypeKind::Record(b)) => {
                compare_by(a, b, |(a_s, a_t), (b_s, b_t)| {
                    a_s.cmp(b_s).then(a_t.local_cmp(b_t))
                })
            }
            (TypeKind::Function(a), TypeKind::Function(b)) => a.local_cmp(b),
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
        match self {
            TypeKind::Native(_) => 1,
            TypeKind::Variable(_) => 2,
            TypeKind::Variant(_) => 3,
            TypeKind::Tuple(_) => 4,
            TypeKind::Record(_) => 5,
            TypeKind::Function(_) => 6,
            TypeKind::Newtype(_, _) => 7,
        }
    }

    fn count_generics_rec(&self, counts: &mut TypeGenericCountMap) -> u32 {
        match self {
            TypeKind::Native(g) => count_generics_rec(&g.arguments, counts),
            TypeKind::Variable(id) => id.0 + 1, // the max number is this index + 1
            TypeKind::Variant(types) => types
                .iter()
                .map(|(_, ty)| ty.count_generics_rec(counts))
                .max()
                .unwrap_or(0),
            TypeKind::Tuple(types) => types
                .iter()
                .map(|ty| ty.count_generics_rec(counts))
                .max()
                .unwrap_or(0),
            TypeKind::Record(fields) => fields
                .iter()
                .map(|(_, ty)| ty.count_generics_rec(counts))
                .max()
                .unwrap_or(0),
            TypeKind::Function(function) => count_arg_generics_rec(&function.args, counts)
                .max(function.ret.count_generics_rec(counts)),
            TypeKind::Newtype(_, ty) => ty.count_generics_rec(counts),
        }
    }

    // fn count_generics_with_counts(&self, counts: &mut NamedTypeGenericCountMap) -> usize {
    //     let local_count = self.count_generics_rec(counts);
    //     local_count + counts.values().sum::<usize>()
    // }

    // pub fn format_generics_with_counts(&self, counts: &mut NamedTypeGenericCountMap) -> String {
    //     format_generics(self.count_generics_with_counts(counts))
    // }
}

impl fmt::Display for TypeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypeKind::Native(g) => {
                let tn = g.bare_ty.as_ref().type_name();
                write!(
                    f,
                    "{}",
                    tn.rsplit_once("::").unwrap_or(("", tn)).1, // FIXME: this formatting is broken for Rust generics
                )?;
                if !g.arguments.is_empty() {
                    write!(f, "<")?;
                    write_with_separator(&g.arguments, ", ", f)?;
                    write!(f, ">")?;
                }
                Ok(())
            }
            TypeKind::Variable(id) => write!(f, "{}", generic_index_to_char(id.0)),
            TypeKind::Variant(types) => {
                for (i, (name, ty)) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{name} of {ty}")?;
                }
                Ok(())
            }
            TypeKind::Tuple(members) => {
                write!(f, "(")?;
                write_with_separator(members, ", ", f)?;
                write!(f, ")")
            }
            TypeKind::Record(fields) => {
                write!(f, "{{ ")?;
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: {ty}")?;
                }
                write!(f, " }}")
            }
            TypeKind::Function(function) => {
                write!(
                    f,
                    "({}) -> {}",
                    function
                        .args
                        .iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    function.ret
                )
            }
            TypeKind::Newtype(name, ty) => write!(f, "{name}({ty})"),
        }
    }
}

impl Ord for TypeKind {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            // Compare the raw pointers (addresses) of the weak references
            (TypeKind::Native(a), TypeKind::Native(b)) => a.cmp(b),
            (TypeKind::Variable(a), TypeKind::Variable(b)) => a.cmp(b),
            (TypeKind::Variant(a), TypeKind::Variant(b)) => a.cmp(b),
            (TypeKind::Tuple(a), TypeKind::Tuple(b)) => a.cmp(b),
            (TypeKind::Record(a), TypeKind::Record(b)) => a.cmp(b),
            (TypeKind::Function(a), TypeKind::Function(b)) => {
                a.args.cmp(&b.args).then_with(|| a.ret.cmp(&b.ret))
            }
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

fn generic_index_to_char(index: u32) -> char {
    // char::from_digit(index as u32 + 10, 36).unwrap_or('_')
    char::from_u32(index as u32 + 0x3B1).unwrap_or('_')
}

pub(crate) fn write_with_separator<T: fmt::Display>(
    vec: &[T],
    separator: &str,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    for e in vec.iter().take(1) {
        write!(f, "{e}")?;
    }
    for e in vec.iter().skip(1) {
        write!(f, "{separator}{e}")?;
    }
    Ok(())
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
                        return B::new(iter::once((input_index, ty))) as B<dyn Iterator<Item = _>>;
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
                    B::new((0..global_world_size).zip(input_indices).map(
                        move |(index, ty_index)| {
                            (ty_index, Type::new_global(world_index as u32, index))
                        },
                    ))
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
        self.worlds[r.world.unwrap().get() as usize]
            .get_index(r.index as usize)
            .unwrap()
    }
}

fn types() -> &'static RwLock<TypeUniverse> {
    static TYPES: OnceLock<RwLock<TypeUniverse>> = OnceLock::new();
    TYPES.get_or_init(|| RwLock::new(TypeUniverse::new()))
}

/// Store a type in the type system and return a type identifier
pub fn store_type(type_data: TypeKind) -> Type {
    types().write().unwrap().insert_type(type_data)
}

/// Store a list of types in the type system and return a list of type identifiers
pub fn store_types<const N: usize>(types_data: &[TypeKind; N]) -> [Type; N] {
    types().write().unwrap().insert_types(types_data)
}

pub fn dump_type_world(index: usize) {
    let world = &types().read().unwrap().worlds[index];
    for (i, ty) in world.iter().enumerate() {
        println!("{}: {}", i, ty);
    }
}

pub struct TypeDataRef<'a> {
    ty: Type,
    guard: std::sync::RwLockReadGuard<'a, TypeUniverse>,
}
impl<'a> std::ops::Deref for TypeDataRef<'a> {
    type Target = TypeKind;
    fn deref(&self) -> &Self::Target {
        self.guard.get_type_data(self.ty)
    }
}

pub struct TypeNames {
    pub names_to_types: HashMap<Ustr, Type>,
    pub types_to_names: HashMap<Type, Ustr>,
}

// Note: if we need to solve type inference, see https://github.com/andrejbauer/plzoo/blob/master/src/poly/type_infer.ml
// Question: how to lookup local and parent variables in case of recursion with static typing? (static lexical scoping, see de Bruijn indices)
// See if needed: Explicit substitutions, M. Abadi, L. Cardelli, P.L. Curien, J.J. Lévy, Journal of Functional Programming 6(2), 1996.

#[cfg(test)]
mod tests {
    use super::*;
    use ustr::ustr;

    #[test]
    fn can_be_used_in_place_of() {
        // A bunch of types
        let _i32 = Type::primitive::<i32>();
        let _f32 = Type::primitive::<f32>();
        let _string = Type::primitive::<String>();
        let _gen_arg0 = Type::variable_id(0);

        // Primitive types
        assert!(_i32.can_be_used_in_place_of(_i32));
        assert!(_i32.can_be_used_in_place_of(_gen_arg0));
        assert!(!_i32.can_be_used_in_place_of(_f32));
        assert!(!_i32.can_be_used_in_place_of(_string));

        // Generics
        assert!(_gen_arg0.can_be_used_in_place_of(_gen_arg0));
        let _gen_arg1 = Type::variable_id(1);
        assert!(_gen_arg0.can_be_used_in_place_of(_gen_arg1));
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
        assert!(_gen_unbound.can_be_used_in_place_of(_gen_unbound));
        assert!(_gen_bound_i32.can_be_used_in_place_of(_gen_unbound));
        assert!(_gen_bound_string.can_be_used_in_place_of(_gen_unbound));
        assert!(_gen_2_unbound_a_b.can_be_used_in_place_of(_gen_2_unbound_a_b));
        assert!(_gen_2_unbound_b_a.can_be_used_in_place_of(_gen_2_unbound_b_a));
        assert!(_gen_2_unbound_a_b.can_be_used_in_place_of(_gen_2_unbound_b_a));
        assert!(_gen_2_unbound_b_a.can_be_used_in_place_of(_gen_2_unbound_a_b));
        assert!(_gen_2_partial_bound_i32_a.can_be_used_in_place_of(_gen_2_partial_bound_i32_a));
        assert!(_gen_2_partial_bound_a_i32.can_be_used_in_place_of(_gen_2_partial_bound_a_i32));
        assert!(!_gen_2_partial_bound_i32_a.can_be_used_in_place_of(_gen_2_partial_bound_a_i32));
        assert!(_gen_2_partial_bound_i32_a.can_be_used_in_place_of(_gen_2_unbound_a_b));
        assert!(_gen_2_partial_bound_i32_a.can_be_used_in_place_of(_gen_2_unbound_b_a));
        assert!(_gen_2_partial_bound_a_i32.can_be_used_in_place_of(_gen_2_unbound_a_b));
        assert!(_gen_2_partial_bound_a_i32.can_be_used_in_place_of(_gen_2_unbound_b_a));
        assert!(_gen_2_bound_i32_i32.can_be_used_in_place_of(_gen_2_unbound_a_b));
        assert!(_gen_2_bound_i32_i32.can_be_used_in_place_of(_gen_2_unbound_b_a));
        assert!(_gen_2_bound_i32_i32.can_be_used_in_place_of(_gen_2_partial_bound_i32_a));
        assert!(_gen_2_bound_i32_i32.can_be_used_in_place_of(_gen_2_partial_bound_a_i32));
        assert!(_gen_2_bound_i32_i32.can_be_used_in_place_of(_gen_2_bound_i32_i32));
        assert!(!_gen_2_bound_i32_i32.can_be_used_in_place_of(_gen_2_bound_i32_f32));
        assert!(_gen_2_bound_i32_f32.can_be_used_in_place_of(_gen_2_unbound_a_b));
        assert!(_gen_2_bound_i32_f32.can_be_used_in_place_of(_gen_2_unbound_b_a));
        assert!(_gen_2_bound_i32_f32.can_be_used_in_place_of(_gen_2_partial_bound_i32_a));
        assert!(!_gen_2_bound_i32_f32.can_be_used_in_place_of(_gen_2_partial_bound_a_i32));
        assert!(!_gen_2_bound_i32_f32.can_be_used_in_place_of(_gen_2_bound_i32_i32));
        assert!(_gen_2_bound_i32_f32.can_be_used_in_place_of(_gen_2_bound_i32_f32));

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
        assert!(_variant_i32_f32.can_be_used_in_place_of(_variant_i32_f32));
        assert!(_variant_f32_i32.can_be_used_in_place_of(_variant_f32_i32));
        assert!(_variant_i32_f32.can_be_used_in_place_of(_variant_f32_i32));
        assert!(_variant_f32_i32.can_be_used_in_place_of(_variant_i32_f32));
        assert!(_variant_i32_f32_string.can_be_used_in_place_of(_variant_i32_f32));
        assert!(_variant_i32_f32_string.can_be_used_in_place_of(_variant_f32_i32));
        assert!(_union_string_i32_f32.can_be_used_in_place_of(_variant_i32_f32));
        assert!(_union_string_i32_f32.can_be_used_in_place_of(_variant_f32_i32));

        // Recursive variants
        let empty_tuple = Type::tuple(vec![]);
        let adt_gen_list_element_td = TypeKind::Tuple(vec![_gen_arg0, Type::new_local(1)]);
        let adt_list_td = TypeKind::Variant(vec![
            (ustr("Nil"), empty_tuple),
            (ustr("Cons"), Type::new_local(0)),
        ]);
        let [adt_gen_list_element, adt_gen_list] =
            store_types(&[adt_gen_list_element_td, adt_list_td.clone()]);
        assert!(adt_gen_list.can_be_used_in_place_of(adt_gen_list));
        assert!(adt_gen_list_element.can_be_used_in_place_of(adt_gen_list_element));
        assert!(!adt_gen_list.can_be_used_in_place_of(adt_gen_list_element));
        assert!(!adt_gen_list_element.can_be_used_in_place_of(adt_gen_list));
        assert!(adt_gen_list.can_be_used_in_place_of(_gen_arg1));
        // FIXME: support recursive types
        // TODO: read Subtyping Recursive Types, Luca Cardelli, 1993
        // let adt_int_list_element_td = TypeData::Tuple(vec![_i32, Type::new_local(1)]);
        // let [adt_int_list_element, adt_int_list] = store_types(&[adt_int_list_element_td, adt_list_td]);
        // assert!(adt_int_list.can_be_used_in_place_of(adt_gen_list));
        // assert!(adt_int_list_element.can_be_used_in_place_of(adt_gen_list_element));

        // Tuples
        let _tuple_i32 = Type::tuple(vec![_i32]);
        let _tuple_f32 = Type::tuple(vec![_f32]);
        let _tuple_i32_i32 = Type::tuple(vec![_i32, _i32]);
        let _tuple_i32_f32 = Type::tuple(vec![_i32, _f32]);
        let _tuple_f32_i32 = Type::tuple(vec![_f32, _i32]);
        assert!(_tuple_i32.can_be_used_in_place_of(_tuple_i32));
        assert!(!_tuple_i32.can_be_used_in_place_of(_tuple_f32));
        assert!(_tuple_i32_i32.can_be_used_in_place_of(_tuple_i32));
        assert!(_tuple_i32_f32.can_be_used_in_place_of(_tuple_i32));
        assert!(!_tuple_f32_i32.can_be_used_in_place_of(_tuple_i32));
        let _tuple_gen0_gen1 = Type::tuple(vec![_gen_arg0, _gen_arg1]);
        assert!(_tuple_i32_i32.can_be_used_in_place_of(_tuple_gen0_gen1));
        let _tuple_i32_tuple_f32_i32 = Type::tuple(vec![_i32, _tuple_f32_i32]);
        assert!(_tuple_i32_tuple_f32_i32.can_be_used_in_place_of(_tuple_gen0_gen1));
        let _gen_arg2 = Type::variable_id(2);
        let _tuple_i32_tuple_f32_gen2 = Type::tuple(vec![_i32, Type::tuple(vec![_f32, _gen_arg2])]);
        assert!(_tuple_i32_tuple_f32_i32.can_be_used_in_place_of(_tuple_i32_tuple_f32_gen2));

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
        assert!(_record_vec2_i32.can_be_used_in_place_of(_record_vec2_i32));
        assert!(_record_vec2_f32.can_be_used_in_place_of(_record_vec2_f32));
        assert!(!_record_vec2_i32.can_be_used_in_place_of(_record_vec2_f32));
        assert!(_record_vec3_f32.can_be_used_in_place_of(_record_vec2_f32));
        assert!(!_record_vec2_f32.can_be_used_in_place_of(_record_vec3_f32));
        assert!(_record_vec3_f32_shuffled.can_be_used_in_place_of(_record_vec3_f32));
        assert!(_record_vec3_f32.can_be_used_in_place_of(_record_vec3_f32_shuffled));
        assert!(_record_vec3_f32_shuffled.can_be_used_in_place_of(_record_vec2_f32));
        assert!(_record_vec2_i32.can_be_used_in_place_of(_record_vec2_gen));
        assert!(!_record_vec2_gen.can_be_used_in_place_of(_record_vec2_i32));
        assert!(_record_het.can_be_used_in_place_of(_record_het));
        assert!(!_record_vec2_i32.can_be_used_in_place_of(_record_het));
        assert!(!_record_het.can_be_used_in_place_of(_record_vec2_i32));
        assert!(!_record_het.can_be_used_in_place_of(_record_vec2_gen));

        // Native functions
        // unary functions
        let _native_fn_i32_i32 = Type::unary_function(_i32, _i32);
        let _native_fn_i32_f32 = Type::unary_function(_i32, _f32);
        let _native_fn_f32_i32 = Type::unary_function(_f32, _i32);
        let _native_fn_f32_f32 = Type::unary_function(_f32, _f32);
        let _native_fn_any_i32 = Type::unary_function(_gen_arg0, _i32);
        let _native_fn_i32_any = Type::unary_function(_i32, _gen_arg0);
        assert!(_native_fn_i32_i32.can_be_used_in_place_of(_native_fn_i32_i32));
        assert!(_native_fn_i32_f32.can_be_used_in_place_of(_native_fn_i32_f32));
        assert!(!_native_fn_i32_i32.can_be_used_in_place_of(_native_fn_i32_f32));
        assert!(_native_fn_any_i32.can_be_used_in_place_of(_native_fn_i32_i32));
        assert!(_native_fn_any_i32.can_be_used_in_place_of(_native_fn_f32_i32));
        assert!(!_native_fn_any_i32.can_be_used_in_place_of(_native_fn_i32_f32));
        assert!(!_native_fn_any_i32.can_be_used_in_place_of(_native_fn_f32_f32));
        assert!(!_native_fn_i32_any.can_be_used_in_place_of(_native_fn_i32_i32));
        assert!(_native_fn_i32_i32.can_be_used_in_place_of(_native_fn_i32_any));

        // binary functions
        // TODO: add more tests

        // new types
        let _int = Type::new_type(ustr("Int"), _i32);
        assert!(_int.can_be_used_in_place_of(_int));
        assert!(_int.can_be_used_in_place_of(_gen_arg0));
        assert!(_int.can_be_used_in_place_of(_i32));
        let _other_int = Type::new_type(ustr("OtherInt"), _i32);
        assert!(_other_int.can_be_used_in_place_of(_other_int));
        assert!(_other_int.can_be_used_in_place_of(_gen_arg0));
        assert!(_other_int.can_be_used_in_place_of(_i32));
        assert!(!_other_int.can_be_used_in_place_of(_int));
    }
}
