use std::any::type_name;
use std::any::TypeId;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{self, Debug};
use std::hash::Hash;
use std::sync::OnceLock;
use std::sync::RwLock;
use std::cell::RefCell;
use std::collections::HashSet;

use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use indexmap::IndexSet;
use nonmax::NonMaxU32;
use ustr::Ustr;

use crate::assert::assert_unique_strings;
use crate::containers::First;
use crate::containers::SmallVec1;

pub trait NativeType: DynClone + DynEq + Send + Sync {
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
}

pub fn native_type<T: 'static>() -> Box<dyn NativeType> {
    Box::new(NativeTypeImpl::<T>::new())
}

dyn_clone::clone_trait_object!(NativeType);
dyn_eq::eq_trait_object!(NativeType);

impl Ord for dyn NativeType {
    fn cmp(&self, other: &Self) -> Ordering {
        NativeType::type_id(self).cmp(&NativeType::type_id(other))
    }
}

impl PartialOrd for dyn NativeType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for dyn NativeType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        NativeType::type_id(self).hash(state)
    }
}

// Helper phantom data to make NativeType Sync
#[derive(Clone, Copy)]
struct SyncPhantomData<T: ?Sized> {
    phantom: std::marker::PhantomData<std::sync::atomic::AtomicPtr<Box<T>>>,
}
impl<T: ?Sized> SyncPhantomData<T> {
    fn new() -> Self {
        Self {
            phantom: std::marker::PhantomData,
        }
    }
}

pub struct NativeTypeImpl<T> {
    _marker: SyncPhantomData<T>,
}
impl<T> Clone for NativeTypeImpl<T> {
    fn clone(&self) -> Self {
        Self::new()
    }
}
impl<T> NativeTypeImpl<T> {
    pub fn new() -> Self {
        Self {
            _marker: SyncPhantomData::new(),
        }
    }
}

impl<T> PartialEq for NativeTypeImpl<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<T> Eq for NativeTypeImpl<T> {}

impl<T: 'static> NativeType for NativeTypeImpl<T> {
    fn type_id(&self) -> TypeId {
        TypeId::of::<T>()
    }

    fn type_name(&self) -> &'static str {
        type_name::<T>()
    }
}

impl Debug for dyn NativeType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.type_name())
    }
}

/// A generic type implemented in Rust
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GenericNativeType {
    native: Box<dyn NativeType>,
    arguments: SmallVec1<Type>,
}

fn count_generics_rec(generics: &[Type], counts: &mut TypeGenericCountMap) -> usize {
    generics
        .iter()
        .map(|ty| ty.count_generics_rec(counts))
        .max()
        .unwrap_or(0)
}

fn format_generics(count: usize) -> String {
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

/// The type of a function
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionType {
    pub arg_ty: Vec<Type>,
    pub return_ty: Type,
}

type TypeGenericCountMap = HashMap<Type, usize>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Type {
    world: Option<NonMaxU32>, // If None, current local world
    index: u32,
}

impl Type {
    // helper constructors
    pub fn primitive<T: Clone + 'static>() -> Self {
        add_type(TypeData::Primitive(native_type::<T>()))
    }

    pub fn generic_native<T: Clone + 'static>(arguments: SmallVec1<Self>) -> Self {
        let native = native_type::<T>();
        add_type(TypeData::GenericNative(Box::new(GenericNativeType {
            arguments,
            native,
        })))
    }

    pub fn generic_native_type(native: Box<dyn NativeType>, arguments: SmallVec1<Self>) -> Self {
        add_type(TypeData::GenericNative(Box::new(GenericNativeType {
            arguments,
            native,
        })))
    }

    pub fn generic_variable(id: usize) -> Self {
        add_type(TypeData::GenericVariable(id))
    }

    pub fn variant(mut types: Vec<(Ustr, Self)>) -> Self {
        types.sort_by(|(a, _), (b, _)| a.cmp(b));
        add_type(TypeData::Variant(types))
    }

    pub fn tuple(elements: Vec<Self>) -> Self {
        add_type(TypeData::Tuple(elements))
    }

    pub fn record(fields: Vec<(Ustr, Self)>) -> Self {
        assert_unique_strings(&fields);
        add_type(TypeData::Record(fields))
    }

    pub fn function(ft: FunctionType) -> Self {
        add_type(TypeData::Function(Box::new(ft)))
    }

    pub fn nullary_function(ret: Self) -> Self {
        Self::function(FunctionType {
            arg_ty: vec![],
            return_ty: ret,
        })
    }

    pub fn unary_function(arg: Self, ret: Self) -> Self {
        Self::function(FunctionType {
            arg_ty: vec![arg],
            return_ty: ret,
        })
    }

    pub fn binary_function(arg1: Self, arg2: Self, ret: Self) -> Self {
        Self::function(FunctionType {
            arg_ty: vec![arg1, arg2],
            return_ty: ret,
        })
    }

    pub fn new_type(name: Ustr, ty: Self) -> Self {
        add_type(TypeData::NewType(name, ty))
    }

    pub fn new_local_ref(index: u32) -> Self {
        Self {
            world: None,
            index,
        }
    }

    // subtyping
    pub fn can_be_used_in_place_of_with_subst(
        self,
        that: Self,
        substitutions: &mut HashMap<usize, Type>,
    ) -> bool {
        // If the types are the same, they can be used in place of each other
        if self == that {
            return true;
        }
        // A generic ref can be replaced by anything, but keep in mind the substitutions
        if let TypeData::GenericVariable(that_index) = get_type(that) {
            match substitutions.get(&that_index) {
                Some(subst) => {
                    return self.can_be_used_in_place_of_with_subst(*subst, substitutions)
                }
                None => {
                    // do not perform substitution if we already have the correct index
                    if let TypeData::GenericVariable(this_index) = get_type(self) {
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
        get_type(self).can_be_used_in_place_of_with_subst(that, substitutions)
    }

    pub fn can_be_used_in_place_of(self, that: Self) -> bool {
        self.can_be_used_in_place_of_with_subst(that, &mut HashMap::new())
    }

    // generic counting
    fn count_generics_rec(&self, counts: &mut TypeGenericCountMap) -> usize {
        if counts.get(self).is_none() {
            counts.insert(*self, 0);
            let count = get_type(*self).count_generics_rec(counts);
            counts.insert(*self, count);
        }
        0
    }

    fn count_generics(&self) -> usize {
        let mut counts = HashMap::new();
        let local_count = self.count_generics_rec(&mut counts);
        local_count + counts.values().sum::<usize>()
    }

    pub fn format_generics(&self) -> String {
        format_generics(self.count_generics())
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
// impl Deref for Type {
//     type Target = TypeData;
//     fn deref(&self) -> &Self::Target {
//         get_type(*self)
//     }
// }
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
        let result = write!(f, "{}", get_type(*self));

        // Remove the value on back-tracking
        TYPE_DISPLAY_VISITED.with(|visited| {
            visited.borrow_mut().remove(self);
        });

        result
    }
}

thread_local! {
    static TYPE_DISPLAY_VISITED: RefCell<HashSet<Type>> = RefCell::new(HashSet::new());
}

/// The representation of a type in the system
#[derive(Debug, Clone, PartialEq, Eq, Hash, EnumAsInner)]
pub enum TypeData {
    /// A native type implemented in Rust without generics
    Primitive(Box<dyn NativeType>),
    /// A native type implemented in Rust with generics
    GenericNative(Box<GenericNativeType>),
    /// A type variable, to be used in generics context.
    /// Its parameter is its indentity in the context considered, as it is bound.
    GenericVariable(usize), // TODO: add bounds
    /// Tagged union sum type
    Variant(Vec<(Ustr, Type)>),
    /// Position-based product type
    Tuple(Vec<Type>),
    /// Named product type
    Record(Vec<(Ustr, Type)>),
    /// A function type
    Function(Box<FunctionType>),
    /// A named new type
    NewType(Ustr, Type),
}
// TODO: traits as bounds of generics

impl TypeData {
    /// Somewhat a sub-type, but named differently to accommodate generics
    fn can_be_used_in_place_of_with_subst(
        &self,
        that: Type,
        substitutions: &mut HashMap<usize, Type>,
    ) -> bool {
        // We know that that is not a GenericArg
        match self {
            // A primitive type can be used in place of itself or instantiate a generics
            TypeData::Primitive(this_ty) => match get_type(that) {
                TypeData::Primitive(that_ty) => this_ty == &that_ty,
                _ => false,
            },
            // A generic type can be used in place of itself with compatible type arguments, or instantiate a generics
            TypeData::GenericNative(this_gen) => match get_type(that) {
                TypeData::GenericNative(that_gen) => {
                    this_gen.native == that_gen.native
                        && this_gen.arguments.len() == that_gen.arguments.len()
                        && this_gen // covariant argument types
                            .arguments
                            .iter()
                            .zip(that_gen.arguments.iter())
                            .all(|(this_ty, that_ty)| {
                                this_ty.can_be_used_in_place_of_with_subst(*that_ty, substitutions)
                            })
                }
                _ => false,
            },
            // We trait generics as invariant
            TypeData::GenericVariable(_) => false,
            // This variant can be used in place of that variant if for every constructor and argument in that variant,
            // there is a constructor and argument in this union that can be used in place of it.
            TypeData::Variant(this_variant) => match get_type(that) {
                TypeData::Variant(that_variant) => that_variant.iter().all(|that_ctor| {
                    this_variant.iter().any(|this_ctor| {
                        this_ctor.0 == that_ctor.0
                            && this_ctor
                                .1
                                .can_be_used_in_place_of_with_subst(that_ctor.1, substitutions)
                    })
                }),
                _ => false,
            },
            // Larger tuples can be used in place of smaller tuples
            TypeData::Tuple(this_tuple) => match get_type(that) {
                TypeData::Tuple(that_tuple) => {
                    this_tuple.len() >= that_tuple.len()
                        && this_tuple // covariant element types
                            .iter()
                            .zip(that_tuple.iter())
                            .all(|(this_ty, that_ty)| {
                                this_ty.can_be_used_in_place_of_with_subst(*that_ty, substitutions)
                            })
                }
                _ => false,
            },
            // This record can be used in place of that record if for every field in that record,
            // there is a field in this record that can be used in place of it.
            TypeData::Record(this_record) => match get_type(that) {
                TypeData::Record(that_record) => that_record.iter().all(|(that_name, that_ty)| {
                    this_record.iter().any(|(this_name, this_ty)| {
                        this_name == that_name
                            && this_ty.can_be_used_in_place_of_with_subst(*that_ty, substitutions)
                    })
                }),
                _ => false,
            },
            // A function can be used in place of another function if the argument types are contravariant and return type covariant.
            TypeData::Function(this_fn) => {
                let this_args = &this_fn.arg_ty;
                let this_ty = &this_fn.return_ty;
                match get_type(that) {
                    TypeData::Function(that_fun) => {
                        let that_args = &that_fun.arg_ty;
                        let that_ty = &that_fun.return_ty;
                        this_args.len() == that_args.len()
                            && this_args // contravariant argument types
                                .iter()
                                .zip(that_args.iter())
                                .all(|(this_ty, that_ty)| {
                                    that_ty
                                        .can_be_used_in_place_of_with_subst(*this_ty, substitutions)
                                })
                            && this_ty.can_be_used_in_place_of_with_subst(*that_ty, substitutions)
                        // covariant return type
                    }
                    _ => false,
                }
            }
            // A new type can be used in place of the type it wraps
            TypeData::NewType(_, this_ty) => {
                this_ty.can_be_used_in_place_of_with_subst(that, substitutions)
            }
        }
    }

    pub fn can_be_used_in_place_of(&self, that: Type) -> bool {
        self.can_be_used_in_place_of_with_subst(that, &mut HashMap::new())
    }

    // helper functions
    fn rank(&self) -> usize {
        match self {
            TypeData::Primitive(_) => 0,
            TypeData::GenericNative(_) => 1,
            TypeData::GenericVariable(_) => 2,
            TypeData::Variant(_) => 3,
            TypeData::Tuple(_) => 4,
            TypeData::Record(_) => 5,
            TypeData::Function(_) => 6,
            TypeData::NewType(_, _) => 7,
        }
    }

    fn count_generics_rec(&self, counts: &mut TypeGenericCountMap) -> usize {
        match self {
            TypeData::Primitive(_) => 0,
            TypeData::GenericNative(g) => count_generics_rec(&g.arguments, counts),
            TypeData::GenericVariable(id) => *id + 1, // the max number is this index + 1
            TypeData::Variant(types) => types
                .iter()
                .map(|(_, ty)| ty.count_generics_rec(counts))
                .max()
                .unwrap_or(0),
            TypeData::Tuple(types) => types
                .iter()
                .map(|ty| ty.count_generics_rec(counts))
                .max()
                .unwrap_or(0),
            TypeData::Record(fields) => fields
                .iter()
                .map(|(_, ty)| ty.count_generics_rec(counts))
                .max()
                .unwrap_or(0),
            TypeData::Function(function) => count_generics_rec(&function.arg_ty, counts)
                .max(function.return_ty.count_generics_rec(counts)),
            TypeData::NewType(_, ty) => ty.count_generics_rec(counts),
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

impl fmt::Display for TypeData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypeData::Primitive(id) => {
                let tn = id.as_ref().type_name();
                write!(f, "{}", tn.rsplit_once("::").unwrap_or(("", tn)).1)
            }
            TypeData::GenericNative(g) => {
                let tn = g.native.as_ref().type_name();
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
            TypeData::GenericVariable(id) => write!(f, "{}", generic_index_to_char(*id)),
            TypeData::Variant(types) => {
                for (i, (name, ty)) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{name}: {ty}")?;
                }
                Ok(())
            }
            TypeData::Tuple(members) => {
                write!(f, "(")?;
                write_with_separator(members, ", ", f)?;
                write!(f, ")")
            }
            TypeData::Record(fields) => {
                write!(f, "{{ ")?;
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: {ty}")?;
                }
                write!(f, " }}")
            }
            TypeData::Function(function) => {
                write!(
                    f,
                    "({}) -> {}",
                    function
                        .arg_ty
                        .iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    function.return_ty
                )
            }
            TypeData::NewType(name, ty) => write!(f, "{name}({ty})"),
        }
    }
}

impl Ord for TypeData {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            // Compare the raw pointers (addresses) of the weak references
            (TypeData::Primitive(a), TypeData::Primitive(b)) => a.cmp(b),
            (TypeData::GenericNative(a), TypeData::GenericNative(b)) => a.cmp(b),
            (TypeData::GenericVariable(a), TypeData::GenericVariable(b)) => a.cmp(b),
            (TypeData::Variant(a), TypeData::Variant(b)) => a.cmp(b),
            (TypeData::Tuple(a), TypeData::Tuple(b)) => a.cmp(b),
            (TypeData::Record(a), TypeData::Record(b)) => a.cmp(b),
            (TypeData::Function(a), TypeData::Function(b)) => a
                .arg_ty
                .cmp(&b.arg_ty)
                .then_with(|| a.return_ty.cmp(&b.return_ty)),
            _ => self.rank().cmp(&other.rank()),
        }
    }
}

impl PartialOrd for TypeData {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn generic_index_to_char(index: usize) -> char {
    char::from_digit(index as u32 + 10, 36).unwrap_or('_')
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

type TypeWorld = IndexSet<TypeData>;

struct TypeUniverse {
    worlds: Vec<TypeWorld>,
}

impl TypeUniverse {
    fn new() -> Self {
        Self {
            worlds: vec![IndexSet::new()],
        }
    }

    fn insert_type(&mut self, ty: TypeData) -> Type {
        self.insert_types::<_, First<_>>([ty]).0.unwrap()
    }

    fn insert_types<I, O>(&mut self, tys: I) -> O
    where
        I: IntoIterator<Item = TypeData>,
        O: FromIterator<Type>,
    {
        // 1. partition tys into cliques of recursive types
        // 2. sort each clique
        // 3. put each clique in a hash map
        // 4. normalize indices of each clique to the universe set
        // 5. link the hash map to these
        // 6. return references to the normalized cliques

        // current el cheapos implementation not handling recursive types
        let world = &mut self.worlds[0];
        tys.into_iter()
            .enumerate()
            .map(|(_i, ty)| {
                let (index, _new) = world.insert_full(ty);
                Type {
                    world: Some(NonMaxU32::new(0).unwrap()),
                    index: index as u32,
                }
            })
            .collect()
    }

    fn get_type(&self, r: Type) -> &TypeData {
        self.worlds[r.world.unwrap().get() as usize]
            .get_index(r.index as usize)
            .unwrap()
    }
}

fn types() -> &'static RwLock<TypeUniverse> {
    static TYPES: OnceLock<RwLock<TypeUniverse>> = OnceLock::new();
    TYPES.get_or_init(|| RwLock::new(TypeUniverse::new()))
}

pub fn add_type(ty: TypeData) -> Type {
    types().write().unwrap().insert_type(ty)
}

pub fn add_types<I, O>(tys: I) -> O
where
    I: IntoIterator<Item = TypeData>,
    O: FromIterator<Type>,
{
    types().write().unwrap().insert_types(tys)
}

pub fn get_type(r: Type) -> TypeData {
    types().read().unwrap().get_type(r).clone()
}
// FIXME: is there a way to return a reference to the type data?
// Something like this:
/*
struct DataRef<'a, T> {
    // The lock guard is stored here to keep the lock alive.
    _guard: std::sync::RwLockReadGuard<'a, MyGlobalStruct>,
    // Reference to the data inside the global structure.
    pub data: &'a T,
}

and

impl<'a, T> Deref for DataRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.data
    }
}

*/

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
    use smallvec::smallvec;
    use ustr::ustr;

    #[test]
    fn can_be_used_in_place_of() {
        // A bunch of types
        let _i32 = Type::primitive::<i32>();
        let _f32 = Type::primitive::<f32>();
        let _string = Type::primitive::<String>();
        let _gen_arg0 = Type::generic_variable(0);

        // Primitive types
        assert!(_i32.can_be_used_in_place_of(_i32));
        assert!(_i32.can_be_used_in_place_of(_gen_arg0));
        assert!(!_i32.can_be_used_in_place_of(_f32));
        assert!(!_i32.can_be_used_in_place_of(_string));

        // Generics
        assert!(_gen_arg0.can_be_used_in_place_of(_gen_arg0));
        let _gen_arg1 = Type::generic_variable(1);
        assert!(_gen_arg0.can_be_used_in_place_of(_gen_arg1));
        #[derive(Debug, Clone)]
        struct List;
        let _gen_unbound = Type::generic_native::<List>(smallvec![_gen_arg0]);
        let _gen_bound_i32 = Type::generic_native::<List>(smallvec![_i32]);
        let _gen_bound_string = Type::generic_native::<List>(smallvec![_string]);
        #[derive(Debug, Clone)]
        struct Map;
        let _gen_2_unbound_a_b = Type::generic_native::<Map>(smallvec![_gen_arg0, _gen_arg1]);
        let _gen_2_unbound_b_a = Type::generic_native::<Map>(smallvec![_gen_arg1, _gen_arg0]);
        let _gen_2_partial_bound_i32_a = Type::generic_native::<Map>(smallvec![_i32, _gen_arg0]);
        let _gen_2_partial_bound_a_i32 = Type::generic_native::<Map>(smallvec![_gen_arg0, _i32]);
        let _gen_2_bound_i32_i32 = Type::generic_native::<Map>(smallvec![_i32, _i32]);
        let _gen_2_bound_i32_f32 = Type::generic_native::<Map>(smallvec![_i32, _f32]);
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

        // Union
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

        // // named
        // let named_types = [
        //     Rc::new((ustr("Int"), RefCell::new(_i32.clone()))),
        //     Rc::new((ustr("OtherInt"), RefCell::new(_i32.clone())))
        // ];
        // let _int = TypeData::named(&named_types[0]);
        // assert!(_int.can_be_used_in_place_of(&_int));
        // assert!(_int.can_be_used_in_place_of(&_gen_arg0));
        // assert!(_int.can_be_used_in_place_of(&_i32));
        // let _other_int = TypeData::named(&named_types[1]);
        // assert!(_other_int.can_be_used_in_place_of(&_other_int));
        // assert!(_other_int.can_be_used_in_place_of(&_gen_arg0));
        // assert!(_other_int.can_be_used_in_place_of(&_i32));
        // assert!(!_other_int.can_be_used_in_place_of(&_int));
    }
}
