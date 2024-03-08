use std::any::type_name;
use std::any::TypeId;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{self, Debug};
use std::rc::Rc;
use std::rc::Weak;

use dyn_clone::DynClone;
use dyn_eq::DynEq;
use ustr::Ustr;

use crate::assert::assert_unique_strings;
use crate::containers::SmallVec1;

pub trait NativeType: DynClone + DynEq {
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
}

pub fn native_type<T: Clone + 'static>() -> Box<dyn NativeType> {
    Box::new(NativeTypeImpl::<T> {
        _marker: std::marker::PhantomData::<T>,
    })
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

#[derive(Clone, Copy)]
pub struct NativeTypeImpl<T> {
    _marker: std::marker::PhantomData<T>,
}

impl<T> PartialEq for NativeTypeImpl<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<T> Eq for NativeTypeImpl<T> {}

impl<T: Clone + 'static> NativeType for NativeTypeImpl<T> {
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GenericNativeType {
    native: Box<dyn NativeType>,
    arguments: SmallVec1<Type>,
}

fn count_generics(generics: &[Type]) -> usize {
    generics.iter().map(Type::count_generics).max().unwrap_or(0)
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub arg_ty: Vec<Type>,
    pub return_ty: Type,
}

pub type NamedType = (Ustr, Type);

// Using Weak for simplicity now, later can be optimized with an arena and references
#[derive(Debug, Clone)]
pub struct NamedTypeRef(pub Weak<NamedType>);
impl PartialEq for NamedTypeRef {
    fn eq(&self, other: &Self) -> bool {
        self.0.ptr_eq(&other.0)
    }
}
impl Eq for NamedTypeRef {}

pub type NamedTypes = Vec<Rc<NamedType>>;

/// The representation of a type in the system
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// A native type implemented in Rust without generics
    Primitive(Box<dyn NativeType>),
    /// A native type implemented in Rust with generics
    GenericNative(Box<GenericNativeType>),
    /// A type variable, to be used in generics context.
    /// Its parameter is its indentity in the context considered, as it is bound.
    GenericVariable(usize),
    /// Anonymous sum type
    Union(Vec<Type>),
    /// Position-based product type
    Tuple(Vec<Type>),
    /// Named product type
    Record(Vec<(Ustr, Type)>),
    /// A function type
    Function(Box<FunctionType>),
    /// A type referenced by a key (a named constructor, like a datatype in ML)
    Named(NamedTypeRef),
}

impl Type {
    // constructors
    pub fn primitive<T: Clone + 'static>() -> Self {
        Self::Primitive(native_type::<T>())
    }

    pub fn generic_native<T: Clone + 'static>(arguments: SmallVec1<Self>) -> Self {
        let native = native_type::<T>();
        Self::GenericNative(Box::new(GenericNativeType { arguments, native }))
    }

    pub fn union(types: Vec<Self>) -> Self {
        Self::Union(types)
    }

    pub fn record(fields: Vec<(Ustr, Self)>) -> Self {
        assert_unique_strings(&fields);
        Self::Record(fields)
    }

    pub fn nullary_function(ret: Self) -> Self {
        Self::Function(Box::new(FunctionType {
            arg_ty: vec![],
            return_ty: ret,
        }))
    }

    pub fn unary_function(arg: Self, ret: Self) -> Self {
        Self::Function(Box::new(FunctionType {
            arg_ty: vec![arg],
            return_ty: ret,
        }))
    }

    pub fn binary_function(arg1: Self, arg2: Self, ret: Self) -> Self {
        Self::Function(Box::new(FunctionType {
            arg_ty: vec![arg1, arg2],
            return_ty: ret,
        }))
    }

    pub fn named(named: &Rc<NamedType>) -> Self {
        Self::Named(NamedTypeRef(Rc::downgrade(named)))
    }

    // public methods

    /// Somewhat a sub-type, but named differently to accommodate generics
    pub fn can_be_used_in_place_of_with_subst(
        &self,
        that: &Self,
        substitutions: &mut HashMap<usize, Type>,
    ) -> bool {
        // A generic ref can be replaced by anything, but keep in mind the substitutions
        if let Type::GenericVariable(that_index) = that {
            match substitutions.get(that_index) {
                Some(subst) => {
                    return self.can_be_used_in_place_of_with_subst(&subst.clone(), substitutions)
                }
                None => {
                    // do not perform substitution if we already have the correct index
                    if let Type::GenericVariable(this_index) = self {
                        if this_index == that_index {
                            return true;
                        }
                    }
                    substitutions.insert(*that_index, self.clone());
                    return true;
                }
            }
        }
        // We know that that is not a GenericArg
        match self {
            // A primitive type can be used in place of itself or instantiate a generics
            Type::Primitive(this_ty) => match that {
                Type::Primitive(that_ty) => this_ty == that_ty,
                _ => false,
            },
            // A generic type can be used in place of itself with compatible type arguments, or instantiate a generics
            Type::GenericNative(this_gen) => match that {
                Type::GenericNative(that_gen) => {
                    this_gen.native == that_gen.native
                        && this_gen.arguments.len() == that_gen.arguments.len()
                        && this_gen // covariant argument types
                            .arguments
                            .iter()
                            .zip(that_gen.arguments.iter())
                            .all(|(this_ty, that_ty)| {
                                this_ty.can_be_used_in_place_of_with_subst(that_ty, substitutions)
                            })
                }
                _ => false,
            },
            // We trait generics as invariant
            Type::GenericVariable(_) => false,
            // This union can be used in place of that union if for every type in that union,
            // there is a type in this union that can be used in place of it.
            Type::Union(this_union) => match that {
                Type::Union(that_union) => that_union.iter().all(|that_ty| {
                    this_union.iter().any(|this_ty| {
                        this_ty.can_be_used_in_place_of_with_subst(that_ty, substitutions)
                    })
                }),
                _ => false,
            },
            // Larger tuples can be used in place of smaller tuples
            Type::Tuple(this_tuple) => match that {
                Type::Tuple(that_tuple) => {
                    this_tuple.len() >= that_tuple.len()
                        && this_tuple // covariant element types
                            .iter()
                            .zip(that_tuple.iter())
                            .all(|(this_ty, that_ty)| {
                                this_ty.can_be_used_in_place_of_with_subst(that_ty, substitutions)
                            })
                }
                _ => false,
            },
            // This record can be used in place of that record if for every field in that record,
            // there is a field in this record that can be used in place of it.
            Type::Record(this_record) => match that {
                Type::Record(that_record) => that_record.iter().all(|(that_name, that_ty)| {
                    this_record.iter().any(|(this_name, this_ty)| {
                        this_name == that_name
                            && this_ty.can_be_used_in_place_of_with_subst(that_ty, substitutions)
                    })
                }),
                _ => false,
            },
            // A function can be used in place of another function if the argument types are contravariant and return type covariant.
            Type::Function(this_fn) => {
                let this_args = &this_fn.arg_ty;
                let this_ty = &this_fn.return_ty;
                match that {
                    Type::Function(that_fun) => {
                        let that_args = &that_fun.arg_ty;
                        let that_ty = &that_fun.return_ty;
                        this_args.len() == that_args.len()
                            && this_args // contravariant argument types
                                .iter()
                                .zip(that_args.iter())
                                .all(|(this_ty, that_ty)| {
                                    that_ty
                                        .can_be_used_in_place_of_with_subst(this_ty, substitutions)
                                })
                            && this_ty.can_be_used_in_place_of_with_subst(that_ty, substitutions)
                        // covariant return type
                    }
                    _ => false,
                }
            }
            Type::Named(this_ref) => match that {
                Type::Named(that_ref) => this_ref == that_ref,
                _ => this_ref
                    .0
                    .upgrade()
                    .unwrap()
                    .1
                    .can_be_used_in_place_of_with_subst(that, substitutions),
            },
        }
    }

    pub fn can_be_used_in_place_of(&self, that: &Self) -> bool {
        self.can_be_used_in_place_of_with_subst(that, &mut HashMap::new())
    }

    // helper functions
    fn rank(&self) -> usize {
        match self {
            Type::Primitive(_) => 0,
            Type::GenericNative(_) => 1,
            Type::GenericVariable(_) => 2,
            Type::Union(_) => 3,
            Type::Tuple(_) => 4,
            Type::Record(_) => 5,
            Type::Function(_) => 6,
            Type::Named(_) => 7,
        }
    }

    fn count_generics_rec(&self, counts: &mut HashMap<*const NamedType, usize>) -> usize {
        match self {
            Type::Primitive(_) => 0,
            Type::GenericNative(g) => count_generics(&g.arguments),
            Type::GenericVariable(id) => *id + 1, // the max number is this index + 1
            Type::Union(types) => types.iter().map(Self::count_generics).max().unwrap_or(0),
            Type::Tuple(types) => types.iter().map(Self::count_generics).max().unwrap_or(0),
            Type::Record(fields) => fields
                .iter()
                .map(|(_, t)| t.count_generics())
                .max()
                .unwrap_or(0),
            Type::Function(function) => {
                count_generics(&function.arg_ty).max(function.return_ty.count_generics())
            }
            Type::Named(named) => {
                let ptr = named.0.as_ptr();
                if counts.get(&ptr).is_none() {
                    counts.insert(ptr, 0);
                    let named = named.0.upgrade().unwrap();
                    let count = named.1.count_generics_rec(counts);
                    counts.insert(ptr, count);
                }
                0
            }
        }
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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Named(NamedTypeRef(weak)) => {
                write!(f, "{}", weak.upgrade().unwrap().0)
            }
            Type::Primitive(id) => {
                let tn = id.as_ref().type_name();
                write!(f, "{}", tn.rsplit_once("::").unwrap_or(("", tn)).1)
            }
            Type::GenericNative(g) => {
                let tn = g.native.as_ref().type_name();
                write!(
                    f,
                    "{}{}",
                    tn.rsplit_once("::").unwrap_or(("", tn)).1,
                    self.format_generics()
                )
            }
            Type::GenericVariable(id) => write!(f, "{}", generic_index_to_char(*id)),
            Type::Union(types) => write_with_separator(types, " | ", f),
            Type::Tuple(members) => {
                write!(f, "(")?;
                write_with_separator(members, ", ", f)?;
                write!(f, ")")
            }
            Type::Record(fields) => {
                write!(f, "{{ ")?;
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}: {ty}")?;
                }
                write!(f, " }}")
            }
            Type::Function(function) => {
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
        }
    }
}

impl Ord for Type {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            // Compare the raw pointers (addresses) of the weak references
            (Type::Named(a), Type::Named(b)) => a.0.as_ptr().cmp(&b.0.as_ptr()),
            (Type::Primitive(a), Type::Primitive(b)) => a.cmp(b),
            (Type::GenericNative(a), Type::GenericNative(b)) => a.cmp(b),
            (Type::GenericVariable(a), Type::GenericVariable(b)) => a.cmp(b),
            (Type::Union(a), Type::Union(b)) => a.cmp(b),
            (Type::Tuple(a), Type::Tuple(b)) => a.cmp(b),
            (Type::Record(a), Type::Record(b)) => a.cmp(b),
            (Type::Function(a), Type::Function(b)) => a
                .arg_ty
                .cmp(&b.arg_ty)
                .then_with(|| a.return_ty.cmp(&b.return_ty)),
            _ => self.rank().cmp(&other.rank()),
        }
    }
}

impl PartialOrd for Type {
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

// Note: if we need to solve type inference, see https://github.com/andrejbauer/plzoo/blob/master/src/poly/type_infer.ml
// Question: how to lookup local and parent variables in case of recursion with static typing? (static lexical scoping, see de Bruijn indices)
// See if needed: Explicit substitutions, M. Abadi, L. Cardelli, P.L. Curien, J.J. Lévy, Journal of Functional Programming 6(2), 1996.

#[cfg(test)]
mod tests {
    use super::*;
    use ustr::ustr;
    use smallvec::smallvec;

    #[test]
    fn can_be_used_in_place_of() {
        // A bunch of types
        let _i32 = Type::primitive::<i32>();
        let _f32 = Type::primitive::<f32>();
        let _string = Type::primitive::<String>();
        let _gen_arg0 = Type::GenericVariable(0);

        // Primitive types
        assert!(_i32.can_be_used_in_place_of(&_i32));
        assert!(_i32.can_be_used_in_place_of(&_gen_arg0));
        assert!(!_i32.can_be_used_in_place_of(&_f32));
        assert!(!_i32.can_be_used_in_place_of(&_string));

        // Generics
        assert!(_gen_arg0.can_be_used_in_place_of(&_gen_arg0));
        let _gen_arg1 = Type::GenericVariable(1);
        assert!(_gen_arg0.can_be_used_in_place_of(&_gen_arg1));
        #[derive(Debug, Clone)]
        struct List;
        let _gen_unbound = Type::generic_native::<List>(smallvec![_gen_arg0.clone()]);
        let _gen_bound_i32 = Type::generic_native::<List>(smallvec![_i32.clone()]);
        let _gen_bound_string = Type::generic_native::<List>(smallvec![_string.clone()]);
        #[derive(Debug, Clone)]
        struct Map;
        let _gen_2_unbound_a_b =
            Type::generic_native::<Map>(smallvec![_gen_arg0.clone(), _gen_arg1.clone()]);
        let _gen_2_unbound_b_a =
            Type::generic_native::<Map>(smallvec![_gen_arg1.clone(), _gen_arg0.clone()]);
        let _gen_2_partial_bound_i32_a =
            Type::generic_native::<Map>(smallvec![_i32.clone(), _gen_arg0.clone()]);
        let _gen_2_partial_bound_a_i32 =
            Type::generic_native::<Map>(smallvec![_gen_arg0.clone(), _i32.clone()]);
        let _gen_2_bound_i32_i32 = Type::generic_native::<Map>(smallvec![_i32.clone(), _i32.clone()]);
        let _gen_2_bound_i32_f32 = Type::generic_native::<Map>(smallvec![_i32.clone(), _f32.clone()]);
        assert!(_gen_unbound.can_be_used_in_place_of(&_gen_unbound));
        assert!(_gen_bound_i32.can_be_used_in_place_of(&_gen_unbound));
        assert!(_gen_bound_string.can_be_used_in_place_of(&_gen_unbound));
        assert!(_gen_2_unbound_a_b.can_be_used_in_place_of(&_gen_2_unbound_a_b));
        assert!(_gen_2_unbound_b_a.can_be_used_in_place_of(&_gen_2_unbound_b_a));
        assert!(_gen_2_unbound_a_b.can_be_used_in_place_of(&_gen_2_unbound_b_a));
        assert!(_gen_2_unbound_b_a.can_be_used_in_place_of(&_gen_2_unbound_a_b));
        assert!(_gen_2_partial_bound_i32_a.can_be_used_in_place_of(&_gen_2_partial_bound_i32_a));
        assert!(_gen_2_partial_bound_a_i32.can_be_used_in_place_of(&_gen_2_partial_bound_a_i32));
        assert!(!_gen_2_partial_bound_i32_a.can_be_used_in_place_of(&_gen_2_partial_bound_a_i32));
        assert!(_gen_2_partial_bound_i32_a.can_be_used_in_place_of(&_gen_2_unbound_a_b));
        assert!(_gen_2_partial_bound_i32_a.can_be_used_in_place_of(&_gen_2_unbound_b_a));
        assert!(_gen_2_partial_bound_a_i32.can_be_used_in_place_of(&_gen_2_unbound_a_b));
        assert!(_gen_2_partial_bound_a_i32.can_be_used_in_place_of(&_gen_2_unbound_b_a));
        assert!(_gen_2_bound_i32_i32.can_be_used_in_place_of(&_gen_2_unbound_a_b));
        assert!(_gen_2_bound_i32_i32.can_be_used_in_place_of(&_gen_2_unbound_b_a));
        assert!(_gen_2_bound_i32_i32.can_be_used_in_place_of(&_gen_2_partial_bound_i32_a));
        assert!(_gen_2_bound_i32_i32.can_be_used_in_place_of(&_gen_2_partial_bound_a_i32));
        assert!(_gen_2_bound_i32_i32.can_be_used_in_place_of(&_gen_2_bound_i32_i32));
        assert!(!_gen_2_bound_i32_i32.can_be_used_in_place_of(&_gen_2_bound_i32_f32));
        assert!(_gen_2_bound_i32_f32.can_be_used_in_place_of(&_gen_2_unbound_a_b));
        assert!(_gen_2_bound_i32_f32.can_be_used_in_place_of(&_gen_2_unbound_b_a));
        assert!(_gen_2_bound_i32_f32.can_be_used_in_place_of(&_gen_2_partial_bound_i32_a));
        assert!(!_gen_2_bound_i32_f32.can_be_used_in_place_of(&_gen_2_partial_bound_a_i32));
        assert!(!_gen_2_bound_i32_f32.can_be_used_in_place_of(&_gen_2_bound_i32_i32));
        assert!(_gen_2_bound_i32_f32.can_be_used_in_place_of(&_gen_2_bound_i32_f32));

        // Union
        let _union_i32_f32 = Type::union(vec![_i32.clone(), _f32.clone()]);
        let _union_f32_i32 = Type::union(vec![_f32.clone(), _i32.clone()]);
        let _union_i32_f32_string = Type::union(vec![_i32.clone(), _f32.clone(), _string.clone()]);
        let _union_string_i32_f32 = Type::union(vec![_string.clone(), _i32.clone(), _f32.clone()]);
        assert!(_union_i32_f32.can_be_used_in_place_of(&_union_i32_f32));
        assert!(_union_f32_i32.can_be_used_in_place_of(&_union_f32_i32));
        assert!(_union_i32_f32.can_be_used_in_place_of(&_union_f32_i32));
        assert!(_union_f32_i32.can_be_used_in_place_of(&_union_i32_f32));
        assert!(_union_i32_f32_string.can_be_used_in_place_of(&_union_i32_f32));
        assert!(_union_i32_f32_string.can_be_used_in_place_of(&_union_f32_i32));
        assert!(_union_string_i32_f32.can_be_used_in_place_of(&_union_i32_f32));
        assert!(_union_string_i32_f32.can_be_used_in_place_of(&_union_f32_i32));

        // Tuples
        let _tuple_i32 = Type::Tuple(vec![_i32.clone()]);
        let _tuple_f32 = Type::Tuple(vec![_f32.clone()]);
        let _tuple_i32_i32 = Type::Tuple(vec![_i32.clone(), _i32.clone()]);
        let _tuple_i32_f32 = Type::Tuple(vec![_i32.clone(), _f32.clone()]);
        let _tuple_f32_i32 = Type::Tuple(vec![_f32.clone(), _i32.clone()]);
        assert!(_tuple_i32.can_be_used_in_place_of(&_tuple_i32));
        assert!(!_tuple_i32.can_be_used_in_place_of(&_tuple_f32));
        assert!(_tuple_i32_i32.can_be_used_in_place_of(&_tuple_i32));
        assert!(_tuple_i32_f32.can_be_used_in_place_of(&_tuple_i32));
        assert!(!_tuple_f32_i32.can_be_used_in_place_of(&_tuple_i32));

        // Record
        let x = ustr("x");
        let y = ustr("y");
        let z = ustr("z");
        let _record_vec2_i32 = Type::record(vec![
            (x, _i32.clone()),
            (y, _i32.clone()),
        ]);
        let _record_vec2_f32 = Type::record(vec![
            (x, _f32.clone()),
            (y, _f32.clone()),
        ]);
        let _record_vec3_f32 = Type::record(vec![
            (x, _f32.clone()),
            (y, _f32.clone()),
            (z, _f32.clone()),
        ]);
        let _record_vec3_f32_shuffled = Type::record(vec![
            (z, _f32.clone()),
            (x, _f32.clone()),
            (y, _f32.clone()),
        ]);
        let _record_vec2_gen = Type::record(vec![
            (x, _gen_arg0.clone()),
            (y, _gen_arg0.clone()),
        ]);
        let _record_het = Type::record(vec![
            (x, _i32.clone()),
            (y, _f32.clone()),
        ]);
        assert!(_record_vec2_i32.can_be_used_in_place_of(&_record_vec2_i32));
        assert!(_record_vec2_f32.can_be_used_in_place_of(&_record_vec2_f32));
        assert!(!_record_vec2_i32.can_be_used_in_place_of(&_record_vec2_f32));
        assert!(_record_vec3_f32.can_be_used_in_place_of(&_record_vec2_f32));
        assert!(!_record_vec2_f32.can_be_used_in_place_of(&_record_vec3_f32));
        assert!(_record_vec3_f32_shuffled.can_be_used_in_place_of(&_record_vec3_f32));
        assert!(_record_vec3_f32.can_be_used_in_place_of(&_record_vec3_f32_shuffled));
        assert!(_record_vec3_f32_shuffled.can_be_used_in_place_of(&_record_vec2_f32));
        assert!(_record_vec2_i32.can_be_used_in_place_of(&_record_vec2_gen));
        assert!(!_record_vec2_gen.can_be_used_in_place_of(&_record_vec2_i32));
        assert!(_record_het.can_be_used_in_place_of(&_record_het));
        assert!(!_record_vec2_i32.can_be_used_in_place_of(&_record_het));
        assert!(!_record_het.can_be_used_in_place_of(&_record_vec2_i32));
        assert!(!_record_het.can_be_used_in_place_of(&_record_vec2_gen));

        // Native functions
        // unary functions
        let _native_fn_i32_i32 = Type::unary_function(_i32.clone(), _i32.clone());
        let _native_fn_i32_f32 = Type::unary_function(_i32.clone(), _f32.clone());
        let _native_fn_f32_i32 = Type::unary_function(_f32.clone(), _i32.clone());
        let _native_fn_f32_f32 = Type::unary_function(_f32.clone(), _f32.clone());
        let _native_fn_any_i32 = Type::unary_function(_gen_arg0.clone(), _i32.clone());
        let _native_fn_i32_any = Type::unary_function(_i32.clone(), _gen_arg0.clone());
        assert!(_native_fn_i32_i32.can_be_used_in_place_of(&_native_fn_i32_i32));
        assert!(_native_fn_i32_f32.can_be_used_in_place_of(&_native_fn_i32_f32));
        assert!(!_native_fn_i32_i32.can_be_used_in_place_of(&_native_fn_i32_f32));
        assert!(_native_fn_any_i32.can_be_used_in_place_of(&_native_fn_i32_i32));
        assert!(_native_fn_any_i32.can_be_used_in_place_of(&_native_fn_f32_i32));
        assert!(!_native_fn_any_i32.can_be_used_in_place_of(&_native_fn_i32_f32));
        assert!(!_native_fn_any_i32.can_be_used_in_place_of(&_native_fn_f32_f32));
        assert!(!_native_fn_i32_any.can_be_used_in_place_of(&_native_fn_i32_i32));
        assert!(_native_fn_i32_i32.can_be_used_in_place_of(&_native_fn_i32_any));

        // binary functions
        // TODO: add more tests

        // named
        let named_types = vec![
            Rc::new((ustr("Int"), _i32.clone())),
            Rc::new((ustr("OtherInt"), _i32.clone())),
        ];
        let _int = Type::named(&named_types[0]);
        assert!(_int.can_be_used_in_place_of(&_int));
        assert!(_int.can_be_used_in_place_of(&_gen_arg0));
        assert!(_int.can_be_used_in_place_of(&_i32));
        let _other_int = Type::named(&named_types[1]);
        assert!(_other_int.can_be_used_in_place_of(&_other_int));
        assert!(_other_int.can_be_used_in_place_of(&_gen_arg0));
        assert!(_other_int.can_be_used_in_place_of(&_i32));
        assert!(!_other_int.can_be_used_in_place_of(&_int));
    }
}
