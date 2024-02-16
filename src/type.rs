use std::any::type_name;
use std::any::TypeId;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{self, Debug};

use dyn_clone::DynClone;
use dyn_eq::DynEq;

use crate::assert::assert_unique_strings;

// TODO: non-native function type

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
pub struct GenericType {
    arguments: Vec<Type>,
    name: &'static str,
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

/// The representation of a type in the system
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// A type implemented in Rust without generics
    Primitive(Box<dyn NativeType>),
    /// A type implemented in Rust with generics
    Generic(Box<GenericType>),
    /// Generic placeholder
    GenericArg(usize),
    /// Anonymous sum type
    Union(Vec<Type>),
    /// Position-based product type
    Tuple(Vec<Type>),
    /// Named product type
    Record(Vec<(String, Type)>),
    /// A function that is implemented in Rust
    NativeFunction(Vec<Type>, Box<Type>),
}

impl Type {
    // constructors
    pub fn primitive<T: Clone + 'static>() -> Self {
        Self::Primitive(native_type::<T>())
    }

    pub fn generic(name: &'static str, arguments: Vec<Self>) -> Self {
        Self::Generic(Box::new(GenericType { name, arguments }))
    }

    pub fn union(types: Vec<Self>) -> Self {
        Self::Union(types)
    }

    pub fn record(fields: Vec<(String, Self)>) -> Self {
        assert_unique_strings(&fields);
        Self::Record(fields)
    }

    // public methods

    /// Somewhat a sub-type, but named differently to accommodate generics
    pub fn can_be_used_in_place_of_with_subst(
        &self,
        that: &Self,
        substitutions: &mut HashMap<usize, Type>,
    ) -> bool {
        // A generic ref can be replaced by anything, but keep in mind the substitutions
        if let Type::GenericArg(that_index) = that {
            match substitutions.get(that_index) {
                Some(subst) => {
                    return self.can_be_used_in_place_of_with_subst(&subst.clone(), substitutions)
                }
                None => {
                    substitutions.insert(*that_index, self.clone());
                    return true;
                }
            }
        }
        // We know that that is not a GenericRef
        match self {
            // A primitive type can be used in place of itself or instantiate a generics
            Type::Primitive(this_ty) => match that {
                Type::Primitive(that_ty) => this_ty == that_ty,
                _ => false,
            },
            // A generic type can be used in place of itself with compatible type arguments, or instantiate a generics
            Type::Generic(this_gen) => match that {
                Type::Generic(that_gen) => {
                    this_gen.name == that_gen.name
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
            Type::GenericArg(_) => false,
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
            Type::NativeFunction(this_args, this_ty) => match that {
                Type::NativeFunction(that_args, that_ty) => {
                    this_args.len() == that_args.len()
                        && this_args // contravariant argument types
                            .iter()
                            .zip(that_args.iter())
                            .all(|(this_ty, that_ty)| {
                                that_ty.can_be_used_in_place_of_with_subst(this_ty, substitutions)
                            })
                        && this_ty.can_be_used_in_place_of_with_subst(that_ty, substitutions)
                    // covariant return type
                }
                _ => false,
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
            Type::Generic(_) => 1,
            Type::GenericArg(_) => 2,
            Type::Union(_) => 3,
            Type::Tuple(_) => 4,
            Type::Record(_) => 5,
            Type::NativeFunction(_, _) => 6,
        }
    }

    fn count_generics(&self) -> usize {
        match self {
            Type::Primitive(_) => 0,
            Type::Generic(g) => count_generics(&g.arguments),
            Type::GenericArg(id) => *id + 1, // the max number is this index + 1
            Type::Union(types) => types.iter().map(Self::count_generics).max().unwrap_or(0),
            Type::Tuple(types) => types.iter().map(Self::count_generics).max().unwrap_or(0),
            Type::Record(fields) => fields
                .iter()
                .map(|(_, t)| t.count_generics())
                .max()
                .unwrap_or(0),
            Type::NativeFunction(args, ret) => count_generics(args).max(ret.count_generics()),
        }
    }

    pub fn format_generics(&self) -> String {
        format_generics(self.count_generics())
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Primitive(id) => {
                let tn = id.type_name();
                write!(f, "{}", tn.rsplit_once("::").unwrap_or(("", tn)).1)
            }
            Type::Generic(g) => write!(f, "{}{}", g.name, self.format_generics()),
            Type::GenericArg(id) => write!(f, "{}", generic_index_to_char(*id)),
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
            Type::NativeFunction(args, ret) => {
                write!(
                    f,
                    "({}) -> {}",
                    args.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    ret
                )
            }
        }
    }
}

impl Ord for Type {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Type::Primitive(a), Type::Primitive(b)) => a.cmp(b),
            (Type::Generic(a), Type::Generic(b)) => a.cmp(b),
            (Type::GenericArg(a), Type::GenericArg(b)) => a.cmp(b),
            (Type::Union(a), Type::Union(b)) => a.cmp(b),
            (Type::Tuple(a), Type::Tuple(b)) => a.cmp(b),
            (Type::Record(a), Type::Record(b)) => a.cmp(b),
            (Type::NativeFunction(args_a, ret_a), Type::NativeFunction(args_b, ret_b)) => {
                args_a.cmp(args_b).then_with(|| ret_a.cmp(ret_b))
            }
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

    #[test]
    fn can_be_used_in_place_of() {
        // A bunch of types
        let _i32 = Type::primitive::<i32>();
        let _f32 = Type::primitive::<f32>();
        let _string = Type::primitive::<String>();
        let _gen_arg0 = Type::GenericArg(0);

        // Primitive types
        assert!(_i32.can_be_used_in_place_of(&_i32));
        assert!(_i32.can_be_used_in_place_of(&_gen_arg0));
        assert!(!_i32.can_be_used_in_place_of(&_f32));
        assert!(!_i32.can_be_used_in_place_of(&_string));

        // Generics
        let _gen_arg1 = Type::GenericArg(1);
        let _gen_unbound = Type::generic("list", vec![_gen_arg0.clone()]);
        let _gen_bound_i32 = Type::generic("list", vec![_i32.clone()]);
        let _gen_bound_string = Type::generic("list", vec![_string.clone()]);
        let _gen_2_unbound_a_b = Type::generic("map", vec![_gen_arg0.clone(), _gen_arg1.clone()]);
        let _gen_2_unbound_b_a = Type::generic("map", vec![_gen_arg1.clone(), _gen_arg0.clone()]);
        let _gen_2_partial_bound_i32_a =
            Type::generic("map", vec![_i32.clone(), _gen_arg0.clone()]);
        let _gen_2_partial_bound_a_i32 =
            Type::generic("map", vec![_gen_arg0.clone(), _i32.clone()]);
        let _gen_2_bound_i32_i32 = Type::generic("map", vec![_i32.clone(), _i32.clone()]);
        let _gen_2_bound_i32_f32 = Type::generic("map", vec![_i32.clone(), _f32.clone()]);
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
        let _record_vec2_i32 = Type::record(vec![
            ("x".to_string(), _i32.clone()),
            ("y".to_string(), _i32.clone()),
        ]);
        let _record_vec2_f32 = Type::record(vec![
            ("x".to_string(), _f32.clone()),
            ("y".to_string(), _f32.clone()),
        ]);
        let _record_vec3_f32 = Type::record(vec![
            ("x".to_string(), _f32.clone()),
            ("y".to_string(), _f32.clone()),
            ("z".to_string(), _f32.clone()),
        ]);
        let _record_vec3_f32_shuffled = Type::record(vec![
            ("z".to_string(), _f32.clone()),
            ("x".to_string(), _f32.clone()),
            ("y".to_string(), _f32.clone()),
        ]);
        let _record_vec2_gen = Type::record(vec![
            ("x".to_string(), _gen_arg0.clone()),
            ("y".to_string(), _gen_arg0.clone()),
        ]);
        let _record_het = Type::record(vec![
            ("x".to_string(), _i32.clone()),
            ("y".to_string(), _f32.clone()),
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
        let _native_fn_i32_i32 = Type::NativeFunction(vec![_i32.clone()], Box::new(_i32.clone()));
        let _native_fn_i32_f32 = Type::NativeFunction(vec![_i32.clone()], Box::new(_f32.clone()));
        let _native_fn_f32_i32 = Type::NativeFunction(vec![_f32.clone()], Box::new(_i32.clone()));
        let _native_fn_f32_f32 = Type::NativeFunction(vec![_f32.clone()], Box::new(_f32.clone()));
        let _native_fn_any_i32 =
            Type::NativeFunction(vec![_gen_arg0.clone()], Box::new(_i32.clone()));
        let _native_fn_i32_any =
            Type::NativeFunction(vec![_i32.clone()], Box::new(_gen_arg0.clone()));
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
    }
}
