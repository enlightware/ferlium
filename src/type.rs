use std::any::type_name;
use std::any::TypeId;
use std::fmt::{self, Debug};

use dyn_clone::DynClone;

// TODO: non-native function type

pub trait NativeType: DynClone {
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
}

pub fn native_type<T: Clone + 'static>() -> Box<dyn NativeType> {
    Box::new(NativeTypeImpl::<T> {
        _marker: std::marker::PhantomData::<T>,
    })
}

dyn_clone::clone_trait_object!(NativeType);

#[derive(Clone, Copy)]
pub struct NativeTypeImpl<T> {
    _marker: std::marker::PhantomData<T>,
}

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
#[derive(Debug, Clone)]
pub struct GenericType {
    generics: Vec<Type>,
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
#[derive(Debug, Clone)]
pub enum Type {
    /// A type implemented in Rust without generics
    Primitive(Box<dyn NativeType>),
    /// A type implemented in Rust with generics
    Generic(Box<GenericType>),
    /// Generic placeholder
    GenericRef(usize),
    /// Anonymous sum type
    Union(Vec<Type>),
    /// Position-based product type
    Tuple(Vec<Type>),
    /// Named product type
    Struct(Vec<(String, Type)>),
    /// A function that is implemented in Rust
    NativeFunction(Vec<Type>, Box<Type>),
}

impl Type {
    pub fn primitive<T: Clone + 'static>() -> Type {
        Type::Primitive(native_type::<T>())
    }

    fn count_generics(&self) -> usize {
        match self {
            Type::Primitive(_) => 0,
            Type::Generic(g) => count_generics(&g.generics),
            Type::GenericRef(id) => *id + 1, // the max number is this index + 1
            Type::Union(types) => types.iter().map(Self::count_generics).max().unwrap_or(0),
            Type::Tuple(types) => types.iter().map(Self::count_generics).max().unwrap_or(0),
            Type::Struct(fields) => fields
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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Primitive(id) => {
                write!(f, "{}", id.type_name())
            }
            Type::Generic(g) => write!(f, "{}{}", g.name, self.format_generics()),
            Type::GenericRef(id) => write!(f, "{}", generic_index_to_char(*id)),
            Type::Union(types) => write_with_separator(types, " | ", f),
            Type::Tuple(members) => {
                write!(f, "(")?;
                write_with_separator(members, ", ", f)?;
                write!(f, ")")
            }
            Type::Struct(fields) => {
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
