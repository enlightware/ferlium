use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use std::{
    any::{type_name, Any, TypeId},
    fmt,
};

use crate::{
    containers::SmallVec2, ir::{FunctionKey, Functions}, r#type::{write_with_separator, NativeType, Type}
};

// Support for primitive values

pub trait PrimitiveValue: Any + fmt::Debug + DynClone + DynEq + 'static {
    fn as_any(&self) -> &dyn Any;
    fn into_any(self: Box<Self>) -> Box<dyn Any>;
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
    fn native_type(&self) -> Box<dyn NativeType>;
    fn ty(&self) -> Type;
}

dyn_clone::clone_trait_object!(PrimitiveValue);
dyn_eq::eq_trait_object!(PrimitiveValue);

impl<T: Any + fmt::Debug + std::cmp::Eq + Clone> PrimitiveValue for T {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }

    fn type_id(&self) -> TypeId {
        TypeId::of::<T>()
    }

    fn type_name(&self) -> &'static str {
        type_name::<T>()
    }

    fn native_type(&self) -> Box<dyn NativeType> {
        crate::r#type::native_type::<T>()
    }

    fn ty(&self) -> Type {
        Type::primitive::<T>()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CompoundValue {
    pub values: SmallVec2<Value>,
    pub ty: Type,
}

/// A value in the system
#[derive(Debug, Clone, PartialEq, EnumAsInner)]
pub enum Value {
    Primitive(Box<dyn PrimitiveValue>),
    List(Box<CompoundValue>),
    Function(FunctionKey),
}

impl Value {
    pub fn primitive<T: Any + Clone + fmt::Debug + std::cmp::Eq + 'static>(value: T) -> Self {
        Value::Primitive(Box::new(value))
    }

    pub fn ty(&self, functions: &Functions) -> Type {
        match self {
            Value::Primitive(value) => value.as_ref().ty(),
            Value::List(value) => value.ty.clone(),
            Value::Function(key) => Type::Function(Box::new(functions[*key].ty.clone())),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Primitive(value) => write!(f, "{:?}: {}", value, value.as_ref().type_name()),
            Value::List(compound) => match &compound.ty {
                Type::Tuple(_) => {
                    write!(f, "(")?;
                    write_with_separator(&compound.values, ", ", f)?;
                    write!(f, "): {}", compound.ty)
                }
                Type::Record(s) => {
                    write!(f, "{{")?;
                    for (i, (name, ty)) in s.iter().enumerate() {
                        write!(f, "{}: {}: {}", name, compound.values[i], ty)?;
                        if i < compound.values.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, "}}: {}", compound.ty)
                }
                _ => panic!(
                    "Cannot display a list of values with type {:?}",
                    compound.ty
                ),
            },
            Value::Function(_) => todo!(),
        }
    }
}
