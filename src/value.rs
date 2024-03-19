use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use std::{
    any::{type_name, Any, TypeId},
    fmt,
};
use ustr::Ustr;

use crate::{
    containers::{SmallVec1, SmallVec2}, function::FunctionKey, r#type::{write_with_separator, NativeType, Type}
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericNativeValue {
    pub native: Box<dyn PrimitiveValue>,
    pub arguments: SmallVec1<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompoundValueType {
    Tuple,
    Record(Box<SmallVec2<Ustr>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompoundValue {
    pub values: SmallVec2<Value>,
    pub ty: CompoundValueType,
}
impl CompoundValue {
    pub fn ty(&self) -> Type {
        match &self.ty {
            CompoundValueType::Tuple => Type::Tuple(self.values.iter().map(|v| v.ty()).collect()),
            CompoundValueType::Record(names) => Type::Record(
                names
                    .iter()
                    .zip(self.values.iter())
                    .map(|(name, value)| (*name, value.ty()))
                    .collect(),
            ),
        }
    }
}

/// A value in the system
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum Value {
    Primitive(Box<dyn PrimitiveValue>),
    GenericNative(Box<GenericNativeValue>),
    Compound(Box<CompoundValue>),
    Function(FunctionKey),
}

impl Value {
    pub fn primitive<T: Any + Clone + fmt::Debug + std::cmp::Eq + 'static>(value: T) -> Self {
        Value::Primitive(Box::new(value))
    }

    pub fn generic_native(native: Box<dyn PrimitiveValue>, arguments: SmallVec1<Type>) -> Self {
        Value::GenericNative(Box::new(GenericNativeValue { native, arguments }))
    }

    pub fn compound(values: SmallVec2<Value>, ty: CompoundValueType) -> Self {
        Value::Compound(Box::new(CompoundValue { values, ty }))
    }

    pub fn ty(&self) -> Type {
        match self {
            Value::Primitive(value) => value.as_ref().ty(),
            Value::GenericNative(value) => {
                Type::generic_native_type(value.native.native_type(), value.arguments.clone())
            }
            Value::Compound(value) => match &value.ty {
                CompoundValueType::Tuple => {
                    Type::Tuple(value.values.iter().map(|v| v.ty()).collect())
                }
                CompoundValueType::Record(names) => Type::Record(
                    names
                        .iter()
                        .zip(value.values.iter())
                        .map(|(name, value)| (*name, value.ty()))
                        .collect(),
                ),
            },
            Value::Function(function) => {
                Type::Function(Box::new(function.get().ty.clone()))
            }
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Primitive(value) => write!(f, "{:?}: {}", value, value.as_ref().type_name()),
            Value::GenericNative(value) => {
                let tn = value.native.as_ref().type_name();
                write!(
                    f,
                    "{:?}: {}<",
                    value.native,
                    tn.rsplit_once("::").unwrap_or(("", tn)).1
                )?;
                write_with_separator(&value.arguments, ", ", f)?;
                write!(f, ">")
            }
            Value::Compound(compound) => match &compound.ty {
                CompoundValueType::Tuple => {
                    write!(f, "(")?;
                    write_with_separator(&compound.values, ", ", f)?;
                    write!(f, "): {}", compound.ty())
                }
                CompoundValueType::Record(s) => {
                    write!(f, "{{")?;
                    for (i, name) in s.iter().enumerate() {
                        let value = &compound.values[i];
                        write!(f, "{}: {}: {}", name, value, value.ty())?;
                        if i < compound.values.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, "}}: {}", compound.ty())
                }
            },
            Value::Function(function) => {
                let function = function.get();
                write!(f, "{:?}: {}", function.code, function.ty())
            },
        }
    }
}
