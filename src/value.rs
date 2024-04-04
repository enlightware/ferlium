use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use std::{
    any::{type_name, Any, TypeId},
    fmt::{self},
};
use ustr::Ustr;

use crate::{
    containers::SmallVec2,
    function::FunctionKey,
    r#type::{write_with_separator, NativeType},
};

// Support for primitive values

pub trait PrimitiveValue: Any + fmt::Debug + DynClone + DynEq + 'static {
    fn as_any(&self) -> &dyn Any;
    fn into_any(self: Box<Self>) -> Box<dyn Any>;
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
    fn native_type(&self) -> Box<dyn NativeType>;
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompoundValueType {
    Tuple,
    Record(Box<SmallVec2<Ustr>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantValue {
    pub tag: Ustr,
    pub value: Value,
}

/// A value in the system
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum Value {
    Primitive(Box<dyn PrimitiveValue>),
    Variant(Box<VariantValue>),
    Tuple(Box<SmallVec2<Value>>),
    Record(Box<SmallVec2<(Ustr, Value)>>),
    Function(FunctionKey),
}

impl Value {
    pub fn primitive<T: Any + Clone + fmt::Debug + std::cmp::Eq + 'static>(value: T) -> Self {
        Value::Primitive(Box::new(value))
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // FIXME: primitive always show the primitive naming
            Value::Primitive(value) => write!(f, "{:?}: {}", value, value.as_ref().type_name()),
            // Value::GenericNative(value) => {
            //     let tn = value.native.as_ref().type_name();
            //     write!(
            //         f,
            //         "{:?}: {}<",
            //         value.native,
            //         tn.rsplit_once("::").unwrap_or(("", tn)).1
            //     )?;
            //     write_with_separator(&value.arguments, ", ", f)?;
            //     write!(f, ">")
            // }
            Value::Variant(variant) => write!(f, "{}({})", variant.tag, variant.value),
            Value::Tuple(tuple) => {
                write!(f, "(")?;
                write_with_separator(tuple, ", ", f)?;
                write!(f, ")")
            }
            Value::Record(fields) => {
                write!(f, "{{")?;
                for (i, (name, value)) in fields.iter().enumerate() {
                    write!(f, "{}: {}", name, value)?;
                    if i < fields.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "}}")
            }
            Value::Function(function) => {
                let function = function.get();
                write!(f, "{:?}: {}", function.code, function.ty())
            }
        }
    }
}
