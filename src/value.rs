use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use std::{
    any::{type_name, Any, TypeId},
    cell::RefCell,
    fmt,
    rc::Rc,
};
use ustr::Ustr;

use crate::{
    containers::{SVec2, B},
    error::RuntimeError,
    function::{FunctionDescription, FunctionRef},
    ir::{EvalCtx, Place},
    r#type::{write_with_separator, NativeType, Type, TypeOfNativeValue},
};

// Support for primitive values

// pub trait PrimitiveDisplay {
//     fn pfmt(&self, f: &mut fmt::Formatter) -> fmt::Result;
// }

// impl<T: fmt::Display> PrimitiveDisplay for T {
//     fn pfmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         self.fmt(f)
//     }
// }

// impl PrimitiveDisplay for () {
//     fn pfmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(f, "()")
//     }
// }

// TODO: investigate: https://docs.rs/manyfmt/latest/manyfmt/

pub trait NativeValue: Any + fmt::Debug + DynClone + DynEq + 'static {
    fn as_any(&self) -> &dyn Any;
    fn as_mut_any(&mut self) -> &mut dyn Any;
    fn into_any(self: B<Self>) -> B<dyn Any>;
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
    fn native_type(&self) -> NativeType;
}

dyn_clone::clone_trait_object!(NativeValue);
dyn_eq::eq_trait_object!(NativeValue);

impl<T: Any + fmt::Debug + std::cmp::Eq + Clone + TypeOfNativeValue> NativeValue for T {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_mut_any(&mut self) -> &mut dyn Any {
        self
    }

    fn into_any(self: B<Self>) -> B<dyn Any> {
        self
    }

    fn type_id(&self) -> TypeId {
        TypeId::of::<T>()
    }

    fn type_name(&self) -> &'static str {
        type_name::<T>()
    }

    fn native_type(&self) -> NativeType {
        self.type_of_value()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompoundValueType {
    Tuple,
    Record(B<SVec2<Ustr>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantValue {
    pub tag: Ustr,
    pub value: Value,
}

/// A value in the system
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum Value {
    Native(B<dyn NativeValue>),
    Variant(B<VariantValue>),
    Tuple(B<SVec2<Value>>),
    Function(FunctionRef),
}

impl Value {
    pub fn unit() -> Self {
        Self::native::<()>(())
    }

    pub fn native<T: Any + Clone + fmt::Debug + std::cmp::Eq + TypeOfNativeValue + 'static>(value: T) -> Self {
        Value::Native(B::new(value))
    }

    pub fn tuple(values: impl Into<SVec2<Value>>) -> Self {
        Value::Tuple(B::new(values.into()))
    }

    pub fn function(description: FunctionDescription) -> Self {
        Value::Function(FunctionRef::new_strong(&Rc::new(RefCell::new(description))))
    }

    pub fn into_primitive_ty<T: 'static>(self) -> Option<T> {
        match self {
            Value::Native(value) => Some(*value.into_any().downcast::<T>().ok()?),
            _ => None,
        }
    }

    pub fn as_primitive_ty_mut<T: 'static>(&mut self) -> Option<&mut T> {
        match self {
            Value::Native(value) => value.as_mut().as_mut_any().downcast_mut::<T>(),
            _ => None,
        }
    }

    pub fn ty(&self) -> Type {
        match self {
            Value::Native(value) => Type::native_type(value.native_type()),
            Value::Variant(_) => todo!("implement variants"),
            Value::Tuple(tuple) => {
                let types = tuple.iter().map(Value::ty).collect();
                Type::tuple(types)
            }
            Value::Function(function) => function.get().borrow().ty(),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Native(value) => write!(f, "{:?}: {}", value, value.as_ref().type_name()),
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
            Value::Function(function) => {
                let function = function.get();
                let function = function.borrow();
                write!(f, "{:?}: {}", function.code, function.ty())
            }
        }
    }
}

/// Either a value or a unique mutable reference to a value.
/// This allows to implement the mutable value semantics.
#[derive(Debug, PartialEq, Eq, EnumAsInner)]
pub enum ValOrMut {
    /// A value, itself
    Val(Value),
    /// A mutable reference, index in the environment plus path within the value
    Mut(Place),
}
impl ValOrMut {
    pub fn into_primitive<T: 'static>(self) -> Option<T> {
        match self {
            ValOrMut::Val(val) => val.into_primitive_ty::<T>(),
            ValOrMut::Mut(_) => None,
        }
    }
    pub fn as_mut_primitive<T: 'static>(
        self,
        ctx: &mut EvalCtx,
    ) -> Result<Option<&mut T>, RuntimeError> {
        Ok(match self {
            ValOrMut::Val(_) => None,
            ValOrMut::Mut(place) => place.target_ref(ctx)?.as_primitive_ty_mut::<T>(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn value_as_primitive_ty_mut() {
        let mut a = Value::native(42);
        let mut b = 42;
        assert_eq!(a.as_primitive_ty_mut::<isize>(), Some(&mut b));
    }
}
