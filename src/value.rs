use dyn_clone::DynClone;
use enum_as_inner::EnumAsInner;
use std::{
    any::{type_name, Any, TypeId},
    fmt,
    ops::Deref,
};

use crate::r#type::{write_with_separator, NativeType, Type};

// Support for primitive values

pub trait PrimitiveValue: Any + fmt::Debug + DynClone + 'static {
    fn as_any(&self) -> &dyn Any;
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
    fn native_type(&self) -> Box<dyn NativeType>;
}

dyn_clone::clone_trait_object!(PrimitiveValue);

impl<T: Any + fmt::Debug + Clone> PrimitiveValue for T {
    fn as_any(&self) -> &dyn Any {
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

// Support for function pointers

pub trait NativeFunction: DynClone {
    fn call(&self, args: Vec<Value>) -> Value;
    fn ty(&self) -> Type;
}

dyn_clone::clone_trait_object!(NativeFunction);

pub trait BinaryNativeFunction:
    Fn(
    <Self as BinaryNativeFunction>::A,
    <Self as BinaryNativeFunction>::B,
) -> <Self as BinaryNativeFunction>::O
{
    type A;
    type B;
    type O;
}

impl<
        A: Clone + 'static,
        B: Clone + 'static,
        O: fmt::Debug + Clone + 'static,
        T: BinaryNativeFunction<A = A, B = B, O = O> + Clone,
    > NativeFunction for T
{
    fn call(&self, args: Vec<Value>) -> Value {
        let a = args[0]
            .as_primitive()
            .unwrap()
            .deref()
            .as_any()
            .downcast_ref::<A>()
            .unwrap();
        let b = args[1]
            .as_primitive()
            .unwrap()
            .deref()
            .as_any()
            .downcast_ref::<B>()
            .unwrap();

        Value::Primitive(Box::new(self(a.clone(), b.clone())))
    }

    fn ty(&self) -> Type {
        Type::primitive::<O>()
    }
}

impl fmt::Debug for dyn NativeFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NativeFunction @ {:p}", self)
    }
}

/// A value in the system, must be interpreted with its type
#[derive(Debug, Clone, EnumAsInner)]
pub enum Value {
    Primitive(Box<dyn PrimitiveValue>),
    List(Vec<Value>),
    NativeFunction(Box<dyn NativeFunction>), // TODO: present the function type somehow, maybe in a table?
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Primitive(value) => write!(f, "{:?}", value),
            Value::List(_) => todo!(),
            Value::NativeFunction(_) => todo!(),
        }
    }
}

pub struct TypedValue {
    pub value: Value,
    pub ty: Type,
}

impl fmt::Display for TypedValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.ty {
            Type::Primitive(_) => write!(f, "{}: {}", self.value, self.ty),
            Type::Generic(_) => write!(f, "{}: {}", self.value, self.ty), // TODO: validate that all generics are filled
            Type::GenericRef(_) => panic!("A value cannot have a generic type"),
            Type::Union(_) => write!(f, "{}: {}", self.value, self.ty),
            Type::Tuple(_) => {
                let values = match &self.value {
                    Value::List(values) => values,
                    _ => panic!("A tuple must be a list of values"),
                };
                write!(f, "(")?;
                write_with_separator(values, ", ", f)?;
                write!(f, "): {}", self.ty)
            }
            Type::Struct(s) => {
                let fields = match &self.value {
                    Value::List(fields) => fields,
                    _ => panic!("A struct must be a list of values"),
                };
                write!(f, "{{")?;
                for (i, (name, ty)) in s.iter().enumerate() {
                    write!(f, "{}: {}: {}", name, fields[i], ty)?;
                    if i < fields.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "}}: {}", self.ty)
            }
            Type::NativeFunction(_, _) => write!(f, "{:?}: {}", self.value, self.ty),
        }
    }
}
