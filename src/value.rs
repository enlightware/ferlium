use dyn_clone::DynClone;
use dyn_eq::DynEq;
use enum_as_inner::EnumAsInner;
use std::{
    any::Any,
    cell::RefCell,
    fmt::{self, Display},
    rc::Rc,
};
use ustr::Ustr;

use crate::{
    containers::{SVec2, B},
    format::write_with_separator,
    function::{Function, FunctionRef},
    module::ModuleEnv,
    r#type::TypeVarSubstitution,
};

// Support for primitive values

/// Native types must implement this so that they can be displayed.
pub trait NativeDisplay {
    fn native_fmt(&self, f: &mut fmt::Formatter) -> fmt::Result;
}

pub trait NativeValue: Any + fmt::Debug + DynClone + DynEq + NativeDisplay + 'static {
    fn as_any(&self) -> &dyn Any;
    fn as_mut_any(&mut self) -> &mut dyn Any;
    fn into_any(self: B<Self>) -> B<dyn Any>;
}

dyn_clone::clone_trait_object!(NativeValue);
dyn_eq::eq_trait_object!(NativeValue);

impl<T: Any + fmt::Debug + std::cmp::Eq + Clone + NativeDisplay> NativeValue for T {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_mut_any(&mut self) -> &mut dyn Any {
        self
    }

    fn into_any(self: B<Self>) -> B<dyn Any> {
        self
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

    pub fn native<T: NativeValue + 'static>(value: T) -> Self {
        Value::Native(B::new(value))
    }

    pub fn tuple(values: impl Into<SVec2<Value>>) -> Self {
        Value::Tuple(B::new(values.into()))
    }

    pub fn function(function: Function) -> Self {
        Value::Function(FunctionRef::new_strong(&Rc::new(RefCell::new(function))))
    }

    pub fn into_primitive_ty<T: 'static>(self) -> Option<T> {
        use Value::*;
        match self {
            Native(value) => Some(*value.into_any().downcast::<T>().ok()?),
            _ => None,
        }
    }

    pub fn as_primitive_ty<T: 'static>(&self) -> Option<&T> {
        match self {
            Value::Native(value) => NativeValue::as_any(value.as_ref()).downcast_ref::<T>(),
            _ => None,
        }
    }

    pub fn as_primitive_ty_mut<T: 'static>(&mut self) -> Option<&mut T> {
        match self {
            Value::Native(value) => value.as_mut().as_mut_any().downcast_mut::<T>(),
            _ => None,
        }
    }

    pub fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = "⎸ ".repeat(indent);
        use Value::*;
        match self {
            Native(value) => {
                // TODO: later, optionally have pretty print for native values
                writeln!(f, "{indent_str}{:?}", value)
            }
            Variant(variant) => {
                writeln!(f, "{indent_str}{}(", variant.tag)?;
                variant.value.format_ind(f, env, indent + 1)?;
                writeln!(f, "{indent_str})")
            }
            Tuple(tuple) => {
                writeln!(f, "(")?;
                for element in tuple.iter() {
                    element.format_ind(f, env, indent + 1)?;
                }
                writeln!(f, ")")
            }
            Function(function) => {
                let function = function.get();
                let function = function.borrow();
                writeln!(f, "{indent_str}lambda @ {:p}", *function,)?;
                function.format_ind(f, env, indent + 1)
            }
        }
    }

    pub fn substitute(&mut self, subst: &TypeVarSubstitution) {
        use Value::*;
        match self {
            Native(_) => {}
            Variant(variant) => {
                variant.value.substitute(subst);
            }
            Tuple(tuple) => {
                for element in tuple.iter_mut() {
                    element.substitute(subst);
                }
            }
            Function(function) => {
                let function = function.get();
                let mut function = function.borrow_mut();
                if let Some(script_fn) = function.as_script_mut() {
                    script_fn.code.substitute(subst);
                }
            }
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Native(value) => value.native_fmt(f),
            Value::Variant(variant) => {
                write!(f, "{}({})", variant.tag, variant.value)
            }
            Value::Tuple(tuple) => {
                write!(f, "(")?;
                write_with_separator(tuple.iter(), ", ", f)?;
                write!(f, ")")
            }
            Value::Function(function) => {
                let function = function.get();
                let function = function.borrow();
                write!(f, "{:?}", function)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn value_as_primitive_ty_mut() {
        let v = 42isize;
        let mut a = Value::native(v);
        let mut b = v;
        assert_eq!(a.as_primitive_ty_mut::<isize>(), Some(&mut b));
    }
}
