// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use dyn_clone::DynClone;
use dyn_eq::DynEq;
use dyn_hash::DynHash;
use enum_as_inner::EnumAsInner;
use std::{
    any::Any,
    cell::RefCell,
    collections::HashSet,
    fmt::{self, Display},
    hash::Hash,
    rc::Rc,
};
use ustr::Ustr;

use crate::{
    containers::{b, IntoSVec2, SVec2, B},
    format::{write_with_separator, write_with_separator_and_format_fn},
    function::{Function, FunctionPtr, FunctionRef},
    module::ModuleEnv,
    type_inference::InstSubstitution,
};

// Support for primitive values

/// Native types must implement this so that they can be displayed.
pub trait NativeDisplay {
    /// Format the native value as it would be written in the language.
    fn fmt_as_literal(&self, f: &mut fmt::Formatter) -> fmt::Result;
    /// Format the native value when converted to a string.
    fn fmt_in_to_string(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_as_literal(f)
    }
}

impl NativeDisplay for () {
    fn fmt_as_literal(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "()")
    }
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

pub trait HashableNativeValue:
    Any + fmt::Debug + DynClone + DynEq + DynHash + NativeDisplay + 'static
{
    fn into_native_value(self: B<Self>) -> B<dyn NativeValue>;
}

impl<T: NativeValue + Hash> HashableNativeValue for T {
    fn into_native_value(self: B<Self>) -> B<dyn NativeValue> {
        self
    }
}

dyn_clone::clone_trait_object!(HashableNativeValue);
dyn_eq::eq_trait_object!(HashableNativeValue);
dyn_hash::hash_trait_object!(HashableNativeValue);

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
impl VariantValue {
    pub fn tag_as_isize(&self) -> isize {
        self.tag.as_char_ptr() as isize
    }
}

/// A value in the system
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner)]
pub enum Value {
    /// A native value, a pointer to the underlying Rust value
    Native(B<dyn NativeValue>),
    /// A variant with its tag and payload
    Variant(B<VariantValue>),
    /// A tuple of values, or the data of a record
    Tuple(B<SVec2<Value>>),
    /// A function, with an optional name (if part of an immediate pointing to a named function)
    Function((FunctionRef, Option<Ustr>)),
}

impl Value {
    pub fn unit() -> Self {
        Self::native::<()>(())
    }

    pub fn native<T: NativeValue + 'static>(value: T) -> Self {
        Self::Native(b(value))
    }

    pub fn tuple_variant(tag: Ustr, values: impl IntoSVec2<Value>) -> Self {
        Self::raw_variant(tag, Self::tuple(values))
    }

    pub fn raw_variant(tag: Ustr, value: Value) -> Self {
        Self::Variant(b(VariantValue { tag, value }))
    }

    pub fn unit_variant(tag: Ustr) -> Self {
        Self::Variant(b(VariantValue {
            tag,
            value: Self::unit(),
        }))
    }

    pub fn tuple(values: impl IntoSVec2<Value>) -> Self {
        Self::Tuple(b(values.into_svec2()))
    }

    pub fn empty_tuple() -> Self {
        Self::Tuple(b(SVec2::new()))
    }

    pub fn function(function: Function) -> Self {
        Self::Function((
            FunctionRef::new_strong(&Rc::new(RefCell::new(function))),
            None,
        ))
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
            Self::Native(value) => NativeValue::as_any(value.as_ref()).downcast_ref::<T>(),
            _ => None,
        }
    }

    pub fn as_primitive_ty_mut<T: 'static>(&mut self) -> Option<&mut T> {
        match self {
            Self::Native(value) => value.as_mut().as_mut_any().downcast_mut::<T>(),
            _ => None,
        }
    }

    pub fn unwrap_fn_tuple_index(&self, index: usize) -> &FunctionRef {
        let fn_tuple = self.as_tuple().expect("Value is not a tuple");
        &fn_tuple[index]
            .as_function()
            .expect("Entry at index is not a function")
            .0
    }

    pub fn format_as_string(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Value::*;
        match self {
            Native(value) => value.fmt_in_to_string(f),
            Variant(variant) => {
                if variant.value.is_tuple() {
                    write!(f, "{}", variant.tag)?;
                    variant.value.format_as_string(f)
                } else {
                    write!(f, "{}(", variant.tag)?;
                    variant.value.format_as_string(f)?;
                    write!(f, ")")
                }
            }
            Tuple(tuple) => {
                write!(f, "(")?;
                write_with_separator_and_format_fn(tuple.iter(), ", ", Value::format_as_string, f)?;
                write!(f, ")")
            }
            Function((function, _)) => {
                let function = function.get();
                let function = function.borrow();
                write!(f, "{function:?}")
            }
        }
    }

    pub fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
        // Thread-local hash-map for cycle detection
        thread_local! {
            static FN_VISITED: RefCell<HashSet<FunctionPtr>> = RefCell::new(HashSet::new());
        }

        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        use Value::*;
        match self {
            Native(value) => {
                write!(f, "{indent_str}")?;
                value.fmt_as_literal(f)?;
                writeln!(f)
            }
            Variant(variant) => {
                if variant.value == Self::unit() {
                    writeln!(f, "{indent_str}{}", variant.tag)
                } else {
                    writeln!(f, "{indent_str}{} ", variant.tag)?;
                    variant.value.format_ind(f, env, spacing, indent + 1)
                }
            }
            Tuple(tuple) => {
                writeln!(f, "{indent_str}(")?;
                for element in tuple.iter() {
                    element.format_ind(f, env, spacing, indent + 1)?;
                }
                writeln!(f, "{indent_str})")
            }
            Function((function, name)) => {
                let function = function.get();
                let fn_ptr = function.as_ptr();
                let function = function.borrow();
                if let Some(name) = name {
                    writeln!(f, "{indent_str}function {name}")?;
                } else {
                    writeln!(f, "{indent_str}function @ {:p}", *function)?;
                }
                let cycle_detected = FN_VISITED.with(|visited| {
                    let mut visited = visited.borrow_mut();
                    if visited.contains(&fn_ptr) {
                        true
                    } else {
                        visited.insert(fn_ptr);
                        false
                    }
                });
                if cycle_detected {
                    writeln!(f, "{indent_str}⎸ self")?;
                    return Ok(());
                } else {
                    function.format_ind(f, env, spacing, indent + 1)?;
                }
                FN_VISITED.with(|visited| {
                    visited.borrow_mut().remove(&fn_ptr);
                });
                Ok(())
            }
        }
    }

    pub fn instantiate(&mut self, subst: &InstSubstitution) {
        use Value::*;
        match self {
            Native(_) => {}
            Variant(variant) => {
                variant.value.instantiate(subst);
            }
            Tuple(tuple) => {
                for element in tuple.iter_mut() {
                    element.instantiate(subst);
                }
            }
            Function((function, _)) => {
                let function = function.get();
                // Note: this can fail if we are having a recursive function used as a value, in that case do not recurse.
                let function = function.try_borrow_mut();
                if let Ok(mut function) = function {
                    if let Some(script_fn) = function.as_script_mut() {
                        script_fn.code.instantiate(subst);
                    }
                }
            }
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Value::*;
        match self {
            Native(value) => value.fmt_as_literal(f),
            Variant(variant) => {
                if variant.value.is_tuple() {
                    write!(f, "{}{}", variant.tag, variant.value)
                } else {
                    write!(f, "{}({})", variant.tag, variant.value)
                }
            }
            Tuple(tuple) => {
                write!(f, "(")?;
                write_with_separator(tuple.iter(), ", ", f)?;
                write!(f, ")")
            }
            Function((function, _)) => {
                let function = function.get();
                let function = function.borrow();
                write!(f, "{function:?}")
            }
        }
    }
}

/// A literal value is a native value that can be hashed.
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner, Hash)]
pub enum LiteralValue {
    Native(B<dyn HashableNativeValue>),
    Tuple(B<SVec2<LiteralValue>>),
}

impl LiteralValue {
    pub fn new_native<T: HashableNativeValue + 'static>(value: T) -> Self {
        Self::Native(b(value))
    }

    pub fn new_tuple(values: impl Into<SVec2<LiteralValue>>) -> Self {
        Self::Tuple(b(values.into()))
    }

    pub fn into_value(self) -> Value {
        use LiteralValue::*;
        match self {
            Native(value) => Value::Native(value.into_native_value()),
            Tuple(args) => Value::tuple(args.into_iter().map(Self::into_value).collect::<Vec<_>>()),
        }
    }
}

impl Display for LiteralValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LiteralValue::*;
        match self {
            Native(value) => value.fmt_as_literal(f),
            Tuple(tuple) => {
                write!(f, "(")?;
                write_with_separator(tuple.iter(), ", ", f)?;
                write!(f, ")")
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
