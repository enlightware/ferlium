// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use derive_new::new;
use dyn_clone::DynClone;
use dyn_eq::DynEq;
use dyn_hash::DynHash;
use enum_as_inner::EnumAsInner;
use std::{
    any::Any,
    fmt::{self, Display},
    hash::Hash,
};
use ustr::Ustr;

use crate::{
    containers::{B, IntoSVec2, SVec2, b},
    format::{FormatWithData, write_with_separator, write_with_separator_and_format_fn},
    module::{LocalFunctionId, ModuleEnv, ModuleId},
    r#type::{NativeType, Type, TypeKind},
};

// Support for primitive values

/// Native types must implement this so that they can be displayed.
pub trait NativeDisplay {
    /// Format the native value, without type information.
    fn fmt_repr(&self, f: &mut fmt::Formatter) -> fmt::Result;

    /// Format the native value, given its type information.
    fn fmt_pretty(&self, f: &mut fmt::Formatter, _ty: &NativeType) -> fmt::Result {
        self.fmt_repr(f)
    }
    /// Format the native value when converted to a string.
    fn fmt_in_to_string(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_repr(f)
    }
}

impl NativeDisplay for () {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

pub fn ustr_to_isize(tag: Ustr) -> isize {
    tag.as_char_ptr() as isize
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantValue {
    pub tag: Ustr,
    pub value: Value,
}
impl VariantValue {
    pub fn tag_as_isize(&self) -> isize {
        ustr_to_isize(self.tag)
    }
}

#[derive(Debug, Clone, new)]
pub struct FunctionValue {
    pub function: LocalFunctionId,
    pub module: ModuleId,
    pub captured: Vec<Value>,
}

impl PartialEq for FunctionValue {
    fn eq(&self, other: &Self) -> bool {
        self.function == other.function
            && self.module == other.module
            && self.captured == other.captured
    }
}
impl Eq for FunctionValue {}

/// A value in the system
#[derive(Debug, Clone, EnumAsInner)]
pub enum Value {
    /// A native value, a pointer to the underlying Rust value
    Native(B<dyn NativeValue>),
    /// A variant with its tag and payload
    Variant(B<VariantValue>),
    /// A tuple of values, or the data of a record
    Tuple(B<SVec2<Value>>),
    /// A first-class function
    Function(FunctionValue),
}

// Note: later we will not need that as Eq will be implemented through a trait
impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        use Value::*;
        match (self, other) {
            (Native(l0), Native(r0)) => l0 == r0,
            (Variant(l0), Variant(r0)) => l0 == r0,
            (Tuple(l0), Tuple(r0)) => l0 == r0,
            (Function(l0), Function(r0)) => l0 == r0,
            _ => false,
        }
    }
}

impl Eq for Value {}

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

    pub fn function(function: LocalFunctionId, module: ModuleId) -> Self {
        Self::Function(FunctionValue::new(function, module, vec![]))
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

    pub fn format_as_string_repr(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Value::*;
        match self {
            Native(value) => value.fmt_in_to_string(f),
            Variant(variant) => {
                if variant.value.is_tuple() {
                    write!(f, "{}", variant.tag)?;
                    variant.value.format_as_string_repr(f)
                } else {
                    write!(f, "{}(", variant.tag)?;
                    variant.value.format_as_string_repr(f)?;
                    write!(f, ")")
                }
            }
            Tuple(tuple) => {
                write!(f, "(")?;
                write_with_separator_and_format_fn(
                    tuple.iter(),
                    ", ",
                    Value::format_as_string_repr,
                    f,
                )?;
                write!(f, ")")
            }
            Function(fv) => {
                if fv.captured.is_empty() {
                    write!(f, "function {} in {}", fv.function, fv.module)
                } else {
                    write!(
                        f,
                        "closure of function {} in {} with captured values [",
                        fv.function, fv.module
                    )?;
                    write_with_separator_and_format_fn(
                        fv.captured.iter(),
                        ", ",
                        Value::format_as_string_repr,
                        f,
                    )?;
                    write!(f, "]")
                }
            }
        }
    }

    /// Convert this value into a string representation.
    /// As no type information is provided, the internal representation is used.
    pub fn to_string_repr(&self) -> String {
        struct FormatInToString<'a>(pub &'a Value);
        impl fmt::Display for FormatInToString<'_> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                self.0.format_as_string_repr(f)
            }
        }
        format!("{}", FormatInToString(self))
    }

    /// Format this value in an indented representation for debugging.
    /// As no type information is provided, the internal representation is used.
    pub fn format_ind_repr(
        &self,
        f: &mut std::fmt::Formatter,
        _env: &ModuleEnv<'_>,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
        let indent_str = format!("{}{}", "  ".repeat(spacing), "⎸ ".repeat(indent));
        use Value::*;
        match self {
            Native(value) => {
                write!(f, "{indent_str}")?;
                value.fmt_repr(f)?;
                writeln!(f)
            }
            Variant(variant) => {
                if variant.value == Self::unit() {
                    writeln!(f, "{indent_str}{}", variant.tag)
                } else {
                    writeln!(f, "{indent_str}{} ", variant.tag)?;
                    variant.value.format_ind_repr(f, _env, spacing, indent + 1)
                }
            }
            Tuple(tuple) => {
                writeln!(f, "{indent_str}(")?;
                for element in tuple.iter() {
                    element.format_ind_repr(f, _env, spacing, indent + 1)?;
                }
                writeln!(f, "{indent_str})")
            }
            Function(fv) => {
                if fv.captured.is_empty() {
                    writeln!(f, "function {} in {}", fv.function, fv.module)
                } else {
                    writeln!(
                        f,
                        "closure of function {} in {} with captured values [",
                        fv.function, fv.module
                    )?;
                    for captured in &fv.captured {
                        captured.format_ind_repr(f, _env, spacing + 1, indent + 1)?;
                    }
                    writeln!(f, "{indent_str}]")
                }
            }
        }
    }

    /// Display this value in a pretty-printed way according to the provided type.
    /// This means that records will be displayed with their field names, etc.
    pub fn display_pretty<'a>(&'a self, ty: &'a Type) -> PrettyPrint<'a> {
        PrettyPrint(FormatWithData {
            value: self,
            data: ty,
        })
    }

    fn fmt_pretty(&self, f: &mut std::fmt::Formatter<'_>, ty: Type) -> std::fmt::Result {
        use TypeKind::*;
        match &*ty.data() {
            Variable(type_var) => panic!(
                "Cannot pretty-print value with uninstantiated type variable: {:?}",
                type_var
            ),
            Native(ty) => self.as_native().unwrap().fmt_pretty(f, ty),
            Variant(types) => {
                let variant = self.as_variant().unwrap();
                let inner_ty = types.iter().find(|(tag, _)| *tag == variant.tag).unwrap().1;
                if variant.value.is_tuple() {
                    write!(
                        f,
                        "{} {}",
                        variant.tag,
                        variant.value.display_pretty(&inner_ty)
                    )
                } else if variant.value == Value::unit() {
                    write!(f, "{}", variant.tag)
                } else {
                    write!(
                        f,
                        "{}({})",
                        variant.tag,
                        variant.value.display_pretty(&inner_ty)
                    )
                }
            }
            Tuple(tuple) => {
                let data = self.as_tuple().unwrap();
                write!(f, "(")?;
                write_with_separator(
                    data.iter()
                        .zip(tuple.iter())
                        .map(|(item, ty)| item.display_pretty(ty)),
                    ", ",
                    f,
                )?;
                write!(f, ")")
            }
            Record(fields) => {
                let data = self.as_tuple().unwrap();
                write!(f, "{{ ")?;
                write_with_separator(
                    data.iter()
                        .zip(fields.iter())
                        .map(|(item, (name, ty))| format!("{}: {}", name, item.display_pretty(ty))),
                    ", ",
                    f,
                )?;
                write!(f, " }}")
            }
            Function(_) => {
                use Value::*;
                match self {
                    Function(_) => self.format_as_string_repr(f),
                    _ => panic!("Value of type Function expected"),
                }
            }
            Named(named_type) => {
                let separator = if named_type.def.shape.data().is_variant() {
                    "::"
                } else {
                    " "
                };
                write!(
                    f,
                    "{}{}{}",
                    &named_type.def.name,
                    separator,
                    self.display_pretty(&named_type.def.shape)
                )
            }
            Never => panic!("A value of type Never cannot exist"),
        }
    }
}

pub struct PrettyPrint<'a>(FormatWithData<'a, Value, Type>);

impl<'a> std::fmt::Display for PrettyPrint<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.value.fmt_pretty(f, *self.0.data)
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
            Native(value) => value.fmt_repr(f),
            Tuple(tuple) => {
                write!(f, "(")?;
                write_with_separator(tuple.iter(), ", ", f)?;
                write!(f, ")")
            }
        }
    }
}

pub fn build_dictionary_value(methods: &[LocalFunctionId], module_id: ModuleId) -> Value {
    let values: Vec<_> = methods
        .iter()
        .map(|&fn_id| Value::function(fn_id, module_id))
        .collect();
    Value::tuple(values)
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
