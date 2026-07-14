// Copyright 2026 Enlightware GmbH
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
    fmt::{self, Display},
    hash::Hash,
    mem::ManuallyDrop,
};
use ustr::Ustr;

use crate::{
    containers::{B, IntoSVec2, SVec2, b},
    format::write_with_separator,
    module::{FunctionId, SubscriptId, TraitDictionaryId},
};

// Support for primitive values

/// Native types implement this when they need a Rust-side literal/string representation.
pub trait NativeDisplay {
    /// Format the native value, without type information.
    fn fmt_repr(&self, f: &mut fmt::Formatter) -> fmt::Result;

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

pub trait NativeValueType: Any + fmt::Debug + 'static {}

impl<T: Any + fmt::Debug + NativeDisplay + 'static> NativeValueType for T {}

pub trait NativeValue: NativeValueType {
    fn as_any(&self) -> &dyn Any;
    fn as_mut_any(&mut self) -> &mut dyn Any;
    fn into_any(self: B<Self>) -> B<dyn Any>;
}

impl<T: NativeValueType> NativeValue for T {
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

/// A native value that can be hashed and compared for equality.
/// This is required for values to be used as literal values in patterns, etc.
pub trait LiteralNativeValue:
    Any + fmt::Debug + DynClone + DynEq + DynHash + NativeDisplay + 'static
{
    fn as_any(&self) -> &dyn Any;
    fn into_native_value(self: B<Self>) -> B<dyn NativeValue>;
}

impl<T: NativeValue + Clone + Hash + Eq + NativeDisplay> LiteralNativeValue for T {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn into_native_value(self: B<Self>) -> B<dyn NativeValue> {
        self
    }
}

dyn_clone::clone_trait_object!(LiteralNativeValue);
dyn_eq::eq_trait_object!(LiteralNativeValue);
dyn_hash::hash_trait_object!(LiteralNativeValue);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompoundValueType {
    Tuple,
    Record(B<SVec2<Ustr>>),
}

pub fn ustr_to_isize(tag: Ustr) -> isize {
    tag.as_char_ptr() as isize
}

#[derive(Debug)]
pub struct VariantValue {
    pub tag: Ustr,
    pub value: Value,
}
impl VariantValue {
    pub fn tag_as_isize(&self) -> isize {
        ustr_to_isize(self.tag)
    }
}

/// Hidden constraint evidence captured by first-class capabilities.
///
/// Typeclass constraints are represented as dictionaries. Projection
/// constraints are represented as first-class subscript capabilities.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HiddenEvidenceArgValue {
    TraitDictionary(TraitDictionaryId),
    Subscript(B<SubscriptValue>),
}

/// Runtime representation of a first-class function.
///
/// Function values carry a code identity plus two hidden argument groups:
/// constraint evidence captured while instantiating generic functions, and the
/// owned source-level closure environment. Only the closure environment is
/// managed by `Value::clone`/`Value::drop`; hidden evidence arguments are not
/// Ferlium values.
#[derive(Debug)]
pub struct FunctionValue {
    pub function: FunctionId,
    /// Hidden dictionary/evidence arguments supplied separately from value arguments.
    pub hidden_args: Vec<HiddenEvidenceArgValue>,
    /// Owned source-level closure environment, stored as a tuple value.
    pub closure_env: Value,
    pub closure_env_len: usize,
    /// Runtime `Value` dictionary metadata for cloning/dropping `closure_env`.
    /// `None` means `closure_env_len == 0`.
    pub closure_env_value_dictionary: Option<TraitDictionaryId>,
}

impl FunctionValue {
    pub fn bare(function: FunctionId) -> Self {
        Self {
            function,
            hidden_args: Vec::new(),
            closure_env: Value::uninit(),
            closure_env_len: 0,
            closure_env_value_dictionary: None,
        }
    }

    pub fn closure(
        function: FunctionId,
        hidden_args: Vec<HiddenEvidenceArgValue>,
        captures: Vec<Value>,
        closure_env_value_dictionary: Option<TraitDictionaryId>,
    ) -> Self {
        let closure_env_len = captures.len();
        debug_assert_eq!(closure_env_value_dictionary.is_some(), closure_env_len > 0);
        Self {
            function,
            hidden_args,
            closure_env: if captures.is_empty() {
                Value::uninit()
            } else {
                Value::tuple(captures)
            },
            closure_env_len,
            closure_env_value_dictionary,
        }
    }

    pub fn closure_env_values(&self) -> &[Value] {
        if self.closure_env_len == 0 {
            &[]
        } else {
            self.closure_env.as_tuple().unwrap()
        }
    }
}

/// Runtime representation of a first-class subscript capability.
///
/// Subscript values carry implementation identity plus captured hidden evidence.
/// Receiver and index/application arguments belong to subscript application,
/// not to the value itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubscriptValue {
    pub subscript: SubscriptId,
    /// Hidden dictionary/evidence arguments supplied separately from value arguments.
    /// Generic structural projection uses this to capture generated subscript evidence.
    pub hidden_args: Vec<HiddenEvidenceArgValue>,
}

impl SubscriptValue {
    pub fn bare(subscript: SubscriptId) -> Self {
        Self {
            subscript,
            hidden_args: Vec::new(),
        }
    }
}

/// A value in the system.
///
/// Runtime duplication must go through generated Ferlium `Value::clone`
/// dispatch, while literals use [`LiteralValue`] and are converted into fresh
/// runtime values when evaluated.
#[derive(Debug)]
pub enum Value {
    /// Internal uninitialized storage used while `Value::clone` writes into a target.
    Uninit,
    /// A native value, a pointer to the underlying Rust value
    Native(ManuallyDrop<B<dyn NativeValue>>),
    /// A variant with its tag and payload
    Variant(ManuallyDrop<B<VariantValue>>),
    /// A tuple of values, or the data of a record
    Tuple(ManuallyDrop<B<SVec2<Value>>>),
    /// A first-class function
    Function(ManuallyDrop<B<FunctionValue>>),
    /// A first-class subscript capability
    Subscript(ManuallyDrop<B<SubscriptValue>>),
}

impl Value {
    pub fn uninit() -> Self {
        Self::Uninit
    }

    pub fn unit() -> Self {
        Self::native::<()>(())
    }

    pub fn is_unit(&self) -> bool {
        self.as_primitive_ty::<()>().is_some()
    }

    pub fn to_literal_value(&self) -> Option<LiteralValue> {
        match self {
            Self::Native(_) =>
            {
                #[allow(clippy::manual_map)]
                if self.as_primitive_ty::<()>().is_some() {
                    Some(LiteralValue::new_native(()))
                } else if let Some(value) = self.as_primitive_ty::<bool>() {
                    Some(LiteralValue::new_native(*value))
                } else if let Some(value) = self.as_primitive_ty::<isize>() {
                    Some(LiteralValue::new_native(*value))
                } else if let Some(value) = self.as_primitive_ty::<crate::std::string::String>() {
                    Some(LiteralValue::new_native(value.clone()))
                } else {
                    None
                }
            }
            Self::Tuple(values) => Some(LiteralValue::new_tuple(
                values
                    .iter()
                    .map(Value::to_literal_value)
                    .collect::<Option<Vec<_>>>()?,
            )),
            Self::Uninit | Self::Variant(_) | Self::Function(_) | Self::Subscript(_) => None,
        }
    }

    pub fn native<T: NativeValue + 'static>(value: T) -> Self {
        Self::Native(ManuallyDrop::new(b(value)))
    }

    pub fn native_box(value: B<dyn NativeValue>) -> Self {
        Self::Native(ManuallyDrop::new(value))
    }

    pub fn tuple_variant(tag: Ustr, values: impl IntoSVec2<Value>) -> Self {
        Self::raw_variant(tag, Self::tuple(values))
    }

    pub fn raw_variant(tag: Ustr, value: Value) -> Self {
        Self::Variant(ManuallyDrop::new(b(VariantValue { tag, value })))
    }

    pub fn unit_variant(tag: Ustr) -> Self {
        Self::raw_variant(tag, Self::unit())
    }

    pub fn tuple(values: impl IntoSVec2<Value>) -> Self {
        Self::Tuple(ManuallyDrop::new(b(values.into_svec2())))
    }

    pub fn empty_tuple() -> Self {
        Self::tuple(Vec::<Value>::new())
    }

    pub fn function(function: FunctionId) -> Self {
        Self::function_value(FunctionValue::bare(function))
    }

    pub fn function_value(function: FunctionValue) -> Self {
        Self::Function(ManuallyDrop::new(b(function)))
    }

    pub fn subscript(subscript: SubscriptId) -> Self {
        Self::subscript_value(SubscriptValue::bare(subscript))
    }

    pub fn subscript_value(subscript: SubscriptValue) -> Self {
        Self::Subscript(ManuallyDrop::new(b(subscript)))
    }

    pub fn is_tuple(&self) -> bool {
        matches!(self, Self::Tuple(_))
    }

    pub fn as_native(&self) -> Option<&B<dyn NativeValue>> {
        match self {
            Self::Native(value) => Some(value),
            _ => None,
        }
    }

    pub fn as_native_mut(&mut self) -> Option<&mut B<dyn NativeValue>> {
        match self {
            Self::Native(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_native(self) -> Option<B<dyn NativeValue>> {
        match self {
            Self::Native(value) => Some(ManuallyDrop::into_inner(value)),
            _ => None,
        }
    }

    pub fn as_variant(&self) -> Option<&B<VariantValue>> {
        match self {
            Self::Variant(value) => Some(value),
            _ => None,
        }
    }

    pub fn as_variant_mut(&mut self) -> Option<&mut B<VariantValue>> {
        match self {
            Self::Variant(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_variant(self) -> Option<B<VariantValue>> {
        match self {
            Self::Variant(value) => Some(ManuallyDrop::into_inner(value)),
            _ => None,
        }
    }

    pub fn as_tuple(&self) -> Option<&B<SVec2<Value>>> {
        match self {
            Self::Tuple(value) => Some(value),
            _ => None,
        }
    }

    pub fn as_tuple_mut(&mut self) -> Option<&mut B<SVec2<Value>>> {
        match self {
            Self::Tuple(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_tuple(self) -> Option<B<SVec2<Value>>> {
        match self {
            Self::Tuple(value) => Some(ManuallyDrop::into_inner(value)),
            _ => None,
        }
    }

    pub fn into_tuple_element(self, index: usize) -> Option<Value> {
        match self {
            Self::Tuple(values) => {
                take_nth_discarding_rest(ManuallyDrop::into_inner(values), index)
            }
            other => {
                other.discard_storage();
                None
            }
        }
    }

    pub fn into_projected_value(self, index: usize) -> Option<Value> {
        match self {
            Self::Tuple(values) => {
                take_nth_discarding_rest(ManuallyDrop::into_inner(values), index)
            }
            Self::Variant(value) if index == 0 => Some(ManuallyDrop::into_inner(value).value),
            other => {
                other.discard_storage();
                None
            }
        }
    }

    pub fn as_function(&self) -> Option<&B<FunctionValue>> {
        match self {
            Self::Function(value) => Some(value),
            _ => None,
        }
    }

    pub fn as_function_mut(&mut self) -> Option<&mut B<FunctionValue>> {
        match self {
            Self::Function(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_function(self) -> Option<B<FunctionValue>> {
        match self {
            Self::Function(value) => Some(ManuallyDrop::into_inner(value)),
            _ => None,
        }
    }

    pub fn as_subscript(&self) -> Option<&B<SubscriptValue>> {
        match self {
            Self::Subscript(value) => Some(value),
            _ => None,
        }
    }

    pub fn as_subscript_mut(&mut self) -> Option<&mut B<SubscriptValue>> {
        match self {
            Self::Subscript(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_subscript(self) -> Option<B<SubscriptValue>> {
        match self {
            Self::Subscript(value) => Some(ManuallyDrop::into_inner(value)),
            _ => None,
        }
    }

    /// Reclaim the boxed interpreter storage for a value whose logical
    /// Ferlium-level drop has already run, without invoking `Value::drop` again.
    pub fn discard_storage(self) {
        match self {
            Self::Uninit => {}
            Self::Native(value) => drop(ManuallyDrop::into_inner(value)),
            Self::Variant(value) => {
                let mut value = ManuallyDrop::into_inner(value);
                let payload = std::mem::replace(&mut value.value, Value::uninit());
                payload.discard_storage();
            }
            Self::Tuple(values) => {
                let values = ManuallyDrop::into_inner(values);
                for value in *values {
                    value.discard_storage();
                }
            }
            Self::Function(value) => {
                let mut value = ManuallyDrop::into_inner(value);
                let closure_env = std::mem::replace(&mut value.closure_env, Value::uninit());
                closure_env.discard_storage();
            }
            Self::Subscript(value) => {
                drop(ManuallyDrop::into_inner(value));
            }
        }
    }

    pub fn into_primitive_ty<T: 'static>(self) -> Option<T> {
        use Value::*;
        match self {
            Uninit => panic!("attempted to read an uninitialized value"),
            Native(value) => Some(
                *ManuallyDrop::into_inner(value)
                    .into_any()
                    .downcast::<T>()
                    .ok()?,
            ),
            _ => None,
        }
    }

    pub fn as_primitive_ty<T: 'static>(&self) -> Option<&T> {
        match self {
            Self::Uninit => panic!("attempted to read an uninitialized value"),
            Self::Native(value) => NativeValue::as_any(value.as_ref()).downcast_ref::<T>(),
            _ => None,
        }
    }

    pub fn as_primitive_ty_mut<T: 'static>(&mut self) -> Option<&mut T> {
        match self {
            Self::Uninit => panic!("attempted to mutably read an uninitialized value"),
            Self::Native(value) => value.as_mut().as_mut_any().downcast_mut::<T>(),
            _ => None,
        }
    }
}

/// Take the value at `index` out of `values`, discarding the storage of every other element.
#[allow(clippy::boxed_local)]
fn take_nth_discarding_rest(values: B<SVec2<Value>>, index: usize) -> Option<Value> {
    let mut result = None;
    for (i, value) in values.into_iter().enumerate() {
        if i == index {
            debug_assert!(result.is_none());
            result = Some(value);
        } else {
            value.discard_storage();
        }
    }
    result
}

/// A literal value is a native value that can be hashed.
#[derive(Debug, Clone, PartialEq, Eq, EnumAsInner, Hash)]
pub enum LiteralValue {
    Native(B<dyn LiteralNativeValue>),
    Tuple(B<SVec2<LiteralValue>>),
}

impl LiteralValue {
    pub fn new_native<T: LiteralNativeValue + 'static>(value: T) -> Self {
        Self::Native(b(value))
    }

    pub fn new_tuple(values: impl Into<SVec2<LiteralValue>>) -> Self {
        Self::Tuple(b(values.into()))
    }

    pub fn into_value(self) -> Value {
        use LiteralValue::*;
        match self {
            Native(value) => Value::native_box(value.into_native_value()),
            Tuple(args) => Value::tuple(args.into_iter().map(Self::into_value).collect::<Vec<_>>()),
        }
    }

    pub fn as_primitive_ty<T: 'static>(&self) -> Option<&T> {
        match self {
            Self::Native(value) => LiteralNativeValue::as_any(value.as_ref()).downcast_ref::<T>(),
            Self::Tuple(_) => None,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::{LocalFunctionId, LocalImplId, LocalSubscriptId, ModuleId, id::Id};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use ustr::ustr;

    static RUST_DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[derive(Debug)]
    struct RustDropTracked;

    impl Drop for RustDropTracked {
        fn drop(&mut self) {
            RUST_DROP_COUNT.fetch_add(1, Ordering::Relaxed);
        }
    }

    impl NativeDisplay for RustDropTracked {
        fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "<rust-drop-tracked>")
        }
    }

    fn reset_rust_drop_count() {
        RUST_DROP_COUNT.store(0, Ordering::Relaxed);
    }

    fn rust_drop_count() -> usize {
        RUST_DROP_COUNT.load(Ordering::Relaxed)
    }

    #[test]
    fn value_as_primitive_ty_mut() {
        let v = 42isize;
        let mut a = Value::native(v);
        let mut b = v;
        assert_eq!(a.as_primitive_ty_mut::<isize>(), Some(&mut b));
        a.discard_storage();
    }

    #[test]
    #[cfg(not(miri))]
    fn rust_drop_does_not_own_value_payload_lifetime() {
        reset_rust_drop_count();
        {
            let _value = Value::native(RustDropTracked);
        }
        assert_eq!(rust_drop_count(), 0);
    }

    #[test]
    fn discard_storage_recursively_reclaims_runtime_payloads() {
        reset_rust_drop_count();
        let dictionary = TraitDictionaryId {
            module_id: ModuleId::from_index(0),
            impl_id: LocalImplId::from_index(0),
        };
        let value = Value::tuple([
            Value::native(RustDropTracked),
            Value::raw_variant(ustr("Payload"), Value::native(RustDropTracked)),
            Value::function_value(FunctionValue::closure(
                FunctionId::new(ModuleId::from_index(0), LocalFunctionId::from_index(0)),
                Vec::new(),
                vec![Value::native(RustDropTracked)],
                Some(dictionary),
            )),
            Value::subscript(SubscriptId::new(
                ModuleId::from_index(0),
                crate::module::LocalSubscriptId::from_index(0),
            )),
        ]);

        assert_eq!(rust_drop_count(), 0);
        value.discard_storage();
        assert_eq!(rust_drop_count(), 3);
    }

    #[test]
    fn subscript_value_hidden_args_can_hold_nested_subscript_evidence() {
        let outer = SubscriptId::new(ModuleId::from_index(0), LocalSubscriptId::from_index(0));
        let inner = SubscriptId::new(ModuleId::from_index(0), LocalSubscriptId::from_index(1));
        let value = SubscriptValue {
            subscript: outer,
            hidden_args: vec![HiddenEvidenceArgValue::Subscript(b(SubscriptValue::bare(
                inner,
            )))],
        };

        let cloned = value.clone();
        assert_eq!(cloned, value);

        Value::subscript_value(value).discard_storage();
        Value::subscript_value(cloned).discard_storage();
    }

    #[test]
    fn owned_projection_discards_unselected_tuple_storage() {
        reset_rust_drop_count();
        let value = Value::tuple([
            Value::native(RustDropTracked),
            Value::native(RustDropTracked),
            Value::native(RustDropTracked),
        ]);

        let selected = value.into_projected_value(1).unwrap();

        assert_eq!(rust_drop_count(), 2);
        selected.discard_storage();
        assert_eq!(rust_drop_count(), 3);
    }
}
