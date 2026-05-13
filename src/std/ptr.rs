// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::fmt;

use ustr::ustr;

use crate::{
    Location,
    compiler::error::RuntimeErrorKind,
    eval::{
        EvalControlFlowResult, EvalCtx, Place, RuntimeError, ValOrMut, ValOrMutArgs,
        call_value_clone_to_target, call_value_drop_for_temp, try_dictionary_from_place,
    },
    format::write_with_separator_and_format_fn,
    hir::{
        function::{ArgPassing, Callable, ContextNativeFn, FunctionDefinition},
        value::NativeDisplay,
    },
    module::{Module, ModuleFunction, TraitDictionaryId},
    types::{
        effects::no_effects,
        r#type::{FnType, Type, TypeKind, bare_native_type},
        type_scheme::{PubTypeConstraint, TypeScheme},
    },
};

use super::value::VALUE_TRAIT;

/// Std-only and unsafe readable pointer to storage containing an initialized `A`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ptr(Place);

/// Std-only and unsafe mutable pointer to storage for `A`, possibly uninitialized.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MutPtr(Place);

impl Ptr {
    pub(crate) fn new(place: Place) -> Self {
        Self(place)
    }

    fn into_place(self) -> Place {
        self.0
    }
}

impl MutPtr {
    pub(crate) fn new(place: Place) -> Self {
        Self(place)
    }

    fn into_place(self) -> Place {
        self.0
    }
}

fn fmt_place(kind: &str, place: &Place, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "<{kind}:{}/", place.target)?;
    write_with_separator_and_format_fn(place.path.iter(), ".", |index, f| write!(f, "{index}"), f)?;
    write!(f, ">")
}

impl NativeDisplay for Ptr {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_place("ptr", &self.0, f)
    }
}

impl NativeDisplay for MutPtr {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_place("mut", &self.0, f)
    }
}

pub(crate) fn ptr_type(element_ty: Type) -> Type {
    Type::native::<Ptr>([element_ty])
}

pub(crate) fn mut_ptr_type(element_ty: Type) -> Type {
    Type::native::<MutPtr>([element_ty])
}

/// Whether `ty` is one of the std-internal pointer types (`Ptr<T>` or `MutPtr<T>`).
pub(crate) fn is_pointer_type(ty: Type) -> bool {
    let ty_data = ty.data();
    let TypeKind::Native(native) = &*ty_data else {
        return false;
    };
    native.bare_ty == bare_native_type::<Ptr>() || native.bare_ty == bare_native_type::<MutPtr>()
}

pub(crate) fn place_from_arg(arg: ValOrMut) -> Result<Place, RuntimeError> {
    match arg {
        ValOrMut::Mut(place) => Ok(place),
        ValOrMut::Val(value) => {
            value.discard_storage();
            Err(RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(
                ustr("place"),
            )))
        }
        ValOrMut::Dictionary(_) | ValOrMut::Ref(_) => Err(RuntimeError::new_native(
            RuntimeErrorKind::InvalidArgument(ustr("place")),
        )),
    }
}

fn value_constraint(ty: Type) -> Vec<PubTypeConstraint> {
    vec![PubTypeConstraint::new_have_trait(
        VALUE_TRAIT.clone(),
        vec![ty],
        vec![],
        Location::new_synthesized(),
    )]
}

fn native_function(
    ty: FnType,
    constraints: impl Into<Vec<PubTypeConstraint>>,
    arg_names: impl IntoIterator<Item = &'static str>,
    doc: &'static str,
    code: impl Callable + Clone + 'static,
) -> ModuleFunction {
    ModuleFunction {
        definition: FunctionDefinition::new(
            TypeScheme::new_infer_quantifiers_with_constraints(ty, constraints.into()),
            arg_names.into_iter().map(ustr::Ustr::from).collect(),
            Some(String::from(doc)),
        ),
        code: Box::new(code),
        spans: None,
        locals: Vec::new(),
    }
}

fn dictionary_from_arg(
    arg: ValOrMut,
    ctx: &mut EvalCtx<'_>,
) -> Result<TraitDictionaryId, RuntimeError> {
    match arg {
        ValOrMut::Dictionary(dictionary) => Ok(dictionary),
        ValOrMut::Mut(place) => try_dictionary_from_place(&place, ctx).ok_or_else(|| {
            RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(ustr("dictionary")))
        }),
        ValOrMut::Val(value) => {
            value.discard_storage();
            Err(RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(
                ustr("dictionary"),
            )))
        }
        ValOrMut::Ref(_) => Err(RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(
            ustr("dictionary"),
        ))),
    }
}

fn clone_value_to_mut_ptr(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
    let source = args.next().unwrap();
    let target = args
        .next()
        .unwrap()
        .into_primitive::<MutPtr>()
        .expect("clone target should be a mutable pointer");
    call_value_clone_to_target(
        ctx,
        dictionary,
        source,
        target.into_place(),
        Location::new_synthesized(),
    )
}

fn clone_value_to_mut_ptr_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    native_function(
        FnType::new_by_val([gen0, mut_ptr_type(gen0)], Type::unit(), no_effects()),
        value_constraint(gen0),
        ["source", "target"],
        "Clones a value into a mutable pointer storage.",
        ContextNativeFn::new(
            "value_clone_to_mut_ptr",
            &[
                ArgPassing::SharedRef,
                ArgPassing::SharedRef,
                ArgPassing::OwnedValue,
            ],
            clone_value_to_mut_ptr,
        ),
    )
}

fn clone_ptr(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
    let source = args
        .next()
        .unwrap()
        .into_primitive::<Ptr>()
        .expect("clone source should be a pointer");
    let target = args
        .next()
        .unwrap()
        .into_primitive::<MutPtr>()
        .expect("clone target should be a mutable pointer");
    call_value_clone_to_target(
        ctx,
        dictionary,
        ValOrMut::Mut(source.into_place()),
        target.into_place(),
        Location::new_synthesized(),
    )
}

fn clone_ptr_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    native_function(
        FnType::new_by_val(
            [ptr_type(gen0), mut_ptr_type(gen0)],
            Type::unit(),
            no_effects(),
        ),
        value_constraint(gen0),
        ["source", "target"],
        "Clones from a pointer into a mutable pointer storage.",
        ContextNativeFn::new(
            "ptr_clone",
            &[
                ArgPassing::SharedRef,
                ArgPassing::OwnedValue,
                ArgPassing::OwnedValue,
            ],
            clone_ptr,
        ),
    )
}

fn drop_ptr(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
    let target = args
        .next()
        .unwrap()
        .into_primitive::<MutPtr>()
        .expect("drop target should be a mutable pointer");
    call_value_drop_for_temp(
        ctx,
        dictionary,
        ValOrMut::Mut(target.into_place()),
        Location::new_synthesized(),
    )
}

fn drop_ptr_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    native_function(
        FnType::new_by_val([mut_ptr_type(gen0)], Type::unit(), no_effects()),
        value_constraint(gen0),
        ["target"],
        "Drops the value stored at a mutable pointer.",
        ContextNativeFn::new(
            "ptr_drop",
            &[ArgPassing::SharedRef, ArgPassing::OwnedValue],
            drop_ptr,
        ),
    )
}

pub fn add_to_module(to: &mut Module) {
    to.add_unsafe_bare_native_type_alias_str("Ptr", bare_native_type::<Ptr>());
    to.add_unsafe_bare_native_type_alias_str("MutPtr", bare_native_type::<MutPtr>());

    to.add_unsafe_function(
        ustr("value_clone_to_mut_ptr"),
        clone_value_to_mut_ptr_descr(),
    );
    to.add_unsafe_function(ustr("ptr_clone"), clone_ptr_descr());
    to.add_unsafe_function(ustr("ptr_drop"), drop_ptr_descr());
}
