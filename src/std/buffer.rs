// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{any::TypeId, mem};

use ustr::ustr;

use crate::{
    containers::b,
    hir::function::{CallableDefinition, Function},
    module::{BlanketTraitImplSubKey, CallableOrigin, Module, ModuleFunction, TraitId},
    primitive::BufferPrimitive,
    std::core_traits_names::{INSPECT_TRAIT_NAME, VALUE_TRAIT_NAME},
    types::{
        effects::no_effects,
        r#type::{
            BareNativeType, BareNativeTypeB, CallResultConvention, FnArgType, FnType, NativeType,
            Type, TypeKind,
        },
        type_scheme::{PubTypeConstraint, TypeScheme},
    },
};

/// Boxed interpreter representation, re-exported for existing embedders.
pub use crate::eval::buffer::Buffer;
#[cfg(test)]
use crate::module::{LocalFunctionId, id::Id};

use super::{STD_MODULE_ID, value::native_layout_associated_consts};

/// The compiled representation of a `Buffer<T>`: one owning pointer to the element storage.
///
/// This is the single source of truth for the compiled Buffer layout. Both the ABI identity
/// ([`BufferBareNativeType`]) and the `Value` associated constants installed in [`add_to_module`]
/// derive their size and alignment from it, so the two cannot drift apart.
type BufferRepr = usize;

/// The compiler ABI identity of Buffer is deliberately separate from its boxed interpreter
/// representation. Compiled Buffer values contain one owning target pointer.
#[derive(Clone, PartialEq, Eq)]
struct BufferBareNativeType;

impl BareNativeType for BufferBareNativeType {
    /// Reported where no module alias is in scope, so it names Buffer itself rather than the
    /// Rust type carrying its ABI identity.
    fn type_name(&self) -> &'static str {
        "ferlium::std::buffer::Buffer"
    }

    fn value_size(&self) -> usize {
        mem::size_of::<BufferRepr>()
    }

    fn value_align(&self) -> usize {
        mem::align_of::<BufferRepr>()
    }
}

pub(crate) fn buffer_bare_native_type() -> BareNativeTypeB {
    b(BufferBareNativeType)
}

pub(crate) fn buffer_type(element_ty: Type) -> Type {
    Type::native_type(NativeType {
        bare_ty: buffer_bare_native_type(),
        arguments: vec![element_ty],
    })
}

/// The element type of the private compiled Buffer representation.
pub(crate) fn buffer_element_type(ty: Type) -> Option<Type> {
    let data = ty.data();
    let TypeKind::Native(native) = &*data else {
        return None;
    };
    if BareNativeType::type_id(native.bare_ty.as_ref()) == TypeId::of::<BufferBareNativeType>()
        && native.arguments.len() == 1
    {
        Some(native.arguments[0])
    } else {
        None
    }
}

fn primitive_function(
    ty: FnType,
    constraints: impl Into<Vec<PubTypeConstraint>>,
    arg_names: impl IntoIterator<Item = &'static str>,
    doc: &'static str,
    primitive: BufferPrimitive,
) -> ModuleFunction {
    let mut function = ModuleFunction::new(
        CallableDefinition::new(
            TypeScheme::new_infer_quantifiers_with_constraints(ty, constraints.into()),
            arg_names.into_iter().map(ustr::Ustr::from).collect(),
            Some(String::from(doc)),
        ),
        Box::new(primitive),
        None,
        Vec::new(),
    );
    function.origin = CallableOrigin::BufferPrimitive(primitive);
    function
}

fn buffer_slot_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    let ty = FnType::new(
        vec![
            FnArgType::new_by_val(buffer_type(gen0)),
            FnArgType::new_by_val(super::math::int_type()),
            FnArgType::new_by_val(super::math::int_type()),
        ],
        gen0,
        no_effects(),
    );
    let mut function = ModuleFunction::new(
        CallableDefinition::new_with_generic_params_and_attributes(
            TypeScheme::new_infer_quantifiers(ty),
            Vec::new(),
            Vec::new(),
            vec![ustr("buffer"), ustr("index"), ustr("element_size")],
            Some(String::from("Returns the place for a buffer slot.")),
            Vec::new(),
        )
        .with_result_convention(CallResultConvention::ADDRESSOR_PLACE)
        // The slot is inside the buffer: parameter 0.
        .with_result_rooted_in(0)
        // Computing a slot neither mutates the buffer nor consults external state.
        .with_repeatable_addressor(),
        Box::new(BufferPrimitive::Slot),
        None,
        Vec::new(),
    );
    function.origin = CallableOrigin::BufferPrimitive(BufferPrimitive::Slot);
    function
}

fn buffer_with_capacity_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    primitive_function(
        FnType::new_by_val(
            [
                super::math::int_type(),
                super::math::int_type(),
                super::math::int_type(),
            ],
            buffer_type(gen0),
            no_effects(),
        ),
        [],
        ["capacity", "element_size", "element_align"],
        "Creates fixed-size uninitialized storage.",
        BufferPrimitive::WithCapacity,
    )
}

fn buffer_move_into_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    primitive_function(
        FnType::new_mut_resolved(
            [
                (buffer_type(gen0), true),
                (super::math::int_type(), false),
                (buffer_type(gen0), true),
                (super::math::int_type(), false),
                (super::math::int_type(), false),
            ],
            Type::unit(),
            no_effects(),
        ),
        [],
        [
            "source",
            "source_index",
            "target",
            "target_index",
            "element_size",
        ],
        "Moves a buffer slot into an uninitialized slot of another buffer.",
        BufferPrimitive::MoveInto,
    )
}

fn buffer_move_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    primitive_function(
        FnType::new_mut_resolved(
            [(buffer_type(gen0), true), (buffer_type(gen0), true)],
            Type::unit(),
            no_effects(),
        ),
        [],
        ["source", "target"],
        "Moves a whole buffer into another buffer.",
        BufferPrimitive::Move,
    )
}

fn buffer_take_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    primitive_function(
        FnType::new_mut_resolved(
            [
                (buffer_type(gen0), true),
                (super::math::int_type(), false),
                (super::math::int_type(), false),
            ],
            gen0,
            no_effects(),
        ),
        [],
        ["source", "index", "element_size"],
        "Moves a value out of a buffer slot.",
        BufferPrimitive::Take,
    )
}

/// Assign compiler identities to the methods just registered for the exact Buffer impl.
/// Keep this authority inside std registration rather than exposing it through `Callable`.
fn set_impl_origins(to: &mut Module, trait_id: TraitId, primitives: &[BufferPrimitive]) {
    let implementations = to.get_blanket_impl_by_key(&trait_id).unwrap();
    let (_, &impl_id) = implementations
        .iter()
        .find(|(key, _)| key.input_tys == [buffer_type(Type::variable_id(0))])
        .expect("the Buffer implementation was just registered");
    let methods = to.get_impl_data(impl_id).unwrap().methods.clone();
    assert_eq!(methods.len(), primitives.len());
    for (method, &primitive) in methods.into_iter().zip(primitives) {
        to.get_function_by_id_mut(method).unwrap().origin =
            CallableOrigin::BufferPrimitive(primitive);
    }
}

pub fn add_to_module(to: &mut Module) {
    assert_eq!(
        to.module_id(),
        STD_MODULE_ID,
        "Buffer intrinsics belong to std"
    );
    let value_trait_id = to.expect_std_trait_id_in_current_module(VALUE_TRAIT_NAME);
    let inspect_trait_id = to.expect_std_trait_id_in_current_module(INSPECT_TRAIT_NAME);
    to.add_unsafe_bare_native_type_alias_str("Buffer", buffer_bare_native_type());
    let gen0 = Type::variable_id(0);
    let value_primitives = [
        BufferPrimitive::Equal,
        BufferPrimitive::ToString,
        BufferPrimitive::Hash,
        BufferPrimitive::Clone,
        BufferPrimitive::Drop,
    ];
    to.add_blanket_impl_no_locals(
        value_trait_id,
        BlanketTraitImplSubKey {
            input_tys: vec![buffer_type(gen0)],
            ty_var_count: 1,
            eff_var_count: 0,
            constraints: vec![],
        },
        [],
        // Compiled `Buffer<A>` is one owning pointer. Keep its Ferlium layout independent of the
        // interpreter's `Vec<Value>` representation, and derived from the same `BufferRepr` as the
        // ABI identity so the two agree by construction.
        native_layout_associated_consts::<BufferRepr>(),
        value_primitives.map(|primitive| Box::new(primitive) as Function),
    );
    set_impl_origins(to, value_trait_id, &value_primitives);
    let inspect_primitives = [BufferPrimitive::ToString];
    to.add_blanket_impl_no_locals(
        inspect_trait_id,
        BlanketTraitImplSubKey {
            input_tys: vec![buffer_type(gen0)],
            ty_var_count: 1,
            eff_var_count: 0,
            constraints: vec![],
        },
        [],
        [],
        inspect_primitives.map(|primitive| Box::new(primitive) as Function),
    );
    set_impl_origins(to, inspect_trait_id, &inspect_primitives);
    to.add_private_unsafe_addressor_subscript(ustr("buffer_slot"), buffer_slot_descr());
    to.add_private_unsafe_function(ustr("buffer_with_capacity"), buffer_with_capacity_descr());
    to.add_private_unsafe_function(ustr("buffer_move"), buffer_move_descr());
    to.add_private_unsafe_function(ustr("buffer_move_into"), buffer_move_into_descr());
    to.add_private_unsafe_function(ustr("buffer_take"), buffer_take_descr());
    to.add_private_unsafe_function(
        ustr("buffer_drop"),
        primitive_function(
            FnType::new_mut_resolved([(buffer_type(gen0), true)], Type::unit(), no_effects()),
            [],
            ["target"],
            "Releases a buffer after all its elements have been consumed.",
            BufferPrimitive::Drop,
        ),
    );
}

/// Resolve the intended registrations by their source identities, independently of origin tags.
#[cfg(test)]
pub(crate) fn expected_primitives(to: &Module) -> Vec<(LocalFunctionId, BufferPrimitive)> {
    let mut expected = vec![(
        to.get_subscript(ustr("buffer_slot"))
            .unwrap()
            .mut_member
            .as_ref()
            .unwrap()
            .function,
        BufferPrimitive::Slot,
    )];
    for (name, primitive) in [
        ("buffer_with_capacity", BufferPrimitive::WithCapacity),
        ("buffer_move_into", BufferPrimitive::MoveInto),
        ("buffer_move", BufferPrimitive::Move),
        ("buffer_take", BufferPrimitive::Take),
        ("buffer_drop", BufferPrimitive::Drop),
    ] {
        expected.push((to.get_local_function_id(ustr(name)).unwrap(), primitive));
    }
    for (trait_name, method_name, primitive) in [
        (VALUE_TRAIT_NAME, "eq", BufferPrimitive::Equal),
        (VALUE_TRAIT_NAME, "to_string", BufferPrimitive::ToString),
        (VALUE_TRAIT_NAME, "hash", BufferPrimitive::Hash),
        (VALUE_TRAIT_NAME, "clone", BufferPrimitive::Clone),
        (VALUE_TRAIT_NAME, "drop", BufferPrimitive::Drop),
        (INSPECT_TRAIT_NAME, "inspect", BufferPrimitive::ToString),
    ] {
        let trait_id = to.expect_std_trait_id_in_current_module(trait_name);
        let method = to
            .trait_def(trait_id)
            .method_index(ustr(method_name))
            .unwrap();
        let implementations = to.get_blanket_impl_by_key(&trait_id).unwrap();
        let (_, &impl_id) = implementations
            .iter()
            .find(|(key, _)| key.input_tys == [buffer_type(Type::variable_id(0))])
            .unwrap();
        expected.push((
            to.get_impl_data(impl_id).unwrap().methods[method.as_index()],
            primitive,
        ));
    }
    expected
}
