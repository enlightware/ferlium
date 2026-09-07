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
    compiler::error::SourceFailureKind,
    containers::b,
    eval::{
        EvalControlFlowResult, EvalCtx, Place, PlaceResult, RuntimeError, ValOrMut, ValOrMutArgs,
        cont,
    },
    hir::{
        function::{
            ArgConvention, Callable, CallableDefinition, Function, extract_trivial_native_input,
        },
        value::{NativeValueType, Value},
    },
    module::{BlanketTraitImplSubKey, Module, ModuleFunction},
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

const LET: ArgConvention = ArgConvention::Let;
const MUTABLE_REF: ArgConvention = ArgConvention::MutableRef;

use super::value::native_layout_associated_consts;

/// Fixed-size typed storage block used by the Ferlium `Array<T>` implementation.
#[derive(Debug)]
pub struct Buffer {
    slots: Vec<Value>,
}

impl NativeValueType for Buffer {}

impl Drop for Buffer {
    fn drop(&mut self) {
        // Normal Array cleanup has already consumed its elements. Poisoning skips that cleanup,
        // so any remaining boxed payloads must be reclaimed here without running Ferlium code.
        // Value contains ManuallyDrop payloads: dropping Vec<Value> alone would leak them.
        for value in self.slots.drain(..) {
            value.discard_storage();
        }
    }
}

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

impl Buffer {
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            slots: (0..capacity).map(|_| Value::uninit()).collect(),
        }
    }

    pub fn from_vec(values: Vec<Value>) -> Self {
        Self { slots: values }
    }

    pub fn capacity(&self) -> usize {
        self.slots.len()
    }

    pub fn get(&self, index: usize) -> Option<&Value> {
        self.slots.get(index)
    }

    pub fn get_signed(&self, index: isize) -> Option<&Value> {
        usize::try_from(index)
            .ok()
            .and_then(|index| self.get(index))
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut Value> {
        self.slots.get_mut(index)
    }

    pub fn get_mut_signed(&mut self, index: isize) -> Option<&mut Value> {
        usize::try_from(index)
            .ok()
            .and_then(|index| self.get_mut(index))
    }

    pub fn take(&mut self, index: usize) -> Option<Value> {
        self.get_mut(index)
            .map(|slot| mem::replace(slot, Value::uninit()))
    }
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

/// Boxed execution of private Buffer operations. These are compiler primitives, not Rust
/// host entries: physical lowering replaces storage operations with MIR instructions.
#[derive(Clone, Copy, Debug)]
enum BufferPrimitive {
    Slot,
    WithCapacity,
    MoveInto,
    Move,
    Take,
    Equal,
    ToString,
    Hash,
    Clone,
    Drop,
}

impl Callable for BufferPrimitive {
    fn call(
        &self,
        args: Vec<ValOrMut>,
        ctx: &mut EvalCtx,
        _: &[crate::module::ELocalDecl],
    ) -> EvalControlFlowResult {
        let mut args = ValOrMutArgs::new(args);
        match self {
            Self::Slot => buffer_slot(args, ctx),
            Self::WithCapacity => {
                let capacity = int_from_arg(
                    args.next().unwrap(),
                    ctx,
                    "buffer capacity should be an int",
                );
                let _size = int_from_arg(
                    args.next().unwrap(),
                    ctx,
                    "buffer element size should be an int",
                );
                let _align = int_from_arg(
                    args.next().unwrap(),
                    ctx,
                    "buffer alignment should be an int",
                );
                cont(Value::native(buffer_with_capacity(capacity)))
            }
            Self::MoveInto => buffer_move_into(args, ctx),
            Self::Move => buffer_move(args, ctx),
            Self::Take => buffer_take(args, ctx),
            Self::Equal => cont(Value::native(false)),
            Self::ToString => cont(Value::native(super::string::String::new("<buffer>"))),
            Self::Hash | Self::Drop => cont(Value::unit()),
            Self::Clone => panic!("Buffer values are std-internal and cannot be cloned directly"),
        }
    }
    fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
        Some(match self {
            Self::Slot | Self::Take => &[MUTABLE_REF, LET, LET],
            Self::WithCapacity => &[LET, LET, LET],
            Self::MoveInto => &[MUTABLE_REF, LET, MUTABLE_REF, LET, LET],
            Self::Move => &[MUTABLE_REF, MUTABLE_REF],
            Self::Equal => &[LET, LET],
            Self::ToString | Self::Clone => &[LET],
            Self::Hash => &[LET, MUTABLE_REF],
            Self::Drop => &[MUTABLE_REF],
        })
    }
    fn format_ind(
        &self,
        f: &mut std::fmt::Formatter,
        _: &[crate::module::ELocalDecl],
        _: &crate::module::ModuleEnv,
        spacing: usize,
        indent: usize,
    ) -> std::fmt::Result {
        write!(
            f,
            "{}{}Buffer::{self:?}",
            "  ".repeat(spacing),
            "⎸ ".repeat(indent)
        )
    }
}

fn native_function(
    ty: FnType,
    constraints: impl Into<Vec<PubTypeConstraint>>,
    arg_names: impl IntoIterator<Item = &'static str>,
    doc: &'static str,
    code: impl Callable + Clone + 'static,
) -> ModuleFunction {
    ModuleFunction::new(
        CallableDefinition::new(
            TypeScheme::new_infer_quantifiers_with_constraints(ty, constraints.into()),
            arg_names.into_iter().map(ustr::Ustr::from).collect(),
            Some(String::from(doc)),
        ),
        Box::new(code),
        None,
        Vec::new(),
    )
}

fn place_from_arg(arg: ValOrMut) -> Result<Place, RuntimeError> {
    match arg {
        ValOrMut::Mut(place) => Ok(place),
        ValOrMut::Val(value) => {
            value.discard_storage();
            Err(RuntimeError::new_native(
                SourceFailureKind::InvalidArgument("buffer".into()),
            ))
        }
        ValOrMut::Dictionary(_) | ValOrMut::Ref(_) => Err(RuntimeError::new_native(
            SourceFailureKind::InvalidArgument("buffer".into()),
        )),
    }
}

fn buffer_slot_place(buffer: ValOrMut, index: isize) -> Result<Place, RuntimeError> {
    let mut place = place_from_arg(buffer)?;
    place.path.push(index);
    Ok(place)
}

fn int_from_arg(arg: ValOrMut, ctx: &mut EvalCtx<'_>, expected: &'static str) -> isize {
    let result = extract_trivial_native_input::<isize>(&arg, ctx).expect(expected);
    arg.discard_storage();
    result
}

fn buffer_slot(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let buffer = args.next().unwrap();
    let index = int_from_arg(
        args.next().unwrap(),
        ctx,
        "buffer slot index should be an int",
    );
    let _element_size = int_from_arg(
        args.next().unwrap(),
        ctx,
        "buffer element size should be an int",
    );
    cont(Value::native(PlaceResult::new(buffer_slot_place(
        buffer, index,
    )?)))
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
    ModuleFunction::new(
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
    )
}

fn buffer_with_capacity(capacity: isize) -> Buffer {
    Buffer::with_capacity(capacity.max(0) as usize)
}

fn buffer_with_capacity_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    native_function(
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

fn buffer_move_into(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let mut source = place_from_arg(args.next().unwrap())?;
    let source_index = int_from_arg(
        args.next().unwrap(),
        ctx,
        "buffer source index should be an int",
    );
    let mut target = place_from_arg(args.next().unwrap())?;
    let target_index = int_from_arg(
        args.next().unwrap(),
        ctx,
        "buffer target index should be an int",
    );
    let _element_size = int_from_arg(
        args.next().unwrap(),
        ctx,
        "buffer element size should be an int",
    );
    source.path.push(source_index);
    target.path.push(target_index);
    let value = {
        let source = source.target_mut(ctx).map_err(RuntimeError::new_native)?;
        mem::replace(source, Value::uninit())
    };
    let target = target.target_mut(ctx).map_err(RuntimeError::new_native)?;
    assert!(
        matches!(target, Value::Uninit),
        "buffer_move_into target slot must be uninitialized"
    );
    *target = value;
    cont(Value::unit())
}

fn buffer_move_into_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    native_function(
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

fn buffer_move(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let source = place_from_arg(args.next().unwrap())?;
    let target = place_from_arg(args.next().unwrap())?;
    let value = {
        let source = source.target_mut(ctx).map_err(RuntimeError::new_native)?;
        mem::replace(source, Value::native(Buffer::with_capacity(0)))
    };
    let target = target.target_mut(ctx).map_err(RuntimeError::new_native)?;
    let old = mem::replace(target, value);
    old.discard_storage();
    cont(Value::unit())
}

fn buffer_move_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    native_function(
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

fn buffer_take(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let mut source = place_from_arg(args.next().unwrap())?;
    let index = int_from_arg(args.next().unwrap(), ctx, "buffer index should be an int");
    let _element_size = int_from_arg(
        args.next().unwrap(),
        ctx,
        "buffer element size should be an int",
    );
    source.path.push(index);
    let value = {
        let source = source.target_mut(ctx).map_err(RuntimeError::new_native)?;
        mem::replace(source, Value::uninit())
    };
    cont(value)
}

fn buffer_take_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    native_function(
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

pub fn add_to_module(to: &mut Module) {
    let value_trait_id = to.expect_std_trait_id_in_current_module(VALUE_TRAIT_NAME);
    let inspect_trait_id = to.expect_std_trait_id_in_current_module(INSPECT_TRAIT_NAME);
    to.add_unsafe_bare_native_type_alias_str("Buffer", buffer_bare_native_type());
    let gen0 = Type::variable_id(0);
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
        [
            Box::new(BufferPrimitive::Equal) as Function,
            Box::new(BufferPrimitive::ToString) as Function,
            Box::new(BufferPrimitive::Hash) as Function,
            Box::new(BufferPrimitive::Clone) as Function,
            Box::new(BufferPrimitive::Drop) as Function,
        ],
    );
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
        [Box::new(BufferPrimitive::ToString) as Function],
    );
    to.add_private_unsafe_addressor_subscript(ustr("buffer_slot"), buffer_slot_descr());
    to.add_private_unsafe_function(ustr("buffer_with_capacity"), buffer_with_capacity_descr());
    to.add_private_unsafe_function(ustr("buffer_move"), buffer_move_descr());
    to.add_private_unsafe_function(ustr("buffer_move_into"), buffer_move_into_descr());
    to.add_private_unsafe_function(ustr("buffer_take"), buffer_take_descr());
}

#[cfg(test)]
mod reclamation_tests {
    use super::*;
    use std::{cell::Cell, rc::Rc};

    #[derive(Debug)]
    struct DropTracked(Rc<Cell<usize>>);
    impl NativeValueType for DropTracked {}
    impl Drop for DropTracked {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn buffer_reclamation_preserves_moved_values_and_skips_cleared_slots() {
        let count = Rc::new(Cell::new(0));
        let mut buffer = Buffer::from_vec(
            (0..3)
                .map(|_| Value::native(DropTracked(count.clone())))
                .collect(),
        );
        let moved = buffer.take(0).unwrap();
        buffer.take(1).unwrap().discard_storage();
        assert_eq!(count.get(), 1);

        drop(buffer);
        assert_eq!(count.get(), 2, "only the remaining live slot is reclaimed");
        assert!(moved.as_primitive_ty::<DropTracked>().is_some());
        moved.discard_storage();
        assert_eq!(
            count.get(),
            3,
            "the moved payload remains independently owned"
        );
        assert_eq!(Rc::strong_count(&count), 1);
    }
}
