// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Boxed Buffer storage and intrinsics shared by the HIR and MIR interpreters.

use std::mem;

use super::{EvalCtx, EvalResult, PlaceResult, RuntimeError, ValOrMut, ValOrMutArgs};
use crate::{
    compiler::error::SourceFailureKind,
    hir::{
        function::extract_trivial_native_input,
        value::{NativeValueType, Value},
    },
    place::Place,
    primitive::{BufferPrimitive, INVALID_BUFFER_CLONE},
    std::string::String as FerliumString,
};

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

    pub(crate) fn slots_mut(&mut self) -> &mut [Value] {
        &mut self.slots
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

pub(super) fn eval_buffer_primitive(
    primitive: BufferPrimitive,
    args: Vec<ValOrMut>,
    ctx: &mut EvalCtx,
) -> EvalResult {
    let mut args = ValOrMutArgs::new(args);
    match primitive {
        BufferPrimitive::Slot => buffer_slot(args, ctx),
        BufferPrimitive::WithCapacity => {
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
            Ok(Value::native(Buffer::with_capacity(
                capacity.max(0) as usize
            )))
        }
        BufferPrimitive::MoveInto => buffer_move_into(args, ctx),
        BufferPrimitive::Move => buffer_move(args, ctx),
        BufferPrimitive::Take => buffer_take(args, ctx),
        BufferPrimitive::Equal => Ok(Value::native(false)),
        BufferPrimitive::ToString => Ok(Value::native(FerliumString::new("<buffer>"))),
        BufferPrimitive::Hash => Ok(Value::unit()),
        BufferPrimitive::Drop => {
            let target = place_from_arg(args.next().unwrap())?;
            let target = target.boxed_mut(ctx).map_err(RuntimeError::new_native)?;
            debug_assert!(
                target.as_primitive_ty::<Buffer>().is_some_and(|buffer| {
                    buffer
                        .slots
                        .iter()
                        .all(|slot| matches!(slot, Value::Uninit))
                }),
                "Buffer drop requires all elements to have been consumed"
            );
            let old = mem::replace(target, Value::uninit());
            old.discard_storage();
            Ok(Value::unit())
        }
        BufferPrimitive::Clone => panic!("{INVALID_BUFFER_CLONE}"),
    }
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
    place.push_index(index);
    Ok(place)
}

fn int_from_arg(arg: ValOrMut, ctx: &mut EvalCtx<'_>, expected: &'static str) -> isize {
    let result = extract_trivial_native_input::<isize>(&arg, ctx).expect(expected);
    arg.discard_storage();
    result
}

fn buffer_slot(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalResult {
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
    Ok(Value::native(PlaceResult::new(buffer_slot_place(
        buffer, index,
    )?)))
}

fn buffer_move_into(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalResult {
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
    source.push_index(source_index);
    target.push_index(target_index);
    let value = {
        let source = source.boxed_mut(ctx).map_err(RuntimeError::new_native)?;
        mem::replace(source, Value::uninit())
    };
    let target = target.boxed_mut(ctx).map_err(RuntimeError::new_native)?;
    assert!(
        matches!(target, Value::Uninit),
        "buffer_move_into target slot must be uninitialized"
    );
    *target = value;
    Ok(Value::unit())
}

fn buffer_move(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalResult {
    let source = place_from_arg(args.next().unwrap())?;
    let target = place_from_arg(args.next().unwrap())?;
    let value = {
        let source = source.boxed_mut(ctx).map_err(RuntimeError::new_native)?;
        mem::replace(source, Value::native(Buffer::with_capacity(0)))
    };
    let target = target.boxed_mut(ctx).map_err(RuntimeError::new_native)?;
    let old = mem::replace(target, value);
    old.discard_storage();
    Ok(Value::unit())
}

fn buffer_take(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalResult {
    let mut source = place_from_arg(args.next().unwrap())?;
    let index = int_from_arg(args.next().unwrap(), ctx, "buffer index should be an int");
    let _element_size = int_from_arg(
        args.next().unwrap(),
        ctx,
        "buffer element size should be an int",
    );
    source.push_index(index);
    let value = {
        let source = source.boxed_mut(ctx).map_err(RuntimeError::new_native)?;
        mem::replace(source, Value::uninit())
    };
    Ok(value)
}

#[cfg(test)]
mod reclamation_tests {
    use super::*;
    use crate::{CompilerSession, Location, module::FunctionId, std::STD_MODULE_ID};
    use std::{cell::Cell, rc::Rc};
    use ustr::ustr;

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
    fn taking_an_element_preserves_it_across_explicit_buffer_drop() {
        let session = CompilerSession::new();
        let mut ctx = EvalCtx::new(STD_MODULE_ID, &session);
        let count = Rc::new(Cell::new(0));
        ctx.environment
            .push(ValOrMut::Val(Value::native(Buffer::from_vec(vec![
                Value::native(DropTracked(count.clone())),
            ]))));
        let function = |name| {
            FunctionId::new(
                STD_MODULE_ID,
                session
                    .std_module()
                    .get_local_function_id(ustr(name))
                    .unwrap(),
            )
        };
        let taken = ctx
            .call_native(
                function("buffer_take"),
                Vec::new(),
                vec![
                    ValOrMut::Mut(Place::boxed(0)),
                    ValOrMut::from_primitive(0isize),
                    ValOrMut::from_primitive(mem::size_of::<DropTracked>() as isize),
                ],
                Location::new_synthesized(),
            )
            .unwrap();
        let result = ctx
            .call_native(
                function("buffer_drop"),
                Vec::new(),
                vec![ValOrMut::Mut(Place::boxed(0))],
                Location::new_synthesized(),
            )
            .unwrap();
        result.discard_storage();
        assert!(
            matches!(ctx.environment[0], ValOrMut::Val(Value::Uninit)),
            "buffer drop must release storage and clear its owning slot immediately"
        );
        assert_eq!(count.get(), 0, "the taken element is independently owned");
        taken.discard_storage();
        assert_eq!(count.get(), 1);
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
