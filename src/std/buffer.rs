// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::{fmt, mem};

use ustr::ustr;

use crate::{
    Location,
    compiler::error::RuntimeErrorKind,
    eval::{
        EvalControlFlowResult, EvalCtx, Place, PlaceResult, RuntimeError, ValOrMut, ValOrMutArgs,
        call_value_clone_to_target, call_value_drop_for_temp, cont, try_dictionary_from_place,
    },
    hir::{
        function::{
            BinaryNativeFnRMN, BinaryNativeFnRRN, BinaryNativeFnRWN, Callable, ContextNativeFn,
            Function, FunctionDefinition, ResolvedArgPassing, ResolvedValueArgPassing,
            SharedRefTempCleanup, UnaryNativeFnMN, UnaryNativeFnRN,
        },
        value::{NativeDisplay, Value},
    },
    module::{BlanketTraitImplSubKey, Module, ModuleFunction, TraitDictionaryId},
    types::{
        effects::no_effects,
        r#type::{FnType, Type, bare_native_type},
        type_scheme::{PubTypeConstraint, TypeScheme},
    },
};

const OWNED: ResolvedArgPassing = ResolvedArgPassing::Value(ResolvedValueArgPassing::Owned);
const SHARED_REF: ResolvedArgPassing =
    ResolvedArgPassing::Value(ResolvedValueArgPassing::SharedRef {
        temp_cleanup: SharedRefTempCleanup::None,
    });
const MUTABLE_REF: ResolvedArgPassing = ResolvedArgPassing::MutableRef;

use super::value::{VALUE_TRAIT, native_layout_associated_consts};

/// Fixed-size typed storage block used by the Ferlium `Array<T>` implementation.
#[derive(Debug)]
pub struct Buffer {
    slots: Vec<Value>,
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

impl NativeDisplay for Buffer {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<buffer:{}>", self.slots.len())
    }
}

fn buffer_type(element_ty: Type) -> Type {
    Type::native::<Buffer>([element_ty])
}

fn buffer_eq(_: &Buffer, _: &Buffer) -> bool {
    false
}

fn buffer_to_string(_: &Buffer) -> super::string::String {
    super::string::String::new("<buffer>")
}

fn buffer_hash(_: &Buffer, _: &mut super::hash::Hasher) {}

fn buffer_clone(_: &Buffer, _: &mut Value) {
    panic!("Buffer values are std-internal and cannot be cloned directly")
}

fn buffer_drop(_: &mut Buffer) {}

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
    ModuleFunction::new(
        FunctionDefinition::new(
            TypeScheme::new_infer_quantifiers_with_constraints(ty, constraints.into()),
            arg_names.into_iter().map(ustr::Ustr::from).collect(),
            Some(String::from(doc)),
        ),
        Box::new(code),
        None,
        Vec::new(),
    )
}

fn dictionary_from_arg(
    arg: ValOrMut,
    ctx: &mut EvalCtx<'_>,
) -> Result<TraitDictionaryId, RuntimeError> {
    match arg {
        ValOrMut::Dictionary(dictionary) => Ok(dictionary),
        ValOrMut::Mut(place) => try_dictionary_from_place(&place, ctx).ok_or_else(|| {
            RuntimeError::new_native(RuntimeErrorKind::InvalidArgument("dictionary".into()))
        }),
        ValOrMut::Val(value) => {
            value.discard_storage();
            Err(RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(
                "dictionary".into(),
            )))
        }
        ValOrMut::Ref(_) => Err(RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(
            "dictionary".into(),
        ))),
    }
}

fn place_from_arg(arg: ValOrMut) -> Result<Place, RuntimeError> {
    match arg {
        ValOrMut::Mut(place) => Ok(place),
        ValOrMut::Val(value) => {
            value.discard_storage();
            Err(RuntimeError::new_native(RuntimeErrorKind::InvalidArgument(
                "buffer".into(),
            )))
        }
        ValOrMut::Dictionary(_) | ValOrMut::Ref(_) => Err(RuntimeError::new_native(
            RuntimeErrorKind::InvalidArgument("buffer".into()),
        )),
    }
}

fn buffer_slot_place(buffer: ValOrMut, index: isize) -> Result<Place, RuntimeError> {
    let mut place = place_from_arg(buffer)?;
    place.path.push(index);
    Ok(place)
}

fn buffer_slot(mut args: ValOrMutArgs, _ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let buffer = args.next().unwrap();
    let index = args
        .next()
        .unwrap()
        .into_primitive::<isize>()
        .expect("buffer slot index should be an int");
    cont(Value::native(PlaceResult::new(buffer_slot_place(
        buffer, index,
    )?)))
}

fn buffer_slot_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    let ty = FnType::new_mut_resolved(
        [(buffer_type(gen0), false), (super::math::int_type(), false)],
        gen0,
        no_effects(),
    );
    ModuleFunction::new(
        FunctionDefinition::new_with_generic_params_and_attributes(
            TypeScheme::new_infer_quantifiers(ty),
            Vec::new(),
            vec![ustr("buffer"), ustr("index")],
            Some(String::from("Returns the place for a buffer slot.")),
            Vec::new(),
            true,
        ),
        Box::new(ContextNativeFn::new(
            "buffer_slot",
            &[MUTABLE_REF, OWNED],
            buffer_slot,
        )),
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
        FnType::new_by_val([super::math::int_type()], buffer_type(gen0), no_effects()),
        [],
        ["capacity"],
        "Creates fixed-size uninitialized storage.",
        ContextNativeFn::new(
            "buffer_with_capacity",
            &[OWNED],
            |mut args: ValOrMutArgs, _ctx: &mut EvalCtx| {
                let capacity = args
                    .next()
                    .unwrap()
                    .into_primitive::<isize>()
                    .expect("buffer capacity should be an int");
                cont(Value::native(buffer_with_capacity(capacity)))
            },
        ),
    )
}

fn buffer_clone_value_into(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
    let source = args.next().unwrap();
    let target = args.next().unwrap();
    let index = args
        .next()
        .unwrap()
        .into_primitive::<isize>()
        .expect("buffer target index should be an int");
    let target = buffer_slot_place(target, index)?;
    call_value_clone_to_target(ctx, dictionary, source, target, Location::new_synthesized())
}

fn buffer_clone_value_into_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    native_function(
        FnType::new_mut_resolved(
            [
                (gen0, false),
                (buffer_type(gen0), true),
                (super::math::int_type(), false),
            ],
            Type::unit(),
            no_effects(),
        ),
        value_constraint(gen0),
        ["source", "target", "target_index"],
        "Clones a value into a buffer slot.",
        ContextNativeFn::new(
            "buffer_clone_value_into",
            &[SHARED_REF, SHARED_REF, MUTABLE_REF, OWNED],
            buffer_clone_value_into,
        ),
    )
}

fn buffer_clone_into(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
    let source = args.next().unwrap();
    let source_index = args
        .next()
        .unwrap()
        .into_primitive::<isize>()
        .expect("buffer source index should be an int");
    let target = args.next().unwrap();
    let target_index = args
        .next()
        .unwrap()
        .into_primitive::<isize>()
        .expect("buffer target index should be an int");
    let source = buffer_slot_place(source, source_index)?;
    let target = buffer_slot_place(target, target_index)?;
    call_value_clone_to_target(
        ctx,
        dictionary,
        ValOrMut::Mut(source),
        target,
        Location::new_synthesized(),
    )
}

fn buffer_clone_into_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    native_function(
        FnType::new_mut_resolved(
            [
                (buffer_type(gen0), false),
                (super::math::int_type(), false),
                (buffer_type(gen0), true),
                (super::math::int_type(), false),
            ],
            Type::unit(),
            no_effects(),
        ),
        value_constraint(gen0),
        ["source", "source_index", "target", "target_index"],
        "Clones a buffer slot into another buffer slot.",
        ContextNativeFn::new(
            "buffer_clone_into",
            &[SHARED_REF, SHARED_REF, OWNED, MUTABLE_REF, OWNED],
            buffer_clone_into,
        ),
    )
}

fn buffer_move_into(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let mut source = place_from_arg(args.next().unwrap())?;
    let source_index = args
        .next()
        .unwrap()
        .into_primitive::<isize>()
        .expect("buffer source index should be an int");
    let mut target = place_from_arg(args.next().unwrap())?;
    let target_index = args
        .next()
        .unwrap()
        .into_primitive::<isize>()
        .expect("buffer target index should be an int");
    source.path.push(source_index);
    target.path.push(target_index);
    let value = {
        let source = source.target_mut(ctx).map_err(RuntimeError::new_native)?;
        mem::replace(source, Value::uninit())
    };
    let target = target.target_mut(ctx).map_err(RuntimeError::new_native)?;
    let old = mem::replace(target, value);
    old.discard_storage();
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
            ],
            Type::unit(),
            no_effects(),
        ),
        [],
        ["source", "source_index", "target", "target_index"],
        "Moves a buffer slot into another buffer slot.",
        ContextNativeFn::new(
            "buffer_move_into",
            &[MUTABLE_REF, OWNED, MUTABLE_REF, OWNED],
            buffer_move_into,
        ),
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
        ContextNativeFn::new("buffer_move", &[MUTABLE_REF, MUTABLE_REF], buffer_move),
    )
}

fn buffer_take(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let mut source = place_from_arg(args.next().unwrap())?;
    let index = args
        .next()
        .unwrap()
        .into_primitive::<isize>()
        .expect("buffer index should be an int");
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
            [(buffer_type(gen0), true), (super::math::int_type(), false)],
            gen0,
            no_effects(),
        ),
        [],
        ["source", "index"],
        "Moves a value out of a buffer slot.",
        ContextNativeFn::new("buffer_take", &[MUTABLE_REF, OWNED], buffer_take),
    )
}

fn buffer_drop_at(mut args: ValOrMutArgs, ctx: &mut EvalCtx) -> EvalControlFlowResult {
    let dictionary = dictionary_from_arg(args.next().unwrap(), ctx)?;
    let target = args.next().unwrap();
    let index = args
        .next()
        .unwrap()
        .into_primitive::<isize>()
        .expect("buffer drop index should be an int");
    let target = buffer_slot_place(target, index)?;
    call_value_drop_for_temp(
        ctx,
        dictionary,
        ValOrMut::Mut(target),
        Location::new_synthesized(),
    )
}

fn buffer_drop_at_descr() -> ModuleFunction {
    let gen0 = Type::variable_id(0);
    native_function(
        FnType::new_mut_resolved(
            [(buffer_type(gen0), true), (super::math::int_type(), false)],
            Type::unit(),
            no_effects(),
        ),
        value_constraint(gen0),
        ["target", "index"],
        "Drops a value stored in a buffer slot.",
        ContextNativeFn::new(
            "buffer_drop_at",
            &[SHARED_REF, MUTABLE_REF, OWNED],
            buffer_drop_at,
        ),
    )
}

pub fn add_to_module(to: &mut Module) {
    to.add_unsafe_bare_native_type_alias_str("Buffer", bare_native_type::<Buffer>());
    let gen0 = Type::variable_id(0);
    to.add_blanket_impl_no_locals(
        VALUE_TRAIT.clone(),
        BlanketTraitImplSubKey {
            input_tys: vec![buffer_type(gen0)],
            ty_var_count: 1,
            constraints: vec![],
        },
        [],
        native_layout_associated_consts::<Buffer>(),
        [
            Box::new(BinaryNativeFnRRN::new(buffer_eq)) as Function,
            Box::new(UnaryNativeFnRN::new(buffer_to_string)) as Function,
            Box::new(BinaryNativeFnRMN::new(buffer_hash)) as Function,
            Box::new(BinaryNativeFnRWN::new(buffer_clone)) as Function,
            Box::new(UnaryNativeFnMN::new(buffer_drop)) as Function,
        ],
    );
    to.add_private_unsafe_function(ustr("buffer_slot"), buffer_slot_descr());
    to.add_private_unsafe_function(ustr("buffer_with_capacity"), buffer_with_capacity_descr());
    to.add_private_unsafe_function(
        ustr("buffer_clone_value_into"),
        buffer_clone_value_into_descr(),
    );
    to.add_private_unsafe_function(ustr("buffer_clone_into"), buffer_clone_into_descr());
    to.add_private_unsafe_function(ustr("buffer_move"), buffer_move_descr());
    to.add_private_unsafe_function(ustr("buffer_move_into"), buffer_move_into_descr());
    to.add_private_unsafe_function(ustr("buffer_take"), buffer_take_descr());
    to.add_private_unsafe_function(ustr("buffer_drop_at"), buffer_drop_at_descr());
}
