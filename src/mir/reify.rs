// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Reification: turning a compile-time [`Value`] back into MIR.
//!
//! This is the other half of the folding pass's contract with compile-time evaluation. The
//! evaluator ([`crate::mir::const_eval`]) answers "what does this call return?" with a runtime
//! value; reification answers "can that value be written down as MIR?", and produces the operand
//! that replaces the call.
//!
//! It is deliberately restricted to values a MIR constant pool can already hold: a `TrivialCopy`
//! native leaf, or a tuple of those (which is also how a record is represented at run time).
//! `doc/mir-ir.md` pins `@cN` to that representation, so anything else — a `String`, a list, a
//! variant, a closure — is refused here and left as a runtime call. Lifting that restriction is a
//! separate piece of work: reifying a non-trivial value needs a way to express it as static data
//! and rebuild it at run time.
//!
//! Refusal is always a normal outcome: it costs an optimization, never a program.
//!
//! Like the evaluator, this has no caller yet — the folding pass that consumes it is a later phase
//! — so its items are exercised only by the tests below and by `const_eval`'s.
#![allow(dead_code)]

use crate::{
    hir::{
        function::literal_of_trivial_copy_native,
        value::{LiteralValue, Value},
    },
    mir::{self, const_eval::NotFoldable, value::Constant},
    module::ModuleEnv,
    types::r#type::Type,
};

/// How a reified compile-time value enters a MIR function.
#[derive(Debug)]
pub(crate) enum Reification {
    /// A typed immediate for the function's constant pool. The fold site adds it with
    /// [`FunctionBuilder::add_constant`](crate::mir::builder::FunctionBuilder::add_constant) and
    /// stores the resulting `@cN` operand into the destination place.
    Constant(Constant),
    /// An operand that needs no constant-pool entry, because MIR can already name the thing
    /// directly.
    Operand(mir::Value),
}

/// Expresses `value`, of instantiated type `ty`, as MIR — or explains why it cannot be.
///
/// Borrows rather than consumes: every reifiable leaf is `Copy`, and the caller owns the value the
/// evaluator handed it in either case (`Value` is `ManuallyDrop`-based, so it must still
/// `discard_storage` what it does not keep).
pub(crate) fn reify(
    value: &Value,
    ty: Type,
    env: &ModuleEnv<'_>,
) -> Result<Reification, NotFoldable> {
    // A function value MIR can name directly needs no constant: `Value::Function` is an operand.
    // This is what will let the folding pass turn an inlined `dict_entry` into a direct call.
    if let Value::Function(function) = value {
        return if function.hidden_args.is_empty() && function.closure_env_len == 0 {
            Ok(Reification::Operand(mir::Value::Function(
                function.function,
            )))
        } else {
            // Captured evidence and captured environments are values in their own right: they need
            // the prototype machinery, not an operand.
            Err(NotFoldable::NotReifiable)
        };
    }

    let representation = freeze(value).ok_or(NotFoldable::NotReifiable)?;
    // The literal tree must *be* the runtime representation of the declared type, which is what a
    // constant-pool entry promises. This is also where a tuple literal is accepted for a record
    // type, the two sharing a runtime representation.
    if !representation.has_representation_type_in(ty, env) {
        return Err(NotFoldable::NotReifiable);
    }
    Ok(Reification::Constant(Constant { ty, representation }))
}

/// Whether [`reify`] would succeed. Reification itself is cheap, so this is a thin wrapper rather
/// than a separate traversal that could disagree with it.
pub(crate) fn is_reifiable(value: &Value, ty: Type, env: &ModuleEnv<'_>) -> bool {
    reify(value, ty, env).is_ok()
}

/// Freezes a runtime value into the immutable literal form a constant pool holds.
///
/// Conservative by construction: only the shapes handled here can be frozen, and every other
/// runtime value — a non-trivial native such as a `String`, a bridged `PlaceResult` place, a
/// variant, a subscript, uninitialized storage — falls through to `None`.
fn freeze(value: &Value) -> Option<LiteralValue> {
    match value {
        Value::Native(_) => literal_of_trivial_copy_native(value),
        Value::Tuple(values) => {
            let members = values
                .iter()
                .map(freeze)
                .collect::<Option<Vec<_>>>()?
                .into_iter()
                .collect::<crate::containers::SVec2<_>>();
            Some(LiteralValue::new_tuple(members))
        }
        // `Uninit` never reaches MIR, a subscript is evidence rather than data, and a function
        // value is handled by `reify` before it gets here.
        Value::Uninit | Value::Variant(..) | Value::Subscript(_) | Value::Function(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, Location,
        eval::PlaceResult,
        format::FormatWith,
        hir::value::{FunctionValue, HiddenEvidenceArgValue},
        mir::{Operation, builder::FunctionBuilder, terminator::Terminator},
        module::{FunctionId, LocalFunctionId, LocalImplId, ModuleId, TraitDictionaryId, id::Id},
        std::{
            math::{Float, float_type, int_type},
            string::{String as FerliumString, string_type},
        },
        types::r#type::Type,
    };
    use ustr::ustr;

    fn bool_type() -> Type {
        Type::primitive::<bool>()
    }

    fn unit_type() -> Type {
        Type::unit()
    }

    /// The semantic round trip `Value -> Constant -> Value`.
    ///
    /// The second leg is exactly what the interpreter does with a constant operand
    /// (`src/mir/interpreter.rs`, `constant_value`): it clones the representation and calls
    /// `LiteralValue::into_value`. Equality is checked with the literal's own runtime comparison,
    /// since `Value` is not `PartialEq`.
    fn assert_round_trips(value: Value, ty: Type, session: &CompilerSession) {
        let env = session.module_env();
        let reified = match reify(&value, ty, &env) {
            Ok(Reification::Constant(constant)) => constant,
            Ok(Reification::Operand(operand)) => panic!("expected a constant, got {operand}"),
            Err(reason) => panic!("{ty:?} must be reifiable, got {reason:?}"),
        };
        assert_eq!(reified.ty, ty);

        let materialized = reified.representation.clone().into_value();
        assert_eq!(
            reified
                .representation
                .try_matches_runtime_value(&materialized),
            Ok(true),
            "a constant must materialize back into the value it was frozen from"
        );
        assert_eq!(
            reified.representation.try_matches_runtime_value(&value),
            Ok(true)
        );
        materialized.discard_storage();
        value.discard_storage();

        // And the constant is accepted in a real function body: `finish` runs the full MIR verifier
        // in test builds.
        let span = Location::new_synthesized();
        let mut builder = FunctionBuilder::new("materialize".into(), Default::default());
        let ret = mir::Value::Parameter(builder.add_parameter(ty, mir::ParameterKind::Return));
        let constant = builder.add_constant(reified.ty, reified.representation, &env);
        let block = builder.add_block();
        builder.append_operation(
            block,
            Operation::store(span, mir::Value::Constant(constant), ret),
        );
        builder.set_terminator(block, Terminator::ret(span));
        let func = builder.finish(env);
        assert!(
            func.format_with(&env).to_string().contains("store @c0"),
            "the reified constant must be the stored operand"
        );
    }

    #[test]
    fn primitives_round_trip() {
        let session = CompilerSession::new();
        assert_round_trips(Value::unit(), unit_type(), &session);
        assert_round_trips(Value::native(true), bool_type(), &session);
        assert_round_trips(Value::native(-7isize), int_type(), &session);
        assert_round_trips(
            Value::native(Float::new_saturating(1.5)),
            float_type(),
            &session,
        );
    }

    #[test]
    fn a_tuple_of_primitives_round_trips() {
        let session = CompilerSession::new();
        assert_round_trips(
            Value::tuple(vec![Value::native(1isize), Value::native(false)]),
            Type::tuple(vec![int_type(), bool_type()]),
            &session,
        );
    }

    /// A record shares the tuple representation at run time, so it reifies through the same path;
    /// the representation check against the declared type is what keeps that sound.
    #[test]
    fn a_record_of_primitives_round_trips() {
        let session = CompilerSession::new();
        assert_round_trips(
            Value::tuple(vec![Value::native(1isize), Value::native(2isize)]),
            Type::record(vec![(ustr("a"), int_type()), (ustr("b"), int_type())]),
            &session,
        );
    }

    /// A value whose type is not its representation is refused rather than mis-typed into the pool.
    #[test]
    fn a_mismatched_representation_is_refused() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let value = Value::native(1isize);
        assert_eq!(
            reify(&value, bool_type(), &env).err(),
            Some(NotFoldable::NotReifiable)
        );
        value.discard_storage();
    }

    /// Everything Phase 5 owns, plus the shapes that must never be reified at all.
    #[test]
    fn non_trivial_values_are_refused() {
        let session = CompilerSession::new();
        let env = session.module_env();

        let mut refused: Vec<(&str, Value, Type)> = vec![
            (
                "string",
                Value::native(FerliumString::from("ab".to_string())),
                string_type(),
            ),
            (
                "variant",
                Value::tuple_variant(crate::ustr("Some"), vec![Value::native(1isize)]),
                int_type(),
            ),
            (
                "tuple with a non-trivial member",
                Value::tuple(vec![
                    Value::native(1isize),
                    Value::native(FerliumString::from("ab".to_string())),
                ]),
                Type::tuple(vec![int_type(), string_type()]),
            ),
            // A place is frame-relative: the interpreter bridges one through an ordinary value cell
            // as a `PlaceResult` native, and freezing it would outlive the frame it points into.
            (
                "bridged place",
                Value::native(PlaceResult::new(crate::eval::Place {
                    root: 0,
                    path: vec![],
                })),
                int_type(),
            ),
            ("uninitialized", Value::uninit(), int_type()),
        ];

        let function = FunctionId {
            module: ModuleId::new(0),
            function: LocalFunctionId::from_index(0),
        };
        let dictionary = TraitDictionaryId {
            module_id: ModuleId::new(0),
            impl_id: LocalImplId::from_index(0),
        };
        refused.push((
            "closure with captures",
            Value::function_value(FunctionValue::closure(
                function,
                vec![],
                vec![Value::native(1isize)],
                Some(dictionary),
            )),
            int_type(),
        ));
        refused.push((
            "function carrying hidden evidence",
            Value::function_value(FunctionValue::closure(
                function,
                vec![HiddenEvidenceArgValue::TraitDictionary(dictionary)],
                vec![],
                None,
            )),
            int_type(),
        ));

        for (name, value, ty) in refused {
            assert_eq!(
                reify(&value, ty, &env).err(),
                Some(NotFoldable::NotReifiable),
                "{name} must not be reifiable"
            );
            assert!(!is_reifiable(&value, ty, &env));
            value.discard_storage();
        }
    }

    /// A bare function value needs no constant pool entry.
    #[test]
    fn a_bare_function_reifies_as_an_operand() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let id = FunctionId {
            module: ModuleId::new(0),
            function: LocalFunctionId::from_index(3),
        };
        let value = Value::function(id);
        match reify(&value, int_type(), &env) {
            Ok(Reification::Operand(mir::Value::Function(reified))) => assert_eq!(reified, id),
            other => panic!("a bare function must reify as a function operand, got {other:?}"),
        }
        value.discard_storage();
    }
}
