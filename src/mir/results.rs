// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Zero-sized call results shared by semantic and physical MIR.

use rustc_hash::FxHashMap;

use crate::{
    Location,
    compiler::error::{CompilerLimit, CompilerLimitKind},
    hir::{function::CallableDefinition, value::LiteralValue},
    mir::operation::accepts_value_result,
    module::ModuleEnv,
    std::value::{TypeLayoutEnv, product_member_types},
    types::{
        r#type::{CallImplType, CallResultConvention, Type, TypeKind},
        type_like::TypeLike,
    },
};

/// How MIR transports a call result, independently of its source calling convention.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ResultTransport {
    /// The caller supplies a trailing output place.
    Place,
    /// The call defines a result register.
    Value,
    /// The result is statically zero-sized and needs no transport.
    NoValue,
}

/// Canonical semantic transport, selected from a call's instantiated type.
pub(crate) fn call_result_transport(
    ty: &CallImplType,
    env: &impl TypeLayoutEnv,
) -> ResultTransport {
    if accepts_no_value_result(ty, env) {
        ResultTransport::NoValue
    } else if accepts_value_result(ty) {
        ResultTransport::Value
    } else {
        ResultTransport::Place
    }
}

/// A definition retains its shared output interface while its result or evidence is generic.
pub(crate) fn definition_result_transport(
    definition: &CallableDefinition,
    env: ModuleEnv<'_>,
) -> ResultTransport {
    if definition_returns_no_value(definition, env) {
        ResultTransport::NoValue
    } else if accepts_value_result(&CallImplType::new(
        definition.ty_scheme.ty.clone(),
        definition.return_convention(),
    )) {
        ResultTransport::Value
    } else {
        ResultTransport::Place
    }
}

/// Whether a call's result needs no transport, independently of its callee and fallibility.
pub(crate) fn accepts_no_value_result(ty: &CallImplType, env: &impl TypeLayoutEnv) -> bool {
    matches!(
        ty.result_convention,
        CallResultConvention::Value | CallResultConvention::NoValue
    ) && is_zero_sized_result(ty.fn_ty.ret, env)
}

/// Shared generic and evidence-taking declarations retain their output interface.
fn definition_returns_no_value(definition: &CallableDefinition, env: ModuleEnv<'_>) -> bool {
    let scheme = &definition.ty_scheme;
    definition.return_convention() == CallResultConvention::Value
        && scheme.ty.is_constant()
        && scheme.ty_quantifiers.is_empty()
        && is_zero_sized_result(scheme.ty.ret, &env)
        && scheme.extra_parameters(env).requirements.is_empty()
}

// Compiler limits bound literal expansion; they never select a different calling convention.
pub(crate) const ZERO_SIZED_RESULT_NODES: usize = 4096;
pub(crate) const ZERO_SIZED_RESULT_DEPTH: usize = 64;

#[derive(Clone, Copy)]
struct ResultShape {
    nodes: usize,
    depth: usize,
}

/// Inspect the type graph once, without expanding its potentially exponential literal tree.
fn result_shape(ty: Type, env: &impl TypeLayoutEnv) -> Option<ResultShape> {
    if !ty.is_constant() {
        return None;
    }
    let leaf = ResultShape { nodes: 1, depth: 0 };
    if ty == Type::unit() {
        return Some(leaf);
    }
    if !matches!(
        &*ty.data(),
        TypeKind::Tuple(_) | TypeKind::Record(_) | TypeKind::Named(_)
    ) {
        return None;
    }
    enum Visit {
        Type(Type),
        Product(Type, Vec<Type>),
    }
    let mut pending = vec![Visit::Type(ty)];
    // None marks an active type: revisiting it would require infinite product storage.
    let mut shapes = FxHashMap::<Type, Option<ResultShape>>::default();
    while let Some(visit) = pending.pop() {
        match visit {
            Visit::Type(ty) => {
                if let Some(shape) = shapes.get(&ty) {
                    shape.as_ref()?;
                    continue;
                }
                if ty == Type::unit() {
                    shapes.insert(ty, Some(leaf));
                    continue;
                }
                let members = product_member_types(ty, env)?;
                shapes.insert(ty, None);
                pending.push(Visit::Product(ty, members.clone()));
                pending.extend(members.into_iter().rev().map(Visit::Type));
            }
            Visit::Product(ty, members) => {
                let mut shape = leaf;
                for member in members {
                    let child = shapes[&member]?;
                    shape.nodes = shape.nodes.saturating_add(child.nodes);
                    shape.depth = shape.depth.max(child.depth.saturating_add(1));
                }
                shapes.insert(ty, Some(shape));
            }
        }
    }
    shapes[&ty]
}

/// Whether a result is an inhabited, statically zero-sized Ferlium product.
pub(crate) fn is_zero_sized_result(ty: Type, env: &impl TypeLayoutEnv) -> bool {
    result_shape(ty, env).is_some()
}

/// Check before reconstructing a concrete result or substituting it into executable MIR.
pub(crate) fn check_result_limits(
    ty: Type,
    env: &impl TypeLayoutEnv,
    span: Location,
) -> Result<(), CompilerLimit> {
    let Some(shape) = result_shape(ty, env) else {
        return Ok(());
    };
    for (kind, actual, limit) in [
        (
            CompilerLimitKind::ZeroSizedResultNodes,
            shape.nodes,
            ZERO_SIZED_RESULT_NODES,
        ),
        (
            CompilerLimitKind::ZeroSizedResultDepth,
            shape.depth,
            ZERO_SIZED_RESULT_DEPTH,
        ),
    ] {
        if actual > limit {
            return Err(CompilerLimit {
                kind,
                actual,
                limit,
                span,
            });
        }
    }
    Ok(())
}

/// Build a result literal only after its expansion has been bounded by compiler-limit checking.
pub(crate) fn zero_sized_result(ty: Type, env: &impl TypeLayoutEnv) -> Option<LiteralValue> {
    fn build(ty: Type, env: &impl TypeLayoutEnv) -> LiteralValue {
        if ty == Type::unit() {
            return LiteralValue::new_native(());
        }
        let fields = product_member_types(ty, env)
            .expect("eligible result is a product")
            .into_iter()
            .map(|member| build(member, env))
            .collect::<Vec<_>>();
        LiteralValue::new_tuple(fields)
    }
    is_zero_sized_result(ty, env).then(|| {
        check_result_limits(ty, env, Location::new_synthesized())
            .expect("result reconstruction was checked before MIR emission or substitution");
        build(ty, env)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession,
        types::{
            effects::{PrimitiveEffect, effect, no_effects},
            r#type::FnType,
        },
    };

    #[test]
    fn zero_sized_result_reconstruction_limits() {
        let session = CompilerSession::new();
        let env = session.module_env();
        let accepts = |ty, effects| {
            accepts_no_value_result(
                &CallImplType::value(FnType::new_by_val([], ty, effects)),
                &env,
            )
        };
        assert!(accepts(Type::unit(), effect(PrimitiveEffect::Fallible)));
        assert!(!accepts(Type::never(), no_effects()));
        let mut ty = Type::unit();
        for _ in 0..11 {
            ty = Type::tuple([ty, ty]);
        }
        assert!(accepts(ty, no_effects())); // 4095 nodes, despite a small type graph.
        ty = Type::tuple([ty, ty]);
        assert!(is_zero_sized_result(ty, &env));
        assert!(accepts(ty, no_effects()));
        assert!(check_result_limits(ty, &env, Location::new_synthesized()).is_err());
        let mut ty = Type::unit();
        for _ in 0..ZERO_SIZED_RESULT_DEPTH {
            ty = Type::tuple([ty]);
        }
        assert!(accepts(ty, no_effects()));
        assert!(check_result_limits(Type::tuple([ty]), &env, Location::new_synthesized()).is_err());
    }
}
