// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Zero-sized direct results and their uniform callable interfaces.

use rustc_hash::FxHashMap;
use ustr::Ustr;

use crate::{
    Location,
    containers::b,
    hir::{function::ArgConvention, value::LiteralValue},
    mir::{
        BasicBlock, BlockId, DebugLocation, Function, Operation, OperationKind, Parameter,
        ParameterId, ParameterKind, Value,
        edit::FunctionEdit,
        operation::CallMetadata,
        results::{is_zero_sized_result, zero_sized_result},
        terminator::{Terminator, TerminatorKind},
        value::Constant,
    },
    module::{FunctionId, LocalFunctionId, ModuleEnv, id::Id},
    std::value::product_member_types,
    types::{
        effects::{PrimitiveEffect, effect, no_effects},
        r#type::{CallImplType, CallResultConvention, FnType, Type},
    },
};

/// Callable symbols keep their Value interface; direct calls resolve to these private bodies.
pub(crate) type DirectEntries = FxHashMap<LocalFunctionId, LocalFunctionId>;

/// Function references outside a direct call select the uniform callable interface.
pub(super) fn callable_targets(operation: &Operation) -> impl Iterator<Item = FunctionId> + '_ {
    let direct = matches!(
        operation.kind,
        OperationKind::Call { .. } | OperationKind::Project { .. }
    );
    operation
        .operands
        .iter()
        .enumerate()
        .filter_map(move |(index, value)| match value {
            Value::Function(id) if index != 0 || !direct => Some(*id),
            _ => None,
        })
        .chain(operation.kind.function_id())
}

/// Semantic bodies already use NoValue. Preserve the uniform callable entry, including for
/// specializations used through evidence or callback thunks. Untyped physical helpers are direct-only.
pub(super) fn select(
    mut entries: Vec<Option<Function>>,
    env: ModuleEnv<'_>,
) -> (Vec<Option<Function>>, DirectEntries) {
    let module = env.current.module_id();
    let mut direct = DirectEntries::default();
    let count = entries.len();
    for index in 0..count {
        let local = LocalFunctionId::from_index(index);
        if entries[index]
            .as_ref()
            .is_none_or(|body| body.result_convention() != CallResultConvention::NoValue)
        {
            continue;
        }
        let implementation = LocalFunctionId::from_index(entries.len());
        let body = entries[index].take().unwrap();
        let Some(result_ty) = body.direct_result_type() else {
            entries[index] = Some(body);
            continue;
        };
        let mut parameters = body.parameters().to_vec();
        parameters.push(Parameter {
            ty: result_ty,
            kind: ParameterKind::Return,
        });
        entries[index] = Some(build_adapter(
            body.name,
            &parameters,
            FunctionId::new(module, implementation),
            may_fail(&body),
            zero_sized_result(result_ty, &env).expect("NoValue result has bounded synthesis"),
            env,
        ));
        entries.push(Some(body));
        direct.insert(local, implementation);
    }
    (entries, direct)
}

fn store_result(
    edit: &mut FunctionEdit,
    result: Value,
    value: Constant,
    span: DebugLocation,
    env: ModuleEnv<'_>,
) -> Operation {
    let constant = edit.add_constant(value.ty, value.representation, &env);
    Operation::store(span, Value::Constant(constant), result)
}

fn may_fail(body: &Function) -> bool {
    body.blocks().any(|block| {
        matches!(
            body.block(block).terminator().kind,
            TerminatorKind::Invoke { .. }
        )
    })
}

/// The forwarding operations shared by adapter execution, profiling and verification.
pub(super) struct ValueAdapter<'a> {
    pub call: &'a Operation,
    pub invoke: Option<&'a Terminator>,
    pub store: &'a Operation,
    pub result: &'a Constant,
    pub returned: &'a Terminator,
    pub failure: Option<&'a Terminator>,
}

/// Read the result from its store operand, independently of constant-table ordering.
pub(super) fn decode_adapter(body: &Function) -> Option<ValueAdapter<'_>> {
    let entry = body.block(body.blocks().next()?);
    let (call, invoke, store, returned, failure) = match &entry.terminator().kind {
        TerminatorKind::Invoke {
            operation,
            normal,
            error,
        } if entry.operations().is_empty() => {
            let block = |id| {
                body.blocks()
                    .find(|candidate| *candidate == id)
                    .map(|id| body.block(id))
            };
            let success = block(*normal)?;
            let failure = block(*error)?;
            let [store] = success.operations() else {
                return None;
            };
            if !failure.operations().is_empty()
                || !matches!(failure.terminator().kind, TerminatorKind::PropagateError)
            {
                return None;
            }
            (
                operation,
                Some(entry.terminator()),
                store,
                success.terminator(),
                Some(failure.terminator()),
            )
        }
        TerminatorKind::Return { .. } => {
            let [call, store] = entry.operations() else {
                return None;
            };
            (call, None, store, entry.terminator(), None)
        }
        _ => return None,
    };
    if !matches!(returned.kind, TerminatorKind::Return { .. })
        || !matches!(call.kind, OperationKind::Call { .. })
        || !matches!(store.kind, OperationKind::Store)
    {
        return None;
    }
    let [Value::Constant(constant), Value::Parameter(output)] = store.operands.as_ref() else {
        return None;
    };
    let result = body.constants().get(constant.as_index())?;
    let parameter = body.parameters().get(output.as_index())?;
    if parameter.kind != ParameterKind::Return || parameter.ty != result.ty {
        return None;
    }
    Some(ValueAdapter {
        call,
        invoke,
        store,
        result,
        returned,
        failure,
    })
}

/// Validate the explicit literal without rebuilding it or imposing the synthesis budget.
fn valid_result_literal(result: &Constant, env: ModuleEnv<'_>) -> bool {
    let mut pending = vec![(result.ty, &result.representation)];
    while let Some((ty, value)) = pending.pop() {
        if ty == Type::unit() {
            if value.as_primitive_ty::<()>().is_none() {
                return false;
            }
        } else {
            let LiteralValue::Tuple(fields) = value else {
                return false;
            };
            let Some(members) = product_member_types(ty, &env) else {
                return false;
            };
            if members.len() != fields.len() {
                return false;
            }
            pending.extend(members.into_iter().zip(fields.iter()));
        }
    }
    true
}

/// Executors may forward these fixed adapters without allocating another interpreter frame.
pub(super) fn valid_adapter(
    adapter: &Function,
    direct: &Function,
    target: FunctionId,
    env: ModuleEnv<'_>,
) -> bool {
    let Some((result, inputs)) = adapter.parameters().split_last() else {
        return false;
    };
    let Some(decoded) = decode_adapter(adapter) else {
        return false;
    };
    if adapter.result_convention() != CallResultConvention::Value
        || direct.result_convention() != CallResultConvention::NoValue
        || result.kind != ParameterKind::Return
        || decoded.result.ty != result.ty
        || direct
            .direct_result_type()
            .is_some_and(|ty| ty != result.ty)
        || !is_zero_sized_result(result.ty, &env)
        || !valid_result_literal(decoded.result, env)
        || inputs != direct.parameters()
    {
        return false;
    }
    // Selection and subsequent storage DCE preserve Invoke terminators, so the direct body has
    // the same fallibility as the original body used to construct this adapter.
    let expected = build_adapter(
        adapter.name,
        adapter.parameters(),
        target,
        may_fail(direct),
        decoded.result.representation.clone(),
        env,
    );
    adapter.constants() == expected.constants()
        && adapter.blocks().count() == expected.blocks().count()
        && adapter
            .blocks()
            .all(|block| adapter.block(block) == expected.block(block))
}

fn build_adapter(
    name: Ustr,
    parameters: &[Parameter],
    implementation: FunctionId,
    fallible: bool,
    result_value: LiteralValue,
    env: ModuleEnv<'_>,
) -> Function {
    let span = Location::new_synthesized();
    let inputs = &parameters[..parameters.len() - 1];
    let result_ty = parameters.last().unwrap().ty;
    let ty = FnType::new_mut_resolved(
        inputs
            .iter()
            .filter(|p| p.kind != ParameterKind::Dictionary)
            .map(|p| {
                (
                    p.ty,
                    p.kind == ParameterKind::Place(ArgConvention::MutableRef),
                )
            }),
        result_ty,
        if fallible {
            effect(PrimitiveEffect::Fallible)
        } else {
            no_effects()
        },
    );
    let mut call = Operation::call(
        span,
        Value::Function(implementation),
        (0..inputs.len()).map(|i| Value::Parameter(ParameterId::from_index(i))),
        CallImplType::new(ty, CallResultConvention::NoValue),
    );
    let mut metadata = CallMetadata::default();
    for (index, input) in inputs
        .iter()
        .filter(|p| p.kind != ParameterKind::Dictionary)
        .enumerate()
    {
        if input.kind == ParameterKind::Owned {
            metadata.owned_arguments.insert(index);
        }
    }
    if !metadata.owned_arguments.is_empty() {
        let OperationKind::Call { metadata: out, .. } = &mut call.kind else {
            unreachable!()
        };
        *out = Some(b(metadata));
    }
    let ret = Terminator::ret(span);
    let blocks = if fallible {
        vec![
            BasicBlock::new(
                vec![],
                Terminator::invoke(span, call, BlockId::from_index(1), BlockId::from_index(2)),
            ),
            BasicBlock::new(vec![], ret),
            BasicBlock::new(vec![], Terminator::propagate_error(span)),
        ]
    } else {
        vec![BasicBlock::new(vec![call], ret)]
    };
    let mut edit = FunctionEdit::new(Function::new(
        name,
        CallResultConvention::Value,
        None,
        parameters.to_vec(),
        vec![],
        blocks,
    ));
    let result = Value::Parameter(ParameterId::from_index(inputs.len()));
    let value = Constant {
        ty: result_ty,
        representation: result_value,
    };
    let store = store_result(&mut edit, result, value, span.into(), env);
    edit.block_mut(BlockId::from_index(usize::from(fallible)))
        .operations
        .push(store);
    edit.finish_unverified()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::results::{ZERO_SIZED_RESULT_DEPTH, check_result_limits};
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization,
        execution::ReferenceInterpreterLimits,
        hir::value::Value as HostValue,
        module::Path,
        std::{STD_MODULE_ID, math::int_type},
    };
    use ustr::ustr;

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn unit_entries_preserve_callable_and_cross_module_contracts() {
        let mut session = CompilerSession::new();
        let library = session
            .compile(
                "#[inline(never)] pub fn bump(x: &mut int) { x = x + 1; }
             #[inline(never)] pub fn invoke<T>(f: (&mut int) -> T, x: &mut int) -> T { f(x) }
             pub fn generic<T>(x: T) { }
             pub struct Empty {}
             pub fn empty() -> Empty { Empty {} }",
                "unit_entries",
                Path::single_str("unit_entries"),
            )
            .unwrap()
            .module_id;
        let user = session
            .compile(
                "use unit_entries::*;
             pub fn compute(x: int) -> int {
                 let mut value = x;
                 bump(value);
                 let f = bump;
                 invoke(f, value);
                 value
             }",
                "unit_user",
                Path::single_str("unit_user"),
            )
            .unwrap()
            .module_id;
        let entry = session
            .expect_fresh_module(user)
            .get_local_function_id(ustr("compute"))
            .unwrap();
        for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
            session.set_physical_mir_optimization(optimization);
            let program = session.prepare_physical_program(user).unwrap();
            let artifacts = program.module(library).unwrap();
            let symbol = |name| {
                session
                    .expect_fresh_module(library)
                    .get_local_function_id(ustr(name))
                    .unwrap()
            };
            let bump = symbol("bump");
            let direct = artifacts.get(artifacts.direct_entry(bump)).unwrap();
            assert_eq!(direct.result_convention(), CallResultConvention::NoValue);
            assert_eq!(direct.parameters().len(), 1);
            if optimization == MirOptimization::Enabled {
                let has_unit_storage = direct
                    .blocks()
                    .flat_map(|b| direct.block(b).operations())
                    .any(
                        |op| matches!(op.kind, OperationKind::Alloca { ty } if ty == Type::unit()),
                    );
                assert!(!has_unit_storage);
            }
            assert_eq!(
                artifacts.get(bump).unwrap().result_convention(),
                CallResultConvention::Value
            );
            let empty = symbol("empty");
            assert_ne!(artifacts.direct_entry(empty), empty);
            for name in ["invoke", "generic"] {
                let id = symbol(name);
                assert_eq!(artifacts.direct_entry(id), id, "{name} retains Value");
            }
            let caller = program.function(FunctionId::new(user, entry)).unwrap();
            assert!(
                caller
                    .blocks()
                    .flat_map(|b| caller.block(b).operations())
                    .any(|op| matches!(&op.kind, OperationKind::Call { ty, .. }
                    if ty.result_convention == CallResultConvention::NoValue
                        && op.operands[0] == Value::Function(FunctionId::new(library, bump))))
            );
            let result = session
                .run_entry(
                    ExecutionTarget::PhysicalMir,
                    user,
                    entry,
                    vec![HostValue::native(40isize)],
                )
                .unwrap();
            assert_eq!(result.into_primitive_ty::<isize>().unwrap(), 42);
        }
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn zero_sized_products_preserve_typed_results_across_calls() {
        let mut session = CompilerSession::new();
        let library = session
            .compile(
                "pub struct Empty {}
             pub struct Bundle { first: Empty, nested: ((), Empty) }
             #[inline(never)] pub fn make(x: &mut int) -> Bundle {
                 x += 1; Bundle { first: Empty {}, nested: ((), Empty {}) }
             }
             #[inline(never)] pub fn apply<T>(f: (&mut int) -> T, x: &mut int) -> T { f(x) }",
                "zero_results",
                Path::single_str("zero_results"),
            )
            .unwrap()
            .module_id;
        let user = session
            .compile(
                "use zero_results::*;
             pub fn compute(x: int) -> (Bundle, Bundle, int) {
                 let mut n = x;
                 let direct = make(n);
                 let f = make;
                 let indirect = apply(f, n);
                 (direct, indirect, n)
             }
             pub fn host(x: int) -> Bundle { let mut n = x; make(n) }",
                "zero_user",
                Path::single_str("zero_user"),
            )
            .unwrap()
            .module_id;
        let function = |module, name| {
            session
                .expect_fresh_module(module)
                .get_local_function_id(ustr(name))
                .unwrap()
        };
        let make = function(library, "make");
        let compute = function(user, "compute");
        let host = function(user, "host");
        for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
            session.set_physical_mir_optimization(optimization);
            let program = session.prepare_physical_program(user).unwrap();
            let artifacts = program.module(library).unwrap();
            let adapter = artifacts.get(make).unwrap();
            let result_ty = adapter.parameters().last().unwrap().ty;
            assert_ne!(result_ty, Type::unit());
            assert_ne!(artifacts.direct_entry(make), make);
            let caller = program.function(FunctionId::new(user, compute)).unwrap();
            assert!(
                caller
                    .blocks()
                    .flat_map(|b| caller.block(b).operations())
                    .any(|op| {
                        matches!(&op.kind, OperationKind::Call { ty, .. }
                    if ty.result_convention == CallResultConvention::NoValue
                        && ty.fn_ty.ret == result_ty
                        && op.operands[0] == Value::Function(FunctionId::new(library, make)))
                    })
            );
            let check_bundle = |value: &HostValue| {
                let fields = value.as_tuple().unwrap();
                assert!(fields[0].as_tuple().unwrap().is_empty());
                let nested = fields[1].as_tuple().unwrap();
                assert_eq!(nested[0].as_primitive_ty::<()>(), Some(&()));
                assert!(nested[1].as_tuple().unwrap().is_empty());
            };
            for target in ExecutionTarget::ALL {
                let result = session
                    .run_entry(target, user, compute, vec![HostValue::native(40isize)])
                    .unwrap();
                let fields = result.as_tuple().unwrap();
                check_bundle(&fields[0]);
                check_bundle(&fields[1]);
                assert_eq!(fields[2].as_primitive_ty::<isize>(), Some(&42));
                result.discard_storage();
                let result = session
                    .run_entry(target, user, host, vec![HostValue::native(0isize)])
                    .unwrap();
                check_bundle(&result);
                result.discard_storage();
            }
        }
    }

    #[test]
    fn zero_sized_result_limits_preserve_existing_adapter_validation() {
        let session = CompilerSession::new();
        let env = ModuleEnv::new(
            session.expect_fresh_module(STD_MODULE_ID),
            session.raw_modules(),
        );
        assert!(zero_sized_result(Type::never(), &env).is_none());
        assert!(zero_sized_result(int_type(), &env).is_none());
        let mut ty = Type::unit();
        for _ in 0..20 {
            ty = Type::tuple([ty, ty]);
        }
        assert!(check_result_limits(ty, &env, Location::new_synthesized()).is_err());
        assert!(is_zero_sized_result(ty, &env));
        let mut ty = Type::unit();
        let mut literal = LiteralValue::new_native(());
        for _ in 0..=ZERO_SIZED_RESULT_DEPTH {
            ty = Type::tuple([ty]);
            literal = LiteralValue::new_tuple(vec![literal]);
        }
        assert!(check_result_limits(ty, &env, Location::new_synthesized()).is_err());
        assert!(is_zero_sized_result(ty, &env));

        // A previously-built adapter remains valid even beyond today's synthesis limits.
        let target = FunctionId::new(STD_MODULE_ID, LocalFunctionId::from_index(0));
        let adapter = build_adapter(
            ustr("large_result"),
            &[Parameter {
                ty,
                kind: ParameterKind::Return,
            }],
            target,
            false,
            literal,
            env,
        );
        let direct = Function::new(
            ustr("direct"),
            CallResultConvention::NoValue,
            None,
            vec![],
            vec![],
            vec![BasicBlock::new(
                vec![],
                Terminator::ret(Location::new_synthesized()),
            )],
        );
        assert!(valid_adapter(&adapter, &direct, target, env));

        let mut edit = FunctionEdit::new(adapter);
        let extra = edit.add_constant(int_type(), LiteralValue::new_native(7isize), &env);
        edit.constants_mut().swap(0, extra.as_index());
        edit.visit_operands_mut(|operand| {
            if matches!(operand, Value::Constant(_)) {
                *operand = Value::Constant(extra);
            }
        });
        let reordered = edit.finish_unverified();
        assert_eq!(decode_adapter(&reordered).unwrap().result.ty, ty);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn unit_adapters_preserve_failures_and_source_call_depth() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "#[inline(never)] pub fn descend(x: int) {
                 if x > 0 { descend(x - 1); } else { let checked = idiv(1, x); }
             }
             #[inline(never)] fn invoke<T>(f: (int) -> T, x: int) -> T { f(x) }
             pub fn compute(x: int) { let f = descend; invoke(f, x); }",
                "unit_failure",
                Path::single_str("unit_failure"),
            )
            .unwrap()
            .module_id;
        let entry = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr("compute"))
            .unwrap();
        for optimization in [MirOptimization::Disabled, MirOptimization::Enabled] {
            session.set_physical_mir_optimization(optimization);
            for depth in [2, 4, 8] {
                let mut outcomes = Vec::new();
                for target in ExecutionTarget::ALL {
                    let result = session.run_entry_with_limits(
                        target,
                        module,
                        entry,
                        vec![HostValue::native(2isize)],
                        ReferenceInterpreterLimits::default().with_call_depth_limit(depth),
                    );
                    outcomes.push(result.unwrap_err().kind());
                }
                assert!(
                    outcomes.iter().all(|outcome| *outcome == outcomes[0]),
                    "{outcomes:?}"
                );
            }
        }
    }
}
