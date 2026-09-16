// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Exact-unit direct entries and their uniform callable interfaces.

use std::mem;

use rustc_hash::FxHashMap;
use ustr::{Ustr, ustr};

use crate::{
    Location,
    containers::b,
    hir::{function::ArgConvention, value::LiteralValue},
    mir::{
        BasicBlock, BlockId, Function, Operation, OperationKind, Parameter, ParameterId,
        ParameterKind, Value,
        edit::FunctionEdit,
        operation::CallMetadata,
        terminator::{Terminator, TerminatorKind},
    },
    module::{FunctionId, LocalFunctionId, ModuleEnv, id::Id},
    types::{
        effects::{PrimitiveEffect, effect, no_effects},
        r#type::{CallImplType, CallResultConvention, FnType, Type},
        type_like::TypeLike,
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

/// Exported conventions depend on declarations, never on optimization decisions in another module.
fn exported_no_value(id: FunctionId, env: ModuleEnv<'_>) -> bool {
    let Some(module) = env.module_by_id(id.module) else {
        return false;
    };
    let Some(function) = module.get_function_by_id(id.function) else {
        return false;
    };
    let scheme = &function.definition.ty_scheme;
    function.code.as_script().is_some()
        && function.definition.return_convention() == CallResultConvention::Value
        && scheme.ty.ret == Type::unit()
        && scheme.ty.is_constant()
        && scheme.ty_quantifiers.is_empty()
        && scheme
            .extra_parameters(ModuleEnv::new(module, env.modules))
            .requirements
            .is_empty()
}

pub(super) fn select(
    mut entries: Vec<Option<Function>>,
    env: ModuleEnv<'_>,
) -> (Vec<Option<Function>>, DirectEntries) {
    let module = env.current.module_id();
    let mut direct = DirectEntries::default();
    let count = entries.len();
    for index in 0..count {
        let local = LocalFunctionId::from_index(index);
        let exported = exported_no_value(FunctionId::new(module, local), env);
        let eligible = entries[index].as_ref().is_some_and(|body| {
            body.result_convention() == CallResultConvention::Value
                && body
                    .parameters()
                    .split_last()
                    .is_some_and(|(result, inputs)| {
                        result.kind == ParameterKind::Return
                            && result.ty == Type::unit()
                            && inputs
                                .iter()
                                .all(|p| p.kind != ParameterKind::Dictionary && p.ty.is_constant())
                    })
        });
        debug_assert!(
            !exported || eligible,
            "declared NoValue entry {local:?} must have an eligible physical body"
        );
        if !eligible || (env.current.get_function_by_id(local).is_some() && !exported) {
            continue;
        }
        let implementation = LocalFunctionId::from_index(entries.len());
        let body = entries[index].take().unwrap();
        entries[index] = Some(adapter(&body, FunctionId::new(module, implementation), env));
        entries.push(Some(without_result(body)));
        direct.insert(local, implementation);
    }
    let mut imported = FxHashMap::default();
    for entry in &mut entries {
        let Some(body) = entry.take() else { continue };
        let mut edit = FunctionEdit::new(body);
        let blocks = edit.blocks().collect::<Vec<_>>();
        for block in blocks {
            let mut operations = mem::take(&mut edit.block_mut(block).operations);
            let mut rewritten = Vec::with_capacity(operations.len());
            for mut operation in operations.drain(..) {
                let result = rewrite_call(&mut operation, &direct, &mut imported, env);
                let span = operation.span;
                rewritten.push(operation);
                if let Some(result) = result {
                    rewritten.push(store_unit(&mut edit, result, span, env));
                }
            }
            edit.block_mut(block).operations = rewritten;
            let terminator = &mut edit.block_mut(block).terminator;
            if let TerminatorKind::Invoke {
                operation, normal, ..
            } = &mut terminator.kind
                && let Some(result) = rewrite_call(operation, &direct, &mut imported, env)
            {
                let (span, target) = (operation.span, *normal);
                let store = store_unit(&mut edit, result, span, env);
                let success = edit.add_block(Terminator::goto(span, target));
                edit.block_mut(success).operations.push(store);
                let TerminatorKind::Invoke { normal, .. } =
                    &mut edit.block_mut(block).terminator.kind
                else {
                    unreachable!()
                };
                *normal = success;
            }
        }
        *entry = Some(edit.finish_unverified());
    }
    (entries, direct)
}

fn rewrite_call(
    operation: &mut Operation,
    direct: &DirectEntries,
    imported: &mut FxHashMap<FunctionId, bool>,
    env: ModuleEnv<'_>,
) -> Option<Value> {
    let OperationKind::Call { ty, .. } = &mut operation.kind else {
        return None;
    };
    if ty.result_convention != CallResultConvention::Value {
        return None;
    }
    let Value::Function(target) = operation.operands[0] else {
        return None;
    };
    let eligible = if target.module == env.current.module_id() {
        direct.contains_key(&target.function)
    } else {
        *imported
            .entry(target)
            .or_insert_with(|| exported_no_value(target, env))
    };
    if !eligible {
        return None;
    }
    assert_eq!(ty.fn_ty.ret, Type::unit());
    ty.result_convention = CallResultConvention::NoValue;
    let mut operands = mem::take(&mut operation.operands).into_vec();
    let result = operands.pop().unwrap();
    operation.operands = operands.into_boxed_slice();
    Some(result)
}

fn store_unit(
    edit: &mut FunctionEdit,
    result: Value,
    span: Location,
    env: ModuleEnv<'_>,
) -> Operation {
    let unit = edit.add_constant(Type::unit(), LiteralValue::new_native(()), &env);
    Operation::store(span, Value::Constant(unit), result)
}

fn without_result(body: Function) -> Function {
    let mut edit = FunctionEdit::new(body);
    edit.set_name(ustr(&format!("{}$no_value", edit.name())));
    let result = Value::Parameter(ParameterId::from_index(edit.parameters().len() - 1));
    // Any internal use that still needs a unit place (notably a native call) keeps local storage.
    // The optimized path removes dead return stores and their local allocation after selection.
    let span = Location::new_synthesized();
    let mut allocation = Operation::alloca(span, Type::unit());
    let local = edit.assign_new_result(&mut allocation).unwrap();
    edit.visit_operands_mut(|operand| {
        if *operand == result {
            *operand = local.clone();
        }
    });
    edit.remove_parameters(|p| p.kind == ParameterKind::Return);
    edit.set_result_convention(CallResultConvention::NoValue);
    edit.block_mut(edit.entry())
        .operations
        .insert(0, allocation);
    edit.finish_unverified()
}

fn adapter(body: &Function, implementation: FunctionId, env: ModuleEnv<'_>) -> Function {
    build_adapter(
        body.name,
        body.parameters(),
        implementation,
        may_fail(body),
        env,
    )
}

fn may_fail(body: &Function) -> bool {
    body.blocks().any(|block| {
        matches!(
            body.block(block).terminator().kind,
            TerminatorKind::Invoke { .. }
        )
    })
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
    if adapter.result_convention() != CallResultConvention::Value
        || direct.result_convention() != CallResultConvention::NoValue
        || result.kind != ParameterKind::Return
        || result.ty != Type::unit()
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
    env: ModuleEnv<'_>,
) -> Function {
    let span = Location::new_synthesized();
    let inputs = &parameters[..parameters.len() - 1];
    let ty = FnType::new_mut_resolved(
        inputs.iter().map(|p| {
            (
                p.ty,
                p.kind == ParameterKind::Parameter(ArgConvention::MutableRef),
            )
        }),
        Type::unit(),
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
    for (index, input) in inputs.iter().enumerate() {
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
        parameters.to_vec(),
        vec![],
        blocks,
    ));
    let result = Value::Parameter(ParameterId::from_index(inputs.len()));
    let store = store_unit(&mut edit, result, span, env);
    edit.block_mut(BlockId::from_index(usize::from(fallible)))
        .operations
        .push(store);
    edit.finish_unverified()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization,
        execution::ReferenceInterpreterLimits,
        hir::value::Value as HostValue,
        mir::{
            pass::dce,
            physical::{
                expand_physical_mir, interpreter::run_entry_with_profile, prepare_physical_mir,
                program::resolve_physical_program,
            },
            profile::MirExecutionProfile,
        },
        module::Path,
    };

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
            for name in ["invoke", "generic", "empty"] {
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

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test::wasm_bindgen_test)]
    fn unit_result_elision_reduces_executed_operations() {
        let mut session = CompilerSession::new();
        let module = session
            .compile(
                "#[inline(never)] fn bump(x: &mut int) { x = x + 1; }
             pub fn compute(n: int) -> int {
                 let mut x = 0; for i in 0..n { bump(x); }; x
             }",
                "unit_profile",
                Path::single_str("unit_profile"),
            )
            .unwrap()
            .module_id;
        let dependencies = session.prepare_physical_program(module).unwrap();
        let source = session.expect_fresh_module(module);
        let env = ModuleEnv::new(source, session.raw_modules());
        let semantic = session
            .mir_artifacts_for(module, MirOptimization::Enabled)
            .unwrap();
        let expanded = expand_physical_mir(module, semantic, env, session.known_callees()).unwrap();
        let original =
            prepare_physical_mir(expanded.clone(), DirectEntries::default(), semantic, env)
                .unwrap();
        let (mut entries, direct) = select(expanded, env);
        for body in entries.iter_mut().flatten() {
            if let Some(cleaned) = dce::remove_dead_storage(body) {
                *body = cleaned;
            }
        }
        let selected = prepare_physical_mir(entries, direct, semantic, env).unwrap();
        let entry = FunctionId::new(
            module,
            source.get_local_function_id(ustr("compute")).unwrap(),
        );
        let mut profiles = Vec::new();
        for local in [&original, &selected] {
            let modules = dependencies
                .modules()
                .iter()
                .copied()
                .filter(|m| m.module() != module)
                .chain([local]);
            let program = resolve_physical_program(modules).unwrap();
            let mut profile = MirExecutionProfile::default();
            let result = run_entry_with_profile(
                &program,
                entry,
                &mut [HostValue::native(16isize)],
                ReferenceInterpreterLimits::default(),
                &session,
                Some(&mut profile),
            )
            .unwrap();
            assert_eq!(result.into_primitive_ty::<isize>().unwrap(), 16);
            profiles.push((profile.total().total(), profile.peak_cells()));
        }
        assert!(
            profiles[1].0 < profiles[0].0,
            "operation counts: {profiles:?}"
        );
        assert!(
            profiles[1].1 <= profiles[0].1,
            "peak allocations: {profiles:?}"
        );
        eprintln!("unit result elision (operations, peak allocations): {profiles:?}");
    }
}
