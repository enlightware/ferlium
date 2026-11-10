// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::{fmt, rc::Rc, slice::from_ref};

use crate::{
    CompilerSession, FxHashMap, FxHashSet, Location, Modules,
    ast::ImplAstIndex,
    eval::{EvalCtx, EvalResult, ValOrMut},
    hir::{
        NodeArena,
        function::{ArgConvention, Callable, CallableDefinition, Function},
    },
    module::{
        self, BlanketTraitImplSubKey, ConcreteTraitImplKey, CurrentTypeItems, ELocalDecl,
        LocalFunctionId, LocalTraitId, Module, ModuleEnv, ModuleId, Path, PendingFunctionCollector,
        TraitDictionary, TraitId, TraitImpl, TypeDefId, Visibility, id::Id,
    },
    std::{
        STD_MODULE_ID, core_traits_names::VALUE_TRAIT_NAME, math::int_type, new_module_using_std,
    },
    types::{
        effects::{EffType, PrimitiveEffect, effect},
        r#trait::Trait,
        r#type::{FnType, SubscriptType, Type, TypeKind},
        type_inference::unify::UnifiedTypeInference,
    },
};

use super::{
    CurrentProjectionSubscriptTypes, TraitSolver,
    matching::input_head_may_match,
    probe::{ConstraintAssumptions, TraitSolverProbe},
    trait_solver_from_module,
};

#[test]
fn borrowed_function_lookup_preserves_named_function_selection() {
    use crate::module::{Def, DefKind};

    fn check(module: &mut Module, modules: &Modules) {
        // Reference the previous eager map, including its treatment of
        // duplicate names, non-functions and anonymous entries.
        let expected: FxHashMap<_, _> = module
            .def_table
            .iter()
            .filter_map(|(def, name)| Some(((*name)?, *def.kind.as_function()?)))
            .collect();
        let solver = trait_solver_from_module!(module, modules);
        let mut probe = TraitSolverProbe::from_solver(&solver);
        for name in [ustr::ustr("f"), ustr::ustr("other"), ustr::ustr("missing")] {
            assert_eq!(solver.current_function(name), expected.get(&name).copied());
            assert_eq!(
                probe.with_solver(|nested| nested.current_function(name)),
                expected.get(&name).copied()
            );
        }
        drop(probe);
        // Finishing releases the definition-table borrow before commit mutates it.
        let mut pending = FxHashMap::default();
        assert!(
            solver
                .finish()
                .commit(&mut module.functions, &mut module.def_table, &mut pending)
                .is_empty()
        );
    }

    let modules = Modules::default();
    let mut module = Module::new(ModuleId::new(0), Path::single_str("$function_lookup"));
    let name = ustr::ustr("f");
    let function = |id| {
        Def::new(
            DefKind::Function(LocalFunctionId::new(id)),
            Visibility::Module,
        )
    };
    check(&mut module, &modules);
    module.def_table.insert(name, function(0));
    module.def_table.insert_anonymous(function(1));
    module.def_table.insert(
        ustr::ustr("other"),
        Def::public(DefKind::BareNativeTypeAlias),
    );
    check(&mut module, &modules);
    module.def_table.insert(name, function(2));
    check(&mut module, &modules);
    module
        .def_table
        .insert(name, Def::public(DefKind::BareNativeTypeAlias));
    check(&mut module, &modules);
}

fn impl_storage_fixture() -> (Module, ConcreteTraitImplKey) {
    // No semantic query uses these entries: they exercise storage and visibility.
    let module_id = ModuleId::new(0);
    let mut module = Module::new(module_id, Path::single_str("$impl_storage"));
    let trait_id = TraitId::new(module_id, LocalTraitId::new(0));
    let key = ConcreteTraitImplKey::new(trait_id, vec![Type::unit()]);
    let imp = TraitImpl::new(
        trait_id,
        vec![Type::unit()],
        vec![],
        vec![],
        TraitDictionary::new(&[], &[]),
        Type::unit(),
        true,
        None,
    );
    module.impls.add_concrete_struct(key.clone(), imp);
    (module, key)
}

#[test]
fn impl_probes_share_tables_and_isolate_nested_writes() {
    let (mut module, key) = impl_storage_fixture();
    let modules = Modules::default();
    {
        let mut borrowed = TraitSolverProbe::from_module(&module, &modules);
        borrowed.with_solver(|scratch| {
            assert!(Rc::ptr_eq(&scratch.impls.data, &module.impls.data));
            assert!(Rc::ptr_eq(
                &scratch.impls.concrete_key_to_id,
                &module.impls.concrete_key_to_id
            ));
        });
    }
    let solver = trait_solver_from_module!(module, &modules);
    let mut probe = TraitSolverProbe::from_solver(&solver);
    assert!(Rc::ptr_eq(&probe.impls.data, &solver.impls.data));
    assert!(Rc::ptr_eq(
        &probe.impls.concrete_key_to_id,
        &solver.impls.concrete_key_to_id
    ));
    probe.with_solver(|inner| {
        // A no-op rollback must not detach the dictionaries.
        let snapshot = inner.snapshot_derived_impl_state();
        inner.rollback_derived_impl_state(snapshot);
        assert!(Rc::ptr_eq(&inner.impls.data, &solver.impls.data));
        let mut nested = TraitSolverProbe::from_solver(inner);
        nested.with_solver(|nested| {
            let mut private = nested.impls.data[0].clone();
            private.public = false;
            let private_key = ConcreteTraitImplKey::new(key.trait_id, vec![Type::never()]);
            let id = nested
                .impls
                .add_concrete_struct(private_key.clone(), private);
            Rc::make_mut(&mut nested.impls.data)[0].output_tys = vec![Type::never()];
            assert_eq!(inner.impls.data[0].output_tys, vec![Type::unit()]);
            assert!(!inner.impls.concrete_key_to_id.contains_key(&private_key));
            let filtered = TraitSolverProbe::from_solver(nested);
            assert!(Rc::ptr_eq(&filtered.impls.data, &nested.impls.data));
            assert!(!Rc::ptr_eq(
                &filtered.impls.concrete_key_to_id,
                &nested.impls.concrete_key_to_id
            ));
            assert!(filtered.impls.concrete_key_to_id.contains_key(&key));
            assert!(!filtered.impls.concrete_key_to_id.contains_key(&private_key));
            assert_eq!(nested.impls.concrete_key_to_id[&private_key], id);
            assert!(!filtered.impls.data[id.as_index()].public);
        });
        assert!(Rc::ptr_eq(&inner.impls.data, &solver.impls.data));
    });
    assert_eq!(solver.impls.data.len(), 1);
    assert_eq!(solver.impls.data[0].output_tys, vec![Type::unit()]);
}

#[test]
fn impl_snapshot_rollback_restores_all_indexes_with_live_probes() {
    let (mut module, key) = impl_storage_fixture();
    let modules = Modules::default();
    let mut solver = trait_solver_from_module!(module, &modules);
    let outer = solver.snapshot_derived_impl_state();
    let observer = TraitSolverProbe::from_solver(&solver);
    let imp = solver.impls.data[0].clone();
    let private_key = ConcreteTraitImplKey::new(key.trait_id, vec![Type::never()]);
    let id = solver
        .impls
        .add_concrete_struct(private_key.clone(), imp.clone());
    let blanket_key = module::BlanketTraitImplKey::new(
        key.trait_id,
        BlanketTraitImplSubKey {
            input_tys: vec![Type::variable_id(0)],
            ty_var_count: 1,
            eff_var_count: 0,
            constraints: vec![],
        },
    );
    solver.impls.add_blanket_struct(blanket_key, imp.clone());
    Rc::make_mut(&mut solver.impls.generated_value_key_to_id).insert(vec![Type::never()], id);
    Rc::make_mut(&mut solver.impls.application_key_to_id).insert(private_key.clone(), id);
    solver
        .fn_collector
        .reserve_with_visibility(ustr::ustr("outer"), Visibility::Module);
    let inner = solver.snapshot_derived_impl_state();
    solver.impls.add_anonymous_dictionary_struct(imp);
    solver
        .fn_collector
        .reserve_with_visibility(ustr::ustr("inner"), Visibility::Module);
    let retained = TraitSolverProbe::from_solver(&solver);
    solver.rollback_derived_impl_state(inner);
    assert_eq!(solver.impls.data.len(), 3);
    assert_eq!(solver.fn_collector.new_elements.len(), 1);
    assert_eq!(solver.impls.application_key_to_id[&private_key], id);
    assert_eq!(retained.impls.data.len(), 4);
    solver.rollback_derived_impl_state(outer);
    assert!(Rc::ptr_eq(
        &solver.impls.concrete_key_to_id,
        &observer.impls.concrete_key_to_id
    ));
    assert!(Rc::ptr_eq(
        &solver.impls.blanket_key_to_id,
        &observer.impls.blanket_key_to_id
    ));
    assert!(Rc::ptr_eq(
        &solver.impls.generated_value_key_to_id,
        &observer.impls.generated_value_key_to_id
    ));
    assert!(Rc::ptr_eq(
        &solver.impls.application_key_to_id,
        &observer.impls.application_key_to_id
    ));
    assert_eq!(solver.impls.data.len(), 1);
    assert!(solver.fn_collector.new_elements.is_empty());
    assert_eq!(observer.impls.data.len(), 1);
    assert_eq!(retained.impls.data.len(), 4);
    assert_eq!(retained.impls.application_key_to_id[&private_key], id);
    // The next insertion reuses the rolled-back local ID.
    let imp = solver.impls.data[0].clone();
    assert_eq!(solver.impls.add_concrete_struct(private_key, imp), id);
}

#[test]
fn improvement_head_filter_never_discards_a_successful_same_type_match() {
    use crate::{
        module::LocalTypeDefId,
        std::{array_type::array_type, logic::bool_type},
        types::r#type::{FnArgType, SubscriptMemberType, SubscriptResultConvention, store_types},
    };
    let span = Location::new_synthesized();
    let var = Type::variable_id;
    let named = |index, parameter| {
        Type::named(
            TypeDefId::new(ModuleId::new(u32::MAX - 1), LocalTypeDefId::new(index)),
            vec![parameter],
        )
    };
    let callback =
        |args: Vec<Type>, ret, effects| Type::function_type(FnType::new_by_val(args, ret, effects));
    let recursive = store_types(&[TypeKind::Variant(vec![
        (ustr::ustr("End"), Type::unit()),
        (ustr::ustr("Next"), Type::new_local(0)),
    ])])[0];
    let subscript = Type::subscript_type(SubscriptType {
        args: vec![FnArgType::new_by_val(var(0))],
        ret: var(1),
        ref_member: Some(SubscriptMemberType::new(
            EffType::empty(),
            SubscriptResultConvention::AddressorPlace,
        )),
        mut_member: None,
    });
    let types = vec![
        var(0),
        var(1),
        Type::never(),
        int_type(),
        bool_type(),
        array_type(int_type()),
        array_type(var(0)),
        Type::unit(),
        Type::tuple([var(0)]),
        Type::tuple([int_type()]),
        Type::tuple([int_type(), bool_type()]),
        Type::record(vec![(ustr::ustr("x"), var(0))]),
        Type::variant(vec![(ustr::ustr("Some"), var(0))]),
        recursive,
        callback(vec![], Type::never(), EffType::empty()),
        callback(vec![], int_type(), effect(PrimitiveEffect::Read)),
        callback(vec![var(0)], var(1), EffType::empty()),
        callback(vec![int_type(), int_type()], int_type(), EffType::empty()),
        Type::function_type(FnType::new_mut_resolved(
            [(int_type(), true)],
            int_type(),
            EffType::empty(),
        )),
        named(0, int_type()),
        named(0, var(0)),
        named(1, int_type()),
        subscript,
    ];
    let mut pruned = 0;
    for &candidate in &types {
        for &input in &types {
            let keep = input_head_may_match(candidate, input);
            pruned += usize::from(!keep);
            let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
            let accepted = inference
                .unify_same_type_with_sub_effects(candidate, span, input, span)
                .is_ok();
            assert!(
                !accepted || keep,
                "discarded a compatible pair: {candidate:?}, {input:?}"
            );
        }
    }
    assert!(pruned > types.len());
    // Never is a subtype of int, but cannot match an int impl head by equality.
    assert!(!input_head_may_match(Type::never(), int_type()));
    // Candidate variables have their own namespace; their numeric IDs must
    // not be looked up in the application's inference table.
    assert!(input_head_may_match(var(0), int_type()));
    assert!(input_head_may_match(int_type(), var(0)));
    // Matching heads are only permission to probe: nested incompatibilities
    // and independently quantified effects still need the real comparator.
    assert!(input_head_may_match(
        named(0, int_type()),
        named(0, bool_type())
    ));
}

#[test]
fn pending_impls_block_negative_answers_only() {
    use crate::{
        module::{PendingImpl, PendingImpls},
        std::{array_type::array_type, logic::bool_type},
    };
    let span = Location::new_synthesized();
    let session = CompilerSession::new();
    let modules = session.raw_modules();
    let module_id = modules.next_id();
    let mut module = new_module_using_std(module_id, Path::single_str("$pending_test"));
    let default_trait = trait_solver_from_module!(module, modules).std_trait_id("Default");
    let pair = |first| Type::tuple([first, int_type()]);
    let mut arena = NodeArena::default();
    let mut solver = trait_solver_from_module!(module, modules);
    assert!(
        solver
            .solve_outputs(default_trait, &[pair(int_type())], span, &mut arena)
            .is_ok()
    );
    drop(solver);

    let set_pending = |module: &mut Module, input_tys| {
        let pending = Rc::new(PendingImpls::new(vec![PendingImpl {
            index: ImplAstIndex::new(7),
            trait_id: default_trait,
            input_tys,
        }]));
        module.impls.pending = pending.clone();
        pending
    };
    let pending = set_pending(&mut module, Some(vec![pair(Type::variable_id(0))]));
    let mut solver = trait_solver_from_module!(module, modules);
    // A visible impl proves this answer whatever is pending.
    assert!(
        solver
            .solve_outputs(default_trait, &[array_type(int_type())], span, &mut arena)
            .is_ok()
    );
    assert!(pending.blockers().is_empty());
    // The pending impl may provide this application, so it is not derived.
    assert!(
        solver
            .solve_outputs(default_trait, &[pair(int_type())], span, &mut arena)
            .is_err()
    );
    assert_eq!(pending.blockers(), vec![ImplAstIndex::new(7)]);
    drop(solver);

    // Probes share the pending impls of the module they read.
    let pending = set_pending(&mut module, Some(vec![pair(bool_type())]));
    let mut probe = TraitSolverProbe::from_module(&module, modules);
    let mut arena = NodeArena::default();
    assert!(probe.with_solver(|solver| {
        solver
            .solve_outputs(default_trait, &[pair(bool_type())], span, &mut arena)
            .is_err()
    }));
    assert_eq!(pending.blockers(), vec![ImplAstIndex::new(7)]);
    drop(probe);

    // An absent concrete impl that the pending impl may fill is blocked.
    let pending = set_pending(&mut module, Some(vec![pair(bool_type())]));
    let solver = trait_solver_from_module!(module, modules);
    assert!(!solver.has_concrete_impl(&ConcreteTraitImplKey::new(
        default_trait,
        vec![pair(bool_type())]
    )));
    assert_eq!(pending.blockers(), vec![ImplAstIndex::new(7)]);
    drop(solver);

    // A headerless pending impl is another candidate for improvement: the single visible
    // candidate, `impl<A> Slice for <Self = [A] |-> Output = [A]>`, no longer determines the
    // output.
    let slice_trait = trait_solver_from_module!(module, modules).std_trait_id("Slice");
    let improves = |module: &mut Module| {
        let mut solver = trait_solver_from_module!(module, modules);
        let mut ty_inf = UnifiedTypeInference::new_with_ty_vars(0);
        let element = Type::variable(ty_inf.fresh_type_var());
        let output = Type::variable(ty_inf.fresh_type_var());
        solver
            .try_improve_trait_application(
                &mut ty_inf,
                slice_trait,
                &[array_type(element)],
                Some(&[output]),
                Some(&[]),
                ConstraintAssumptions::all(&[]),
                span,
                &mut NodeArena::default(),
            )
            .unwrap();
        drop(solver);
        ty_inf.substitute_in_type(output) == array_type(ty_inf.substitute_in_type(element))
    };
    module.impls.pending = Rc::default();
    assert!(improves(&mut module));
    let pending = Rc::new(PendingImpls::new(vec![PendingImpl {
        index: ImplAstIndex::new(7),
        trait_id: slice_trait,
        input_tys: None,
    }]));
    module.impls.pending = pending.clone();
    assert!(!improves(&mut module));
    assert_eq!(pending.blockers(), vec![ImplAstIndex::new(7)]);
}

/// Type-solver fixture with an unresolved effect, not an executable host entry.
#[derive(Clone)]
struct UnexecutedEffectMethod;

impl Callable for UnexecutedEffectMethod {
    fn call(&self, _: Vec<ValOrMut>, _: &mut EvalCtx) -> EvalResult {
        unreachable!("the effect-cache test only queries method types")
    }
    fn runtime_argument_passing(&self) -> Option<&[ArgConvention]> {
        Some(&[ArgConvention::Let])
    }
    fn format_ind(
        &self,
        f: &mut fmt::Formatter,
        _: &[ELocalDecl],
        _: &ModuleEnv,
        _: usize,
        _: usize,
    ) -> fmt::Result {
        f.write_str("UnexecutedEffectMethod")
    }
}

#[test]
fn open_generated_value_dictionaries_ignore_caller_local_variable_numbers() {
    let session = CompilerSession::new();
    let modules = session.raw_modules();
    let module_id = modules.next_id();
    let mut module = new_module_using_std(module_id, Path::single_str("$open_dictionary_test"));
    let current_def_table = &module.def_table;
    let current_type_items = CurrentTypeItems::new(
        module::ModuleIdentity {
            id: module_id,
            path: &module.path,
        },
        &module.type_aliases,
        module.type_defs.as_slice(),
        module.traits.as_slice(),
        &module.projection_subscripts,
        &module.environment,
    );
    let value_trait_id = modules
        .get(STD_MODULE_ID)
        .unwrap()
        .module()
        .unwrap()
        .get_trait_id_str(VALUE_TRAIT_NAME)
        .unwrap();
    let method_count = modules
        .get(STD_MODULE_ID)
        .unwrap()
        .module()
        .unwrap()
        .trait_def(value_trait_id)
        .methods
        .len();
    let methods = (0..method_count)
        .map(LocalFunctionId::from_index)
        .collect::<Vec<_>>();
    let mut deps = FxHashSet::default();
    let mut solver = TraitSolver::new(
        current_type_items,
        &mut module.impls,
        current_def_table,
        &mut deps,
        CurrentProjectionSubscriptTypes::empty(),
        PendingFunctionCollector::new(method_count),
        modules,
    );
    let open_type = |variable| {
        Type::tuple([Type::function_type(FnType::new_by_val(
            [int_type()],
            Type::variable_id(variable),
            EffType::empty(),
        ))])
    };
    let first = solver
        .materialize_generated_value_impl_from_methods(
            value_trait_id,
            &[open_type(3)],
            Location::new_synthesized(),
            methods.clone(),
        )
        .unwrap()
        .0;
    let second = solver
        .materialize_generated_value_impl_from_methods(
            value_trait_id,
            &[open_type(19)],
            Location::new_synthesized(),
            methods,
        )
        .unwrap()
        .0;

    assert_eq!(
        first, second,
        "alpha-equivalent callers must reuse one module-owned dictionary definition"
    );
}

#[test]
fn unmaterialized_output_cache_does_not_reuse_constrained_effects() {
    let session = CompilerSession::new();
    let modules = session.raw_modules();
    let module_id = modules.next_id();
    let mut module = Module::new(module_id, Path::single_str("$trait_solver_test"));
    let trait_id = TraitId::new(
        module_id,
        module.add_trait(
            Trait::new_with_self_input_type(
                "UnconstrainedEffect",
                "Test trait with an application-selected associated effect.",
                ["Output"],
                [(
                    "run",
                    CallableDefinition::new_infer_quantifiers(
                        FnType::new_by_val(
                            [Type::variable_id(0)],
                            Type::variable_id(1),
                            EffType::single_variable_id(0),
                        ),
                        ["value"],
                        "Returns its value.",
                    ),
                )],
            )
            .with_output_effects(["E"]),
        ),
    );
    module.add_blanket_impl_with_effects_no_locals(
        trait_id,
        BlanketTraitImplSubKey {
            input_tys: vec![int_type()],
            ty_var_count: 0,
            eff_var_count: 1,
            constraints: vec![],
        },
        [int_type()],
        [EffType::single_variable_id(0)],
        [],
        // This solver fixture has unresolved effects and is never executed.
        [Box::new(UnexecutedEffectMethod) as Function],
    );

    let current_def_table = &module.def_table;
    let function_count = module.functions.len();
    let current_type_items = CurrentTypeItems::new(
        module::ModuleIdentity {
            id: module_id,
            path: &module.path,
        },
        &module.type_aliases,
        module.type_defs.as_slice(),
        module.traits.as_slice(),
        &module.projection_subscripts,
        &module.environment,
    );
    let mut deps = FxHashSet::default();
    let mut solver = TraitSolver::new(
        current_type_items,
        &mut module.impls,
        current_def_table,
        &mut deps,
        CurrentProjectionSubscriptTypes::empty(),
        PendingFunctionCollector::new(function_count),
        modules,
    );
    let mut arena = NodeArena::default();
    let read = effect(PrimitiveEffect::Read);

    let (_, output_effs) = solver
        .solve_application_outputs(
            trait_id,
            &[int_type()],
            &[int_type()],
            from_ref(&read),
            Location::new_synthesized(),
            &mut arena,
        )
        .unwrap();
    // The implementation's own effect takes its least solution, which the request includes.
    assert_eq!(output_effs, vec![EffType::empty()]);

    let (_, output_effs) = solver
        .solve_outputs(
            trait_id,
            &[int_type()],
            Location::new_synthesized(),
            &mut arena,
        )
        .unwrap();
    assert_eq!(output_effs, vec![EffType::empty()]);
    let cached = solver
        .cached_unmaterialized_outputs(trait_id, &[int_type()])
        .expect("the unconstrained query must populate the output cache");
    assert_eq!(cached.output_effs, vec![EffType::empty()]);
}
