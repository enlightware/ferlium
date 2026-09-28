// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Default bodies and forwarding instances created before source std is available.

use crate::{
    Location,
    containers::b,
    hir::{
        self, CallArgument, ENodeArena, FnInstData, NodeArena, NodeKind,
        dictionary::{DictionaryReq, EvidenceBinding, EvidenceBindingSource},
        function::{CallableDefinition, ScriptFunction, arg_conventions_for_args},
        hir_syn::*,
    },
    module::{
        EvidenceBindingId, ExtraParameterId, FunctionId, LocalDecl, LocalDeclId, Module,
        ModuleFunction, PendingFunctionBody, TraitId, Visibility, id::Id,
    },
    std::{
        logic::bool_type,
        value::{VALUE_EQ_METHOD_INDEX, VALUE_NE_METHOD_INDEX},
    },
    types::{
        r#trait::{Trait, TraitDefaultMethod, TraitDictionaryEntryIndex},
        r#type::{CallImplType, Type},
        type_scheme::{PubTypeConstraint, TypeScheme},
    },
};

pub(crate) fn register_value_ne(module: &mut Module, trait_id: TraitId) {
    let ty = Type::variable_id(0);
    let trait_def = module.trait_def(trait_id);
    let mut definition = trait_def.methods[VALUE_NE_METHOD_INDEX.as_index()]
        .1
        .clone();
    let requirement = DictionaryReq::new_trait_impl(trait_id, vec![ty], vec![], vec![]);
    definition.ty_scheme = TypeScheme::new_infer_quantifiers_with_constraints(
        definition.ty_scheme.ty.clone(),
        vec![PubTypeConstraint::new_have_trait(
            trait_id,
            vec![ty],
            vec![],
            vec![],
            Location::new_synthesized(),
        )],
    );
    let dictionary_ty = trait_def.get_dictionary_type_for_tys(&[ty], &[], &[]);
    let eq_ty = trait_def.methods[VALUE_EQ_METHOD_INDEX.as_index()]
        .1
        .ty_scheme
        .ty
        .clone();
    let arena = &mut module.hir_arena;
    let dictionary = alloc_synth(
        arena,
        NodeKind::LoadDictionary(hir::LoadDictionary {
            extra_parameter: EvidenceBindingId::from_index(0),
        }),
        dictionary_ty,
    );
    let args = (0..2)
        .map(|index| alloc_synth(arena, load_local(LocalDeclId::from_index(index)), ty))
        .collect();
    let eq = alloc_synth(
        arena,
        call_dictionary_function(
            dictionary,
            TraitDictionaryEntryIndex::from_index(VALUE_EQ_METHOD_INDEX.as_index()),
            CallArgument::from_values_and_passing(args, arg_conventions_for_args(&eq_ty.args)),
            definition.arg_names.clone(),
            CallImplType::value(eq_ty),
        ),
        bool_type(),
    );
    let yes = alloc_synth(arena, native(true), bool_type());
    let no = alloc_synth(arena, native(false), bool_type());
    let root = alloc_synth(
        arena,
        NodeKind::Case(b(hir::Case {
            value: eq,
            alternatives: vec![(hir::value::LiteralValue::new_native(true), no)],
            default: yes,
        })),
        bool_type(),
    );
    let locals = definition.gen_locals_no_bounds(
        std::iter::repeat(Location::new_synthesized()),
        Location::new_synthesized(),
    );
    let mut function = ModuleFunction::new_elaborated(
        definition.clone(),
        b(ScriptFunction::new(root, 2)),
        arg_conventions_for_args(&definition.ty_scheme.ty.args),
        None,
        locals.into_iter().map(LocalDecl::into_elaborated).collect(),
    );
    function.evidence_bindings = vec![EvidenceBinding {
        requirement,
        source: EvidenceBindingSource::Parameter(ExtraParameterId::from_index(0)),
    }];
    let id = module.add_function_with_visibility(
        ustr::ustr("@Value::ne#default"),
        function,
        Visibility::Module,
    );
    module.traits[trait_id.index.as_index()].default_methods[VALUE_NE_METHOD_INDEX.as_index()] =
        Some(TraitDefaultMethod {
            function: FunctionId::new(module.module_id(), id),
        });
}

/// Forward a generated entry to a checked default. Evidence is supplied by normal elaboration.
fn pending_default_call(
    function: FunctionId,
    definition: &CallableDefinition,
    requirement: DictionaryReq,
) -> (PendingFunctionBody, Vec<LocalDecl>) {
    let mut arena = NodeArena::default();
    let span = Location::new_synthesized();
    let locals = definition.gen_locals_no_bounds(std::iter::repeat(span), span);
    let args = definition
        .ty_scheme
        .ty
        .args
        .iter()
        .enumerate()
        .map(|(index, arg)| {
            alloc_synth(
                &mut arena,
                load_local(LocalDeclId::from_index(index)),
                arg.ty,
            )
        })
        .collect();
    let mut call = static_apply(
        function,
        definition.ty_scheme.ty.clone(),
        CallArgument::from_values_and_passing(
            args,
            arg_conventions_for_args(&definition.ty_scheme.ty.args),
        ),
        span,
    );
    let NodeKind::StaticApply(app) = &mut call else {
        unreachable!()
    };
    app.inst_data = default_inst_data(requirement);
    let root = alloc_synth(&mut arena, call, definition.ty_scheme.ty.ret);
    (PendingFunctionBody::new(arena, root), locals)
}

/// Native registration has no pending-HIR phase. Its default entry receives self evidence
/// from the dictionary, after any blanket prerequisites.
pub(crate) fn native_default_call(
    function: FunctionId,
    mut definition: CallableDefinition,
    requirement: DictionaryReq,
    prerequisites: Vec<DictionaryReq>,
    dictionary_ty: Type,
    arena: &mut ENodeArena,
) -> ModuleFunction {
    let span = Location::new_synthesized();
    let locals = definition.gen_locals_no_bounds(std::iter::repeat(span), span);
    let args = definition
        .ty_scheme
        .ty
        .args
        .iter()
        .enumerate()
        .map(|(index, arg)| alloc_synth(arena, load_local(LocalDeclId::from_index(index)), arg.ty))
        .collect();
    let dictionary = alloc_synth(
        arena,
        NodeKind::LoadDictionary(hir::LoadDictionary {
            extra_parameter: EvidenceBindingId::from_index(prerequisites.len()),
        }),
        dictionary_ty,
    );
    let mut call = static_apply(
        function,
        definition.ty_scheme.ty.clone(),
        CallArgument::from_values_and_passing(
            args,
            arg_conventions_for_args(&definition.ty_scheme.ty.args),
        ),
        span,
    );
    let NodeKind::StaticApply(app) = &mut call else {
        unreachable!()
    };
    app.extra_arguments = vec![dictionary];
    app.inst_data = default_inst_data(requirement.clone());
    let root = alloc_synth(arena, call, definition.ty_scheme.ty.ret);
    let DictionaryReq::TraitImpl {
        trait_id,
        input_tys,
        output_tys,
        output_effs,
    } = &requirement
    else {
        unreachable!()
    };
    definition
        .ty_scheme
        .constraints
        .push(PubTypeConstraint::new_have_trait(
            *trait_id,
            input_tys.clone(),
            output_tys.clone(),
            output_effs.clone(),
            span,
        ));
    let count = definition.arg_names.len();
    let passing = arg_conventions_for_args(&definition.ty_scheme.ty.args);
    let mut result = ModuleFunction::new_elaborated(
        definition,
        b(ScriptFunction::new(root, count)),
        passing,
        None,
        locals.into_iter().map(LocalDecl::into_elaborated).collect(),
    );
    result.evidence_bindings = prerequisites
        .into_iter()
        .chain([requirement])
        .enumerate()
        .map(|(index, requirement)| EvidenceBinding {
            requirement,
            source: EvidenceBindingSource::Parameter(ExtraParameterId::from_index(index)),
        })
        .collect();
    result
}

/// Complete the trailing defaulted slots of a compiler-generated implementation.
/// The returned boundary distinguishes supplied bodies from forwarding instances.
pub(crate) fn complete_pending_methods(
    trait_def: &Trait,
    definitions: &[CallableDefinition],
    requirement: DictionaryReq,
    entries: &mut Vec<(PendingFunctionBody, Vec<LocalDecl>)>,
) -> usize {
    assert!(
        entries.len() <= definitions.len(),
        "too many generated impl methods"
    );
    let supplied = entries.len();
    for (index, definition) in definitions.iter().enumerate().skip(supplied) {
        let default = trait_def.default_methods[index]
            .as_ref()
            .expect("missing required generated impl method");
        assert!(
            trait_def.parent_constraints.is_empty() && trait_def.constraints.is_empty(),
            "compiler-generated default completion requires a self-only default contract"
        );
        entries.push(pending_default_call(
            default.function,
            definition,
            requirement.clone(),
        ));
    }
    supplied
}

fn default_inst_data(requirement: DictionaryReq) -> FnInstData {
    let DictionaryReq::TraitImpl {
        input_tys,
        output_tys,
        output_effs,
        ..
    } = &requirement
    else {
        unreachable!()
    };
    FnInstData {
        ty_args: input_tys.iter().chain(output_tys).copied().collect(),
        eff_args: output_effs.clone(),
        dicts_req: vec![requirement],
    }
}
