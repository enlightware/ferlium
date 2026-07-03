// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    Location, ast,
    compiler::error::{
        InternalCompilationError, InvalidSubscriptDefinitionKind, SubscriptDefinitionSubject,
    },
    internal_compilation_error,
    module::{
        LocalFunctionId, LocalSubscriptId, Module, ModuleEnv, ProjectionKey, ProjectionOrigin,
        SubscriptDefinition as ModuleSubscriptDefinition, SubscriptMember as ModuleSubscriptMember,
        SubscriptMemberKind, SubscriptSignature, Visibility, YieldProvenance, id::Id,
    },
    types::{
        mutability::MutType,
        r#type::{FnArgType, Type, TypeKind},
    },
};

pub(super) fn predeclare_subscripts(
    output: &mut Module,
    source: &ast::DModule,
    others: &crate::Modules,
) -> Result<Vec<LocalSubscriptId>, InternalCompilationError> {
    let mut ids = Vec::with_capacity(source.subscripts.len());
    for subscript in &source.subscripts {
        validate_subscript_members(subscript)?;
        if let Some(key) = projection_key_for_subscript(output, others, subscript)? {
            let env = ModuleEnv::new(output, others);
            if output.get_projection_subscript(key).is_some()
                || env.projection_subscript(key).is_some()
            {
                return Err(internal_compilation_error!(InvalidSubscriptDefinition {
                    subject: SubscriptDefinitionSubject::Subscript(subscript.name.0),
                    kind: InvalidSubscriptDefinitionKind::DuplicateProjection,
                    span: subscript.name.1,
                }));
            }
            ids.push(add_empty_projection_subscript_bundle(output, subscript)?);
            let id = *ids.last().expect("just pushed subscript id");
            output.add_projection_subscript(
                key,
                id,
                subscript.visibility,
                ProjectionOrigin::Explicit,
            );
        } else {
            ids.push(add_empty_subscript_bundle(output, subscript)?);
        }
    }
    Ok(ids)
}

fn validate_subscript_members(
    subscript: &ast::DSubscriptDefinition,
) -> Result<(), InternalCompilationError> {
    if subscript.members.is_empty() {
        return Err(internal_compilation_error!(InvalidSubscriptDefinition {
            subject: SubscriptDefinitionSubject::Subscript(subscript.name.0),
            kind: InvalidSubscriptDefinitionKind::EmptyBundle,
            span: subscript.span,
        }));
    }

    let mut ref_member_seen = false;
    let mut mut_member_seen = false;
    for member in &subscript.members {
        if member.mode.ref_member && member.mode.mut_member && subscript.members.len() > 1 {
            return Err(internal_compilation_error!(InvalidSubscriptDefinition {
                subject: SubscriptDefinitionSubject::Subscript(subscript.name.0),
                kind: InvalidSubscriptDefinitionKind::SharedMemberCombinedWithSeparateMembers,
                span: member.span,
            }));
        }
        if member.mode.ref_member {
            if ref_member_seen {
                return Err(internal_compilation_error!(InvalidSubscriptDefinition {
                    subject: SubscriptDefinitionSubject::Subscript(subscript.name.0),
                    kind: InvalidSubscriptDefinitionKind::DuplicateMember(SubscriptMemberKind::Ref,),
                    span: member.span,
                }));
            }
            ref_member_seen = true;
        }
        if member.mode.mut_member {
            if mut_member_seen {
                return Err(internal_compilation_error!(InvalidSubscriptDefinition {
                    subject: SubscriptDefinitionSubject::Subscript(subscript.name.0),
                    kind: InvalidSubscriptDefinitionKind::DuplicateMember(SubscriptMemberKind::Mut,),
                    span: member.span,
                }));
            }
            mut_member_seen = true;
        }
    }
    Ok(())
}

fn projection_key_for_subscript(
    output: &Module,
    others: &crate::Modules,
    subscript: &ast::DSubscriptDefinition,
) -> Result<Option<ProjectionKey>, InternalCompilationError> {
    let Some((receiver_ty, receiver_span)) = validate_projection_receiver_binding(subscript)?
    else {
        return Ok(None);
    };
    let env = ModuleEnv::new(output, others);
    let receiver_type_def =
        validate_projection_receiver_type(env, receiver_ty, subscript, receiver_span)?;
    reject_accessible_structural_projection_conflict(
        env,
        receiver_ty,
        subscript.name,
        receiver_span,
    )?;
    Ok(Some(ProjectionKey::nominal(
        receiver_type_def,
        subscript.name.0,
    )))
}

fn validate_projection_receiver_type(
    env: ModuleEnv<'_>,
    receiver_ty: Type,
    subscript: &ast::DSubscriptDefinition,
    receiver_span: Location,
) -> Result<crate::module::TypeDefId, InternalCompilationError> {
    let field = subscript.name;
    let TypeKind::Named(named) = &*receiver_ty.data() else {
        return Err(internal_compilation_error!(InvalidSubscriptDefinition {
            subject: SubscriptDefinitionSubject::Subscript(field.0),
            kind: InvalidSubscriptDefinitionKind::ProjectionReceiverMustBeNominal,
            span: Location::fuse([field.1, receiver_span]).unwrap_or(field.1),
        }));
    };

    let source_params = subscript.generic_params.type_params();
    let expected_params = env.type_def_param_names(named.def).collect::<Vec<_>>();
    let expected_effect_param_count = env.type_def_effect_param_count(named.def);
    let params_match = named.params.len() == expected_params.len()
        && source_params.len() == expected_params.len()
        && named.effect_params.is_empty()
        && expected_effect_param_count == 0
        && subscript.generic_params.effect_params().is_empty()
        && named
            .params
            .iter()
            .enumerate()
            .all(|(index, ty)| match &*ty.data() {
                TypeKind::Variable(var) => {
                    var.name() as usize == index && source_params[index].0 == expected_params[index]
                }
                _ => false,
            });
    if params_match {
        return Ok(named.def);
    }
    Err(internal_compilation_error!(InvalidSubscriptDefinition {
        subject: SubscriptDefinitionSubject::Subscript(field.0),
        kind: InvalidSubscriptDefinitionKind::ProjectionReceiverGenericParametersMismatch,
        span: Location::fuse([field.1, receiver_span]).unwrap_or(field.1),
    }))
}

fn validate_projection_receiver_binding(
    subscript: &ast::DSubscriptDefinition,
) -> Result<Option<(Type, Location)>, InternalCompilationError> {
    let Some((receiver_ty, receiver_span)) = subscript.projection_receiver else {
        return Ok(None);
    };
    if subscript.args.is_empty() {
        return Err(internal_compilation_error!(InvalidSubscriptDefinition {
            subject: SubscriptDefinitionSubject::Subscript(subscript.name.0),
            kind: InvalidSubscriptDefinitionKind::ProjectionMissingReceiverParameter,
            span: subscript.args_span,
        }));
    };
    if subscript.args.len() > 1 {
        let extra_arg = &subscript.args[1];
        return Err(internal_compilation_error!(InvalidSubscriptDefinition {
            subject: SubscriptDefinitionSubject::Subscript(subscript.name.0),
            kind: InvalidSubscriptDefinitionKind::ProjectionUnexpectedParameter,
            span: extra_arg.name.1,
        }));
    }
    let receiver_arg = &subscript.args[0];
    if let Some((_mut_ty, _ty, ty_span)) = receiver_arg.ty {
        return Err(internal_compilation_error!(InvalidSubscriptDefinition {
            subject: SubscriptDefinitionSubject::Subscript(subscript.name.0),
            kind: InvalidSubscriptDefinitionKind::ProjectionReceiverParameterMustBeUntyped,
            span: ty_span,
        }));
    }
    Ok(Some((receiver_ty, receiver_span)))
}

fn reject_accessible_structural_projection_conflict(
    env: ModuleEnv<'_>,
    receiver_ty: Type,
    field: ast::UstrSpan,
    receiver_span: Location,
) -> Result<(), InternalCompilationError> {
    let TypeKind::Named(named) = &*receiver_ty.data() else {
        return Ok(());
    };
    let type_def = env.type_def(named.def);
    if type_def.has_private_repr() {
        return Ok(());
    }
    let shape = type_def.instantiated_shape_with_effects(&named.params, &named.effect_params);
    if shape.data().as_record().is_some_and(|record| {
        record
            .iter()
            .any(|(structural_field, _)| *structural_field == field.0)
    }) {
        return Err(internal_compilation_error!(InvalidSubscriptDefinition {
            subject: SubscriptDefinitionSubject::Subscript(field.0),
            kind: InvalidSubscriptDefinitionKind::ProjectionConflictsWithStructuralField,
            span: Location::fuse([field.1, receiver_span]).unwrap_or(field.1),
        }));
    }
    Ok(())
}

fn subscript_signature(
    subscript: &ast::DSubscriptDefinition,
) -> Result<SubscriptSignature, InternalCompilationError> {
    let provisional_ret = || {
        subscript
            .ret_ty
            .map(|(ret_ty, _)| ret_ty)
            .unwrap_or_else(|| Type::variable_id(0))
    };
    if let Some((receiver_ty, _)) = validate_projection_receiver_binding(subscript)? {
        return Ok(SubscriptSignature {
            args: vec![FnArgType::new_by_val(receiver_ty)],
            ret: provisional_ret(),
            generic_params: subscript.generic_params.type_params().to_vec(),
            generic_effect_params: subscript.generic_params.effect_params().to_vec(),
            arg_names: vec![subscript.args[0].name.0],
            constraints: subscript.where_clause.clone(),
            doc: subscript.doc.clone(),
        });
    }
    let args = subscript
        .args
        .iter()
        .enumerate()
        .map(|(index, arg)| {
            if let Some((mut_ty, ty, _span)) = arg.ty {
                FnArgType::new(ty, mut_ty.unwrap_or_else(MutType::constant))
            } else {
                // Source subscripts are predeclared before their SCC is emitted.
                // Placeholder type vars start at 1 so var 0 remains available for a
                // provisional omitted return; all placeholders are replaced by
                // real fresh variables in emit_functions before real consumption.
                FnArgType::new(
                    Type::variable_id((index + 1) as u32),
                    MutType::variable_id(index as u32),
                )
            }
        })
        .collect::<Vec<_>>();
    Ok(SubscriptSignature {
        args,
        ret: provisional_ret(),
        generic_params: subscript.generic_params.type_params().to_vec(),
        generic_effect_params: subscript.generic_params.effect_params().to_vec(),
        arg_names: subscript.args.iter().map(|arg| arg.name.0).collect(),
        constraints: subscript.where_clause.clone(),
        doc: subscript.doc.clone(),
    })
}

pub(super) fn synthetic_subscript_member_function(
    subscript: &ast::DSubscriptDefinition,
    member: &ast::SubscriptMember<ast::Desugared>,
) -> ast::DModuleFunction {
    let suffix = member_function_suffix(member);
    let args = if let Some((receiver_ty, receiver_span)) = subscript.projection_receiver {
        let mut args = subscript.args.clone();
        let receiver_arg = args
            .first_mut()
            .expect("projection subscript receiver binding should be validated before emission");
        let receiver_mut_ty = member.mode.mut_member.then_some(MutType::mutable());
        receiver_arg.ty = Some((receiver_mut_ty, receiver_ty, receiver_span));
        args
    } else {
        subscript.args.clone()
    };
    ast::DModuleFunction {
        visibility: Visibility::Module,
        name: (
            format!("$subscript${}${suffix}", subscript.name.0).into(),
            member.span,
        ),
        generic_params: subscript.generic_params.clone(),
        args,
        args_span: subscript.args_span,
        ret_ty: subscript.ret_ty,
        where_clause: subscript.where_clause.clone(),
        attributes: Vec::new(),
        body: member.body,
        span: member.span,
        doc: subscript.doc.clone(),
    }
}

fn member_function_suffix(member: &ast::SubscriptMember<ast::Desugared>) -> &'static str {
    if member.mode.ref_member && member.mode.mut_member {
        "ref_mut"
    } else if member.mode.ref_member {
        "ref"
    } else {
        "mut"
    }
}

fn add_empty_subscript_bundle(
    output: &mut Module,
    subscript: &ast::DSubscriptDefinition,
) -> Result<LocalSubscriptId, InternalCompilationError> {
    Ok(output.add_subscript(
        subscript.name.0,
        ModuleSubscriptDefinition {
            signature: subscript_signature(subscript)?,
            ref_member: None,
            mut_member: None,
        },
        subscript.visibility,
    ))
}

fn add_empty_projection_subscript_bundle(
    output: &mut Module,
    subscript: &ast::DSubscriptDefinition,
) -> Result<LocalSubscriptId, InternalCompilationError> {
    Ok(output.add_subscript_anonymous(ModuleSubscriptDefinition {
        signature: subscript_signature(subscript)?,
        ref_member: None,
        mut_member: None,
    }))
}

pub(super) fn attach_subscript_member(
    output: &mut Module,
    subscript_id: LocalSubscriptId,
    function: LocalFunctionId,
    is_mut_member: bool,
    provenance: YieldProvenance,
    span: Location,
) -> Result<(), InternalCompilationError> {
    let member = ModuleSubscriptMember {
        function,
        provenance,
    };
    let subscript_name = output.get_subscript_name_by_id(subscript_id);
    let subscript = output
        .subscripts
        .get_mut(subscript_id.as_index())
        .expect("subscript id should be valid");
    let slot = if is_mut_member {
        &mut subscript.mut_member
    } else {
        &mut subscript.ref_member
    };
    if slot.is_some() {
        return Err(internal_compilation_error!(InvalidSubscriptDefinition {
            subject: subscript_name.map_or(
                SubscriptDefinitionSubject::AddressorFunction(None),
                SubscriptDefinitionSubject::Subscript,
            ),
            kind: InvalidSubscriptDefinitionKind::DuplicateAttachedMember,
            span,
        }));
    }
    *slot = Some(member);
    Ok(())
}
