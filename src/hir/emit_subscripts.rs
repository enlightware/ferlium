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
        SubscriptMemberRole,
    },
    internal_compilation_error,
    module::{
        LocalFunctionId, LocalSubscriptId, Module,
        SubscriptDefinition as ModuleSubscriptDefinition, SubscriptMember as ModuleSubscriptMember,
        SubscriptSignature, Visibility, YieldProvenance, id::Id,
    },
    types::{mutability::MutType, r#type::FnArgType},
};

pub(super) fn predeclare_subscripts(
    output: &mut Module,
    source: &ast::DModule,
) -> Result<Vec<LocalSubscriptId>, InternalCompilationError> {
    let mut ids = Vec::with_capacity(source.subscripts.len());
    for subscript in &source.subscripts {
        validate_subscript_members(subscript)?;
        ids.push(add_empty_subscript_bundle(output, subscript)?);
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
                    kind: InvalidSubscriptDefinitionKind::DuplicateMember(SubscriptMemberRole::Ref,),
                    span: member.span,
                }));
            }
            ref_member_seen = true;
        }
        if member.mode.mut_member {
            if mut_member_seen {
                return Err(internal_compilation_error!(InvalidSubscriptDefinition {
                    subject: SubscriptDefinitionSubject::Subscript(subscript.name.0),
                    kind: InvalidSubscriptDefinitionKind::DuplicateMember(SubscriptMemberRole::Mut,),
                    span: member.span,
                }));
            }
            mut_member_seen = true;
        }
    }
    Ok(())
}

fn subscript_signature(
    subscript: &ast::DSubscriptDefinition,
) -> Result<SubscriptSignature, InternalCompilationError> {
    let args = subscript
        .args
        .iter()
        .map(|arg| {
            let Some((mut_ty, ty, _span)) = arg.ty else {
                return Err(internal_compilation_error!(InvalidSubscriptDefinition {
                    subject: SubscriptDefinitionSubject::Subscript(subscript.name.0),
                    kind: InvalidSubscriptDefinitionKind::ParameterMissingType,
                    span: arg.name.1,
                }));
            };
            Ok(FnArgType::new(ty, mut_ty.unwrap_or_else(MutType::constant)))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SubscriptSignature {
        args,
        ret: subscript.ret_ty.0,
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
    ast::DModuleFunction {
        visibility: Visibility::Module,
        name: (
            format!("$subscript${}${suffix}", subscript.name.0).into(),
            member.span,
        ),
        generic_params: subscript.generic_params.clone(),
        args: subscript.args.clone(),
        args_span: subscript.args_span,
        ret_ty: Some(subscript.ret_ty),
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
