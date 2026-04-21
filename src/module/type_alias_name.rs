// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use ustr::Ustr;

use crate::{
    format::FormatWith,
    module::{Module, ModuleEnv},
    r#type::{NamedType, Type, TypeAliasEntry, TypeKind, TypeSubstitution, TypeVar},
};

#[derive(Debug, Clone)]
pub(crate) struct GenericAliasName {
    pub name: Ustr,
    pub rendered: String,
}

pub(crate) fn find_generic_alias_name(
    module: &Module,
    ty: Type,
    env: &ModuleEnv<'_>,
) -> Option<GenericAliasName> {
    module.type_aliases.type_entries().find_map(|alias| {
        (!alias.param_names.is_empty())
            .then(|| render_generic_alias_name(alias, ty, env))
            .flatten()
    })
}

pub(crate) fn render_generic_alias_name(
    alias: &TypeAliasEntry,
    ty: Type,
    env: &ModuleEnv<'_>,
) -> Option<GenericAliasName> {
    let mut subst = TypeSubstitution::default();
    match_alias_type(alias.ty, ty, alias.ty_var_count, &mut subst).then(|| {
        let args = (0..alias.ty_var_count)
            .map(|i| subst.get(&TypeVar::new(i)).copied())
            .collect::<Option<Vec<_>>>()?;
        let rendered = if args.is_empty() {
            alias.name.to_string()
        } else {
            format!(
                "{}<{}>",
                alias.name,
                args.iter()
                    .map(|ty| ty.format_with(env).to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        Some(GenericAliasName {
            name: alias.name,
            rendered,
        })
    })?
}

pub(crate) fn match_alias_type(
    pattern: Type,
    actual: Type,
    ty_var_count: u32,
    subst: &mut TypeSubstitution,
) -> bool {
    let pattern_data = pattern.data();
    let actual_data = actual.data();
    use TypeKind::*;
    match (&*pattern_data, &*actual_data) {
        (Variable(var), _) if var.name() < ty_var_count => {
            if let Some(existing) = subst.get(var) {
                *existing == actual
            } else {
                subst.insert(*var, actual);
                true
            }
        }
        (Variable(lhs), Variable(rhs)) => lhs == rhs,
        (Never, Never) => true,
        (Tuple(lhs), Tuple(rhs)) => {
            lhs.len() == rhs.len()
                && lhs
                    .iter()
                    .zip(rhs.iter())
                    .all(|(lhs, rhs)| match_alias_type(*lhs, *rhs, ty_var_count, subst))
        }
        (Record(lhs), Record(rhs)) => {
            lhs.len() == rhs.len()
                && lhs
                    .iter()
                    .zip(rhs.iter())
                    .all(|((lhs_name, lhs_ty), (rhs_name, rhs_ty))| {
                        lhs_name == rhs_name
                            && match_alias_type(*lhs_ty, *rhs_ty, ty_var_count, subst)
                    })
        }
        (Variant(lhs), Variant(rhs)) => {
            lhs.len() == rhs.len()
                && lhs
                    .iter()
                    .zip(rhs.iter())
                    .all(|((lhs_name, lhs_ty), (rhs_name, rhs_ty))| {
                        lhs_name == rhs_name
                            && match_alias_type(*lhs_ty, *rhs_ty, ty_var_count, subst)
                    })
        }
        (Native(lhs), Native(rhs)) => {
            lhs.bare_ty == rhs.bare_ty
                && lhs.arguments.len() == rhs.arguments.len()
                && lhs
                    .arguments
                    .iter()
                    .zip(rhs.arguments.iter())
                    .all(|(lhs, rhs)| match_alias_type(*lhs, *rhs, ty_var_count, subst))
        }
        (Function(lhs), Function(rhs)) => {
            lhs.args.len() == rhs.args.len()
                && lhs.effects == rhs.effects
                && lhs.args.iter().zip(rhs.args.iter()).all(|(lhs, rhs)| {
                    lhs.mut_ty == rhs.mut_ty
                        && match_alias_type(lhs.ty, rhs.ty, ty_var_count, subst)
                })
                && match_alias_type(lhs.ret, rhs.ret, ty_var_count, subst)
        }
        (
            Named(NamedType {
                def: lhs_def,
                params: lhs_params,
            }),
            Named(NamedType {
                def: rhs_def,
                params: rhs_params,
            }),
        ) => {
            lhs_def == rhs_def
                && lhs_params.len() == rhs_params.len()
                && lhs_params
                    .iter()
                    .zip(rhs_params.iter())
                    .all(|(lhs, rhs)| match_alias_type(*lhs, *rhs, ty_var_count, subst))
        }
        _ => false,
    }
}
