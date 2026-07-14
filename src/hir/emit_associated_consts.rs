// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::types::effects::EffType;
use crate::{
    FxHashSet, Location, ast,
    compiler::error::{
        InternalCompilationError, InvalidTraitAssociatedConstImplKind,
        InvalidTraitAssociatedConstImplKind::{Duplicate, Missing, Unknown},
    },
    hir::{Node, NodeArena, NodeId, hir_syn},
    hir::{
        function::{CallableDefinition, PendingScriptFunction},
        value::LiteralValue,
        value_dispatch::materialize_static_string,
    },
    internal_compilation_error,
    module::{LocalDecl, PendingModuleFunction, TraitId},
    std::value::{is_value_trait, value_layout_associated_const_values},
    types::{
        r#trait::Trait,
        trait_solver::TraitSolver,
        r#type::{FnType, Type, TypeKind},
        type_inference::unify::SubOrSameType,
    },
};

fn materialize_associated_const_literal(
    arena: &mut NodeArena,
    locals: &mut Vec<LocalDecl>,
    solver: &mut TraitSolver<'_>,
    value: &LiteralValue,
    ty: Type,
    span: Location,
) -> Result<NodeId, InternalCompilationError> {
    if let Some(value) = value.as_primitive_ty::<crate::std::string::StaticStr>() {
        debug_assert_eq!(ty, crate::std::string::string_type());
        return materialize_static_string(arena, locals, solver, value.as_str(), span);
    }

    match value {
        LiteralValue::Native(_) => Ok(arena.alloc(Node::new(
            hir_syn::immediate(value.clone()),
            ty,
            EffType::empty(),
            span,
        ))),
        LiteralValue::Tuple(values) => {
            let kind = ty.data().clone();
            let (member_tys, record) = match kind {
                TypeKind::Tuple(member_tys) => (member_tys, false),
                TypeKind::Record(fields) => (fields.into_iter().map(|(_, ty)| ty).collect(), true),
                _ => panic!("tuple literal metadata should have a tuple or record result type"),
            };
            assert_eq!(values.len(), member_tys.len());
            let nodes = values
                .iter()
                .zip(member_tys)
                .map(|(value, ty)| {
                    materialize_associated_const_literal(arena, locals, solver, value, ty, span)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let kind = if record {
                hir_syn::record(nodes)
            } else {
                hir_syn::tuple(nodes)
            };
            Ok(arena.alloc(Node::new(kind, ty, EffType::empty(), span)))
        }
    }
}

/// Build the authoritative runtime getter from canonical literal metadata and
/// the associated constant's declared result type.
pub(super) fn associated_const_getter(
    value: &LiteralValue,
    ty: Type,
    span: Location,
    solver: &mut TraitSolver<'_>,
) -> Result<PendingModuleFunction, InternalCompilationError> {
    let mut arena = NodeArena::default();
    let mut locals = Vec::new();
    let root =
        materialize_associated_const_literal(&mut arena, &mut locals, solver, value, ty, span)?;
    let definition = CallableDefinition::new_infer_quantifiers(
        FnType::new_by_val([], ty, EffType::empty()),
        [],
        "Compiler-generated associated constant getter.",
    );
    Ok(PendingModuleFunction::new(
        definition,
        PendingScriptFunction::new(arena, root, 0),
        None,
        locals,
    ))
}

/// Synthesize compiler-provided associated const values for source-emitted impls.
pub(super) fn emitted_associated_const_values(
    trait_id: TraitId,
    input_tys: &[Type],
    ty_var_count: u32,
    span: Location,
    solver: &TraitSolver<'_>,
) -> Result<Vec<LiteralValue>, InternalCompilationError> {
    let trait_def = solver.trait_def(trait_id);
    if trait_def.associated_const_count() == 0 {
        return Ok(Vec::new());
    }

    // Temporary special case: generic source impls cannot yet store associated
    // const formulas, so only Value has compiler-owned layout synthesis here.
    if is_value_trait(trait_id, trait_def) {
        if ty_var_count != 0 {
            return Ok(Vec::new());
        }
        return Ok(
            value_layout_associated_const_values(input_tys[0], span, solver)?
                .into_iter()
                .map(LiteralValue::new_native)
                .collect(),
        );
    }

    Err(internal_compilation_error!(Internal {
        error: format!(
            "cannot emit compiler-defined associated consts for source impl of trait {}",
            trait_def.name
        ),
        span,
    }))
}

fn invalid_associated_const_impl(
    trait_id: TraitId,
    kind: InvalidTraitAssociatedConstImplKind,
    span: Location,
) -> InternalCompilationError {
    internal_compilation_error!(InvalidTraitAssociatedConstImpl {
        trait_ref: trait_id,
        kind,
        span,
    })
}

/// Validate and collect associated const values written in a source impl.
#[allow(clippy::too_many_arguments)]
fn source_associated_const_values(
    trait_id: TraitId,
    trait_def: &Trait,
    input_tys: &[Type],
    output_tys: &[Type],
    output_effs: &[EffType],
    associated_consts: &[ast::TraitAssociatedConstImpl],
    impl_span: Location,
) -> Result<Vec<LiteralValue>, InternalCompilationError> {
    if trait_def.associated_const_count() == 0 {
        if let Some(associated_const) = associated_consts.first() {
            return Err(invalid_associated_const_impl(
                trait_id,
                Unknown {
                    name: associated_const.name.0,
                },
                associated_const.span,
            ));
        }
        return Ok(Vec::new());
    }

    let associated_const_tys =
        trait_def.instantiate_associated_const_tys_for_tys(input_tys, output_tys, output_effs);
    let mut values = Vec::with_capacity(trait_def.associated_const_count());
    let mut seen = FxHashSet::default();
    for associated_const in associated_consts {
        if !seen.insert(associated_const.name.0) {
            return Err(invalid_associated_const_impl(
                trait_id,
                Duplicate {
                    name: associated_const.name.0,
                },
                associated_const.span,
            ));
        }
        if trait_def
            .associated_const_index(associated_const.name.0)
            .is_none()
        {
            return Err(invalid_associated_const_impl(
                trait_id,
                Unknown {
                    name: associated_const.name.0,
                },
                associated_const.span,
            ));
        }
    }

    let mut missing = Vec::new();
    for (index, decl) in trait_def.associated_consts.iter().enumerate() {
        let Some(associated_const) = associated_consts
            .iter()
            .find(|associated_const| associated_const.name.0 == decl.name)
        else {
            missing.push(decl.name);
            continue;
        };
        let expected_ty = associated_const_tys[index];
        if associated_const.ty != expected_ty {
            return Err(internal_compilation_error!(TypeMismatch {
                current_ty: associated_const.ty,
                current_span: associated_const.span,
                expected_ty,
                expected_span: impl_span,
                sub_or_same: SubOrSameType::SameTypeWithSubEffects,
            }));
        }
        values.push(associated_const.value.clone());
    }

    if !missing.is_empty() {
        return Err(invalid_associated_const_impl(
            trait_id,
            Missing { names: missing },
            impl_span,
        ));
    }

    Ok(values)
}

/// Source impl data needed to choose and type-check associated const values.
pub(super) struct SourceAssociatedConstImpl<'a> {
    pub(super) input_tys: &'a [Type],
    pub(super) output_tys: &'a [Type],
    pub(super) output_effs: &'a [EffType],
    pub(super) ty_var_count: u32,
    pub(super) associated_consts: &'a [ast::TraitAssociatedConstImpl],
    pub(super) span: Location,
}

/// Resolve the associated const values stored for a source impl.
pub(super) fn associated_const_values_for_source_impl(
    trait_id: TraitId,
    trait_def: &Trait,
    imp: SourceAssociatedConstImpl<'_>,
    solver: &TraitSolver<'_>,
) -> Result<Vec<LiteralValue>, InternalCompilationError> {
    if imp.associated_consts.is_empty()
        && (trait_def.associated_const_count() == 0 || is_value_trait(trait_id, trait_def))
    {
        emitted_associated_const_values(trait_id, imp.input_tys, imp.ty_var_count, imp.span, solver)
    } else {
        source_associated_const_values(
            trait_id,
            trait_def,
            imp.input_tys,
            imp.output_tys,
            imp.output_effs,
            imp.associated_consts,
            imp.span,
        )
    }
}
