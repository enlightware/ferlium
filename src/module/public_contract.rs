// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The contract of a public item names only public traits and types: what another module may
//! rely on or must satisfy through the item is something that module can name. Representations
//! and implementations are hidden by other means: a type marked `#[private_repr]` keeps its
//! fields out of its contract, and the requirements that a body adds are reduced in its module.
//!
//! The requirements of public functions, subscripts and impls, and the heads of public impls,
//! are checked where they are published; this module checks the rest.

use ustr::Ustr;

use crate::{
    FxHashMap, Location, Modules,
    ast::UstrSpan,
    compiler::error::{InternalCompilationError, PrivateNameKind, PublicItemKind},
    internal_compilation_error,
    module::{DefKind, LocalSubscriptId, Module, TraitId, TypeDefId, id::Id},
    types::{type_like::TypeLike, type_scheme::PubTypeConstraint},
};

/// A public item, as an error names it.
type Item = (PublicItemKind, Ustr);

fn private_name_error(
    (item_kind, item): Item,
    (private_kind, private): (PrivateNameKind, Ustr),
    span: Location,
) -> InternalCompilationError {
    internal_compilation_error!(PrivateNameInPublicContract {
        item_kind,
        item,
        private_kind,
        private,
        span,
    })
}

fn check_type_like(
    module: &Module,
    others: &Modules,
    item: Item,
    ty: &impl TypeLike,
    span: Location,
) -> Result<(), InternalCompilationError> {
    match module.first_private_type(ty, others) {
        Some(private) => Err(private_name_error(item, private, span)),
        None => Ok(()),
    }
}

fn check_requirements(
    module: &Module,
    others: &Modules,
    item: Item,
    requirements: &[PubTypeConstraint],
) -> Result<(), InternalCompilationError> {
    for requirement in requirements {
        if let Some(private) = module.first_private_name_in_requirement(requirement, others) {
            return Err(private_name_error(item, private, requirement.use_site()));
        }
    }
    Ok(())
}

/// Check the contracts of the public types, type aliases and traits of `module`, once they are
/// all desugared. `alias_spans` locates the type aliases, whose entries have no span.
pub(crate) fn check_public_declarations(
    module: &Module,
    others: &Modules,
    alias_spans: &FxHashMap<Ustr, Location>,
) -> Result<(), InternalCompilationError> {
    for (def, name) in module.def_table.iter() {
        let Some(name) = *name else {
            continue;
        };
        if !def.visibility.is_public() {
            continue;
        }
        match def.kind {
            DefKind::TypeDef(id) => {
                let type_def = module.type_def(TypeDefId::new(module.module_id(), id));
                let item = (PublicItemKind::TypeDef, name);
                // A user of the type satisfies its requirements, but sees its fields only if its
                // representation is public.
                check_requirements(module, others, item, &type_def.shape.constraints)?;
                if !type_def.has_private_repr() {
                    check_type_like(module, others, item, &type_def.shape.ty, type_def.span)?;
                }
            }
            DefKind::TypeAlias(id) => {
                let alias = module.type_aliases.get_entry(id);
                let span = alias_spans
                    .get(&name)
                    .copied()
                    .unwrap_or_else(Location::new_synthesized);
                check_type_like(
                    module,
                    others,
                    (PublicItemKind::TypeAlias, name),
                    &alias.ty,
                    span,
                )?;
            }
            DefKind::Trait(id) => {
                let trait_def = module.trait_def(TraitId::new(module.module_id(), id));
                let item = (PublicItemKind::Trait, name);
                check_requirements(module, others, item, &trait_def.parent_constraints)?;
                check_requirements(module, others, item, &trait_def.constraints)?;
                let spans = trait_def.spans.as_ref();
                let trait_span = spans.map_or_else(Location::new_synthesized, |spans| spans.name);
                for (index, (_, method)) in trait_def.methods.iter().enumerate() {
                    let span = spans
                        .and_then(|spans| spans.methods.get(index))
                        .map_or(trait_span, |spans| spans.span);
                    check_type_like(module, others, item, &method.ty_scheme.ty, span)?;
                }
                for associated_const in &trait_def.associated_consts {
                    check_type_like(module, others, item, &associated_const.ty, trait_span)?;
                }
            }
            DefKind::Function(_) | DefKind::Subscript(_) | DefKind::BareNativeTypeAlias => {}
        }
    }
    Ok(())
}

/// Check the published types of the public functions and subscripts that the source of `module`
/// declares, written or inferred, once all are emitted. Their requirements were checked when
/// they were published. Projection subscripts are part of the contract of their type.
pub(crate) fn check_public_signatures(
    module: &Module,
    others: &Modules,
    functions: impl IntoIterator<Item = UstrSpan>,
    subscripts: impl IntoIterator<Item = (UstrSpan, LocalSubscriptId)>,
) -> Result<(), InternalCompilationError> {
    for (name, span) in functions {
        let id = module
            .get_definition(name)
            .and_then(|def| def.as_function().copied())
            .expect("a source function is defined");
        let ty = &module.functions[id.as_index()].definition.ty_scheme.ty;
        check_type_like(module, others, (PublicItemKind::Function, name), ty, span)?;
    }
    for ((name, span), id) in subscripts {
        let signature = module
            .get_subscript_by_id(id)
            .and_then(|subscript| subscript.resolved_signature())
            .expect("an emitted source subscript has its signature");
        let item = (PublicItemKind::Subscript, name);
        for arg in &signature.args {
            check_type_like(module, others, item, &arg.ty, span)?;
        }
        check_type_like(module, others, item, &signature.ret, span)?;
    }
    Ok(())
}
