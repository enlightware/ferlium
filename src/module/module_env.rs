// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    FxHashMap, Location,
    ast::{self, UstrSpan},
    compiler::error::InternalCompilationError,
    format::FormatWith,
    internal_compilation_error,
    module::{
        Module, ModuleFunction, ModuleId, Modules, ProjectionEntry, ProjectionKey,
        ProjectionOrigin, ProjectionReceiverKey, SubscriptId, SubscriptMemberFunctionKind, TraitId,
        TypeDefId, YieldProvenance, disambiguated_subscript_member_function_name,
        id::Id,
        path::Path,
        stable_generated_name_hash,
        type_alias_name::{find_generic_alias_name, find_generic_alias_name_with},
    },
    std::STD_MODULE_ID,
    types::effects::EffType,
    types::r#trait::{Trait, TraitMethodIndex},
    types::r#type::{
        BareNativeTypeB, FnArgType, NativeType, Type, TypeAliasEntry, TypeAliases, TypeDef,
        TypeDefSlot,
    },
    types::type_scheme::PubTypeConstraint,
    types::typing_env::TraitMethodDescription,
};
use ustr::{Ustr, ustr};

#[derive(Debug, Clone)]
pub enum TypeDefLookupResult {
    Enum(TypeDefId, Ustr),
    Struct(TypeDefId),
}
impl TypeDefLookupResult {
    pub fn lookup_payload(&self) -> (TypeDefId, Option<Ustr>) {
        use TypeDefLookupResult::*;
        match self {
            Enum(type_def, tag) => (*type_def, Some(*tag)),
            Struct(type_def) => (*type_def, None),
        }
    }
}

fn unavailable_type_def<T>(id: TypeDefId) -> T {
    panic!("Type definition #{}:{} is unavailable", id.module, id.index)
}

fn unavailable_trait<T>(id: TraitId) -> T {
    panic!("Trait #{}:{} is unavailable", id.module, id.index)
}

fn visible_projection_entry(
    module: &Module,
    current_module: ModuleId,
    key: ProjectionKey,
    entry: ProjectionEntry,
) -> Option<ProjectionEntry> {
    (module.module_id() == current_module || entry.visibility == crate::module::Visibility::Public)
        .then_some(entry)
        .filter(|entry| entry.origin == ProjectionOrigin::Explicit)
        .filter(|_| module.get_projection_subscript(key).is_some())
}

#[derive(Clone, Copy, Debug)]
pub struct ModuleEnv<'m> {
    pub(crate) current: &'m Module,
    pub(crate) modules: &'m Modules,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ModuleIdentity<'m> {
    pub(crate) id: ModuleId,
    pub(crate) path: &'m Path,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct CurrentTypeItems<'m> {
    pub(crate) module: ModuleIdentity<'m>,
    pub(crate) type_aliases: &'m TypeAliases,
    pub(crate) type_defs: &'m [TypeDefSlot],
    pub(crate) traits: &'m [Trait],
    pub(crate) projection_subscripts: &'m FxHashMap<ProjectionKey, ProjectionEntry>,
}

impl<'m> CurrentTypeItems<'m> {
    pub(crate) fn new(
        module: ModuleIdentity<'m>,
        type_aliases: &'m TypeAliases,
        type_defs: &'m [TypeDefSlot],
        traits: &'m [Trait],
        projection_subscripts: &'m FxHashMap<ProjectionKey, ProjectionEntry>,
    ) -> Self {
        Self {
            module,
            type_aliases,
            type_defs,
            traits,
            projection_subscripts,
        }
    }

    pub(crate) fn new_from_module(current: &'m Module) -> Self {
        Self::new(
            ModuleIdentity {
                id: current.module_id(),
                path: current.path(),
            },
            &current.type_aliases,
            current.type_defs.as_slice(),
            current.traits.as_slice(),
            &current.projection_subscripts,
        )
    }

    pub(crate) fn type_def(self, id: TypeDefId) -> Option<&'m TypeDef> {
        if id.module == self.module.id {
            self.type_defs
                .get(id.index.as_index())
                .map(TypeDefSlot::def)
        } else {
            None
        }
    }

    pub(crate) fn trait_def(self, id: TraitId) -> Option<&'m Trait> {
        if id.module == self.module.id {
            self.traits.get(id.index.as_index())
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct QualifiedNameEnv<'m> {
    pub(crate) current: CurrentTypeItems<'m>,
    pub(crate) modules: &'m Modules,
}

impl<'m> QualifiedNameEnv<'m> {
    pub(crate) fn new(current: CurrentTypeItems<'m>, modules: &'m Modules) -> Self {
        Self { current, modules }
    }

    pub(crate) fn new_from_module(current: &'m Module, modules: &'m Modules) -> Self {
        Self::new(CurrentTypeItems::new_from_module(current), modules)
    }

    fn format_module_prefix(&self, module_id: ModuleId) -> String {
        if module_id == self.current.module.id {
            self.current.module.path.to_string()
        } else {
            self.modules
                .get_name(module_id)
                .map(ToString::to_string)
                .unwrap_or_else(|| format!("#{module_id}"))
        }
    }

    pub(crate) fn type_def_name(&self, id: TypeDefId) -> Option<Ustr> {
        if id.module == self.current.module.id {
            self.current
                .type_defs
                .get(id.index.as_index())
                .map(TypeDefSlot::name)
        } else {
            self.modules
                .get(id.module)
                .and_then(|entry| entry.module())
                .and_then(|module| module.try_type_def_name(id))
        }
    }

    pub(crate) fn format_type_def_id(&self, id: TypeDefId) -> String {
        let name = self
            .type_def_name(id)
            .map(|name| name.to_string())
            .unwrap_or_else(|| format!("#{}", id.index));
        format!("{}::{name}", self.format_module_prefix(id.module))
    }

    pub(crate) fn trait_name(&self, id: TraitId) -> Option<Ustr> {
        if id.module == self.current.module.id {
            self.current
                .traits
                .get(id.index.as_index())
                .map(|trait_def| trait_def.name)
        } else {
            self.modules
                .get(id.module)
                .and_then(|entry| entry.module())
                .and_then(|module| module.try_trait_name(id))
        }
    }

    pub(crate) fn format_trait_id(&self, id: TraitId, fallback: Ustr) -> String {
        let name = self.trait_name(id).unwrap_or(fallback).to_string();
        format!("{}::{name}", self.format_module_prefix(id.module))
    }

    fn format_item_name_readable(&self, module_id: ModuleId, name: &str) -> String {
        if module_id == self.current.module.id {
            name.to_owned()
        } else {
            format!("{}::{name}", self.format_module_prefix(module_id))
        }
    }

    fn format_type_def_id_readable(&self, id: TypeDefId) -> String {
        let name = self
            .type_def_name(id)
            .map(|name| name.to_string())
            .unwrap_or_else(|| format!("#{}", id.index));
        self.format_item_name_readable(id.module, &name)
    }

    fn format_trait_id_readable(&self, id: TraitId, fallback: Ustr) -> String {
        let name = self.trait_name(id).unwrap_or(fallback);
        self.format_item_name_readable(id.module, name.as_str())
    }

    pub(crate) fn bare_native_name(&self, native: &BareNativeTypeB) -> Option<String> {
        if let Some(name) = self.current.type_aliases.get_bare_native_name(native) {
            return Some(format!(
                "{}::{name}",
                self.format_module_prefix(self.current.module.id)
            ));
        }

        self.modules.iter_named().find_map(|(mod_path, entry)| {
            entry.module().and_then(|module| {
                module
                    .type_aliases
                    .get_bare_native_name(native)
                    .map(|ty_name| format!("{mod_path}::{ty_name}"))
            })
        })
    }

    pub(crate) fn native_type_name(&self, native: &NativeType) -> Option<String> {
        if let Some(name) = self.current.type_aliases.get_native_name(native) {
            return Some(format!(
                "{}::{name}",
                self.format_module_prefix(self.current.module.id)
            ));
        }

        self.modules.iter_named().find_map(|(mod_path, entry)| {
            entry.module().and_then(|module| {
                module
                    .type_aliases
                    .get_native_name(native)
                    .map(|ty_name| format!("{mod_path}::{ty_name}"))
            })
        })
    }

    pub(crate) fn format_type(&self, ty: Type) -> String {
        ty.format_with(self).to_string()
    }

    fn format_effect(eff: &EffType) -> String {
        match eff.as_single() {
            Some(effect) => effect.to_string(),
            None if eff.is_empty() => "()".to_string(),
            None => format!("({eff})"),
        }
    }

    fn format_constraint(&self, constraint: &PubTypeConstraint) -> String {
        match constraint {
            PubTypeConstraint::TupleAtIndexIs {
                tuple_ty,
                index,
                element_ty,
                ..
            } => format!(
                "tuple-at-index({}, {}, {})",
                self.format_type(*tuple_ty),
                index,
                self.format_type(*element_ty)
            ),
            PubTypeConstraint::ProjectionSubscriptIs {
                requirement,
                field,
                subscript_ty,
                ..
            } => format!(
                "projection-subscript({:?}, {}, {}, {})",
                requirement,
                self.format_type(subscript_ty.receiver_ty()),
                field,
                self.format_type(Type::subscript_type(subscript_ty.clone()))
            ),
            PubTypeConstraint::TypeHasVariant {
                variant_ty,
                tag,
                payload_ty,
                ..
            } => format!(
                "type-has-variant({}, {}, {})",
                self.format_type(*variant_ty),
                tag,
                self.format_type(*payload_ty)
            ),
            PubTypeConstraint::HaveTrait {
                trait_id,
                input_tys,
                output_tys,
                output_effs,
                ..
            } => format!(
                "have-trait({}, inputs=[{}], outputs=[{}], effects=[{}])",
                self.format_trait_id(*trait_id, ustr("#trait")),
                self.format_type_list(input_tys),
                self.format_type_list(output_tys),
                Self::format_effect_list(output_effs)
            ),
        }
    }

    fn format_type_list(&self, tys: &[Type]) -> String {
        tys.iter()
            .map(|ty| self.format_type(*ty))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn format_fn_arg_list(&self, args: &[FnArgType]) -> String {
        args.iter()
            .map(|arg| arg.format_with(self).to_string())
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn format_effect_list(effs: &[EffType]) -> String {
        effs.iter()
            .map(Self::format_effect)
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn format_constraint_list(&self, constraints: &[PubTypeConstraint]) -> String {
        constraints
            .iter()
            .map(|constraint| self.format_constraint(constraint))
            .collect::<Vec<_>>()
            .join("; ")
    }

    pub(crate) fn qualified_method_name(
        &self,
        trait_id: TraitId,
        trait_def: &Trait,
        index: TraitMethodIndex,
        input_tys: &[Type],
    ) -> String {
        let mut s = format!(
            "{}<",
            self.format_trait_id_readable(trait_id, trait_def.name)
        );
        for (i, ty) in input_tys.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            s.push_str(&self.format_type(*ty));
        }
        s.push_str(&format!(">::{}", trait_def.method(index).0));
        s
    }

    pub(crate) fn qualified_named_subscript_name(&self, module_id: ModuleId, name: Ustr) -> String {
        self.format_item_name_readable(module_id, name.as_str())
    }

    pub(crate) fn qualified_projection_subscript_name(&self, key: ProjectionKey) -> String {
        let receiver = match key.receiver {
            ProjectionReceiverKey::Structural(ty) => self.format_type(ty),
            ProjectionReceiverKey::Nominal(type_def) => self.format_type_def_id_readable(type_def),
        };
        format!("{receiver}.{}", key.field)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn disambiguated_impl_method_name(
        &self,
        trait_id: TraitId,
        trait_def: &Trait,
        index: TraitMethodIndex,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        ty_var_count: u32,
        eff_var_count: u32,
        constraints: &[PubTypeConstraint],
    ) -> String {
        let readable_name = self.qualified_method_name(trait_id, trait_def, index, input_tys);
        let canonical_identity = format!(
            "trait={}; method={}; inputs=[{}]; outputs=[{}]; effects=[{}]; ty_vars={}; eff_vars={}; constraints=[{}]",
            self.format_trait_id(trait_id, trait_def.name),
            trait_def.method(index).0,
            self.format_type_list(input_tys),
            self.format_type_list(output_tys),
            Self::format_effect_list(output_effs),
            ty_var_count,
            eff_var_count,
            self.format_constraint_list(constraints)
        );
        format!(
            "{readable_name}#impl:{:08x}",
            stable_generated_name_hash(&canonical_identity)
        )
    }

    pub(crate) fn disambiguated_subscript_member_name(
        &self,
        readable_subscript_name: &str,
        member_kind: SubscriptMemberFunctionKind,
        definition: &crate::hir::function::CallableDefinition,
        provenance: YieldProvenance,
    ) -> String {
        let ty_scheme = &definition.ty_scheme;
        let fn_ty = &ty_scheme.ty;
        let canonical_identity = format!(
            "subscript={}; member={}; args=[{}]; return={}; effects=[{}]; result={:?}; provenance={:?}; ty_vars={}; eff_vars={}; constraints=[{}]",
            readable_subscript_name,
            member_kind.keyword(),
            self.format_fn_arg_list(&fn_ty.args),
            self.format_type(fn_ty.ret),
            Self::format_effect(&fn_ty.effects),
            definition.result_convention,
            provenance,
            ty_scheme.ty_quantifiers.len(),
            ty_scheme.eff_quantifiers.len(),
            self.format_constraint_list(&ty_scheme.constraints)
        );
        disambiguated_subscript_member_function_name(
            readable_subscript_name,
            member_kind,
            &canonical_identity,
        )
    }
}

impl<'m> ModuleEnv<'m> {
    pub(crate) fn new(current: &'m Module, modules: &'m Modules) -> Self {
        Self { current, modules }
    }

    pub fn type_alias_name(&self, ty: Type) -> Option<String> {
        if let Some(name) = self.current.type_aliases.get_name(ty) {
            return Some(name.to_string());
        }
        if let Some(alias_name) = find_generic_alias_name(self.current, ty, self) {
            return Some(alias_name.rendered);
        }

        if let Some(name) = self.modules.iter_named().find_map(|(mod_path, entry)| {
            entry.module().and_then(|module| {
                module.type_aliases.get_name(ty).map(|ty_name| {
                    if self.current.uses(mod_path, ty_name) {
                        ty_name.to_string()
                    } else {
                        format!("{mod_path}::{ty_name}")
                    }
                })
            })
        }) {
            return Some(name);
        }

        self.modules
            .iter_named()
            .filter_map(|(mod_path, entry)| {
                let module = entry.module()?;
                find_generic_alias_name(module, ty, self).map(|alias_name| {
                    let rendered = if self.current.uses(mod_path, alias_name.name) {
                        alias_name.rendered
                    } else {
                        format!("{mod_path}::{}", alias_name.rendered)
                    };
                    (alias_name.score, rendered)
                })
            })
            .max_by(|left, right| left.0.cmp(&right.0).then_with(|| right.1.cmp(&left.1)))
            .map(|(_, rendered)| rendered)
    }

    pub fn type_alias_name_with(
        &self,
        ty: Type,
        mut format_type: impl FnMut(Type) -> String,
    ) -> Option<String> {
        if let Some(name) = self.current.type_aliases.get_name(ty) {
            return Some(name.to_string());
        }
        if let Some(alias_name) = find_generic_alias_name_with(self.current, ty, &mut format_type) {
            return Some(alias_name.rendered);
        }

        if let Some(name) = self.modules.iter_named().find_map(|(mod_path, entry)| {
            entry.module().and_then(|module| {
                module.type_aliases.get_name(ty).map(|ty_name| {
                    if self.current.uses(mod_path, ty_name) {
                        ty_name.to_string()
                    } else {
                        format!("{mod_path}::{ty_name}")
                    }
                })
            })
        }) {
            return Some(name);
        }

        self.modules
            .iter_named()
            .filter_map(|(mod_path, entry)| {
                let module = entry.module()?;
                find_generic_alias_name_with(module, ty, &mut format_type).map(|alias_name| {
                    let rendered = if self.current.uses(mod_path, alias_name.name) {
                        alias_name.rendered
                    } else {
                        format!("{mod_path}::{}", alias_name.rendered)
                    };
                    (alias_name.score, rendered)
                })
            })
            .max_by(|left, right| left.0.cmp(&right.0).then_with(|| right.1.cmp(&left.1)))
            .map(|(_, rendered)| rendered)
    }

    pub fn bare_native_name(&self, native: &BareNativeTypeB) -> Option<String> {
        self.current
            .type_aliases
            .get_bare_native_name(native)
            .map_or_else(
                || {
                    self.modules.iter_named().find_map(|(mod_name, entry)| {
                        entry.module().and_then(|module| {
                            module
                                .type_aliases
                                .get_bare_native_name(native)
                                .map(|ty_name| {
                                    if self.current.uses(mod_name, ty_name) {
                                        ty_name.to_string()
                                    } else {
                                        format!("{mod_name}::{ty_name}")
                                    }
                                })
                        })
                    })
                },
                |name| Some(name.to_string()),
            )
    }

    pub fn type_alias_type(
        &self,
        path: &ast::Path,
    ) -> Result<Option<Type>, InternalCompilationError> {
        Ok(self
            .get_module_member(&path.segments, &|name, module| {
                module.get_type_alias(ustr(name))
            })?
            .and_then(|(_, entry)| entry.generic_params.is_empty().then_some(entry.ty)))
    }

    /// Like [`type_alias_type`], but also returns the source [`ModuleId`] when the alias
    /// is defined in another module (`None` means it belongs to the current module).
    /// Returns the full [`TypeAliasEntry`] to support generic aliases.
    pub fn type_alias_with_module<'a>(
        &'a self,
        path: &'a ast::Path,
    ) -> Result<Option<(Option<ModuleId>, &'a TypeAliasEntry)>, InternalCompilationError> {
        self.get_module_member(&path.segments, &|name, module| {
            module.get_type_alias(ustr(name))
        })
    }

    /// Look up a bare native type alias by path, returning the bare native type and the source
    /// module id (None means the current module).
    pub fn bare_native_type_alias_with_module(
        &self,
        path: &ast::Path,
    ) -> Result<Option<(Option<ModuleId>, BareNativeTypeB)>, InternalCompilationError> {
        self.get_module_member(&path.segments, &|name, module| {
            module.get_bare_native_type_alias(ustr(name))
        })
    }

    /// Return whether an unsafe item is unavailable from the module currently being compiled.
    pub fn is_unsafe_item_unavailable_in_current_context(
        &self,
        module_id: Option<ModuleId>,
        name: Ustr,
    ) -> bool {
        if self.current.module_id() == STD_MODULE_ID {
            return false;
        }

        let Some(module_id) = module_id else {
            return false;
        };
        if module_id != STD_MODULE_ID {
            return false;
        }

        self.modules
            .get(module_id)
            .and_then(|entry| entry.module())
            .is_some_and(|module| module.is_unsafe_item(name))
    }

    pub fn type_def_with_module(
        &self,
        path: &ast::Path,
    ) -> Result<Option<(Option<ModuleId>, TypeDefId)>, InternalCompilationError> {
        self.get_module_member(&path.segments, &|name, module| {
            module.get_type_def_id(ustr(name))
        })
    }

    fn type_def_module(&self, id: TypeDefId) -> Option<&Module> {
        if id.module == self.current.module_id() {
            Some(self.current)
        } else {
            self.modules.get(id.module).and_then(|entry| entry.module())
        }
    }

    pub fn type_def_name(&self, id: TypeDefId) -> Ustr {
        self.try_type_def_name(id)
            .unwrap_or_else(|| unavailable_type_def(id))
    }

    pub fn try_type_def_name(&self, id: TypeDefId) -> Option<Ustr> {
        self.type_def_module(id)
            .and_then(|module| module.try_type_def_name(id))
    }

    pub fn type_def_param_names(&self, id: TypeDefId) -> impl ExactSizeIterator<Item = Ustr> + '_ {
        self.try_type_def_param_names(id)
            .unwrap_or_else(|| unavailable_type_def(id))
    }

    pub fn try_type_def_param_names(
        &self,
        id: TypeDefId,
    ) -> Option<impl ExactSizeIterator<Item = Ustr> + '_> {
        self.type_def_module(id)
            .and_then(|module| module.try_type_def_param_names(id))
    }

    pub fn type_def_param_spans(
        &self,
        id: TypeDefId,
    ) -> impl ExactSizeIterator<Item = Location> + '_ {
        self.try_type_def_param_spans(id)
            .unwrap_or_else(|| unavailable_type_def(id))
    }

    pub fn try_type_def_param_spans(
        &self,
        id: TypeDefId,
    ) -> Option<impl ExactSizeIterator<Item = Location> + '_> {
        self.type_def_module(id)
            .and_then(|module| module.try_type_def_param_spans(id))
    }

    pub fn type_def_effect_param_count(&self, id: TypeDefId) -> usize {
        self.try_type_def_effect_param_count(id)
            .unwrap_or_else(|| unavailable_type_def(id))
    }

    pub fn try_type_def_effect_param_count(&self, id: TypeDefId) -> Option<usize> {
        self.type_def_module(id)
            .and_then(|module| module.try_type_def_effect_param_count(id))
    }

    pub fn type_def_span(&self, id: TypeDefId) -> Location {
        self.try_type_def_span(id)
            .unwrap_or_else(|| unavailable_type_def(id))
    }

    pub fn try_type_def_span(&self, id: TypeDefId) -> Option<Location> {
        self.type_def_module(id)
            .and_then(|module| module.try_type_def_span(id))
    }

    pub fn type_def(&self, id: TypeDefId) -> &TypeDef {
        self.try_type_def(id)
            .unwrap_or_else(|| unavailable_type_def(id))
    }

    pub fn try_type_def(&self, id: TypeDefId) -> Option<&TypeDef> {
        self.type_def_module(id)
            .and_then(|module| module.try_type_def(id))
    }

    /// Resolve an explicit projection implementation visible from the current module.
    pub fn projection_subscript(&self, key: ProjectionKey) -> Option<SubscriptId> {
        self.current
            .get_projection_subscript(key)
            .filter(|entry| entry.origin == ProjectionOrigin::Explicit)
            .map(|entry| SubscriptId::new(self.current.module_id(), entry.subscript))
            .or_else(|| {
                self.modules.enumerate().find_map(|(module_id, entry, _)| {
                    let module = entry.module()?;
                    visible_projection_entry(
                        module,
                        self.current.module_id(),
                        key,
                        module.get_projection_subscript(key)?,
                    )
                    .map(|entry| SubscriptId::new(module_id, entry.subscript))
                })
            })
    }

    fn reject_inaccessible_private_repr(
        &self,
        id: TypeDefId,
        access_span: Location,
    ) -> Result<(), InternalCompilationError> {
        if id.module != self.current.module_id() && self.type_def(id).has_private_repr() {
            return Err(internal_compilation_error!(PrivateReprAccess {
                type_def: id,
                access_span,
            }));
        }
        Ok(())
    }

    pub fn type_def_for_construction(
        &self,
        path: &ast::Path,
    ) -> Result<Option<(Option<ModuleId>, TypeDefLookupResult)>, InternalCompilationError> {
        // First search for a matching enum
        let segments = &path.segments;
        let len = segments.len();
        if len >= 2 {
            let enum_segments = &segments[0..len - 1];
            let variant_name = segments[len - 1].0;
            if let Some((module_id, ty_def)) = self
                .get_module_member(enum_segments, &|name, module| {
                    module.get_type_def_id(ustr(name))
                })?
            {
                let ty_def_data = self.type_def(ty_def);
                if ty_def_data.is_enum() {
                    let ty_data = ty_def_data.shape_ty().data();
                    let variants = ty_data.as_variant().unwrap();
                    let variant = variants.iter().find(|(name, _)| *name == variant_name);
                    if let Some((tag, _)) = variant {
                        self.reject_inaccessible_private_repr(
                            ty_def,
                            path.span().unwrap_or(ty_def_data.span),
                        )?;
                        let td = TypeDefLookupResult::Enum(ty_def, *tag);
                        return Ok(Some((module_id, td)));
                    }
                }
            }
        }
        // Not found, search for a matching struct
        if len >= 1 {
            if let Some((module_id, ty_def)) = self
                .get_module_member(segments, &|name, module| module.get_type_def_id(ustr(name)))?
            {
                if self.type_def(ty_def).is_struct_like() {
                    self.reject_inaccessible_private_repr(
                        ty_def,
                        path.span().unwrap_or(self.type_def(ty_def).span),
                    )?;
                    let td = TypeDefLookupResult::Struct(ty_def);
                    return Ok(Some((module_id, td)));
                }
            }
        }

        Ok(None)
    }

    pub fn type_def_type(
        &self,
        path: &ast::Path,
    ) -> Result<Option<Type>, InternalCompilationError> {
        Ok(self.type_def_with_module(path)?.and_then(|(_, type_def)| {
            (self.type_def_param_names(type_def).len() == 0).then(|| Type::named(type_def, vec![]))
        }))
    }

    /// Like [`type_def_type`], but also returns the source [`ModuleId`] when the type
    /// is defined in another module (`None` means it belongs to the current module).
    pub fn type_def_type_with_module(
        &self,
        path: &ast::Path,
    ) -> Result<Option<(Option<ModuleId>, Type)>, InternalCompilationError> {
        Ok(self
            .type_def_with_module(path)?
            .and_then(|(module_id, type_def)| {
                (self.type_def_param_names(type_def).len() == 0)
                    .then(|| (module_id, Type::named(type_def, vec![])))
            }))
    }

    /// Get a function from the current module, or other ones, return the ID of the module if other.
    pub fn get_function(
        &'m self,
        path: &'m [UstrSpan],
    ) -> Result<Option<(Option<ModuleId>, &'m ModuleFunction)>, InternalCompilationError> {
        self.get_module_member(path, &|name, module| module.get_function(ustr(name)))
    }

    /// Get a function from the current module, or other ones, return the ID of the module if other.
    pub fn get_program_function(
        &'m self,
        path: &'m [UstrSpan],
    ) -> Result<Option<(Option<ModuleId>, &'m ModuleFunction)>, InternalCompilationError> {
        self.get_module_member(path, &|name, module| module.get_function(ustr(name)))
    }

    /// Resolve a function path to the source module and local function name, applying visibility rules.
    pub fn function_name_with_module(
        &self,
        path: &ast::Path,
    ) -> Result<Option<(Option<ModuleId>, Ustr)>, InternalCompilationError> {
        self.find_member_by_path(&path.segments, &|name, module, require_accessible| {
            if require_accessible
                && !module.is_symbol_accessible_from(ustr(name), self.current.module_id())
            {
                return None;
            }

            let name = ustr(name);
            module.get_local_function_id(name).is_some().then_some(name)
        })
    }

    /// Resolve a subscript path to the source module and local subscript name, applying visibility rules.
    pub fn subscript_name_with_module(
        &self,
        path: &ast::Path,
    ) -> Result<Option<(Option<ModuleId>, Ustr)>, InternalCompilationError> {
        self.find_member_by_path(&path.segments, &|name, module, require_accessible| {
            if require_accessible
                && !module.is_symbol_accessible_from(ustr(name), self.current.module_id())
            {
                return None;
            }

            let name = ustr(name);
            module
                .get_local_subscript_id(name)
                .is_some()
                .then_some(name)
        })
    }

    /// Get the trait definition associated to a trait id.
    pub fn trait_def(&self, id: TraitId) -> &Trait {
        self.try_trait_def(id)
            .unwrap_or_else(|| unavailable_trait(id))
    }

    pub fn try_trait_def(&self, id: TraitId) -> Option<&Trait> {
        if let Some(trait_def) = self.current.try_trait_def(id) {
            return Some(trait_def);
        }
        self.modules
            .get(id.module)
            .and_then(|entry| entry.module())
            .and_then(|module| module.try_trait_def(id))
    }

    pub fn trait_name(&self, id: TraitId) -> Ustr {
        self.try_trait_name(id)
            .unwrap_or_else(|| unavailable_trait(id))
    }

    pub fn try_trait_name(&self, id: TraitId) -> Option<Ustr> {
        if let Some(name) = self.current.try_trait_name(id) {
            return Some(name);
        }
        self.modules
            .get(id.module)
            .and_then(|entry| entry.module())
            .and_then(|module| module.try_trait_name(id))
    }

    pub fn get_trait_id(
        &'m self,
        name: UstrSpan,
    ) -> Result<Option<TraitId>, InternalCompilationError> {
        Ok(self
            .trait_id_with_module(&ast::Path::single_tuple(name))?
            .map(|(_, trait_id)| trait_id))
    }

    pub fn trait_id_with_module(
        &'m self,
        path: &'m ast::Path,
    ) -> Result<Option<(Option<ModuleId>, TraitId)>, InternalCompilationError> {
        self.get_module_member(&path.segments, &|name, module| {
            module.get_trait_id(ustr(name))
        })
    }

    /// Look up a trait in the registered std module by its fully-qualified module id.
    pub fn expect_std_trait_id(&self, name: &str) -> TraitId {
        if self.current.module_id() == crate::std::STD_MODULE_ID {
            if let Some(id) = self.current.get_trait_id_str(name) {
                return id;
            }
        }
        Module::expect_std_trait_id(self.modules, name)
    }

    /// Get a trait method from the current module, or other ones, return the ID of the module if other.
    pub fn get_trait_method(
        &'m self,
        path: &'m ast::Path,
    ) -> Result<Option<(Option<ModuleId>, TraitMethodDescription<'m>)>, InternalCompilationError>
    {
        match path.segments.as_slice() {
            [] => Ok(None),
            [(method_name, span)] => self.get_unqualified_trait_method(*method_name, *span),
            segments => {
                let ((method_name, _), trait_segments) = segments.split_last().unwrap();
                let Some((module_id, trait_id)) = self
                    .get_module_member(trait_segments, &|name, module| {
                        module.get_trait_id(ustr(name))
                    })?
                else {
                    return Ok(None);
                };
                Ok(self
                    .trait_method_in_trait(trait_id, *method_name)
                    .map(|method| (module_id, method)))
            }
        }
    }

    fn get_unqualified_trait_method(
        &'m self,
        method_name: Ustr,
        span: Location,
    ) -> Result<Option<(Option<ModuleId>, TraitMethodDescription<'m>)>, InternalCompilationError>
    {
        let mut matches = Vec::new();
        self.collect_trait_methods_from_module(None, self.current, method_name, &mut matches);

        for (trait_name, use_data) in &self.current.uses.explicits {
            if let Some((module_id, entry)) = self.modules.get_by_name(&use_data.module)
                && let Some(module) = entry.module()
                && let Some(trait_id) = module.get_trait_id(*trait_name)
                && module.is_trait_accessible_from(trait_id, self.current.module_id(), self.modules)
                && let Some(method) = Self::trait_method_in_definition(
                    trait_id,
                    module.trait_def(trait_id),
                    method_name,
                )
            {
                matches.push((Some(module_id), method));
            }
        }

        for use_data in &self.current.uses.wildcards {
            if let Some((module_id, entry)) = self.modules.get_by_name(&use_data.module)
                && let Some(module) = entry.module()
            {
                self.collect_trait_methods_from_module(
                    Some(module_id),
                    module,
                    method_name,
                    &mut matches,
                );
            }
        }

        matches.sort_by_key(|(_, (trait_id, _, _))| (trait_id.module.0, trait_id.index.0));
        matches.dedup_by_key(|(_, (trait_id, _, _))| *trait_id);

        match matches.len() {
            0 => Ok(None),
            1 => Ok(matches.pop()),
            _ => Err(internal_compilation_error!(AmbiguousTraitMethod {
                method_name,
                trait_refs: matches
                    .into_iter()
                    .map(|(_, (trait_id, _, _))| trait_id)
                    .collect(),
                span,
            })),
        }
    }

    fn collect_trait_methods_from_module(
        &'m self,
        module_id: Option<ModuleId>,
        module: &'m Module,
        method_name: Ustr,
        matches: &mut Vec<(Option<ModuleId>, TraitMethodDescription<'m>)>,
    ) {
        for (trait_id, trait_def) in module.trait_iter() {
            if module_id.is_some()
                && !module.is_trait_accessible_from(
                    trait_id,
                    self.current.module_id(),
                    self.modules,
                )
            {
                continue;
            }
            if let Some(method) = Self::trait_method_in_definition(trait_id, trait_def, method_name)
            {
                matches.push((module_id, method));
            }
        }
    }

    fn trait_method_in_trait(
        &'m self,
        trait_id: TraitId,
        method_name: Ustr,
    ) -> Option<TraitMethodDescription<'m>> {
        let trait_def = self.trait_def(trait_id);
        Self::trait_method_in_definition(trait_id, trait_def, method_name)
    }

    fn trait_method_in_definition(
        trait_id: TraitId,
        trait_def: &'m Trait,
        method_name: Ustr,
    ) -> Option<TraitMethodDescription<'m>> {
        trait_def
            .methods
            .iter()
            .enumerate()
            .find_map(|(index, function)| {
                if function.0 == method_name {
                    Some((trait_id, TraitMethodIndex::from_index(index), &function.1))
                } else {
                    None
                }
            })
    }

    /// Get a member of a module, by first looking in the current module, and then in others, considering the path.
    fn get_module_member<'a, T>(
        &'a self,
        segments: &'a [UstrSpan],
        getter: &impl Fn(/*name*/ &'a str, /*current*/ &'a Module) -> Option<T>,
    ) -> Result<Option<(Option<ModuleId>, T)>, InternalCompilationError> {
        self.find_member_by_path(segments, &|name, module, require_accessible| {
            if require_accessible
                && !module.is_symbol_accessible_from(ustr(name), self.current.module_id())
            {
                return None;
            }
            getter(name, module)
        })
    }

    fn find_member_by_path<'a, T>(
        &'a self,
        segments: &'a [UstrSpan],
        getter: &impl Fn(&'a str, &'a Module, bool) -> Option<T>,
    ) -> Result<Option<(Option<ModuleId>, T)>, InternalCompilationError> {
        // If the name is not qualified, look in the current module.
        if let [(name, _)] = segments {
            return self.find_unqualified_member(name, getter);
        }
        // The name is qualified, split between path and symbol name.
        if let Some(path) = segments.split_last() {
            let ((sym_name, _), module) = path;
            // Special case when compiling std.
            if let [single_segment] = module
                && single_segment.0 == "std"
                && self.current.module_id() == STD_MODULE_ID
            {
                return self.find_unqualified_member(sym_name, getter);
            }
            // Look into the foreign module, if it exists.
            let path = Path::from_ast_segments(module);
            Ok(
                if let Some((foreign_id, foreign_entry)) = self.modules.get_by_name(&path)
                    && let Some(module) = foreign_entry.module()
                    && let Some(t) = getter(sym_name, module, true)
                {
                    Some((Some(foreign_id), t))
                } else {
                    None
                },
            )
        } else {
            Ok(None)
        }
    }

    fn find_unqualified_member<'a, T>(
        &'a self,
        name: &'a str,
        getter: &impl Fn(&'a str, &'a Module, bool) -> Option<T>,
    ) -> Result<Option<(Option<ModuleId>, T)>, InternalCompilationError> {
        self.current.find_member(name, self.modules, getter)
    }
}
