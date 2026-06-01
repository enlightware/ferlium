// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    Location,
    ast::{self, UstrSpan},
    compiler::error::InternalCompilationError,
    module::{
        Module, ModuleFunction, ModuleId, Modules, TraitId, TypeDefId,
        id::Id,
        path::Path,
        type_alias_name::{find_generic_alias_name, find_generic_alias_name_with},
    },
    std::STD_MODULE_ID,
    types::r#trait::{Trait, TraitMethodIndex},
    types::r#type::{BareNativeTypeB, Type, TypeAliasEntry, TypeDef},
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

#[derive(Clone, Copy, Debug)]
pub struct ModuleEnv<'m> {
    pub(crate) current: &'m Module,
    pub(crate) modules: &'m Modules,
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
        self.find_member_by_path(&path.segments, &|name, module, require_accessible| {
            self.trait_method_in_module(name, module, require_accessible)
        })
    }

    fn trait_method_in_module(
        &'m self,
        name: &'m str,
        module: &'m Module,
        require_accessible_trait: bool,
    ) -> Option<TraitMethodDescription<'m>> {
        module.trait_iter().find_map(|(trait_id, trait_def)| {
            if require_accessible_trait
                && !module.is_trait_accessible_from(
                    trait_id,
                    self.current.module_id(),
                    self.modules,
                )
            {
                return None;
            }

            trait_def
                .methods
                .iter()
                .enumerate()
                .find_map(|(index, function)| {
                    if function.0 == name {
                        Some((trait_id, TraitMethodIndex::from_index(index), &function.1))
                    } else {
                        None
                    }
                })
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
