// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use crate::{
    ast::{self, UstrSpan},
    error::InternalCompilationError,
    module::{Module, ModuleFunction, ModuleId, Modules, path::Path},
    std::STD_MODULE_ID,
    r#trait::TraitRef,
    r#type::TypeDefRef,
    typing_env::TraitFunctionDescription,
};
use derive_new::new;
use ustr::{Ustr, ustr};

use crate::{
    containers::B,
    r#type::{BareNativeType, Type},
};

#[derive(Debug, Clone)]
pub enum TypeDefLookupResult {
    Enum(TypeDefRef, Ustr),
    Struct(TypeDefRef),
}
impl TypeDefLookupResult {
    pub fn lookup_payload(&self) -> (TypeDefRef, Option<Ustr>) {
        use TypeDefLookupResult::*;
        match self {
            Enum(type_def, tag) => (type_def.clone(), Some(*tag)),
            Struct(type_def) => (type_def.clone(), None),
        }
    }
}

#[derive(Clone, Copy, Debug, new)]
pub struct ModuleEnv<'m> {
    pub(crate) current: &'m Module,
    pub(crate) modules: &'m Modules,
}

impl<'m> ModuleEnv<'m> {
    pub fn type_alias_name(&self, ty: Type) -> Option<String> {
        self.current.type_aliases.get_name(ty).map_or_else(
            || {
                self.modules.iter_named().find_map(|(mod_path, entry)| {
                    entry.module().and_then(|module| {
                        module.type_aliases.get_name(ty).map(|ty_name| {
                            if self.current.uses(mod_path, ty_name) {
                                ty_name.to_string()
                            } else {
                                format!("{mod_path}::{ty_name}")
                            }
                        })
                    })
                })
            },
            |name| Some(name.to_string()),
        )
    }

    pub fn bare_native_name(&self, native: &B<dyn BareNativeType>) -> Option<String> {
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
            .map(|(_, ty)| ty))
    }

    /// Like [`type_alias_type`], but also returns the source [`ModuleId`] when the alias
    /// is defined in another module (`None` means it belongs to the current module).
    pub fn type_alias_type_with_module(
        &self,
        path: &ast::Path,
    ) -> Result<Option<(Option<ModuleId>, Type)>, InternalCompilationError> {
        self.get_module_member(&path.segments, &|name, module| {
            module.get_type_alias(ustr(name))
        })
    }

    /// Look up a bare native type alias by path, returning the bare native type and the source
    /// module id (None means the current module).
    pub fn bare_native_type_alias_with_module(
        &self,
        path: &ast::Path,
    ) -> Result<Option<(Option<ModuleId>, crate::containers::B<dyn BareNativeType>)>, InternalCompilationError> {
        self.get_module_member(&path.segments, &|name, module| {
            module.get_bare_native_type_alias(ustr(name))
        })
    }

    pub fn type_def_with_module(
        &self,
        path: &ast::Path,
    ) -> Result<Option<(Option<ModuleId>, TypeDefRef)>, InternalCompilationError> {
        self.get_module_member(&path.segments, &|name, module| {
            module.get_type_def(ustr(name)).cloned()
        })
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
                    module.get_type_def(ustr(name))
                })?
            {
                if ty_def.is_enum() {
                    let ty_data = ty_def.shape_ty().data();
                    let variants = ty_data.as_variant().unwrap();
                    let variant = variants.iter().find(|(name, _)| *name == variant_name);
                    if let Some((tag, _)) = variant {
                        let td = TypeDefLookupResult::Enum(ty_def.clone(), *tag);
                        return Ok(Some((module_id, td)));
                    }
                }
            }
        }
        // Not found, search for a matching struct
        if len >= 1 {
            if let Some((module_id, ty_def)) =
                self.get_module_member(segments, &|name, module| module.get_type_def(ustr(name)))?
            {
                if ty_def.is_struct_like() {
                    let td = TypeDefLookupResult::Struct(ty_def.clone());
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
        Ok(self
            .type_def_with_module(path)?
            .and_then(|(_, type_def)| type_def.param_names.is_empty().then(|| type_def.as_type())))
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
                type_def
                    .param_names
                    .is_empty()
                    .then(|| (module_id, type_def.as_type()))
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

    /// Get the trait reference associated to a trait name.
    pub fn get_trait_ref(
        &'m self,
        name: UstrSpan,
    ) -> Result<Option<TraitRef>, InternalCompilationError> {
        Ok(self
            .trait_ref_with_module(&ast::Path::single_tuple(name))?
            .map(|(_, trait_ref)| trait_ref))
    }

    pub fn trait_ref_with_module(
        &'m self,
        path: &'m ast::Path,
    ) -> Result<Option<(Option<ModuleId>, TraitRef)>, InternalCompilationError> {
        self.get_module_member(&path.segments, &|name, module| {
            module.trait_iter().find_map(|trait_ref| {
                if trait_ref.name == name {
                    Some(trait_ref.clone())
                } else {
                    None
                }
            })
        })
    }

    /// Get a trait function from the current module, or other ones, return the ID of the module if other.
    pub fn get_trait_function(
        &'m self,
        path: &'m ast::Path,
    ) -> Result<Option<(Option<ModuleId>, TraitFunctionDescription<'m>)>, InternalCompilationError>
    {
        self.get_module_member(&path.segments, &|name, module| {
            module.trait_iter().find_map(|trait_ref| {
                trait_ref
                    .functions
                    .iter()
                    .enumerate()
                    .find_map(|(index, function)| {
                        if function.0 == name {
                            Some((trait_ref.clone(), index, &function.1))
                        } else {
                            None
                        }
                    })
            })
        })
    }

    /// Get a member of a module, by first looking in the current module, and then in others, considering the path.
    fn get_module_member<'a, T>(
        &'a self,
        segments: &'a [UstrSpan],
        getter: &impl Fn(/*name*/ &'a str, /*current*/ &'a Module) -> Option<T>,
    ) -> Result<Option<(Option<ModuleId>, T)>, InternalCompilationError> {
        // If the name is not qualified, look in the current module.
        if let [(name, _)] = segments {
            return self.current.get_member(name, self.modules, getter);
        }
        // The name is qualified, split between path and symbol name.
        if let Some(path) = segments.split_last() {
            let ((sym_name, _), module) = path;
            // Special case when compiling std.
            if let [single_segment] = module
                && single_segment.0 == "std"
                && self.current.module_id() == STD_MODULE_ID
            {
                return self.current.get_member(sym_name, self.modules, getter);
            }
            // Look into the foreign module, if it exists.
            let path = Path::from_ast_segments(module);
            Ok(
                if let Some((foreign_id, foreign_entry)) = self.modules.get_by_name(&path)
                    && let Some(module) = foreign_entry.module()
                {
                    getter(sym_name, module)
                        .map(|t| Some((Some(foreign_id), t)))
                        .unwrap_or(None)
                } else {
                    None
                },
            )
        } else {
            Ok(None)
        }
    }
}
