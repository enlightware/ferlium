// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::rc::Rc;

use crate::{
    ast::{self, UstrSpan},
    error::InternalCompilationError,
    module::{Module, ModuleFunction, Modules, path::Path},
    r#trait::TraitRef,
    r#type::TypeDefRef,
    typing_env::TraitFunctionDescription,
};
use derive_new::new;
use ustr::{Ustr, ustr};

use crate::{
    containers::B,
    function::FunctionRc,
    r#type::{BareNativeType, Type},
};

#[derive(Debug, Clone)]
pub enum TypeDefLookupResult {
    Enum(TypeDefRef, Ustr, Type),
    Struct(TypeDefRef),
}
impl TypeDefLookupResult {
    pub fn lookup_payload(&self) -> (TypeDefRef, Type, Option<Ustr>) {
        use TypeDefLookupResult::*;
        match self {
            Enum(type_def, tag, variant_ty) => (type_def.clone(), *variant_ty, Some(*tag)),
            Struct(type_def) => {
                let payload_ty = type_def.shape;
                (type_def.clone(), payload_ty, None)
            }
        }
    }
}

#[derive(Clone, Copy, Debug, new)]
pub struct ModuleEnv<'m> {
    pub(crate) current: &'m Module,
    pub(crate) others: &'m Modules,
    pub(crate) within_std: bool,
}

impl<'m> ModuleEnv<'m> {
    pub fn type_alias_name(&self, ty: Type) -> Option<String> {
        self.current.type_aliases.get_name(ty).map_or_else(
            || {
                self.others.modules.iter().find_map(|(mod_path, module)| {
                    module.type_aliases.get_name(ty).map(|ty_name| {
                        if self.current.uses(mod_path, ty_name) {
                            ty_name.to_string()
                        } else {
                            format!("{mod_path}::{ty_name}")
                        }
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
                    self.others.modules.iter().find_map(|(mod_name, module)| {
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
                module.type_aliases.get_type(&ustr(name))
            })?
            .map(|(_, ty)| ty))
    }

    pub fn type_def_for_construction(
        &self,
        path: &ast::Path,
    ) -> Result<Option<TypeDefLookupResult>, InternalCompilationError> {
        // First search for a matching enum
        let segments = &path.segments;
        let len = segments.len();
        if len >= 2 {
            let enum_segments = &segments[0..len - 1];
            let variant_name = segments[len - 1].0;
            if let Some((_, ty_def)) = self.get_module_member(enum_segments, &|name, module| {
                module.type_defs.get(&ustr(name)).cloned()
            })? {
                if ty_def.is_enum() {
                    let ty_data = ty_def.shape.data();
                    let variants = ty_data.as_variant().unwrap();
                    let variant = variants.iter().find(|(name, _)| *name == variant_name);
                    if let Some((tag, ty)) = variant {
                        return Ok(Some(TypeDefLookupResult::Enum(ty_def.clone(), *tag, *ty)));
                    }
                }
            }
        }
        // Not found, search for a matching struct
        if len >= 1 {
            if let Some((_, ty_def)) = self.get_module_member(segments, &|name, module| {
                module.type_defs.get(&ustr(name)).cloned()
            })? {
                if ty_def.is_struct_like() {
                    return Ok(Some(TypeDefLookupResult::Struct(ty_def.clone())));
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
            .get_module_member(&path.segments, &|name, module| {
                module.type_defs.get(&ustr(name)).cloned()
            })?
            .map(|(_, ty_def)| ty_def.as_type()))
    }

    pub fn function_name(&self, func: &FunctionRc) -> Option<String> {
        // FIXME: this needs update
        self.current
            .functions
            .iter()
            .find(|local_fn| Rc::ptr_eq(&local_fn.function.code, func))
            .map_or_else(
                || {
                    self.others.modules.iter().find_map(|(mod_name, module)| {
                        module
                            .functions
                            .iter()
                            .find(|local_fn| Rc::ptr_eq(&local_fn.function.code, func))
                            .map(|local_fn| {
                                let fn_name = local_fn.name;
                                if self.current.uses(mod_name, fn_name) {
                                    fn_name.to_string()
                                } else {
                                    format!("{mod_name}::{fn_name}")
                                }
                            })
                    })
                },
                |local_fn| Some(local_fn.name.to_string()),
            )
    }

    /// Get a function from the current module, or other ones, return the name of the module if other.
    pub fn get_function(
        &'m self,
        path: &'m [UstrSpan],
    ) -> Result<Option<(Option<Path>, &'m ModuleFunction)>, InternalCompilationError> {
        self.get_module_member(path, &|name, module| {
            module.get_unique_own_function(ustr(name))
        })
    }

    /// Get a function from the current module, or other ones, return the name of the module if other.
    pub fn get_program_function(
        &'m self,
        path: &'m [UstrSpan],
    ) -> Result<Option<(Option<Path>, &'m ModuleFunction)>, InternalCompilationError> {
        self.get_module_member(path, &|name, module| {
            module.get_unique_own_function(ustr(name))
        })
    }

    /// Get the trait reference associated to a trait name.
    pub fn get_trait_ref(
        &'m self,
        name: UstrSpan,
    ) -> Result<Option<TraitRef>, InternalCompilationError> {
        Ok(self
            .get_module_member(&[name], &|name, module| {
                module.traits.iter().find_map(|trait_ref| {
                    if trait_ref.name == name {
                        Some(trait_ref.clone())
                    } else {
                        None
                    }
                })
            })?
            .map(|(_, t)| t))
    }

    /// Get a trait function from the current module, or other ones, return the name of the module if other.
    pub fn get_trait_function(
        &'m self,
        path: &'m ast::Path,
    ) -> Result<Option<(Option<Path>, TraitFunctionDescription<'m>)>, InternalCompilationError>
    {
        self.get_module_member(&path.segments, &|name, module| {
            module.traits.iter().find_map(|trait_ref| {
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
    fn get_module_member<T>(
        &'m self,
        segments: &'m [UstrSpan],
        getter: &impl Fn(/*name*/ &'m str, /*current*/ &'m Module) -> Option<T>,
    ) -> Result<Option<(Option<Path>, T)>, InternalCompilationError> {
        if let [(name, _)] = segments {
            return self.current.get_member(name, self.others, getter);
        }
        if let Some(path) = segments.split_last() {
            let ((function_name, _), module) = path;
            if let [single_segment] = module
                && single_segment.0 == "std"
                && self.within_std
            {
                return self.current.get_member(function_name, self.others, getter);
            }
            let path = Path::new(module.iter().map(|(seg, _)| *seg).collect());
            self.others.get(&path).map_or(Ok(None), |module| {
                module.get_member(function_name, self.others, getter)
            })
        } else {
            Ok(None)
        }
    }
}
