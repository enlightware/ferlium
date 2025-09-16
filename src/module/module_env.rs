// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::rc::Rc;

use crate::{
    module::{Module, ModuleFunction, Modules},
    r#trait::TraitRef,
    r#type::TypeDefRef,
    typing_env::TraitFunctionDescription,
};
use derive_new::new;
use itertools::Itertools;
use ustr::{ustr, Ustr};

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
}

impl<'m> ModuleEnv<'m> {
    pub fn type_alias_name(&self, ty: Type) -> Option<String> {
        self.current.type_aliases.get_name(ty).map_or_else(
            || {
                self.others.modules.iter().find_map(|(mod_name, module)| {
                    module.type_aliases.get_name(ty).map(|ty_name| {
                        if self.current.uses(*mod_name, ty_name) {
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
                                if self.current.uses(*mod_name, ty_name) {
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

    pub fn type_alias_type(&self, path: &str) -> Option<Type> {
        self.get_module_member(path, &|name, module| {
            module.type_aliases.get_type(&ustr(name))
        })
        .map(|(_, ty)| ty)
    }

    pub fn type_def_for_construction(&self, joined_path: &str) -> Option<TypeDefLookupResult> {
        let path = joined_path.split("::").collect::<Vec<_>>();
        // First search for a matching enum
        let len = path.len();
        if len >= 2 {
            // FIXME: this is inefficient, we should keep the split path all the way from parsing
            let enum_path = path[0..=len - 2].join("::");
            let variant_name = path[len - 1];
            if let Some((_, ty_def)) = self.get_module_member(&enum_path, &|name, module| {
                module.type_defs.get(&ustr(name)).cloned()
            }) {
                if ty_def.is_enum() {
                    let ty_data = ty_def.shape.data();
                    let variants = ty_data.as_variant().unwrap();
                    let variant = variants
                        .iter()
                        .find(|(name, _)| name.as_str() == variant_name);
                    if let Some((tag, ty)) = variant {
                        return Some(TypeDefLookupResult::Enum(ty_def.clone(), *tag, *ty));
                    }
                }
            }
        }
        // Not found, search for a matching struct
        if len >= 1 {
            if let Some((_, ty_def)) = self.get_module_member(joined_path, &|name, module| {
                module.type_defs.get(&ustr(name)).cloned()
            }) {
                if ty_def.is_struct_like() {
                    return Some(TypeDefLookupResult::Struct(ty_def.clone()));
                }
            }
        }

        None
    }

    pub fn type_def_type(&self, path: &str) -> Option<Type> {
        self.get_module_member(path, &|name, module| {
            module.type_defs.get(&ustr(name)).cloned()
        })
        .map(|(_, ty_def)| ty_def.as_type())
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
                                if let Some(fn_name) = fn_name {
                                    if self.current.uses(*mod_name, fn_name) {
                                        fn_name.to_string()
                                    } else {
                                        format!("{mod_name}::{fn_name}")
                                    }
                                } else {
                                    "<anonymous>".to_string()
                                }
                            })
                    })
                },
                |local_fn| Some(local_fn.name.unwrap_or(ustr("anonymous")).to_string()),
            )
    }

    /// Get a function from the current module, or other ones, return the name of the module if other.
    pub fn get_function(&'m self, path: &'m str) -> Option<(Option<Ustr>, &'m ModuleFunction)> {
        self.get_module_member(path, &|name, module| module.get_own_function(ustr(name)))
    }

    /// Get a function from the current module, or other ones, return the name of the module if other.
    pub fn get_program_function(
        &'m self,
        path: &'m str,
    ) -> Option<(Option<Ustr>, &'m ModuleFunction)> {
        self.get_module_member(path, &|name, module| module.get_own_function(ustr(name)))
    }

    /// Get the trait reference associated to a trait name.
    pub fn get_trait_ref(&'m self, path: &'m str) -> Option<TraitRef> {
        self.get_module_member(path, &|name, module| {
            module.traits.iter().find_map(|trait_ref| {
                if trait_ref.name == name {
                    Some(trait_ref.clone())
                } else {
                    None
                }
            })
        })
        .map(|(_, t)| t)
    }

    /// Get a trait function from the current module, or other ones, return the name of the module if other.
    pub fn get_trait_function(
        &'m self,
        path: &'m str,
    ) -> Option<(Option<Ustr>, TraitFunctionDescription<'m>)> {
        self.get_module_member(path, &|name, module| {
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
        path: &'m str,
        getter: &impl Fn(/*name*/ &'m str, /*current*/ &'m Module) -> Option<T>,
    ) -> Option<(Option<Ustr>, T)> {
        self.current
            .get_member(path, self.others, getter)
            .or_else(|| {
                let path = path.split("::").next_tuple();
                if let Some(path) = path {
                    let (module_name, function_name) = path;
                    let module_name = ustr(module_name);
                    self.others
                        .get(&module_name)
                        .and_then(|module| module.get_member(function_name, self.others, getter))
                } else {
                    None
                }
            })
    }
}
