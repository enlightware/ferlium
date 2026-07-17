// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    compiler::Modules,
    emit_ssa::build_ssa_function,
    module::{LocalFunctionId, Module, ModuleEnv, ModuleId, id::Id},
    ssa,
};

/// Backend output derived from one completed semantic module revision.
#[derive(Default)]
pub(crate) struct ModuleArtifacts {
    ssa: Option<SsaArtifacts>,
}

impl std::fmt::Debug for ModuleArtifacts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ModuleArtifacts")
            .field(
                "ssa_function_slots",
                &self.ssa.as_ref().map(SsaArtifacts::len),
            )
            .finish()
    }
}

impl ModuleArtifacts {
    pub(crate) fn with_ssa(module: &Module, modules: &Modules) -> Self {
        Self {
            ssa: Some(SsaArtifacts::build(module, modules)),
        }
    }

    pub(crate) fn has_ssa(&self) -> bool {
        self.ssa.is_some()
    }

    pub(crate) fn ssa(&self) -> Option<&SsaArtifacts> {
        self.ssa.as_ref()
    }

    pub(crate) fn set_ssa(&mut self, ssa: SsaArtifacts) {
        self.ssa = Some(ssa);
    }
}

/// SSA bodies aligned one-for-one with a module's dense local function table.
///
/// Native functions have no SSA body; every script function has exactly one.
pub(crate) struct SsaArtifacts {
    functions: Vec<Option<ssa::Function>>,
}

impl SsaArtifacts {
    pub(crate) fn build(module: &Module, modules: &Modules) -> Self {
        let env = ModuleEnv::new(module, modules);
        let functions = (0..module.function_count())
            .map(LocalFunctionId::from_index)
            .map(|id| {
                let function = module
                    .get_function_by_id(id)
                    .expect("local function table must be dense");
                function
                    .code
                    .as_ref()
                    .as_script()
                    .map(|_| build_ssa_function(id, env))
            })
            .collect();
        Self { functions }
    }

    pub(crate) fn get(&self, id: LocalFunctionId) -> Option<&ssa::Function> {
        self.functions.get(id.as_index())?.as_ref()
    }

    pub(crate) fn len(&self) -> usize {
        self.functions.len()
    }
}

/// Install complete SSA artifacts for a fresh module and all of its dependencies.
pub(crate) fn ensure_ssa_artifacts(modules: &mut Modules, module_id: ModuleId) {
    let entry = modules
        .get(module_id)
        .unwrap_or_else(|| panic!("module {module_id} is not registered"));
    assert!(
        !entry.stale,
        "module {module_id} is stale and cannot receive current SSA artifacts"
    );
    if entry.current_ssa().is_some() {
        return;
    }

    let dependencies = entry
        .module()
        .expect("a fresh module entry must contain its module")
        .deps()
        .collect::<Vec<_>>();
    for dependency in dependencies {
        ensure_ssa_artifacts(modules, dependency);
    }

    let ssa = {
        let module = modules
            .get(module_id)
            .unwrap()
            .module()
            .expect("a fresh module entry must contain its module");
        SsaArtifacts::build(module, modules)
    };
    modules.get_mut(module_id).unwrap().artifacts.set_ssa(ssa);
}
