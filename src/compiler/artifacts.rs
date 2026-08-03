// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::cell::OnceCell;

use crate::{
    compiler::Modules,
    emit_mir::build_mir_function,
    mir,
    module::{LocalFunctionId, Module, ModuleEnv, ModuleId, id::Id},
};

/// Backend output derived from one completed semantic module revision.
#[derive(Default)]
pub(crate) struct ModuleArtifacts {
    mir: OnceCell<MirArtifacts>,
}

impl std::fmt::Debug for ModuleArtifacts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ModuleArtifacts")
            .field("mir_function_slots", &self.mir.get().map(MirArtifacts::len))
            .finish()
    }
}

impl ModuleArtifacts {
    pub(crate) fn with_mir(module: &Module, modules: &Modules) -> Self {
        let artifacts = Self::default();
        artifacts
            .mir
            .set(MirArtifacts::build(module, modules))
            .unwrap_or_else(|_| unreachable!("a new artifact set cannot already contain MIR"));
        artifacts
    }

    pub(crate) fn has_mir(&self) -> bool {
        self.mir.get().is_some()
    }

    pub(crate) fn mir(&self) -> Option<&MirArtifacts> {
        self.mir.get()
    }

    pub(crate) fn set_mir(&self, mir: MirArtifacts) {
        self.mir
            .set(mir)
            .unwrap_or_else(|_| panic!("MIR artifacts may only be installed once per revision"));
    }
}

/// MIR bodies aligned one-for-one with a module's dense local function table.
///
/// Native functions have no MIR body; every script function has exactly one.
pub(crate) struct MirArtifacts {
    functions: Vec<Option<mir::Function>>,
}

impl MirArtifacts {
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
                    .map(|_| build_mir_function(id, env))
            })
            .collect();
        Self { functions }
    }

    pub(crate) fn get(&self, id: LocalFunctionId) -> Option<&mir::Function> {
        self.functions.get(id.as_index())?.as_ref()
    }

    pub(crate) fn len(&self) -> usize {
        self.functions.len()
    }
}

/// Install complete MIR artifacts for a fresh module and all of its dependencies.
pub(crate) fn ensure_mir_artifacts(modules: &Modules, module_id: ModuleId) {
    let entry = modules
        .get(module_id)
        .unwrap_or_else(|| panic!("module {module_id} is not registered"));
    assert!(
        !entry.stale,
        "module {module_id} is stale and cannot receive current MIR artifacts"
    );
    if entry.current_mir().is_some() {
        return;
    }

    let dependencies = entry
        .module()
        .expect("a fresh module entry must contain its module")
        .deps()
        .collect::<Vec<_>>();
    for dependency in dependencies {
        ensure_mir_artifacts(modules, dependency);
    }

    let mir = {
        let module = modules
            .get(module_id)
            .unwrap()
            .module()
            .expect("a fresh module entry must contain its module");
        MirArtifacts::build(module, modules)
    };
    modules.get(module_id).unwrap().artifacts().set_mir(mir);
}
