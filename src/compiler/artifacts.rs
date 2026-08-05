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
    compiler::{CompilerSession, Modules},
    emit_mir::build_mir_function,
    mir::{self, pass::optimize_function},
    module::{LocalFunctionId, Module, ModuleEnv, ModuleId, id::Id},
};

/// Whether a compilation session runs the MIR optimization passes.
///
/// Optimized bodies are stored beside the raw ones rather than replacing them, and a session only
/// ever reads the stage it asked for. This matters because module revisions — the standard library
/// in particular — are shared between sessions: one session enabling optimization must not change
/// what another session executes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum MirOptimization {
    /// Execute the MIR the emitter produced.
    #[default]
    Disabled,
    /// Execute optimized MIR, building it on demand.
    Enabled,
}

/// Backend output derived from one completed semantic module revision.
///
/// Both stages are monotone: once installed, a stage is never replaced, so references handed out
/// of a session stay valid and artifact reuse remains observable by pointer identity.
#[derive(Default)]
pub(crate) struct ModuleArtifacts {
    /// MIR as lowered from final HIR by `emit_mir`.
    raw_mir: OnceCell<MirArtifacts>,
    /// MIR after the optimization passes, installed at most once and only when some session
    /// requested [`MirOptimization::Enabled`].
    optimized_mir: OnceCell<MirArtifacts>,
}

impl std::fmt::Debug for ModuleArtifacts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ModuleArtifacts")
            .field(
                "mir_function_slots",
                &self.raw_mir.get().map(MirArtifacts::len),
            )
            .field("optimized", &self.optimized_mir.get().is_some())
            .finish()
    }
}

impl ModuleArtifacts {
    pub(crate) fn with_mir(module: &Module, modules: &Modules) -> Self {
        let artifacts = Self::default();
        artifacts
            .raw_mir
            .set(MirArtifacts::build(module, modules))
            .unwrap_or_else(|_| unreachable!("a new artifact set cannot already contain MIR"));
        artifacts
    }

    pub(crate) fn has_mir(&self) -> bool {
        self.raw_mir.get().is_some()
    }

    /// The MIR the emitter produced, before optimization.
    pub(crate) fn raw_mir(&self) -> Option<&MirArtifacts> {
        self.raw_mir.get()
    }

    /// The MIR to execute under `optimization`.
    ///
    /// A session that requested optimization but reaches a module whose optimized stage was never
    /// built falls back to the raw bodies: they are equivalent, only slower.
    pub(crate) fn mir(&self, optimization: MirOptimization) -> Option<&MirArtifacts> {
        match optimization {
            MirOptimization::Disabled => self.raw_mir.get(),
            MirOptimization::Enabled => self.optimized_mir.get().or_else(|| self.raw_mir.get()),
        }
    }

    pub(crate) fn set_mir(&self, mir: MirArtifacts) {
        self.raw_mir
            .set(mir)
            .unwrap_or_else(|_| panic!("MIR artifacts may only be installed once per revision"));
    }

    fn set_optimized_mir(&self, mir: MirArtifacts) {
        self.optimized_mir.set(mir).unwrap_or_else(|_| {
            panic!("optimized MIR artifacts may only be installed once per revision")
        });
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

    /// Runs the optimization passes over every body in `raw`.
    ///
    /// Every body is opened for editing and closed again, whether or not a pass changed it: closing
    /// re-verifies, so a body no pass touched still proves that editing preserves identities and is
    /// genuinely the identity.
    ///
    /// Takes the whole session because the folding passes const-evaluate through the MIR
    /// interpreter, which resolves callees, dictionaries, and native code through it.
    pub(crate) fn optimize(raw: &MirArtifacts, module: &Module, session: &CompilerSession) -> Self {
        let modules = session.raw_modules();
        let env = ModuleEnv::new(module, modules);
        let functions = raw
            .functions
            .iter()
            .map(|function| {
                function
                    .as_ref()
                    .map(|function| optimize_function(function, env, session, module.module_id()))
            })
            .collect();
        Self { functions }
    }

    pub(crate) fn get(&self, id: LocalFunctionId) -> Option<&mir::Function> {
        self.functions.get(id.as_index())?.as_ref()
    }

    /// Every body, in local function order, with `None` where a function has no MIR (a native).
    pub(crate) fn bodies(&self) -> &[Option<mir::Function>] {
        &self.functions
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
    if entry.raw_mir().is_some() {
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

/// Install optimized MIR artifacts for a fresh module and all of its dependencies.
///
/// This is the post-installation optimization hook: unlike raw lowering — which runs while the
/// module being compiled is not yet registered — it runs against fully installed module entries, so
/// a pass may consult the bodies of the module it is optimizing as well as those of its
/// dependencies.
pub(crate) fn ensure_optimized_mir_artifacts(session: &CompilerSession, module_id: ModuleId) {
    let modules = session.raw_modules();
    ensure_mir_artifacts(modules, module_id);

    let entry = modules
        .get(module_id)
        .unwrap_or_else(|| panic!("module {module_id} is not registered"));
    if entry.artifacts().optimized_mir.get().is_some() {
        return;
    }

    let dependencies = entry
        .module()
        .expect("a fresh module entry must contain its module")
        .deps()
        .collect::<Vec<_>>();
    for dependency in dependencies {
        ensure_optimized_mir_artifacts(session, dependency);
    }

    let entry = modules.get(module_id).unwrap();
    let module = entry
        .module()
        .expect("a fresh module entry must contain its module");
    let raw = entry
        .raw_mir()
        .expect("raw MIR artifacts were just ensured for this module");
    let optimized = MirArtifacts::optimize(raw, module, session);
    entry.artifacts().set_optimized_mir(optimized);
}
