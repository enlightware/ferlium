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
    mir::{
        self,
        pass::{
            Specializations, dead_evidence, optimize_function,
            provenance::{AddressorSummaries, AddressorSummary},
        },
    },
    module::{FunctionId, LocalFunctionId, Module, ModuleEnv, ModuleId, id::Id},
};

use ustr::Ustr;

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

/// A body the optimizer created by specializing another function at one instantiation.
///
/// It has no entry in the module's HIR function table — nothing in the source declared it — so
/// everything the rest of the compiler reads through a `FunctionId` comes from `original` instead.
/// That indirection is the whole cost of specialization's storage, and it is cheap precisely because
/// a specialized body keeps its original's *visible* signature, so no metadata is duplicated. Its
/// hidden evidence parameters are dropped by
/// [`dead_evidence`](crate::mir::pass::dead_evidence), which no HIR record describes.
pub(crate) struct Specialization {
    /// The function this was specialized from, and the source of all its metadata.
    pub(crate) original: FunctionId,
    /// A generated name, following the same shape as the compiler's generated impl functions:
    /// a readable original, a `#spec:` marker, and a discriminator.
    pub(crate) name: Ustr,
    pub(crate) body: mir::Function,
}

/// MIR bodies aligned one-for-one with a module's dense local function table, plus any bodies the
/// optimizer specialized.
///
/// Native functions have no MIR body; every script function has exactly one.
///
/// **Specializations extend the table past the HIR function count.** A [`LocalFunctionId`] at or
/// beyond `functions.len()` names one, and only ever in the optimized stage — the raw stage is
/// always exactly the HIR table. That is what makes a `FunctionId` meaningful only in a
/// `(module, stage)` context, and what lets the two stages be told apart without a flag.
pub(crate) struct MirArtifacts {
    functions: Vec<Option<mir::Function>>,
    specializations: Vec<Specialization>,
    /// The cached provenance and repeatability of every addressor.
    ///
    /// Derived once, from the *raw* bodies, and carried into the optimized stage unchanged:
    /// These are properties of what a function does, which optimization preserves. Kept here
    /// rather than recomputed because a consumer's callee is often in another module, and a
    /// dependency's summaries have to be readable the way its bodies already are.
    addressor_summaries: AddressorSummaries,
}

impl MirArtifacts {
    pub(crate) fn build(module: &Module, modules: &Modules) -> Self {
        let env = ModuleEnv::new(module, modules);
        let functions: Vec<Option<mir::Function>> = (0..module.function_count())
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
        // Every dependency's artifacts are built before this module's, so a cross-module callee's
        // summary is already installed and can simply be read.
        let external = |callee: FunctionId| {
            modules
                .get(callee.module)
                .and_then(|entry| entry.raw_mir())
                .map_or(AddressorSummary::UNKNOWN, |artifacts| {
                    artifacts.addressor_summary(callee.module, callee.function)
                })
        };
        let addressor_summaries =
            AddressorSummaries::of_module(&functions, module.module_id(), env, &external);
        Self {
            functions,
            specializations: Vec::new(),
            addressor_summaries,
        }
    }

    /// The place and evaluation properties of the addressor `id`, if known.
    ///
    /// A specialization of a local original inherits its summary. A cross-module specialization
    /// cannot be answered from this module's table and is conservatively unknown; optimizer passes
    /// resolve its `Specialization::original` before selecting that original module's artifacts.
    pub(crate) fn addressor_summary(
        &self,
        module: ModuleId,
        id: LocalFunctionId,
    ) -> AddressorSummary {
        match self.specialization(id) {
            Some(specialization) if specialization.original.module == module => self
                .addressor_summaries
                .summary(specialization.original.function),
            Some(_) => AddressorSummary::UNKNOWN,
            None => self.addressor_summaries.summary(id),
        }
    }

    /// Runs the optimization passes over every body in `raw`.
    ///
    /// Every body is opened for editing and closed again, whether or not a pass changed it: closing
    /// re-verifies, so a body no pass touched still proves that editing preserves identities and is
    /// genuinely the identity.
    ///
    /// Takes the whole session because the folding passes const-evaluate through the MIR
    /// interpreter, which resolves callees, dictionaries, and native code through it.
    ///
    /// Specialization makes this two-staged. Optimizing a body may ask for a specialized copy of a
    /// callee, which is itself a body needing optimization — that is the whole point, since binding
    /// its dictionaries is what lets folding resolve them. So the declared functions are optimized
    /// first, then the specializations they requested are drained as a worklist, which may request
    /// more. [`MAX_SPECIALIZATIONS`](crate::mir::pass::budget::MAX_SPECIALIZATIONS) bounds the
    /// total, so a chain of generic callees cannot expand without end.
    pub(crate) fn optimize(raw: &MirArtifacts, module: &Module, session: &CompilerSession) -> Self {
        let modules = session.raw_modules();
        let env = ModuleEnv::new(module, modules);
        let module_id = module.module_id();
        let mut specializations = Specializations::new(module_id, raw.functions.len());

        let mut functions: Vec<Option<mir::Function>> = raw
            .functions
            .iter()
            .map(|function| {
                function.as_ref().map(|function| {
                    optimize_function(function, env, session, module_id, &mut specializations)
                })
            })
            .collect();

        // Drain the worklist. A specialization created while optimizing one is appended past the
        // end, so this walk reaches it too.
        let mut next = 0;
        while next < specializations.len() {
            let id = LocalFunctionId::from_index(functions.len() + next);
            let body = specializations
                .body(id)
                .expect("a specialization just created has a body")
                .clone();
            let optimized = optimize_function(&body, env, session, module_id, &mut specializations);
            specializations.set_body(id, optimized);
            next += 1;
        }

        // Last, over the finished bodies. Every decision above was taken against the signatures the
        // optimizer has always seen; this only narrows the calling convention of bodies nothing
        // will consult again.
        let specializations = dead_evidence::drop_dead_specialization_evidence(
            &mut functions,
            specializations.into_created(),
            module_id,
            env,
        );

        Self {
            functions,
            specializations,
            // Carried across unchanged: optimization preserves a proved root and repeatability.
            // A specialization may admit a more precise summary after substitution, but reusing
            // its original's conservative answer is sound and avoids per-stage recomputation.
            addressor_summaries: raw.addressor_summaries.clone(),
        }
    }

    pub(crate) fn get(&self, id: LocalFunctionId) -> Option<&mir::Function> {
        match self.specialization(id) {
            Some(specialization) => Some(&specialization.body),
            None => self.functions.get(id.as_index())?.as_ref(),
        }
    }

    /// The specialization `id` names, if it names one rather than a function the source declared.
    pub(crate) fn specialization(&self, id: LocalFunctionId) -> Option<&Specialization> {
        self.specializations
            .get(id.as_index().checked_sub(self.functions.len())?)
    }

    /// Every body the *source* declared, in local function order, with `None` where a function has
    /// no MIR (a native).
    ///
    /// Deliberately excludes specializations: this is what pairs the two artifact stages up, and
    /// only the HIR-declared prefix exists in both. A caller that wants specializations too has to
    /// ask for them, which is what stops them being silently dropped from a zip.
    pub(crate) fn bodies(&self) -> &[Option<mir::Function>] {
        &self.functions
    }

    /// Every specialized body, in the order the optimizer created them.
    pub(crate) fn specializations(&self) -> &[Specialization] {
        &self.specializations
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
