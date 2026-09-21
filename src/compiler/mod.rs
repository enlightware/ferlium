// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

mod artifacts;
pub mod diagnostics;
pub mod error;
pub(crate) mod lints;
mod pipeline;
mod session;
#[cfg(feature = "std-snapshot")]
#[cfg_attr(
    any(
        not(feature = "std-cache"),
        all(target_arch = "wasm32", target_os = "unknown")
    ),
    allow(dead_code)
)]
pub(crate) mod snapshot;

pub use artifacts::MirOptimization;
/// Re-exported for tests that read a module's MIR without going through a compilation.
#[cfg(test)]
pub(crate) use artifacts::ensure_mir_artifacts;
pub(crate) use artifacts::{MirArtifacts, ModuleArtifacts, Specialization};
pub use diagnostics::{DiagnosticSeverity, ModuleDiagnostic};
pub use error::*;
pub(crate) use pipeline::add_code_to_module_with_capabilities;
pub use pipeline::parse_module_and_expr;
pub(crate) use session::Modules;
pub use session::{
    CompilationCapabilities, CompilationOutput, CompilationRevision, CompilerSession, ModuleInfo,
    ModuleRegistry, ModuleSource, SourceVersion,
};

#[doc(hidden)]
pub mod bench_support {
    pub use crate::compiler::session::reset_initial_session_state_cache;
}

#[doc(hidden)]
pub mod test_support {
    use crate::{
        compiler::{
            CompilationError, CompilationRevision, CompilerSession, SourceVersion,
            add_code_to_module_with_capabilities,
        },
        module::{Module, ModuleId},
    };

    /// Add script fixtures alongside a test module's typed native entries.
    pub fn add_module_source(
        session: &mut CompilerSession,
        module: Module,
        source: &str,
    ) -> Result<Module, CompilationError> {
        let module_id = module.module_id();
        add_code_to_module_with_capabilities(
            "<fixture>",
            source,
            module,
            module_id,
            &session.modules,
            &mut session.source_table,
            session.capabilities,
        )
    }

    pub fn module_entry_exists(session: &CompilerSession, module_id: ModuleId) -> bool {
        session.modules().contains(module_id)
    }

    pub fn module_is_stale(session: &CompilerSession, module_id: ModuleId) -> Option<bool> {
        Some(session.modules().info(module_id)?.is_stale())
    }

    pub fn module_has_compiled_version(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> Option<bool> {
        Some(session.modules().info(module_id)?.has_compiled_module())
    }

    pub fn module_source_version(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> Option<SourceVersion> {
        session.modules().info(module_id)?.source_version()
    }

    pub fn module_compilation_revision(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> Option<CompilationRevision> {
        Some(session.modules().info(module_id)?.compilation_revision())
    }

    pub fn module_diagnostics_len(session: &CompilerSession, module_id: ModuleId) -> Option<usize> {
        Some(session.modules().info(module_id)?.diagnostics().len())
    }

    pub fn module_latest_deps(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> Option<Vec<ModuleId>> {
        Some(session.modules().info(module_id)?.latest_deps().to_vec())
    }

    pub fn module_has_mir_artifacts(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> Option<bool> {
        Some(session.modules().info(module_id)?.has_mir_artifacts())
    }

    pub fn module_mir_function_slots(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> Option<usize> {
        session
            .modules
            .get(module_id)?
            .raw_mir()
            .map(|mir| mir.len())
    }
}
