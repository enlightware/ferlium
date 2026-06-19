// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

pub mod diagnostics;
pub mod error;
mod pipeline;
mod session;

pub use diagnostics::ModuleDiagnostic;
pub use error::*;
pub(crate) use pipeline::add_code_to_module;
pub use pipeline::parse_module_and_expr;
pub(crate) use session::Modules;
pub use session::{
    CompilationCapabilities, CompilationRevision, CompilerSession, ModuleAndExpr, ModuleInfo,
    ModuleRegistry, ModuleSource, ModuleUpdateResult, SourceVersion,
};

#[doc(hidden)]
pub mod test_support {
    use crate::{
        compiler::{CompilationRevision, CompilerSession, Modules, SourceVersion},
        module::ModuleId,
    };

    pub fn raw_modules(session: &CompilerSession) -> &Modules {
        &session.modules
    }

    pub fn module_entry_exists(session: &CompilerSession, module_id: ModuleId) -> bool {
        session.modules.get(module_id).is_some()
    }

    pub fn module_is_stale(session: &CompilerSession, module_id: ModuleId) -> Option<bool> {
        Some(session.modules.get(module_id)?.is_stale())
    }

    pub fn module_has_compiled_version(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> Option<bool> {
        Some(session.modules.get(module_id)?.module().is_some())
    }

    pub fn module_source_version(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> Option<SourceVersion> {
        session.modules.get(module_id)?.source_version()
    }

    pub fn module_compilation_revision(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> Option<CompilationRevision> {
        Some(session.modules.get(module_id)?.compilation_revision())
    }

    pub fn module_diagnostics_len(session: &CompilerSession, module_id: ModuleId) -> Option<usize> {
        Some(session.modules.get(module_id)?.diagnostics().len())
    }

    pub fn module_latest_deps(
        session: &CompilerSession,
        module_id: ModuleId,
    ) -> Option<Vec<ModuleId>> {
        Some(session.modules.get(module_id)?.latest_deps().to_vec())
    }
}
