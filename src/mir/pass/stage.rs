// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Immutable callee inputs for each optimization stage.

use crate::{
    compiler::{CompilerSession, MirArtifacts, MirOptimization},
    mir::Function,
    module::{FunctionId, ModuleEnv, ModuleId, id::Id},
};

use super::{Specializations, provenance::AddressorSummary};

/// A pass must never substitute a semantic body for a physical callee.
#[derive(Clone, Copy)]
pub(crate) enum OptimizationStage<'a> {
    Semantic(SemanticCallees<'a>),
    Physical {
        module: ModuleId,
        bodies: &'a [Option<Function>],
        semantic: &'a MirArtifacts,
    },
}

impl<'a> OptimizationStage<'a> {
    /// Physical expansion gets its own budget for generated helpers and expanded native slots,
    /// not source bodies already optimized semantically. Bodyless natives are rejected by `body`.
    pub(crate) fn permits_inlining(self, callee: FunctionId) -> bool {
        match self {
            Self::Semantic(_) => true,
            Self::Physical {
                module, semantic, ..
            } => callee.module == module && semantic.get(callee.function).is_none(),
        }
    }

    pub(crate) fn body(self, callee: FunctionId) -> Option<&'a Function> {
        match self {
            Self::Semantic(callees) => callees.body(callee),
            // Foreign bodies are deliberately opaque until an immutable expanded dependency view
            // is available. Reading already optimized dependencies would make this stage asymmetric.
            Self::Physical { module, bodies, .. } if callee.module == module => {
                bodies.get(callee.function.as_index())?.as_ref()
            }
            Self::Physical { .. } => None,
        }
    }

    pub(crate) fn original(self, callee: FunctionId) -> FunctionId {
        match self {
            Self::Semantic(callees) => callees.original(callee),
            Self::Physical {
                module, semantic, ..
            } if callee.module == module => semantic
                .specialization(callee.function)
                .map_or(callee, |entry| entry.original),
            Self::Physical { .. } => callee,
        }
    }

    pub(crate) fn inline_never(self, callee: FunctionId, env: ModuleEnv<'_>) -> bool {
        let original = self.original(callee);
        let module = match self {
            Self::Semantic(callees) => callees.session.expect_fresh_module(original.module),
            Self::Physical { .. } => env
                .module_by_id(original.module)
                .expect("physical callee's module must be available"),
        };
        module
            .get_function_by_id(original.function)
            .is_some_and(|function| function.definition.is_inline_never())
    }
}

/// Callee identities and facts for semantic optimization; each module answers for its own.
///
/// The module being optimized is read raw, with its specializations from the table under
/// construction, so that no decision depends on optimization order. A dependency is already
/// optimized and immutable, so its identities resolve through its optimized artifact. Without a
/// table, every module resolves through its optimized artifact.
#[derive(Clone, Copy)]
pub(crate) struct SemanticCallees<'a> {
    session: &'a CompilerSession,
    specializations: Option<&'a Specializations>,
}

impl<'a> SemanticCallees<'a> {
    pub(crate) fn new(
        session: &'a CompilerSession,
        specializations: Option<&'a Specializations>,
    ) -> Self {
        Self {
            session,
            specializations,
        }
    }

    pub(crate) fn session(self) -> &'a CompilerSession {
        self.session
    }

    pub(crate) fn specializations(self) -> Option<&'a Specializations> {
        self.specializations
    }

    /// The declared function `callee` specializes, or `callee` itself.
    pub(crate) fn original(self, callee: FunctionId) -> FunctionId {
        let Some(specializations) = self.specializations else {
            return self
                .session
                .hir_identity_of(callee, MirOptimization::Enabled);
        };
        if let Some(original) = specializations.original(callee) {
            return original;
        }
        if callee.module == specializations.module() {
            return callee;
        }
        self.session
            .mir_artifacts_for(callee.module, MirOptimization::Enabled)
            .expect("a dependency is optimized before the modules that use it")
            .specialization(callee.function)
            .map_or(callee, |specialization| specialization.original)
    }

    /// The raw body of `callee`; a specialization of this module is read as it was created.
    pub(crate) fn body(self, callee: FunctionId) -> Option<&'a Function> {
        if let Some(specializations) = self.specializations
            && specializations.is_specialization(callee)
        {
            return specializations.raw_body(callee.function);
        }
        self.session
            .mir_artifacts_for(callee.module, MirOptimization::Disabled)?
            .get(callee.function)
    }

    /// The place and evaluation properties of `callee` as an addressor, if known.
    pub(crate) fn addressor_summary(self, callee: FunctionId) -> AddressorSummary {
        let original = self.original(callee);
        self.session
            .mir_artifacts_for(original.module, MirOptimization::Disabled)
            .map_or(AddressorSummary::UNKNOWN, |artifacts| {
                artifacts.addressor_summary(original.module, original.function)
            })
    }

    /// Whether every valid invocation of `callee` is proved to complete.
    pub(crate) fn will_return(self, callee: FunctionId) -> bool {
        let original = self.original(callee);
        self.session
            .mir_artifacts_for(original.module, MirOptimization::Disabled)
            .is_some_and(|artifacts| {
                artifacts
                    .will_return(original.module, original.function)
                    .is_proven()
            })
    }

    /// [`Self::original`] as the passes' `original_of` callback.
    pub(crate) fn original_of(self) -> impl Fn(FunctionId) -> Option<FunctionId> + Copy + 'a {
        move |callee| Some(self.original(callee))
    }
}
