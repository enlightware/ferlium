// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Immutable callee inputs for each optimization stage.

use crate::{
    compiler::{CompilerSession, MirArtifacts, MirOptimization},
    mir::Function,
    module::{FunctionId, ModuleEnv, ModuleId, id::Id},
};

use super::Specializations;

/// A pass must never substitute a semantic body for a physical callee.
#[derive(Clone, Copy)]
pub(crate) enum OptimizationStage<'a> {
    Semantic {
        session: &'a CompilerSession,
        specializations: Option<&'a Specializations>,
    },
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
            Self::Semantic { .. } => true,
            Self::Physical {
                module, semantic, ..
            } => callee.module == module && semantic.get(callee.function).is_none(),
        }
    }

    pub(crate) fn body(self, callee: FunctionId) -> Option<&'a Function> {
        match self {
            Self::Semantic {
                session,
                specializations,
            } => {
                if let Some(specializations) = specializations
                    && specializations.is_specialization(callee)
                {
                    return specializations.raw_body(callee.function);
                }
                session
                    .mir_artifacts_for(callee.module, MirOptimization::Disabled)?
                    .get(callee.function)
            }
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
            Self::Semantic {
                session,
                specializations,
            } => match specializations {
                Some(specializations) => specializations.original(callee).unwrap_or(callee),
                None => session.hir_identity_of(callee, MirOptimization::Enabled),
            },
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
            Self::Semantic { session, .. } => session.expect_fresh_module(original.module),
            Self::Physical { .. } => env
                .module_by_id(original.module)
                .expect("physical callee's module must be available"),
        };
        module
            .get_function_by_id(original.function)
            .is_some_and(|function| function.definition.is_inline_never())
    }
}
