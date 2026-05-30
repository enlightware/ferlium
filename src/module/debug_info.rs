// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

//! Static debug information for compiled functions.

use ustr::Ustr;

use crate::{
    Location,
    hir::HirPhase,
    module::{LocalDecl, LocalFrameSlot},
    types::r#type::Type,
};

/// Whether a local came from user source or compiler-generated lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalDebugOrigin {
    User,
    Internal,
}

/// Source or lowered-code range where a debug entry is available.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DebugLocationRangeKey {
    Source(Location),
}

/// Runtime storage location for a local debug entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DebugStorage {
    LocalFrameSlot(LocalFrameSlot),
}

/// A range where a local debug entry has a particular storage location.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DebugLocationRange {
    pub range: DebugLocationRangeKey,
    pub storage: DebugStorage,
}

/// Static debug metadata for one local binding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalDebugInfo {
    pub name: Ustr,
    pub name_span: Location,
    pub ty: Type,
    pub origin: LocalDebugOrigin,
    pub locations: Vec<DebugLocationRange>,
}

/// Visibility filter used when presenting local debug entries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalDebugVisibility {
    User,
    All,
}

/// Static debug metadata for one compiled function.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionDebugInfo {
    pub locals: Vec<LocalDebugInfo>,
}

impl FunctionDebugInfo {
    pub fn from_locals<P: HirPhase>(locals: &[LocalDecl<P>]) -> Self {
        let locals = locals
            .iter()
            .map(LocalDebugInfo::from_local)
            .collect::<Vec<_>>();
        Self { locals }
    }

    pub fn locals_at_source(
        &self,
        location: Location,
        visibility: LocalDebugVisibility,
    ) -> Vec<&LocalDebugInfo> {
        self.locals
            .iter()
            .filter(|local| match visibility {
                LocalDebugVisibility::User => local.origin == LocalDebugOrigin::User,
                LocalDebugVisibility::All => true,
            })
            .filter(|local| local.is_available_at_source(location))
            .collect()
    }
}

impl LocalDebugInfo {
    fn from_local<P: HirPhase>(local: &LocalDecl<P>) -> Self {
        let (name, name_span) = local.name;
        let origin = if name.as_str().starts_with('$') || name_span.is_synthesized() {
            LocalDebugOrigin::Internal
        } else {
            LocalDebugOrigin::User
        };
        Self {
            name,
            name_span,
            ty: local.ty,
            origin,
            locations: vec![DebugLocationRange {
                range: DebugLocationRangeKey::Source(local.scope),
                storage: DebugStorage::LocalFrameSlot(local.slot),
            }],
        }
    }

    fn is_available_at_source(&self, location: Location) -> bool {
        self.locations.iter().any(|range| match range.range {
            DebugLocationRangeKey::Source(scope) => {
                scope.source_id() == location.source_id()
                    && scope.start() <= location.start()
                    && location.start() <= scope.end()
            }
        })
    }
}
