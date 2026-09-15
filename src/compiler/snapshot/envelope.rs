// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use crate::{module::ModuleId, std::STD_MODULE_ID};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StdSnapshotHeader {
    pub(crate) module: ModuleId,
    pub(crate) module_path: String,
    pub(crate) std_source_fingerprint: String,
    pub(crate) semantic_build_fingerprint: String,
    pub(crate) native_offer_fingerprint: String,
}

impl StdSnapshotHeader {
    pub(crate) fn current(native_offer_fingerprint: String) -> Self {
        Self {
            module: STD_MODULE_ID,
            module_path: "std".into(),
            std_source_fingerprint: env!("FERLIUM_STD_SOURCE_FINGERPRINT").to_owned(),
            semantic_build_fingerprint: env!("FERLIUM_SEMANTIC_BUILD_FINGERPRINT").to_owned(),
            native_offer_fingerprint,
        }
    }

    pub(crate) fn matches_current(&self, native_offer_fingerprint: &str) -> bool {
        self.module == STD_MODULE_ID
            && self.module_path == "std"
            && self.std_source_fingerprint == env!("FERLIUM_STD_SOURCE_FINGERPRINT")
            && self.semantic_build_fingerprint == env!("FERLIUM_SEMANTIC_BUILD_FINGERPRINT")
            && self.native_offer_fingerprint == native_offer_fingerprint
    }
}

/// Fingerprint-validated envelope for compiler-owned std data.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StdSnapshot<T> {
    pub(crate) header: StdSnapshotHeader,
    pub(crate) payload: T,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_checks_sources_semantics_and_native_offer() {
        let header = StdSnapshotHeader::current("native-v1".to_owned());
        assert!(header.matches_current("native-v1"));
        assert!(!header.matches_current("native-v2"));
    }
}
