/// Current on-disk schema number. It is independent of cache staleness fingerprints: changing a
/// DTO or its encoding increments this number, while changing std/compiler inputs changes one of
/// the fingerprints below.
pub(crate) const STD_SNAPSHOT_FORMAT_VERSION: u32 = 1;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StdSnapshotHeader {
    pub(crate) format_version: u32,
    pub(crate) std_source_fingerprint: String,
    pub(crate) semantic_build_fingerprint: String,
    pub(crate) native_offer_fingerprint: String,
}

impl StdSnapshotHeader {
    pub(crate) fn current(native_offer_fingerprint: String) -> Self {
        Self {
            format_version: STD_SNAPSHOT_FORMAT_VERSION,
            std_source_fingerprint: env!("FERLIUM_STD_SOURCE_FINGERPRINT").to_owned(),
            semantic_build_fingerprint: env!("FERLIUM_SEMANTIC_BUILD_FINGERPRINT").to_owned(),
            native_offer_fingerprint,
        }
    }

    pub(crate) fn matches_current(&self, native_offer_fingerprint: &str) -> bool {
        self.format_version == STD_SNAPSHOT_FORMAT_VERSION
            && self.std_source_fingerprint == env!("FERLIUM_STD_SOURCE_FINGERPRINT")
            && self.semantic_build_fingerprint == env!("FERLIUM_SEMANTIC_BUILD_FINGERPRINT")
            && self.native_offer_fingerprint == native_offer_fingerprint
    }
}

/// Versioned envelope for compiled std data. The payload is deliberately named `StdSnapshot`,
/// rather than baking the schema version into the Rust type name.
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
    fn header_checks_schema_sources_semantics_and_native_offer() {
        let header = StdSnapshotHeader::current("native-v1".to_owned());
        assert!(header.matches_current("native-v1"));
        assert!(!header.matches_current("native-v2"));

        let mut wrong_schema = header;
        wrong_schema.format_version += 1;
        assert!(!wrong_schema.matches_current("native-v1"));
    }
}
