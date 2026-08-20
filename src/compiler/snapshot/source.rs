use crate::parser::location::SourceTable;

/// Stable source-table data. Line indexes are derived again rather than persisted.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotSource {
    pub(crate) name: String,
    pub(crate) text: String,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SnapshotSourceTable {
    pub(crate) sources: Vec<SnapshotSource>,
}

impl SnapshotSourceTable {
    pub(crate) fn capture(table: &SourceTable) -> Self {
        let sources = table
            .entries()
            .map(|source| SnapshotSource {
                name: source.name().clone(),
                text: source.source().clone(),
            })
            .collect::<Vec<_>>();
        debug_assert_eq!(
            sources.first().map(|source| source.name.as_str()),
            Some("<synthesized>"),
            "source zero must remain the synthesized SourceTable entry"
        );
        Self { sources }
    }

    pub(crate) fn materialize(&self) -> SourceTable {
        let mut table = SourceTable::default();
        // Source zero is the synthesized entry supplied by Default.
        for source in self.sources.iter().skip(1) {
            table.add_source(source.name.clone(), source.text.clone());
        }
        table
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_table_round_trip_rebuilds_derived_line_indexes() {
        let mut original = SourceTable::default();
        let source = original.add_source("example.fer".into(), "one\ntwo\n".into());
        let snapshot = SnapshotSourceTable::capture(&original);
        let restored = snapshot.materialize();

        assert_eq!(restored.len(), original.len());
        assert_eq!(restored.get_source_name(source).unwrap(), "example.fer");
        assert_eq!(restored.get_source_text(source).unwrap(), "one\ntwo\n");
        assert_eq!(restored.get_line_column(source, 4), (2, 1));
    }
}
