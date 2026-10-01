// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Source locations of MIR code, with the call sites it was inlined through.
//!
//! Inlining copies a callee's operations into its caller. Each copy keeps the callee's own source
//! location, and additionally records the call site it was copied through, whose own location may
//! in turn have been inlined somewhere: a chain from the innermost call site outward, as LLVM's
//! `DILocation::inlinedAt`.
//!
//! Chains are interned into a table of [`InlineSites`], one per module revision: every stage of that
//! module adds to the same table, in the fixed order the stages are built in. An [`InlineSiteId`] is
//! therefore meaningful only within one module's table. When a body moves into another module — by
//! inlining or by specialization — its chains are copied into the destination table by an
//! [`InlineRebase`], so no table ever refers to another.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{Location, define_id_type, module::id::Id};

define_id_type!(
    /// A call site that code was inlined through, in one module's [`InlineSites`].
    InlineSiteId
);

/// A MIR operation's or terminator's source location, and the call sites it was inlined through.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DebugLocation {
    /// The source of the code itself, in the function that wrote it.
    pub location: Location,
    /// The innermost call site this code was inlined through, if any.
    pub inlined_at: Option<InlineSiteId>,
}

impl DebugLocation {
    /// Code written where it is, not inlined.
    pub fn new(location: Location) -> Self {
        Self {
            location,
            inlined_at: None,
        }
    }

    /// Code the compiler produced without a source of its own.
    pub fn new_synthesized() -> Self {
        Self::new(Location::new_synthesized())
    }

    pub fn is_synthesized(&self) -> bool {
        self.location.is_synthesized()
    }
}

impl From<Location> for DebugLocation {
    fn from(location: Location) -> Self {
        Self::new(location)
    }
}

/// One link of an inline chain: a call site, and the call site that one was inlined through.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InlineSite {
    pub call: Location,
    pub parent: Option<InlineSiteId>,
}

/// The interned inline chains of one module revision.
///
/// Append-only, so an id stays valid for as long as the table lives. Equal links intern to one id,
/// so two chains are equal exactly when their ids are.
#[derive(Clone, Debug, Default)]
pub struct InlineSites {
    sites: Vec<InlineSite>,
    interned: FxHashMap<InlineSite, InlineSiteId>,
}

impl InlineSites {
    pub fn intern(&mut self, site: InlineSite) -> InlineSiteId {
        debug_assert!(
            site.parent
                .is_none_or(|parent| parent.as_index() < self.sites.len()),
            "an inline site's parent is interned before it"
        );
        *self.interned.entry(site).or_insert_with(|| {
            let id = InlineSiteId::from_index(self.sites.len());
            self.sites.push(site);
            id
        })
    }

    pub fn get(&self, id: InlineSiteId) -> InlineSite {
        self.sites[id.as_index()]
    }

    pub fn len(&self) -> usize {
        self.sites.len()
    }

    pub fn is_empty(&self) -> bool {
        self.sites.is_empty()
    }

    /// Every link, in the order it was interned.
    pub fn sites(&self) -> &[InlineSite] {
        &self.sites
    }

    /// Restores the links of a snapshot of this table: `sites` must extend what this table
    /// already holds, which the fixed build order of the stages guarantees. Returns whether it did.
    pub fn restore(&mut self, sites: &[InlineSite]) -> bool {
        if !sites.starts_with(&self.sites) {
            return false;
        }
        // A captured table holds no duplicate, and interns parents first.
        let start = self.sites.len();
        let added = &sites[start..];
        let mut seen = FxHashSet::default();
        let valid = added.iter().enumerate().all(|(offset, site)| {
            site.parent
                .is_none_or(|parent| parent.as_index() < start + offset)
                && !self.interned.contains_key(site)
                && seen.insert(*site)
        });
        if !valid {
            return false;
        }
        for &site in added {
            self.intern(site);
        }
        true
    }

    /// The call sites of `inlined_at`, from the innermost outward.
    pub fn call_sites(
        &self,
        mut inlined_at: Option<InlineSiteId>,
    ) -> impl Iterator<Item = Location> + '_ {
        std::iter::from_fn(move || {
            let site = self.get(inlined_at?);
            inlined_at = site.parent;
            Some(site.call)
        })
    }
}

/// Copies inline chains from the table a body was read from into the table it is copied into,
/// optionally adding the call site it is inlined at as their new outermost link.
///
/// One rebase serves one copied body: it caches the translation of each distinct source chain, so
/// the cost is per chain rather than per operation.
pub struct InlineRebase {
    /// The call site the body is inlined at, already in the destination table; `None` when the body
    /// moves without being inlined, as a specialization does.
    base: Option<InlineSiteId>,
    translated: FxHashMap<InlineSiteId, Option<InlineSiteId>>,
}

impl InlineRebase {
    /// Rebases a body inlined at `call`, a location in the destination.
    pub fn inlined_at(call: DebugLocation, destination: &mut InlineSites) -> Self {
        let base = destination.intern(InlineSite {
            call: call.location,
            parent: call.inlined_at,
        });
        Self::new(Some(base))
    }

    /// Rebases a body that moves between tables without being inlined.
    pub fn moved() -> Self {
        Self::new(None)
    }

    fn new(base: Option<InlineSiteId>) -> Self {
        Self {
            base,
            translated: FxHashMap::default(),
        }
    }

    /// Translates `span` from `source` — `None` when that is the destination itself.
    pub fn span(
        &mut self,
        span: DebugLocation,
        source: Option<&InlineSites>,
        destination: &mut InlineSites,
    ) -> DebugLocation {
        DebugLocation {
            location: span.location,
            inlined_at: self.chain(span.inlined_at, source, destination),
        }
    }

    fn chain(
        &mut self,
        inlined_at: Option<InlineSiteId>,
        source: Option<&InlineSites>,
        destination: &mut InlineSites,
    ) -> Option<InlineSiteId> {
        let Some(id) = inlined_at else {
            return self.base;
        };
        // Moving within one table changes nothing.
        if source.is_none() && self.base.is_none() {
            return Some(id);
        }
        if let Some(&translated) = self.translated.get(&id) {
            return translated;
        }
        let site = match source {
            Some(source) => source.get(id),
            None => destination.get(id),
        };
        let parent = self.chain(site.parent, source, destination);
        let translated = Some(destination.intern(InlineSite {
            call: site.call,
            parent,
        }));
        self.translated.insert(id, translated);
        translated
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SourceId;

    fn at(start: u32) -> Location {
        Location::new(start, start + 1, SourceId::new(1))
    }

    #[test]
    fn inlining_appends_the_call_site_outermost() {
        // `max` inlined into `clamp` in one module…
        let mut dependency = InlineSites::default();
        let max_in_clamp = dependency.intern(InlineSite {
            call: at(10),
            parent: None,
        });
        let compare = DebugLocation {
            location: at(1),
            inlined_at: Some(max_in_clamp),
        };
        let own = DebugLocation::new(at(2));

        // …then `clamp` inlined into another at a call that was itself inlined.
        let mut module = InlineSites::default();
        let outer = module.intern(InlineSite {
            call: at(30),
            parent: None,
        });
        let call = DebugLocation {
            location: at(20),
            inlined_at: Some(outer),
        };
        let mut rebase = InlineRebase::inlined_at(call, &mut module);
        let compare = rebase.span(compare, Some(&dependency), &mut module);
        let own = rebase.span(own, Some(&dependency), &mut module);

        assert_eq!(compare.location, at(1));
        assert_eq!(
            module.call_sites(compare.inlined_at).collect::<Vec<_>>(),
            [at(10), at(20), at(30)]
        );
        assert_eq!(
            module.call_sites(own.inlined_at).collect::<Vec<_>>(),
            [at(20), at(30)]
        );
        // Rebasing the same chain again reuses its links.
        let length = module.len();
        let again = rebase.span(
            DebugLocation {
                location: at(3),
                inlined_at: Some(max_in_clamp),
            },
            Some(&dependency),
            &mut module,
        );
        assert_eq!(again.inlined_at, compare.inlined_at);
        assert_eq!(module.len(), length);
    }

    #[test]
    fn a_snapshot_restores_only_over_the_table_it_extends() {
        let site = |start| InlineSite {
            call: at(start),
            parent: None,
        };
        let mut captured = InlineSites::default();
        captured.intern(site(1));
        captured.intern(site(2));

        // An empty table, or one holding what the snapshot starts with, takes the rest.
        let mut empty = InlineSites::default();
        assert!(empty.restore(captured.sites()));
        assert_eq!(empty.sites(), captured.sites());
        let mut prefix = InlineSites::default();
        prefix.intern(site(1));
        assert!(prefix.restore(captured.sites()));
        assert_eq!(prefix.sites(), captured.sites());

        // A table that diverged would give the snapshot's ids other meanings.
        let mut diverged = InlineSites::default();
        diverged.intern(site(3));
        assert!(!diverged.restore(captured.sites()));

        // Nor can a table hold the same link twice, or a parent after its child.
        let mut empty = InlineSites::default();
        assert!(!empty.restore(&[site(1), site(1)]));
        let orphan = InlineSite {
            call: at(4),
            parent: Some(InlineSiteId::from_index(1)),
        };
        assert!(!empty.restore(&[orphan, site(1)]));
        assert!(empty.is_empty());
    }

    #[test]
    fn a_moved_body_keeps_its_chains() {
        let mut dependency = InlineSites::default();
        let site = dependency.intern(InlineSite {
            call: at(10),
            parent: None,
        });
        let mut module = InlineSites::default();
        module.intern(InlineSite {
            call: at(99),
            parent: None,
        });
        let mut rebase = InlineRebase::moved();
        let span = DebugLocation {
            location: at(1),
            inlined_at: Some(site),
        };
        let moved = rebase.span(span, Some(&dependency), &mut module);
        assert_eq!(
            module.call_sites(moved.inlined_at).collect::<Vec<_>>(),
            [at(10)]
        );
        let not_inlined = rebase.span(DebugLocation::new(at(2)), Some(&dependency), &mut module);
        assert_eq!(not_inlined.inlined_at, None);
        // Within one table, nothing changes.
        assert_eq!(rebase.span(moved, None, &mut module), moved);
    }
}
