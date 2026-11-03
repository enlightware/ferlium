// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Same-module impls not emitted yet, and the decisions that depend on them.
//!
//! A solver answer that one of these impls could change once emitted is blocked: "no impl
//! applies", "this is the only candidate", "derive since none is written". The solver still
//! returns its answer from the visible impls, but records the pending impls it depends on. The
//! attempt that asked is then discarded as a whole, so no caller can turn a blocked answer into
//! a decision. Positive answers, proven by a visible impl, stay valid when impls are added and
//! record nothing.

use std::{cell::RefCell, collections::BTreeSet, mem, rc::Rc};

use crate::{
    ast::ImplAstIndex,
    module::TraitId,
    types::r#type::{Type, TypeKind},
};

/// A same-module impl not emitted yet, described by what its source writes.
#[derive(Clone, Debug)]
pub(crate) struct PendingImpl {
    /// The index of the impl in its module's source.
    pub(crate) index: ImplAstIndex,
    pub(crate) trait_id: TraitId,
    /// The written input types, whose variables are the impl's generic parameters. `None` for an
    /// impl without a header, which may match any application of its trait.
    pub(crate) input_tys: Option<Vec<Type>>,
}

impl PendingImpl {
    fn may_match(&self, trait_id: TraitId, input_tys: &[Type]) -> bool {
        self.trait_id == trait_id
            && self
                .input_tys
                .as_ref()
                .is_none_or(|header| all_may_match(header, input_tys, 0))
    }
}

/// The same-module impls not emitted yet, shared by every solver over the module.
#[derive(Debug, Default)]
pub(crate) struct PendingImpls {
    impls: Vec<PendingImpl>,
    /// The indices of the pending impls that an answer depended on.
    blockers: RefCell<BTreeSet<ImplAstIndex>>,
}

impl PendingImpls {
    pub(crate) fn new(impls: Vec<PendingImpl>) -> Self {
        Self {
            impls,
            blockers: RefCell::default(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.impls.is_empty()
    }

    /// Whether a pending impl may match the application of `trait_id` at `input_tys`, under any
    /// substitution of the variables of either. Each impl that may is recorded as a blocker.
    ///
    /// Call this where the visible impls would otherwise conclude that none, or a single one,
    /// applies.
    pub(crate) fn blocks(&self, trait_id: TraitId, input_tys: &[Type]) -> bool {
        if self.impls.is_empty() {
            return false;
        }
        let mut blocked = false;
        for imp in &self.impls {
            if imp.may_match(trait_id, input_tys) {
                self.blockers.borrow_mut().insert(imp.index);
                blocked = true;
            }
        }
        blocked
    }

    /// Record every pending impl as a blocker, for an answer given up on: any of them could have
    /// changed it.
    pub(crate) fn block_all(&self) {
        self.blockers
            .borrow_mut()
            .extend(self.impls.iter().map(|imp| imp.index));
    }

    /// The source indices of the pending impls that an answer depended on, in source order.
    pub(crate) fn blockers(&self) -> Vec<ImplAstIndex> {
        self.blockers.borrow().iter().copied().collect()
    }
}

/// A search over alternative impl candidates, stopping at the first that applies.
///
/// A candidate that fails may record blockers while checking its prerequisites. If the search
/// fails, they stand, as the pending impls could change the answer. If another candidate of a fully
/// determined application succeeds, they do not matter: should a pending impl later make the failed
/// candidate apply too, the two would overlap, and coherence rejects the module.
pub(crate) struct CandidateSearch {
    pending: Rc<PendingImpls>,
    /// The blockers recorded before the search.
    before: BTreeSet<ImplAstIndex>,
    /// The blockers recorded by the candidates that failed so far.
    failed: BTreeSet<ImplAstIndex>,
}

impl CandidateSearch {
    pub(crate) fn new(pending: &Rc<PendingImpls>) -> Self {
        Self {
            pending: pending.clone(),
            before: pending.blockers.borrow().clone(),
            failed: BTreeSet::new(),
        }
    }

    /// Start examining a candidate, the previous one having failed.
    pub(crate) fn next_candidate(&mut self) {
        let mut blockers = self.pending.blockers.borrow_mut();
        self.failed.append(&mut blockers);
        blockers.clone_from(&self.before);
    }

    /// The current candidate applies to a fully determined application.
    pub(crate) fn succeed(&mut self) {
        self.failed.clear();
    }
}

/// Any other way of leaving the search, including an error, keeps the blockers of failed candidates.
impl Drop for CandidateSearch {
    fn drop(&mut self) {
        self.pending
            .blockers
            .borrow_mut()
            .append(&mut mem::take(&mut self.failed));
    }
}

/// Beyond this depth, types are assumed to match: recursive types unfold indefinitely.
const MATCH_DEPTH_LIMIT: usize = 64;

/// Whether some substitution of the type variables of `header` and `query` may make them the
/// same type. Effects and mutability are not compared, and a variable occurring
/// twice may stand for different types: the answer errs towards "may match".
fn types_may_match(header: Type, query: Type, depth: usize) -> bool {
    if depth > MATCH_DEPTH_LIMIT {
        return true;
    }
    let depth = depth + 1;
    use TypeKind::*;
    match (&*header.data(), &*query.data()) {
        (Variable(_), _) | (_, Variable(_)) => true,
        (Never, Never) => true,
        (Native(header), Native(query)) => {
            header.bare_ty == query.bare_ty
                && all_may_match(&header.arguments, &query.arguments, depth)
        }
        (Named(header), Named(query)) => {
            header.def == query.def && all_may_match(&header.params, &query.params, depth)
        }
        (Tuple(header), Tuple(query)) => all_may_match(header, query, depth),
        (Record(header), Record(query)) | (Variant(header), Variant(query)) => {
            header.len() == query.len()
                && header
                    .iter()
                    .zip(query)
                    .all(|((header_name, header), (query_name, query))| {
                        header_name == query_name && types_may_match(*header, *query, depth)
                    })
        }
        (Function(header), Function(query)) => {
            header.args.len() == query.args.len()
                && header
                    .args
                    .iter()
                    .zip(&query.args)
                    .all(|(header, query)| types_may_match(header.ty, query.ty, depth))
                && types_may_match(header.ret, query.ret, depth)
        }
        (Subscript(_), Subscript(_)) => true,
        _ => false,
    }
}

fn all_may_match(headers: &[Type], queries: &[Type], depth: usize) -> bool {
    headers.len() == queries.len()
        && headers
            .iter()
            .zip(queries)
            .all(|(header, query)| types_may_match(*header, *query, depth))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        module::{LocalTraitId, ModuleId},
        std::{array_type::array_type, logic::bool_type, math::int_type},
        types::{effects::EffType, r#type::FnType},
    };

    fn trait_id(index: u32) -> TraitId {
        TraitId::new(ModuleId::new(0), LocalTraitId::new(index))
    }

    #[test]
    fn headers_match_any_substitution_of_either_side() {
        let var = Type::variable_id;
        let may_match = |header, query| types_may_match(header, query, 0);
        assert!(may_match(var(0), int_type()));
        assert!(may_match(int_type(), var(0)));
        assert!(may_match(array_type(var(0)), array_type(int_type())));
        assert!(may_match(array_type(int_type()), array_type(var(3))));
        assert!(!may_match(array_type(int_type()), array_type(bool_type())));
        assert!(!may_match(array_type(int_type()), int_type()));
        assert!(!may_match(Type::never(), int_type()));
        assert!(!may_match(
            Type::tuple([var(0)]),
            Type::tuple([var(0), var(1)])
        ));
        assert!(may_match(
            Type::record(vec![(ustr::ustr("x"), var(0))]),
            Type::record(vec![(ustr::ustr("x"), int_type())])
        ));
        assert!(!may_match(
            Type::record(vec![(ustr::ustr("x"), var(0))]),
            Type::record(vec![(ustr::ustr("y"), int_type())])
        ));
        let function =
            |arg, ret, effects| Type::function_type(FnType::new_by_val(vec![arg], ret, effects));
        // Effects are not compared.
        assert!(may_match(
            function(int_type(), var(0), EffType::empty()),
            function(int_type(), bool_type(), EffType::single_variable_id(0))
        ));
        assert!(!may_match(
            function(int_type(), bool_type(), EffType::empty()),
            function(bool_type(), bool_type(), EffType::empty())
        ));
    }

    #[test]
    fn only_matching_pending_impls_block_and_are_recorded() {
        let pending = PendingImpls::new(vec![
            PendingImpl {
                index: ImplAstIndex::new(1),
                trait_id: trait_id(0),
                input_tys: Some(vec![int_type()]),
            },
            PendingImpl {
                index: ImplAstIndex::new(3),
                trait_id: trait_id(1),
                input_tys: None,
            },
        ]);
        assert!(!pending.blocks(trait_id(0), &[bool_type()]));
        assert!(!pending.blocks(trait_id(2), &[int_type()]));
        assert!(pending.blockers().is_empty());
        assert!(pending.blocks(trait_id(0), &[int_type()]));
        assert_eq!(pending.blockers(), vec![ImplAstIndex::new(1)]);
        // A headerless impl may match any application of its trait.
        assert!(pending.blocks(trait_id(1), &[array_type(bool_type())]));
        assert_eq!(
            pending.blockers(),
            vec![ImplAstIndex::new(1), ImplAstIndex::new(3)]
        );
    }

    #[test]
    fn a_successful_candidate_discards_the_blockers_of_failed_ones() {
        let pending = Rc::new(PendingImpls::new(vec![
            PendingImpl {
                index: ImplAstIndex::new(0),
                trait_id: trait_id(0),
                input_tys: None,
            },
            PendingImpl {
                index: ImplAstIndex::new(1),
                trait_id: trait_id(1),
                input_tys: None,
            },
            PendingImpl {
                index: ImplAstIndex::new(2),
                trait_id: trait_id(2),
                input_tys: None,
            },
        ]));
        pending.blocks(trait_id(0), &[int_type()]);

        // Failed, then successful: the blockers from before and of the success remain.
        let mut search = CandidateSearch::new(&pending);
        search.next_candidate();
        pending.blocks(trait_id(1), &[int_type()]);
        search.next_candidate();
        pending.blocks(trait_id(2), &[int_type()]);
        search.succeed();
        assert_eq!(
            pending.blockers(),
            vec![ImplAstIndex::new(0), ImplAstIndex::new(2)]
        );
    }

    #[test]
    fn a_search_left_without_success_keeps_all_blockers() {
        let pending = Rc::new(PendingImpls::new(vec![
            PendingImpl {
                index: ImplAstIndex::new(0),
                trait_id: trait_id(0),
                input_tys: None,
            },
            PendingImpl {
                index: ImplAstIndex::new(1),
                trait_id: trait_id(1),
                input_tys: None,
            },
        ]));
        {
            let mut search = CandidateSearch::new(&pending);
            search.next_candidate();
            pending.blocks(trait_id(0), &[int_type()]);
            search.next_candidate();
            pending.blocks(trait_id(1), &[int_type()]);
        }
        assert_eq!(
            pending.blockers(),
            vec![ImplAstIndex::new(0), ImplAstIndex::new(1)]
        );
    }
}
