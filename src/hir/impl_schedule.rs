// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! The order in which a module's impls, and the functions they use, are inferred.
//!
//! Every impl not emitted yet is pending. An item whose inference consulted a pending impl that
//! could change a decision, such as "no impl applies" or "this is the only candidate", is blocked:
//! its attempt is undone and retried once another item has been committed. So each committed item
//! is inferred as it would be against the complete module, whatever the source order.

use std::rc::Rc;

use crate::{
    FxHashMap, Location,
    ast::{self, FunctionAstIndex, ImplAstIndex, ModuleImplementationAstIndex, Path},
    compiler::{diagnostics::CompilationWarning, error::InternalCompilationError},
    desugar::ModuleImplementationDependencies,
    hir::emit_hir::{EmissionCtx, ModuleEmission},
    internal_compilation_error,
    module::{Module, ModuleEnv, PendingImpl, PendingImpls, id::Id},
    types::r#trait::TraitMethodIndex,
};

/// An item scheduled with the impls.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Candidate {
    /// A source impl.
    Impl(ImplAstIndex),
    /// An implementation SCC that impls reach, a helper, by index.
    Helper(usize),
}

struct CandidateInfo {
    candidate: Candidate,
    /// The helpers that must be committed before this candidate is attempted.
    requires: Vec<usize>,
    span: Location,
}

/// The impls of a module and their helpers, to be emitted in an order where no pending impl can
/// change their inference.
pub(super) struct ImplSchedule {
    /// In source order.
    candidates: Vec<CandidateInfo>,
    /// Whether each implementation SCC is a helper.
    helpers: Vec<bool>,
    /// What each source impl's header says before it is emitted. `None` for impls whose
    /// interface is registered before any emission, and for impls of unknown traits, whose
    /// emission fails.
    pending: Vec<Option<PendingImpl>>,
}

impl ImplSchedule {
    pub(super) fn new(
        output: &Module,
        emission: &ModuleEmission<'_>,
        dependencies: &ModuleImplementationDependencies,
    ) -> Self {
        let source = emission.source;
        let env = ModuleEnv::new(output, emission.others);
        let default_functions = emission
            .trait_defaults
            .iter()
            .map(|(function, method)| (*method, *function))
            .collect::<FxHashMap<_, _>>();

        // An impl requires the SCCs its methods name, and those of the defaults it inherits.
        let mut pending = Vec::with_capacity(source.impls.len());
        let mut impl_requires = Vec::with_capacity(source.impls.len());
        for (position, imp) in source.impls.iter().enumerate() {
            let index = ImplAstIndex::from_index(position);
            let mut requires = dependencies.impls[position].clone();
            let trait_id = env
                .trait_id_with_module(&Path::single_tuple(imp.trait_name))
                .ok()
                .flatten()
                .map(|(_, trait_id)| trait_id);
            if let Some(trait_id) = trait_id {
                let trait_def = env.trait_def(trait_id);
                for (method_index, (name, _)) in trait_def.methods.iter().enumerate() {
                    let written = imp
                        .functions
                        .iter()
                        .any(|function| function.name.0 == *name);
                    let default = default_functions
                        .get(&(trait_id, TraitMethodIndex::new(method_index as u32)))
                        .copied();
                    if let (false, Some(default)) = (written, default) {
                        requires.push(dependencies.function_sccs[default.as_index()]);
                    }
                }
            }
            requires.sort_unstable();
            requires.dedup();
            impl_requires.push(requires);
            let is_stub = emission.concrete_impl_stubs.contains_key(&index);
            pending.push(trait_id.filter(|_| !is_stub).map(|trait_id| {
                PendingImpl {
                    index,
                    trait_id,
                    input_tys: imp
                        .for_trait
                        .as_ref()
                        .map(|for_trait| for_trait.input_tys()),
                }
            }));
        }

        // Helpers are the SCCs that impls reach.
        let mut helpers = vec![false; emission.sccs.len()];
        let mut stack = impl_requires.iter().flatten().copied().collect::<Vec<_>>();
        while let Some(scc) = stack.pop() {
            if !helpers[scc] {
                helpers[scc] = true;
                stack.extend(dependencies.sccs[scc].iter().copied());
            }
        }

        let mut candidates = impl_requires
            .into_iter()
            .enumerate()
            .map(|(position, requires)| CandidateInfo {
                candidate: Candidate::Impl(ImplAstIndex::from_index(position)),
                requires,
                span: source.impls[position].span,
            })
            .chain(
                helpers
                    .iter()
                    .enumerate()
                    .filter(|(_, helper)| **helper)
                    .map(|(scc, _)| CandidateInfo {
                        candidate: Candidate::Helper(scc),
                        requires: dependencies.sccs[scc].clone(),
                        span: scc_span(source, &emission.sccs[scc]),
                    }),
            )
            .collect::<Vec<_>>();
        candidates.sort_by_key(|info| info.span.start());
        Self {
            candidates,
            helpers,
            pending,
        }
    }

    /// Whether the implementation SCC at `scc` is emitted by the schedule.
    pub(super) fn is_helper(&self, scc: usize) -> bool {
        self.helpers[scc]
    }

    /// Emit the impls and their helpers. At each step, attempt the first candidate in source
    /// order whose required helpers are committed and that has not been blocked since the last
    /// commit. Every commit enables a candidate, so this ends after at most `n` sweeps of at most
    /// `n` attempts. It fails when every remaining candidate is blocked.
    pub(super) fn run(
        &self,
        ctx: &mut EmissionCtx<'_>,
        emission: &ModuleEmission<'_>,
        warnings: &mut Vec<CompilationWarning>,
    ) -> Result<(), InternalCompilationError> {
        let mut remaining = self.candidates.iter().collect::<Vec<_>>();
        let mut committed = vec![false; self.helpers.len()];
        let mut blocked = FxHashMap::<Candidate, Vec<ImplAstIndex>>::default();
        while let Some(position) = remaining.iter().position(|info| {
            !blocked.contains_key(&info.candidate)
                && info.requires.iter().all(|scc| committed[*scc])
        }) {
            let candidate = remaining[position].candidate;
            // An impl is never visible while it is inferred, whatever the order, so its own
            // header cannot make its inference order dependent.
            let pending = remaining
                .iter()
                .filter(|info| info.candidate != candidate)
                .filter_map(|info| match info.candidate {
                    Candidate::Impl(index) => self.pending[index.as_index()].clone(),
                    Candidate::Helper(_) => None,
                })
                .collect::<Vec<_>>();
            let mut attempt_warnings = Vec::new();
            if pending.is_empty() {
                self.emit(ctx, emission, candidate, &mut attempt_warnings)?;
            } else {
                let replaced_functions = match candidate {
                    Candidate::Impl(index) => emission
                        .concrete_impl_stubs
                        .get(&index)
                        .map(|stub| stub.method_ids.as_slice())
                        .unwrap_or_default(),
                    Candidate::Helper(_) => &[],
                };
                let checkpoint = ctx.output.checkpoint(replaced_functions);
                let pending = Rc::new(PendingImpls::new(pending));
                ctx.output.impls.pending = pending.clone();
                let result = self.emit(ctx, emission, candidate, &mut attempt_warnings);
                let blockers = pending.blockers();
                if !blockers.is_empty() {
                    log::trace!("Emission of {candidate:?} blocked by impls {blockers:?}");
                    ctx.output.restore(checkpoint);
                    blocked.insert(candidate, blockers);
                    continue;
                }
                ctx.output.impls.pending = Rc::default();
                result?;
            }
            warnings.extend(attempt_warnings);
            match candidate {
                // Only the impls that blocked an attempt can change its outcome.
                Candidate::Impl(index) => blocked.retain(|_, blockers| !blockers.contains(&index)),
                Candidate::Helper(scc) => committed[scc] = true,
            }
            remaining.remove(position);
        }
        if remaining.is_empty() {
            return Ok(());
        }
        let blocked = remaining
            .iter()
            .filter_map(|info| {
                let blockers = blocked.get(&info.candidate)?;
                Some((
                    info.span,
                    blockers
                        .iter()
                        .map(|index| emission.source.impls[index.as_index()].span)
                        .collect(),
                ))
            })
            .collect();
        Err(internal_compilation_error!(
            InferenceBlockedByPendingImpls { blocked }
        ))
    }

    fn emit(
        &self,
        ctx: &mut EmissionCtx<'_>,
        emission: &ModuleEmission<'_>,
        candidate: Candidate,
        warnings: &mut Vec<CompilationWarning>,
    ) -> Result<(), InternalCompilationError> {
        match candidate {
            Candidate::Impl(index) => emission.emit_impl(ctx, index, warnings),
            Candidate::Helper(scc) => emission.emit_scc(ctx, scc, warnings),
        }
    }
}

/// Where an implementation SCC starts in the source.
fn scc_span(source: &ast::DModule, scc: &ast::ModuleImplementationScc) -> Location {
    scc.implementations
        .iter()
        .map(|implementation| match *implementation {
            ModuleImplementationAstIndex::Function(index) => function_span(source, index),
            ModuleImplementationAstIndex::SubscriptMember { subscript, .. } => {
                source.subscripts[subscript.as_index()].span
            }
        })
        .min_by_key(Location::start)
        .expect("an implementation SCC is not empty")
}

fn function_span(source: &ast::DModule, index: FunctionAstIndex) -> Location {
    source.functions[index.as_index()].span
}
