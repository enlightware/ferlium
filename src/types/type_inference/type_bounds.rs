// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Directional subtype obligations between equality-normalized type terms.
//!
//! This component performs only equivalence-preserving propagation. It neither
//! chooses an exact solution nor constructs a type shape. Structural pairs are
//! returned to the structural solver; equality normalization must rebuild the
//! graph from its seeds before those pairs are reused.

use std::{collections::VecDeque, mem, rc::Rc};

use super::tables::Revision;

use crate::{
    FxHashMap, FxHashSet,
    graph::{Node, find_strongly_connected_components},
    parser::location::Location,
    types::{
        r#type::{Type, TypeVar},
        type_like::TypeLike,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct TypeBound {
    pub lower: Type,
    pub lower_span: Location,
    pub upper: Type,
    pub upper_span: Location,
}

/// Snapshots share the graph until a mutation, including its provenance and
/// pending structural work. A normalization stamp is local to each snapshot:
/// checking unchanged seeds need not copy the graph just to update the stamp.
#[derive(Clone, Debug, Default)]
pub(super) struct TypeBounds {
    graph: Rc<BoundGraph>,
    normalized_at: Option<(Revision, Revision)>,
}

#[derive(Clone, Debug, Default)]
struct BoundGraph {
    seeds: Vec<TypeBound>,
    seed_keys: FxHashSet<(Type, Type)>,
    relations: FxHashMap<(Type, Type), TypeBound>,
    incoming: FxHashMap<Type, Vec<Type>>,
    outgoing: FxHashMap<Type, Vec<Type>>,
    structural: Vec<TypeBound>,
}

impl TypeBounds {
    /// Keep the first source origin for an equivalent obligation. Derived bounds
    /// carry the endpoint contributors, rather than the intermediate variable's
    /// span, so a conflict still identifies its two source requirements.
    pub fn insert(&mut self, bound: TypeBound) -> bool {
        if bound.lower == bound.upper {
            return false;
        }
        let key = (bound.lower, bound.upper);
        if self.graph.seed_keys.contains(&key) {
            return false;
        }
        self.normalized_at = None;
        let graph = Rc::make_mut(&mut self.graph);
        graph.seed_keys.insert(key);
        graph.seeds.push(bound);
        graph.propagate(bound);
        true
    }

    /// Skip unchanged inputs; `None` means skipped, `Some` reports graph changes.
    pub fn normalize_if_changed(
        &mut self,
        revision: (Revision, Revision),
        normalize: impl FnMut(Type) -> Type,
    ) -> Option<bool> {
        if self.normalized_at == Some(revision) {
            return None;
        }
        let changed = self.normalize(normalize);
        self.normalized_at = Some(revision);
        Some(changed)
    }

    /// Equality changes both representatives and nested terms. Rebuild from the
    /// remaining seeds, never from a cache of successful symbolic comparisons.
    /// The caller drains and checks structural work after every rebuild.
    pub fn normalize(&mut self, mut normalize: impl FnMut(Type) -> Type) -> bool {
        let seeds: Vec<_> = self
            .graph
            .seeds
            .iter()
            .map(|bound| TypeBound {
                lower: normalize(bound.lower),
                upper: normalize(bound.upper),
                ..*bound
            })
            .collect();
        if seeds == self.graph.seeds {
            return false;
        }
        *self = Self::default();
        for bound in seeds {
            self.insert(bound);
        }
        true
    }

    pub fn take_structural(&mut self) -> Vec<TypeBound> {
        if self.graph.structural.is_empty() {
            return Vec::new();
        }
        mem::take(&mut Rc::make_mut(&mut self.graph).structural)
    }

    /// Forget successfully checked immutable pairs. They cannot change under
    /// later substitutions, and concrete endpoints never connect propagation
    /// paths. Symbolic pairs must stay, including those with only effect vars.
    pub fn discharge_checked(&mut self, checked: &[TypeBound]) {
        let ground: FxHashSet<_> = checked
            .iter()
            .filter(|bound| bound.lower.is_constant() && bound.upper.is_constant())
            .map(|bound| (bound.lower, bound.upper))
            .collect();
        if ground.is_empty() {
            return;
        }
        let graph = Rc::make_mut(&mut self.graph);
        graph
            .seeds
            .retain(|bound| !ground.contains(&(bound.lower, bound.upper)));
        for (lower, upper) in ground {
            graph.seed_keys.remove(&(lower, upper));
            graph.relations.remove(&(lower, upper));
            if let Some(incoming) = graph.incoming.get_mut(&upper) {
                incoming.retain(|ty| *ty != lower);
                if incoming.is_empty() {
                    graph.incoming.remove(&upper);
                }
            }
            if let Some(outgoing) = graph.outgoing.get_mut(&lower) {
                outgoing.retain(|ty| *ty != upper);
                if outgoing.is_empty() {
                    graph.outgoing.remove(&lower);
                }
            }
        }
    }

    pub fn relations(&self) -> impl Iterator<Item = &TypeBound> {
        self.graph.relations.values()
    }

    /// Return a spanning set of equalities for each variable SCC, using the
    /// smallest variable as its root. The caller applies these in its equality
    /// table and normalizes the bounds before continuing structural work.
    pub fn equalities(&self) -> Vec<(TypeVar, TypeVar)> {
        let mut edges = Vec::new();
        let mut variables = FxHashSet::default();
        for &(lower, upper) in self.graph.relations.keys() {
            if let (Some(lower), Some(upper)) = (
                lower.data().as_variable().copied(),
                upper.data().as_variable().copied(),
            ) {
                variables.extend([lower, upper]);
                edges.push((lower, upper));
            }
        }
        let mut variables: Vec<_> = variables.into_iter().collect();
        variables.sort_by_key(|var| var.name());
        let indices: FxHashMap<_, _> = variables.iter().enumerate().map(|(i, v)| (*v, i)).collect();
        let mut graph: Vec<_> = variables.iter().map(|_| VariableNode::default()).collect();
        for (lower, upper) in edges {
            graph[indices[&lower]].0.push(indices[&upper]);
        }
        let mut equalities = Vec::new();
        for mut component in find_strongly_connected_components(&graph) {
            component.sort_unstable();
            let root = variables[component[0]];
            for &index in &component[1..] {
                equalities.push((root, variables[index]));
            }
        }
        equalities.sort_by_key(|(lower, upper)| (lower.name(), upper.name()));
        equalities
    }
}

impl BoundGraph {
    fn propagate(&mut self, bound: TypeBound) {
        let mut queue = VecDeque::from([bound]);
        while let Some(bound) = queue.pop_front() {
            let key = (bound.lower, bound.upper);
            if bound.lower == bound.upper || self.relations.contains_key(&key) {
                continue;
            }
            self.relations.insert(key, bound);
            self.incoming
                .entry(bound.upper)
                .or_default()
                .push(bound.lower);
            self.outgoing
                .entry(bound.lower)
                .or_default()
                .push(bound.upper);

            if is_bare_variable(bound.lower) {
                for &lower in self.incoming.get(&bound.lower).into_iter().flatten() {
                    // Propagate concrete bounds along sparse variable edges;
                    // materializing every variable path would make chains use
                    // quadratic storage before any concrete bound arrived.
                    if is_bare_variable(lower) && is_bare_variable(bound.upper) {
                        continue;
                    }
                    let previous = self.relations[&(lower, bound.lower)];
                    queue.push_back(TypeBound {
                        lower,
                        lower_span: previous.lower_span,
                        ..bound
                    });
                }
            }
            if is_bare_variable(bound.upper) {
                for &upper in self.outgoing.get(&bound.upper).into_iter().flatten() {
                    if is_bare_variable(bound.lower) && is_bare_variable(upper) {
                        continue;
                    }
                    let next = self.relations[&(bound.upper, upper)];
                    queue.push_back(TypeBound {
                        upper,
                        upper_span: next.upper_span,
                        ..bound
                    });
                }
            }
            if !is_bare_variable(bound.lower) && !is_bare_variable(bound.upper) {
                self.structural.push(bound);
            }
        }
    }
}

// Test the root constructor, not TypeLike::is_variable's recursive free-variable query.
fn is_bare_variable(ty: Type) -> bool {
    ty.data().as_variable().is_some()
}

#[derive(Default)]
struct VariableNode(Vec<usize>);

impl Node for VariableNode {
    type Index = usize;
    fn neighbors(&self) -> impl Iterator<Item = usize> {
        self.0.iter().copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::std::{logic::bool_type, math::int_type};

    fn edge(lower: Type, upper: Type) -> TypeBound {
        TypeBound {
            lower,
            upper,
            lower_span: Location::new_synthesized(),
            upper_span: Location::new_synthesized(),
        }
    }

    fn variable(index: u32) -> Type {
        Type::variable(TypeVar::new(index))
    }

    #[test]
    fn type_bounds_no_op_updates_preserve_snapshot_sharing() {
        let mut bounds = TypeBounds::default();
        let relation = edge(variable(0), variable(1));
        bounds.insert(relation);
        let first = Revision::default();
        bounds.normalize_if_changed((first, first), |ty| ty);
        let mut snapshot = bounds.clone();
        assert!(Rc::ptr_eq(&bounds.graph, &snapshot.graph));

        assert!(!bounds.insert(relation));
        assert!(!bounds.insert(edge(variable(0), variable(0))));
        assert!(bounds.take_structural().is_empty());
        bounds.discharge_checked(&[]);
        // An unrelated equality may require checking the seeds again without
        // changing the graph. Updating that stamp must neither clone the graph
        // nor change the stamp retained by the snapshot.
        let mut next = first;
        next.advance();
        assert_eq!(
            bounds.normalize_if_changed((next, first), |ty| ty),
            Some(false)
        );
        assert!(Rc::ptr_eq(&bounds.graph, &snapshot.graph));
        assert_eq!(
            bounds.normalize_if_changed((next, first), |_| panic!("current stamp")),
            None
        );
        assert_eq!(
            snapshot.normalize_if_changed((first, first), |_| panic!("snapshot stamp")),
            None
        );
        assert_eq!(
            snapshot.normalize_if_changed((next, first), |ty| ty),
            Some(false)
        );
        assert!(Rc::ptr_eq(&bounds.graph, &snapshot.graph));
    }

    #[test]
    fn type_bounds_snapshots_preserve_pending_work_and_provenance() {
        let lower = Type::nullary_function_by_val(Type::never());
        let upper = Type::nullary_function_by_val(int_type());
        let mut relation = edge(lower, upper);
        let source = Location::new_synthesized().source_id;
        relation.lower_span = Location::new(10, 11, source);
        relation.upper_span = Location::new(20, 21, source);
        let mut bounds = TypeBounds::default();
        bounds.insert(relation);
        bounds.insert(edge(variable(0), variable(1)));
        let snapshot = bounds.clone();

        let work = bounds.take_structural();
        assert_eq!(work, vec![relation]);
        bounds.discharge_checked(&work);
        assert!(!bounds.relations().any(|bound| *bound == relation));
        // A second branch rebuilds its graph under a new equality. Neither
        // draining work, retiring a checked pair nor rebuilding may change the
        // still-live outer snapshot or its source locations.
        let mut other_branch = snapshot.clone();
        assert!(other_branch.normalize(|ty| if ty == variable(1) { int_type() } else { ty }));
        other_branch.insert(edge(variable(0), bool_type()));
        assert!(
            other_branch
                .relations()
                .any(|b| b.lower == variable(0) && b.upper == int_type())
        );

        bounds = snapshot;
        assert_eq!(bounds.relations().count(), 2);
        assert!(
            bounds
                .relations()
                .any(|bound| *bound == edge(variable(0), variable(1)))
        );
        assert_eq!(bounds.take_structural(), vec![relation]);
        assert!(bounds.take_structural().is_empty());
        // A mutation after rollback must propagate using the restored indexes.
        bounds.insert(edge(int_type(), variable(0)));
        bounds.insert(edge(variable(1), bool_type()));
        assert!(
            bounds
                .take_structural()
                .iter()
                .any(|b| b.lower == int_type() && b.upper == bool_type())
        );
    }

    #[test]
    fn type_bounds_normalization_skips_only_unchanged_inputs() {
        let mut bounds = TypeBounds::default();
        bounds.insert(edge(variable(0), variable(1)));
        let first = Revision::default();
        let mut next = first;
        next.advance();
        assert_eq!(
            bounds.normalize_if_changed((first, first), |ty| ty),
            Some(false)
        );
        assert_eq!(
            bounds.normalize_if_changed((first, first), |_| panic!("unchanged")),
            None
        );
        bounds.insert(edge(variable(1), int_type()));
        let mut visits = 0;
        bounds.normalize_if_changed((first, first), |ty| {
            visits += 1;
            ty
        });
        assert!(visits > 0);
        // Mutability alone must invalidate, as must ordinary type equalities.
        for revision in [(first, next), (next, next)] {
            visits = 0;
            bounds.normalize_if_changed(revision, |ty| {
                visits += 1;
                ty
            });
            assert!(visits > 0);
        }
    }

    #[test]
    fn type_bounds_discharge_only_immutable_checked_pairs() {
        use crate::types::{
            effects::{EffType, EffectVar},
            r#type::FnType,
        };
        let lower = Type::nullary_function_by_val(Type::never());
        let upper = Type::nullary_function_by_val(int_type());
        let effectful = Type::function_type(FnType::new(
            vec![],
            int_type(),
            EffType::single_variable(EffectVar::new(0)),
        ));
        let symbolic = Type::nullary_function_by_val(variable(1));
        let mut bounds = TypeBounds::default();
        bounds.insert(edge(lower, variable(0)));
        bounds.insert(edge(variable(0), upper));
        bounds.insert(edge(upper, effectful));
        bounds.insert(edge(symbolic, upper));
        let work = bounds.take_structural();
        bounds.discharge_checked(&work);
        let pairs: FxHashSet<_> = bounds.relations().map(|b| (b.lower, b.upper)).collect();
        assert!(!pairs.contains(&(lower, upper)));
        assert!(pairs.contains(&(lower, variable(0))));
        assert!(pairs.contains(&(variable(0), upper)));
        assert!(pairs.contains(&(upper, effectful)));
        assert!(pairs.contains(&(symbolic, upper)));
        // A future equality must still schedule the symbolic obligations again.
        bounds.normalize(|ty| if ty == symbolic { upper } else { ty });
        assert!(
            bounds
                .take_structural()
                .iter()
                .any(|b| b.upper == effectful)
        );
    }

    #[test]
    fn type_bounds_derived_relations_are_sound_in_finite_model() {
        // Retaining input obligations means solution equivalence alone cannot detect a
        // missing consequence. Reachability completeness is tested separately.
        // Three variable assignments over an independent finite subtype model:
        // Never, int, bool, () -> Never, () -> int. Model points denote sets of
        // observable values/behaviors; inclusion defines their order.
        let domain = [
            (Type::never(), 0_u8),
            (int_type(), 1),
            (bool_type(), 2),
            (Type::nullary_function_by_val(Type::never()), 4),
            (Type::nullary_function_by_val(int_type()), 12),
        ];
        let terms: Vec<_> = (0..3)
            .map(variable)
            .chain(domain.iter().map(|(ty, _)| *ty))
            .collect();
        // Exhaust all two-edge graphs and their reverse insertion order. They
        // include chains, mutual inequalities, conflicting bounds and isolated
        // bounds with no opposite endpoint.
        for &a in &terms {
            for &b in &terms {
                for &c in &terms {
                    for &d in &terms {
                        let inputs = [edge(a, b), edge(c, d)];
                        let mut bounds = TypeBounds::default();
                        let mut reversed = TypeBounds::default();
                        for input in inputs {
                            bounds.insert(input);
                        }
                        for input in inputs.into_iter().rev() {
                            reversed.insert(input);
                        }
                        let pairs = |bounds: &TypeBounds| {
                            bounds
                                .relations()
                                .map(|b| (b.lower, b.upper))
                                .collect::<FxHashSet<_>>()
                        };
                        assert_eq!(pairs(&bounds), pairs(&reversed));
                        for x in 0..domain.len() {
                            for y in 0..domain.len() {
                                for z in 0..domain.len() {
                                    let assignment = [x, y, z];
                                    let value = |ty: Type| {
                                        if let Some(var) = ty.data().as_variable() {
                                            domain[assignment[var.name() as usize]].1
                                        } else {
                                            domain.iter().find(|(t, _)| *t == ty).unwrap().1
                                        }
                                    };
                                    let holds = |bound: &TypeBound| {
                                        value(bound.lower) & value(bound.upper)
                                            == value(bound.lower)
                                    };
                                    assert_eq!(
                                        inputs.iter().all(holds),
                                        bounds.relations().all(holds)
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn type_bounds_cycles_normalization_and_snapshots() {
        let (a, b, c) = (variable(0), variable(1), variable(2));
        let mut bounds = TypeBounds::default();
        bounds.insert(edge(int_type(), a));
        bounds.insert(edge(a, b));
        bounds.insert(edge(b, c));
        bounds.insert(edge(c, a));
        assert_eq!(bounds.equalities().len(), 2);
        let snapshot = bounds.clone();
        bounds.insert(edge(c, bool_type()));
        assert!(
            bounds
                .take_structural()
                .iter()
                .any(|b| b.lower == int_type() && b.upper == bool_type())
        );
        bounds = snapshot;
        assert!(bounds.take_structural().is_empty());
        bounds.normalize(|ty| if is_bare_variable(ty) { int_type() } else { ty });
        assert_eq!(bounds.relations().count(), 0);
        assert!(bounds.equalities().is_empty());
    }

    #[test]
    fn type_bounds_propagation_is_complete_for_three_edge_graphs() {
        let terms = [
            variable(0),
            variable(1),
            variable(2),
            Type::never(),
            int_type(),
            bool_type(),
            Type::nullary_function_by_val(Type::never()),
            Type::nullary_function_by_val(int_type()),
        ];
        let edges: Vec<_> = (0..terms.len())
            .flat_map(|a| (0..terms.len()).map(move |b| (a, b)))
            .collect();
        let permutations = [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ];
        // Enumerate edge multisets and every insertion order. Unlike the
        // assignment oracle, this checks that required work was actually emitted.
        for a in 0..edges.len() {
            for b in a..edges.len() {
                for c in b..edges.len() {
                    let inputs = [edges[a], edges[b], edges[c]];
                    let mut reachable = [[false; 8]; 8];
                    for &(from, to) in &inputs {
                        reachable[from][to] = true;
                    }
                    // Independent Floyd-Warshall closure: only variables may
                    // be internal path nodes. A structural type is a terminal
                    // obligation for the external comparator, not a transit node.
                    for via in 0..3 {
                        for from in 0..terms.len() {
                            for to in 0..terms.len() {
                                reachable[from][to] |= reachable[from][via] && reachable[via][to];
                            }
                        }
                    }
                    let mut expected_relations = FxHashSet::default();
                    let mut expected_structural = FxHashSet::default();
                    for from in 0..terms.len() {
                        for to in 0..terms.len() {
                            if from != to && reachable[from][to] && (from >= 3 || to >= 3) {
                                let pair = (terms[from], terms[to]);
                                expected_relations.insert(pair);
                                if from >= 3 && to >= 3 {
                                    expected_structural.insert(pair);
                                }
                            }
                        }
                    }
                    for order in permutations {
                        let mut bounds = TypeBounds::default();
                        for index in order {
                            let (from, to) = inputs[index];
                            bounds.insert(edge(terms[from], terms[to]));
                        }
                        // Selection needs propagated lower/upper bounds too.
                        // Exclude variable-only edges: those stay sparse rather
                        // than materializing the variable transitive closure.
                        let actual_relations: FxHashSet<_> = bounds
                            .relations()
                            .filter(|b| !is_bare_variable(b.lower) || !is_bare_variable(b.upper))
                            .map(|b| (b.lower, b.upper))
                            .collect();
                        assert_eq!(
                            actual_relations, expected_relations,
                            "relations: edges {inputs:?}, order {order:?}"
                        );
                        let actual_structural: FxHashSet<_> = bounds
                            .take_structural()
                            .into_iter()
                            .map(|b| (b.lower, b.upper))
                            .collect();
                        assert_eq!(
                            actual_structural, expected_structural,
                            "structural work: edges {inputs:?}, order {order:?}"
                        );
                        assert!(bounds.take_structural().is_empty());
                    }
                }
            }
        }
    }

    #[test]
    fn type_bounds_normalization_rechecks_nested_bindings() {
        let a = variable(0);
        let b = variable(1);
        let lower = Type::tuple(vec![a]);
        let upper = Type::tuple(vec![int_type()]);
        let mut bounds = TypeBounds::default();
        bounds.insert(edge(lower, b));
        bounds.insert(edge(b, upper));
        assert_eq!(bounds.take_structural().len(), 1);
        bounds.normalize(|ty| {
            if ty == lower {
                Type::tuple(vec![bool_type()])
            } else {
                ty
            }
        });
        let structural = bounds.take_structural();
        assert_eq!(structural.len(), 1);
        assert_eq!(structural[0].lower, Type::tuple(vec![bool_type()]));
    }

    #[test]
    fn type_bounds_long_chains_keep_variable_edges_sparse() {
        let count = 1024;
        for reverse in [false, true] {
            let mut bounds = TypeBounds::default();
            let mut edges: Vec<_> = (0..count - 1)
                .map(|i| edge(variable(i), variable(i + 1)))
                .collect();
            edges.extend([
                edge(int_type(), variable(0)),
                edge(variable(count - 1), int_type()),
            ]);
            if reverse {
                edges.reverse();
            }
            for edge in edges {
                bounds.insert(edge);
            }
            // n-1 variable edges, n lower bounds, n upper bounds. Reflexive
            // int <: int is discharged without retaining a structural pair.
            assert_eq!(bounds.relations().count(), (3 * count - 1) as usize);
            assert!(bounds.equalities().is_empty());
            assert!(bounds.take_structural().is_empty());
        }
    }
}
