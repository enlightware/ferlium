// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use std::collections::VecDeque;

use crate::FxHashSet;

pub(crate) trait Node {
    /// How this graph names its own nodes.
    ///
    /// Both conversions are infallible in practice — a position comes from the graph's own length —
    /// so the errors are unwrapped, which is why both need `Debug`.
    type Index: TryInto<usize, Error: std::fmt::Debug>
        + TryFrom<usize, Error: std::fmt::Debug>
        + Copy;
    fn neighbors(&self) -> impl Iterator<Item = Self::Index>;
}

/// A position, in the caller's index type.
fn index_of<I: TryFrom<usize, Error: std::fmt::Debug>>(position: usize) -> I {
    I::try_from(position).expect("a position within the graph must fit its own index type")
}

/// A caller's index, as a position.
fn position_of<I: TryInto<usize, Error: std::fmt::Debug>>(index: I) -> usize {
    index
        .try_into()
        .expect("a graph index must be usable as a position")
}

/// Reachable nodes in reverse postorder from `entry`.
///
/// Iterative rather than recursive so compiler graph size is independent of the host thread's
/// call-stack capacity. A node always precedes its forward descendants except where a cycle makes
/// that impossible, which is the useful visitation order for forward dataflow.
pub(crate) fn reverse_postorder(successors: &[Vec<usize>], entry: usize) -> Vec<usize> {
    let mut visited = vec![false; successors.len()];
    let mut postorder = Vec::with_capacity(successors.len());
    let mut stack = vec![(entry, 0)];
    visited[entry] = true;
    while let Some((node, next_successor)) = stack.last_mut() {
        if let Some(&successor) = successors[*node].get(*next_successor) {
            *next_successor += 1;
            if !visited[successor] {
                visited[successor] = true;
                stack.push((successor, 0));
            }
        } else {
            postorder.push(*node);
            stack.pop();
        }
    }
    postorder.reverse();
    postorder
}

#[allow(dead_code)]
pub(crate) fn find_disjoint_subgraphs<N: Node>(graph: &[N]) -> Vec<Vec<N::Index>> {
    let mut visited = vec![false; graph.len()]; // Track visited nodes
    let mut disjoint_subgraphs = Vec::new(); // Store the result

    for start in 0..graph.len() {
        if visited[start] {
            continue; // Skip already visited nodes
        }
        let mut queue = vec![start]; // BFS queue
        let mut current_subgraph = Vec::new(); // Collect nodes for the current component

        while let Some(node_idx) = queue.pop() {
            if visited[node_idx] {
                continue; // Skip if already visited
            }
            visited[node_idx] = true; // Mark as visited
            current_subgraph.push(index_of::<N::Index>(node_idx)); // Add to current subgraph

            // Add all unvisited connected nodes to the queue
            for neighbor_idx in graph[node_idx].neighbors() {
                if !visited[neighbor_idx.try_into().unwrap()] {
                    queue.push(neighbor_idx.try_into().unwrap());
                }
            }
        }

        disjoint_subgraphs.push(current_subgraph); // Save the found subgraph
    }

    disjoint_subgraphs
}

/// The strongly connected components of `graph`, each after all the components that it reaches.
///
/// Tarjan's algorithm, iterative rather than recursive as `reverse_postorder` is: the graphs
/// include the interned types that the compiler builds, whose size is bounded by limits rather
/// than by the host thread's call-stack capacity.
pub(crate) fn find_strongly_connected_components<N: Node>(graph: &[N]) -> Vec<Vec<N::Index>> {
    let mut search = SccSearch {
        graph,
        next_index: 0,
        stack: Vec::new(),
        in_stack: vec![false; graph.len()],
        indices: vec![None; graph.len()],
        low_link: vec![0; graph.len()],
        path: Vec::new(),
        sccs: Vec::new(),
    };
    for root in 0..graph.len() {
        if search.indices[root].is_none() {
            search.run_from(root);
        }
    }
    search.sccs
}

/// The state of Tarjan's algorithm.
struct SccSearch<'g, N: Node> {
    graph: &'g [N],
    next_index: usize,
    stack: Vec<usize>,
    in_stack: Vec<bool>,
    indices: Vec<Option<usize>>,
    low_link: Vec<usize>,
    /// The active path of the search, each node with the neighbors it has still to explore.
    path: Vec<(usize, std::vec::IntoIter<usize>)>,
    sccs: Vec<Vec<N::Index>>,
}

impl<N: Node> SccSearch<'_, N> {
    fn run_from(&mut self, root: usize) {
        self.enter(root);
        while let Some((node, neighbors)) = self.path.last_mut() {
            let node = *node;
            if let Some(neighbor) = neighbors.next() {
                match self.indices[neighbor] {
                    // Not visited yet: descend into it.
                    None => self.enter(neighbor),
                    // In the stack, hence part of the current SCC.
                    Some(index) if self.in_stack[neighbor] => {
                        self.low_link[node] = self.low_link[node].min(index);
                    }
                    Some(_) => {}
                }
            } else {
                self.leave(node);
            }
        }
    }

    fn enter(&mut self, node: usize) {
        self.indices[node] = Some(self.next_index);
        self.low_link[node] = self.next_index;
        self.next_index += 1;
        self.stack.push(node);
        self.in_stack[node] = true;
        let neighbors: Vec<_> = self.graph[node].neighbors().map(position_of).collect();
        self.path.push((node, neighbors.into_iter()));
    }

    /// Return from `node`, all of whose neighbors are explored, to its parent on the path.
    fn leave(&mut self, node: usize) {
        self.path.pop();
        if let Some(&(parent, _)) = self.path.last() {
            self.low_link[parent] = self.low_link[parent].min(self.low_link[node]);
        }
        // If `node` is a root node, pop the stack to form an SCC.
        if self.low_link[node] == self.indices[node].unwrap() {
            let mut scc = Vec::new();
            while let Some(w) = self.stack.pop() {
                self.in_stack[w] = false;
                // Converted here, at the one push that builds a component, rather than by a
                // second pass over the finished answer.
                scc.push(index_of::<N::Index>(w));
                if w == node {
                    break;
                }
            }
            self.sccs.push(scc);
        }
    }
}

pub(crate) fn topological_sort_sccs<N: Node>(
    graph: &[N],
    sccs: &[Vec<N::Index>],
) -> Vec<Vec<N::Index>> {
    // Map each node to its SCC index for quick lookup.
    let mut node_to_scc = vec![None; graph.len()];
    for (i, scc) in sccs.iter().enumerate() {
        for &node in scc {
            node_to_scc[position_of::<N::Index>(node)] = Some(i);
        }
    }

    // Build the condensed graph of SCC dependencies
    let mut scc_graph: Vec<Option<FxHashSet<usize>>> = vec![None; sccs.len()];
    let mut in_degree = vec![0; sccs.len()];

    for (i, scc) in sccs.iter().enumerate() {
        for &node in scc {
            for neighbor in graph[position_of::<N::Index>(node)].neighbors() {
                let neighbor_index: usize = neighbor.try_into().unwrap();
                if let Some(j) = node_to_scc[neighbor_index] {
                    if i != j
                        && scc_graph[i]
                            .get_or_insert_with(FxHashSet::default)
                            .insert(j)
                    {
                        // Increment in-degree only if the edge is unique
                        in_degree[j] += 1;
                    }
                }
            }
        }
    }

    // Perform topological sort on the SCC graph using Kahn’s algorithm
    let mut queue = VecDeque::new();
    let mut sorted_sccs = Vec::new();

    // Initialize queue with SCCs that have zero in-degrees
    for (i, &degree) in in_degree.iter().enumerate() {
        if degree == 0 {
            queue.push_back(i);
        }
    }

    while let Some(i) = queue.pop_front() {
        sorted_sccs.push(sccs[i].clone());
        let Some(neighbors) = scc_graph[i].as_ref() else {
            continue;
        };
        for &neighbor in neighbors {
            in_degree[neighbor] -= 1;
            if in_degree[neighbor] == 0 {
                queue.push_back(neighbor);
            }
        }
    }

    sorted_sccs
}

/// Visitation state of a node during a depth-first search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VisitState {
    /// Not yet reached.
    Unvisited,
    /// Currently on the active DFS path — a back-edge to this node means a cycle.
    OnStack,
    /// Fully explored; all descendants have been processed.
    Done,
}

/// Starting from `start`, perform an iterative DFS over `graph` and return the first cycle
/// found as an ordered list of node indices, or `None` if the reachable subgraph is acyclic.
///
/// The returned `Vec` begins at the node where the back-edge closes back and lists every
/// node on the cycle path in traversal order. For example, given edges `0→1→2→1` starting
/// from `0`, the result is `Some([1, 2])`.
///
/// `start` must be a valid index into `graph`.
pub(crate) fn find_cycle_from<N: Node>(graph: &[N], start: N::Index) -> Option<Vec<N::Index>> {
    let start = position_of::<N::Index>(start);
    let mut state = vec![VisitState::Unvisited; graph.len()];

    // Each stack frame holds (node_index, index_of_next_child_to_visit).
    let mut dfs_stack: Vec<(usize, usize)> = vec![(start, 0)];
    // `path` mirrors the live DFS recursion stack.
    let mut path: Vec<usize> = vec![start];
    state[start] = VisitState::OnStack;

    while let Some((current, child_idx)) = dfs_stack.last_mut() {
        let current = *current;
        // Collect neighbors eagerly to avoid holding a borrow on `graph[current]`
        // while we mutate `dfs_stack` and `path` below.
        let neighbors: Vec<usize> = graph[current]
            .neighbors()
            .map(|nb| nb.try_into().unwrap())
            .collect();

        if *child_idx < neighbors.len() {
            let neighbor = neighbors[*child_idx];
            *child_idx += 1;

            match state[neighbor] {
                VisitState::Unvisited => {
                    state[neighbor] = VisitState::OnStack;
                    path.push(neighbor);
                    dfs_stack.push((neighbor, 0));
                }
                VisitState::OnStack => {
                    // Back-edge: collect the cycle portion of `path` starting at `neighbor`.
                    let cycle = path
                        .iter()
                        .copied()
                        .skip_while(|&id| id != neighbor)
                        .map(index_of::<N::Index>)
                        .collect();
                    return Some(cycle);
                }
                VisitState::Done => {
                    // Already fully explored; safe to skip.
                }
            }
        } else {
            // All neighbours processed; mark done and pop.
            state[current] = VisitState::Done;
            dfs_stack.pop();
            path.pop();
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    struct TestNode(Vec<u32>);
    impl super::Node for TestNode {
        type Index = u32;
        fn neighbors(&self) -> impl Iterator<Item = Self::Index> {
            self.0.iter().copied()
        }
    }

    use TestNode as N;

    #[test]
    fn reverse_postorder_ignores_unreachable_nodes_and_puts_back_edges_last() {
        let successors = vec![vec![1], vec![2, 3], vec![1], vec![], vec![0]];
        assert_eq!(reverse_postorder(&successors, 0), vec![0, 1, 3, 2]);
    }

    // ---- find_cycle_from ----

    #[test]
    fn cycle_from_no_edges() {
        // Single isolated node — no cycle.
        let graph = vec![N(vec![])];
        assert_eq!(find_cycle_from(&graph, 0), None);
    }

    #[test]
    fn cycle_from_linear_chain() {
        // 0 → 1 → 2, no cycle.
        let graph = vec![N(vec![1]), N(vec![2]), N(vec![])];
        assert_eq!(find_cycle_from(&graph, 0), None);
    }

    #[test]
    fn cycle_from_self_loop() {
        // Node 1 points to itself; reachable from 0.
        let graph = vec![N(vec![1]), N(vec![1]), N(vec![])];
        assert_eq!(find_cycle_from(&graph, 0), Some(vec![1]));
    }

    #[test]
    fn cycle_from_simple_cycle() {
        // 0 → 1 → 2 → 0
        let graph = vec![N(vec![1]), N(vec![2]), N(vec![0])];
        assert_eq!(find_cycle_from(&graph, 0), Some(vec![0, 1, 2]));
    }

    #[test]
    fn cycle_from_diamond_no_cycle() {
        // Diamond: 0 → 1, 0 → 2, 1 → 3, 2 → 3 — shared dependency but no cycle.
        let graph = vec![N(vec![1, 2]), N(vec![3]), N(vec![3]), N(vec![])];
        assert_eq!(find_cycle_from(&graph, 0), None);
    }

    #[test]
    fn cycle_from_start_not_in_cycle() {
        // 0 → 1 → 2 → 1  (cycle is 1→2, start node 0 is outside it)
        let graph = vec![N(vec![1]), N(vec![2]), N(vec![1])];
        assert_eq!(find_cycle_from(&graph, 0), Some(vec![1, 2]));
    }

    #[test]
    fn cycle_from_cycle_not_at_start() {
        // 0 → 1 → 2 → 3 → 1  (cycle is 1→2→3, start node 0 is outside it)
        let graph = vec![N(vec![1]), N(vec![2]), N(vec![3]), N(vec![1])];
        assert_eq!(find_cycle_from(&graph, 0), Some(vec![1, 2, 3]));
    }

    #[test]
    fn cycle_from_unreachable_cycle() {
        // 0 has no edges; cycle 1→2→1 is not reachable from 0.
        let graph = vec![N(vec![]), N(vec![2]), N(vec![1])];
        assert_eq!(find_cycle_from(&graph, 0), None);
    }

    // ---- find_disjoint_subgraphs ----

    #[test]
    fn single_disjoint_graph() {
        let graph = vec![N(vec![]), N(vec![]), N(vec![])];
        let subgraphs = find_disjoint_subgraphs(&graph);
        assert_eq!(subgraphs.len(), 3);
        assert_eq!(subgraphs[0].len(), 1);
        assert_eq!(subgraphs[0][0], 0);
        assert_eq!(subgraphs[1].len(), 1);
        assert_eq!(subgraphs[1][0], 1);
        assert_eq!(subgraphs[2].len(), 1);
        assert_eq!(subgraphs[2][0], 2);
    }

    #[test]
    fn single_joint_graph() {
        let graph = vec![N(vec![1, 2]), N(vec![0]), N(vec![0])];
        let subgraphs = find_disjoint_subgraphs(&graph);
        assert_eq!(subgraphs.len(), 1);
        assert_eq!(subgraphs[0].len(), 3);
        assert_eq!(subgraphs[0][0], 0);
        assert_eq!(subgraphs[0][1], 2);
        assert_eq!(subgraphs[0][2], 1);
    }

    #[test]
    fn three_disjoint_subgraphs() {
        let graph = vec![
            N(vec![1]),
            N(vec![0]),
            N(vec![4, 5]),
            N(vec![3]),
            N(vec![2, 5]),
            N(vec![4]),
        ];
        let subgraphs = find_disjoint_subgraphs(&graph);
        assert_eq!(subgraphs.len(), 3);
        assert_eq!(subgraphs[0].len(), 2);
        assert_eq!(subgraphs[0][0], 0);
        assert_eq!(subgraphs[0][1], 1);
        assert_eq!(subgraphs[1].len(), 3);
        assert_eq!(subgraphs[1][0], 2);
        assert_eq!(subgraphs[1][1], 5);
        assert_eq!(subgraphs[1][2], 4);
        assert_eq!(subgraphs[2].len(), 1);
        assert_eq!(subgraphs[2][0], 3);
    }

    fn to_sorted_sets<I: Ord>(sccs: Vec<Vec<I>>) -> Vec<BTreeSet<I>> {
        sccs.into_iter()
            .map(|scc| scc.into_iter().collect())
            .collect()
    }

    #[test]
    fn scc_no_edges() {
        let graph = vec![N(vec![]), N(vec![]), N(vec![])];
        let sccs = find_strongly_connected_components(&graph);
        assert_eq!(sccs.len(), 3);
        assert!(sccs.contains(&vec![0]));
        assert!(sccs.contains(&vec![1]));
        assert!(sccs.contains(&vec![2]));
        let sorted_sccs = topological_sort_sccs(&graph, &sccs);
        assert_eq!(sorted_sccs.len(), 3);
        assert!(sorted_sccs.contains(&vec![0]));
        assert!(sorted_sccs.contains(&vec![1]));
        assert!(sorted_sccs.contains(&vec![2]));
    }

    #[test]
    fn scc_simple_chain() {
        let graph = vec![
            N(vec![1]), // 0 -> 1
            N(vec![2]), // 1 -> 2
            N(vec![]),  // 2
        ];
        let sccs = find_strongly_connected_components(&graph);
        assert_eq!(sccs.len(), 3);
        assert!(sccs.contains(&vec![0]));
        assert!(sccs.contains(&vec![1]));
        assert!(sccs.contains(&vec![2]));

        let sorted_sccs = topological_sort_sccs(&graph, &sccs);
        assert_eq!(sorted_sccs.len(), 3);
        assert_eq!(sorted_sccs, vec![vec![0], vec![1], vec![2]]);
    }

    #[test]
    fn scc_simple_cycle() {
        let graph = vec![
            N(vec![1]), // 0 -> 1
            N(vec![2]), // 1 -> 2
            N(vec![0]), // 2 -> 0 (cycle)
        ];
        let sccs = find_strongly_connected_components(&graph);
        let expected = vec![BTreeSet::from([0, 1, 2])];
        assert_eq!(to_sorted_sets(sccs.clone()), expected);

        let sorted_sccs = topological_sort_sccs(&graph, &sccs);
        assert_eq!(sorted_sccs.len(), 1);
        assert_eq!(to_sorted_sets(sorted_sccs), vec![BTreeSet::from([0, 1, 2])]);
    }

    #[test]
    fn scc_disconnected_cycles() {
        let graph = vec![
            N(vec![1]), // 0 -> 1
            N(vec![0]), // 1 -> 0 (first cycle)
            N(vec![3]), // 2 -> 3
            N(vec![2]), // 3 -> 2 (second cycle)
        ];
        let sccs = find_strongly_connected_components(&graph);
        let expected = vec![BTreeSet::from([0, 1]), BTreeSet::from([2, 3])];
        assert_eq!(to_sorted_sets(sccs.clone()), expected);

        let sorted_sccs = topological_sort_sccs(&graph, &sccs);
        let sorted_sccs = to_sorted_sets(sorted_sccs);
        assert_eq!(sorted_sccs.len(), 2);
        assert!(sorted_sccs.contains(&BTreeSet::from([0, 1])));
        assert!(sorted_sccs.contains(&BTreeSet::from([2, 3])));
    }

    fn to_set_of_sets<I: Ord>(sccs: Vec<Vec<I>>) -> BTreeSet<BTreeSet<I>> {
        sccs.into_iter()
            .map(|scc| scc.into_iter().collect())
            .collect()
    }

    #[test]
    fn scc_complex_graph() {
        let graph = vec![
            N(vec![1]),    // 0 -> 1
            N(vec![2, 3]), // 1 -> 2, 3
            N(vec![0]),    // 2 -> 0 (cycle with 0, 1, 2)
            N(vec![4]),    // 3 -> 4
            N(vec![5]),    // 4 -> 5
            N(vec![3, 6]), // 5 -> 3, 6 (cycle with 3, 4, 5)
            N(vec![]),     // 6
        ];
        let sccs = find_strongly_connected_components(&graph);
        let expected = vec![
            BTreeSet::from([0, 1, 2]), // First SCC (cycle between 0, 1, 2)
            BTreeSet::from([3, 4, 5]), // Second SCC (cycle between 3, 4, 5)
            BTreeSet::from([6]),       // Third SCC (independent node)
        ]
        .into_iter()
        .collect::<BTreeSet<_>>();
        assert_eq!(to_set_of_sets(sccs.clone()), expected);

        let sorted_sccs = topological_sort_sccs(&graph, &sccs);
        let sorted_sccs = to_sorted_sets(sorted_sccs);

        // Expected sorted order: SCC containing {0, 1, 2} first, followed by {3, 4, 5}, then {6}.
        assert_eq!(sorted_sccs.len(), 3);
        assert_eq!(sorted_sccs[0], BTreeSet::from([0, 1, 2]));
        assert_eq!(sorted_sccs[1], BTreeSet::from([3, 4, 5]));
        assert_eq!(sorted_sccs[2], BTreeSet::from([6]));
    }

    /// Each component comes after all those it reaches, its nodes in the order in which the
    /// search leaves them.
    #[test]
    fn scc_order_follows_the_search() {
        let graph = vec![
            N(vec![1]),
            N(vec![2, 3]),
            N(vec![0]),
            N(vec![4]),
            N(vec![5]),
            N(vec![3, 6]),
            N(vec![]),
        ];
        let sccs = find_strongly_connected_components(&graph);
        assert_eq!(sccs, vec![vec![6], vec![5, 4, 3], vec![2, 1, 0]]);
    }

    /// The search does not use the call stack, on a path longer than a thread's stack could
    /// hold as recursion.
    #[test]
    fn scc_of_a_long_path() {
        let n = 1_000_000;
        let mut graph: Vec<_> = (1..n).map(|i| N(vec![i])).collect();
        graph.push(N(vec![0]));
        let sccs = std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(move || find_strongly_connected_components(&graph))
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0].len(), n as usize);
    }
}
