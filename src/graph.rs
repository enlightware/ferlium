// Copyright 2025 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::collections::{HashSet, VecDeque};

pub(crate) trait Node {
    type Index: TryInto<usize> + Copy;
    fn neighbors(&self) -> impl Iterator<Item = Self::Index>;
}

pub(crate) fn find_disjoint_subgraphs<N: Node>(graph: &[N]) -> Vec<Vec<usize>>
where
    <<N as Node>::Index as TryInto<usize>>::Error: std::fmt::Debug,
{
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
            current_subgraph.push(node_idx); // Add to current subgraph

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

pub(crate) fn find_strongly_connected_components<N: Node>(graph: &[N]) -> Vec<Vec<usize>>
where
    <<N as Node>::Index as TryInto<usize>>::Error: std::fmt::Debug,
{
    let mut index = 0;
    let mut stack = Vec::new();
    let mut in_stack = vec![false; graph.len()];
    let mut indices = vec![None; graph.len()];
    let mut low_link = vec![0; graph.len()];
    let mut sccs = Vec::new();

    #[allow(clippy::too_many_arguments)]
    fn strong_connect<N: Node>(
        node_index: usize,
        index: &mut usize,
        stack: &mut Vec<usize>,
        in_stack: &mut [bool],
        indices: &mut [Option<usize>],
        low_link: &mut [usize],
        graph: &[N],
        sccs: &mut Vec<Vec<usize>>,
    ) where
        <<N as Node>::Index as TryInto<usize>>::Error: std::fmt::Debug,
    {
        indices[node_index] = Some(*index);
        low_link[node_index] = *index;
        *index += 1;
        stack.push(node_index);
        in_stack[node_index] = true;

        // Explore neighbors
        for neighbor in graph[node_index].neighbors() {
            let neighbor_index: usize = neighbor.try_into().unwrap();

            if indices[neighbor_index].is_none() {
                // Neighbor has not been visited, recurse
                strong_connect(
                    neighbor_index,
                    index,
                    stack,
                    in_stack,
                    indices,
                    low_link,
                    graph,
                    sccs,
                );
                low_link[node_index] = low_link[node_index].min(low_link[neighbor_index]);
            } else if in_stack[neighbor_index] {
                // Neighbor is in the stack, hence part of the current SCC
                low_link[node_index] = low_link[node_index].min(indices[neighbor_index].unwrap());
            }
        }

        // If `node_index` is a root node, pop the stack to form an SCC
        if low_link[node_index] == indices[node_index].unwrap() {
            let mut scc = Vec::new();
            while let Some(w) = stack.pop() {
                in_stack[w] = false;
                scc.push(w);
                if w == node_index {
                    break;
                }
            }
            sccs.push(scc);
        }
    }

    // Call `strong_connect` for each node that hasn't been visited yet
    for node_index in 0..graph.len() {
        if indices[node_index].is_none() {
            strong_connect(
                node_index,
                &mut index,
                &mut stack,
                &mut in_stack,
                &mut indices,
                &mut low_link,
                graph,
                &mut sccs,
            );
        }
    }

    sccs
}

pub(crate) fn topological_sort_sccs<N: Node>(graph: &[N], sccs: &[Vec<usize>]) -> Vec<Vec<usize>>
where
    <<N as Node>::Index as TryInto<usize>>::Error: std::fmt::Debug,
{
    // Map each node to its SCC index for quick lookup
    let mut node_to_scc = vec![None; graph.len()];
    for (i, scc) in sccs.iter().enumerate() {
        for &node in scc {
            node_to_scc[node] = Some(i);
        }
    }

    // Build the condensed graph of SCC dependencies
    let mut scc_graph: Vec<HashSet<usize>> = vec![HashSet::new(); sccs.len()];
    let mut in_degree = vec![0; sccs.len()];

    for (i, scc) in sccs.iter().enumerate() {
        for &node in scc {
            for neighbor in graph[node].neighbors() {
                let neighbor_index: usize = neighbor.try_into().unwrap();
                if let Some(j) = node_to_scc[neighbor_index] {
                    if i != j && scc_graph[i].insert(j) {
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
        for &neighbor in &scc_graph[i] {
            in_degree[neighbor] -= 1;
            if in_degree[neighbor] == 0 {
                queue.push_back(neighbor);
            }
        }
    }

    sorted_sccs
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    struct Node(Vec<u32>);
    impl super::Node for Node {
        type Index = u32;
        fn neighbors(&self) -> impl Iterator<Item = Self::Index> {
            self.0.iter().copied()
        }
    }

    use Node as N;

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

    fn to_sorted_sets(sccs: Vec<Vec<usize>>) -> Vec<BTreeSet<usize>> {
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

    fn to_set_of_sets(sccs: Vec<Vec<usize>>) -> BTreeSet<BTreeSet<usize>> {
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
}
